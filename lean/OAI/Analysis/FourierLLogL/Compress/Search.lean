import Mathlib
/-! # Two-order finite refinement search -/
open Set Function Filter
noncomputable section
namespace OAI

namespace FourierLLogL.Compress
set_option maxHeartbeats 600000
open Real
universe u
variable {S : Type u}

/-- Normalized potentials. A can only move down in time. Across indices A
moves up while the low and high potentials are margins of disjoint intervals
that move down. -/
structure Arena (S : Type u) where
  N : ℕ
  mov : S → S → Prop
  refl (s) : mov s s
  trans {s t u} : mov s t → mov t u → mov s u
  topc : S → ℝ
  pay {s t} : mov s t → topc t ≤ topc s
  A : ℕ → S → ℝ
  Alo (s i) (hi : i<N) : 0 ≤ A i s
  Ahi (s i) (hi : i<N) : A i s ≤ 1
  Am (s) {i j} (hi : i ≤ j) (hj : j<N) : A i s ≤ A j s
  As {s t} (h : mov s t) {i} (hi : i<N) : A i t ≤ A i s
  L : ℕ → S → ℝ
  H : ℕ → S → ℝ
  Llo (s i) (hi : i<N) : 0 ≤ L i s
  Hhi (s i) (hi : i<N) : H i s ≤ 1
  LH (s i) (hi : i<N) : L i s ≤ H i s
  BC (s) {i j} (hi : i < j) (hj : j<N) : H j s ≤ L i s
  Ls {s t} (h : mov s t) {i} (hi : i<N) : L i t ≤ L i s
  Hs {s t} (h : mov s t) {i} (hi : i<N) : H i t ≤ H i s
  found : S → Prop
  rate : ℝ
  r0 : 0 < rate
  offer (s) {i} (hi : i < N) (h : ¬ found s) (x : ℝ) (hp : 0 < x) (hb : x ≤ rate) :
    ∃ t, mov s t ∧ x ≤ A i s - A i t ∧
      topc s - topc t ≤ 2*(H i s-L i s)*x

namespace Arena
variable (d : Arena S)
omit d in
private lemma dummy : True := trivial

lemma H_index (s) {i j} (hi : i ≤ j) (hj : j<d.N) : d.H j s ≤ d.H i s := by
  obtain rfl|h := eq_or_lt_of_le hi
  · exact le_rfl
  · exact (d.BC s h hj).trans (d.LH s _ (by omega))
lemma L_index (s) {i j} (hi : i ≤ j) (hj : j<d.N) : d.L j s ≤ d.L i s := by
  obtain rfl|h := eq_or_lt_of_le hi
  · exact le_rfl
  · exact (d.LH s _ hj).trans (d.BC s h hj)

lemma budget_index (s : S) {i : ℕ} (hi : i < d.N)
    (u a δ η : ℝ) (hu : 0 < u) (ha : 0 < a) (hδ : 0 < δ)
    (hη : δ*exp (2*u/a) ≤ η) :
    ∃ t, d.mov s t ∧ d.topc s-d.topc t ≤ a*η ∧
      (d.found t ∨ u ≤ d.A i s - d.A i t ∨
        (d.topc s-d.topc t)+a*δ ≤ a*(d.H i s-d.L i t)) := by
  classical
  let cost (t : S) := d.topc s-d.topc t
  let Δ t := d.A i s - d.A i t
  let b t := min u (Δ t)
  let goal (t : S) := d.found t ∨ u ≤ Δ t ∨ cost t+a*δ ≤ a*(d.H i s-d.L i t)

  have H (k : ℕ) : ∃ t, d.mov s t ∧ cost t+a*δ ≤ a*δ*exp (2*b t/a) ∧
      (goal t ∨ k*d.rate ≤ Δ t) := by
    induction k with
    | zero =>
      refine ⟨s,d.refl _,?_ ,Or.inr ?_⟩ <;> simp [cost,Δ,b,le_of_lt hu]
    | succ k ih =>
      obtain ⟨t,hst,hc,hk⟩ := ih
      by_cases h : goal t
      · exact ⟨t,hst,hc,Or.inl h⟩
      unfold goal at h
      push Not at h
      have he : 0 < u-Δ t := by linarith [h.2.1]
      let x := min d.rate (u-Δ t)
      have hx : 0 < x := lt_min d.r0 he
      obtain ⟨q,hq,hA,hV⟩ := d.offer t hi h.1 x hx (min_le_left _ _)
      have hT : b t = Δ t := min_eq_right h.2.1.le
      have hQ : Δ t+x ≤ b q := by
        refine le_min ?_ ?_
        · linarith [show x ≤ u-Δ t from min_le_right _ _]
        · dsimp [Δ]; linarith
      have hcp : 0 ≤ cost t := sub_nonneg.mpr (d.pay hst)
      have H1 : cost q+a*δ ≤ (cost t+a*δ)*(1+2*x/a) := by
        have HH : a*(d.H i t-d.L i t) ≤ cost t+a*δ :=
          (mul_le_mul_of_nonneg_left (sub_le_sub_right (d.Hs hst hi) _) ha.le).trans h.2.2.le
        have h1 : a*(cost q-cost t) ≤ (cost t+a*δ)* (2*x) := by
          calc
            _ ≤ a*(2*(d.H i t-d.L i t)*x) :=
              mul_le_mul_of_nonneg_left (by unfold cost; linarith) ha.le
            _ = a*(d.H i t-d.L i t)*(2*x) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right HH (by positivity)
        field_simp; linarith
      have H2 : exp (2*b t/a) * exp (2*x/a) ≤ exp (2*b q/a) := by
        rw [← exp_add,exp_le_exp,hT]
        field_simp; linarith
      have H3 : cost q+a*δ ≤ a*δ*exp (2*b q/a) := by
        apply le_trans H1
        have hxp : 1+2*x/a ≤ exp (2*x/a) := by linarith [add_one_le_exp (2*x/a)]
        apply le_trans (mul_le_mul hc hxp (by positivity) (by positivity))
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left H2 (mul_pos ha hδ).le
      refine ⟨q,d.trans hst hq,H3,?_⟩

      rcases le_total d.rate (u-Δ t) with hn|hn
      · have hh : k*d.rate ≤ Δ t := hk.resolve_left (by unfold goal; grind)
        right
        have hh' : x = d.rate := min_eq_left hn
        push_cast
        have H := min_le_right u (Δ q)
        linarith [show b q ≤ Δ q from H]
      · left
        refine Or.inr (Or.inl ?_)
        have hh : x = u - Δ t := min_eq_right hn
        have he : b q ≤ Δ q := min_le_right _ _
        linarith
  obtain ⟨k,hk⟩ := exists_nat_gt (1 / d.rate)
  obtain ⟨t,hst,h1,h2⟩ := H k
  have h3 : goal t :=
    h2.resolve_right (fun hh => by
      have Hr := (div_lt_iff₀ d.r0).mp hk
      unfold Δ at hh; linarith [d.Ahi s i hi,d.Alo t i hi])
  refine ⟨t,hst,?_ ,h3⟩
  have H0 : b t ≤ u := min_le_left _ _
  have H1 : exp (2*b t/a) ≤ exp (2*u/a) := by gcongr
  change cost t ≤ _
  nlinarith [mul_le_mul_of_nonneg_left H1 (mul_pos ha hδ).le,
    mul_le_mul_of_nonneg_left hη ha.le]

/-- Forward search through adjacent blocks [o+i*m,o+(i+1)m). Fully failed blocks consume width. -/
lemma budget_ascending (s : S) (G : S → Prop)
    (o n m : ℕ) (hm : 0 < m) (hn : 0 < n) (hb : o+n*m ≤ d.N)
    (a b δ : ℝ) (ha : 0 < a) (hδ : 1 < n*δ)
    (hstep : ∀ (t) (_h : d.mov s t) i (_hi : i<n), ∃ q, d.mov t q ∧
      ((G q ∧ d.topc t-d.topc q ≤ a*(d.H (o+i*m) t-d.L (o+(i+1)*m-1) q)+b) ∨
        (d.topc t-d.topc q)+a*δ ≤ a*(d.H (o+i*m) t-d.L (o+(i+1)*m-1) q))) :
    ∃ t, d.mov s t ∧ G t ∧ d.topc s-d.topc t ≤ a*(d.H o s-d.L (o+n*m-1) t)+b := by
  let first i := o+i*m
  let last i := o+(i+1)*m-1
  have hF (i) (hi : i < n) : first i < d.N := by dsimp [first]; nlinarith
  have hL (i) (hi : i < n) : last i < d.N := by
    have hb' : o+(i+1)*m ≤ o+n*m := by gcongr; omega
    have hp : 0 < (i+1)*m := Nat.mul_pos (by omega) hm
    dsimp [last]; omega
  have H (k) (hk : k < n) :
      ∃ t, d.mov s t ∧
       ((G t ∧ d.topc s-d.topc t ≤ a*(d.H o s-d.L (last k) t)+b) ∨
         d.topc s-d.topc t+((k:ℝ)+1)*(a*δ) ≤ a*(d.H o s-d.L (last k) t)) := by
    induction k with
    | zero => simpa [last] using hstep s (d.refl s) 0 hk
    | succ k ih =>
      have hk' : k<n := by omega
      obtain ⟨t,hst,HG|hh⟩ := ih hk'
      · refine ⟨t,hst,Or.inl ⟨HG.1,HG.2.trans ?_⟩⟩
        have Hs : d.L (last (k+1)) t ≤ d.L (last k) t :=
          d.L_index _ (by unfold last; gcongr; omega) (hL _ hk)
        gcongr
      obtain ⟨q,hq,hq'⟩ := hstep t hst (k+1) hk
      have he : last k < first (k+1) := by
        have : 0 < m*(k+1) := Nat.mul_pos hm (by omega)
        rw [Nat.mul_comm] at this
        unfold last first; omega
      have h' := mul_le_mul_of_nonneg_left (d.BC t he (hF _ hk)) ha.le
      have hd : 0 ≤ (k+1:ℝ)*(a*δ) := by
        have hp : 0 < δ := by
          have : (0:ℝ) < n := by exact_mod_cast hn
          nlinarith
        positivity
      refine ⟨q,d.trans hst hq,?_⟩
      dsimp only [last,first] at *
      rcases hq' with H1|H1
      · exact Or.inl ⟨H1.1,by linarith [H1.2]⟩
      · right; push_cast; linarith
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨t,hst,hh|hh⟩ := H k (by omega)
  · exact ⟨t,hst,hh⟩
  exfalso
  have h1 := (d.pay hst)
  have h2 := d.Llo t (last k) (hL k (by omega))
  have hx : o < d.N := by simpa [first] using hF 0 (by omega)
  have h3 := d.Hhi s o hx
  push_cast at hδ
  nlinarith


lemma budget_sub (s : S) (o n : ℕ) (hn : 0<n) (hb : o+n ≤ d.N)
    (u a δ η : ℝ) (hu : 0 < u) (ha : 0 < a) (hδ : 0 < δ)
    (hη : δ*exp (2*u/a) ≤ η)
    (hnδ : 1 < (n:ℝ)*δ) :
    ∃ t, d.mov s t ∧
      (d.found t ∨ u ≤ d.A (o+n-1) s - d.A o t) ∧
      d.topc s-d.topc t ≤ a*(d.H o s-d.L (o+n-1) t)+a*η := by
  let G t := d.found t ∨ u ≤ d.A (o+n-1) s-d.A o t
  have step : ∀ (t) (_h : d.mov s t) i (_hi : i<n), ∃ q, d.mov t q ∧
      ((G q ∧ d.topc t-d.topc q ≤ a*(d.H (o+i) t-d.L (o+i) q)+a*η) ∨
        (d.topc t-d.topc q)+a*δ ≤ a*(d.H (o+i) t-d.L (o+i) q)) := by
    intro t ht i hi
    have hb' : o+i<d.N := by omega
    obtain ⟨q,hq,hA,hQ⟩ := d.budget_index t hb' u a δ η hu ha hδ hη
    refine ⟨q,hq,?_⟩
    have hp := (d.Ls hq hb').trans (d.LH t _ hb')
    have hA' : d.topc t - d.topc q ≤ a*(d.H (o+i) t-d.L (o+i) q)+a*η := by
      nlinarith
    rcases hQ with h|h|h
    · exact Or.inl ⟨Or.inl h,hA'⟩
    · have hl := d.Am q (i:=o) (by omega) hb'
      have hv := d.Am s (i:=o+i) (by omega) (by omega : o+n-1<d.N)
      have hj := d.As ht hb'
      exact Or.inl ⟨Or.inr (by linarith),hA'⟩
    · exact Or.inr h
  have Hstep := d.budget_ascending s G o n 1 (by omega) hn (by simpa)
    a (a*η) δ ha (by linarith)
  simpa only [G,mul_one] using Hstep (by simpa [← add_assoc] using step)

/-- The macro-scale scan goes from right to left through small blocks.
Skip if lower-to-upper width is too large, unless goal encountered. -/
lemma budget_macro (s : S) (o q n : ℕ) (hn : 0 < n) (hq : 0 < q)
    (hb : o+q*n ≤ d.N)
    (u a δ η α ε : ℝ) (hu : 0 < u) (ha : 0 < a) (hδ : 0 < δ)
    (hη : δ*exp (2*u/a) ≤ η) (hnδ : 1 < (n:ℝ)*δ)
    (ha' : 0 < α) (he : 0 < ε) (hb' : 2*(a/α) ≤ 1)
    (hc : (ε+η)*exp (2*(a/α)*q) ≤ 1) (hqu : 1 < (q:ℝ)*u) :
    ∃ t, d.mov s t ∧
      ((d.found t ∧ d.topc s-d.topc t ≤ α+a*(1+η)) ∨
        (d.topc s-d.topc t)+α*ε ≤ α*(d.H o s-d.L (o+q*n-1) t)) := by
  classical
  let l := o+q*n-1
  have hpn : 0 < q*n := Nat.mul_pos hq hn
  have hlo : o ≤ l := by unfold l; omega
  have hl : l<d.N := by unfold l; omega
  have hl' := lt_of_le_of_lt hlo hl
  let x t := d.topc s-d.topc t
  let y t := α*(d.H o s-d.L l t)
  let z := α*(η+ε)
  let β := a/α
  let G t := (d.found t ∧ x t ≤ α+a*(1+η)) ∨ x t + α*ε ≤ y t
  have bpos : 0 < β := div_pos ha ha'
  have zpos : 0 < z := mul_pos ha' (add_pos_of_nonneg_of_pos
    (le_trans (by positivity : 0 ≤ δ*exp (2*u/a)) hη) he)
  have hB : β*α = a := div_mul_cancel₀ a ha'.ne'
  change 2*β ≤ 1 at hb'
  change _*exp (2*β*q) ≤ 1 at hc
  have HI (k : ℕ) (hk : k ≤ q) : ∃ t, d.mov s t ∧
      (G t ∨
        (x t + z ≤ z * exp (2*β*k) ∧ k*u ≤ (1:ℝ) ∧
        ∀ i < o+(q-k)*n, d.A i t ≤ 1 - k*u)) := by
    induction k with
    | zero =>
      refine ⟨s,d.refl _,Or.inr ⟨by simp [x],by simp,?_⟩⟩
      intro i hi; have HH : i<d.N := lt_of_lt_of_le (by simpa using hi) hb
      simpa using d.Ahi s i HH
    | succ k ih =>
      obtain ⟨t,hst,ht|⟨ht,hv,hA⟩⟩ := ih (by omega)
      · exact ⟨t,hst,Or.inl ht⟩
      let b := o+(q-(k+1))*n
      have h1 : b+n=o+(q-k)*n := by
        have H1 : q-k=q-(k+1)+1 := by omega
        unfold b; rw [H1,add_mul]; omega
      have h2 : b+n ≤ o+q*n := by rw [h1]; gcongr; omega
      obtain ⟨t',htt',hg,hw⟩ := d.budget_sub t b n hn (h2.trans hb) u a δ η hu ha hδ hη hnδ
      have hx := d.trans hst htt'
      refine ⟨t',hx,?_⟩
      have hy1 : b+n-1 ≤ l := by dsimp only [l]; omega
      have hb0 : o ≤ b := Nat.le_add_right _ _
      have hy2 : o ≤ b+n-1 := by omega
      have hl2 := lt_of_le_of_lt hy1 hl
      have hl3 : b ≤ b+n-1 := by omega
      have hl4 := lt_of_le_of_lt hl3 hl2
      have hw' : x t' - x t ≤ a*(d.H o s-d.L l t')+a*η := by
        have hA : d.H b t ≤ d.H o s := le_trans (d.Hs hst hl4) (d.H_index s hb0 hl4)
        have hL := d.L_index t' hy1 hl
        unfold x
        nlinarith [hw]
      rcases hg with hh|hh
      · have hE : exp (2*β*k) ≤ exp (2*β*q) := by
          gcongr; omega
        have hv : z*exp (2*β*q) ≤ α := by
          unfold z; nlinarith [mul_le_mul_of_nonneg_left hc ha'.le]
        have hT : x t ≤ α := by nlinarith
        exact Or.inl (Or.inl ⟨hh,by nlinarith [d.Hhi s o hl',d.Llo t' l hl]⟩)
      by_cases H : x t'+α*ε ≤ y t'
      · exact Or.inl (Or.inr H)
      have hy : y t' ≤ x t'+α*ε := le_of_not_ge H

      have hrec : (x t'+z)*(1-β) ≤ (x t+z) := by
        unfold y at hy
        unfold z
        have Hh := mul_le_mul_of_nonneg_left hy bpos.le

        simp only [mul_add, ← mul_assoc,hB] at Hh
        have h3 (c : ℝ) : β*(α*c) = a*c := by rw [← mul_assoc,hB]
        nlinarith [h3 (η+ε)]
      have hxp : x t'+z ≥ 0 := by have H := d.pay hx; unfold x; linarith

      have hiter : (x t'+z) ≤ z * exp (2*β*(k+1)) := by
        have hg : 1 ≤ (1-β)*exp (2*β) := by
          have h := Real.add_one_le_exp (2*β)
          nlinarith
        apply le_trans (b:=(z*exp (2*β*k))*exp (2*β))
        · have HH := mul_le_mul_of_nonneg_right (hrec.trans ht) (exp_nonneg (2*β))
          exact le_trans (by
            rw [mul_assoc]; exact le_mul_of_one_le_right hxp hg) HH
        · rw [mul_assoc,← exp_add]
          apply le_of_eq; ring_nf
      refine Or.inr ⟨by push_cast; exact hiter,?_,?_⟩
      · have H := hA (b+n-1) (by omega)
        have H1 := d.Alo t' b hl4
        push_cast; linarith
      · intro i hi
        have H := hA (b+n-1) (by omega)
        change i < b at hi
        have H1 := d.Am t' hi.le hl4
        push_cast; linarith
  obtain ⟨t,hst,h|h⟩ := HI q le_rfl
  · exact ⟨t,hst,h⟩
  · exfalso
    linarith [h.2.1]

lemma complete_search (s : S) (N q n : ℕ) (hn : 0<n) (hq : 0<q)
    (hN : 0<N) (hb : N*(q*n) ≤ d.N)
    (u a δ η α ε : ℝ) (hu : 0 < u) (ha : 0 < a) (hδ : 0 < δ)
    (hη : δ*exp (2*u/a) ≤ η) (hnδ : 1 < (n:ℝ)*δ)
    (ha' : 0 < α) (he : 0 < ε) (hb' : 2*(a/α) ≤ 1)
    (hc : (ε+η)*exp (2*(a/α)*q) ≤ 1) (hqu : 1 < (q:ℝ)*u) (ht : 1 < (N:ℝ)*ε) :
    ∃ t, d.mov s t ∧ d.found t ∧ d.topc s-d.topc t ≤ 2*α+a*(1+η) := by
  let m := q*n
  have hm : 0 < m := Nat.mul_pos hq hn
  obtain ⟨t,hst,hd,hH⟩ := d.budget_ascending s d.found 0 N m hm hN
    (by simpa using hb) α (α+a*(1+η)) ε ha' ht (by
    intro t hst i hi
    simp only [zero_add]
    have h1 : i*m+m ≤ d.N := by
      rw [show i*m+m=(i+1)*m by ring]
      exact le_trans (Nat.mul_le_mul_right m hi) hb
    obtain ⟨t',h',hH⟩ :=
      d.budget_macro t (i*m) q n hn hq h1 u a δ η α ε hu ha hδ hη hnδ ha' he hb' hc hqu
    rw [show (i+1)*m=i*m+q*n by dsimp [m]; ring]
    refine ⟨t',h',?_⟩
    rcases hH with h|h
    · left
      have hh : i*m ≤ i*m+m-1 := by omega
      have hk : i*m+m-1 < d.N := by omega
      have ht : d.L (i*m+m-1) t' ≤ d.H (i*m) t := (d.Ls h' hk).trans
        ((d.L_index t hh hk).trans (d.LH _ _ (by omega)))
      exact ⟨h.1,h.2.trans (le_add_of_nonneg_left (mul_nonneg ha'.le (sub_nonneg.mpr ht)))⟩
    · exact Or.inr h)
  refine ⟨t,hst,hd,?_⟩
  have hh : 0<N*m := Nat.mul_pos hN hm
  have hh' : N*m ≤ d.N := hb
  have h1 := d.Hhi s 0 (by omega)
  have h2 := d.Llo t (0+N*m-1) (by omega)
  nlinarith

end Arena
end FourierLLogL.Compress

end OAI
