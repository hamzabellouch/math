import OAI.NumberTheory.GaussianMoat.PointEnrichment

namespace OAI

universe uOmega uCapitalKappa uAlpha uBeta uGamma uIota

namespace GaussianMoat

section
open scoped BigOperators Classical

structure TimeLaw where
  last : ℕ
  law : FinLaw (Fin (last+1))

noncomputable def endpointTime (a n : ℕ) :
    Bool × (Fin (a+1) × (Fin (n+1) × Fin (n+1))) → Fin (a+n+1) :=
  fun v => ⟨v.2.1.val+(if v.1 then v.2.2.1.val else v.2.2.2.val),by
    split_ifs <;> omega⟩

noncomputable def TimeLaw.step (P : TimeLaw) (z : ℕ → GaussianInt) (n : ℕ) : TimeLaw where
  last := P.last+n
  law := ((FinLaw.uniform Bool).joint (fun _ => P.law.joint (fun a =>
    differenceLaw (fun t => z (a.val+t)) n))).map (endpointTime P.last n)

lemma SplitSieve.pointEntropy_map {Ω : Type uOmega} {Κ : Type uCapitalKappa} [Fintype Ω] [Fintype Κ]
    (s : SplitSieve) (p : FinLaw Ω) (f : Ω → Κ) (Z : Κ → GaussianInt) (b : ℕ) :
    s.pointEntropy (p.map f) Z b = s.pointEntropy p (Z ∘ f) b := by
  unfold pointEntropy FinLaw.signedEntropy FinLaw.orderedEntropy
  simp only [FinLaw.Hf_map]
  rfl

lemma SplitSieve.pointEntropy_joint_fst {Ω : Type uOmega} {Κ : Type uCapitalKappa} [Fintype Ω] [Fintype Κ]
    (s : SplitSieve) (p : FinLaw Ω) (q : Ω → FinLaw Κ) (Z : Ω → GaussianInt) (b : ℕ) :
    s.pointEntropy (p.joint q) (fun v => Z v.1) b = s.pointEntropy p Z b := by
  have h := s.pointEntropy_map (p.joint q) Prod.fst Z b
  rw [FinLaw.joint_map_fst] at h
  exact h.symm

lemma shifted_walk_injective (z : ℕ → GaussianInt) (hz : Function.Injective z) (a : ℕ) :
    Function.Injective (fun t => z (a+t)) := by intro i j h; have := hz h; omega

lemma walk_pair_displacement (z : ℕ → GaussianInt) {D : ℝ} (hD : 0 ≤ D)
    (hstep : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D) (a n i j : ℕ)
    (hi : i ≤ n) (hj : j ≤ n) :
    ‖((z (a+i)-z (a+j):GaussianInt):ℂ)‖ ≤ D*n := by
  have h := walkSegment_dist_le (fun t => z (a+t)) hD
    (fun t _ => by simpa only [Nat.add_assoc] using hstep (a+t)) hi hj
  simpa only [dist_eq_norm,map_sub] using h

theorem TimeLaw.step_enrichment (P : TimeLaw) (s : SplitSieve)
    (z : ℕ → GaussianInt) {D F : ℝ} (hD : 1 ≤ D)
    (hstep : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D) {n b q : ℕ}
    (hn : 1 ≤ n) (hb : 0 < b) (hbq : b < q) (hq : q ≤ s.primes.card)
    (hF : ∀ a : Fin (P.last+1), F ≤ s.freshCoordinate
      (differenceLaw (fun t => z (a.val+t)) n)
      (fun ij => z (a.val+ij.1.val)) (fun ij => z (a.val+ij.2.val)) b (by omega)) :
    (b:ℝ)*((q-b:ℕ)*F+s.pointEntropy P.law (fun a => z a.val) q-
      2*(Real.log 36+2*Real.log (D*n))) ≤
      2*(q:ℝ)*s.pointEntropy (P.step z n).law (fun a => z a.val) b := by
  let K := P.law.joint (fun a => differenceLaw (fun t => z (a.val+t)) n)
  let X := fun v : Fin (P.last+1) × (Fin (n+1) × Fin (n+1)) => z (v.1.val+v.2.1.val)
  let Y := fun v : Fin (P.last+1) × (Fin (n+1) × Fin (n+1)) => z (v.1.val+v.2.2.val)
  let Z := fun v : Fin (P.last+1) × (Fin (n+1) × Fin (n+1)) => z v.1.val
  have hF' : F ≤ s.freshCoordinate K X Y b (by omega) := by
    have hh := s.freshCoordinate_joint_ge P.law
      (fun a => differenceLaw (fun t => z (a.val+t)) n)
      (fun a ij => z (a.val+ij.1.val)) (fun a ij => z (a.val+ij.2.val)) (by omega : b < s.primes.card)
    apply le_trans _ hh
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
      mul_le_mul_of_nonneg_left (hF a) (P.law.nonneg a))
    simpa only [← Finset.sum_mul,P.law.sum_one,one_mul] using hsum
  have hDn : 1 ≤ D*n := one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast hn)
  have h := s.actual_enrichment K X Y Z hb hbq hq hF' hDn
    (fun v => walk_pair_displacement z (by linarith) hstep _ _ _ _ (by omega) (by omega))
    (fun v => by
      change ‖((z (v.1.val+v.2.1.val)-z v.1.val:GaussianInt):ℂ)‖ ≤ D*n
      simpa only [Nat.add_zero] using
        walk_pair_displacement z (by linarith) hstep v.1.val n v.2.1.val 0 (by omega) (by omega))
  have hZ := s.pointEntropy_joint_fst P.law
    (fun a => differenceLaw (fun t => z (a.val+t)) n) (fun a => z a.val) q
  rw [hZ] at h
  have hout : s.pointEntropy (P.step z n).law (fun a => z a.val) b =
      s.pointEntropy ((FinLaw.uniform Bool).joint (fun _ => K))
        (fun v => if v.1 then X v.2 else Y v.2) b := by
    change s.pointEntropy (((FinLaw.uniform Bool).joint (fun _ => K)).map
      (endpointTime P.last n)) (fun a => z a.val) b = _
    rw [s.pointEntropy_map]
    apply congrArg (fun F => s.pointEntropy ((FinLaw.uniform Bool).joint (fun _ => K)) F b)
    funext v
    simp only [Function.comp_def,endpointTime,X,Y]
    split_ifs <;> rfl
  rw [hout]
  exact h

end

namespace FinLaw

section
open scoped BigOperators Classical
variable {Ω : Type uOmega} [Fintype Ω]

noncomputable def prob (p : FinLaw Ω) (E : Ω → Prop) : ℝ := ∑ ω, if E ω then p ω else 0

lemma prob_nonneg (p : FinLaw Ω) (E : Ω → Prop) : 0 ≤ p.prob E := by
  exact Finset.sum_nonneg (fun ω _ => by split_ifs <;> simp [p.nonneg ω])

lemma prob_le_one (p : FinLaw Ω) (E : Ω → Prop) : p.prob E ≤ 1 := by
  rw [← p.sum_one]
  exact Finset.sum_le_sum (fun ω _ => by split_ifs <;> simp [p.nonneg ω])

lemma prob_mono (p : FinLaw Ω) {E F : Ω → Prop} (h : ∀ ω, E ω → F ω) :
    p.prob E ≤ p.prob F := by
  apply Finset.sum_le_sum
  intro ω _
  by_cases he : E ω
  · simp [he,h ω he]
  · by_cases hf : F ω <;> simp [he,hf,p.nonneg ω]

noncomputable def iid (p : FinLaw Ω) (n : ℕ) : FinLaw (Fin n → Ω) where
  mass := fun x => ∏ i, p (x i)
  nonneg := fun x => Finset.prod_nonneg (fun i _ => p.nonneg _)
  sum_one := by
    rw [← Fintype.prod_sum]
    simp only [p.sum_one,Finset.prod_const_one]

@[simp] lemma iid_mass (p : FinLaw Ω) (n : ℕ) (x : Fin n → Ω) :
    p.iid n x = ∏ i, p (x i) := rfl

lemma iid_product (p : FinLaw Ω) (n : ℕ) (f : Ω → ℝ) :
    (∑ x : Fin n → Ω, p.iid n x * ∏ i, f (x i)) = (∑ ω, p ω*f ω)^n := by
  simp only [iid_mass,← Finset.prod_mul_distrib]
  exact (Fintype.sum_pow (fun ω => p ω*f ω) n).symm

lemma exp_neg_le_quadratic {t : ℝ} (ht : 0 ≤ t) : Real.exp (-t) ≤ 1-t+t^2/2 := by
  have hm : Monotone (fun x : ℝ => 1-x+x^2/2-Real.exp (-x)) := by
    apply monotone_of_hasDerivAt_nonneg (f' := fun x => -1+x+Real.exp (-x))
    · intro x
      convert! (((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).add
        (((hasDerivAt_id x).pow 2).div_const 2)).sub
          (((hasDerivAt_id x).neg).exp) using 1
      simp only [Pi.neg_apply,id_eq]
      ring
    · intro x
      have h := Real.add_one_le_exp (-x)
      change 0 ≤ -1+x+Real.exp (-x)
      linarith
  have h := hm ht
  simpa using h

lemma prob_le_exp_moment (p : FinLaw Ω) (S : Ω → ℝ) {t a : ℝ} (ht : 0 ≤ t) :
    p.prob (fun ω => S ω ≤ a) ≤ Real.exp (t*a) * ∑ ω, p ω*Real.exp (-t*S ω) := by
  have h (ω : Ω) : (if S ω ≤ a then p ω else 0) ≤
      Real.exp (t*a)*(p ω*Real.exp (-t*S ω)) := by
    by_cases hh : S ω ≤ a
    · rw [ite_eq_left hh]
      have he : 1 ≤ Real.exp (t*a+-t*S ω) := Real.one_le_exp_iff.mpr (by nlinarith)
      calc
        p ω = p ω*1 := by ring
        _ ≤ p ω*Real.exp (t*a+-t*S ω) := mul_le_mul_of_nonneg_left he (p.nonneg ω)
        _ = Real.exp (t*a)*(p ω*Real.exp (-t*S ω)) := by rw [Real.exp_add]; ring
    · rw [ite_eq_right hh]
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (p.nonneg ω) (Real.exp_pos _).le)
  simpa only [prob,Finset.mul_sum] using Finset.sum_le_sum (s := Finset.univ) (fun ω _ => h ω)

lemma bernoulli_moment (p : FinLaw Ω) (E : Ω → Prop) (t : ℝ) :
    (∑ ω, p ω*Real.exp (-t*(if E ω then 1 else 0))) =
      1+p.prob E*(Real.exp (-t)-1) := by
  have he (ω : Ω) : p ω*Real.exp (-t*(if E ω then 1 else 0)) =
      p ω+(if E ω then p ω else 0)*(Real.exp (-t)-1) := by
    split_ifs <;> simp only [mul_one,mul_zero,Real.exp_zero,zero_mul,add_zero]
    ring
  simp only [he,Finset.sum_add_distrib,← Finset.sum_mul,p.sum_one,prob]

theorem iid_lower_tail (p : FinLaw Ω) (E : Ω → Prop) (n : ℕ)
    {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 ≤ δ) (hp : μ ≤ p.prob E) :
    (p.iid n).prob (fun x => (∑ i : Fin n, if E (x i) then (1:ℝ) else 0) ≤ n*(μ-δ)) ≤
      Real.exp (- (n:ℝ)*δ^2/(2*μ)) := by
  let t := δ/μ
  have ht : 0 ≤ t := div_nonneg hδ hμ.le
  have hm := prob_le_exp_moment (p.iid n)
    (fun x => ∑ i : Fin n, if E (x i) then (1:ℝ) else 0) ht (a := n*(μ-δ))
  have hfactor : (∑ x : Fin n → Ω, p.iid n x *
      Real.exp (-t*∑ i : Fin n, if E (x i) then 1 else 0)) =
      (1+p.prob E*(Real.exp (-t)-1))^n := by
    simp_rw [Finset.mul_sum,Real.exp_sum]
    rw [iid_product p n (fun ω => Real.exp (-t*(if E ω then 1 else 0))),bernoulli_moment]
  rw [hfactor] at hm
  have hbase0 : 0 ≤ 1+p.prob E*(Real.exp (-t)-1) := by
    rw [← bernoulli_moment]
    exact Finset.sum_nonneg (fun ω _ => mul_nonneg (p.nonneg ω) (Real.exp_pos _).le)
  have hbase : 1+p.prob E*(Real.exp (-t)-1) ≤ Real.exp (μ*(Real.exp (-t)-1)) := by
    have hn : Real.exp (-t)-1 ≤ 0 := by
      have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
      linarith
    have h1 := mul_le_mul_of_nonpos_right hp hn
    have h2 := Real.add_one_le_exp (μ*(Real.exp (-t)-1))
    linarith
  have hpw := pow_le_pow_left₀ hbase0 hbase n
  have hmul := mul_le_mul_of_nonneg_left hpw (Real.exp_pos (t*(n*(μ-δ)))).le
  apply hm.trans (hmul.trans ?_)
  rw [← Real.exp_nat_mul,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he := exp_neg_le_quadratic ht
  have h := mul_le_mul_of_nonneg_left he (mul_nonneg (Nat.cast_nonneg n) hμ.le)
  have hid : t*((n:ℝ)*(μ-δ))+(n:ℝ)*μ*(-t+t^2/2) = -(n:ℝ)*δ^2/(2*μ) := by
    dsimp [t]
    field_simp
    ring
  rw [← hid]
  nlinarith

end

section
open scoped BigOperators Classical
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]

lemma le_map_apply (p : FinLaw Ω) (X : Ω → α) (ω : Ω) : p ω ≤ p.map X (X ω) := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun ν => if X ν=X ω then p ν else 0)
    (fun ν _ => by split_ifs <;> simp [p.nonneg ν]) (Finset.mem_univ ω)
  simpa only [ite_true,map_mass] using h

noncomputable def conditionOn (p : FinLaw Ω) (X : Ω → α) (a : α) : FinLaw Ω :=
  if h : p.map X a = 0 then p else {
    mass := fun ω => if X ω=a then p ω/(p.map X a) else 0
    nonneg := fun ω => by split_ifs; exact div_nonneg (p.nonneg ω) ((p.map X).nonneg a); rfl
    sum_one := by
      have he : (∑ ω, if X ω=a then p ω/(p.map X a) else 0) =
          (∑ ω, if X ω=a then p ω else 0)/(p.map X a) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro ω _
        split_ifs <;> simp
      rw [he,← map_mass,div_self h] }

lemma conditionOn_weight (p : FinLaw Ω) (X : Ω → α) (a : α) (ω : Ω) :
    p.map X a * p.conditionOn X a ω = if X ω=a then p ω else 0 := by
  by_cases hz : p.map X a=0
  · rw [hz,zero_mul]
    split_ifs with hh
    · have h := p.le_map_apply X ω
      rw [hh,hz] at h
      exact (le_antisymm h (p.nonneg ω)).symm
    · rfl
  · unfold conditionOn
    rw [dite_eq_right hz]
    change p.map X a * (if X ω=a then p ω/(p.map X a) else 0) = _
    by_cases hx : X ω=a
    · rw [ite_eq_left hx,ite_eq_left hx]
      exact mul_div_cancel₀ _ hz
    · rw [ite_eq_right hx,ite_eq_right hx,mul_zero]

lemma disintegration (p : FinLaw Ω) (X : Ω → α) :
    (p.map X).joint (p.conditionOn X) = p.map (fun ω => (X ω,ω)) := by
  ext ⟨a,ω⟩
  rw [joint_mass,conditionOn_weight,map_mass]
  simp only [Prod.mk.injEq]
  rw [Finset.sum_eq_single ω]
  · simp
  · intro ν _ hn
    simp [hn]
  · simp

lemma conditionOn_mixture (p : FinLaw Ω) (X : Ω → α) :
    (p.map X).mix (p.conditionOn X) = p := by
  rw [← joint_map_snd,disintegration,map_comp]
  exact p.map_id

lemma conditionOn_observation (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.H (fun ω => (X ω,Y ω)) = p.H X+∑ a, p.map X a*(p.conditionOn X a).H Y := by
  have h := (p.map X).Hf_joint_pair (p.conditionOn X) Y
  rw [disintegration,Hf_map] at h
  simpa only [Hf_eq_H,H,Function.comp_def] using h

lemma condH_eq_conditionOn (p : FinLaw Ω) (Y : Ω → β) (X : Ω → α) :
    p.condH Y X = ∑ a, p.map X a*(p.conditionOn X a).H Y := by
  unfold condH
  rw [p.H_pair_comm Y X,p.conditionOn_observation X Y]
  ring

lemma prob_map (p : FinLaw Ω) (f : Ω → α) (E : α → Prop) :
    (p.map f).prob E = p.prob (fun ω => E (f ω)) := by
  simp only [prob,map_mass]
  have h (a : α) : (if E a then ∑ ω, if f ω=a then p ω else 0 else 0) =
      ∑ ω, if f ω=a then (if E a then p ω else 0) else 0 := by
    by_cases he : E a <;> simp [he]
  simp_rw [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp

lemma prob_joint (p : FinLaw Ω) (q : Ω → FinLaw α) (E : Ω × α → Prop) :
    (p.joint q).prob E = ∑ ω, p ω*(q ω).prob (fun a => E (ω,a)) := by
  simp only [prob,Fintype.sum_prod_type,joint_mass,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

lemma conditionOn_prob (p : FinLaw Ω) (X : Ω → α) (E : Ω → Prop) :
    (∑ a, p.map X a*(p.conditionOn X a).prob E) = p.prob E := by
  rw [← prob_joint (p.map X) (p.conditionOn X) (fun v => E v.2),disintegration,prob_map]

lemma prob_le_expect_div (p : FinLaw Ω) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω)
    {a : ℝ} (ha : 0 < a) :
    p.prob (fun ω => a < f ω) ≤ (∑ ω, p ω*f ω)/a := by
  apply (le_div_iff₀ ha).mpr
  rw [prob,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hh : a < f ω
  · simp only [ite_eq_left hh]
    exact mul_le_mul_of_nonneg_left hh.le (p.nonneg ω)
  · simp only [ite_eq_right hh,zero_mul]
    exact mul_nonneg (p.nonneg ω) (hf ω)

lemma prob_compl (p : FinLaw Ω) (E : Ω → Prop) :
    p.prob (fun ω => ¬ E ω) = 1-p.prob E := by
  have h : p.prob (fun ω => ¬ E ω)+p.prob E = 1 := by
    rw [prob,prob,← Finset.sum_add_distrib,← p.sum_one]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases he : E ω <;> simp [he]
  linarith

lemma prob_inter_ge (p : FinLaw Ω) (E F : Ω → Prop) :
    p.prob E-p.prob (fun ω => ¬ F ω) ≤ p.prob (fun ω => E ω ∧ F ω) := by
  rw [prob,prob,prob,← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases he : E ω <;> by_cases hf : F ω <;> simp [he,hf,p.nonneg ω]

lemma prob_exists_le_sum {ι : Type uIota} [Fintype ι] (p : FinLaw Ω) (E : ι → Ω → Prop) :
    p.prob (fun ω => ∃ i, E i ω) ≤ ∑ i, p.prob (E i) := by
  simp only [prob]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hh : ∃ i, E i ω
  · obtain ⟨i,hi⟩ := hh
    rw [ite_eq_left ⟨i,hi⟩]
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun i => if E i ω then p ω else 0)
      (fun j _ => by split_ifs <;> simp [p.nonneg ω]) (Finset.mem_univ i)
    simpa only [ite_eq_left hi] using h
  · simp only [ite_eq_right hh]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> simp [p.nonneg ω])

end

open scoped BigOperators Classical
variable {Ω : Type uOmega} {Κ : Type uCapitalKappa} {ι : Type uIota} {α : Type uAlpha} {β : Type uBeta} [Fintype Ω] [Fintype Κ] [Fintype ι]

lemma map_equiv_mass (p : FinLaw Ω) (e : Ω ≃ Κ) (x : Κ) :
    p.map e x = p (e.symm x) := by
  rw [map_mass,Finset.sum_eq_single (e.symm x)]
  · simp
  · intro ω _ hn
    have hh : e ω ≠ x := by intro h; exact hn (e.injective (by simpa using h))
    simp [hh]
  · simp

lemma entropy_map_equiv (p : FinLaw Ω) (e : Ω ≃ Κ) :
    (p.map e).entropy = p.entropy := by
  simp only [entropy,entropySum,map_equiv_mass]
  exact e.symm.sum_comp (fun ω => Real.negMulLog (p ω))

lemma iid_succ (p : FinLaw Ω) (n : ℕ) :
    p.iid (n+1) = (p.joint (fun _ => p.iid n)).map
      (Fin.consEquiv (fun _ : Fin (n+1) => Ω)) := by
  ext x
  rw [map_equiv_mass]
  change (∏ i : Fin (n+1), p (x i)) = p (x 0)*(∏ i : Fin n, p (x i.succ))
  exact Fin.prod_univ_succ _

lemma entropy_iid (p : FinLaw Ω) (n : ℕ) :
    (p.iid n).entropy = n*p.entropy := by
  induction n with
  | zero =>
    have he : p.iid 0 = uniform (Fin 0 → Ω) := by ext x; simp [uniform_mass]
    rw [he]
    simp [entropy,entropySum,uniform_mass]
  | succ n ih =>
    rw [iid_succ,entropy_map_equiv,entropy_joint]
    simp only [ih,← Finset.sum_mul,p.sum_one,one_mul,Nat.cast_add,Nat.cast_one]
    ring

lemma iid_split (p : FinLaw Ω) (n : ℕ) (i : Fin n) :
    p.iid n = (p.joint (fun _ =>
      ({ mass := fun x : (j : {j : Fin n // j ≠ i}) → Ω => ∏ j, p (x j)
         nonneg := fun x => Finset.prod_nonneg (fun j _ => p.nonneg _)
         sum_one := by rw [← Fintype.prod_sum]; simp only [p.sum_one,Finset.prod_const_one] } :
            FinLaw ((j : {j : Fin n // j ≠ i}) → Ω)))).map
      (Equiv.piSplitAt i (fun _ : Fin n => Ω)).symm := by
  ext x
  rw [map_equiv_mass]
  change (∏ j : Fin n, p (x j)) = p (x i)*(∏ j : {j : Fin n // j ≠ i}, p (x j))
  rw [← Fintype.prod_subtype_mul_prod_subtype (p := fun j : Fin n => j=i)]
  have he : (∏ j : {j : Fin n // j=i}, p (x j)) = p (x i) := by
    have hsub := Finset.prod_subtype (F := inferInstance) (p := fun j : Fin n => j=i) ({i} : Finset (Fin n)) (by simp) (fun j => p (x j))
    simpa using hsub.symm
  convert! congrArg (fun v => v*(∏ j : {j : Fin n // j ≠ i}, p (x j))) he using 1
  congr 1
  congr 1
  ext j
  simp only [Finset.mem_univ]

lemma iid_map_eval (p : FinLaw Ω) (n : ℕ) (i : Fin n) :
    (p.iid n).map (fun x => x i) = p := by
  rw [iid_split p n i,map_comp]
  have he : ((fun x : Fin n → Ω => x i) ∘ (Equiv.piSplitAt i (fun _ : Fin n => Ω)).symm) = Prod.fst := by
    funext x
    simp [Equiv.piSplitAt]
  rw [he,joint_map_fst]

end FinLaw
end GaussianMoat

end OAI
