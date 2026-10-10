import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.RelationDestinations
import OAI.Combinatorics.MatchingCount.Probability.Mean

namespace OAI

namespace MatchingFPRAS.Replica

section

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]

variable (p : I → Ω → ℝ)

noncomputable def localVariance (π : Ω → ℝ) (a : Ω → ℝ) : ℝ :=
  ∑ u, π u*(a u-∑ v, π v*a v)^2

def PairPoincare (x y : I) (Q : PairCapacity p x y) (C : ℝ) : Prop :=
  ∀ a b : Ω → ℝ, localVariance (p x) a ≤ C*localEnergy Q.q (fun z => a z.1+b z.2)

omit [Fintype I] [DecidableEq Ω] in
lemma invariant_update (i : I) (f : (I → Ω) → ℝ) (hi : average p i f = f)
    (s : I → Ω) (a : Ω) : f (Function.update s i a) = f s := by
  rw [← hi]
  exact average_update p i a f s

omit [DecidableEq Ω] in
lemma pairEnergy_shift_invariant (x y : I) (Q : PairCapacity p x y)
    (f d : (I → Ω) → ℝ) (hx : average p x d = d) (hy : average p y d = d) :
    pairEnergy p x y Q (f-d) = pairEnergy p x y Q f := by
  have he (s : I → Ω) : slice x y (f-d) s = (fun a => slice x y f s a-d s) := by
    funext a
    change f (replacePair x y s a)-d (Function.update (Function.update s x a.1) y a.2) = _
    rw [invariant_update p y d hy,invariant_update p x d hx]
    rfl
  unfold pairEnergy
  simp_rw [he,localEnergy_shift]

omit [DecidableEq Ω] in
lemma pair_poincare_global (hp : ∀ i a, 0 ≤ p i a) (hs : ∀ i, ∑ a, p i a = 1)
    (x y : I) (hxy : x ≠ y) (Q : PairCapacity p x y) (C : ℝ) (hQ : PairPoincare p x y Q C)
    (h k : (I → Ω) → ℝ) (hh : average p x h = 0) (hhy : average p y h = h)
    (hkx : average p x k = k) : dot p h h ≤ C*pairEnergy p x y Q (h+k) := by
  have hc (s : I → Ω) : (∑ a, p x a*h (Function.update s x a)) = 0 := by
    change average p x h s = 0
    rw [hh]; rfl
  have he (s : I → Ω) : (fun a : Ω × Ω =>
      h (Function.update s x a.1)+k (Function.update s y a.2)) = slice x y (h+k) s := by
    funext a
    change _ = h (Function.update (Function.update s x a.1) y a.2)+
      k (Function.update (Function.update s x a.1) y a.2)
    rw [invariant_update p y h hhy,Function.update_comm hxy,invariant_update p x k hkx]
  have hi (s : I → Ω) : average p x (fun s => (h s)^2) s ≤
      C*localEnergy Q.q (slice x y (h+k) s) := by
    have hi := hQ (fun a => h (Function.update s x a)) (fun b => k (Function.update s y b))
    unfold localVariance at hi
    rw [hc,he] at hi
    simpa only [sub_zero,average_apply] using hi
  have hi := mean_mono p hp hi
  rw [mean_average p hs,mean_square,mean_mul] at hi
  exact hi

omit [DecidableEq Ω] in
lemma projection_contraction (hp : ∀ i a, 0 ≤ p i a) (P : Projection p) (f : (I → Ω) → ℝ) :
    dot p (P.op f) (P.op f) ≤ dot p f f := by
  have hh := dot_nonneg p hp (f-P.op f)
  rw [projection_pythagoras] at hh
  linarith

noncomputable def baseEnergy (i : I) (f : (I → Ω) → ℝ) : ℝ :=
  dot p (f-average p i f) (f-average p i f)

omit [DecidableEq Ω] in
lemma baseEnergy_nonneg (hp : ∀ i a, 0 ≤ p i a) (i : I) (f : (I → Ω) → ℝ) :
    0 ≤ baseEnergy p i f := dot_nonneg p hp _

variable [LinearOrder I]

omit [DecidableEq Ω] in
lemma increment_base_bound (hp : ∀ i a, 0 ≤ p i a) (hs : ∀ i, ∑ a, p i a = 1)
    (i : I) (f : (I → Ω) → ℝ) :
    dot p (increment p Finset.univ i f) (increment p Finset.univ i f) ≤ baseEnergy p i f := by
  let P := listProjection p hs ((Finset.univ.filter (i < ·)).toList)
  have he : increment p Finset.univ i f = P.op (f-average p i f) := by
    change avgList p _ f-average p i (avgList p _ f) = avgList p _ (f-average p i f)
    rw [map_sub,average_comm_list]
  rw [he]
  exact projection_contraction p hp P (f-average p i f)

omit [DecidableEq Ω] in
lemma one_pair (hp : ∀ i a, 0 ≤ p i a) (hs : ∀ i, ∑ a, p i a = 1)
    (x y : I) (hxy : x < y) (Q : PairCapacity p x y) (L : ℝ) (hL : 0 ≤ L)
    (hQ : PairPoincare p x y Q (2*L)) (f : (I → Ω) → ℝ) :
    dot p (increment p Finset.univ x f) (increment p Finset.univ x f) ≤
      4*L*pairEnergy p x y Q f+8*L*dot p (residual p x y f) (residual p x y f) := by
  let c := pairCondition p x y f
  let h := increment p Finset.univ x f
  let k := average p x c-average p x (average p y c)
  let d := average p x (average p y c)
  have hh : h = average p y c-d := increment_pair_formula p hs x y hxy f
  have hhy : average p y h = h := by
    rw [hh,map_sub]
    change average p y (average p y c)-average p y (average p x (average p y c)) =
      average p y c-average p x (average p y c)
    rw [average_comm p y x,average_idem p hs]
  have hkx : average p x k = k := by
    change average p x (average p x c-average p x (average p y c)) = _
    rw [map_sub,average_idem p hs,average_idem p hs]
  have hdx : average p x d = d := average_idem p hs x _
  have hdy : average p y d = d := by
    change average p y (average p x (average p y c)) = average p x (average p y c)
    rw [average_comm,average_idem p hs]
  have hhk : h+k = c-residual p x y f-d := by
    rw [hh,residual_formula]
    change (average p y c-d)+(average p x c-d) =
      c-(c-average p x c-average p y c+average p x (average p y c))-d
    dsimp [d]; abel
  have hpq := pair_poincare_global p hp hs x y (ne_of_lt hxy) Q (2*L) hQ h k
    (increment_center p hs Finset.univ x f) hhy hkx
  rw [hhk,pairEnergy_shift_invariant p x y Q _ d hdx hdy] at hpq
  have hc : pairEnergy p x y Q c ≤ pairEnergy p x y Q f := by
    apply pairEnergy_avgList p hp hs (outside x y) x y _ Q f
    intro i hi
    have hi : x < i ∧ i ≠ y := by simpa [outside] using hi
    exact ⟨ne_of_gt hi.1,hi.2⟩
  have he := pairEnergy_sub p hp x y Q c (residual p x y f)
  have hr := pairEnergy_bound p hp hs x y Q (residual p x y f)
  nlinarith [mul_nonneg hL (sub_nonneg.mpr hc),mul_nonneg hL (sub_nonneg.mpr hr),
    mul_nonneg hL (sub_nonneg.mpr he)]

end

section

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [LinearOrder I]
  [Fintype Ω] [DecidableEq Ω]

variable (p : I → Ω → ℝ)

noncomputable def allowed (guides : I → Finset I) : Finset (I × I) :=
  Finset.univ.filter (fun z => z.2 ∈ guides z.1)

omit [LinearOrder I] in
lemma sum_allowed (guides : I → Finset I) (f : I × I → ℝ) :
    (∑ z ∈ allowed guides, f z) = ∑ x, ∑ y ∈ guides x, f (x,y) := by
  classical
  simp only [allowed,Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro x _
  simpa only [Finset.filter_univ_mem] using
    (Finset.sum_filter (s := Finset.univ) (fun y => y ∈ guides x) (fun y => f (x,y))).symm

noncomputable def pairTotal (guides : I → Finset I) (Q : ∀ x y, PairCapacity p x y)
    (f : (I → Ω) → ℝ) : ℝ := ∑ x, ∑ y ∈ guides x, pairEnergy p x y (Q x y) f

noncomputable def baseTotal (base : Finset I) (f : (I → Ω) → ℝ) : ℝ :=
  ∑ x ∈ base, baseEnergy p x f

noncomputable def scanEnergy (guides : I → Finset I) (base : Finset I)
    (Q : ∀ x y, PairCapacity p x y) (f : (I → Ω) → ℝ) : ℝ :=
  (pairTotal p guides Q f+baseTotal p base f)/(2*((∑ x, (guides x).card)+base.card : ℕ))

omit [DecidableEq Ω] in
theorem replica_gap (hp : ∀ i a, 0 ≤ p i a) (hs : ∀ i, ∑ a, p i a = 1)
    (guides : I → Finset I) (base : Finset I) (hbase : base.Nonempty)
    (q : ℕ) (L : ℝ) (hL : 0 < L) (hq : (q:ℝ) = 32*L)
    (hn : ∀ x ∉ base, (guides x).card = q) (hb : ∀ x ∈ base, guides x = ∅)
    (horder : ∀ x y, y ∈ guides x → x < y)
    (Q : ∀ x y, PairCapacity p x y)
    (hQ : ∀ x y, y ∈ guides x → PairPoincare p x y (Q x y) (2*L))
    (f : (I → Ω) → ℝ) :
    variance p f ≤ (8*((∑ x, (guides x).card)+base.card : ℕ)/3:ℝ)*
      scanEnergy p guides base Q f := by
  classical
  let H : I → ℝ := fun x => dot p (increment p Finset.univ x f) (increment p Finset.univ x f)
  let B := ∑ x ∈ base, H x
  let A := ∑ x ∈ baseᶜ, H x
  let E := pairTotal p guides Q f
  let F := baseTotal p base f
  have hvar : variance p f = A+B := by
    have h := Finset.sum_add_sum_compl base H
    rw [martingale_variance]
    change (∑ x, H x) = A+B
    dsimp [A,B]; linarith
    exact hs
  have hbaseBound : B ≤ F := Finset.sum_le_sum (fun x _ => increment_base_bound p hp hs x f)
  have hE : 0 ≤ E := Finset.sum_nonneg (fun x _ => Finset.sum_nonneg
    (fun y _ => pairEnergy_nonneg p hp x y (Q x y) f))
  have hF : 0 ≤ F := Finset.sum_nonneg (fun x _ => baseEnergy_nonneg p hp x f)
  have hlhs : (∑ x, ∑ y ∈ guides x, H x) = (q:ℝ)*A := by
    calc
      _ = ∑ x, if x ∈ baseᶜ then (q:ℝ)*H x else 0 := by
        apply Finset.sum_congr rfl; intro x _
        by_cases hx : x ∈ base
        · simp [hb x hx,hx]
        · simp [hx,hn x hx]
      _ = ∑ x ∈ baseᶜ, (q:ℝ)*H x := by
        simpa only [Finset.filter_univ_mem] using
          (Finset.sum_filter (s := Finset.univ) (fun x => x ∈ baseᶜ) (fun x => (q:ℝ)*H x)).symm
      _ = _ := by rw [Finset.mul_sum]
  have hr : (∑ x, ∑ y ∈ guides x, dot p (residual p x y f) (residual p x y f)) ≤ variance p f := by
    have hh := residual_sum p hp hs (allowed guides)
      (fun z hz => horder z.1 z.2 (by simpa [allowed] using hz)) f
    rw [sum_allowed] at hh
    have hv : variance p f = ∑ s, density p s*(f s-∑ t, density p t*f t)^2 := by
      unfold variance dot mean
      apply Finset.sum_congr rfl; intro s _
      change density p s*(f s-∑ t, density p t*f t)*(f s-∑ t, density p t*f t) = _
      ring
    rw [hv]
    exact hh
  have hpair := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset I)) =>
    Finset.sum_le_sum (fun y hy => one_pair p hp hs x y (horder x y hy) (Q x y) L
      (le_of_lt hL) (hQ x y hy) f))
  change (∑ x, ∑ y ∈ guides x, H x) ≤ _ at hpair
  rw [hlhs,hq] at hpair
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hpair
  change 32*L*A ≤ 4*L*E+8*L*(∑ x, ∑ y ∈ guides x,
      dot p (residual p x y f) (residual p x y f)) at hpair
  have hstrong : variance p f ≤ E/6+(4/3:ℝ)*F := by
    apply (mul_le_mul_iff_left₀ hL).mp
    nlinarith [mul_nonneg (le_of_lt hL) (sub_nonneg.mpr hr),
      mul_nonneg (le_of_lt hL) (sub_nonneg.mpr hbaseBound)]
  let M : ℝ := ((∑ x, (guides x).card)+base.card : ℕ)
  have hM : 0 < M := by
    have hnM : 0 < ((∑ x, (guides x).card)+base.card : ℕ) :=
      lt_of_lt_of_le (Finset.card_pos.mpr hbase) (Nat.le_add_left _ _)
    dsimp [M]
    exact_mod_cast hnM
  change variance p f ≤ (8*M/3)*((E+F)/(2*M))
  have he : (8*M/3)*((E+F)/(2*M)) = (4/3:ℝ)*(E+F) := by
    field_simp [ne_of_gt hM]
    ring
  rw [he]
  linarith

end

open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

structure SymmetricProposal (Ω : Type*) [Fintype Ω] where
  q : Ω → Ω → ℝ
  nonneg : ∀ a b, 0 ≤ q a b
  row : ∀ a, ∑ b, q a b = 1
  symmetric : ∀ a b, q a b = q b a

noncomputable def offCapacity (P : SymmetricProposal Ω) (π : Ω → ℝ) (a b : Ω) : ℝ :=
  min (π a) (π b)*P.q a b

noncomputable def metropolisCapacity (P : SymmetricProposal Ω) (π : Ω → ℝ) (a b : Ω) : ℝ :=
  if a = b then π a - ∑ z ∈ Finset.univ.erase a, offCapacity P π a z
  else offCapacity P π a b

omit [DecidableEq Ω] in
lemma offCapacity_nonneg (P : SymmetricProposal Ω) (π : Ω → ℝ)
    (hπ : ∀ a, 0 ≤ π a) (a b : Ω) : 0 ≤ offCapacity P π a b :=
  mul_nonneg (le_min (hπ a) (hπ b)) (P.nonneg a b)

omit [DecidableEq Ω] in
lemma offCapacity_le (P : SymmetricProposal Ω) (π : Ω → ℝ)
    (a b : Ω) : offCapacity P π a b ≤ π a*P.q a b :=
  mul_le_mul_of_nonneg_right (min_le_left _ _) (P.nonneg a b)

omit [DecidableEq Ω] in
lemma offCapacity_symmetric (P : SymmetricProposal Ω) (π : Ω → ℝ)
    (a b : Ω) : offCapacity P π a b = offCapacity P π b a := by
  simp only [offCapacity,min_comm (π a),P.symmetric]

lemma offCapacity_sum_le (P : SymmetricProposal Ω) (π : Ω → ℝ)
    (hπ : ∀ a, 0 ≤ π a) (a : Ω) :
    (∑ z ∈ Finset.univ.erase a, offCapacity P π a z) ≤ π a := by
  calc
    _ ≤ ∑ z, offCapacity P π a z := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset _ _) (fun z _ _ => offCapacity_nonneg P π hπ a z)
    _ ≤ ∑ z, π a*P.q a z := Finset.sum_le_sum (fun z _ => offCapacity_le P π a z)
    _ = π a := by rw [← Finset.mul_sum,P.row,mul_one]

lemma metropolisCapacity_nonneg (P : SymmetricProposal Ω) (π : Ω → ℝ)
    (hπ : ∀ a, 0 ≤ π a) (a b : Ω) : 0 ≤ metropolisCapacity P π a b := by
  unfold metropolisCapacity
  split_ifs
  · exact sub_nonneg.mpr (offCapacity_sum_le P π hπ a)
  · exact offCapacity_nonneg P π hπ a b

lemma metropolisCapacity_symmetric (P : SymmetricProposal Ω) (π : Ω → ℝ)
    (a b : Ω) : metropolisCapacity P π a b = metropolisCapacity P π b a := by
  by_cases h : a = b
  · subst b; rfl
  · simp only [metropolisCapacity,ite_eq_right h,ite_eq_right (Ne.symm h)]
    exact offCapacity_symmetric P π a b

lemma metropolisCapacity_row (P : SymmetricProposal Ω) (π : Ω → ℝ)
    (a : Ω) : (∑ b, metropolisCapacity P π a b) = π a := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
  have he : (∑ b ∈ Finset.univ.erase a, metropolisCapacity P π a b) =
      ∑ b ∈ Finset.univ.erase a, offCapacity P π a b := by
    apply Finset.sum_congr rfl; intro b hb
    rw [metropolisCapacity,ite_eq_right (Finset.ne_of_mem_erase hb).symm]
  rw [he]
  simp only [metropolisCapacity,ite_true]
  ring

lemma metropolisCapacity_col (P : SymmetricProposal Ω) (π : Ω → ℝ)
    (b : Ω) : (∑ a, metropolisCapacity P π a b) = π b := by
  simp_rw [metropolisCapacity_symmetric P π]
  exact metropolisCapacity_row P π b

noncomputable def metropolis (P : SymmetricProposal Ω) (π : Ω → ℝ) (a b : Ω) : ℝ :=
  metropolisCapacity P π a b / π a

lemma metropolis_row (P : SymmetricProposal Ω) (π : Ω → ℝ)
    (hπ : ∀ a, 0 < π a) (a : Ω) : (∑ b, metropolis P π a b) = 1 := by
  simp only [metropolis,← Finset.sum_div,metropolisCapacity_row]
  exact div_self (ne_of_gt (hπ a))

lemma metropolis_nonneg (P : SymmetricProposal Ω) (π : Ω → ℝ)
    (hπ : ∀ a, 0 < π a) (a b : Ω) : 0 ≤ metropolis P π a b :=
  div_nonneg (metropolisCapacity_nonneg P π (fun a => (hπ a).le) a b) (hπ a).le

lemma metropolis_acceptance (P : SymmetricProposal Ω) (π : Ω → ℝ)
    (hπ : ∀ a, 0 < π a) (a b : Ω) (hab : a ≠ b) :
    metropolis P π a b = P.q a b*min 1 (π b/π a) := by
  unfold metropolis metropolisCapacity
  rw [ite_eq_right hab]
  unfold offCapacity
  rw [mul_div_right_comm,← min_div_div_right (hπ a).le,div_self (ne_of_gt (hπ a)),mul_comm]

lemma metropolis_detailed (P : SymmetricProposal Ω) (π : Ω → ℝ)
    (hπ : ∀ a, 0 < π a) (a b : Ω) :
    π a*metropolis P π a b = π b*metropolis P π b a := by
  simp only [metropolis,mul_div_cancel₀ _ (ne_of_gt (hπ a)),
    mul_div_cancel₀ _ (ne_of_gt (hπ b))]
  exact metropolisCapacity_symmetric P π a b

lemma metropolis_energy (P : SymmetricProposal Ω) (π : Ω → ℝ) (f : Ω → ℝ) :
    localEnergy (metropolisCapacity P π) f = localEnergy (offCapacity P π) f := by
  unfold localEnergy
  congr 1
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  by_cases h : a = b
  · subst b; simp
  · simp only [metropolisCapacity,ite_eq_right h]

theorem metropolis_energy_domination (P : SymmetricProposal Ω) (π μ : Ω → ℝ)
    (r : ℝ) (hr : 0 ≤ r) (h : ∀ a, r*π a ≤ μ a) (f : Ω → ℝ) :
    r*localEnergy (metropolisCapacity P π) f ≤ localEnergy (metropolisCapacity P μ) f := by
  rw [metropolis_energy,metropolis_energy]
  unfold localEnergy
  rw [← mul_div_assoc,Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum; intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro b _
  have hh : r*min (π a) (π b) ≤ min (μ a) (μ b) := by
    apply le_min
    · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hr).trans (h a)
    · exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hr).trans (h b)
  calc
    _ = (r*min (π a) (π b))*P.q a b*(f a-f b)^2 := by unfold offCapacity; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hh (P.nonneg a b)) (sq_nonneg _)

end MatchingFPRAS.Replica

namespace MatchingFPRAS.Transport

section

open Finset MatchingFPRAS.Replica

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

attribute [local instance] Classical.propDecidable

noncomputable def firstLift {Ω : Type*} [Fintype Ω] (q : Ω → Ω → ℝ)
    (a b : Ω × Ω) : ℝ := if a.2 = b.2 then q a.1 b.1 else 0

lemma firstLift_row {Ω : Type*} [Fintype Ω] (q : Ω → Ω → ℝ)
    (hq : ∀ a, ∑ b, q a b = 1) (a : Ω × Ω) : (∑ b, firstLift q a b) = 1 := by
  classical
  simp [Fintype.sum_prod_type,firstLift,hq]

lemma firstLift_symmetric {Ω : Type*} [Fintype Ω] (q : Ω → Ω → ℝ)
    (hq : ∀ a b, q a b = q b a) (a b : Ω × Ω) : firstLift q a b = firstLift q b a := by
  simp [firstLift,eq_comm,hq a.1 b.1]

noncomputable def pairProposalRaw (a b : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) : ℝ :=
  (firstLift (switchProposal ends) a b + firstLift (colorProposal ends) a b + cycleProposal a b)/3

noncomputable def pairProposal (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (Finset.univ.filter (fun f => ends f = ends e)).card ≤ 2) :
    SymmetricProposal (PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) where
  q := pairProposalRaw ends
  nonneg a b := by
    unfold pairProposalRaw firstLift
    have hs := switchProposal_nonneg ends hloop hpar a.1 b.1
    have hc := colorProposal_nonneg ends hloop hpar a.1 b.1
    have hy := cycleProposal_nonneg a b
    split_ifs <;> positivity
  row a := by
    unfold pairProposalRaw
    rw [← Finset.sum_div,Finset.sum_add_distrib,Finset.sum_add_distrib,
      firstLift_row _ (switchProposal_row ends),firstLift_row _ (colorProposal_row ends),cycleProposal_row]
    norm_num
  symmetric a b := by
    unfold pairProposalRaw
    rw [firstLift_symmetric _ (switchProposal_symmetric ends),
      firstLift_symmetric _ (colorProposal_symmetric ends),cycleProposal_symmetric a b]

noncomputable def pairLaw (w z : E → ℝ) (a : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) : ℝ :=
  gibbs w a.1*gibbs z a.2

end

open Finset MatchingFPRAS.Replica

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

lemma firstLift_energy (π : Ω → ℝ) (hπ : ∀ a, 0 ≤ π a) (hs : ∑ a, π a = 1)
    (q : Ω → Ω → ℝ) (f g : Ω → ℝ) :
    (∑ a : Ω × Ω, ∑ b : Ω × Ω, min (π a.1*π a.2) (π b.1*π b.2)*
      firstLift q a b*((f a.1+g a.2)-(f b.1+g b.2))^2) =
      ∑ a, ∑ b, min (π a) (π b)*q a b*(f a-f b)^2 := by
  classical
  simp only [Fintype.sum_prod_type,firstLift,mul_ite,ite_mul,zero_mul,mul_zero]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  have h (a b c : Ω) :
      min (π a*π b) (π c*π b)*q a c*((f a+g b)-(f c+g b))^2 =
      π b*(min (π a) (π c)*q a c*(f a-f c)^2) := by
    rw [← min_mul_of_nonneg _ _ (hπ b)]
    ring
  simp_rw [h,← Finset.mul_sum]
  simp only [← Finset.sum_mul,hs,one_mul]

end MatchingFPRAS.Transport

end OAI
