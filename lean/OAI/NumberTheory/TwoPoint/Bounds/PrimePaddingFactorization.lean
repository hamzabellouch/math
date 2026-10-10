import OAI.NumberTheory.TwoPoint.Bounds.ResidueRestriction
import OAI.NumberTheory.TwoPoint.Bounds.PaddingResidueTilt
import OAI.NumberTheory.TwoPoint.Bounds.PrimeDegreeTail

namespace OAI

/-! Exact independence of tuple-prime and padding-prime observables under
the actual union residue law. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace FiniteLaw

lemma independent_average_sum_product {ι κ A : Type*}
    [Fintype ι] [Fintype κ] [Fintype A] [DecidableEq ι] [DecidableEq κ]
    (μ : ι → FiniteLaw A) (ν : κ → FiniteLaw A)
    (f : (ι → A) → ℝ) (g : (κ → A) → ℝ) :
    (independent (Sum.elim μ ν)).average
      (fun x => f (fun i => x (Sum.inl i)) * g (fun k => x (Sum.inr k))) =
      (independent μ).average f * (independent ν).average g := by
  let e := Equiv.sumArrowEquivProdArrow ι κ A
  calc
    _ = ∑ xy : (ι → A) × (κ → A),
        (independent (Sum.elim μ ν)).weight (Sum.elim xy.1 xy.2) * (f xy.1 * g xy.2) :=
      (e.symm.sum_comp (fun x => (independent (Sum.elim μ ν)).weight x *
        (f (fun i => x (Sum.inl i)) * g (fun k => x (Sum.inr k))))).symm
    _ = _ := by
      simp only [Fintype.sum_prod_type, independent, Fintype.prod_sum_type,
        Sum.elim_inl, Sum.elim_inr, average]
      rw [sum_mul]
      apply sum_congr rfl
      intro x _
      rw [mul_sum]
      apply sum_congr rfl
      intro y _
      ring

end FiniteLaw

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)

def tupleRestriction (x : ↥(data.P ∪ data.Q) → Fin B) : data.P → Fin B :=
  fun p => x ⟨p.val, mem_union_left _ p.property⟩

noncomputable def tupleResidueLaw (B : ℕ)
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) : FiniteLaw (data.P → Fin B) :=
  FiniteLaw.independent (fun p : data.P =>
    uniformResidueLaw B p.val (data.primeP _ p.property).pos
      (hB _ (mem_union_left _ p.property)))

lemma residue_average_tuple_padding
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (f : (data.P → Fin B) → ℝ) (g : (data.Q → Fin B) → ℝ) :
    (data.residueLaw B hB).average (fun x =>
      f (data.tupleRestriction x) * g (data.paddingRestriction x)) =
      (data.tupleResidueLaw B hB).average f *
        (data.paddingResidueLaw B hB).average g := by
  let e : data.P ⊕ data.Q → ↥(data.P ∪ data.Q) := Sum.elim
    (fun p => ⟨p.val, mem_union_left _ p.property⟩)
    (fun p => ⟨p.val, mem_union_right _ p.property⟩)
  have he : Function.Injective e := by
    intro x y hxy
    have hv := congrArg (fun p : ↥(data.P ∪ data.Q) => p.val) hxy
    cases x with
    | inl p =>
      cases y with
      | inl q => exact congrArg Sum.inl (Subtype.ext hv)
      | inr q =>
        exact False.elim (disjoint_left.mp data.disjoint p.property (hv.symm ▸ q.property))
    | inr p =>
      cases y with
      | inl q =>
        exact False.elim (disjoint_left.mp data.disjoint q.property (hv ▸ p.property))
      | inr q => exact congrArg Sum.inr (Subtype.ext hv)
  let μ := fun p : ↥(data.P ∪ data.Q) =>
    uniformResidueLaw B p.val (data.prime p).pos (hB _ p.property)
  have hμ : (fun i => μ (e i)) = Sum.elim
      (fun p : data.P => uniformResidueLaw B p.val (data.primeP _ p.property).pos
        (hB _ (mem_union_left _ p.property)))
      (fun p : data.Q => uniformResidueLaw B p.val (data.primeQ _ p.property).pos
        (hB _ (mem_union_right _ p.property))) := by
    funext i
    cases i <;> rfl
  have ht := FiniteLaw.independent_average_embedding e he μ
    (fun x => f (fun p => x (Sum.inl p)) * g (fun p => x (Sum.inr p)))
  rw [hμ, FiniteLaw.independent_average_sum_product] at ht
  exact ht

/-- Prime divisibility observables and an arbitrary padding-periodic
integer weight are independent at the same translated CRT origin. -/
lemma residue_average_prime_boolean_padding
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) (site : ℤ)
    (F : (data.P → Bool) → ℝ) (g : ℤ → ℝ)
    (hg : ∀ n m : ℤ, (∀ q ∈ data.Q, (n : ZMod q) = (m : ZMod q)) → g n = g m) :
    (data.residueLaw B hB).average (fun x =>
      F (fun p : data.P => decide ((p.val : ℤ) ∣ data.residueOrigin x + site)) *
        g (data.residueOrigin x + site)) =
      (paddingOriginalLaw data.P (fun p hp => (data.primeP p hp).two_le)).average F *
        (data.paddingResidueLaw B hB).average (fun z =>
          g (data.paddingResidueOrigin z + site)) := by
  calc
    _ = (data.residueLaw B hB).average (fun x =>
        F (paddingResidueAvailable data.P B site (data.tupleRestriction x)) *
          g (data.paddingResidueOrigin (data.paddingRestriction x) + site)) := by
      apply congrArg (data.residueLaw B hB).average
      funext x
      apply congrArg₂ (fun a b : ℝ => a * b)
      · apply congrArg F
        funext p
        change decide ((p.val : ℤ) ∣ data.residueOrigin x + site) =
          decide ((p.val : ℤ) ∣ (x ⟨p.val, mem_union_left _ p.property⟩).val + site)
        have hdiv : (p.val : ℤ) ∣ data.residueOrigin x + site ↔
            (p.val : ℤ) ∣ (x ⟨p.val, mem_union_left _ p.property⟩).val + site :=
          data.residueOrigin_divisibility x ⟨p.val, mem_union_left _ p.property⟩ site
        simp only [hdiv]
      · apply hg
        intro q hq
        let p : data.Q := ⟨q, hq⟩
        rw [Int.cast_add, Int.cast_add]
        exact congrArg (fun a : ZMod q => a + (site : ZMod q))
          ((data.residueOrigin_spec x (data.paddingCoordinate p)).trans
            (data.paddingResidueOrigin_spec (data.paddingRestriction x) p).symm)
    _ = (data.tupleResidueLaw B hB).average
        (fun z => F (paddingResidueAvailable data.P B site z)) *
          (data.paddingResidueLaw B hB).average
            (fun z => g (data.paddingResidueOrigin z + site)) :=
      data.residue_average_tuple_padding hB
        (fun z : data.P → Fin B => F (paddingResidueAvailable data.P B site z))
        (fun z : data.Q → Fin B => g (data.paddingResidueOrigin z + site))
    _ = _ := by
      congr 1
      exact padding_residue_average data.P B (fun p hp => (data.primeP p hp).two_le)
        (fun p hp => hB p (mem_union_left _ hp)) site F

lemma positive_prime_padding_average
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (S : Finset ℕ) (hSP : S ⊆ data.P) (site : ℤ) (g : ℤ → ℝ)
    (hg : ∀ n m : ℤ, (∀ q ∈ data.Q, (n : ZMod q) = (m : ZMod q)) → g n = g m) :
    (data.residueLaw B hB).average (fun x =>
      positivePrimeWeight S (data.residueOrigin x + site) * g (data.residueOrigin x + site)) =
      positivePrimeNormalizer S * (data.paddingResidueLaw B hB).average
        (fun z => g (data.paddingResidueOrigin z + site)) := by
  let q := fun p : data.P => 1 / (p.val : ℝ)
  let T := primeSelection data.P S hSP
  have hq0 (p : data.P) : 0 ≤ q p := by dsimp [q]; positivity
  have hq1 (p : data.P) : q p ≤ 1 := by
    apply (div_le_one (by exact_mod_cast (data.primeP p p.property).pos)).mpr
    exact_mod_cast (data.primeP p p.property).one_lt.le
  simp_rw [positivePrimeWeight_eq_selection data.P S hSP]
  rw [data.residue_average_prime_boolean_padding hB site (positiveCenterWeight q T) g hg]
  have hm : (paddingOriginalLaw data.P (fun p hp => (data.primeP p hp).two_le)).average
      (positiveCenterWeight q T) = positivePrimeNormalizer S := by
    simpa only [paddingOriginalLaw, paddingOriginalPrimeLaw, q, T] using
      (positive_center_tilt_total q T hq0 hq1).trans
        (positivePrimeNormalizer_eq_selection data.P S hSP).symm
  rw [hm]

theorem positive_prime_padding_degree_tail
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (S : Finset ℕ) (hSP : S ⊆ data.P) (W : ℝ) (hW : 10 ≤ W)
    (hmass : (∑ p ∈ data.P, 1 / (p : ℝ)) ≤ 2 * W * S.card)
    (site : ℤ) (g : ℤ → ℝ) (hg0 : ∀ n, 0 ≤ g n)
    (hg : ∀ n m : ℤ, (∀ q ∈ data.Q, (n : ZMod q) = (m : ZMod q)) → g n = g m) :
    (data.residueLaw B hB).average (fun x =>
      (positivePrimeWeight S (data.residueOrigin x + site) *
        if 6 * W * S.card < (actualPaddingDegree data.P (data.residueOrigin x + site) : ℝ)
          then 1 else 0) * g (data.residueOrigin x + site)) ≤
      (positivePrimeNormalizer S * Real.exp (-2 * W * S.card)) *
        (data.paddingResidueLaw B hB).average (fun z =>
          g (data.paddingResidueOrigin z + site)) := by
  let q := fun p : data.P => 1 / (p.val : ℝ)
  let T := primeSelection data.P S hSP
  let F := fun a : data.P → Bool => positiveCenterWeight q T a *
    if 6 * W * T.card < booleanCount a then (1 : ℝ) else 0
  have he (x : ↥(data.P ∪ data.Q) → Fin B) :
      (positivePrimeWeight S (data.residueOrigin x + site) *
        if 6 * W * S.card < (actualPaddingDegree data.P (data.residueOrigin x + site) : ℝ)
          then (1 : ℝ) else 0) =
      F (fun p : data.P => decide ((p.val : ℤ) ∣ data.residueOrigin x + site)) := by
    dsimp [F]
    rw [positivePrimeWeight_eq_selection data.P S hSP,
      actualPrimeDegree_eq_count, primeSelection_card]
  have htail : (paddingOriginalLaw data.P (fun p hp => (data.primeP p hp).two_le)).average F ≤
      positivePrimeNormalizer S * Real.exp (-2 * W * S.card) := by
    rw [← data.residue_average_prime_availability hB site F]
    simp_rw [← he]
    exact data.positive_prime_degree_tail hB S hSP W hW hmass site
  simp_rw [he]
  rw [data.residue_average_prime_boolean_padding hB site F g hg]
  exact mul_le_mul_of_nonneg_right htail
    ((data.paddingResidueLaw B hB).average_nonneg (fun z => hg0 _))

end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI
