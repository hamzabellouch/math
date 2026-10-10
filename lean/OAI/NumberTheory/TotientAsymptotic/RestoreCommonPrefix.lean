import OAI.NumberTheory.TotientAsymptotic.CollisionPrefixFibers
import OAI.NumberTheory.TotientAsymptotic.ProjectedMass
import OAI.NumberTheory.TotientAsymptotic.ActualSuffixMass

namespace OAI

/-! Restoring all common prefixes after counting distinct suffix pairs. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def collisionInnerPrefixes (x : ℝ) (H : ℕ) (t : ℝ) (i : ℕ) : Finset (Fin (i-1) → ℕ) :=
  (firstCollisionPairs x H t i).image (fun q => tupleInnerPrefix q.1 (i-1))

lemma first_collision_prefix_sum : ∀ᶠ x : ℝ in atTop,
    ∀ H i : ℕ, P H ≤ H → 1 ≤ i → i ≤ R x H → ∀ t ≤ x,
    ((firstCollisionPairs x H t i).card : ℝ) ≤
      (10*x/Real.log x)*
        (∑ s ∈ firstCollisionSuffixes x H t i, (prefixDenominator s.1 : ℝ)⁻¹)*
        (∑ p ∈ collisionInnerPrefixes x H t i, reciprocalShiftWeight p) := by
  filter_upwards [collision_prefix_fiber_bound] with x hx
  intro H i hPH hi hiR t ht
  let Q := firstCollisionPairs x H t i
  let S := firstCollisionSuffixes x H t i
  let P := collisionInnerPrefixes x H t i
  have hb := finite_class_card_bound Q (S ×ˢ P)
    (fun q => (pairSuffix q i,tupleInnerPrefix q.1 (i-1)))
    (fun k => (10*x/Real.log x)*(prefixDenominator k.1.1 : ℝ)⁻¹*reciprocalShiftWeight k.2)
    (by
      intro q hq
      exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨q,hq,rfl⟩,
        Finset.mem_image.mpr ⟨q,hq,rfl⟩⟩) (by
      rintro ⟨s,p⟩ _
      have he : Q.filter (fun q => (pairSuffix q i,tupleInnerPrefix q.1 (i-1))=(s,p)) =
          Q.filter (fun q => pairSuffix q i=s ∧ tupleInnerPrefix q.1 (i-1)=p) := by
        ext q
        simp only [Finset.mem_filter,Prod.mk.injEq]
      rw [he]
      exact hx H i hPH hi hiR t ht s p)
  apply hb.trans_eq
  rw [Finset.sum_product]
  simp_rw [← Finset.mul_sum,← Finset.sum_mul]
  rw [← Finset.mul_sum]

/-- The common-prefix mass is bounded uniformly in the suffix and index. -/
theorem collision_inner_prefix_mass (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, 1 ≤ i → i ≤ R x H → ∀ t : ℝ,
    (∑ p ∈ collisionInnerPrefixes x H t i, reciprocalShiftWeight p) ≤ G x (m x) := by
  filter_upwards [projected_mass_le_G hbox hren,eventually_tail_cut_separated]
    with H hmass hsep
  filter_upwards [hmass,m_tendsto.eventually (eventually_ge_atTop H)] with x hx hm
  intro i hi hiR t
  let K := m x-(i-1)
  have hiM : i ≤ m x := hiR.trans (Nat.sub_le _ _)
  have hd : R x K=i-1 := by dsimp [K,R]; omega
  have hK : H ≤ K := by dsimp [K]; unfold R at hiR; omega
  have hKm : K ≤ m x := Nat.sub_le _ _
  have hlen : R x K ≤ R x H := by rw [hd]; omega
  let Q := (firstCollisionPairs x H t i).image (fun q => tupleInnerPrefix q.1 (R x K))
  have he := hx K hK hKm Q (by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    have hq' := (firstCollisionPairs_data (by omega) hq).1
    exact tupleInnerPrefix_geometry (by omega) hlen (by unfold L; omega) hq'.1)
  have hsum := congrArg (fun n : ℕ => ∑ p ∈
    (firstCollisionPairs x H t i).image (fun q => tupleInnerPrefix q.1 n), reciprocalShiftWeight p) hd
  change (∑ p ∈ (firstCollisionPairs x H t i).image (fun q => tupleInnerPrefix q.1 (R x K)),
    reciprocalShiftWeight p) ≤ G x (m x) at he
  rw [hsum] at he
  exact he

/-- Count all original pairs at a positive first-difference index: both
suffix choices and all their common prefixes are now included. -/
theorem actual_positive_collision_count (hford : FordLemma51Input) (hmertens : MertensProductInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, 1 ≤ i → i ≤ R x H → ∀ t ≤ x,
    ((firstCollisionPairs x H t i).card : ℝ) ≤
      (160/Real.log 2)*(x/Real.log x)*G x (m x)*((m x-i : ℕ) : ℝ)^4*
        Real.exp (-fordBandScale x i/(16*((m x-i : ℕ) : ℝ)^4)) := by
  filter_upwards [actual_suffix_mass hford hmertens,collision_inner_prefix_mass hbox hren,
    eventually_tail_cut_separated] with H hs hp hsep
  filter_upwards [hs,hp,first_collision_prefix_sum,m_tendsto.eventually (eventually_ge_atTop H),
    eventually_gt_atTop (1 : ℝ),B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))]
    with x hx hpx hcount hm hx1 hB
  intro i hi hiR t ht
  have hL : L x H < m x := by unfold L; omega
  have hR : R x H < L x H := by unfold R L; omega
  have hS := hx i hi hiR hL hR t
  have hP := hpx i hi hiR t
  have hSP : 0 ≤ ∑ s ∈ firstCollisionSuffixes x H t i, (prefixDenominator s.1 : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hA : 0 ≤ 10*x/Real.log x := by positivity
  calc
    _ ≤ (10*x/Real.log x)*
        (∑ s ∈ firstCollisionSuffixes x H t i, (prefixDenominator s.1 : ℝ)⁻¹)*
        (∑ p ∈ collisionInnerPrefixes x H t i, reciprocalShiftWeight p) :=
      hcount H i (by omega) hi hiR t ht
    _ ≤ (10*x/Real.log x)*
        (∑ s ∈ firstCollisionSuffixes x H t i, (prefixDenominator s.1 : ℝ)⁻¹)*G x (m x) :=
      mul_le_mul_of_nonneg_left hP (mul_nonneg hA hSP)
    _ ≤ (10*x/Real.log x)*
        ((16/Real.log 2)*((m x-i : ℕ) : ℝ)^4*
          Real.exp (-fordBandScale x i/(16*((m x-i : ℕ) : ℝ)^4)))*G x (m x) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS hA) (G_pos hB _).le
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
