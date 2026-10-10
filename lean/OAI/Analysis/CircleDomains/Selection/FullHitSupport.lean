import OAI.Analysis.CircleDomains.Selection.FinitePointAvoidance
import OAI.Analysis.CircleDomains.Sobolev.FiniteHitSquareEnergy

namespace OAI

/-! Outside the dust, only the distinguished image of infinity can have
positive hit probability. Thus the full prior-law mark set is countable. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem codeHitProbability_zero_off_dust
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hBU : d.dustᶜ ⊆ d.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (hend : d.target ∉ d.quotientDomain)
    (P : ProbabilityMeasure (BasePathCode d)) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanCodeOccupation d P = sphericalArea.withDensity g)
    (henergy : (∫⁻ x, g x ^ 2 ∂sphericalArea) < ∞)
    (x : Sphere) (hx : x ∉ d.dust) (hxi : x ≠ π OnePoint.infty) :
    codeHitProbability d P x = 0 := by
  let y : d.physicalDomain := d.domainEquiv.symm ⟨x, hBU hx⟩
  have hy : π y.val = x := by
    rw [← he y]
    exact congrArg Subtype.val (d.domainEquiv.apply_symm_apply ⟨x, hBU hx⟩)
  have hyi : y.val ≠ OnePoint.infty := fun h => hxi (hy.symm.trans (congrArg π h))
  cases heq : y.val using OnePoint.rec with
  | infty => exact (hyi heq).elim
  | coe z =>
    have hz : (z : Sphere) ∈ d.physicalDomain := heq ▸ y.property
    have hzx : π (z : Sphere) = x := heq ▸ hy
    rw [← pathHitProbability_codePathLaw, ← hzx]
    exact finite_domain_point_avoided d hU hG π hπ hclosed hsurj hr he hend P g hg hocc henergy z hz

omit [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)] in
theorem countable_full_hit_support {X : Type*} (m : X → ℝ≥0∞) (B : Set X) (p : X)
    (hB : {x | x ∈ B ∧ 0 < m x}.Countable)
    (hz : ∀ x, x ∉ B → x ≠ p → m x = 0) : (support m).Countable := by
  apply (hB.insert p).mono
  intro x hx
  by_cases hxp : x = p
  · exact Or.inl hxp
  · right
    have hxB : x ∈ B := by
      by_contra hn
      exact hx (hz x hn hxp)
    exact ⟨hxB, pos_iff_ne_zero.mpr hx⟩

omit [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)] in
theorem full_hit_square_sum_lt_top {X : Type*} (m : X → ℝ≥0∞) (B : Set X) (p : X)
    (hm : ∀ x, m x ≤ 1) (hB : (∑' x : B, m x.val ^ 2) < ∞)
    (hz : ∀ x, x ∉ B → x ≠ p → m x = 0) : (∑' x, m x ^ 2) < ∞ := by
  classical
  have hbound (x : X) : m x ^ 2 ≤
      (if x ∈ B then m x ^ 2 else 0) + (if x = p then 1 else 0) := by
    by_cases hx : x ∈ B
    · simp only [hx, ite_true]
      exact le_add_right le_rfl
    · by_cases hp : x = p
      · simp only [hx, ite_false]
        simp only [hp, ite_true, zero_add]
        simpa only [hp, one_pow] using pow_le_pow_left' (hm x) 2
      · simp [hx, hp, hz x hx hp]
  have he : (∑' x, if x ∈ B then m x ^ 2 else 0) = ∑' x : B, m x.val ^ 2 := by
    exact (tsum_subtype B (fun x => m x ^ 2)).symm
  apply (ENNReal.tsum_le_tsum hbound).trans_lt
  rw [ENNReal.tsum_add, he]
  have hs : (∑' x : X, if x = p then (1 : ℝ≥0∞) else 0) = 1 := by simp
  rw [hs]
  exact ENNReal.add_lt_top.2 ⟨hB, by simp⟩

end CircleDomainRigidity

end

end OAI
