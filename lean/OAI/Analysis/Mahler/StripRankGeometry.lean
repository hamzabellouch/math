import OAI.Analysis.Mahler.ActualFiniteStrips
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace OAI

noncomputable section
namespace SymmetricMahler
open Set Finset Complex
open MahlerConformal
variable {I J : Type*} [Fintype I] [fintypeJ : Fintype J]

/-- The complexification of the real strip matrix, in real pair coordinates. -/
def stripCoordinateLinear (A : J → I → ℝ) :
    ((I → ℝ) × (I → ℝ)) →ₗ[ℝ] (J → ℂ) where
  toFun := stripCoordinate A
  map_add' z w := by
    ext j ; simp [stripCoordinate, measurement, mul_add, sum_add_distrib] ; ring
  map_smul' c z := by
    ext j ; simp [stripCoordinate, measurement, Finset.mul_sum, mul_left_comm, mul_comm]

omit fintypeJ in
lemma stripCoordinate_injective [Fintype J] (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) : Function.Injective (stripCoordinate A) := by
  intro z w h
  apply Prod.ext
  · apply hA
    funext j
    have := congrArg Complex.re (congrFun h j)
    simpa [stripCoordinate] using this
  · apply hA
    funext j
    have := congrArg Complex.im (congrFun h j)
    simpa [stripCoordinate] using this

omit fintypeJ in
lemma continuous_stripCoordinate [Fintype J] (A : J → I → ℝ) : Continuous (stripCoordinate A) :=
  (stripCoordinateLinear A).continuous_of_finiteDimensional

/-- Rank n implies properness of the full complexified matrix. -/
theorem stripCoordinate_isClosedEmbedding (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) :
    Topology.IsClosedEmbedding (stripCoordinate A) :=
  (stripCoordinateLinear A).isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr (stripCoordinate_injective A hA))

/-- Compact coordinate constraints have compact inverse image, with no
additional boundedness assumption on z. -/
theorem stripCoordinate_compact_preimage (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) {K : Set (J → ℂ)} (hK : IsCompact K) :
    IsCompact (stripCoordinate A ⁻¹' K) :=
  (stripCoordinate_isClosedEmbedding A hA).isCompact_preimage hK

omit fintypeJ in
@[simp] lemma stripCoordinate_zero [Fintype J] (A : J → I → ℝ) : stripCoordinate A 0 = 0 := by
  ext j ; simp [stripCoordinate, measurement]

lemma stripCoordinate_eq_zero_iff (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) {z : (I → ℝ) × (I → ℝ)} :
    stripCoordinate A z = 0 ↔ z = 0 := by
  rw [← stripCoordinate_zero A]
  exact (stripCoordinate_injective A hA).eq_iff

lemma stripGeometry_isOpen_domain (A : J → I → ℝ) : IsOpen (stripDomain A) := by
  have heq : stripDomain A = ⋂ j, (fun z => stripCoordinate A z j) ⁻¹' Omega := by
    ext z; simp [stripDomain]
  rw [heq]
  exact isOpen_iInter_of_finite fun j => isOpen_Omega.preimage
    ((continuous_apply j).comp (continuous_stripCoordinate A))

@[simp] lemma zero_mem_stripDomain (A : J → I → ℝ) :
    (0 : (I → ℝ) × (I → ℝ)) ∈ stripDomain A := by
  intro j
  simpa only [stripCoordinate_zero, Pi.zero_apply] using zero_mem_Omega

/-- The literal holomorphic map used in the mass application has only the
origin as a common zero. -/
theorem strip_power_common_zero (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    {z : (I → ℝ) × (I → ℝ)} (hz : z ∈ stripDomain A) :
    (∀ j, inverseF (stripCoordinate A z j) ^ m = 0) ↔ z = 0 := by
  constructor
  · intro h
    apply (stripCoordinate_eq_zero_iff A hA).mp
    funext j
    exact (inverseF_eq_zero_iff (hz j)).mp (eq_zero_of_pow_eq_zero (h j))
  · rintro rfl j
    simp [stripCoordinate_zero, inverseF_zero, hm.ne']

/-- The displayed leading homogeneous map also has no nonzero common zero. -/
theorem strip_leading_common_zero (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    {c : ℂ} (hc : c ≠ 0) {z : (I → ℝ) × (I → ℝ)} :
    (∀ j, (c * stripCoordinate A z j) ^ m = 0) ↔ z = 0 := by
  constructor
  · intro h
    apply (stripCoordinate_eq_zero_iff A hA).mp
    funext j
    exact (mul_eq_zero.mp (eq_zero_of_pow_eq_zero (h j))).resolve_left hc
  · rintro rfl j
    simp [stripCoordinate_zero, hm.ne']

end SymmetricMahler

end

end OAI
