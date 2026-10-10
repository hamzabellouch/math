import OAI.Analysis.Mahler.StripCompactSublevels
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace OAI

/-! Topological and rank properties of the finite-strip
sublevels. No differential, Jacobian or change-of-variables result is assumed. -/
noncomputable section
namespace SymmetricMahler
open Set Finset Complex Metric Real
open scoped Topology
open MahlerConformal
variable {I J : Type*} [Fintype I] [fintypeJ : Fintype J]

def measurementLinear (A : J → I → ℝ) : (I → ℝ) →ₗ[ℝ] (J → ℝ) where
  toFun := measurement A
  map_add' x y := by ext j; simp [measurement, mul_add, sum_add_distrib]
  map_smul' c x := by ext j; simp [measurement, Finset.mul_sum, mul_left_comm]

omit fintypeJ in
/-- The rank-n premise is exactly injectivity of measurement. -/
theorem measurement_full_rank_iff [Fintype J] (A : J → I → ℝ) :
    Module.finrank ℝ (LinearMap.range (measurementLinear A)) = Fintype.card I ↔
      Function.Injective (measurement A) := by
  have hd : Module.finrank ℝ (I → ℝ) = Fintype.card I := by simp
  constructor
  · intro h
    have hr := (measurementLinear A).finrank_range_add_finrank_ker
    rw [h, hd] at hr
    have hk : Module.finrank ℝ (LinearMap.ker (measurementLinear A)) = 0 := by omega
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)
  · intro h
    exact (LinearMap.finrank_range_of_inj (f := measurementLinear A) h).trans hd

lemma stripTau_eq_sum_pow (A : J → I → ℝ) (m : ℕ) (z : (I → ℝ) × (I → ℝ)) :
    stripTau A m z = ∑ j, ‖inverseF (stripCoordinate A z j)‖ ^ (2*m) := by
  simp only [stripTau, show 2 * (m : ℝ) = ((2*m : ℕ) : ℝ) by norm_cast,
    Real.rpow_natCast]

/-- The literal tau is exactly the squared Euclidean norm of the displayed
holomorphic vector f_j = h((Az)_j)^m, expressed as a coordinate sum. -/
theorem stripTau_eq_sum_norm_sq (A : J → I → ℝ) (m : ℕ)
    (z : (I → ℝ) × (I → ℝ)) :
    stripTau A m z = ∑ j, ‖inverseF (stripCoordinate A z j) ^ m‖ ^ 2 := by
  simp [stripTau_eq_sum_pow, norm_pow, ← pow_mul, Nat.mul_comm]

lemma stripGeometry_continuousOn_tau (A : J → I → ℝ) (m : ℕ) :
    ContinuousOn (stripTau A m) (stripDomain A) := by
  simp_rw [show stripTau A m = fun z => ∑ j, ‖inverseF (stripCoordinate A z j)‖ ^ (2*m)
    from funext (stripTau_eq_sum_pow A m)]
  apply continuousOn_finsetSum
  intro j _
  exact ((differentiableOn_inverseF.continuousOn.comp
    ((continuous_apply j).comp (continuous_stripCoordinate A)).continuousOn
    (fun z (hz : z ∈ stripDomain A) => hz j)).norm).pow _

/-- Every strict sublevel is open in the ambient real 2n-space. -/
theorem isOpen_strip_sublevel (A : J → I → ℝ) (m : ℕ) (R : ℝ) :
    IsOpen {z | z ∈ stripDomain A ∧ stripTau A m z < R} := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hU := (stripGeometry_isOpen_domain A).mem_nhds hz.1
  have ht := ((stripGeometry_continuousOn_tau A m z hz.1).continuousAt hU).preimage_mem_nhds
    (isOpen_Iio.mem_nhds hz.2)
  exact Filter.inter_mem hU ht

/-- Closed R-sublevels are themselves compact for R<1, not merely bounded. -/
theorem isCompact_strip_closed_sublevel (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) :
    IsCompact {z | z ∈ stripDomain A ∧ stripTau A m z ≤ R} := by
  obtain ⟨K, hK, hKU, hs⟩ := strip_sublevel_compact_container A hA hm hR hR1
  have heq : {z | z ∈ stripDomain A ∧ stripTau A m z ≤ R} =
      K ∩ (stripTau A m) ⁻¹' Iic R := by
    ext z
    exact ⟨fun hz => ⟨hs hz, hz.2⟩, fun hz => ⟨hKU hz.1, hz.2⟩⟩
  rw [heq]
  exact hK.of_isClosed_subset
    (((stripGeometry_continuousOn_tau A m).mono hKU).preimage_isClosed_of_isClosed hK.isClosed isClosed_Iic)
    inter_subset_left

end SymmetricMahler

end

end OAI
