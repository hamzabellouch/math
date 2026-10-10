import OAI.Analysis.Mahler.StripSublevelTopology

namespace OAI

noncomputable section
namespace SymmetricMahler
open Set Finset Complex Metric Real
open MahlerConformal
variable {I J : Type*} [Fintype I] [Fintype J]

lemma stripTau_nonneg (A : J → I → ℝ) (m : ℕ) (z : (I → ℝ) × (I → ℝ)) :
    0 ≤ stripTau A m z := by
  rw [stripTau_eq_sum_pow]
  exact sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _

lemma stripTau_zero (A : J → I → ℝ) {m : ℕ} (hm : 0 < m) :
    stripTau A m 0 = 0 := by
  simp [stripTau_eq_sum_pow, stripCoordinate_zero, inverseF_zero, hm.ne']

/-- No hidden zero away from the origin occurs in the literal tau. -/
theorem stripTau_eq_zero_iff (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    {z : (I → ℝ) × (I → ℝ)} (hz : z ∈ stripDomain A) :
    stripTau A m z = 0 ↔ z = 0 := by
  constructor
  · intro h
    apply (strip_power_common_zero A hA hm hz).mp
    intro j
    have hj : ‖inverseF (stripCoordinate A z j)‖ ^ (2*m) ≤ stripTau A m z := by
      rw [stripTau_eq_sum_pow]
      exact single_le_sum (fun k _ => pow_nonneg (norm_nonneg
        (inverseF (stripCoordinate A z k))) _) (mem_univ j)
    rw [h] at hj
    have hn := eq_zero_of_pow_eq_zero (le_antisymm hj (pow_nonneg (norm_nonneg _) _))
    rw [norm_eq_zero.mp hn]
    exact zero_pow hm.ne'
  · rintro rfl
    exact stripTau_zero A hm

theorem manuscript_finite_strip_geometry (A : J → I → ℝ)
    (hRank : Module.finrank ℝ (LinearMap.range (measurementLinear A)) = Fintype.card I)
    {m : ℕ} (hm : 2 ≤ m) :
    IsOpen (stripDomain A) ∧
    (0 : (I → ℝ) × (I → ℝ)) ∈ stripDomain A ∧
    (∀ z ∈ stripDomain A, (∀ j, inverseF (stripCoordinate A z j) ^ m = 0) ↔ z = 0) ∧
    deriv inverseF 0 ≠ 0 ∧
    (∀ z : (I → ℝ) × (I → ℝ),
      (∀ j, (deriv inverseF 0 * stripCoordinate A z j) ^ m = 0) ↔ z = 0) ∧
    (∀ R : ℝ, 0 < R → R < 1 →
      IsCompact (closure {z | z ∈ stripDomain A ∧ stripTau A m z < R}) ∧
      closure {z | z ∈ stripDomain A ∧ stripTau A m z < R} ⊆ stripDomain A) ∧
    IsOpen {z | z ∈ stripDomain A ∧ stripTau A m z < 1} := by
  have hA := (measurement_full_rank_iff A).mp hRank
  have hm0 : 0 < m := by omega
  have hc := inverseF_deriv_ne_zero zero_mem_Omega
  exact ⟨stripGeometry_isOpen_domain A, zero_mem_stripDomain A,
    fun _ hz => strip_power_common_zero A hA hm0 hz, hc,
    fun _ => strip_leading_common_zero A hA hm0 hc,
    fun _ hR hR1 => strip_sublevel_compact_closure A hA hm0 hR hR1,
    isOpen_strip_sublevel A m 1⟩

end SymmetricMahler

end

end OAI
