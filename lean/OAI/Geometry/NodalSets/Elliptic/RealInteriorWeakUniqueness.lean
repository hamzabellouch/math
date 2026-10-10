import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import OAI.Geometry.NodalSets.Elliptic.RealInteriorWeakProduct

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_interior_L2_eq_of_test_pairings {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (u v : Coord n → ℝ) (hu : MemLp u 2 (volume.restrict K))
    (hv : MemLp v 2 (volume.restrict K))
    (hpair : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, u x*psi x)=(∫ x in K, v x*psi x)) :
    u =ᵐ[volume.restrict (interior K)] v := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  have hI : IntegrableOn (fun x ↦ u x-v x) K := (hu.sub hv).integrable (by norm_num)
  have he := isOpen_interior.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hI.locallyIntegrableOn.mono_set interior_subset)
  have hz : ∀ᵐ x ∂volume, x ∈ interior K → u x-v x=0 := by
    apply he
    intro psi hp hc hs
    have hsame : (∫ x, psi x • (u x-v x)) = ∫ x in K, psi x*(u x-v x) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (interior_subset (hs ht))),zero_mul]
    rw [hsame]
    have hpsi := real_continuous_memLp_compact hK psi hp.continuous
    have hiu : IntegrableOn (fun x ↦ u x*psi x) K := hu.integrable_mul hpsi
    have hiv : IntegrableOn (fun x ↦ v x*psi x) K := hv.integrable_mul hpsi
    have hid : (fun x ↦ psi x*(u x-v x)) = fun x ↦ u x*psi x-v x*psi x := by funext x; ring
    rw [hid,integral_sub hiu hiv,hpair psi hp hc (hs.trans interior_subset),sub_self]
  apply (ae_restrict_iff' isOpen_interior.measurableSet).mpr
  filter_upwards [hz] with x hx hmem
  exact sub_eq_zero.mp (hx hmem)

end
end Yau

end OAI
