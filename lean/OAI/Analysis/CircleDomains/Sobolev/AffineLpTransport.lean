import OAI.Analysis.CircleDomains.Topology.PlanarAffineRescale
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

namespace OAI

/-! Integrability under the same physical affine rescaling as the weak
partial identities. The area factor is explicit and finite. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma map_volume_planarAffine (a : EuclideanPlane) {s : ℝ} (hs : 0 < s) :
    Measure.map (fun x : EuclideanPlane => a+s • x) volume =
      ENNReal.ofReal ((s^2)⁻¹) • volume := by
  have hm : Measurable (fun x : EuclideanPlane => s • x) := by fun_prop
  have ha : Measurable (fun x : EuclideanPlane => a+x) := by fun_prop
  rw [show (fun x : EuclideanPlane => a+s • x) =
    (fun x => a+x) ∘ (fun x => s • x) from rfl, ← Measure.map_map ha hm,
    Measure.map_addHaar_smul volume hs.ne', Measure.map_smul _ ha.aemeasurable]
  simp only [finrank_euclideanSpace_fin, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg s)),
    map_add_left_eq_self]

lemma memLp_planarAffine {F : Type*} [NormedAddCommGroup F] {f : EuclideanPlane → F}
    {p : ℝ≥0∞} (hf : MemLp f p volume) (a : EuclideanPlane) {s : ℝ} (hs : 0 < s) :
    MemLp (fun x => f (a+s • x)) p volume := by
  have h : MemLp f p (Measure.map (fun x : EuclideanPlane => a+s • x) volume) := by
    rw [map_volume_planarAffine a hs]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact h.comp_of_map (by fun_prop)

end CircleDomainRigidity

end

end OAI
