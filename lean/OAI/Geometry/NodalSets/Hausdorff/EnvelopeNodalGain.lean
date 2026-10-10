import OAI.Geometry.NodalSets.Elliptic.CorrugationOldData
import OAI.Geometry.NodalSets.Elliptic.PlacedEnvelopeDomains
import OAI.Geometry.NodalSets.Elliptic.SphericalSeed
import OAI.Geometry.NodalSets.Hausdorff.PlacedNodalCertificate

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff ENNReal
noncomputable section

lemma corrugationOldSlope_le_sourceSignScale
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ) (x : Coord) :
    corrugationOldSlope g S x ≤ sourceSignScale g S x := by
  apply Real.sqrt_le_sqrt
  linarith

lemma PlacedEnvelopeData.gain_lt_sign_integral
    {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w : Coord → ℝ}
    {r a T : ℝ} {Kset : Set Coord} {m J K k0 : ℕ}
    (d : PlacedEnvelopeData g r a Kset T)
    (b : LocalCompactWaveData g w d.S (closure d.U) m J K k0)
    (hg : ContDiff ℝ ∞ g) (hp : ∀ x v, v ≠ 0 → 0 < g x v v) :
    T < ∫ x in seedCoordCube a, sourceSignScale g d.S x := by
  have hcube : seedCoordCube a ⊆ closure d.U := fun x hx ↦
    subset_closure (d.C_U (d.inner_C (Or.inl hx)))
  have hbranch : seedCoordCube a ⊆ seedCoordBranch := hcube.trans d.closure_U_branch
  have hi : IntegrableOn (corrugationOldSlope g d.S) (seedCoordCube a) :=  ((corrugationOldSlope_continuousOn g d.S seedCoordBranch_open hg.contDiffOn d.smooth
    (fun x _ ↦ hp x)).mono hbranch).integrableOn_compact (show IsCompact (seedCoordCube a) from isCompact_Icc)
  have hj : IntegrableOn (sourceSignScale g d.S) (seedCoordCube a) :=  (b.source_sign_scale_continuousOn hcube).integrableOn_compact
    (show IsCompact (seedCoordCube a) from isCompact_Icc)
  exact d.gain.trans_le (setIntegral_mono_on hi hj measurableSet_Icc
    (fun x _ ↦ corrugationOldSlope_le_sourceSignScale g d.S x))

lemma seedEigenvalue_sqrt_bound {n : ℕ} (hn : 0 < n) :
    Real.sqrt (seedEigenvalue n) ≤ 4*(n:ℝ) := by
  have h : (1:ℝ) ≤ n := by exact_mod_cast hn
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · unfold seedEigenvalue
    nlinarith

lemma normalized_seed_nodal_lower {n : ℕ} (hn : 0 < n) {c I : ℝ}
    (hc : 0 ≤ c) (hI : 0 ≤ I) {M : ℝ≥0∞}
    (hM : ENNReal.ofReal (c*((n:ℝ)*I)) ≤ M) :
    ENNReal.ofReal (c*I/4) ≤ M / ENNReal.ofReal (Real.sqrt (seedEigenvalue n)) := by
  have hlam : 0 < Real.sqrt (seedEigenvalue n) := Real.sqrt_pos.mpr (seedEigenvalue_pos hn)
  apply (ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hlam))) (Or.inl ENNReal.ofReal_ne_top)).mpr
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply (ENNReal.ofReal_le_ofReal ?_).trans hM
  have h := mul_le_mul_of_nonneg_left (seedEigenvalue_sqrt_bound hn)
    (show 0 ≤ c*I/4 by positivity)
  nlinarith

end
end Yau.Target

end OAI
