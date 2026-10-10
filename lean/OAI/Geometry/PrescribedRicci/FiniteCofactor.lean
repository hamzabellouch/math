import Mathlib
import OAI.Geometry.PrescribedPotential.CompletedRealification
import OAI.Geometry.PrescribedPotential.GlobalConjugation
import OAI.Geometry.PrescribedPotential.GlobalHessian
import OAI.Geometry.PrescribedPotential.GlobalMetricEntries
import OAI.Geometry.PrescribedRicci.MatrixDifferentialNew
import OAI.Geometry.PrescribedPotential.NonlinearHessianCommutator
import OAI.Geometry.PrescribedPotential.SobolevDetDifferential

namespace OAI

/-! Finite Cofactor. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff SchwartzMap Classical BoundedContinuousFunction ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace Localizers
variable (L : Localizers A ι)
lemma strong_lower {s t : ℝ} (hst : t ≤ s)
    (hs : (Module.finrank ℝ (EC d):ℝ) < 2*s)
    (ht : (Module.finrank ℝ (EC d):ℝ) < 2*t) (u : L.Sobolev s) :
    L.strong t (L.lower s t u) = L.strong s u := by
  have he : (fun u => L.strong t (L.lower s t u)) = (fun u => L.strong s u) := by
    apply (L.embed_dense s).equalizer (by fun_prop) (by fun_prop)
    funext f
    simp only [Function.comp_apply,L.lower_embed hst,L.strong_embed s hs,L.strong_embed t ht]
  exact congr_fun he u
end Localizers
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

lemma completedHessian_lower (k l : ℕ) (hlk : l ≤ k) (p : ι) (i j : Fin d)
    (u : D.localizers.Sobolev ((k:ℝ)+2)) :
    D.completedHessian l p i j (D.localizers.lower ((k:ℝ)+2) ((l:ℝ)+2) u) =
      D.localizers.lower (k:ℝ) (l:ℝ) (D.completedHessian k p i j u) := by
  have hkl : (l:ℝ) ≤ (k:ℝ) := by exact_mod_cast hlk
  have he : (fun u => D.completedHessian l p i j (D.localizers.lower ((k:ℝ)+2) ((l:ℝ)+2) u)) =
      (fun u => D.localizers.lower (k:ℝ) (l:ℝ) (D.completedHessian k p i j u)) := by
    apply (D.localizers.embed_dense ((k:ℝ)+2)).equalizer (by fun_prop) (by fun_prop)
    funext f
    simp only [Function.comp_apply,D.completedHessian_embed,
      D.localizers.lower_embed (add_le_add hkl le_rfl),D.localizers.lower_embed hkl]
  exact congr_fun he u

lemma completedRealify_strong (k : ℕ)
    (hk : (Module.finrank ℝ (EC d):ℝ) < 2*(k:ℝ)) (u : D.localizers.Sobolev (k:ℝ)) (x : X) :
    D.localizers.strong (k:ℝ) (D.completedRealify k u) x =
      ((D.localizers.strong (k:ℝ) u x).re : ℂ) := by
  have he : (fun u => D.localizers.strong (k:ℝ) (D.completedRealify k u) x) =
      (fun u => ((D.localizers.strong (k:ℝ) u x).re : ℂ)) := by
    apply (D.localizers.embed_dense (k:ℝ)).equalizer (by fun_prop) (by fun_prop)
    funext f
    simp only [Function.comp_apply,D.completedRealify_embed,D.localizers.strong_embed _ hk]
    exact Smooth.realify_apply f x
  exact congr_fun he u

def cofactorMatrix (B : Bilin (EC d)) : Matrix (Fin d) (Fin d) ℂ :=
  PotentialKaehler.hermitianPartMatrix (pullBilin B)

def cofactorScalar (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (p : ι)
    (B : Bilin (EC d)) (u : D.localizers.Sobolev ((k:ℝ)+2)) : D.localizers.Sobolev (k:ℝ) :=
  D.completedRealify k (D.product k hk (D.localizers.embed (k:ℝ) (D.inverseDet p))
    (D.detDifferential k hk d
      (fun i j => D.localizers.embed (k:ℝ) (D.metricEntry p i j) + D.completedHessian k p i j u)
      (fun i j => D.localizers.embed (k:ℝ) (Smooth.const (cofactorMatrix B i j)))))

lemma cofactorScalar_continuous (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (B : Bilin (EC d)) : Continuous (D.cofactorScalar k hk p B) := by
  apply (D.completedRealify k).continuous.comp
  apply (D.product k hk (D.localizers.embed (k:ℝ) (D.inverseDet p))).continuous.comp
  apply Continuous.clm_apply
  · exact (D.detDifferential_contDiff k hk d).continuous.comp (by fun_prop)
  · fun_prop

lemma cofactorScalar_strong (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (B : Bilin (EC d)) (u : D.localizers.Sobolev ((k:ℝ)+2)) (x : X) :
    D.localizers.strong (k:ℝ) (D.cofactorScalar k hk p B u) x =
      ((D.inverseDet p x * NonlinearHessian.detDifferential
        (fun i j => D.metricEntry p i j x + D.localizers.strong (k:ℝ) (D.completedHessian k p i j u) x)
        (cofactorMatrix B)).re : ℂ) := by
  have hs : (Module.finrank ℝ (EC d):ℝ) < 2*(k:ℝ) := by
    have hh : (Module.finrank ℝ (EC d):ℝ) < k := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α:=ℝ) k]
  rw [cofactorScalar,D.completedRealify_strong k hs,D.product_strong,
    BoundedContinuousFunction.mul_apply,D.localizers.strong_embed _ hs]
  erw [D.detDifferential_strong]
  simp only [map_add,BoundedContinuousFunction.add_apply,D.localizers.strong_embed _ hs]
  rfl

lemma cofactorScalar_zero_source (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (B : Bilin (EC d)) {x : X}
    (hx : x ∈ tsupport (D.localizers.weight p : X → ℂ)) :
    D.localizers.strong (k:ℝ) (D.cofactorScalar k hk p B 0) x =
      (traceBilin (g.matrix (D.patch p).index (A.chart (D.patch p).index x)) B : ℂ) := by
  rw [D.cofactorScalar_strong]
  simp only [map_zero,BoundedContinuousFunction.coe_zero,Pi.zero_apply,add_zero]
  simp_rw [D.metricEntry_apply p _ _ hx]
  rw [D.inverseDet_apply p hx]
  have hp := g.positive (D.patch p).index _ ((A.chart (D.patch p).index).mapsTo (by simpa using D.patch_source p hx))
  change (((((g.matrix (D.patch p).index (A.chart (D.patch p).index x)).det)⁻¹ *
    fderiv ℝ Matrix.det (g.matrix (D.patch p).index (A.chart (D.patch p).index x)) (cofactorMatrix B)).re : ℂ)) = _
  rw [MongeAmpere.real_fderiv_det_apply _ _
    (isUnit_iff_ne_zero.mpr hp.det_pos.ne')]
  rw [← mul_assoc,inv_mul_cancel₀ hp.det_pos.ne',one_mul]
  rfl

lemma cofactorScalar_strong_lower (k l : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hl : Module.finrank ℝ (EC d) < l) (hlk : l ≤ k) (p : ι) (B : Bilin (EC d))
    (u : D.localizers.Sobolev ((k:ℝ)+2)) (x : X) :
    D.localizers.strong (l:ℝ) (D.cofactorScalar l hl p B
      (D.localizers.lower ((k:ℝ)+2) ((l:ℝ)+2) u)) x =
    D.localizers.strong (k:ℝ) (D.cofactorScalar k hk p B u) x := by
  have hs : (Module.finrank ℝ (EC d):ℝ) < 2*(l:ℝ) := by
    have hh : (Module.finrank ℝ (EC d):ℝ) < l := by exact_mod_cast hl
    linarith [Nat.cast_nonneg (α:=ℝ) l]
  have hkl : (l:ℝ) ≤ (k:ℝ) := by exact_mod_cast hlk
  have ht : (Module.finrank ℝ (EC d):ℝ) < 2*(k:ℝ) := by linarith
  rw [D.cofactorScalar_strong,D.cofactorScalar_strong]
  simp_rw [D.completedHessian_lower k l hlk,
    D.localizers.strong_lower hkl ht hs]

end GluingData
end GlobalElliptic

end
end

end OAI
