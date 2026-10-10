import Mathlib
import OAI.Geometry.PrescribedPotential.NonlinearHessianCommutator
import OAI.Geometry.PrescribedPotential.RegularityCoordinates
import OAI.Geometry.PrescribedPotential.NonlinearRemainder
import OAI.Geometry.PrescribedPotential.PotentialDensity

namespace OAI

/-! Nonlinear Local Coordinates. -/

section

 

noncomputable section
open Set Filter Topology Matrix LineDeriv
open scoped ContDiff SchwartzMap Classical Matrix.Norms.Elementwise
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]

omit [T2Space X] [CompactSpace X] in
lemma hessianEntrySchwartz_source (q : Fin A.count) (φ : SmoothRealFunction A)
    (f : 𝓢(EC d, ℂ)) {y : EC d} (hy : y ∈ (A.euclideanChart q).target)
    (he : (f : EC d → ℂ) =ᶠ[𝓝 y] Smooth.ofReal φ ∘ (A.euclideanChart q).symm)
    (i j : Fin d) : hessianEntrySchwartz i j f y = φ.hessian q (coordinateEquiv d y) i j := by
  let u : EC d → ℝ := φ.localExpression q ∘ coordinateEquiv d
  have hu : ContDiffAt ℝ ∞ u y := (φ.euclidean_smooth q).contDiffAt
    (by simpa only [ComplexAtlas.euclideanChart_target] using
      (A.euclideanChart q).open_target.mem_nhds hy)
  have hre : (Smooth.ofReal φ ∘ (A.euclideanChart q).symm) = Complex.ofRealCLM ∘ u := rfl
  rw [hessianEntrySchwartz_real hu _ (he.trans (Filter.Eventually.of_forall (congr_fun hre))) i j,
    pullBilin_hessian hu]
  have hcomp : u ∘ (coordinateEquiv d).symm = φ.localExpression q := by
    funext z
    simp [u]
  rw [hcomp]
  rfl

omit [T2Space X] [CompactSpace X] in
lemma hessianMatrix_source_nhds (q : Fin A.count) (φ : SmoothRealFunction A)
    (f : 𝓢(EC d, ℂ)) {y : EC d} (hy : y ∈ (A.euclideanChart q).target)
    (he : (f : EC d → ℂ) =ᶠ[𝓝 y] Smooth.ofReal φ ∘ (A.euclideanChart q).symm) :
    NonlinearHessian.hessianMatrix f =ᶠ[𝓝 y] (fun z => φ.hessian q (coordinateEquiv d z)) := by
  filter_upwards [(A.euclideanChart q).open_target.mem_nhds hy,he.eventually_nhds] with z hz hez
  ext i j
  exact hessianEntrySchwartz_source q φ f hz hez i j

omit [T2Space X] [CompactSpace X] in
lemma density_local_schwartz (g : KaehlerMetric A) (q : Fin A.count) (φ : SmoothRealFunction A)
    (f : 𝓢(EC d, ℂ)) {y : EC d} (hy : y ∈ (A.euclideanChart q).target)
    (he : (f : EC d → ℂ) =ᶠ[𝓝 y] Smooth.ofReal φ ∘ (A.euclideanChart q).symm) :
    (Smooth.ofReal (g.potentialDensity φ) ∘ (A.euclideanChart q).symm) =ᶠ[𝓝 y]
      (fun z => (g.matrix q (coordinateEquiv d z)).det⁻¹ *
        (g.matrix q (coordinateEquiv d z) + NonlinearHessian.hessianMatrix f z).det) := by
  filter_upwards [(A.euclideanChart q).open_target.mem_nhds hy,
    hessianMatrix_source_nhds q φ f hy he] with z hz hez
  change ((g.potentialDensity φ).value ((A.euclideanChart q).symm z) : ℂ) = _
  rw [g.potentialDensity_complex φ q (by simpa using ((A.euclideanChart q).symm.mapsTo hz))]
  have hec : A.chart q ((A.euclideanChart q).symm z) = coordinateEquiv d z := by
    have hh := congrArg (coordinateEquiv d) ((A.euclideanChart q).right_inv hz)
    simpa only [ComplexAtlas.euclideanChart_apply, ContinuousLinearEquiv.apply_symm_apply] using hh
  rw [KaehlerMetric.volumePolynomial,hec,hez,div_eq_mul_inv,mul_comm]

namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

omit [CompactSpace X] in
lemma regularityMetric_local (p : ι) (i j : Fin d) {y : EC d}
    (hy : y ∈ tsupport (D.cutoff p : EC d → ℂ)) :
    (D.regularityMetric p i j ∘ (A.euclideanChart (D.patch p).index).symm) =ᶠ[𝓝 y]
      (fun z => g.matrix (D.patch p).index (coordinateEquiv d z) i j) := by
  have ht := (D.cutoff p).support_sub hy
  filter_upwards [chartFunction_local (D.patch p).index (D.regularityCutoff p)
    (fun z => g.matrix (D.patch p).index (coordinateEquiv d z) i j) _ ht,
    D.regularityCutoff_one p hy] with z hz he
  change D.regularityMetric p i j ((A.euclideanChart (D.patch p).index).symm z) = _ at hz ⊢
  rw [hz,he,one_mul]

omit [CompactSpace X] in
lemma regularityInverseDet_local (p : ι) {y : EC d}
    (hy : y ∈ tsupport (D.cutoff p : EC d → ℂ)) :
    (D.regularityInverseDet p ∘ (A.euclideanChart (D.patch p).index).symm) =ᶠ[𝓝 y]
      (fun z => (g.matrix (D.patch p).index (coordinateEquiv d z)).det⁻¹) := by
  have ht := (D.cutoff p).support_sub hy
  filter_upwards [chartFunction_local (D.patch p).index (D.regularityCutoff p)
    (fun z => (g.matrix (D.patch p).index (coordinateEquiv d z)).det⁻¹) _ ht,
    D.regularityCutoff_one p hy] with z hz he
  change D.regularityInverseDet p ((A.euclideanChart (D.patch p).index).symm z) = _ at hz ⊢
  rw [hz,he,one_mul]

end GluingData
end GlobalElliptic

end
end

end OAI
