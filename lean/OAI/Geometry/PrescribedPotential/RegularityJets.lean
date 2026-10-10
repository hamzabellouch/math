import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalHessian
import OAI.Geometry.PrescribedPotential.HessianCommutator
import OAI.Geometry.PrescribedPotential.RegularityCutoffs

namespace OAI

/-! Regularity Jets. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped ContDiff SchwartzMap Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]

def chartOperator (q : Fin A.count) (κ η : ChartCutoff (A.euclideanChart q).target)
    (T : 𝓢(EC d, ℂ) →L[ℂ] 𝓢(EC d, ℂ)) : Smooth A →ₗ[ℝ] Smooth A :=
  (globalize q κ).comp ((T.restrictScalars ℝ).toLinearMap.comp
    (localizeLinear A q (cutoffGlobal q η) (cutoffGlobal_support q η)))

namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

lemma chartOperator_bound (q : Fin A.count)
    (κ η : ChartCutoff (A.euclideanChart q).target) (k l : ℕ)
    (T : 𝓢(EC d, ℂ) →L[ℂ] 𝓢(EC d, ℂ)) (hT : CoreBound (l : ℝ) (k : ℝ) T) :
    D.localizers.BoundedCore (l : ℝ) (k : ℝ) (chartOperator q κ η T) := by
  obtain ⟨B,hB,hb⟩ := globalize_integer_bound D.localizers q κ k
  obtain ⟨C,hC,hc⟩ := hT
  obtain ⟨E,hE,he⟩ := D.localization_integer_bound q (cutoffGlobal q η) (cutoffGlobal_support q η) l
  refine ⟨B*(C*E),mul_nonneg hB (mul_nonneg hC hE),fun f => ?_⟩
  let u := localize A q (cutoffGlobal q η) (cutoffGlobal_support q η) f
  change ‖D.localizers.embed (k : ℝ) (globalize q κ (T u))‖ ≤ _
  calc
    _ ≤ B*‖schwartzCoord (k : ℝ) (T u)‖ := hb _
    _ ≤ B*(C*‖schwartzCoord (l : ℝ) u‖) := mul_le_mul_of_nonneg_left (hc u) hB
    _ ≤ B*(C*(E*‖D.localizers.embed (l : ℝ) f‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (he f) hC) hB
    _ = _ := by ring

def regularityHessian (p : ι) (i j : Fin d) : Smooth A →ₗ[ℝ] Smooth A :=
  chartOperator (D.patch p).index (D.regularityCutoff p) (D.regularityOuter p) (hessianEntrySchwartz i j)

def regularityError (p : ι) (v : EC d) (i j : Fin d) : Smooth A →ₗ[ℝ] Smooth A :=
  chartOperator (D.patch p).index (D.regularityCutoff p) (D.regularityOuter p)
    (hessianLocalizedError (D.cutoff p).realPart.val v i j)

lemma regularityHessian_bound (k : ℕ) (p : ι) (i j : Fin d) :
    D.localizers.BoundedCore ((k : ℝ)+2) (k : ℝ) (D.regularityHessian p i j) := by
  have hh := D.chartOperator_bound (D.patch p).index (D.regularityCutoff p) (D.regularityOuter p)
    k (k+2) (hessianEntrySchwartz i j) (by
      simpa only [Nat.cast_add,Nat.cast_ofNat] using hessianEntrySchwartz_bound (k : ℝ) i j)
  simpa only [Nat.cast_add,Nat.cast_ofNat,regularityHessian] using hh

lemma regularityError_bound (k : ℕ) (p : ι) (v : EC d) (i j : Fin d) :
    D.localizers.BoundedCore ((k : ℝ)+2) (k : ℝ) (D.regularityError p v i j) := by
  have hh := D.chartOperator_bound (D.patch p).index (D.regularityCutoff p) (D.regularityOuter p)
    k (k+2) (hessianLocalizedError (D.cutoff p).realPart.val v i j) (by
      simpa only [Nat.cast_add,Nat.cast_ofNat]
        using hessianLocalizedError_bound (D.cutoff p).realPart.val v i j k)
  simpa only [Nat.cast_add,Nat.cast_ofNat,regularityError] using hh

end GluingData

lemma chartHessian_source (q : Fin A.count) (κ η : ChartCutoff (A.euclideanChart q).target)
    (hη : ∀ y ∈ tsupport (κ : EC d → ℂ), η y = 1)
    (φ : SmoothRealFunction A) (i j : Fin d) {x : X}
    (hx : x ∈ (A.euclideanChart q).source) :
    chartOperator q κ η (hessianEntrySchwartz i j) (Smooth.ofReal φ) x =
      κ (A.euclideanChart q x) * φ.hessian q (A.chart q x) i j := by
  change globalize q κ (hessianEntrySchwartz i j
    (localize A q (cutoffGlobal q η) (cutoffGlobal_support q η) (Smooth.ofReal φ))) x = _
  rw [globalize_apply,ite_eq_left hx]
  by_cases hc : κ (A.euclideanChart q x) = 0
  · rw [hc,zero_mul,zero_mul]
  have ht := (A.euclideanChart q).mapsTo hx
  have he := localize_cutoff_eventually q κ η hη (Smooth.ofReal φ) ht hc
  let u : EC d → ℝ := φ.localExpression q ∘ coordinateEquiv d
  have hu : ContDiffAt ℝ ∞ u (A.euclideanChart q x) := (φ.euclidean_smooth q).contDiffAt
    (by simpa only [ComplexAtlas.euclideanChart_target] using
      (A.euclideanChart q).open_target.mem_nhds ht)
  have hre : (fun y => Smooth.ofReal φ ((A.euclideanChart q).symm y)) = Complex.ofRealCLM ∘ u := rfl
  rw [hessianEntrySchwartz_real hu _ (he.trans (Filter.Eventually.of_forall (congr_fun hre))) i j,
    pullBilin_hessian hu]
  have hcomp : u ∘ (coordinateEquiv d).symm = φ.localExpression q := by
    funext z; simp [u]
  rw [hcomp]
  change κ (A.euclideanChart q x) * PotentialKaehler.hermitianPartMatrix
    (fderiv ℝ (fderiv ℝ (φ.localExpression q))
      (coordinateEquiv d (A.euclideanChart q x))) i j = _
  rw [ComplexAtlas.euclideanChart_apply,ContinuousLinearEquiv.apply_symm_apply]
  rfl

namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

lemma regularityHessian_source (p : ι) (φ : SmoothRealFunction A) (i j : Fin d) {x : X}
    (hx : x ∈ (A.euclideanChart (D.patch p).index).source)
    (hκ : A.euclideanChart (D.patch p).index x ∈ tsupport (D.cutoff p : EC d → ℂ)) :
    D.regularityHessian p i j (Smooth.ofReal φ) x =
      φ.hessian (D.patch p).index (A.chart (D.patch p).index x) i j := by
  rw [regularityHessian,chartHessian_source _ _ _
    (fun y hy => (D.regularityOuter_one p hy).eq_of_nhds) φ i j hx,
    (D.regularityCutoff_one p hκ).eq_of_nhds,one_mul]

def completedRegularityHessian (k : ℕ) (p : ι) (i j : Fin d) :
    D.localizers.Sobolev ((k : ℝ)+2) →L[ℝ] D.localizers.Sobolev (k : ℝ) :=
  D.localizers.extendCore ((k : ℝ)+2) (k : ℝ) (D.regularityHessian p i j)

def completedRegularityError (k : ℕ) (p : ι) (v : EC d) (i j : Fin d) :
    D.localizers.Sobolev ((k : ℝ)+2) →L[ℝ] D.localizers.Sobolev (k : ℝ) :=
  D.localizers.extendCore ((k : ℝ)+2) (k : ℝ) (D.regularityError p v i j)

lemma completedRegularityHessian_embed (k : ℕ) (p : ι) (i j : Fin d) (f : Smooth A) :
    D.completedRegularityHessian k p i j (D.localizers.embed ((k : ℝ)+2) f) =
      D.localizers.embed (k : ℝ) (D.regularityHessian p i j f) :=
  D.localizers.extendCore_embed (D.regularityHessian_bound k p i j) f

lemma completedRegularityError_embed (k : ℕ) (p : ι) (v : EC d) (i j : Fin d) (f : Smooth A) :
    D.completedRegularityError k p v i j (D.localizers.embed ((k : ℝ)+2) f) =
      D.localizers.embed (k : ℝ) (D.regularityError p v i j f) :=
  D.localizers.extendCore_embed (D.regularityError_bound k p v i j) f

end GluingData
end GlobalElliptic

end
end

end OAI
