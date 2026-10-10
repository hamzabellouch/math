import Mathlib
import OAI.Geometry.PrescribedPotential.CircleRadialCalculus
import OAI.Geometry.PrescribedPotential.ComplexHessian
import OAI.Geometry.PrescribedPotential.GlobalCompletion
import OAI.Geometry.PrescribedPotential.GlobalParametrix
import OAI.Geometry.PrescribedPotential.GlobalProduct
import OAI.Geometry.PrescribedPotential.KaehlerClosedDerivatives

namespace OAI

/-! Global Hessian. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped ContDiff SchwartzMap Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]

omit [CompactSpace X] in
lemma cutoffGlobal_support (i : Fin A.count) (κ : ChartCutoff (A.euclideanChart i).target) :
    tsupport (cutoffGlobal i κ : X → ℂ) ⊆ (A.euclideanChart i).source := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := cutoffGlobal_tsupport i κ hx
  exact (A.euclideanChart i).symm.mapsTo (κ.support_sub hy)

lemma localize_cutoff_eventually (i : Fin A.count)
    (κ η : ChartCutoff (A.euclideanChart i).target)
    (hη : ∀ y ∈ tsupport (κ : EC d → ℂ), η y = 1)
    (f : Smooth A) {y : EC d} (hy : y ∈ (A.euclideanChart i).target) (hκ : κ y ≠ 0) :
    (localize A i (cutoffGlobal i η) (cutoffGlobal_support i η) f : EC d → ℂ)
      =ᶠ[𝓝 y] f ∘ (A.euclideanChart i).symm := by
  have hn : ∀ᶠ z in 𝓝 y, κ z ≠ 0 :=
    (isOpen_ne_fun κ.val.continuous continuous_const).mem_nhds hκ
  filter_upwards [(A.euclideanChart i).open_target.mem_nhds hy, hn] with z hz hnz
  rw [localize_apply, localizeFun_apply A _ _ hz]
  have hs : (A.euclideanChart i).symm z ∈ (A.euclideanChart i).source :=
    (A.euclideanChart i).symm.mapsTo hz
  change (if (A.euclideanChart i).symm z ∈ (A.euclideanChart i).source then
      η (A.euclideanChart i ((A.euclideanChart i).symm z)) else 0) * f ((A.euclideanChart i).symm z) = _
  rw [ite_eq_left hs, (A.euclideanChart i).right_inv hz, hη z (subset_tsupport _ hnz), one_mul]
  rfl

namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

def localizedHessian (p : ι) (i j : Fin d) : Smooth A →ₗ[ℝ] Smooth A :=
  (globalize (D.patch p).index (D.cutoff p)).comp
    (((hessianEntrySchwartz i j).restrictScalars ℝ).toLinearMap.comp
      (localizeLinear A (D.patch p).index (cutoffGlobal (D.patch p).index (D.outerCutoff p))
        (cutoffGlobal_support _ _)))

lemma localizedHessian_bound (k : ℕ) (p : ι) (i j : Fin d) :
    D.localizers.BoundedCore ((k : ℝ)+2) (k : ℝ) (D.localizedHessian p i j) := by
  let q := (D.patch p).index
  let ρ := cutoffGlobal q (D.outerCutoff p)
  let hp := cutoffGlobal_support q (D.outerCutoff p)
  obtain ⟨B,hB,hb⟩ := globalize_integer_bound D.localizers q (D.cutoff p) k
  obtain ⟨C,hC,hc⟩ := hessianEntrySchwartz_bound (k : ℝ) i j
  obtain ⟨E,hE,he⟩ := D.localization_integer_bound q ρ hp (k+2)
  rw [Nat.cast_add, Nat.cast_ofNat] at he
  refine ⟨B*(C*E),mul_nonneg hB (mul_nonneg hC hE),fun f => ?_⟩
  let v := localize A q ρ hp f
  change ‖D.localizers.embed (k : ℝ) (globalize q (D.cutoff p) (hessianEntrySchwartz i j v))‖ ≤ _
  calc
    _ ≤ B*‖schwartzCoord (k : ℝ) (hessianEntrySchwartz i j v)‖ := hb _
    _ ≤ B*(C*‖schwartzCoord ((k : ℝ)+2) v‖) := mul_le_mul_of_nonneg_left (hc v) hB
    _ ≤ B*(C*(E*‖D.localizers.embed ((k : ℝ)+2) f‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (he f) hC) hB
    _ = _ := by ring

lemma localizedHessian_source (p : ι) (i j : Fin d) (φ : SmoothRealFunction A)
    {x : X} (hx : x ∈ tsupport (D.localizers.weight p : X → ℂ)) :
    D.localizedHessian p i j (Smooth.ofReal φ) x =
      φ.hessian (D.patch p).index (A.chart (D.patch p).index x) i j := by
  let q := (D.patch p).index
  let e := A.euclideanChart q
  have hs : x ∈ e.source := by
    have hh := D.localizers.support_sub p hx
    rwa [D.index_eq] at hh
  have ht : e x ∈ e.target := e.mapsTo hs
  have hc : D.cutoff p (e x) = 1 := D.cutoff_one p x hx
  have he := localize_cutoff_eventually q (D.cutoff p) (D.outerCutoff p)
    (D.outerCutoff_one p) (Smooth.ofReal φ) ht (by rw [hc]; exact one_ne_zero)
  let u : EC d → ℝ := φ.localExpression q ∘ coordinateEquiv d
  have hu : ContDiffAt ℝ ∞ u (e x) := (φ.euclidean_smooth q).contDiffAt (by simpa only [e, ComplexAtlas.euclideanChart_target] using e.open_target.mem_nhds ht)
  have hre : (fun y => Smooth.ofReal φ (e.symm y)) = Complex.ofRealCLM ∘ u := rfl
  change globalize q (D.cutoff p) (hessianEntrySchwartz i j
    (localize A q (cutoffGlobal q (D.outerCutoff p)) (cutoffGlobal_support _ _) (Smooth.ofReal φ))) x = _
  rw [globalize_apply, ite_eq_left hs, hc, one_mul,
    hessianEntrySchwartz_real hu _ (he.trans (Filter.Eventually.of_forall (congr_fun hre))) i j,
    pullBilin_hessian hu]
  have hcomp : u ∘ (coordinateEquiv d).symm = φ.localExpression q := by
    funext z; simp [u]
  rw [hcomp]
  change PotentialKaehler.hermitianPartMatrix
    (fderiv ℝ (fderiv ℝ (φ.localExpression q)) (coordinateEquiv d (e x))) i j = _
  have heq : coordinateEquiv d (e x) = A.chart q x := by
    change coordinateEquiv d ((coordinateEquiv d).symm (A.chart q x)) = _
    exact (coordinateEquiv d).apply_symm_apply _
  rw [heq]
  rfl

def completedHessian (k : ℕ) (p : ι) (i j : Fin d) :
    D.localizers.Sobolev ((k : ℝ)+2) →L[ℝ] D.localizers.Sobolev (k : ℝ) :=
  D.localizers.extendCore ((k : ℝ)+2) (k : ℝ) (D.localizedHessian p i j)

lemma completedHessian_embed (k : ℕ) (p : ι) (i j : Fin d) (f : Smooth A) :
    D.completedHessian k p i j (D.localizers.embed ((k : ℝ)+2) f) =
      D.localizers.embed (k : ℝ) (D.localizedHessian p i j f) :=
  D.localizers.extendCore_embed (D.localizedHessian_bound k p i j) f

end GluingData
end GlobalElliptic

end
end

end OAI
