import Mathlib
import OAI.Geometry.PrescribedPotential.FrozenEllipticJets
import OAI.Geometry.PrescribedPotential.NonlinearHessianCommutator
import OAI.Geometry.PrescribedPotential.NonlinearRemainderStrong
import OAI.Geometry.PrescribedPotential.RealSobolev
import OAI.Geometry.PrescribedPotential.RegularityCoordinates

namespace OAI

/-! Commutator Support. -/

section

 

noncomputable section
open Set Filter Topology Matrix LineDeriv
open scoped ContDiff SchwartzMap Classical Matrix.Norms.Elementwise
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]

lemma hessianLocalizedError_zero {κ : 𝓢(EC d, ℂ)} (v : EC d) (f : 𝓢(EC d, ℂ))
    {y : EC d} (hy : y ∉ tsupport (κ : EC d → ℂ)) (i j : Fin d) :
    hessianLocalizedError κ v i j f y = 0 := by
  have hz := notMem_tsupport_iff_eventuallyEq.mp hy
  have he : (SchwartzMap.smulLeftCLM ℂ κ (∂_{v} f) : EC d → ℂ) =ᶠ[𝓝 y]
      (0 : 𝓢(EC d, ℂ)) := by
    filter_upwards [hz] with z hzz
    rw [SchwartzMap.smulLeftCLM_apply_apply κ.hasTemperateGrowth]
    change κ z * _ = 0
    simp only [hzz,Pi.zero_apply,zero_mul]
  have hh := congrArg (fun u : 𝓢(EC d, ℂ) => u y) (hessianLocalizedError_identity κ f v i j)
  rw [hessianEntrySchwartz_congr he,map_zero,_root_.zero_apply] at hh
  simp only [_root_.add_apply] at hh
  rw [SchwartzMap.smulLeftCLM_apply_apply κ.hasTemperateGrowth] at hh
  change 0 = κ y * _ + hessianLocalizedError κ v i j f y at hh
  simp only [hz.eq_of_nhds,Pi.zero_apply,zero_mul,zero_add] at hh
  exact hh.symm

omit [T2Space X] [CompactSpace X] in
lemma source_hessian_zero_of_local {φ : SmoothRealFunction A} {x : X}
    (he : φ.value =ᶠ[𝓝 x] (fun _ => 0)) (q : Fin A.count)
    (hx : x ∈ (A.chart q).source) : φ.hessian q (A.chart q x) = 0 := by
  have ht := (A.chart q).mapsTo hx
  have hc : Tendsto (A.chart q).symm (𝓝 (A.chart q x)) (𝓝 x) := by
    simpa only [(A.chart q).left_inv hx] using
      ((A.chart q).symm.continuousAt ht).tendsto
  have hh : φ.localExpression q =ᶠ[𝓝 (A.chart q x)] (fun _ => 0) := he.comp_tendsto hc
  have h2 := (hh.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  change PotentialKaehler.hermitianPartMatrix (fderiv ℝ (fderiv ℝ (φ.localExpression q))
    (A.chart q x)) = 0
  rw [h2]
  ext i j
  simp [PotentialKaehler.hermitianPartMatrix_apply,PotentialKaehler.hermitianPart]
  rfl

namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

def derivativeSupport (p : ι) : Set X :=
  (A.euclideanChart (D.patch p).index).symm '' tsupport (D.cutoff p : EC d → ℂ)

lemma localizedDerivative_tsupport (p : ι) (v : EC d) (f : Smooth A) :
    tsupport (D.localizedDerivative p v f : X → ℂ) ⊆ D.derivativeSupport p := by
  rw [D.localizedDerivative_regularity]
  exact (globalize_tsupport _ _ _).trans (image_mono (D.cutoff p).realPart_support)

omit [T2Space X] [CompactSpace X] in
lemma derivativeSupport_source {p : ι} {x : X} (hx : x ∈ D.derivativeSupport p) :
    x ∈ (A.euclideanChart (D.patch p).index).source ∧
      A.euclideanChart (D.patch p).index x ∈ tsupport (D.cutoff p : EC d → ℂ) := by
  obtain ⟨y,hy,rfl⟩ := hx
  have ht := (D.cutoff p).support_sub hy
  exact ⟨(A.euclideanChart (D.patch p).index).symm.mapsTo ht,
    by rwa [(A.euclideanChart (D.patch p).index).right_inv ht]⟩

omit [T2Space X] [CompactSpace X] in
lemma outsideDerivativeSupport_coord {p : ι} {x : X} (hx : x ∉ D.derivativeSupport p)
    (hs : x ∈ (A.euclideanChart (D.patch p).index).source) :
    A.euclideanChart (D.patch p).index x ∉ tsupport (D.cutoff p : EC d → ℂ) := by
  intro hh
  exact hx ⟨_,hh,(A.euclideanChart (D.patch p).index).left_inv hs⟩

lemma localizedDerivative_zero {p : ι} {x : X} (hx : x ∉ D.derivativeSupport p)
    (v : EC d) (f : Smooth A) : D.localizedDerivative p v f x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun hh => hx (D.localizedDerivative_tsupport p v f hh))

lemma regularityError_zero {p : ι} {x : X} (hx : x ∉ D.derivativeSupport p)
    (v : EC d) (f : Smooth A) (i j : Fin d) : D.regularityError p v i j f x = 0 := by
  change globalize (D.patch p).index (D.regularityCutoff p) _ x = 0
  rw [globalize_apply]
  split_ifs with hs
  · have hh := D.outsideDerivativeSupport_coord hx hs
    have hz := hessianLocalizedError_zero v
      (localize A (D.patch p).index (cutoffGlobal (D.patch p).index (D.regularityOuter p))
        (cutoffGlobal_support _ _) f)
      (fun hh' => hh ((D.cutoff p).realPart_support hh')) i j
    exact mul_eq_zero_of_right _ hz
  · rfl

lemma nonlinearRemainder_zero {p : ι} {x : X} (hx : x ∉ D.derivativeSupport p)
    (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (v : EC d) (f : Smooth A) :
    D.localizers.strong (k : ℝ)
      (D.nonlinearRemainder k hk p v (D.localizers.embed ((k : ℝ)+2) f)) x = 0 := by
  rw [D.nonlinearRemainder_strong_embed]
  have hm : (fun (i j : Fin d) => D.regularityError p v i j f x -
      D.localizedDerivative p v (D.regularityMetric p i j) x) = 0 := by
    ext i j
    rw [D.regularityError_zero hx,D.localizedDerivative_zero hx,sub_self]
    rfl
  let M : Matrix (Fin d) (Fin d) ℂ := fun i j =>
    D.regularityMetric p i j x + D.regularityHessian p i j f x
  change D.regularityInverseDet p x * NonlinearHessian.detDifferential M _ -
    D.localizedDerivative p v (D.regularityInverseDet p) x * M.det = 0
  rw [hm]
  change D.regularityInverseDet p x * NonlinearHessian.detDifferential M (0 : Matrix (Fin d) (Fin d) ℂ) -
    D.localizedDerivative p v (D.regularityInverseDet p) x * M.det = 0
  rw [(NonlinearHessian.detDifferential M).map_zero,D.localizedDerivative_zero hx,
    mul_zero,zero_mul,sub_self]

lemma localizedDerivative_source_hessian_zero {p : ι} {x : X}
    (hx : x ∉ D.derivativeSupport p) (v : EC d) (φ : SmoothRealFunction A)
    (q : Fin A.count) (hq : x ∈ (A.chart q).source) :
    ((D.realLocalizedDerivative p v (RealSmooth.ofReal φ)).source).hessian q (A.chart q x) = 0 := by
  apply source_hessian_zero_of_local _ q hq
  have hn : x ∉ tsupport (D.localizedDerivative p v (Smooth.ofReal φ) : X → ℂ) :=
    fun hh => hx (D.localizedDerivative_tsupport p v (Smooth.ofReal φ) hh)
  have he := notMem_tsupport_iff_eventuallyEq.mp hn
  filter_upwards [he] with y hy
  change (D.localizedDerivative p v (Smooth.ofReal φ) y).re = 0
  rw [hy]
  rfl

end GluingData
end GlobalElliptic

end
end

end OAI
