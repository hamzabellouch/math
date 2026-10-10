import Mathlib
import OAI.Geometry.PrescribedPotential.LocalizedDerivations
import OAI.Geometry.PrescribedPotential.RealSobolev

namespace OAI

/-! Regularity Cutoffs. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory Manifold IsManifold
open scoped ContDiff SchwartzMap Classical
namespace GlobalElliptic
open Anticanonical EllipticKernel SobolevChart SourceSmooth
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma exists_chartCutoff_nhds {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ κ : ChartCutoff U, (∀ x, (κ x).im = 0) ∧
      ∀ x ∈ K, (κ : E → ℂ) =ᶠ[𝓝 x] (fun _ => 1) := by
  obtain ⟨L, hLc, hLl, hKL, hLU⟩ := exists_compact_closed_between hK hU hKU
  obtain ⟨f, hf, hf0, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ, E)) hK.isClosed hKL (n := ⊤)
  have hsm : ContDiff ℝ ∞ (fun x => (f x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contMDiff_iff_contDiff.mp f.contMDiff)
  have hsub : tsupport (fun x => (f x : ℂ)) ⊆ L := by
    apply closure_minimal _ hLl
    intro x hx
    by_contra hn
    exact hx (by simp [hf0 x hn])
  have hc : HasCompactSupport (fun x => (f x : ℂ)) :=
    hLc.of_isClosed_subset (isClosed_tsupport _) hsub
  refine ⟨⟨hc.toSchwartzMap hsm, hc, hsub.trans hLU⟩, fun _ => Complex.ofReal_im _, ?_⟩
  intro x hx
  filter_upwards [hf.filter_mono (nhds_le_nhdsSet hx)] with y hy
  change (f y : ℂ) = 1
  rw [hy]
  rfl

variable {d : ℕ} {X : Type*} [TopologicalSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

lemma exists_regularityCutoff (p : ι) :
    ∃ η : ChartCutoff (A.euclideanChart (D.patch p).index).target,
      (∀ x, (η x).im = 0) ∧
      ∀ x ∈ tsupport (D.cutoff p : EC d → ℂ),
        (η : EC d → ℂ) =ᶠ[𝓝 x] (fun _ => 1) :=
  exists_chartCutoff_nhds (D.cutoff p).compact
    (A.euclideanChart (D.patch p).index).open_target (D.cutoff p).support_sub

def regularityCutoff (p : ι) : ChartCutoff (A.euclideanChart (D.patch p).index).target :=
  (D.exists_regularityCutoff p).choose

lemma regularityCutoff_real (p : ι) (x : EC d) : (D.regularityCutoff p x).im = 0 :=
  (D.exists_regularityCutoff p).choose_spec.1 x

lemma regularityCutoff_one (p : ι) {x : EC d}
    (hx : x ∈ tsupport (D.cutoff p : EC d → ℂ)) :
    (D.regularityCutoff p : EC d → ℂ) =ᶠ[𝓝 x] (fun _ => 1) :=
  (D.exists_regularityCutoff p).choose_spec.2 x hx

lemma exists_regularityOuter (p : ι) :
    ∃ η : ChartCutoff (A.euclideanChart (D.patch p).index).target,
      (∀ x, (η x).im = 0) ∧
      ∀ x ∈ tsupport (D.regularityCutoff p : EC d → ℂ),
        (η : EC d → ℂ) =ᶠ[𝓝 x] (fun _ => 1) :=
  exists_chartCutoff_nhds (D.regularityCutoff p).compact
    (A.euclideanChart (D.patch p).index).open_target (D.regularityCutoff p).support_sub

def regularityOuter (p : ι) : ChartCutoff (A.euclideanChart (D.patch p).index).target :=
  (D.exists_regularityOuter p).choose

lemma regularityOuter_one (p : ι) {x : EC d}
    (hx : x ∈ tsupport (D.regularityCutoff p : EC d → ℂ)) :
    (D.regularityOuter p : EC d → ℂ) =ᶠ[𝓝 x] (fun _ => 1) :=
  (D.exists_regularityOuter p).choose_spec.2 x hx

variable [T2Space X] [CompactSpace X]

lemma localizedDerivative_real (p : ι) (v : EC d) (f : RealSmooth A) :
    D.localizedDerivative p v f.val ∈ realSmoothSpace A := by
  intro x
  rw [D.localizedDerivative_apply]
  split_ifs with hx
  · have ht := (A.euclideanChart (D.patch p).index).mapsTo hx
    have hd : DifferentiableAt ℝ (f.val ∘ (A.euclideanChart (D.patch p).index).symm)
        (A.euclideanChart (D.patch p).index x) :=
      ((f.val.smooth (D.patch p).index).contDiffAt
        ((A.euclideanChart (D.patch p).index).open_target.mem_nhds ht)).differentiableAt (by simp)
    have he : (fun y : EC d => (f.val ((A.euclideanChart (D.patch p).index).symm y)).im) =
        (fun _ => 0) := funext (fun y => f.property _)
    have hh := congrArg (fun L : EC d →L[ℝ] ℝ => L v)
      ((Complex.imCLM.hasFDerivAt.comp _ hd.hasFDerivAt).fderiv)
    change fderiv ℝ (fun y => (f.val ((A.euclideanChart (D.patch p).index).symm y)).im)
      (A.euclideanChart (D.patch p).index x) v = _ at hh
    rw [he, fderiv_const_apply, zero_apply] at hh
    simp only [ChartCutoff.realPart_apply, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    exact mul_eq_zero_of_right _ hh.symm
  · rfl

def realLocalizedDerivative (p : ι) (v : EC d) : RealSmooth A →ₗ[ℝ] RealSmooth A :=
  ((D.localizedDerivative p v).comp (realSmoothSpace A).subtype).codRestrict
    (realSmoothSpace A) (D.localizedDerivative_real p v)

lemma completedDerivative_real (k : ℕ) (p : ι) (v : EC d) :
    ∀ u ∈ D.localizers.realCompletion ((k : ℝ)+1),
      D.completedDerivative k p v u ∈ D.localizers.realCompletion (k : ℝ) := by
  apply D.localizers.maps_realCompletion
  intro f
  exact ⟨D.realLocalizedDerivative p v f,D.completedDerivative_embed k p v f.val⟩

end GluingData
end GlobalElliptic

end
end

end OAI
