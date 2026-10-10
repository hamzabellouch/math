import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalMetricEntries
import OAI.Geometry.PrescribedPotential.GlobalParametrixEquation
import OAI.Geometry.PrescribedPotential.LocalizedDerivations
import OAI.Geometry.PrescribedPotential.RegularityJets

namespace OAI

/-! Regularity Coordinates. -/

section

 

noncomputable section
open Set Filter Topology LineDeriv
open scoped ContDiff SchwartzMap Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]

lemma localize_cutoff_nhds (q : Fin A.count) (η : ChartCutoff (A.euclideanChart q).target)
    (f : Smooth A) {y : EC d} (hy : y ∈ (A.euclideanChart q).target)
    (hη : (η : EC d → ℂ) =ᶠ[𝓝 y] (fun _ => 1)) :
    (localize A q (cutoffGlobal q η) (cutoffGlobal_support q η) f : EC d → ℂ)
      =ᶠ[𝓝 y] f ∘ (A.euclideanChart q).symm := by
  filter_upwards [(A.euclideanChart q).open_target.mem_nhds hy,hη] with z hz he
  rw [localize_apply,localizeFun_apply A _ _ hz]
  have hs : (A.euclideanChart q).symm z ∈ (A.euclideanChart q).source :=
    (A.euclideanChart q).symm.mapsTo hz
  change (if (A.euclideanChart q).symm z ∈ (A.euclideanChart q).source then
    η (A.euclideanChart q ((A.euclideanChart q).symm z)) else 0) * _ = _
  rw [ite_eq_left hs,(A.euclideanChart q).right_inv hz,he,one_mul]
  rfl

lemma hessianEntrySchwartz_congr {f h : 𝓢(EC d, ℂ)} {y : EC d}
    (he : (f : EC d → ℂ) =ᶠ[𝓝 y] (h : EC d → ℂ)) (i j : Fin d) :
    hessianEntrySchwartz i j f y = hessianEntrySchwartz i j h y := by
  simp only [hessianEntrySchwartz_apply,(he.fderiv (𝕜 := ℝ)).fderiv_eq]

omit [CompactSpace X] in
lemma chartFunction_local (q : Fin A.count) (κ : ChartCutoff (A.euclideanChart q).target)
    (f : EC d → ℂ) (hf : ContDiffOn ℝ ∞ f (A.euclideanChart q).target)
    {y : EC d} (hy : y ∈ (A.euclideanChart q).target) :
    (chartFunction q κ f hf ∘ (A.euclideanChart q).symm) =ᶠ[𝓝 y] (fun z => κ z * f z) := by
  filter_upwards [(A.euclideanChart q).open_target.mem_nhds hy] with z hz
  rw [Function.comp_apply,chartFunction_apply _ _ _ _ ((A.euclideanChart q).symm.mapsTo hz),
    (A.euclideanChart q).right_inv hz]

namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

omit [T2Space X] [CompactSpace X] in
lemma cutoff_support_regularity (p : ι) :
    tsupport (D.cutoff p : EC d → ℂ) ⊆ tsupport (D.regularityCutoff p : EC d → ℂ) := by
  intro y hy
  apply subset_tsupport
  change D.regularityCutoff p y ≠ 0
  rw [(D.regularityCutoff_one p hy).eq_of_nhds]
  exact one_ne_zero

omit [T2Space X] [CompactSpace X] in
lemma regularityOuter_inner (p : ι) {y : EC d}
    (hy : y ∈ tsupport (D.cutoff p : EC d → ℂ)) :
    (D.regularityOuter p : EC d → ℂ) =ᶠ[𝓝 y] (fun _ => 1) :=
  D.regularityOuter_one p (D.cutoff_support_regularity p hy)

lemma localizedDerivative_regularity (p : ι) (v : EC d) (f : Smooth A) :
    D.localizedDerivative p v f = globalize (D.patch p).index (D.cutoff p).realPart
      (∂_{v} (localize A (D.patch p).index (cutoffGlobal (D.patch p).index (D.regularityOuter p))
        (cutoffGlobal_support _ _) f)) := by
  apply Smooth.ext
  intro x
  rw [D.localizedDerivative_apply,globalize_apply]
  split_ifs with hx
  · by_cases hκ : (D.cutoff p).realPart (A.euclideanChart (D.patch p).index x) = 0
    · rw [hκ,zero_mul,zero_mul]
    · have ht := (A.euclideanChart (D.patch p).index).mapsTo hx
      have hs := (D.cutoff p).realPart_support (subset_tsupport _ hκ)
      have he := localize_cutoff_nhds (D.patch p).index (D.regularityOuter p) f ht
        (D.regularityOuter_inner p hs)
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,he.fderiv_eq]
  · rfl

lemma localizedDerivative_local_regularity (p : ι) (v : EC d) (f : Smooth A)
    {y : EC d} (hy : y ∈ (A.euclideanChart (D.patch p).index).target) :
    (D.localizedDerivative p v f ∘ (A.euclideanChart (D.patch p).index).symm) =ᶠ[𝓝 y]
      (SchwartzMap.smulLeftCLM ℂ (D.cutoff p).realPart.val
        (∂_{v} (localize A (D.patch p).index (cutoffGlobal (D.patch p).index (D.regularityOuter p))
          (cutoffGlobal_support _ _) f)) : EC d → ℂ) := by
  rw [D.localizedDerivative_regularity]
  exact globalize_local _ _ _ hy

lemma regularityHessian_localizedDerivative (p : ι) (v : EC d) (f : Smooth A)
    (i j : Fin d) {x : X}
    (hx : x ∈ (A.euclideanChart (D.patch p).index).source)
    (hκ : A.euclideanChart (D.patch p).index x ∈ tsupport (D.cutoff p : EC d → ℂ)) :
    D.regularityHessian p i j (D.localizedDerivative p v f) x =
      hessianEntrySchwartz i j (SchwartzMap.smulLeftCLM ℂ (D.cutoff p).realPart.val
        (∂_{v} (localize A (D.patch p).index (cutoffGlobal (D.patch p).index (D.regularityOuter p))
          (cutoffGlobal_support _ _) f))) (A.euclideanChart (D.patch p).index x) := by
  change globalize (D.patch p).index (D.regularityCutoff p)
    (hessianEntrySchwartz i j (localize A (D.patch p).index
      (cutoffGlobal (D.patch p).index (D.regularityOuter p)) (cutoffGlobal_support _ _)
      (D.localizedDerivative p v f))) x = _
  rw [globalize_apply,ite_eq_left hx,(D.regularityCutoff_one p hκ).eq_of_nhds,one_mul]
  apply hessianEntrySchwartz_congr
  exact (localize_cutoff_nhds _ _ _ ((A.euclideanChart (D.patch p).index).mapsTo hx)
    (D.regularityOuter_inner p hκ)).trans
    (D.localizedDerivative_local_regularity p v f ((A.euclideanChart (D.patch p).index).mapsTo hx))

end GluingData
end GlobalElliptic

end
end

end OAI
