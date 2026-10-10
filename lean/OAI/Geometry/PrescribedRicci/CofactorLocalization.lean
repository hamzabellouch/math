import Mathlib
import OAI.Geometry.PrescribedRicci.CofactorBilin
import OAI.Geometry.PrescribedRicci.CofactorCore
import OAI.Geometry.PrescribedPotential.GlobalHessian

namespace OAI

/-! Cofactor Localization. -/

section

 

noncomputable section
open Set Filter Topology Matrix _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped ContDiff SchwartzMap Classical BoundedContinuousFunction Matrix.Norms.Elementwise
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart FrozenPoisson MetricLocalization
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

def outerCore (p : ι) (f : Smooth A) : 𝓢(EC d,ℂ) :=
  localize A (D.patch p).index (cutoffGlobal (D.patch p).index (D.outerCutoff p))
    (cutoffGlobal_support _ _) f

def weightCore (p : ι) : 𝓢(EC d,ℂ) := D.forcing p (Smooth.const 1)

lemma outerCore_eventually (p : ι) (f : Smooth A) {x : X}
    (hx : x ∈ tsupport (D.localizers.weight p : X → ℂ)) :
    (D.outerCore p f : EC d → ℂ) =ᶠ[𝓝 (A.euclideanChart (D.patch p).index x)]
      f ∘ (A.euclideanChart (D.patch p).index).symm :=
  localize_cutoff_eventually _ (D.cutoff p) (D.outerCutoff p) (D.outerCutoff_one p) f
    ((A.euclideanChart _).mapsTo (D.patch_source p hx))
    (by rw [D.cutoff_one p x hx]; exact one_ne_zero)

lemma outerHessian_source (p : ι) (i j : Fin d) (φ : SmoothRealFunction A) {x : X}
    (hx : x ∈ tsupport (D.localizers.weight p : X → ℂ)) :
    hessianEntrySchwartz i j (D.outerCore p (Smooth.ofReal φ))
      (A.euclideanChart (D.patch p).index x) =
      φ.hessian (D.patch p).index (A.chart (D.patch p).index x) i j := by
  have hh := D.localizedHessian_source p i j φ hx
  change globalize (D.patch p).index (D.cutoff p)
    (hessianEntrySchwartz i j (D.outerCore p (Smooth.ofReal φ))) x = _ at hh
  rw [globalize_apply,ite_eq_left (D.patch_source p hx),D.cutoff_one p x hx,one_mul] at hh
  exact hh

lemma cofactorDifferential_source (p : ι) (φ ψ : SmoothRealFunction A) {x : X}
    (hx : x ∈ tsupport (D.localizers.weight p : X → ℂ)) :
    schwartzDifferential
      (extendedCoefficient (D.patch p).matrix (coefficientBCF (D.cofactorLocalCore p · · (Smooth.ofReal φ))))
      (D.outerCore p (Smooth.ofReal ψ)) (A.euclideanChart (D.patch p).index x) =
      (((g.matrix (D.patch p).index (A.chart (D.patch p).index x)).det⁻¹ *
        NonlinearHessian.detDifferential
          (g.matrix (D.patch p).index (A.chart (D.patch p).index x) +
            φ.hessian (D.patch p).index (A.chart (D.patch p).index x))
          (ψ.hessian (D.patch p).index (A.chart (D.patch p).index x))).re : ℂ) := by
  let q := (D.patch p).index
  let e := A.euclideanChart q
  let U := ψ.localExpression q ∘ coordinateEquiv d
  have hs := D.patch_source p hx
  have ht := e.mapsTo hs
  have hU : ContDiffAt ℝ ∞ U (e x) := (ψ.euclidean_smooth q).contDiffAt
    (by simpa only [e,ComplexAtlas.euclideanChart_target] using e.open_target.mem_nhds ht)
  have he : (D.outerCore p (Smooth.ofReal ψ) : EC d → ℂ) =ᶠ[𝓝 (e x)] Complex.ofRealCLM ∘ U :=
    D.outerCore_eventually p (Smooth.ofReal ψ) hx
  rw [schwartzDifferential_apply _ (extendedCoefficient_temperate _ _
    (fun i j => (D.cofactorLocalCore p i j (Smooth.ofReal φ)).hasTemperateGrowth))]
  simp_rw [D.cofactorLocalCore_source p _ _ _ hx,D.cofactorScalarCore_apply,
    D.metricEntry_apply p _ _ hx,D.inverseDet_apply p hx,D.localizedHessian_source p _ _ φ hx]
  have hh := cofactor_smooth_expression hU (D.outerCore p (Smooth.ofReal ψ)) he
    (g.matrix q (A.chart q x)).det⁻¹
    (g.matrix q (A.chart q x)+φ.hessian q (A.chart q x))
  dsimp only [q,e] at hh
  simp_rw [D.outerHessian_source p _ _ ψ hx] at hh
  exact hh.symm

lemma weightCore_apply (p : ι) (y : EC d) : D.weightCore p y =
    if y ∈ (A.euclideanChart (D.patch p).index).target then
      D.localizers.weight p ((A.euclideanChart (D.patch p).index).symm y) else 0 := by
  change localize A (D.localizers.index p) (D.localizers.weight p) (D.localizers.support_sub p)
    (Smooth.const 1) y = _
  simp only [localize_apply,localizeFun,D.index_eq]
  have hc (z : X) : (Smooth.const (A:=A) 1) z = 1 := rfl
  simp only [hc,mul_one]

lemma weightCore_outerCore (p : ι) (f : Smooth A) :
    SchwartzMap.smulLeftCLM ℂ (D.weightCore p) (D.outerCore p f) = D.forcing p f := by
  ext y
  rw [SchwartzMap.smulLeftCLM_apply_apply (D.weightCore p).hasTemperateGrowth,smul_eq_mul,
    D.weightCore_apply]
  change _ = localizeFun A (D.localizers.index p) (D.localizers.weight p) f y
  simp only [localizeFun,D.index_eq]
  split_ifs with hy
  · by_cases hw : D.localizers.weight p ((A.euclideanChart (D.patch p).index).symm y) = 0
    · rw [hw,zero_mul,zero_mul]
    · have hx := subset_tsupport (D.localizers.weight p : X → ℂ) hw
      have he := (A.euclideanChart (D.patch p).index).right_inv hy
      have hh := (D.outerCore_eventually p f hx).self_of_nhds
      rw [he] at hh
      rw [hh]
      rfl
  · exact zero_mul _

end GluingData
end GlobalElliptic

end
end

end OAI
