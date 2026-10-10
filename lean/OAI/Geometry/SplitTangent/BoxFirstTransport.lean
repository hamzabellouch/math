import Mathlib
import OAI.Geometry.SplitTangent.BoxTransportBase
import OAI.Geometry.SplitTangent.FamilyPropagationStep
import OAI.Geometry.SplitTangent.BracketIntegrability
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.RationalTrivialization

namespace OAI

/-! Box First Transport. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle
universe u

namespace SplitTangent.TangentSplitting
open Filter Topology Set
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

def canonicalChartImages {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) : LocalChartImages S g :=
  Classical.choice (S.exists_local_chart_images hg)

def entireMap {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (hv : ∀ z, S.projector (g z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0)
    (a b : ℂ) : Tangent X (g a) →L[ℂ] Tangent X (g b) :=
  (S.canonicalChartImages hg).continuationMap hg hv a b

lemma entireMap_congr {g h : ℂ → X.Carrier} (he : g=h)
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (hh : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω h)
    (hvg : ∀ z, S.projector (g z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0)
    (hvh : ∀ z, S.projector (h z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) h z (1 : ℂ))=0)
    (a b : ℂ) : S.entireMap hg hvg a b=S.entireMap hh hvh a b := by
  subst h
  rfl

lemma entireMap_self {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (hv : ∀ z, S.projector (g z)
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) g z (1 : ℂ))=0) (a : ℂ) :
    S.entireMap hg hv a a=S.projector (g a) :=
  (S.canonicalChartImages hg).continuationMap_self hg hv a

lemma entireMap_family_holomorphic_at {F : ℂ × ℂ → X.Carrier}
    (hF : ContMDiff 𝓘(ℂ,ℂ × ℂ) (ModelWithCorners X) ω F)
    (hvel : ∀ s t, S.projector (F (s,t))
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) (fun w => F (s,w)) t (1 : ℂ))=0)
    {q u v : ℂ → ℂ} {z : ℂ}
    (hq : AnalyticAt ℂ q z) (hu : AnalyticAt ℂ u z) (hv : AnalyticAt ℂ v z)
    (σ : ∀ w, Tangent X (F (q w,u w)))
    (hσ : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,u w),σ w⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) z) :
    ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F (q w,v w),S.entireMap (family_slice_holomorphic hF (q w))
        (hvel (q w)) (u w) (v w) (σ w)⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) z :=
  familyContinuation_holomorphic_at hF hvel
    (fun s => S.canonicalChartImages (family_slice_holomorphic hF s)) hq hu hv σ hσ

end SplitTangent.TangentSplitting

namespace SplitTangent.TangentBox
open Filter Topology Set TangentSplitting
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : RationalCurve X}
  (F : TangentBox S g)

lemma vertical_holomorphic (a b : Bool) (s : ℂ) :
    ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω (fun t => F.chart a b (s,t)) :=
  family_slice_holomorphic (F.holomorphic a b) s

lemma vertical_tangent (a b : Bool) (s t : ℂ) :
    S.projector (F.chart a b (s,t))
      (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) (fun w => F.chart a b (s,w)) t (1 : ℂ))=0 := by
  have hd : HasFDerivAt (fun w : ℂ => (s,w))
      ((0 : ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ)) t :=
    (hasFDerivAt_const s t).prodMk (hasFDerivAt_id t)
  have hm : MDifferentiableAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ × ℂ) (fun w : ℂ => (s,w)) t :=
    hd.differentiableAt.mdifferentiableAt
  have hchain := mfderiv_comp t ((F.holomorphic a b (s,t)).mdifferentiableAt (by simp)) hm
  change S.projector _ ((mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X)
    ((F.chart a b) ∘ (fun w : ℂ => (s,w))) t) (1 : ℂ))=0
  rw [hchain,mfderiv_eq_fderiv,hd.fderiv]
  exact (F.tangency a b (s,t)).2

def vertical (a : Bool) (s : ℂ) : RationalCurve X where
  finite t := F.chart a false (s,t)
  infinity t := F.chart a true (s,t)
  finite_holomorphic := F.vertical_holomorphic a false s
  infinity_holomorphic := F.vertical_holomorphic a true s
  overlap t ht := by
    have h := F.overlap a false a true (s,t) ⟨by simp,fun _ => ht⟩
    cases a <;> simpa [ReciprocalCharts.changeChart,ReciprocalCharts.coord] using h

def chartTransport (a b : Bool) (s u v : ℂ) :
    Tangent X (F.chart a b (s,u)) →L[ℂ] Tangent X (F.chart a b (s,v)) :=
  S.entireMap (F.vertical_holomorphic a b s) (F.vertical_tangent a b s) u v

lemma chartTransport_self (a b : Bool) (s u : ℂ) :
    F.chartTransport a b s u u = S.projector (F.chart a b (s,u)) :=
  S.entireMap_self (F.vertical_holomorphic a b s) (F.vertical_tangent a b s) u

lemma chartTransport_horizontal_overlap (d : Bool) {s : ℂ} (hs : s≠0) (u v : ℂ) :
    F.chartTransport false d s u v = F.chartTransport true d s⁻¹ u v := by
  apply S.entireMap_congr
  funext t
  have h := F.overlap false d true d (s,t) ⟨fun _ => hs,by simp⟩
  cases d <;> simpa [ReciprocalCharts.changeChart,ReciprocalCharts.coord] using h

lemma chartTransport_vertical_overlap (d : Bool) (s a : ℂ) {z : ℂ} (hz : z≠0)
    (v : Tangent X (F.chart d false (s,z))) :
    F.chartTransport d false s z a v =
      F.chartTransport d false s 1 a (F.chartTransport d true s z⁻¹ 1 v) :=
  S.rational_reverse_overlap (F.vertical d s)
    (S.canonicalChartImages (F.vertical_holomorphic d false s))
    (S.canonicalChartImages (F.vertical_holomorphic d true s))
    (F.vertical_tangent d false s) (F.vertical_tangent d true s) a hz v

lemma chartTransport_holomorphic_at (a b : Bool) {q u v : ℂ → ℂ} {z : ℂ}
    (hq : AnalyticAt ℂ q z) (hu : AnalyticAt ℂ u z) (hv : AnalyticAt ℂ v z)
    (σ : ∀ w, Tangent X (F.chart a b (q w,u w)))
    (hσ : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F.chart a b (q w,u w),σ w⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) z) :
    ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨F.chart a b (q w,v w),F.chartTransport a b (q w) (u w) (v w) (σ w)⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) z :=
  S.entireMap_family_holomorphic_at (F.holomorphic a b) (F.vertical_tangent a b) hq hu hv σ hσ

lemma vertical_one (a : Bool) (s : ℂ) : F.chart a true (s,1)=F.chart a false (s,1) := by
  have he := F.overlap a true a false (s,1) ⟨by simp,fun _ => one_ne_zero⟩
  cases a <;> simpa [ReciprocalCharts.changeChart,ReciprocalCharts.coord] using he

lemma section_holomorphic_congr_base {f h : ℂ → X.Carrier} (he : ∀ w, f w=h w)
    (σ : ∀ w, Tangent X (f w)) {z : ℂ}
    (hσ : ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨f w,σ w⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) z) :
    ContMDiffAt 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun w => (⟨h w,σ w⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) z := by
  apply hσ.congr_of_eventuallyEq
  filter_upwards [] with w
  erw [he w]

 

def firstMap (b : ℂ) : CurveBundleMap g (F.firstFactor b) where
  finite z := F.chartTransport false false z z b
  infinity z := (F.chartTransport true false z 1 b).comp (F.chartTransport true true z z 1)
  overlap z hz := by
    apply ContinuousLinearMap.ext
    intro v
    change F.chartTransport false false z z b v =
      F.chartTransport true false z⁻¹ 1 b (F.chartTransport true true z⁻¹ z⁻¹ 1 v)
    rw [F.chartTransport_vertical_overlap false z b hz v]
    erw [F.chartTransport_horizontal_overlap false hz 1 b,
      F.chartTransport_horizontal_overlap true hz z⁻¹ 1]
    rfl
  finite_holomorphic U hU v hv z hz := by
    have h₀ := section_holomorphic_congr_base (fun w => (F.finite_diagonal w).symm) v
      ((hv z hz).contMDiffAt (hU.mem_nhds hz))
    exact (F.chartTransport_holomorphic_at false false analyticAt_id analyticAt_id
      analyticAt_const v h₀).contMDiffWithinAt
  infinity_holomorphic U hU v hv z hz := by
    have h₀ := section_holomorphic_congr_base (fun w => (F.infinity_diagonal w).symm) v
      ((hv z hz).contMDiffAt (hU.mem_nhds hz))
    have h₁ := F.chartTransport_holomorphic_at true true analyticAt_id analyticAt_id
      analyticAt_const v h₀ (v := fun _ => (1 : ℂ))
    have h₂ := section_holomorphic_congr_base (F.vertical_one true)
      (fun w => F.chartTransport true true w w 1 (v w)) h₁
    exact (F.chartTransport_holomorphic_at true false analyticAt_id analyticAt_const
      analyticAt_const (fun w => F.chartTransport true true w w 1 (v w)) h₂).contMDiffWithinAt

lemma firstMap_normalized (b : ℂ) : (F.firstMap b).finite b=S.projector (g.finite b) := by
  change F.chartTransport false false b b b = _
  rw [F.chartTransport_self]
  erw [F.finite_diagonal]

include F in
theorem exists_normalized_factor_transport (b : ℂ) :
    Nonempty (NormalizedFactorTransport S g b) := by
  obtain ⟨B,hB⟩ := F.exists_normalized_second_map b
  exact ⟨⟨F.firstFactor b,F.firstFactor_diagonal b,F.firstMap b,B,F.firstMap_normalized b,hB⟩⟩

end SplitTangent.TangentBox

end

end OAI
