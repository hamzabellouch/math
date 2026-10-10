import Mathlib
import OAI.Analysis.SymmetricDomains.AnalyticMulZeroGerm

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def germDirectionalDerivative (v : E) :
    Filter.Germ (𝓝 (0 : E)) ℂ → Filter.Germ (𝓝 (0 : E)) ℂ :=
  Quotient.map' (fun f x => fderiv ℂ f x v) (by
    intro f g h
    exact (h.fderiv (𝕜 := ℂ)).mono fun x hx => congrArg (fun L => L v) hx)

@[simp] theorem germDirectionalDerivative_ofFun (v : E) (f : E → ℂ) :
    germDirectionalDerivative E v (f : Filter.Germ (𝓝 (0 : E)) ℂ) =
      ((fun x => fderiv ℂ f x v) : Filter.Germ (𝓝 (0 : E)) ℂ) := rfl

noncomputable def analyticDirectionalDerivative (v : E) : AnalyticGerm E → AnalyticGerm E :=
  fun g => ⟨germDirectionalDerivative E v g.val,by
    obtain ⟨f,hf,he⟩ := g.property
    refine ⟨fun x => fderiv ℂ f x v,?_,?_⟩
    · exact ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hf.fderiv
    · rw [← he]; rfl⟩

noncomputable def analyticDirectionalDerivation (v : E) :
    Derivation ℂ (AnalyticGerm E) (AnalyticGerm E) where
  toFun := analyticDirectionalDerivative E v
  map_add' := by
    rintro ⟨_,f,hf,rfl⟩ ⟨_,g,hg,rfl⟩
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    change (fun x => fderiv ℂ (f+g) x v) =ᶠ[𝓝 (0:E)] (fun x => fderiv ℂ f x v + fderiv ℂ g x v)
    filter_upwards [hf.eventually_analyticAt,hg.eventually_analyticAt] with x hfx hgx
    simp only [fderiv_add hfx.differentiableAt hgx.differentiableAt,
      add_apply]
  map_smul' := by
    intro c
    rintro ⟨_,f,hf,rfl⟩
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    change (fun x => fderiv ℂ (c • f) x v) =ᶠ[𝓝 (0:E)] (fun x => c • fderiv ℂ f x v)
    filter_upwards [hf.eventually_analyticAt] with x hfx
    simp only [fderiv_const_smul hfx.differentiableAt,
      smul_apply]
  map_one_eq_zero' := by
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun x => by simp
  leibniz' := by
    rintro ⟨_,f,hf,rfl⟩ ⟨_,g,hg,rfl⟩
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    change (fun x => fderiv ℂ (f*g) x v) =ᶠ[𝓝 (0:E)] (fun x => f x * fderiv ℂ g x v + g x * fderiv ℂ f x v)
    filter_upwards [hf.eventually_analyticAt,hg.eventually_analyticAt] with x hfx hgx
    simp only [fderiv_mul hfx.differentiableAt hgx.differentiableAt,
      add_apply,smul_apply,smul_eq_mul]

abbrev MeromorphicGermField := FractionRing (AnalyticGerm E)

noncomputable def analyticGermOf (f : E → ℂ) (hf : AnalyticAt ℂ f 0) : AnalyticGerm E :=
  ⟨(f : Filter.Germ (𝓝 (0 : E)) ℂ),⟨f,hf,rfl⟩⟩

@[simp] theorem analyticGermOf_eq_iff (f g : E → ℂ)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    analyticGermOf E f hf = analyticGermOf E g hg ↔ f =ᶠ[𝓝 (0:E)] g := by
  exact Subtype.ext_iff.trans Filter.Germ.coe_eq

@[simp] theorem analyticDirectionalDerivation_ofFun (v : E)
    (f : E → ℂ) (hf : AnalyticAt ℂ f 0) :
    analyticDirectionalDerivation E v (analyticGermOf E f hf) =
      analyticGermOf E (fun x => fderiv ℂ f x v)
        (((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hf.fderiv) := rfl

end Release061

end

end OAI
