import Mathlib
import OAI.Analysis.SymmetricDomains.Vector
import OAI.Analysis.SymmetricDomains.AnalyticExtensionSemialgebraicAlgebraic

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
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology

theorem real_analytic_semialgebraic_nash_extension {n : ℕ}
    (B : Set (Fin n → ℝ)) (hB : B ∈ 𝓝 0)
    (f : (Fin n → ℝ) → ℝ) (hf : AnalyticAt ℝ f 0)
    (hgraph : PolynomialSignSet (id : (Option (Fin n) → ℝ) → (Option (Fin n) → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = f (fun i => x (some i))}) :
    ∃ F : (Fin n → ℂ) → ℂ, ∃ hF : AnalyticAt ℂ F 0,
      ((fun x : Fin n → ℝ => F (fun i => (x i : ℂ))) =ᶠ[𝓝 0] fun x => (f x : ℂ)) ∧
      IsAlgebraic (IntermediateField.adjoin ℂ (range (meromorphicCoordinate (n := n))))
        (meromorphicGermOf F hF) := by
  obtain ⟨F,hF,hext⟩ := Complexify.scalar hf
  exact ⟨F,hF,hext,analytic_extension_of_semialgebraic_isAlgebraic B hB f F hF hext hgraph⟩

theorem meromorphicGermOf_add_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f g : E → ℂ) (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (c : ℂ) :
    meromorphicGermOf (fun z => f z + c * g z) (hf.add (analyticAt_const.mul hg)) =
      meromorphicGermOf f hf + algebraMap ℂ (MeromorphicGermField E) c * meromorphicGermOf g hg := by
  have h : analyticGermOf E (fun z => f z + c * g z) (hf.add (analyticAt_const.mul hg)) =
      analyticGermOf E f hf + algebraMap ℂ (AnalyticGerm E) c * analyticGermOf E g hg := by
    apply Subtype.ext
    rfl
  simp only [meromorphicGermOf,h,map_add,map_mul,← IsScalarTower.algebraMap_apply]

theorem complex_valued_nash_extension {n : ℕ}
    (B : Set (Fin n → ℝ)) (hB : B ∈ 𝓝 0)
    (q : (Fin n → ℝ) → ℂ) (hq : AnalyticAt ℝ q 0)
    (hre : PolynomialSignSet (id : (Option (Fin n) → ℝ) → (Option (Fin n) → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = (q (fun i => x (some i))).re})
    (him : PolynomialSignSet (id : (Option (Fin n) → ℝ) → (Option (Fin n) → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = (q (fun i => x (some i))).im}) :
    ∃ F : (Fin n → ℂ) → ℂ, ∃ hF : AnalyticAt ℂ F 0,
      ((fun x : Fin n → ℝ => F (fun i => (x i : ℂ))) =ᶠ[𝓝 0] q) ∧
      IsAlgebraic (IntermediateField.adjoin ℂ (range (meromorphicCoordinate (n := n))))
        (meromorphicGermOf F hF) := by
  obtain ⟨f,hf,he,ha⟩ := real_analytic_semialgebraic_nash_extension B hB
    (fun x => (q x).re) ((Complex.reCLM.analyticAt _).comp hq) hre
  obtain ⟨g,hg,he',ha'⟩ := real_analytic_semialgebraic_nash_extension B hB
    (fun x => (q x).im) ((Complex.imCLM.analyticAt _).comp hq) him
  refine ⟨fun z => f z + Complex.I * g z,hf.add (analyticAt_const.mul hg),?_,?_⟩
  · filter_upwards [he,he'] with x hx hx'
    rw [hx,hx',mul_comm]
    exact Complex.re_add_im (q x)
  · rw [meromorphicGermOf_add_mul f g hf hg Complex.I]
    apply ha.add (IsAlgebraic.mul ?_ ha')
    let L := IntermediateField.adjoin ℂ (range (meromorphicCoordinate (n := n)))
    have hc := isAlgebraic_algebraMap (A := MeromorphicGermField (Fin n → ℂ))
      (algebraMap ℂ L Complex.I)
    simpa only [← IsScalarTower.algebraMap_apply] using hc

theorem nash_parametrization_extension {n N : ℕ}
    (B : Set (Fin n → ℝ)) (hB : B ∈ 𝓝 0)
    (q : (Fin n → ℝ) → Fin N → ℂ) (hq : AnalyticAt ℝ q 0)
    (hre : ∀ j, PolynomialSignSet (id : (Option (Fin n) → ℝ) → (Option (Fin n) → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = (q (fun i => x (some i)) j).re})
    (him : ∀ j, PolynomialSignSet (id : (Option (Fin n) → ℝ) → (Option (Fin n) → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = (q (fun i => x (some i)) j).im}) :
    ∃ F : Fin N → (Fin n → ℂ) → ℂ, ∃ hF : ∀ j, AnalyticAt ℂ (F j) 0,
      ((fun (x : Fin n → ℝ) j => F j (fun i => (x i : ℂ))) =ᶠ[𝓝 0] q) ∧
      ∀ j, IsAlgebraic (IntermediateField.adjoin ℂ (range (meromorphicCoordinate (n := n))))
        (meromorphicGermOf (F j) (hF j)) := by
  have hqj := analyticAt_pi_iff.mp hq
  choose F hF he ha using fun j => complex_valued_nash_extension B hB
    (fun x => q x j) (hqj j) (hre j) (him j)
  refine ⟨F,hF,?_,ha⟩
  filter_upwards [Filter.eventually_all.mpr he] with x hx
  exact funext hx

end Release061

end

end OAI
