import OAI.Analysis.TriangularHilbert.MeshFinite

namespace OAI

universe uι uE

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma continuous_heatCarrier_param {E : Type uE} [TopologicalSpace E]
    (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (v w : Three) :
    Continuous (fun t => heatCarrier A h u (p t) (σ t) v w) := by
  unfold heatCarrier
  split_ifs
  · exact continuous_heatRow_param A h u hp hσ hpos v
  · exact (continuous_heatRow_param A h u hp hσ hpos v).star

omit [Fintype ι] in
lemma continuous_scoreMask_param {E : Type uE} [TopologicalSpace E] (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (w : Three) :
    Continuous (fun t => heatMask (fun a j => if a = w then score (u j) (p t a) (σ t a) else 0)) := by
  apply continuous_heatMask
  intro a j
  split_ifs
  · unfold score
    exact (continuous_const.sub ((continuous_apply a).comp hp)).div
      ((continuous_apply a).comp hσ) (fun t => (hpos t a).ne')
  · exact continuous_const

omit [Fintype ι] in
lemma continuous_secondMask_param {E : Type uE} [TopologicalSpace E] (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (w : Three) :
    Continuous (fun t => heatMask (fun a j => if a = w then score (u j) (p t a) (σ t a)^2-(σ t a)⁻¹ else 0)) := by
  apply continuous_heatMask
  intro a j
  split_ifs
  · unfold score
    exact (((continuous_const.sub ((continuous_apply a).comp hp)).div
      ((continuous_apply a).comp hσ) (fun t => (hpos t a).ne')).pow 2).sub
      (((continuous_apply a).comp hσ).inv₀ (fun t => (hpos t a).ne'))
  · exact continuous_const

lemma continuous_heatFirst_param {E : Type uE} [TopologicalSpace E]
    (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h) (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (v w : Three) :
    Continuous (fun t => heatFirst A h u (p t) (σ t) v w) := by
  simp only [heatFirst,localGram_eq_carrier A hh u _ (hpos _),localFirst_eq_carrier A hh u _ (hpos _)]
  exact continuous_energyGradient_insert (continuous_heatCarrier_param A h u hp hσ hpos v w)
    (continuous_scoreMask_param u hp hσ hpos w)

lemma continuous_heatSecondGradient_param {E : Type uE} [TopologicalSpace E]
    (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h) (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (v w : Three) :
    Continuous (fun t => energyGradient (localGram A h u (p t) (σ t) v w) (localSecond A h u (p t) (σ t) v w)) := by
  simp only [localGram_eq_carrier A hh u _ (hpos _),localSecond_eq_carrier A hh u _ (hpos _)]
  exact continuous_energyGradient_insert (continuous_heatCarrier_param A h u hp hσ hpos v w)
    (continuous_secondMask_param u hp hσ hpos w)

lemma continuous_heatVariance_param {E : Type uE} [TopologicalSpace E]
    (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h) (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (v w : Three) :
    Continuous (fun t => heatVariance A h u (p t) (σ t) v w) :=
  continuous_const.mul (continuous_heatSecondGradient_param A hh u hp hσ hpos v w)
end
end TriangularHilbert.Heat
end

end OAI
