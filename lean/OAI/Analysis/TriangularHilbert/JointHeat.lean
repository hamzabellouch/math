import OAI.Analysis.TriangularHilbert.StarJump

namespace OAI

universe uι uE

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_weight_param {E : Type uE} [TopologicalSpace E] (h u : ℝ)
    {p σ : E → ℝ} (hp : Continuous p) (hσ : Continuous σ) (hpos : ∀ t, 0 < σ t) :
    Continuous (fun t => weight h u (p t) (σ t)) := by
  unfold weight density
  have hden : ∀ t, Real.sqrt (2*Real.pi*σ t) ≠ 0 := fun t => (Real.sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) Real.pi_pos) (hpos t))).ne'
  apply continuous_const.mul
  apply Continuous.mul
  · exact (Real.continuous_sqrt.comp (continuous_const.mul hσ)).inv₀ hden
  · apply Real.continuous_exp.comp
    exact ((continuous_const.sub hp).pow 2 |>.neg).div (continuous_const.mul hσ) (fun t => (mul_pos (by norm_num) (hpos t)).ne')

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_heatArray_param {E : Type uE} [TopologicalSpace E]
    (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (v : Three) :
    Continuous (fun t => heatArray A h u (p t) (σ t) v) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hw (w : Three) (k : ι) : Continuous (fun t => (Real.sqrt (heatWeights h u (p t) (σ t) w k) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      (continuous_weight_param h (u k) ((continuous_apply w).comp hp) ((continuous_apply w).comp hσ) (hpos · w)))
  exact ((hw v i).mul continuous_const).mul (hw (v+1) j)

lemma continuous_heatRow_param {E : Type uE} [TopologicalSpace E]
    (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (v : Three) :
    Continuous (fun t => rowStar (heatArray A h u (p t) (σ t)) v) := by
  have he := continuous_heatArray_param A h u hp hσ hpos
  have hb (a b : Three) : Continuous (fun t => triangleBlocks (heatArray A h u (p t) (σ t)) a b) := by
    unfold triangleBlocks
    split_ifs <;> first | exact continuous_const | exact he _ | exact (he _).star
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [rowStar_apply]
  by_cases hv : a.1 = v
  · simp only [ite_eq_left hv]
    exact (continuous_apply b.2).comp ((continuous_apply a.2).comp (hb a.1 b.1))
  · simp only [ite_eq_right hv]
    exact continuous_const
end
end TriangularHilbert.Heat
end

end OAI
