import Mathlib
import OAI.Probability.SKBarriers.Gaussian.LocalGaussian

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

def ParamExpGrowth {P E F : Type} [Norm P] [Norm E] [Norm F]
    (f : P × E → F) : Prop :=
  ∀ R : ℝ, ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧
    ∀ p e, ‖p‖ ≤ R → ‖f (p,e)‖ ≤ C*Real.exp (M*‖e‖)

def ParamLinearGrowth {P E : Type} [Norm P] [Norm E]
    (f : P × E → ℝ) : Prop :=
  ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ p e, ‖p‖ ≤ R → |f (p,e)| ≤ C*(1+‖e‖)

theorem ParamExpGrowth.of_norm_le {P E F G : Type} [Norm P] [Norm E] [Norm F] [Norm G]
    {f : P × E → F} (hf : ParamExpGrowth f)
    {g : P × E → G} {K : ℝ} (hK : 0 ≤ K) (hg : ∀ z, ‖g z‖ ≤ K*‖f z‖) :
    ParamExpGrowth g := by
  intro R
  obtain ⟨C,M,hC,hM,hf⟩ := hf R
  refine ⟨K*C,M,mul_nonneg hK hC,hM,?_⟩
  intro p e hp
  exact (hg (p,e)).trans ((mul_le_mul_of_nonneg_left (hf p e hp) hK).trans_eq (mul_assoc _ _ _).symm)

section ParameterGrowth
variable {P E F G : Type} [NormedAddCommGroup P] [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedAddCommGroup G]

theorem ParamExpGrowth.of_bounded {f : P × E → F} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ z, ‖f z‖ ≤ C) : ParamExpGrowth f := by
  intro R
  refine ⟨C,0,hC,le_rfl,?_⟩
  intro p e _
  simpa only [zero_mul,Real.exp_zero,mul_one] using hf (p,e)

theorem ParamExpGrowth.add {f g : P × E → F} (hf : ParamExpGrowth f)
    (hg : ParamExpGrowth g) : ParamExpGrowth (fun z => f z+g z) := by
  intro R
  obtain ⟨C,M,hC,hM,hf⟩ := hf R
  obtain ⟨D,L,hD,hL,hg⟩ := hg R
  refine ⟨C+D,max M L,add_nonneg hC hD,(le_max_left M L).trans' hM,?_⟩
  intro p e hp
  calc
    _ ≤ ‖f (p,e)‖+‖g (p,e)‖ := norm_add_le _ _
    _ ≤ C*Real.exp (M*‖e‖)+D*Real.exp (L*‖e‖) := add_le_add (hf p e hp) (hg p e hp)
    _ ≤ C*Real.exp (max M L*‖e‖)+D*Real.exp (max M L*‖e‖) := by
      gcongr <;> first | exact le_max_left _ _ | exact le_max_right _ _
    _ = _ := by ring

theorem ParamExpGrowth.mul {f g : P × E → ℝ} (hf : ParamExpGrowth f)
    (hg : ParamExpGrowth g) : ParamExpGrowth (fun z => f z*g z) := by
  intro R
  obtain ⟨C,M,hC,hM,hf⟩ := hf R
  obtain ⟨D,L,hD,hL,hg⟩ := hg R
  refine ⟨C*D,M+L,mul_nonneg hC hD,add_nonneg hM hL,?_⟩
  intro p e hp
  calc
    ‖f (p,e)*g (p,e)‖ = ‖f (p,e)‖*‖g (p,e)‖ := norm_mul _ _
    _ ≤ (C*Real.exp (M*‖e‖))*(D*Real.exp (L*‖e‖)) :=
      mul_le_mul (hf p e hp) (hg p e hp) (norm_nonneg _) (by positivity)
    _ = _ := by rw [add_mul,Real.exp_add]; ring

theorem ParamExpGrowth.norm {f : P × E → F} (hf : ParamExpGrowth f) :
    ParamExpGrowth (fun z => ‖f z‖) := by
  apply hf.of_norm_le (K := 1) (by norm_num)
  intro z
  simp

theorem ParamLinearGrowth.exp_mul {f : P × E → ℝ} (hf : ParamLinearGrowth f) (m : ℝ) :
    ParamExpGrowth (fun z => Real.exp (m*f z)) := by
  intro R
  obtain ⟨C,hC,hf⟩ := hf R
  refine ⟨Real.exp (|m| *C),|m| *C,(Real.exp_pos _).le,mul_nonneg (abs_nonneg _) hC,?_⟩
  intro p e hp
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
  apply Real.exp_le_exp.2
  calc
    m*f (p,e) ≤ |m*f (p,e)| := le_abs_self _
    _ = |m| *|f (p,e)| := abs_mul _ _
    _ ≤ |m| *(C*(1+‖e‖)) := mul_le_mul_of_nonneg_left (hf p e hp) (abs_nonneg m)
    _ = _ := by ring

theorem ParamLinearGrowth.expGrowth {f : P × E → ℝ} (hf : ParamLinearGrowth f) :
    ParamExpGrowth f := by
  intro R
  obtain ⟨C,hC,hf⟩ := hf R
  refine ⟨C,1,hC,by norm_num,?_⟩
  intro p e hp
  rw [one_mul,Real.norm_eq_abs]
  exact (hf p e hp).trans (mul_le_mul_of_nonneg_left (by have h := Real.add_one_le_exp ‖e‖; linarith) hC)

theorem ParamExpGrowth.locallyDominated {f : P × (E × ℝ) → F} (hf : ParamExpGrowth f) :
    GaussianLocallyDominated (fun z : (P × E) × ℝ => f (z.1.1,(z.1.2,z.2))) := by
  intro R
  obtain ⟨C,M,hC,hM,hf⟩ := hf R
  refine ⟨fun y => C*Real.exp (M*R)*Real.exp (M*|y|),
    (integrable_exp_mul_abs_gaussian M).const_mul _,?_⟩
  rintro ⟨p,e⟩ y hpe
  have hp : ‖p‖ ≤ R := (le_max_left _ _).trans hpe
  have he : ‖e‖ ≤ R := (le_max_right _ _).trans hpe
  apply (hf p (e,y) hp).trans
  change C*Real.exp (M*‖(e,y)‖) ≤ C*Real.exp (M*R)*Real.exp (M*|y|)
  rw [mul_assoc,← Real.exp_add,← mul_add]
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.2
  apply mul_le_mul_of_nonneg_left _ hM
  rw [Prod.norm_def,Real.norm_eq_abs]
  exact max_le (he.trans (le_add_of_nonneg_right (abs_nonneg _)))
    (le_add_of_nonneg_left ((norm_nonneg e).trans he))

variable [NormedSpace ℝ F] [NormedSpace ℝ G]

theorem ParamExpGrowth.clm {f : P × E → F} (hf : ParamExpGrowth f) (L : F →L[ℝ] G) :
    ParamExpGrowth (fun z => L (f z)) := hf.of_norm_le (norm_nonneg L) (fun z => L.le_opNorm (f z))

theorem ParamExpGrowth.smul {f : P × E → ℝ} {g : P × E → F}
    (hf : ParamExpGrowth f) (hg : ParamExpGrowth g) : ParamExpGrowth (fun z => f z • g z) := by
  apply (hf.norm.mul hg.norm).of_norm_le (K := 1) (by norm_num)
  intro z
  simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_abs,abs_of_nonneg (norm_nonneg _),one_mul]
  exact le_rfl

theorem ParamExpGrowth.gaussian_integral {f : P × (E × ℝ) → F}
    (hf : ParamExpGrowth f) :
    ParamExpGrowth (fun z : P × E => ∫ y, f (z.1,(z.2,y)) ∂gaussianReal 0 1) := by
  intro R
  obtain ⟨C,M,hC,hM,hf⟩ := hf R
  let B := ∫ y : ℝ, Real.exp (M*|y|) ∂gaussianReal 0 1
  have hB : 0 ≤ B := integral_nonneg (fun y => (Real.exp_pos _).le)
  refine ⟨C*B,M,mul_nonneg hC hB,hM,?_⟩
  intro p e hp
  have hb : ∀ y, ‖f (p,(e,y))‖ ≤ C*Real.exp (M*‖e‖)*Real.exp (M*|y|) := by
    intro y
    apply (hf p (e,y) hp).trans
    rw [mul_assoc,← Real.exp_add,← mul_add]
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.exp_le_exp.2
    apply mul_le_mul_of_nonneg_left _ hM
    rw [Prod.norm_def,Real.norm_eq_abs]
    exact max_le_add_of_nonneg (norm_nonneg e) (abs_nonneg y)
  calc
    _ ≤ ∫ y, ‖f (p,(e,y))‖ ∂gaussianReal 0 1 := norm_integral_le_integral_norm _
    _ ≤ ∫ y, C*Real.exp (M*‖e‖)*Real.exp (M*|y|) ∂gaussianReal 0 1 :=
      integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _))
        ((integrable_exp_mul_abs_gaussian M).const_mul _) (ae_of_all _ hb)
    _ = _ := by rw [integral_const_mul]; dsimp [B]; ring
end ParameterGrowth
end SK.Analytic

end
end

end

end OAI
