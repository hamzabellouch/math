import OAI.Probability.InvariantIsing.Fields.VectorTerminalCascade

namespace OAI

/-! The normalized ancestor increments induce the actual Gaussian field transition. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

lemma vectorTerminalBackward_regular {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (i : ℕ) :
    Measurable (vectorTerminalBackward N n b v F i) ∧ HasLinearGrowth (vectorTerminalBackward N n b v F i) := by
  refine ⟨measurable_vectorTerminalBackward N n b v F hF i,?_⟩
  exact cascadeRecursion_linearGrowth (n-i) (fun j => b (i+j))
    (fun j => vectorGaussianLaw N (v (i+j)))
    (fun j _ => vectorGaussianLaw_moments hN (v (i+j))) hF hG
    (fun j hj => (hb.1 (i+j) (by omega)).1)

lemma vectorTerminalAncestorKernel_eq_tilted {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (i : ℕ) (hi : i < n) (z : Fin N → ℝ) :
    vectorTerminalAncestorKernel N n b v F hF i z =
      (vectorGaussianLaw N (v i) : Measure (Fin N → ℝ)).tilted
        (fun a => b i * vectorTerminalBackward N n b v F (i+1) (z+a)) := by
  have hint := backwardValue_linearGrowth_moments n b (fun j => vectorGaussianLaw N (v j))
    (fun j _ => vectorGaussianLaw_moments hN (v j)) hF hG (fun j hj => (hb.1 j hj).1) i hi z
  have hp := IsingPerceptron.integral_exp_pos (vectorGaussianLaw N (v i) : Measure (Fin N → ℝ))
    (fun a => vectorTerminalBackward N n b v F (i+1) (z+a)) hint
  have hd : vectorTerminalAncestorKernel N n b v F hF i z =
      (vectorGaussianLaw N (v i) : Measure (Fin N → ℝ)).withDensity
        (fun a => ENNReal.ofReal (Real.exp (b i *
          (vectorTerminalBackward N n b v F (i+1) (z+a) - vectorTerminalBackward N n b v F i z)))) := by
    change Measure.withDensity _ _ = _
    congr 1
    funext a
    simp only [vectorTerminalMultiplier,vectorTerminalUpdate,stoppedUpdate,hi,ite_true,← Real.exp_mul]
    rw [mul_comm]
  have hs : vectorTerminalBackward N n b v F i z =
      logMean (b i) (vectorGaussianLaw N (v i) : Measure (Fin N → ℝ))
        (fun a => vectorTerminalBackward N n b v F (i+1) (z+a)) :=
    backwardValue_step n b (fun j => vectorGaussianLaw N (v j)) (fun _ p => p.1+p.2) F hi z
  rw [hd,hs]
  unfold Measure.tilted
  congr 1
  funext a
  congr 1
  have hx (x y : ℝ) : b i * (x - Real.log y / b i) = b i*x - Real.log y := by
    field_simp [(hb.1 i hi).1.ne']
  rw [logMean,hx,Real.exp_sub,Real.exp_log hp]

lemma vectorTerminalAncestorKernel_add {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (i : ℕ) (hi : i < n) (z : Fin N → ℝ) :
    (vectorTerminalAncestorKernel N n b v F hF i z).map (fun a => z+a) =
      vectorGaussianTransition N (b i) (v i) (vectorTerminalBackward N n b v F (i+1))
        (measurable_vectorTerminalBackward N n b v F hF (i+1)) z := by
  rw [vectorTerminalAncestorKernel_eq_tilted hN n b v hb F hF hG i hi z]
  exact (vectorGaussianTransition_eq_map hN (b i) (v i) _
    (measurable_vectorTerminalBackward N n b v F hF (i+1))
    (vectorTerminalBackward_regular hN n b v hb F hF hG (i+1)).2 z).symm

end InvariantIsing

end

end OAI
