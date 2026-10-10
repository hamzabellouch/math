import OAI.Probability.InvariantIsing.Fields.VectorTerminalCascade
import OAI.Probability.InvariantIsing.Fields.CascadeSeedReplicaLaw
import OAI.Probability.InvariantIsing.Fields.CascadeKeepUpdate
import OAI.Probability.IsingPerceptron.NoiseGibbsRegular

namespace OAI

/-! Terminal Gibbs sampling and retained trees for finite vector fields. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal ENNReal
namespace InvariantIsing

def vectorLeafSum (N : ℕ) : (n : ℕ) → (Fin N → ℝ) → NoiseLeaf (Fin N → ℝ) n → (Fin N → ℝ)
  | 0,z,_ => z
  | n+1,z,w => vectorLeafSum N n (z+w.2.1) w.2.2

lemma measurable_vectorLeafSum (N n : ℕ) :
    Measurable (fun p : (Fin N → ℝ) × NoiseLeaf (Fin N → ℝ) n => vectorLeafSum N n p.1 p.2) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih => exact ih.comp ((measurable_fst.add measurable_snd.snd.fst).prodMk measurable_snd.snd.snd)

lemma noiseLeafTerminal_vector_sum (N n : ℕ) (X : ℕ → (Fin N → ℝ) → ℝ)
    (u : ℕ → (Fin N → ℝ) × (Fin N → ℝ) → (Fin N → ℝ))
    (F : (Fin N → ℝ) → ℝ) (hX : X n = F)
    (hu : ∀ i < n, u i = fun p => p.1+p.2) (z : Fin N → ℝ) (w : NoiseLeaf (Fin N → ℝ) n) :
    noiseLeafTerminal n X u z w = F (vectorLeafSum N n z w) := by
  induction n generalizing X u z with
  | zero => exact congrFun hX z
  | succ n ih =>
    rw [noiseLeafTerminal,hu 0 (by omega)]
    exact ih (fun i => X (i+1)) (fun i => u (i+1))
      (by simpa only [Nat.add_comm] using hX) (fun i hi => hu (i+1) (by omega)) (z+w.2.1) w.2.2

def vectorTerminalNoiseLaw (N n : ℕ) (F : (Fin N → ℝ) → ℝ)
    (z : Fin N → ℝ) (T : NoiseTree (Fin N → ℝ) n) : Measure (NoiseLeaf (Fin N → ℝ) n) :=
  normalizeMass ((noiseLeafKernel (Fin N → ℝ) n T).withDensity
    (fun w => ENNReal.ofReal (Real.exp (F (vectorLeafSum N n z w)))))

instance vectorTerminalNoiseLaw_probability (N n : ℕ) (F : (Fin N → ℝ) → ℝ)
    (z : Fin N → ℝ) (T : NoiseTree (Fin N → ℝ) n) :
    IsProbabilityMeasure (vectorTerminalNoiseLaw N n F z T) := normalizeMass_probability _

lemma measurable_vectorTerminalNoiseLaw (N n : ℕ) (F : (Fin N → ℝ) → ℝ) (hF : Measurable F)
    (z : Fin N → ℝ) : Measurable (vectorTerminalNoiseLaw N n F z) :=
  measurable_normalizeMass.comp ((measurable_withDensity_fixed
    ((hF.comp ((measurable_vectorLeafSum N n).comp (measurable_const.prodMk measurable_id))).exp.ennreal_ofReal)).comp
      (noiseLeafKernel (Fin N → ℝ) n).measurable)

lemma vectorTerminalNoiseLaw_eq_backward (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (z : Fin N → ℝ) (T : NoiseTree (Fin N → ℝ) n) :
    vectorTerminalNoiseLaw N n F z T = noiseTerminalGibbsLaw n
      (vectorTerminalBackward N n b v F) (vectorTerminalUpdate N n) z T := by
  have hX : vectorTerminalBackward N n b v F n = F :=
    backwardValue_terminal n b (fun j => vectorGaussianLaw N (v j)) (fun _ p => p.1+p.2) F (le_refl n)
  have hu : ∀ i < n, vectorTerminalUpdate N n i = fun p => p.1+p.2 := by
    intro i hi
    funext p
    simp only [vectorTerminalUpdate,stoppedUpdate,hi,ite_true]
  unfold vectorTerminalNoiseLaw noiseTerminalGibbsLaw
  congr 2
  funext w
  rw [noiseLeafTerminal_vector_sum N n _ _ _ hX hu]

lemma vectorTerminalNoiseLaw_keep_ae {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ) :
    ∀ᵐ T ∂(noiseCascadeLaw (Fin N → ℝ) n b (fun i => vectorGaussianLaw N (v i)) : Measure (NoiseTree (Fin N → ℝ) n)),
      (vectorTerminalNoiseLaw N n F z T).map
        (noiseLeafKeep n (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z) =
      noiseLeafKernel (Fin N → ℝ) n (noiseTreeKeep n b (fun i => vectorGaussianLaw N (v i))
        (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z T) := by
  have hr := noiseGibbsRegular_ae n b hb (fun i => vectorGaussianLaw N (v i))
    (measurable_vectorTerminalMultiplier N n b v F hF) (measurable_vectorTerminalUpdate N n)
    (fun _ _ _ => Real.exp_pos _) (vectorTerminalMultiplier_moment hN n b v hb F hF hG) z
  filter_upwards [hr] with T hT
  rw [vectorTerminalNoiseLaw_eq_backward]
  exact noiseTerminalGibbsLaw_keep n b (fun i => vectorGaussianLaw N (v i))
    (measurable_vectorTerminalBackward N n b v F hF) (measurable_vectorTerminalUpdate N n) z T hT

end InvariantIsing

end

end OAI
