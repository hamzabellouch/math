import OAI.Probability.InvariantIsing.Arrays.NSpinTensorLabeled
import OAI.Probability.InvariantIsing.Fields.CascadeTilt

namespace OAI

/-! The actual finite tensor terminal induces ancestor-dependent retained mark transitions. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal ENNReal

namespace InvariantIsing

def tensorCascadeBackward {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (i : ℕ) :
    (SpinTensorIndex I degree → ℝ) → ℝ :=
  backwardValue n b (fun j => tensorGaussianLaw I degree (v j)) (fun _ p => p.1 + p.2)
    (spinTensorTerminal eig U c I degree amplitude) i

def tensorCascadeStopped {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) :
    ℕ → ((SpinTensorIndex I degree → ℝ) × (SpinTensorIndex I degree → ℝ)) →
      (SpinTensorIndex I degree → ℝ) := stoppedUpdate n (fun _ p => p.1 + p.2)

def tensorCascadeMultiplier {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (i : ℕ)
    (p : (SpinTensorIndex I degree → ℝ) × (SpinTensorIndex I degree → ℝ)) : ℝ :=
  Real.exp (tensorCascadeBackward eig U c I degree amplitude n b v (i + 1)
      (tensorCascadeStopped I degree n i p) -
    tensorCascadeBackward eig U c I degree amplitude n b v i p.1)

lemma measurable_tensorCascadeBackward {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (i : ℕ) :
    Measurable (tensorCascadeBackward eig U c I degree amplitude n b v i) :=
  measurable_backwardValue n b (fun j => tensorGaussianLaw I degree (v j))
    (fun _ => measurable_fst.add measurable_snd)
    (measurable_spinTensorTerminal eig U c I degree amplitude) i

lemma measurable_tensorCascadeStopped {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n i : ℕ) :
    Measurable (tensorCascadeStopped I degree n i) :=
  measurable_stoppedUpdate n (fun _ => measurable_fst.add measurable_snd) i

lemma measurable_tensorCascadeMultiplier {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (i : ℕ) :
    Measurable (tensorCascadeMultiplier eig U c I degree amplitude n b v i) :=
  (((measurable_tensorCascadeBackward eig U c I degree amplitude n b v (i + 1)).comp
    (measurable_tensorCascadeStopped I degree n i)).sub
    ((measurable_tensorCascadeBackward eig U c I degree amplitude n b v i).comp measurable_fst)).exp

lemma tensorCascadeMultiplier_pos {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (i : ℕ)
    (z a : SpinTensorIndex I degree → ℝ) :
    0 < tensorCascadeMultiplier eig U c I degree amplitude n b v i (z, a) := Real.exp_pos _

/-- Each transition is normalized at its own cascade exponent, for every
ancestor state. The terminal is the actual finite Ising log partition. -/
lemma tensorCascadeMultiplier_moment {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (i : ℕ) (z : SpinTensorIndex I degree → ℝ) :
    (∫⁻ a, ENNReal.ofReal (tensorCascadeMultiplier eig U c I degree amplitude n b v i (z, a) ^ b i)
      ∂(tensorGaussianLaw I degree (v i) : Measure (SpinTensorIndex I degree → ℝ))) = 1 := by
  have hadm := backwardValue_linearGrowth_moments n b
    (fun j => tensorGaussianLaw I degree (v j))
    (fun j _ => tensorGaussianLaw_moments hN I degree (v j))
    (measurable_spinTensorTerminal eig U c I degree amplitude)
    (spinTensorTerminal_linearGrowth eig U c I degree amplitude) (fun j hj => (hb.1 j hj).1)
  exact backwardValue_multiplier_moment_admissible n b
    (fun j => tensorGaussianLaw I degree (v j)) (fun _ p => p.1 + p.2)
    (spinTensorTerminal eig U c I degree amplitude) (fun j hj => (hb.1 j hj).1) hadm i z

private lemma measurable_tensorAncestorMarkMeasure {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (i : ℕ) :
    Measurable (fun z => (tensorGaussianLaw I degree (v i) : Measure (SpinTensorIndex I degree → ℝ)).withDensity
    (fun a => ENNReal.ofReal (tensorCascadeMultiplier eig U c I degree amplitude n b v i (z, a) ^ b i))) := by
  let ν := fun _ : SpinTensorIndex I degree → ℝ =>
    (tensorGaussianLaw I degree (v i) : Measure (SpinTensorIndex I degree → ℝ))
  let W := fun p : (SpinTensorIndex I degree → ℝ) × (SpinTensorIndex I degree → ℝ) =>
    ENNReal.ofReal (tensorCascadeMultiplier eig U c I degree amplitude n b v i p ^ b i)
  have hW : Measurable W :=
    ((measurable_tensorCascadeMultiplier eig U c I degree amplitude n b v i).pow_const (b i)).ennreal_ofReal
  exact measurable_random_withDensity (ν := ν) (W := W) measurable_const hW

/-- The ancestor-dependent mark transition, with density `c_i(z,a)^b_i`. -/
def tensorAncestorMarkKernel {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (i : ℕ) :
    Kernel (SpinTensorIndex I degree → ℝ) (SpinTensorIndex I degree → ℝ) :=
  ⟨fun z => (tensorGaussianLaw I degree (v i) : Measure (SpinTensorIndex I degree → ℝ)).withDensity
    (fun a => ENNReal.ofReal (tensorCascadeMultiplier eig U c I degree amplitude n b v i (z, a) ^ b i)),
    measurable_tensorAncestorMarkMeasure eig U c I degree amplitude n b v i⟩

theorem tensorAncestorMarkKernel_markov {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (hb : CascadeExponents n b) (i : ℕ) :
    IsMarkovKernel (tensorAncestorMarkKernel eig U c I degree amplitude n b v i) := by
  constructor
  intro z
  constructor
  change ((tensorGaussianLaw I degree (v i) : Measure (SpinTensorIndex I degree → ℝ)).withDensity
    (fun a => ENNReal.ofReal (tensorCascadeMultiplier eig U c I degree amplitude n b v i (z, a) ^ b i))) Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  exact tensorCascadeMultiplier_moment hN eig U c I degree amplitude n b v hb i z

lemma tensorAncestorMarkKernel_density {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (i : ℕ) (hi : i < n) (z : SpinTensorIndex I degree → ℝ) :
    tensorAncestorMarkKernel eig U c I degree amplitude n b v i z =
      (tensorGaussianLaw I degree (v i) : Measure (SpinTensorIndex I degree → ℝ)).withDensity
        (fun a => ENNReal.ofReal (Real.exp (b i *
          (tensorCascadeBackward eig U c I degree amplitude n b v (i + 1) (z + a) -
            tensorCascadeBackward eig U c I degree amplitude n b v i z)))) := by
  change Measure.withDensity _ _ = _
  congr 1
  funext a
  simp only [tensorCascadeMultiplier, tensorCascadeStopped, stoppedUpdate, hi, ite_true, ← Real.exp_mul]
  rw [mul_comm]

def tensorRetainedCascade {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (z : SpinTensorIndex I degree → ℝ) :
    NoiseTree (SpinTensorIndex I degree → ℝ) n → NoiseTree (SpinTensorIndex I degree → ℝ) n :=
  noiseTreeKeep n b (fun i => tensorGaussianLaw I degree (v i))
    (tensorCascadeMultiplier eig U c I degree amplitude n b v) (tensorCascadeStopped I degree n) z

lemma measurable_tensorRetainedCascade {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (z : SpinTensorIndex I degree → ℝ) :
    Measurable (tensorRetainedCascade eig U c I degree amplitude n b v z) :=
  (measurable_noiseTreeKeep n b (fun i => tensorGaussianLaw I degree (v i))
    (measurable_tensorCascadeMultiplier eig U c I degree amplitude n b v)
    (measurable_tensorCascadeStopped I degree n)).comp (measurable_const.prodMk measurable_id)

/-- Forgetting the retained marks gives exactly the original raw cascade law. -/
theorem tensorRetainedCascade_forget_law {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ) :
    (tensorCascadeLaw I degree n b v).map
      (fun T => noiseTreeForget (SpinTensorIndex I degree → ℝ) n
        (tensorRetainedCascade eig U c I degree amplitude n b v z T)) = rawCascadeLaw n b := by
  have he : (fun T => noiseTreeForget (SpinTensorIndex I degree → ℝ) n
      (tensorRetainedCascade eig U c I degree amplitude n b v z T)) =
      noiseTreeDisplace n b (fun i => tensorGaussianLaw I degree (v i))
        (tensorCascadeMultiplier eig U c I degree amplitude n b v) (tensorCascadeStopped I degree n) z := by
    funext T
    exact noiseTreeKeep_forget n b (fun i => tensorGaussianLaw I degree (v i))
      (measurable_tensorCascadeMultiplier eig U c I degree amplitude n b v)
      (measurable_tensorCascadeStopped I degree n) z T
  rw [he]
  exact noiseTreeDisplace_law n b (fun i => tensorGaussianLaw I degree (v i))
    (measurable_tensorCascadeMultiplier eig U c I degree amplitude n b v)
    (measurable_tensorCascadeStopped I degree n)
    (tensorCascadeMultiplier_pos eig U c I degree amplitude n b v)
    (tensorCascadeMultiplier_moment hN eig U c I degree amplitude n b v hb) z

/-- The retained tree has the actual ancestor-dependent root mark kernel.
The descendant is transformed at the updated ancestor state; it is not
replaced by an independent level tilt. -/
theorem tensorRetainedCascade_law_succ {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents (n + 1) b) (z : SpinTensorIndex I degree → ℝ) :
    letI := tensorAncestorMarkKernel_markov hN eig U c I degree amplitude (n + 1) b v hb 0
    let μ := fun i => tensorGaussianLaw I degree (v i)
    let ct := tensorCascadeMultiplier eig U c I degree amplitude (n + 1) b v
    let ut := tensorCascadeStopped I degree (n + 1)
    let P := (noiseCascadeLaw (SpinTensorIndex I degree → ℝ) n
      (fun i => b (i + 1)) (fun i => μ (i + 1)) : Measure (NoiseTree (SpinTensorIndex I degree → ℝ) n))
    let G := fun p : (SpinTensorIndex I degree → ℝ) × NoiseTree (SpinTensorIndex I degree → ℝ) n =>
      (p.1, noiseTreeKeep n (fun i => b (i + 1)) (fun i => μ (i + 1))
        (fun i => ct (i + 1)) (fun i => ut (i + 1)) (ut 0 (z, p.1)) p.2)
    (tensorCascadeLaw I degree (n + 1) b v).map
      (tensorRetainedCascade eig U c I degree amplitude (n + 1) b v z) =
      poissonLaw ((powerIntensity (b 0)).prod
        (((tensorAncestorMarkKernel eig U c I degree amplitude (n + 1) b v 0 z).prod P).map G)) := by
  let := tensorAncestorMarkKernel_markov hN eig U c I degree amplitude (n + 1) b v hb 0
  intro μ ct ut P G
  have h := noiseTreeKeep_law_succ n b μ
    (measurable_tensorCascadeMultiplier eig U c I degree amplitude (n + 1) b v)
    (measurable_tensorCascadeStopped I degree (n + 1))
    (tensorCascadeMultiplier_pos eig U c I degree amplitude (n + 1) b v) z
  have hd : Measurable (fun a : SpinTensorIndex I degree → ℝ => ENNReal.ofReal (ct 0 (z, a) ^ b 0)) :=
    (((measurable_tensorCascadeMultiplier eig U c I degree amplitude (n + 1) b v 0).comp
      (measurable_const.prodMk measurable_id)).pow_const (b 0)).ennreal_ofReal
  change (tensorCascadeLaw I degree (n + 1) b v).map
      (tensorRetainedCascade eig U c I degree amplitude (n + 1) b v z) =
    poissonLaw ((powerIntensity (b 0)).prod
      ((((μ 0 : Measure (SpinTensorIndex I degree → ℝ)).withDensity
        (fun a => ENNReal.ofReal (ct 0 (z, a) ^ b 0))).prod P).map G))
  apply h.trans
  apply poissonLaw_congr
  exact congrArg (fun Q => (powerIntensity (b 0)).prod (Q.map G))
    (prod_withDensity_left (ν := P) hd).symm

private lemma tensorLeafTerminal_last {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (X : ℕ → (SpinTensorIndex I degree → ℝ) → ℝ)
    (u : ℕ → ((SpinTensorIndex I degree → ℝ) × (SpinTensorIndex I degree → ℝ)) →
      (SpinTensorIndex I degree → ℝ)) (F : (SpinTensorIndex I degree → ℝ) → ℝ)
    (hX : X n = F) (hu : ∀ i < n, u i = fun p => p.1 + p.2)
    (z : SpinTensorIndex I degree → ℝ) (leaf : NoiseLeaf (SpinTensorIndex I degree → ℝ) n) :
    noiseLeafTerminal n X u z leaf = F (tensorLeafState I degree n z leaf) := by
  induction n generalizing X u z with
  | zero => simpa only [noiseLeafTerminal, tensorLeafState] using congrFun hX z
  | succ n ih =>
    rw [noiseLeafTerminal, hu 0 (by omega)]
    exact ih (fun i => X (i + 1)) (fun i => u (i + 1))
      (by simpa only [Nat.add_comm] using hX) (fun i hi => hu (i + 1) (by omega))
      (z + leaf.2.1) leaf.2.2

def tensorTerminalLeafLaw {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) (T : NoiseTree (SpinTensorIndex I degree → ℝ) n) :
    Measure (NoiseLeaf (SpinTensorIndex I degree → ℝ) n) :=
  normalizeMass ((noiseLeafKernel (SpinTensorIndex I degree → ℝ) n T).withDensity
    (fun leaf => ENNReal.ofReal (Real.exp
      (spinTensorTerminal eig U c I degree amplitude (tensorLeafState I degree n z leaf)))))

lemma tensorTerminalLeafLaw_eq_backward {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (z : SpinTensorIndex I degree → ℝ) (T : NoiseTree (SpinTensorIndex I degree → ℝ) n) :
    tensorTerminalLeafLaw eig U c I degree amplitude n z T =
      noiseTerminalGibbsLaw n (tensorCascadeBackward eig U c I degree amplitude n b v)
        (tensorCascadeStopped I degree n) z T := by
  have hX : tensorCascadeBackward eig U c I degree amplitude n b v n =
      spinTensorTerminal eig U c I degree amplitude :=
    backwardValue_terminal n b (fun i => tensorGaussianLaw I degree (v i))
      (fun _ p => p.1 + p.2) (spinTensorTerminal eig U c I degree amplitude) (le_refl n)
  have hu : ∀ i < n, tensorCascadeStopped I degree n i = fun p => p.1 + p.2 := by
    intro i hi
    funext p
    simp only [tensorCascadeStopped, stoppedUpdate, hi, ite_true]
  unfold tensorTerminalLeafLaw noiseTerminalGibbsLaw
  congr 2
  funext leaf
  rw [tensorLeafTerminal_last I degree n _ _ _ hX hu]

/-- Sampling after the actual terminal tilt is transported to ordinary
sampling from the retained marked tree, with every mark kept. -/
theorem tensorTerminalLeafLaw_keep_ae {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ) :
    ∀ᵐ T ∂tensorCascadeLaw I degree n b v,
      (tensorTerminalLeafLaw eig U c I degree amplitude n z T).map
        (noiseLeafKeep n (tensorCascadeMultiplier eig U c I degree amplitude n b v)
          (tensorCascadeStopped I degree n) z) =
        noiseLeafKernel (SpinTensorIndex I degree → ℝ) n
          (tensorRetainedCascade eig U c I degree amplitude n b v z T) := by
  have hr := noiseGibbsRegular_ae n b hb (fun i => tensorGaussianLaw I degree (v i))
    (measurable_tensorCascadeMultiplier eig U c I degree amplitude n b v)
    (measurable_tensorCascadeStopped I degree n)
    (tensorCascadeMultiplier_pos eig U c I degree amplitude n b v)
    (tensorCascadeMultiplier_moment hN eig U c I degree amplitude n b v hb) z
  filter_upwards [hr] with T hT
  rw [tensorTerminalLeafLaw_eq_backward eig U c I degree amplitude n b v]
  exact noiseTerminalGibbsLaw_keep n b (fun i => tensorGaussianLaw I degree (v i))
    (measurable_tensorCascadeBackward eig U c I degree amplitude n b v)
    (measurable_tensorCascadeStopped I degree n) z T hT

end InvariantIsing

end

end OAI
