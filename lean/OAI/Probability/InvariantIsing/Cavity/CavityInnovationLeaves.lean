import OAI.Probability.InvariantIsing.Cavity.CavityQuadraticTree

namespace OAI

/-! Leaf transport for the retained quadratic innovation tree. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal

namespace InvariantIsing

def cavityInnovationLeaf {d : ℕ} : (n : ℕ) →
    (ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ) →
    (ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) →
    EuclideanSpace ℝ (Fin d) → NoiseLeaf (EuclideanSpace ℝ (Fin d)) n →
      NoiseLeaf (EuclideanSpace ℝ (Fin d)) n
  | 0, _, _, _, _ => PUnit.unit
  | n + 1, c, g, s, v => (c 0 (s, v.2.1) * v.1, (g 0 (s, v.2.1),
      cavityInnovationLeaf n (fun i => c (i + 1)) (fun i => g (i + 1))
        (s + v.2.1) v.2.2))

lemma measurable_cavityInnovationLeaf {d : ℕ} (n : ℕ)
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (g : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hc : ∀ i, Measurable (c i)) (hg : ∀ i, Measurable (g i)) :
    Measurable (fun p : EuclideanSpace ℝ (Fin d) × NoiseLeaf (EuclideanSpace ℝ (Fin d)) n =>
      cavityInnovationLeaf n c g p.1 p.2) := by
  induction n generalizing c g with
  | zero => exact measurable_const
  | succ n ih =>
    exact (((hc 0).comp (by fun_prop)).mul (by fun_prop)).prodMk
      (((hg 0).comp (by fun_prop)).prodMk
        ((ih _ _ (fun i => hc (i + 1)) (fun i => hg (i + 1))).comp
          ((measurable_fst.add measurable_snd.snd.fst).prodMk measurable_snd.snd.snd)))

lemma cavityInnovationTree_forget {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (g : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hc : ∀ i, Measurable (c i)) (hg : ∀ i, Measurable (g i))
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n) :
    noiseTreeForget _ n (cavityInnovationTree n b μ c g s V) =
      noiseTreeForget _ n (noiseTreeKeep n b μ c (fun _ p => p.1 + p.2) s V) := by
  induction n generalizing b μ c g s with
  | zero => rfl
  | succ n ih =>
    let bt := fun i => b (i + 1)
    let μt := fun i => μ (i + 1)
    let ct := fun i => c (i + 1)
    let gt := fun i => g (i + 1)
    let F := fun p : ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) =>
      (c 0 (s, p.2.1) * p.1, (g 0 (s, p.2.1),
        cavityInnovationTree n bt μt ct gt (s + p.2.1) p.2.2))
    let G := fun p : ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) =>
      (c 0 (s, p.2.1) * p.1, (p.2.1,
        noiseTreeKeep n bt μt ct (fun _ p => p.1 + p.2) (s + p.2.1) p.2.2))
    have hF : Measurable F :=
      (((hc 0).comp (by fun_prop)).mul (by fun_prop)).prodMk
        (((hg 0).comp (by fun_prop)).prodMk
          ((measurable_cavityInnovationTree n bt μt ct gt
            (fun i => hc (i + 1)) (fun i => hg (i + 1))).comp
              ((measurable_const.add measurable_snd.fst).prodMk measurable_snd.snd)))
    have hG : Measurable G :=
      (((hc 0).comp (by fun_prop)).mul (by fun_prop)).prodMk
        (measurable_snd.fst.prodMk
          ((measurable_noiseTreeKeep n bt μt (fun i => hc (i + 1))
            (fun _ => measurable_fst.add measurable_snd)).comp
              ((measurable_const.add measurable_snd.fst).prodMk measurable_snd.snd)))
    change Measure.map (fun p => (p.1, noiseTreeForget _ n p.2.2))
      (Measure.map F _) = Measure.map (fun p => (p.1, noiseTreeForget _ n p.2.2))
        (Measure.map G _)
    have hforget : Measurable (fun p :
        ℝ × (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) =>
        (p.1, noiseTreeForget _ n p.2.2)) :=
      measurable_fst.prodMk ((measurable_noiseTreeForget _ n).comp measurable_snd.snd)
    rw [Measure.map_map hforget hF, Measure.map_map hforget hG]
    congr 1
    funext p
    exact Prod.ext rfl (ih bt μt ct gt (fun i => hc (i + 1)) (fun i => hg (i + 1))
      (s + p.2.1) p.2.2)

lemma cavityInnovationTree_total {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (g : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hc : ∀ i, Measurable (c i)) (hg : ∀ i, Measurable (g i))
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n) :
    noiseTreeTotal _ n (cavityInnovationTree n b μ c g s V) =
      noiseTreeTotal _ n (noiseTreeKeep n b μ c (fun _ p => p.1 + p.2) s V) := by
  unfold noiseTreeTotal
  rw [cavityInnovationTree_forget n b μ c g hc hg s V]

def cavityLeafSum {d : ℕ} : (n : ℕ) → EuclideanSpace ℝ (Fin d) →
    NoiseLeaf (EuclideanSpace ℝ (Fin d)) n → EuclideanSpace ℝ (Fin d)
  | 0, s, _ => s
  | n + 1, s, v => cavityLeafSum n (s + v.2.1) v.2.2

/-- The transformed increments telescope to the rescaled final sum. -/
theorem cavityInnovationLeaf_sum {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (s : EuclideanSpace ℝ (Fin d)) (v : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n) :
    cavityLeafSum n (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹ s)
      (cavityInnovationLeaf n c (fun i => cavityStepInnovation K (H i) (H (i + 1))) s v) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H n * K)⁻¹ (cavityLeafSum n s v) := by
  induction n generalizing H c s with
  | zero => rfl
  | succ n ih =>
    simp only [cavityLeafSum, cavityInnovationLeaf]
    have he : Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹ s +
        cavityStepInnovation K (H 0) (H 1) (s, v.2.1) =
        Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 1 * K)⁻¹ (s + v.2.1) := by
      unfold cavityStepInnovation
      abel
    rw [he]
    exact ih (fun i => H (i + 1)) (fun i => c (i + 1)) (s + v.2.1) v.2.2

theorem cavityInnovationLeaf_terminal_sum {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (c : ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (hH : H n = 0) (s : EuclideanSpace ℝ (Fin d))
    (v : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n) :
    cavityLeafSum n (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹ s)
      (cavityInnovationLeaf n c (fun i => cavityStepInnovation K (H i) (H (i + 1))) s v) =
      cavityLeafSum n s v := by
  rw [cavityInnovationLeaf_sum n K H c s v, hH]
  simp only [zero_mul, sub_zero, inv_one, map_one, one_apply_eq_self]

end InvariantIsing

end

end OAI
