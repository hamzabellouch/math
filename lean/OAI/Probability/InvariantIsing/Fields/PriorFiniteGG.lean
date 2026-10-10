import OAI.Probability.InvariantIsing.Fields.PriorKernelDiagonal

namespace OAI

/-! The actual finite constrained-prior spectral Ghirlanda–Guerra residual. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def priorSpectralGGResidual {N m k n q : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν₀ : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k)
    (D : SpecialOrthogonal N → (Fin (q + 1) → Spin N × LabeledLeaf n) → ℝ) : ℝ :=
  let avg := fun (q' : ℕ) (F : SpecialOrthogonal N → (Fin q' → Spin N × LabeledLeaf n) → ℝ) =>
    priorNamespacedReplicaAverage μ ν₀ eig c I degree amplitude r h F
  let κ := spectralPerturbationKernel (id : SpecialOrthogonal N → SpecialOrthogonal N) I (degree j) n (r j)
  (q + 1 : ℕ) * avg (q + 1 + 1)
      (fun U τ => D U (Fin.tail τ) * κ U ((Fin.tail τ) 0) (τ 0)) -
    avg (q + 1) D * avg 2 (fun U τ => κ U (τ 1) (τ 0)) -
    avg (q + 1)
      (fun U σ => D U σ * ∑ l : Fin q, κ U (σ 0) (σ l.succ))

private lemma measurable_ggFresh {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {q : ℕ} (D : Ω → (Fin (q + 1) → X) → ℝ) (κ : Ω → X → X → ℝ)
    (hD : Measurable (Function.uncurry D))
    (hκ : Measurable (fun p : Ω × (X × X) => κ p.1 p.2.1 p.2.2)) :
    Measurable (Function.uncurry (fun V (τ : Fin (q + 1 + 1) → X) =>
      D V (Fin.tail τ) * κ V ((Fin.tail τ) 0) (τ 0))) := by
  have ht : Measurable (fun p : Ω × (Fin (q + 1 + 1) → X) => (p.1, Fin.tail p.2)) :=
    measurable_fst.prodMk (Measurable.of_eval fun a =>
      (measurable_pi_apply a.succ).comp measurable_snd)
  have hk : Measurable (fun p : Ω × (Fin (q + 1 + 1) → X) =>
      (p.1, ((Fin.tail p.2) 0, p.2 0))) :=
    measurable_fst.prodMk (((measurable_pi_apply (0 : Fin (q + 1)).succ).comp measurable_snd).prodMk
      ((measurable_pi_apply 0).comp measurable_snd))
  exact (hD.comp ht).mul (hκ.comp hk)

private lemma measurable_ggPair {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (κ : Ω → X → X → ℝ)
    (hκ : Measurable (fun p : Ω × (X × X) => κ p.1 p.2.1 p.2.2)) :
    Measurable (Function.uncurry (fun V (τ : Fin 2 → X) => κ V (τ 1) (τ 0))) := by
  have h1 : Measurable (fun p : Ω × (Fin 2 → X) => p.2 1) :=
    (measurable_pi_apply 1).comp measurable_snd
  have h0 : Measurable (fun p : Ω × (Fin 2 → X) => p.2 0) :=
    (measurable_pi_apply 0).comp measurable_snd
  exact hκ.comp (measurable_fst.prodMk (h1.prodMk h0))

private lemma measurable_ggOld {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {q : ℕ} (D : Ω → (Fin (q + 1) → X) → ℝ) (κ : Ω → X → X → ℝ)
    (hD : Measurable (Function.uncurry D))
    (hκ : Measurable (fun p : Ω × (X × X) => κ p.1 p.2.1 p.2.2)) :
    Measurable (Function.uncurry (fun V (σ : Fin (q + 1) → X) =>
      D V σ * ∑ l : Fin q, κ V (σ 0) (σ l.succ))) := by
  apply hD.mul
  apply Finset.measurable_sum
  intro l _
  have h0 : Measurable (fun p : Ω × (Fin (q + 1) → X) => p.2 0) :=
    (measurable_pi_apply 0).comp measurable_snd
  have hl : Measurable (fun p : Ω × (Fin (q + 1) → X) => p.2 l.succ) :=
    (measurable_pi_apply l.succ).comp measurable_snd
  exact hκ.comp (measurable_fst.prodMk (h0.prodMk hl))

theorem priorFiniteGG_bound {N m k n q : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν₀ : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν₀] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (j : Fin k) (β d₀ e C : ℝ) (hC : 0 ≤ C)
    (D : SpecialOrthogonal N → (Fin (q + 1) → Spin N × LabeledLeaf n) → ℝ)
    (hD : Measurable (Function.uncurry D)) (hDb : ∀ U σ, |D U σ| ≤ C)
    (hE :
      let A := spectralPerturbationCoefficients (fun ω : PriorFrozenData N j => ω.1)
        I (degree j) n (r j)
      let ν := priorFrozenReference ν₀ eig c I degree amplitude r h j
      let E := fun p : PriorFrozenData N j × (ℕ → ℝ) => ∫ x,
        |cylinderField (A p.1 x) p.2 - β|
        ∂(ν p.1).tilted (fun x => amplitude j * cylinderField (A p.1 x) p.2)
      Integrable E ((priorFrozenLaw μ j).prod gaussianCoordinates) ∧
        (∫ p, E p ∂(priorFrozenLaw μ j).prod gaussianCoordinates) ≤ e) :
    |amplitude j| * |priorSpectralGGResidual μ ν₀ eig c I degree amplitude r h j D| ≤
      2 * C * (e + |amplitude j| * priorNamespacedObservableAverage μ ν₀ eig c I degree amplitude r h
        (fun U x => |spectralPerturbationKernel (id : SpecialOrthogonal N → SpecialOrthogonal N)
          I (degree j) n (r j) U x x - d₀|)) := by
  let U := fun ω : PriorFrozenData N j => ω.1
  let κ := spectralPerturbationKernel (id : SpecialOrthogonal N → SpecialOrthogonal N) I (degree j) n (r j)
  let ν := priorFrozenReference ν₀ eig c I degree amplitude r h j
  let A := spectralPerturbationCoefficients U I (degree j) n (r j)
  have hκ : Measurable (fun p : SpecialOrthogonal N ×
      ((Spin N × LabeledLeaf n) × (Spin N × LabeledLeaf n)) => κ p.1 p.2.1 p.2.2) := by
    simpa only [spectralPerturbationCoefficients_cross] using
      measurable_spectralPerturbationCross (id : SpecialOrthogonal N → SpecialOrthogonal N)
        measurable_id I (degree j) n (r j)
  let fresh := fun (V : SpecialOrthogonal N) (τ : Fin (q + 1 + 1) → Spin N × LabeledLeaf n) =>
    D V (Fin.tail τ) * κ V ((Fin.tail τ) 0) (τ 0)
  let pair := fun (V : SpecialOrthogonal N) (τ : Fin 2 → Spin N × LabeledLeaf n) => κ V (τ 1) (τ 0)
  let old := fun (V : SpecialOrthogonal N) (σ : Fin (q + 1) → Spin N × LabeledLeaf n) =>
    D V σ * ∑ l : Fin q, κ V (σ 0) (σ l.succ)
  have hfresh : Measurable (Function.uncurry fresh) := measurable_ggFresh D κ hD hκ
  have hpair : Measurable (Function.uncurry pair) := measurable_ggPair κ hκ
  have hold : Measurable (Function.uncurry old) := measurable_ggOld D κ hD hκ
  have hdiag : Measurable (Function.uncurry
      (fun V x => |κ V x x - d₀|)) :=
    ((hκ.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_snd))).sub_const d₀).abs
  have hg := spectralPerturbation_gg_bound (P := priorFrozenLaw μ j) U measurable_fst
    I (degree j) (r j) (measurable_priorFrozenReference ν₀ eig c I degree amplitude r h j)
    (amplitude j) β d₀ (fun ω => D (U ω))
    (hD.comp (measurable_fst.fst.prodMk measurable_snd)) hC (fun ω => hDb (U ω)) hE.1
  have heq (z : ℕ) (F : SpecialOrthogonal N → (Fin z → Spin N × LabeledLeaf n) → ℝ)
      (hF : Measurable (Function.uncurry F)) :
      randomCoefficientAverage (priorFrozenLaw μ j) ν A (amplitude j) (fun ω => F (U ω)) =
        priorNamespacedReplicaAverage μ ν₀ eig c I degree amplitude r h F := by
    simpa only [Function.update_eq_self] using
      priorFrozenGaussian_replicaAverage μ ν₀ eig c I degree amplitude r h hh h0 j (amplitude j) F hF
  have hd := priorFrozenGaussian_observableAverage μ ν₀ eig c I degree amplitude r h hh h0 j
    (amplitude j) (fun V x => |κ V x x - d₀|) hdiag
  simp only [Function.update_eq_self] at hd
  change |amplitude j| * |(q + 1 : ℕ) *
      randomCoefficientAverage (priorFrozenLaw μ j) ν A (amplitude j) (fun ω => fresh (U ω)) -
      randomCoefficientAverage (priorFrozenLaw μ j) ν A (amplitude j) (fun ω => D (U ω)) *
        randomCoefficientAverage (priorFrozenLaw μ j) ν A (amplitude j) (fun ω => pair (U ω)) -
      randomCoefficientAverage (priorFrozenLaw μ j) ν A (amplitude j) (fun ω => old (U ω))| ≤ _ at hg
  rw [heq _ fresh hfresh, heq _ D hD, heq _ pair hpair, heq _ old hold] at hg
  change |amplitude j| * |priorSpectralGGResidual μ ν₀ eig c I degree amplitude r h j D| ≤
    2 * C * (_ + |amplitude j| * _) at hg
  have hd' : (∫ p : PriorFrozenData N j × (ℕ → ℝ), ∫ x,
      |spectralPerturbationKernel U I (degree j) n (r j) p.1 x x - d₀|
      ∂(ν p.1).tilted (fun x => amplitude j * cylinderField (A p.1 x) p.2)
      ∂(priorFrozenLaw μ j).prod gaussianCoordinates) =
      priorNamespacedObservableAverage μ ν₀ eig c I degree amplitude r h
        (fun V x => |κ V x x - d₀|) := hd
  rw [hd'] at hg
  exact hg.trans (mul_le_mul_of_nonneg_left
    (add_le_add hE.2 le_rfl) (mul_nonneg (by norm_num) hC))

end InvariantIsing
namespace InvariantIsing

/-- Each individual self-overlap error controls every selected tensor
covariance. The Gaussian energy error is expressed in the same actual model. -/
theorem priorFiniteGG_individualDiagonal_bound {N m k n q : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν₀ : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν₀] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (j : Fin k) (β e C : ℝ) (hC : 0 ≤ C) (ha : 0 < |amplitude j|)
    (D : SpecialOrthogonal N → (Fin (q + 1) → Spin N × LabeledLeaf n) → ℝ)
    (hD : Measurable (Function.uncurry D)) (hDb : ∀ U σ, |D U σ| ≤ C)
    (center δ : Fin m → ℝ)
    (hδ : ∀ a, priorNamespacedObservableAverage μ ν₀ eig c I degree amplitude r h
      (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center a|) ≤ δ a)
    (hE :
      let A := spectralPerturbationCoefficients (fun ω : PriorFrozenData N j => ω.1)
        I (degree j) n (r j)
      let ν := priorFrozenReference ν₀ eig c I degree amplitude r h j
      let E := fun p : PriorFrozenData N j × (ℕ → ℝ) => ∫ x,
        |cylinderField (A p.1 x) p.2 - β|
        ∂(ν p.1).tilted (fun x => amplitude j * cylinderField (A p.1 x) p.2)
      Integrable E ((priorFrozenLaw μ j).prod gaussianCoordinates) ∧
        (∫ p, E p ∂(priorFrozenLaw μ j).prod gaussianCoordinates) ≤ e) :
    |priorSpectralGGResidual μ ν₀ eig c I degree amplitude r h j D| ≤
      2 * C * (e / |amplitude j| + ∑ a, (degree j a : ℝ) * δ a) := by
  let d₀ := (∏ a, spectralDiagonalCenter (center a) ^ degree j a) *
    ((n : ℝ) / (n + 1 : ℕ)) ^ r j
  have hg := priorFiniteGG_bound μ ν₀ eig c I degree amplitude r h hh h0 j β d₀ e C hC D hD hDb hE
  have hd := priorKernelDiagonalError_le μ ν₀ eig c I degree amplitude r h (degree j) (r j) center
  have hs : (∑ a, (degree j a : ℝ) * priorNamespacedObservableAverage μ ν₀ eig c I degree amplitude r h
      (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center a|)) ≤
      ∑ a, (degree j a : ℝ) * δ a :=
    Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hδ a) (Nat.cast_nonneg _)
  have hb := hg.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hd.trans hs) ha.le))
    (mul_nonneg (by norm_num) hC))
  apply (mul_le_mul_iff_left₀ ha).mp
  calc
    _ ≤ 2 * C * (e + |amplitude j| * ∑ a, (degree j a : ℝ) * δ a) := by
      simpa only [mul_comm] using hb
    _ = (2 * C * (e / |amplitude j| + ∑ a, (degree j a : ℝ) * δ a)) * |amplitude j| := by
      field_simp [ha.ne']

end InvariantIsing

end

end OAI
