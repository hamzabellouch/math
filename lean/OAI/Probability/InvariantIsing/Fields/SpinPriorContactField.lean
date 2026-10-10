import OAI.Probability.InvariantIsing.Fields.SpinPriorContactMinimum
import OAI.Probability.InvariantIsing.Fields.SpinPriorFieldDerivativeMean
import OAI.Probability.IsingPerceptron.TimeIncrement

namespace OAI

/-! The field-coordinate inequality at the actual joint minimum. Tied and
zero covariance levels are allowed; only the upper cap must be inactive. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

def spinPriorContactFieldObjective {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : Fin N → ℝ) (v : Fin m → ℝ)
    (t : ℝ) (b : ℕ → ℝ) (w : Fin (n + 1) → ℝ) (h : ℕ → ℝ) : ℝ :=
  -spinPriorMeanPressure (n := n) μ π (diagonalPerturbedEigenvalues eig I v t) c I
    (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
    b (fun j => enumeratedTreeDegree m j) h - (∑ i, w i * h i) / 2

theorem spinPriorContactFieldObjective_right_derivative {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : Fin N → ℝ) (v : Fin m → ℝ)
    (t : ℝ) (b : ℕ → ℝ) (w : Fin (n + 1) → ℝ) (h g : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hg : Monotone g) (g0 : 0 ≤ g 0) :
    HasDerivWithinAt
      (fun a => spinPriorContactFieldObjective μ π eig c I u v t b w (fun i => h i + a * g i))
      (spinPriorReplicaAverage μ π (diagonalPerturbedEigenvalues eig I v t) c I
        (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
        n b (fun j => enumeratedTreeDegree m j) h
        (fun _ => tensorFieldPairObservable g) / 2 - (∑ i, w i * g i) / 2) (Ici 0) 0 := by
  have hd := spinPriorMeanPressure_field_right_derivative hN μ π
    (diagonalPerturbedEigenvalues eig I v t) c I (fun j => enumeratedSpectralDegree m j)
    (tensorPerturbationAmplitude N u) n b (fun j => enumeratedTreeDegree m j) h g hh h0 hg g0
  have hs : HasDerivAt (fun a : ℝ => ∑ i : Fin (n + 1), w i * (h i + a * g i))
      (∑ i, w i * g i) 0 := by
    simpa only [one_mul, id_eq] using HasDerivAt.fun_sum
      (fun (i : Fin (n + 1)) (_ : i ∈ Finset.univ) =>
        (((hasDerivAt_id (0 : ℝ)).mul_const (g i)).const_add (h i)).const_mul (w i))
  convert! hd.fun_neg.fun_sub (hs.div_const 2).hasDerivWithinAt using 1
  simp only [neg_div, neg_neg]

theorem spinPriorContact_minimum_field_cone {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (w : Fin (n + 1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (H : ℝ) (p : TensorContactParameter N m n)
    (hp : p ∈ tensorContactRegion N m n H)
    (hmin : ∀ q ∈ tensorContactRegion N m n H,
      spinPriorContactObjective μ π eig c I b w S V p ≤ spinPriorContactObjective μ π eig c I b w S V q)
    (hcap : (∑ i, p.2.1 i) < H) (d : Fin (n + 1) → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (∑ i, w i * finiteFieldPath d i) ≤
      spinPriorReplicaAverage μ π (diagonalPerturbedEigenvalues eig I p.2.2.2 p.1) c I
        (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1)
        n b (fun j => enumeratedTreeDegree m j) (finiteFieldPath p.2.1)
        (fun _ => tensorFieldPairObservable (finiteFieldPath d)) := by
  obtain ⟨ht, ha, hsum, hu, hv⟩ := tensorContactRegion_bounds hp
  have hder := spinPriorContactFieldObjective_right_derivative hN μ π eig c I p.2.2.1 p.2.2.2
    p.1 b w (finiteFieldPath p.2.1) (finiteFieldPath d)
    (monotone_finiteFieldPath ha) (finiteFieldPath_nonneg ha 0)
    (monotone_finiteFieldPath hd) (finiteFieldPath_nonneg hd 0)
  have hfeas : ∀ᶠ a in 𝓝[>] (0 : ℝ), (∑ i, p.2.1 i) + a * (∑ i, d i) < H := by
    have hc : ContinuousAt (fun a : ℝ => (∑ i, p.2.1 i) + a * (∑ i, d i)) 0 := by fun_prop
    exact (hc.eventually (gt_mem_nhds (by simpa only [zero_mul, add_zero] using hcap))).filter_mono
      nhdsWithin_le_nhds
  have hnon := right_derivative_nonneg_of_min hder (by
    filter_upwards [hfeas, self_mem_nhdsWithin] with a hafeas ha0
    have hnew : (p.1, (fun i => p.2.1 i + a * d i), p.2.2.1, p.2.2.2) ∈
        tensorContactRegion N m n H := tensorContactRegion_mem ht
      (fun i => add_nonneg (ha i) (mul_nonneg ha0.le (hd i)))
      (by simpa only [Finset.sum_add_distrib, Finset.mul_sum] using hafeas.le) hu hv
    have hm := hmin _ hnew
    simp only [spinPriorContactObjective, spinPriorContactPressure, finiteFieldPath_add,
      finiteFieldPath_const_mul] at hm
    simp only [spinPriorContactFieldObjective, zero_mul, add_zero]
    linarith)
  linarith

end InvariantIsing

end

end OAI
