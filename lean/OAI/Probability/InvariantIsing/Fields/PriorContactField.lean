import OAI.Probability.InvariantIsing.Fields.PriorFieldDerivative
import OAI.Probability.InvariantIsing.Fields.PriorContactMinimum
import OAI.Probability.InvariantIsing.Arrays.TensorContactField

namespace OAI

/-! Field-cone inequalities at the actual constrained-prior joint contact
minimum. No strict positivity of the covariance increments is required. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

lemma priorContactPressure_eq_namespaced {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (p : TensorContactParameter N m n) :
    priorContactPressure μ ν eig c I p =
      priorNamespacedMeanPressure μ ν (diagonalPerturbedEigenvalues eig I p.2.2.2 p.1)
        c I (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1)
        (fun j : Fin N => enumeratedTreeDegree m j) (finiteFieldPath p.2.1) := by
  unfold priorContactPressure priorNamespacedMeanPressure priorPerturbationPressureMean
  rw [priorNamespacedLog_integral]

def priorContactFieldObjective {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ) (w : Fin (n+1) → ℝ) (h : ℕ → ℝ) : ℝ :=
  -priorNamespacedMeanPressure μ ν (diagonalPerturbedEigenvalues eig I v t) c I
    (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
    (fun j : Fin N => enumeratedTreeDegree m j) h-(∑ i, w i*h i)/2

lemma priorContactFieldObjective_right_derivative
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ) (w : Fin (n+1) → ℝ)
    (h g : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (hg : Monotone g) (g0 : 0 ≤ g 0) :
    HasDerivWithinAt
      (fun a => priorContactFieldObjective μ ν eig c I u v t w (fun i => h i+a*g i))
      (priorNamespacedReplicaAverage μ ν (diagonalPerturbedEigenvalues eig I v t) c I
        (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
        (fun j : Fin N => enumeratedTreeDegree m j) h (fun _ => tensorFieldPairObservable g)/2-
        (∑ i, w i*g i)/2) (Ici 0) 0 := by
  have hd := priorNamespacedMeanPressure_field_right_derivative hhaar hgauss hN μ hμ ν
    (diagonalPerturbedEigenvalues eig I v t) c I (fun j : Fin N => enumeratedSpectralDegree m j)
    (tensorPerturbationAmplitude N u) (fun j : Fin N => enumeratedTreeDegree m j) h g hh h0 hg g0
  have hs : HasDerivAt (fun a : ℝ => ∑ i : Fin (n+1), w i*(h i+a*g i)) (∑ i, w i*g i) 0 := by
    simpa only [one_mul,id_eq] using HasDerivAt.fun_sum
      (fun (i : Fin (n+1)) (_ : i ∈ Finset.univ) =>
        (((hasDerivAt_id (0 : ℝ)).mul_const (g i)).const_add (h i)).const_mul (w i))
  convert! hd.fun_neg.fun_sub (hs.div_const 2).hasDerivWithinAt using 1
  simp only [neg_div,neg_neg]

theorem priorContact_minimum_field_cone
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m n : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (w : Fin (n+1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (H : ℝ) (p : TensorContactParameter N m n)
    (hp : p ∈ tensorContactRegion N m n H)
    (hmin : ∀ q ∈ tensorContactRegion N m n H,
      priorContactObjective μ ν eig c I w S V p ≤ priorContactObjective μ ν eig c I w S V q)
    (hcap : (∑ i, p.2.1 i) < H) (d : Fin (n+1) → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (∑ i, w i*finiteFieldPath d i) ≤
      priorNamespacedReplicaAverage μ ν (diagonalPerturbedEigenvalues eig I p.2.2.2 p.1) c I
        (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1)
        (fun j : Fin N => enumeratedTreeDegree m j) (finiteFieldPath p.2.1)
        (fun _ => tensorFieldPairObservable (finiteFieldPath d)) := by
  obtain ⟨ht,ha,hsum,hu,hv⟩ := tensorContactRegion_bounds hp
  have hder := priorContactFieldObjective_right_derivative hhaar hgauss hN μ hμ ν eig c I
    p.2.2.1 p.2.2.2 p.1 w (finiteFieldPath p.2.1) (finiteFieldPath d)
    (monotone_finiteFieldPath ha) (finiteFieldPath_nonneg ha 0)
    (monotone_finiteFieldPath hd) (finiteFieldPath_nonneg hd 0)
  have hfeas : ∀ᶠ a in 𝓝[>] (0 : ℝ), (∑ i, p.2.1 i)+a*(∑ i, d i) < H := by
    have hc : ContinuousAt (fun a : ℝ => (∑ i, p.2.1 i)+a*(∑ i, d i)) 0 := by fun_prop
    exact (hc.eventually (gt_mem_nhds (by simpa only [zero_mul,add_zero] using hcap))).filter_mono
      nhdsWithin_le_nhds
  have hnon := right_derivative_nonneg_of_min hder (by
    filter_upwards [hfeas,self_mem_nhdsWithin] with a hafeas ha0
    let z : TensorContactParameter N m n := (p.1,(fun i => p.2.1 i+a*d i),p.2.2.1,p.2.2.2)
    have hz : z ∈ tensorContactRegion N m n H := tensorContactRegion_mem ht
      (fun i => add_nonneg (ha i) (mul_nonneg ha0.le (hd i)))
      (by simpa only [z,Finset.sum_add_distrib,Finset.mul_sum] using hafeas.le) hu hv
    have hm := hmin z hz
    simp only [priorContactObjective,priorContactPressure_eq_namespaced] at hm
    simp only [z,finiteFieldPath_add,finiteFieldPath_const_mul] at hm
    simp only [priorContactFieldObjective,zero_mul,add_zero]
    linarith)
  linarith

end InvariantIsing

end

end OAI
