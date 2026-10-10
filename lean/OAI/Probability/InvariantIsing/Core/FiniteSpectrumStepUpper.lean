import OAI.Probability.InvariantIsing.Arrays.TensorContactAsymptotic
import OAI.Probability.InvariantIsing.Arrays.TensorZeroFieldPressure

namespace OAI

/-! The finite-spectrum pressure upper bound against a fixed finite-step
trial. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem finiteSpectrum_meanPressure_step_upper
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig : (k : ℕ) → Fin (N k) → ℝ)
    (K : ℝ) (hK : 0 < K) (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
    (ρ : Fin m → ℝ) (hρpos : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ))
    (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (trial : OverlapPath) (values : Fin (n + 1) → ℝ)
    (hvalues : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → trial s = values i)
    (d : ℝ) (hd : 0 < d) (htrial : ∀ᵐ s ∂pathMeasure, trial s ≤ 1 - d)
    (S : ℝ) (hS : entropyFunctional trial ≤ (S : EReal)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      (∫ U : SpecialOrthogonal (N k),
        rotatedPressure (eig k) (specialRotation U) (fun _ => 0) ∂μ k) ≤
      S + spectralFunctional (finiteR ρ lam hρpos hρsum) trial + ε := by
  intro ε hε
  have hthird : 0 < ε / 3 := div_pos hε (by norm_num)
  obtain ⟨H, hH, hevent⟩ := tensorContact_eventually_nonnegative hhaar hgauss
    N hN hNlim m n μ hμinv eig K hK heig I hdis hcover lam hlam ρ hρpos hρsum hρ
    cut hc hfirst hlast trial values hvalues d hd htrial (ε / 3) S hthird hS
  have hcost : ∀ᶠ k in atTop,
      2 * m * perturbationScale (N k) + 8 * perturbationScale (N k) ^ 2 < ε / 3 :=
    ((fullPerturbationCost_tendsto m).comp hNlim).eventually (gt_mem_nhds hthird)
  filter_upwards [hevent (ε / 3) hthird, hcost] with k hk hck
  let p : TensorContactParameter (N k) m n :=
    (1, (fun _ => 0), (fun _ => 3 / 2), (fun _ => 3 / 2))
  have hp : p ∈ tensorContactRegion (N k) m n H := by
    apply tensorContactRegion_mem (by norm_num) (fun _ => le_rfl)
    · simpa only [p, Finset.sum_const_zero] using hH.le
    · intro j; norm_num
    · intro a; norm_num
  have hj := hk p hp
  have hz := tensorContactPressure_one_zero_field_cost hhaar hgauss (hN k) (μ k) (hμinv k)
    (eig k) (fun _ => 0) (I k) (fun _ => 3 / 2) (by intro j; norm_num)
    (fun _ => 3 / 2) (by intro j; norm_num) n (chainExponent cut)
    (chainExponent_admissible hc hfirst hlast)
  have hg : finiteTemperatureFunctional ρ lam hρpos hρsum trial 1 =
      spectralFunctional (finiteR ρ lam hρpos hρsum) trial := by
    simpa only [one_mul] using finiteTemperatureFunctional_eq ρ lam hρpos hρsum trial zero_le_one
  have hzero : finiteFieldPath (fun _ : Fin (n + 1) => (0 : ℝ)) = fun _ => 0 := by
    funext i
    simp only [finiteFieldPath, ite_self, Finset.sum_const_zero]
  simp only [tensorContactObjective, p, hzero, mul_zero, Finset.sum_const_zero, zero_div,
    sub_zero, one_mul, sub_self, zero_pow (by norm_num : 2 ≠ 0), add_zero, hg] at hj
  have hdiff := neg_le_abs (tensorContactPressure (μ k) (eig k) (fun _ => 0) (I k)
    (chainExponent cut) p - ∫ U : SpecialOrthogonal (N k),
      rotatedPressure (eig k) (specialRotation U) (fun _ => 0) ∂μ k)
  change |tensorContactPressure (μ k) (eig k) (fun _ => 0) (I k) (chainExponent cut) p - _| ≤ _ at hz
  linarith

end InvariantIsing

end

end OAI
