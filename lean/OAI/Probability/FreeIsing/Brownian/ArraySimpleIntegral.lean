import OAI.Probability.FreeIsing.Brownian.FiltrationIntegral
import OAI.Probability.FreeIsing.Brownian.SpatialIntegral

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Problem367.SimpleIntegral

theorem predictable_array_increments_orthogonal
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (F : Filtration ℕ mΩ) (H D : ι → ℕ → Ω → ℝ)
    (hH : ∀ a k, StronglyMeasurable[F k] (H a k))
    (hD : ∀ a k, StronglyMeasurable[F (k + 1)] (D a k))
    (hDi : ∀ a k, Integrable (D a k) P)
    (hHD : ∀ a k, MemLp (fun ω => H a k ω * D a k ω) 2 P)
    (hz : ∀ a k, P[D a k | F k] =ᵐ[P] 0)
    (hsame : ∀ k, Pairwise fun a b =>
      ∫ ω, (H a k ω * D a k ω) * (H b k ω * D b k ω) ∂P = 0) :
    Pairwise fun p q : ι × ℕ => ∫ ω,
      (H p.1 p.2 ω * D p.1 p.2 ω) * (H q.1 q.2 ω * D q.1 q.2 ω) ∂P = 0 := by
  have hoff (a b : ι) (i j : ℕ) (hij : i < j) :
      (∫ ω, (H a i ω * D a i ω) * (H b j ω * D b j ω) ∂P) = 0 := by
    have hc : StronglyMeasurable[F j] (fun ω => (H a i ω * D a i ω) * H b j ω) := by
      simpa only [Pi.mul_def] using
        (((hH a i).mono (F.mono hij.le)).mul
          ((hD a i).mono (F.mono (Nat.succ_le_of_lt hij)))).mul (hH b j)
    have hp : Integrable ((fun ω => (H a i ω * D a i ω) * H b j ω) * D b j) P := by
      simpa only [Pi.mul_def, mul_assoc] using (hHD a i).integrable_mul (hHD b j)
    simpa only [mul_assoc] using
      integral_mul_eq_zero_of_condExp_eq_zero (F.le j) hc (hDi b j) hp (hz b j)
  intro p q hpq
  rcases lt_trichotomy p.2 q.2 with h | h | h
  · exact hoff p.1 q.1 p.2 q.2 h
  · have hab : p.1 ≠ q.1 := fun ha => hpq (Prod.ext ha h)
    simpa only [h] using hsame q.2 hab
  · simpa only [mul_comm] using hoff q.1 p.1 q.2 p.2 h

theorem integral_mul_sums_eq_zero
    {Ω ι κ : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ι → Ω → ℝ) (Y : κ → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) (hY : ∀ j, MemLp (Y j) 2 P)
    (horth : ∀ i j, ∫ ω, X i ω * Y j ω ∂P = 0)
    (s : Finset ι) (t : Finset κ) :
    (∫ ω, (∑ i ∈ s, X i ω) * (∑ j ∈ t, Y j ω) ∂P) = 0 := by
  have hint (i : ι) (j : κ) : Integrable (fun ω => X i ω * Y j ω) P :=
    (hX i).integrable_mul (hY j)
  simp_rw [Finset.sum_mul_sum]
  rw [integral_finsetSum s (fun i _ =>
    integrable_finsetSum t (fun j _ => hint i j))]
  apply Finset.sum_eq_zero
  intro i hi
  rw [integral_finsetSum t (fun j _ => hint i j)]
  exact Finset.sum_eq_zero fun j _ => horth i j

end Problem367.SimpleIntegral

namespace Problem367.BrownianArrayIntegral

theorem planted_grid_orthogonal
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ a, IsPreBrownianReal (B a) (μ a))
    (hmB : ∀ a t, Measurable (B a t))
    (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ι → ℕ → S × (ι → Ω) → ℝ)
    (hH : ∀ a k, StronglyMeasurable[signalArrayFiltration B hmB (t k)] (H a k))
    (hH2 : ∀ a k, MemLp (H a k) 2 (ν.prod (Measure.infinitePi μ))) :
    Pairwise fun p q : ι × ℕ => ∫ x : S × (ι → Ω),
      (H p.1 p.2 x * (B p.1 (t (p.2 + 1)) (x.2 p.1) - B p.1 (t p.2) (x.2 p.1))) *
      (H q.1 q.2 x * (B q.1 (t (q.2 + 1)) (x.2 q.1) - B q.1 (t q.2) (x.2 q.1)))
        ∂ν.prod (Measure.infinitePi μ) = 0 := by
  have (a : ι) : IsProbabilityMeasure (μ a) := (hB a).isGaussianProcess.isProbabilityMeasure
  let P := ν.prod (Measure.infinitePi μ)
  let F := signalArrayFiltration (S := S) B hmB
  let G : Filtration ℕ (inferInstance : MeasurableSpace (S × (ι → Ω))) :=
    ⟨fun k => F (t k), fun _ _ h => F.mono (ht h), fun k => F.le (t k)⟩
  let D : ι → ℕ → S × (ι → Ω) → ℝ :=
    fun a k x => B a (t (k + 1)) (x.2 a) - B a (t k) (x.2 a)
  have hC (a : ι) := planted_coordinate_preBrownian ν μ hB a
  have hAd (a : ι) := (preBrownian_martingale_signalArrayFiltration ν μ hB hmB a).stronglyAdapted
  have hD2 (a : ι) (k : ℕ) : MemLp (D a k) 2 P :=
    ((hC a).isGaussianProcess.hasGaussianLaw_eval (t (k + 1))).memLp_two.sub
      ((hC a).isGaussianProcess.hasGaussianLaw_eval (t k)).memLp_two
  have hind (k : ℕ) : IndepFun (fun x a => H a k x) (fun x a => D a k x) P :=
    PredictableL2.planted_coefficients_indep_increments ν μ hB hmB
      (ht (Nat.le_succ k)) (fun a => hH a k)
  have hHD (a : ι) (k : ℕ) : MemLp (fun x => H a k x * D a k x) 2 P :=
    PredictableL2.memLp_two_mul_of_indep
      ((hind k).comp (measurable_pi_apply a) (measurable_pi_apply a)) (hH2 a k) (hD2 a k)
  have hz (a : ι) (k : ℕ) : (∫ x, D a k x ∂P) = 0 := by
    change (∫ x : S × (ι → Ω), B a (t (k + 1)) (x.2 a) - B a (t k) (x.2 a) ∂P) = 0
    rw [integral_sub ((hC a).integrable_eval _) ((hC a).integrable_eval _),
      (hC a).integral_eval, (hC a).integral_eval, sub_self]
  have hnoise (k : ℕ) : Pairwise fun a b => ∫ x, D a k x * D b k x ∂P = 0 := by
    intro a b hab
    have hi := (planted_coordinate_increments_indep ν μ hB hmB (t k) (t (k + 1)) hab).integral_fun_mul_eq_mul_integral
      (hD2 a k).aestronglyMeasurable (hD2 b k).aestronglyMeasurable
    change (∫ x, D a k x * D b k x ∂P) = (∫ x, D a k x ∂P) * ∫ x, D b k x ∂P at hi
    simpa only [hz, zero_mul] using hi
  apply SimpleIntegral.predictable_array_increments_orthogonal G H D hH
  · intro a k
    exact (hAd a (t (k + 1))).sub ((hAd a (t k)).mono (F.mono (ht (Nat.le_succ k))))
  · exact fun a k => (hD2 a k).integrable (by norm_num)
  · exact hHD
  · intro a k
    apply BrownianFiltration.increment_condExp_zero (hC a) (hAd a)
    change Indep _ (signalArrayFiltration B hmB (t k)) P
    rw [signalArrayFiltration_eq_comap]
    exact (planted_array_increments_indep_signal_past ν μ hB hmB (ht (Nat.le_succ k))).comp
      (measurable_pi_apply a) measurable_id
  · intro k
    exact PredictableL2.weighted_array_orthogonal (hind k) (fun a => hH2 a k)
      (fun a => hD2 a k) (hnoise k)

theorem planted_grid_sums_orthogonal
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ a, IsPreBrownianReal (B a) (μ a))
    (hmB : ∀ a t, Measurable (B a t))
    (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ι → ℕ → S × (ι → Ω) → ℝ)
    (hH : ∀ a k, StronglyMeasurable[signalArrayFiltration B hmB (t k)] (H a k))
    (hH2 : ∀ a k, MemLp (H a k) 2 (ν.prod (Measure.infinitePi μ)))
    {a b : ι} (hab : a ≠ b) (u v : Finset ℕ) :
    (∫ x : S × (ι → Ω),
      (∑ k ∈ u, H a k x * (B a (t (k + 1)) (x.2 a) - B a (t k) (x.2 a))) *
      (∑ k ∈ v, H b k x * (B b (t (k + 1)) (x.2 b) - B b (t k) (x.2 b)))
        ∂ν.prod (Measure.infinitePi μ)) = 0 := by
  let P := ν.prod (Measure.infinitePi μ)
  let D : ι → ℕ → S × (ι → Ω) → ℝ :=
    fun a k x => B a (t (k + 1)) (x.2 a) - B a (t k) (x.2 a)
  have hHD (a : ι) (k : ℕ) : MemLp (fun x => H a k x * D a k x) 2 P := by
    have hc := planted_coordinate_preBrownian ν μ hB a
    have hd : MemLp (D a k) 2 P :=
      (hc.isGaussianProcess.hasGaussianLaw_eval (t (k + 1))).memLp_two.sub
        (hc.isGaussianProcess.hasGaussianLaw_eval (t k)).memLp_two
    have hi := PredictableL2.planted_coefficients_indep_increments ν μ hB hmB
      (ht (Nat.le_succ k)) (fun a => hH a k)
    exact PredictableL2.memLp_two_mul_of_indep
      (hi.comp (measurable_pi_apply a) (measurable_pi_apply a)) (hH2 a k) hd
  apply SimpleIntegral.integral_mul_sums_eq_zero
    (fun k x => H a k x * D a k x) (fun k x => H b k x * D b k x)
    (hHD a) (hHD b) _ u v
  intro k l
  exact planted_grid_orthogonal ν μ hB hmB t ht H hH hH2
    (show (a, k) ≠ (b, l) from fun h => hab (congrArg Prod.fst h))

end Problem367.BrownianArrayIntegral

end

end OAI
