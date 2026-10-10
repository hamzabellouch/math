import OAI.Probability.InvariantIsing.Arrays.NSpinTensorTerminalDerivative

namespace OAI

/-! Coordinate derivatives through the actual finite Gaussian cascade recursion. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology NNReal ENNReal

namespace InvariantIsing

/-- The bounded coordinate derivative gives a local exponential dominator,
even when the terminal itself is unbounded. -/
lemma hasDerivAt_logMean_of_bounded_derivative
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (F D : ℝ → A → ℝ) (hF : ∀ s, Measurable (F s)) (hD : ∀ s, Measurable (D s))
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ s a, |D s a| ≤ K)
    (hd : ∀ s a, HasDerivAt (fun q => F q a) (D s a) s)
    {b : ℝ} (hb : b ≠ 0) (t : ℝ)
    (hi : Integrable (fun a => Real.exp (b * F t a)) μ) :
    HasDerivAt (fun s => logMean b μ (F s))
      (∫ a, D t a ∂μ.tilted (fun a => b * F t a)) t := by
  have hdiff (a : A) (s : ℝ) : |F s a - F t a| ≤ K * |s - t| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun q (_ : q ∈ (Set.univ : Set ℝ)) => (hd q a).hasDerivWithinAt)
        (fun q _ => by simpa only [Real.norm_eq_abs] using hbound q a)
        convex_univ (Set.mem_univ t) (Set.mem_univ s)
  have hloc (s : ℝ) (hs : s ∈ Ioo (t - 1) (t + 1)) (a : A) :
      b * F s a ≤ b * F t a + |b| * K := by
    have hst : |s - t| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h1 := (hdiff a s).trans (mul_le_of_le_one_right hK hst)
    have h2 : b * (F s a - F t a) ≤ |b| * K := (le_abs_self (b * (F s a - F t a))).trans
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg b))
    nlinarith
  let C := Real.exp (|b| * K) * (|b| * K)
  have hdom : Integrable (fun a => C * Real.exp (b * F t a)) μ := hi.const_mul C
  have hnorm (s : ℝ) (hs : s ∈ Ioo (t - 1) (t + 1)) (a : A) :
      ‖Real.exp (b * F s a) * (b * D s a)‖ ≤ C * Real.exp (b * F t a) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
    calc
      _ ≤ Real.exp (b * F t a + |b| * K) * (|b| * K) :=
        mul_le_mul (Real.exp_le_exp.mpr (hloc s hs a))
          (mul_le_mul_of_nonneg_left (hbound s a) (abs_nonneg b))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.exp_pos _).le
      _ = C * Real.exp (b * F t a) := by rw [Real.exp_add]; dsimp only [C]; ring
  obtain ⟨_, hI⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith : t - 1 < t) (by linarith : t < t + 1))
    (Eventually.of_forall fun s => ((hF s).const_mul b).exp.aestronglyMeasurable) hi
    (((hF t).const_mul b).exp.mul ((hD t).const_mul b)).aestronglyMeasurable
    (ae_of_all _ fun a s hs => hnorm s hs a) hdom
    (ae_of_all _ fun a s _ => ((hd s a).const_mul b).exp)
  have hpos := IsingPerceptron.integral_exp_pos μ (F t) hi
  convert (hI.log hpos.ne').div_const b using 1
  · rfl
  · rw [integral_tilted_eq_div]
    have he : (∫ a, Real.exp (b * F t a) * (b * D t a) ∂μ) =
        b * ∫ a, Real.exp (b * F t a) * D t a ∂μ := by
      rw [← integral_const_mul]
      congr 1
      funext a
      ring
    rw [he]
    field_simp

lemma tensorCascadeBackward_step {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (i : ℕ) (hi : i < n) (z : SpinTensorIndex I degree → ℝ) :
    tensorCascadeBackward eig U c I degree amplitude n b v i z =
      logMean (b i) (tensorGaussianLaw I degree (v i) : Measure (SpinTensorIndex I degree → ℝ))
        (fun a => tensorCascadeBackward eig U c I degree amplitude n b v (i + 1) (z + a)) :=
  backwardValue_step n b (fun j => tensorGaussianLaw I degree (v j))
    (fun _ p => p.1 + p.2) (spinTensorTerminal eig U c I degree amplitude) hi z

/-- The normalized retained mark transition is exactly the Gaussian tilt
by the next actual backward value. -/
theorem tensorAncestorMarkKernel_eq_tilted {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (i : ℕ) (hi : i < n) (z : SpinTensorIndex I degree → ℝ) :
    tensorAncestorMarkKernel eig U c I degree amplitude n b v i z =
      (tensorGaussianLaw I degree (v i) : Measure (SpinTensorIndex I degree → ℝ)).tilted
        (fun a => b i * tensorCascadeBackward eig U c I degree amplitude n b v (i + 1) (z + a)) := by
  have hint := backwardValue_linearGrowth_moments n b
    (fun j => tensorGaussianLaw I degree (v j))
    (fun j _ => tensorGaussianLaw_moments hN I degree (v j))
    (measurable_spinTensorTerminal eig U c I degree amplitude)
    (spinTensorTerminal_linearGrowth eig U c I degree amplitude)
    (fun j hj => (hb.1 j hj).1) i hi z
  have hp := IsingPerceptron.integral_exp_pos
    (tensorGaussianLaw I degree (v i) : Measure (SpinTensorIndex I degree → ℝ))
    (fun a => tensorCascadeBackward eig U c I degree amplitude n b v (i + 1) (z + a)) hint
  rw [tensorAncestorMarkKernel_density eig U c I degree amplitude n b v i hi z,
    tensorCascadeBackward_step eig U c I degree amplitude n b v i hi z]
  unfold Measure.tilted
  congr 1
  funext a
  congr 1
  have he (x y : ℝ) : b i * (x - Real.log y / b i) = b i * x - Real.log y := by
    field_simp [(hb.1 i hi).1.ne']
  rw [logMean, he, Real.exp_sub, Real.exp_log hp]

def tensorCascadeCoordinateMean {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ) :
    (n : ℕ) → (ℕ → ℝ) → (ℕ → SpinTensorIndex I degree → ℝ≥0) →
      (SpinTensorIndex I degree → ℝ) → SpinTensorIndex I degree → ℝ
  | 0, _, _, z, j => tensorTerminalCoordinateMean eig U c I degree amplitude z j
  | n + 1, b, v, z, j =>
      ∫ a, tensorCascadeCoordinateMean eig U c I degree amplitude n
        (fun i => b (i + 1)) (fun i => v (i + 1)) (z + a) j
        ∂tensorAncestorMarkKernel eig U c I degree amplitude (n + 1) b v 0 z

lemma measurable_tensorCascadeCoordinateMean {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (j : SpinTensorIndex I degree) :
    Measurable (fun z => tensorCascadeCoordinateMean eig U c I degree amplitude n b v z j) := by
  induction n generalizing b v with
  | zero => exact measurable_tensorTerminalCoordinateMean eig U c I degree amplitude j
  | succ n ih =>
    let := tensorAncestorMarkKernel_markov hN eig U c I degree amplitude (n + 1) b v hb 0
    exact (((ih _ _ hb.tail).comp (measurable_fst.add measurable_snd)).stronglyMeasurable
      |>.integral_kernel_prod_right').measurable

lemma tensorCascadeCoordinateMean_abs_le {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ) (j : SpinTensorIndex I degree) :
    |tensorCascadeCoordinateMean eig U c I degree amplitude n b v z j| ≤
      tensorFeatureCoordinateCap U I degree amplitude j := by
  induction n generalizing b v z with
  | zero => exact tensorTerminalCoordinateMean_abs_le eig U c I degree amplitude z j
  | succ n ih =>
    let := tensorAncestorMarkKernel_markov hN eig U c I degree amplitude (n + 1) b v hb 0
    simpa only [tensorCascadeCoordinateMean, Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const
        (μ := tensorAncestorMarkKernel eig U c I degree amplitude (n + 1) b v 0 z)
        (f := fun a => tensorCascadeCoordinateMean eig U c I degree amplitude n
          (fun i => b (i + 1)) (fun i => v (i + 1)) (z + a) j)
        (ae_of_all _ fun a => by simpa only [Real.norm_eq_abs] using ih _ _ hb.tail (z + a))

lemma tensorCoordinateVariation_add {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (z a : SpinTensorIndex I degree → ℝ)
    (j : SpinTensorIndex I degree) (s : ℝ) :
    tensorCoordinateVariation I degree z j s + a = tensorCoordinateVariation I degree (z + a) j s := by
  funext i
  simp only [tensorCoordinateVariation, Pi.add_apply]
  ring

/-- Every coordinate derivative of the actual backward value is the
corresponding mean propagated through the ancestor kernels. -/
theorem hasDerivAt_tensorCascadeValue_coordinate {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ)
    (j : SpinTensorIndex I degree) (t : ℝ) :
    HasDerivAt (fun s => tensorCascadeValue eig U c I degree amplitude n b v
      (tensorCoordinateVariation I degree z j s))
      (tensorCascadeCoordinateMean eig U c I degree amplitude n b v
        (tensorCoordinateVariation I degree z j t) j) t := by
  induction n generalizing b v z t with
  | zero => exact hasDerivAt_spinTensorTerminal_coordinate eig U c I degree amplitude z j t
  | succ n ih =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    let G := tensorCascadeValue eig U c I degree amplitude n bs vs
    let D := fun x => tensorCascadeCoordinateMean eig U c I degree amplitude n bs vs x j
    have hm : Measurable G := measurable_cascadeRecursion n bs
      (fun i => tensorGaussianLaw I degree (vs i)) (fun _ => measurable_fst.add measurable_snd)
      (measurable_spinTensorTerminal eig U c I degree amplitude)
    have hDm : Measurable D := measurable_tensorCascadeCoordinateMean hN eig U c I degree amplitude n bs vs hb.tail j
    have hg : HasLinearGrowth G := cascadeRecursion_linearGrowth n bs
      (fun i => tensorGaussianLaw I degree (vs i))
      (fun i _ => tensorGaussianLaw_moments hN I degree (vs i))
      (measurable_spinTensorTerminal eig U c I degree amplitude)
      (spinTensorTerminal_linearGrowth eig U c I degree amplitude) (fun i hi => (hb.tail.1 i hi).1)
    have hint : Integrable (fun a => Real.exp (b 0 * G (tensorCoordinateVariation I degree z j t + a)))
        (tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ)) :=
      integrable_exp_of_linearGrowth _ (tensorGaussianLaw_moments hN I degree (v 0))
        (hm.comp (measurable_const.add measurable_id))
        (hg.add_left (tensorCoordinateVariation I degree z j t)) (b 0)
    have hd (s : ℝ) (a : SpinTensorIndex I degree → ℝ) :
        HasDerivAt (fun q => G (tensorCoordinateVariation I degree z j q + a))
          (D (tensorCoordinateVariation I degree z j s + a)) s := by
      simpa only [tensorCoordinateVariation_add, G, D] using ih bs vs hb.tail (z + a) s
    have h := hasDerivAt_logMean_of_bounded_derivative
      (tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ))
      (fun s a => G (tensorCoordinateVariation I degree z j s + a))
      (fun s a => D (tensorCoordinateVariation I degree z j s + a))
      (fun s => hm.comp (measurable_const.add measurable_id))
      (fun s => hDm.comp (measurable_const.add measurable_id))
      (K := tensorFeatureCoordinateCap U I degree amplitude j)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (fun s a => tensorCascadeCoordinateMean_abs_le hN eig U c I degree amplitude n bs vs hb.tail _ j)
      hd (hb.1 0 (by omega)).1.ne' t hint
    have hk := tensorAncestorMarkKernel_eq_tilted hN eig U c I degree amplitude
      (n + 1) b v hb 0 (by omega) (tensorCoordinateVariation I degree z j t)
    have hv : tensorCascadeBackward eig U c I degree amplitude (n + 1) b v 1 = G := by
      dsimp only [G, tensorCascadeValue, tensorCascadeBackward, backwardValue, bs, vs]
      simp only [Nat.add_sub_cancel, Nat.add_comm]
      rfl
    rw [hv] at hk
    simpa only [tensorCascadeValue, cascadeRecursion, tensorCascadeCoordinateMean,
      hk, G, D, bs, vs] using h

def tensorBackwardCoordinateMean {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (i : ℕ)
    (z : SpinTensorIndex I degree → ℝ) (j : SpinTensorIndex I degree) : ℝ :=
  tensorCascadeCoordinateMean eig U c I degree amplitude (n - i)
    (fun q => b (i + q)) (fun q => v (i + q)) z j

/-- The same derivative identity at every backward level, with the
manuscript's ancestor indexing. -/
theorem hasDerivAt_tensorCascadeBackward_coordinate {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (i : ℕ) (z : SpinTensorIndex I degree → ℝ)
    (j : SpinTensorIndex I degree) (t : ℝ) :
    HasDerivAt (fun s => tensorCascadeBackward eig U c I degree amplitude n b v i
      (tensorCoordinateVariation I degree z j s))
      (tensorBackwardCoordinateMean eig U c I degree amplitude n b v i
        (tensorCoordinateVariation I degree z j t) j) t := by
  have hbs : CascadeExponents (n - i) (fun q => b (i + q)) := by
    constructor
    · intro q hq
      exact hb.1 (i + q) (by omega)
    · intro q r hqr hr
      exact hb.2 (i + q) (i + r) (by omega) (by omega)
  exact hasDerivAt_tensorCascadeValue_coordinate hN eig U c I degree amplitude (n - i)
    (fun q => b (i + q)) (fun q => v (i + q)) hbs z j t

lemma measurable_tensorBackwardCoordinateMean {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (i : ℕ) (j : SpinTensorIndex I degree) :
    Measurable (fun z => tensorBackwardCoordinateMean eig U c I degree amplitude n b v i z j) := by
  have hbs : CascadeExponents (n - i) (fun q => b (i + q)) :=
    ⟨fun q hq => hb.1 (i + q) (by omega),
      fun q r hqr hr => hb.2 (i + q) (i + r) (by omega) (by omega)⟩
  exact measurable_tensorCascadeCoordinateMean hN eig U c I degree amplitude (n - i)
    (fun q => b (i + q)) (fun q => v (i + q)) hbs j

lemma tensorBackwardCoordinateMean_abs_le {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (i : ℕ) (z : SpinTensorIndex I degree → ℝ)
    (j : SpinTensorIndex I degree) :
    |tensorBackwardCoordinateMean eig U c I degree amplitude n b v i z j| ≤
      tensorFeatureCoordinateCap U I degree amplitude j := by
  have hbs : CascadeExponents (n - i) (fun q => b (i + q)) :=
    ⟨fun q hq => hb.1 (i + q) (by omega),
      fun q r hqr hr => hb.2 (i + q) (i + r) (by omega) (by omega)⟩
  exact tensorCascadeCoordinateMean_abs_le hN eig U c I degree amplitude (n - i)
    (fun q => b (i + q)) (fun q => v (i + q)) hbs z j

/-- The backward gradient is a martingale under the actual normalized
ancestor mark transitions. -/
theorem tensorBackwardCoordinateMean_step {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (i : ℕ) (hi : i < n)
    (z : SpinTensorIndex I degree → ℝ) (j : SpinTensorIndex I degree) :
    tensorBackwardCoordinateMean eig U c I degree amplitude n b v i z j =
      ∫ a, tensorBackwardCoordinateMean eig U c I degree amplitude n b v (i + 1) (z + a) j
        ∂tensorAncestorMarkKernel eig U c I degree amplitude n b v i z := by
  have hm := measurable_tensorCascadeBackward eig U c I degree amplitude n b v (i + 1)
  have hDm := measurable_tensorBackwardCoordinateMean hN eig U c I degree amplitude n b v hb (i + 1) j
  have hint := backwardValue_linearGrowth_moments n b
    (fun q => tensorGaussianLaw I degree (v q))
    (fun q _ => tensorGaussianLaw_moments hN I degree (v q))
    (measurable_spinTensorTerminal eig U c I degree amplitude)
    (spinTensorTerminal_linearGrowth eig U c I degree amplitude)
    (fun q hq => (hb.1 q hq).1) i hi z
  have hd (s : ℝ) (a : SpinTensorIndex I degree → ℝ) :
      HasDerivAt (fun q => tensorCascadeBackward eig U c I degree amplitude n b v (i + 1)
        (tensorCoordinateVariation I degree z j q + a))
        (tensorBackwardCoordinateMean eig U c I degree amplitude n b v (i + 1)
          (tensorCoordinateVariation I degree z j s + a) j) s := by
    simpa only [tensorCoordinateVariation_add] using
      hasDerivAt_tensorCascadeBackward_coordinate hN eig U c I degree amplitude n b v hb (i + 1) (z + a) j s
  have hz : tensorCoordinateVariation I degree z j 0 = z := by
    ext a
    simp [tensorCoordinateVariation]
  have hh := hasDerivAt_logMean_of_bounded_derivative
    (tensorGaussianLaw I degree (v i) : Measure (SpinTensorIndex I degree → ℝ))
    (fun s a => tensorCascadeBackward eig U c I degree amplitude n b v (i + 1)
      (tensorCoordinateVariation I degree z j s + a))
    (fun s a => tensorBackwardCoordinateMean eig U c I degree amplitude n b v (i + 1)
      (tensorCoordinateVariation I degree z j s + a) j)
    (fun s => hm.comp (measurable_const.add measurable_id))
    (fun s => hDm.comp (measurable_const.add measurable_id))
    (K := tensorFeatureCoordinateCap U I degree amplitude j)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (fun s a => tensorBackwardCoordinateMean_abs_le hN eig U c I degree amplitude n b v hb (i + 1) _ j)
    hd (hb.1 i hi).1.ne' 0 (by simpa only [hz, tensorCascadeBackward] using hint)
  have hf : (fun s => logMean (b i)
      (tensorGaussianLaw I degree (v i) : Measure (SpinTensorIndex I degree → ℝ))
      (fun a => tensorCascadeBackward eig U c I degree amplitude n b v (i + 1)
        (tensorCoordinateVariation I degree z j s + a))) =
      (fun s => tensorCascadeBackward eig U c I degree amplitude n b v i
        (tensorCoordinateVariation I degree z j s)) := by
    funext s
    exact (tensorCascadeBackward_step eig U c I degree amplitude n b v i hi _).symm
  rw [hf, hz, ← tensorAncestorMarkKernel_eq_tilted hN eig U c I degree amplitude n b v hb i hi z] at hh
  have hc := hasDerivAt_tensorCascadeBackward_coordinate hN eig U c I degree amplitude n b v hb i z j 0
  rw [hz] at hc
  exact hc.unique hh

end InvariantIsing

end

end OAI
