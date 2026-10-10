import OAI.Probability.FreeIsing.Stochastic.StoppedBrownianSquare

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.StoppedBrownianCross
open StoppedSimpleIntegral BrownianFiltration StoppedBrownianSquare

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B C : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem product_martingale_of_increment_product_zero [IsFiniteMeasure P]
    (hB : Martingale B F P) (hC : Martingale C F P)
    (hB2 : ∀ t, MemLp (B t) 2 P) (hC2 : ∀ t, MemLp (C t) 2 P)
    (hcross : ∀ s t, s ≤ t →
      P[(fun ω => (B t ω - B s ω) * (C t ω - C s ω)) | F s] =ᵐ[P] 0) :
    Martingale (fun t ω => B t ω * C t ω) F P := by
  refine ⟨fun t => (hB.stronglyAdapted t).mul (hC.stronglyAdapted t), ?_⟩
  intro s t hst
  have hBC : Integrable (fun ω => B s ω * (C t ω - C s ω)) P :=
    (hB2 s).integrable_mul ((hC2 t).sub (hC2 s))
  have hCB : Integrable (fun ω => C s ω * (B t ω - B s ω)) P :=
    (hC2 s).integrable_mul ((hB2 t).sub (hB2 s))
  have hzBC : P[(fun ω => B s ω * (C t ω - C s ω)) | F s] =ᵐ[P] 0 := by
    have h := intervalSum_eq_condExp_terminal_of_integrable hC hst
      (hB.stronglyAdapted s) hBC s
    filter_upwards [h] with ω hω
    simpa only [intervalSum, min_self, min_eq_left hst, sub_self, mul_zero, Pi.zero_apply] using hω
  have hzCB : P[(fun ω => C s ω * (B t ω - B s ω)) | F s] =ᵐ[P] 0 := by
    have h := intervalSum_eq_condExp_terminal_of_integrable hB hst
      (hC.stronglyAdapted s) hCB s
    filter_upwards [h] with ω hω
    simpa only [intervalSum, min_self, min_eq_left hst, sub_self, mul_zero, Pi.zero_apply] using hω
  have hDC : Integrable (fun ω => (B t ω - B s ω) * (C t ω - C s ω)) P :=
    ((hB2 t).sub (hB2 s)).integrable_mul ((hC2 t).sub (hC2 s))
  have hSS : Integrable (fun ω => B s ω * C s ω) P :=
    (hB2 s).integrable_mul (hC2 s)
  have hself : P[(fun ω => B s ω * C s ω) | F s] =
      (fun ω => B s ω * C s ω) := condExp_of_stronglyMeasurable (F.le s)
        ((hB.stronglyAdapted s).mul (hC.stronglyAdapted s)) hSS
  have hpoly : (fun ω => B t ω * C t ω) =
      ((fun ω => (B t ω - B s ω) * (C t ω - C s ω)) +
        (fun ω => B s ω * (C t ω - C s ω))) +
      ((fun ω => C s ω * (B t ω - B s ω)) + (fun ω => B s ω * C s ω)) := by
    funext ω
    simp only [Pi.add_apply]
    ring
  change P[(fun ω => B t ω * C t ω) | F s] =ᵐ[P] (fun ω => B s ω * C s ω)
  rw [hpoly]
  filter_upwards [condExp_add (hDC.add hBC) (hCB.add hSS) (F s),
    condExp_add hDC hBC (F s), condExp_add hCB hSS (F s),
    hcross s t hst, hzBC, hzCB] with ω h1 h2 h3 h4 h5 h6
  simp only [Pi.add_apply] at h1 h2 h3
  rw [hself] at h3
  rw [h1, h2, h3, h4, h5, h6]
  simp

theorem increment_product_condExp_zero
    (hB : IsPreBrownianReal B P) (_hC : IsPreBrownianReal C P)
    (hAdB : StronglyAdapted F B) (hAdC : StronglyAdapted F C)
    {s t : ℝ≥0}
    (hpair : Indep (MeasurableSpace.comap
      (fun ω => (B t ω - B s ω, C t ω - C s ω)) inferInstance) (F s) P)
    (hind : IndepFun (fun ω => B t ω - B s ω) (fun ω => C t ω - C s ω) P) :
    P[(fun ω => (B t ω - B s ω) * (C t ω - C s ω)) | F s] =ᵐ[P] 0 := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hmB := ((hAdB t).mono (F.le t)).measurable.sub
    ((hAdB s).mono (F.le s)).measurable
  have hmC := ((hAdC t).mono (F.le t)).measurable.sub
    ((hAdC s).mono (F.le s)).measurable
  have hmPair : Measurable[MeasurableSpace.comap
      (fun ω => (B t ω - B s ω, C t ω - C s ω)) inferInstance]
      (fun ω => (B t ω - B s ω, C t ω - C s ω)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hmProd := (measurable_fst.mul measurable_snd).comp hmPair
  have hi : Indep (MeasurableSpace.comap
      (fun ω => (B t ω - B s ω) * (C t ω - C s ω)) inferInstance) (F s) P :=
    indep_of_indep_of_le_left hpair hmProd.comap_le
  have hce := condExp_indep_eq (hmB.mul hmC).comap_le (F.le s)
    (show StronglyMeasurable[MeasurableSpace.comap
      (fun ω => (B t ω - B s ω) * (C t ω - C s ω)) inferInstance]
      (fun ω => (B t ω - B s ω) * (C t ω - C s ω)) from
        (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable) hi
  have hzB : (∫ ω, B t ω - B s ω ∂P) = 0 := by
    rw [integral_sub (hB.integrable_eval t) (hB.integrable_eval s),
      hB.integral_eval, hB.integral_eval, sub_self]
  have he := hind.integral_fun_mul_eq_mul_integral hmB.aestronglyMeasurable
    hmC.aestronglyMeasurable
  rw [hzB, zero_mul] at he
  filter_upwards [hce] with ω hω
  simpa only [he, Pi.zero_apply] using hω

theorem brownian_product_martingale
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C P)
    (hAdB : StronglyAdapted F B) (hAdC : StronglyAdapted F C)
    (hpair : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
      (fun ω => (B t ω - B s ω, C t ω - C s ω)) inferInstance) (F s) P)
    (hind : ∀ s t, s ≤ t →
      IndepFun (fun ω => B t ω - B s ω) (fun ω => C t ω - C s ω) P) :
    Martingale (fun t ω => B t ω * C t ω) F P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hleft s t (hst : s ≤ t) : Indep (MeasurableSpace.comap
      (fun ω => B t ω - B s ω) inferInstance) (F s) P := by
    apply indep_of_indep_of_le_left (hpair s t hst)
    have hmPair : Measurable[MeasurableSpace.comap
        (fun ω => (B t ω - B s ω, C t ω - C s ω)) inferInstance]
        (fun ω => (B t ω - B s ω, C t ω - C s ω)) :=
      measurable_iff_comap_le.mpr le_rfl
    exact hmPair.fst.comap_le
  have hright s t (hst : s ≤ t) : Indep (MeasurableSpace.comap
      (fun ω => C t ω - C s ω) inferInstance) (F s) P := by
    apply indep_of_indep_of_le_left (hpair s t hst)
    have hmPair : Measurable[MeasurableSpace.comap
        (fun ω => (B t ω - B s ω, C t ω - C s ω)) inferInstance]
        (fun ω => (B t ω - B s ω, C t ω - C s ω)) :=
      measurable_iff_comap_le.mpr le_rfl
    exact hmPair.snd.comap_le
  exact product_martingale_of_increment_product_zero
    (martingale_of_independent_past hB hAdB hleft)
    (martingale_of_independent_past hC hAdC hright)
    (fun t => (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two)
    (fun t => (hC.isGaussianProcess.hasGaussianLaw_eval t).memLp_two)
    (fun s t hst => increment_product_condExp_zero hB hC hAdB hAdC
      (hpair s t hst) (hind s t hst))

theorem intervalSum_memLp_two_of_bounded [IsFiniteMeasure P]
    (hB2 : ∀ t, MemLp (B t) 2 P) {a b : ℝ≥0} {H : Ω → ℝ}
    (hH : StronglyMeasurable[F a] H) {K : ℝ}
    (hbound : ∀ᵐ ω ∂P, ‖H ω‖ ≤ K) (t : ℝ≥0) :
    MemLp (intervalSum B H a b t) 2 P := by
  have hHtop : MemLp H (⊤ : ENNReal) P :=
    MemLp.of_bound (hH.mono (F.le a)).aestronglyMeasurable K hbound
  exact hHtop.fun_mul ((hB2 (min t b)).sub (hB2 (min t a)))

theorem intervalSum_product_martingale [IsFiniteMeasure P]
    (hB : Martingale B F P) (hC : Martingale C F P)
    (hBC : Martingale (fun t ω => B t ω * C t ω) F P)
    (hB2 : ∀ t, MemLp (B t) 2 P) (hC2 : ∀ t, MemLp (C t) 2 P)
    {a b : ℝ≥0} (hab : a ≤ b) {H G : Ω → ℝ}
    (hH : StronglyMeasurable[F a] H) (hG : StronglyMeasurable[F a] G)
    {K L : ℝ} (hboundH : ∀ᵐ ω ∂P, ‖H ω‖ ≤ K)
    (hboundG : ∀ᵐ ω ∂P, ‖G ω‖ ≤ L) :
    Martingale (fun t ω => intervalSum B H a b t ω * intervalSum C G a b t ω) F P := by
  have hHG : StronglyMeasurable[F a] (fun ω => H ω * G ω) := hH.mul hG
  have hboundHG : ∀ᵐ ω ∂P, ‖H ω * G ω‖ ≤ K * L := by
    filter_upwards [hboundH, hboundG] with ω hω kω
    rw [norm_mul]
    exact mul_le_mul hω kω (norm_nonneg _) ((norm_nonneg _).trans hω)
  have hm1 := intervalSum_martingale hBC hab hHG hboundHG
  have hCB : Integrable (fun ω => C a ω * (B b ω - B a ω)) P :=
    (hC2 a).integrable_mul ((hB2 b).sub (hB2 a))
  have hBC' : Integrable (fun ω => B a ω * (C b ω - C a ω)) P :=
    (hB2 a).integrable_mul ((hC2 b).sub (hC2 a))
  have hCBH : Integrable (fun ω => (H ω * G ω * C a ω) * (B b ω - B a ω)) P := by
    have h := hCB.bdd_mul (hHG.mono (F.le a)).aestronglyMeasurable hboundHG
    convert h using 1
    funext ω
    ring
  have hBCH : Integrable (fun ω => (H ω * G ω * B a ω) * (C b ω - C a ω)) P := by
    have h := hBC'.bdd_mul (hHG.mono (F.le a)).aestronglyMeasurable hboundHG
    convert h using 1
    funext ω
    ring
  have hm2 := intervalSum_martingale_of_integrable_terminal hB hab
    (hHG.mul (hC.stronglyAdapted a)) hCBH
  have hm3 := intervalSum_martingale_of_integrable_terminal hC hab
    (hHG.mul (hB.stronglyAdapted a)) hBCH
  convert (hm1.sub hm2).sub hm3 using 1
  funext t ω
  rcases le_total t a with hta | hat
  · simp only [intervalSum, min_eq_left hta, min_eq_left (hta.trans hab),
      sub_self, mul_zero, Pi.sub_apply]
  · simp only [intervalSum, min_eq_right hat, Pi.sub_apply, Pi.mul_apply]
    ring

theorem stopped_predictable_sum_product_martingale [IsFiniteMeasure P]
    (hB : Martingale B F P) (hC : Martingale C F P)
    (hBC : Martingale (fun t ω => B t ω * C t ω) F P)
    (hB2 : ∀ t, MemLp (B t) 2 P) (hC2 : ∀ t, MemLp (C t) 2 P)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (H G : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (τ i)] (H i))
    (hG : ∀ i, StronglyMeasurable[F (τ i)] (G i))
    (K L : ℕ → ℝ) (hboundH : ∀ i, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ K i)
    (hboundG : ∀ i, ∀ᵐ ω ∂P, ‖G i ω‖ ≤ L i) (n : ℕ) :
    Martingale (fun t ω =>
      (∑ i ∈ Finset.range n, intervalSum B (H i) (τ i) (τ (i + 1)) t ω) *
      (∑ i ∈ Finset.range n, intervalSum C (G i) (τ i) (τ (i + 1)) t ω)) F P := by
  have hsumB2 (m : ℕ) (t : ℝ≥0) : MemLp (fun ω => ∑ i ∈ Finset.range m,
      intervalSum B (H i) (τ i) (τ (i + 1)) t ω) 2 P :=
    memLp_finsetSum _ fun i _ => intervalSum_memLp_two_of_bounded hB2 (hH i) (hboundH i) t
  have hsumC2 (m : ℕ) (t : ℝ≥0) : MemLp (fun ω => ∑ i ∈ Finset.range m,
      intervalSum C (G i) (τ i) (τ (i + 1)) t ω) 2 P :=
    memLp_finsetSum _ fun i _ => intervalSum_memLp_two_of_bounded hC2 (hG i) (hboundG i) t
  induction n with
  | zero =>
      convert martingale_zero ℝ F P using 1
      funext t ω
      simp
  | succ n ih =>
      let S : ℝ≥0 → Ω → ℝ := fun t ω => ∑ i ∈ Finset.range n,
        intervalSum B (H i) (τ i) (τ (i + 1)) t ω
      let R : ℝ≥0 → Ω → ℝ := fun t ω => ∑ i ∈ Finset.range n,
        intervalSum C (G i) (τ i) (τ (i + 1)) t ω
      have hS : Martingale S F P := finite_intervalSum_martingale hB (Finset.range n)
        τ (fun i => τ (i + 1)) H (fun i _ => hτ (Nat.le_succ i))
        (fun i _ => hH i) K (fun i _ => hboundH i)
      have hR : Martingale R F P := finite_intervalSum_martingale hC (Finset.range n)
        τ (fun i => τ (i + 1)) G (fun i _ => hτ (Nat.le_succ i))
        (fun i _ => hG i) L (fun i _ => hboundG i)
      have hnewB := intervalSum_memLp_two_of_bounded (b := τ (n + 1)) hB2 (hH n) (hboundH n) (τ (n + 1))
      have hnewC := intervalSum_memLp_two_of_bounded (b := τ (n + 1)) hC2 (hG n) (hboundG n) (τ (n + 1))
      have hiSC : Integrable (fun ω => (S (τ n) ω * G n ω) *
          (C (τ (n + 1)) ω - C (τ n) ω)) P := by
        have h := (hsumB2 n (τ n)).integrable_mul hnewC
        convert h using 1
        funext ω
        simp only [Pi.mul_apply, intervalSum, min_self, min_eq_right (hτ (Nat.le_succ n))]
        dsimp [S, R]
        simp only [intervalSum]
        ring
      have hiRB : Integrable (fun ω => (R (τ n) ω * H n ω) *
          (B (τ (n + 1)) ω - B (τ n) ω)) P := by
        have h := (hsumC2 n (τ n)).integrable_mul hnewB
        convert h using 1
        funext ω
        simp only [Pi.mul_apply, intervalSum, min_self, min_eq_right (hτ (Nat.le_succ n))]
        dsimp [S, R]
        simp only [intervalSum]
        ring
      have hSC := intervalSum_martingale_of_integrable_terminal hC (hτ (Nat.le_succ n))
        ((hS.stronglyAdapted (τ n)).mul (hG n)) hiSC
      have hRB := intervalSum_martingale_of_integrable_terminal hB (hτ (Nat.le_succ n))
        ((hR.stronglyAdapted (τ n)).mul (hH n)) hiRB
      have heqSC : (fun t ω => S t ω * intervalSum C (G n) (τ n) (τ (n + 1)) t ω) =
          intervalSum C (fun ω => S (τ n) ω * G n ω) (τ n) (τ (n + 1)) := by
        funext t ω
        rcases le_total t (τ n) with hta | hat
        · simp only [intervalSum, min_eq_left hta,
            min_eq_left (hta.trans (hτ (Nat.le_succ n))), sub_self, mul_zero]
        · have hc : S t = S (τ n) := sum_intervalSum_eq_terminal τ hτ H n hat
          rw [hc]
          simp only [intervalSum]
          ring
      have heqRB : (fun t ω => R t ω * intervalSum B (H n) (τ n) (τ (n + 1)) t ω) =
          intervalSum B (fun ω => R (τ n) ω * H n ω) (τ n) (τ (n + 1)) := by
        funext t ω
        rcases le_total t (τ n) with hta | hat
        · simp only [intervalSum, min_eq_left hta,
            min_eq_left (hta.trans (hτ (Nat.le_succ n))), sub_self, mul_zero]
        · have hc : R t = R (τ n) := sum_intervalSum_eq_terminal τ hτ G n hat
          rw [hc]
          simp only [intervalSum]
          ring
      change Martingale (intervalSum C (fun ω => S (τ n) ω * G n ω)
        (τ n) (τ (n + 1))) F P at hSC
      change Martingale (intervalSum B (fun ω => R (τ n) ω * H n ω)
        (τ n) (τ (n + 1))) F P at hRB
      rw [← heqSC] at hSC
      rw [← heqRB] at hRB
      have hdiag := intervalSum_product_martingale hB hC hBC hB2 hC2
        (hτ (Nat.le_succ n)) (hH n) (hG n) (hboundH n) (hboundG n)
      convert ((ih.add hdiag).add hSC).add hRB using 1
      funext t ω
      simp only [Finset.sum_range_succ, Pi.add_apply]
      dsimp [S, R]
      ring

theorem stopped_brownian_sum_product_martingale
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C P)
    (hAdB : StronglyAdapted F B) (hAdC : StronglyAdapted F C)
    (hpair : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
      (fun ω => (B t ω - B s ω, C t ω - C s ω)) inferInstance) (F s) P)
    (hind : ∀ s t, s ≤ t →
      IndepFun (fun ω => B t ω - B s ω) (fun ω => C t ω - C s ω) P)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (H G : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (τ i)] (H i))
    (hG : ∀ i, StronglyMeasurable[F (τ i)] (G i))
    (K L : ℕ → ℝ) (hboundH : ∀ i, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ K i)
    (hboundG : ∀ i, ∀ᵐ ω ∂P, ‖G i ω‖ ≤ L i) (n : ℕ) :
    Martingale (fun t ω =>
      (∑ i ∈ Finset.range n, intervalSum B (H i) (τ i) (τ (i + 1)) t ω) *
      (∑ i ∈ Finset.range n, intervalSum C (G i) (τ i) (τ (i + 1)) t ω)) F P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hleft s t (hst : s ≤ t) : Indep (MeasurableSpace.comap
      (fun ω => B t ω - B s ω) inferInstance) (F s) P := by
    apply indep_of_indep_of_le_left (hpair s t hst)
    have hmPair : Measurable[MeasurableSpace.comap
        (fun ω => (B t ω - B s ω, C t ω - C s ω)) inferInstance]
        (fun ω => (B t ω - B s ω, C t ω - C s ω)) :=
      measurable_iff_comap_le.mpr le_rfl
    exact hmPair.fst.comap_le
  have hright s t (hst : s ≤ t) : Indep (MeasurableSpace.comap
      (fun ω => C t ω - C s ω) inferInstance) (F s) P := by
    apply indep_of_indep_of_le_left (hpair s t hst)
    have hmPair : Measurable[MeasurableSpace.comap
        (fun ω => (B t ω - B s ω, C t ω - C s ω)) inferInstance]
        (fun ω => (B t ω - B s ω, C t ω - C s ω)) :=
      measurable_iff_comap_le.mpr le_rfl
    exact hmPair.snd.comap_le
  exact stopped_predictable_sum_product_martingale
    (martingale_of_independent_past hB hAdB hleft)
    (martingale_of_independent_past hC hAdC hright)
    (brownian_product_martingale hB hC hAdB hAdC hpair hind)
    (fun t => (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two)
    (fun t => (hC.isGaussianProcess.hasGaussianLaw_eval t).memLp_two)
    τ hτ H G hH hG K L hboundH hboundG n

theorem integral_stopped_sum_product_eq_zero [IsFiniteMeasure P]
    (τ : ℕ → ℝ≥0) (H G : ℕ → Ω → ℝ) (n : ℕ)
    (hM : Martingale (fun t ω =>
      (∑ i ∈ Finset.range n, intervalSum B (H i) (τ i) (τ (i + 1)) t ω) *
      (∑ i ∈ Finset.range n, intervalSum C (G i) (τ i) (τ (i + 1)) t ω)) F P)
    (t : ℝ≥0) :
    (∫ ω, (∑ i ∈ Finset.range n, intervalSum B (H i) (τ i) (τ (i + 1)) t ω) *
      (∑ i ∈ Finset.range n, intervalSum C (G i) (τ i) (τ (i + 1)) t ω) ∂P) = 0 := by
  have he := hM.setIntegral_eq (show (0 : ℝ≥0) ≤ t from zero_le) MeasurableSet.univ
  simpa [intervalSum] using he.symm

end Problem367.StoppedBrownianCross

end

end OAI
