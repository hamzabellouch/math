import OAI.Probability.FreeIsing.Trees.LawSpectral

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem367.TreeLawKoopman

variable {d : ℕ} {A : Type*} [MeasurableSpace A]
variable (μ : Measure (TreeVertex d → A))
variable (hμ : ∀ g : TreeAut d, MeasurePreserving (relabel g) μ μ)

theorem inner_koopman_eq_integral (f : Lp ℝ 2 μ) (g : TreeAut d) :
    inner ℝ f (koopmanL2 (relabel g) (hμ g) f) =
      ∫ U, f U * f (relabel g U) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving f (hμ g)] with U hU
  change koopmanL2 (relabel g) (hμ g) f U = f (relabel g U) at hU
  simp [hU, mul_comm]

theorem inner_koopman_eq_integral_of_local
    (s : Finset (TreeVertex d)) (f : Lp ℝ 2 μ) (F : (s → A) → ℝ)
    (hf : f =ᵐ[μ] fun U => F (fun i => U i)) (g : TreeAut d) :
    inner ℝ f (koopmanL2 (relabel g) (hμ g) f) =
      ∫ U, F (fun i => U i) * F (fun i => U (g.toEquiv.symm i)) ∂μ := by
  rw [inner_koopman_eq_integral]
  apply integral_congr_ae
  filter_upwards [hf, (hμ g).quasiMeasurePreserving.ae hf] with U hU hUg
  rw [hU, hUg]
  rfl

theorem exists_radial_bound_of_far_decay (f : Lp ℝ 2 μ) (N : ℕ)
    {theta q : ℝ} (htheta : 0 ≤ theta) (hthetaq : theta ≤ q)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hfar : ∀ g : TreeAut d, N < (g.toEquiv TreeEscape.root).1.length →
      |inner ℝ f (koopmanL2 (relabel g) (hμ g) f)| ≤
        ‖f‖ ^ 2 * theta ^ ((g.toEquiv TreeEscape.root).1.length - N)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : TreeAut d,
      |inner ℝ f (koopmanL2 (relabel g) (hμ g) f)| ≤
        C * q ^ (g.toEquiv TreeEscape.root).1.length := by
  let C := ‖f‖ ^ 2 / q ^ N
  have hC : 0 ≤ C := div_nonneg (sq_nonneg _) (pow_nonneg hq.le _)
  refine ⟨C, hC, fun g => ?_⟩
  let k := (g.toEquiv TreeEscape.root).1.length
  by_cases hNk : N < k
  · have hpow : q ^ k = q ^ (k - N) * q ^ N := by
      rw [← pow_add, Nat.sub_add_cancel hNk.le]
    calc
      |inner ℝ f (koopmanL2 (relabel g) (hμ g) f)| ≤
          ‖f‖ ^ 2 * theta ^ (k - N) := hfar g hNk
      _ ≤ ‖f‖ ^ 2 * q ^ (k - N) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htheta hthetaq _) (sq_nonneg _)
      _ = C * q ^ k := by
        dsimp [C]
        rw [hpow]
        field_simp
  · have hpow : q ^ N ≤ q ^ k :=
      pow_le_pow_of_le_one hq.le hq1 (Nat.le_of_not_gt hNk)
    calc
      |inner ℝ f (koopmanL2 (relabel g) (hμ g) f)| ≤
          ‖f‖ * ‖koopmanL2 (relabel g) (hμ g) f‖ := abs_real_inner_le_norm _ _
      _ = ‖f‖ ^ 2 := by rw [koopmanL2_norm, pow_two]
      _ = C * q ^ N := by
        dsimp [C]
        rw [div_mul_cancel₀ _ (pow_ne_zero _ hq.ne')]
      _ ≤ C * q ^ k := mul_le_mul_of_nonneg_left hpow hC

theorem localCriticalDecay_of_far_decay (hd : 3 ≤ d)
    {theta : ℝ} (htheta : 0 ≤ theta)
    (hthreshold : theta ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹)
    (hfar : ∀ (s : Finset (TreeVertex d)) (f : Lp ℝ 2 μ) (F : (s → A) → ℝ),
      Measurable F → (f =ᵐ[μ] fun U => F (fun i => U i)) →
      (∫ U, f U ∂μ) = 0 →
      ∃ N : ℕ, ∀ g : TreeAut d, N < (g.toEquiv TreeEscape.root).1.length →
        |inner ℝ f (koopmanL2 (relabel g) (hμ g) f)| ≤
          ‖f‖ ^ 2 * theta ^ ((g.toEquiv TreeEscape.root).1.length - N)) :
    LocalCriticalDecay μ hμ := by
  intro s f F hF hf hzero
  obtain ⟨N, hN⟩ := hfar s f F hF hf hzero
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  apply exists_radial_bound_of_far_decay μ hμ f N htheta hthreshold (inv_pos.mpr hs)
  · apply inv_le_one_of_one_le₀
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ (d : ℝ) - 1)).2
    norm_num
    linarith
  · exact hN

end Problem367.TreeLawKoopman

end

end OAI
