import OAI.MathematicalPhysics.CriticalSK.VariationalDefinitions

namespace OAI

noncomputable section
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
namespace CriticalSK

section FullRelaxation
variable {n : ℕ} (W : Disorder n)

lemma kernel_energy_pair_identity (K : Matrix (Spin n) (Spin n) ℝ)
    (hrow : ∀ x, ∑ y, K x y = 1)
    (hstat : ∀ y, ∑ x, gibbs W x * K x y = gibbs W y)
    (f : Spin n → ℝ) :
    mean W (fun x => ∑ y, K x y * (f x - f y) ^ 2) =
      2 * mean W (fun x => f x * (f x - K.mulVec f x)) := by
  have ht (x : Spin n) : (∑ y, K x y * (f x - f y) ^ 2) =
      (f x ^ 2 - 2 * (f x * K.mulVec f x)) + K.mulVec (fun y => f y ^ 2) x := by
    calc
      _ = ∑ y, (K x y * f x ^ 2 - 2 * (f x * (K x y * f y)) + K x y * f y ^ 2) := by
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.sum_mul, hrow, one_mul, Matrix.mulVec, dotProduct]
  simp_rw [ht]
  rw [mean_add, mean_sub, mean_const_mul, mean_kernel W K hstat]
  have he (x : Spin n) : f x * (f x - K.mulVec f x) =
      f x ^ 2 - f x * K.mulVec f x := by ring
  simp_rw [he]
  rw [mean_sub]
  ring

lemma variance_pair_identity (f : Spin n → ℝ) :
    mean W (fun x => ∑ y, gibbs W y * (f x - f y) ^ 2) = 2 * variance W f := by
  have hh := kernel_energy_pair_identity W (fun _ y => gibbs W y)
    (fun _ => gibbs_sum W)
    (fun y => by simp only [← Finset.sum_mul, gibbs_sum, one_mul]) f
  have hmul (x : Spin n) :
      Matrix.mulVec (fun _ y : Spin n => gibbs W y) f x = mean W f := rfl
  simp_rw [hmul] at hh
  rw [hh]
  congr 1
  have he (x : Spin n) : f x * (f x - mean W f) = f x ^ 2 - f x * mean W f := by ring
  simp_rw [he]
  rw [mean_sub, mean_mul_const]
  have hs := mean_square_center_identity W f 0
  simp only [sub_zero] at hs
  nlinarith

lemma kernel_energy_minorization (K : Matrix (Spin n) (Spin n) ℝ)
    (hrow : ∀ x, ∑ y, K x y = 1)
    (hstat : ∀ y, ∑ x, gibbs W x * K x y = gibbs W y)
    {c : ℝ} (hminor : ∀ x y, c * gibbs W y ≤ K x y) (f : Spin n → ℝ) :
    c * variance W f ≤ mean W (fun x => f x * (f x - K.mulVec f x)) := by
  have hh : c * mean W (fun x => ∑ y, gibbs W y * (f x - f y) ^ 2) ≤
      mean W (fun x => ∑ y, K x y * (f x - f y) ^ 2) := by
    rw [← mean_const_mul]
    apply mean_mono
    intro x
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hminor x y) (sq_nonneg (f x - f y))
  rw [variance_pair_identity, kernel_energy_pair_identity W K hrow hstat] at hh
  linarith

lemma exists_finite_poincare (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Spin n → ℝ, variance W f ≤ C * dirichlet W f := by
  classical
  let T : Finset ℝ := Finset.univ.image (fun p : Spin n × Spin n => (discreteKernel W ^ n) p.1 p.2)
  have hT : T.Nonempty := Finset.Nonempty.image Finset.univ_nonempty _
  let c := T.min' hT
  have hc : 0 < c := by
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp (Finset.min'_mem T hT)
    dsimp only [c]
    rw [← hp]
    exact discreteKernel_power_pos W hn p.1 p.2
  have hminor : ∀ x y, c * gibbs W y ≤ (discreteKernel W ^ n) x y := by
    intro x y
    calc
      _ ≤ c := by simpa only [mul_one] using mul_le_mul_of_nonneg_left (gibbs_le_one W y) hc.le
      _ ≤ _ := Finset.min'_le T _ (Finset.mem_image.mpr ⟨(x, y), Finset.mem_univ _, rfl⟩)
  refine ⟨c⁻¹, inv_pos.mpr hc, fun f => ?_⟩
  have hlow := kernel_energy_minorization W (discreteKernel W ^ n)
    (kernel_pow_sum (discreteKernel_sum W hn) n)
    (kernel_pow_stationary (discreteKernel_stationary W hn) n) hminor f
  have hup := discrete_inner_increment_le W hn n f
  rw [div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)), one_mul] at hup
  have hh : c * variance W f ≤ dirichlet W f := hlow.trans hup
  have := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hh)
  simpa only [div_eq_mul_inv, mul_comm] using this

lemma variance_nonneg_full (f : Spin n → ℝ) : 0 ≤ variance W f :=
  mean_nonneg W (fun _ => sq_nonneg _)

lemma dirichlet_le_sites_variance (f : Spin n → ℝ) :
    dirichlet W f ≤ (n : ℝ) * variance W f := by
  calc
    _ ≤ ∑ _i : Fin n, variance W f := by
      apply Finset.sum_le_sum
      intro i _
      exact siteAverage_least_squares W i f (fun _ => mean W f) (fun _ _ _ => rfl)
    _ = _ := by simp

lemma variance_linear_pos_full {a : Fin n → ℝ} (ha : a ≠ 0) :
    0 < variance W (linearObservable a) := by
  have hdpos := dirichlet_linear_pos W ha
  have hd := dirichlet_le_sites_variance W (linearObservable a)
  by_contra h
  have ht := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (le_of_not_gt h)
  linarith

lemma full_ratios_bdd (hn : 0 < n) :
    BddAbove {r : ℝ | ∃ f : Spin n → ℝ, 0 < variance W f ∧
      r = variance W f / dirichlet W f} := by
  obtain ⟨C, hC, hgap⟩ := exists_finite_poincare W hn
  refine ⟨C, ?_⟩
  rintro r ⟨f, hf, rfl⟩
  have hd : 0 < dirichlet W f := by
    by_contra h
    have ht := mul_nonpos_of_nonneg_of_nonpos hC.le (le_of_not_gt h)
    have hh := hgap f
    linarith
  exact (div_le_iff₀ hd).mpr (hgap f)

lemma linearRayleigh_le_relaxationTime (hn : 0 < n) :
    linearRayleigh W ≤ relaxationTime W := by
  apply csSup_le (linear_ratios_nonempty W hn)
  rintro r ⟨a, ha, rfl⟩
  exact le_csSup (full_ratios_bdd W hn) ⟨linearObservable a, variance_linear_pos_full W ha, rfl⟩

end FullRelaxation

theorem critical_relaxation_lower_bound (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => (disorderLaw n).real
      {W | (n : ℝ) ^ (2 / 3 - δ) ≤ relaxationTime W}) atTop (𝓝 1) := by
  let M : ℕ → ℝ := fun n => if n = 0 then 1 else (n : ℝ) ^ δ
  have hMpos : ∀ n, 0 < M n := by
    intro n
    by_cases hn : n = 0
    · simp [M, hn]
    · simpa only [M, ite_eq_right hn] using Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) δ
  have hMeq : (fun n : ℕ => (n : ℝ) ^ δ) =ᶠ[atTop] M := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp [M, Nat.ne_of_gt hn]
  have hM : Tendsto M atTop atTop :=
    ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop).congr' hMeq
  have hp := linearRayleigh_natural_scale M hMpos hM
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [(tendsto_order.mp hp).1 a ha, eventually_gt_atTop 0] with n hn hnpos
    refine lt_of_lt_of_le hn (measureReal_mono ?_)
    intro W hW
    have hlo : (n : ℝ) ^ (2 / 3 - δ) ≤ linearRayleigh W := by
      rw [Real.rpow_sub (Nat.cast_pos.mpr hnpos)]
      simpa only [M, ite_eq_right (Nat.ne_of_gt hnpos)] using hW.1
    exact hlo.trans (linearRayleigh_le_relaxationTime W hnpos)
  · intro a ha
    exact Filter.Eventually.of_forall (fun _ => lt_of_le_of_lt measureReal_le_one ha)

end CriticalSK
end

end OAI
