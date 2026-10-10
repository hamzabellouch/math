import OAI.Probability.FreeIsing.Posterior.Fields
import OAI.Probability.FreeIsing.Trees.FinitePathGibbs

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.PathPosterior

def interaction (beta : ℝ) (n : ℕ) (s : Fin (n + 1) → IsingSpin) : ℝ :=
  beta * ∑ i : Fin n, spinSign (s i.castSucc) * spinSign (s i.succ)

def spin (n : ℕ) (s : Fin (n + 1) → IsingSpin) (v : Fin (n + 1)) : ℝ :=
  spinSign (s v)

def childFields {n : ℕ} (y : Fin (n + 1) → ℝ) (i : ℕ) : ℝ :=
  if hi : i < n then y ⟨i + 1, Nat.succ_lt_succ hi⟩ else 0

@[simp] theorem childFields_fin {n : ℕ} (y : Fin (n + 1) → ℝ) (i : Fin n) :
    childFields y i = y i.succ := by
  simp only [childFields, dite_eq_left i.isLt]
  rfl

theorem energy_eq_fieldEnergy (beta : ℝ) (n : ℕ)
    (y : Fin (n + 1) → ℝ) (s : Fin (n + 1) → IsingSpin) :
    FinitePathGibbs.energy beta (y 0) (childFields y) n s =
      FinitePosterior.fieldEnergy (interaction beta n) (spin n) y s := by
  unfold FinitePathGibbs.energy FinitePosterior.fieldEnergy interaction spin
  rw [Fin.sum_univ_succ]
  simp only [childFields_fin, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  ring

theorem mean_eq_fieldMean (beta : ℝ) (n : ℕ) (y : Fin (n + 1) → ℝ)
    (f : (Fin (n + 1) → IsingSpin) → ℝ) :
    FinitePathGibbs.mean beta (y 0) (childFields y) n f =
      FinitePosterior.fieldMean (interaction beta n) (spin n) f y := by
  unfold FinitePathGibbs.mean FinitePosterior.fieldMean
  simp_rw [FinitePathGibbs.mass_eq_exp_energy]
  rw [FinitePathGibbs.partition_eq_sum_exp]
  simp_rw [energy_eq_fieldEnergy]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  apply congrArg (fun a => a / ∑ s, Real.exp
    (FinitePosterior.fieldEnergy (interaction beta n) (spin n) y s))
  apply Finset.sum_congr rfl
  intro s _
  ring

def rootMean (beta : ℝ) (n : ℕ) (y : Fin (n + 1) → ℝ) : ℝ :=
  FinitePosterior.fieldMean (interaction beta n) (spin n) (fun s => spinSign (s 0)) y

def rootField (beta : ℝ) (n : ℕ) (y : Fin (n + 1) → ℝ) : ℝ :=
  Real.artanh (rootMean beta n y)

theorem rootMean_eq_tanh (beta : ℝ) (n : ℕ) (y : Fin (n + 1) → ℝ) :
    rootMean beta n y =
      Real.tanh (FinitePathGibbs.rootField beta (y 0) (childFields y) n) := by
  rw [rootMean, ← mean_eq_fieldMean, FinitePathGibbs.mean_first_eq_tanh]

theorem rootMean_mem_Ioo (beta : ℝ) (n : ℕ) (y : Fin (n + 1) → ℝ) :
    rootMean beta n y ∈ Set.Ioo (-1 : ℝ) 1 := by
  rw [rootMean_eq_tanh]
  exact ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩

theorem rootField_eq (beta : ℝ) (n : ℕ) (y : Fin (n + 1) → ℝ) :
    rootField beta n y = FinitePathGibbs.rootField beta (y 0) (childFields y) n := by
  rw [rootField, rootMean_eq_tanh, Real.artanh_tanh]

theorem endpoint_covariance (beta : ℝ) (n : ℕ) (y : Fin (n + 1) → ℝ) :
    FinitePosterior.fieldMean (interaction beta n) (spin n)
      (fun s => spinSign (s 0) * spinSign (s (Fin.last n))) y -
      rootMean beta n y * FinitePosterior.fieldMean (interaction beta n) (spin n)
        (fun s => spinSign (s (Fin.last n))) y =
      (1 - rootMean beta n y ^ 2) * Real.tanh beta ^ n *
        (∏ i ∈ Finset.range n,
          responseAttenuation (Real.tanh beta) (FinitePathGibbs.backwardField beta (childFields y) n i)) := by
  simp only [rootMean, ← mean_eq_fieldMean]
  exact FinitePathGibbs.endpointCovariance_eq beta (y 0) (childFields y) n

theorem hasDerivAt_rootMean_endpoint (beta : ℝ) (n : ℕ) (y : Fin (n + 1) → ℝ) :
    HasDerivAt
      (fun t => rootMean beta n (fun v => y v + if v = Fin.last n then t else 0))
      ((1 - rootMean beta n y ^ 2) * Real.tanh beta ^ n *
        (∏ i ∈ Finset.range n,
          responseAttenuation (Real.tanh beta) (FinitePathGibbs.backwardField beta (childFields y) n i))) 0 := by
  let : Nonempty (Fin (n + 1) → IsingSpin) := ⟨fun _ => .pos⟩
  have hd := FinitePosterior.hasDerivAt_fieldMean_coordinate
    (interaction beta n) (spin n) (fun s => spinSign (s 0)) y (Fin.last n)
  change HasDerivAt _
    (FinitePosterior.fieldMean (interaction beta n) (spin n)
        (fun s => spinSign (s 0) * spinSign (s (Fin.last n))) y -
      rootMean beta n y * FinitePosterior.fieldMean (interaction beta n) (spin n)
        (fun s => spinSign (s (Fin.last n))) y) 0 at hd
  rw [endpoint_covariance] at hd
  exact hd

theorem hasDerivAt_rootField_endpoint (beta : ℝ) (n : ℕ) (y : Fin (n + 1) → ℝ) :
    HasDerivAt
      (fun t => rootField beta n (fun v => y v + if v = Fin.last n then t else 0))
      (Real.tanh beta ^ n *
        (∏ i ∈ Finset.range n,
          responseAttenuation (Real.tanh beta) (FinitePathGibbs.backwardField beta (childFields y) n i))) 0 := by
  have hm := rootMean_mem_Ioo beta n y
  have hv : 1 - rootMean beta n y ^ 2 ≠ 0 := by
    have hs : rootMean beta n y ^ 2 < 1 := by
      rw [rootMean_eq_tanh]
      exact Real.tanh_sq_lt_one _
    linarith
  have hbase : (fun v => y v + if v = Fin.last n then (0 : ℝ) else 0) = y := by
    funext v
    simp
  have ha : HasDerivAt Real.artanh (1 / (1 - rootMean beta n y ^ 2))
      (rootMean beta n (fun v => y v + if v = Fin.last n then (0 : ℝ) else 0)) := by
    simpa only [hbase] using hasDerivAt_artanh_interval hm
  have hd := ha.comp 0 (hasDerivAt_rootMean_endpoint beta n y)
  simpa only [hbase, Function.comp_def, rootField, one_div, mul_assoc,
    inv_mul_cancel_left₀ hv] using hd

theorem hasDerivAt_rootField_endpoint_at (beta : ℝ) (n : ℕ)
    (y : Fin (n + 1) → ℝ) (t : ℝ) :
    HasDerivAt
      (fun s => rootField beta n (fun v => y v + if v = Fin.last n then s else 0))
      (Real.tanh beta ^ n *
        (∏ i ∈ Finset.range n,
          responseAttenuation (Real.tanh beta)
            (FinitePathGibbs.backwardField beta
              (childFields (fun v => y v + if v = Fin.last n then t else 0)) n i))) t := by
  have hd := hasDerivAt_rootField_endpoint beta n
    (fun v => y v + if v = Fin.last n then t else 0)
  have hc := hd.comp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)
  simp only [mul_one, Function.comp_def, id_eq] at hc
  convert! hc using 1
  funext s
  congr 1
  funext v
  split_ifs <;> ring

theorem response_mem_Icc {beta : ℝ} (hbeta : 0 ≤ beta) (n : ℕ)
    (y : Fin (n + 1) → ℝ) :
    (Real.tanh beta ^ n *
      (∏ i ∈ Finset.range n,
        responseAttenuation (Real.tanh beta) (FinitePathGibbs.backwardField beta (childFields y) n i))) ∈
      Set.Icc 0 (Real.tanh beta ^ n) := by
  have hθ := tanh_nonneg_of_beta_nonneg hbeta
  have hs := (Real.tanh_sq_lt_one beta).le
  have ha0 : 0 ≤ ∏ i ∈ Finset.range n,
      responseAttenuation (Real.tanh beta) (FinitePathGibbs.backwardField beta (childFields y) n i) :=
    Finset.prod_nonneg fun i _ => (responseAttenuation_pos hs _).le
  have ha1 : (∏ i ∈ Finset.range n,
      responseAttenuation (Real.tanh beta) (FinitePathGibbs.backwardField beta (childFields y) n i)) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => (responseAttenuation_pos hs _).le)
      (fun i _ => responseAttenuation_le_one hs _)
  exact ⟨mul_nonneg (pow_nonneg hθ n) ha0,
    mul_le_of_le_one_right (pow_nonneg hθ n) ha1⟩

theorem lipschitzWith_rootField_endpoint {beta : ℝ} (hbeta : 0 ≤ beta)
    (n : ℕ) (y : Fin (n + 1) → ℝ) :
    LipschitzWith ⟨Real.tanh beta ^ n, pow_nonneg (tanh_nonneg_of_beta_nonneg hbeta) n⟩
      (fun t => rootField beta n (fun v => y v + if v = Fin.last n then t else 0)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro t
    exact (hasDerivAt_rootField_endpoint_at beta n y t).differentiableAt
  · intro t
    rw [(hasDerivAt_rootField_endpoint_at beta n y t).deriv]
    have hb := response_mem_Icc hbeta n
      (fun v => y v + if v = Fin.last n then t else 0)
    change |Real.tanh beta ^ n * _| ≤ Real.tanh beta ^ n
    rw [abs_of_nonneg hb.1]
    exact hb.2

end Problem367.PathPosterior

end

end OAI
