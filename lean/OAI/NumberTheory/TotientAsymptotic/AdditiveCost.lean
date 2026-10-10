import OAI.NumberTheory.TotientAsymptotic.AdditiveEnclosure

namespace OAI

/-! Summation of the additive box errors with their exact slice coefficients. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def boxErrorTail (H : ℕ) : ℝ := exponentialShellTail H+quadraticShellTail H

lemma quadraticShellTail_nonneg (H : ℕ) : 0 ≤ quadraticShellTail H :=
  tsum_nonneg (fun _ => mul_nonneg (sq_nonneg _) (pow_nonneg rho_pos.le _))

lemma boxErrorTail_nonneg (H : ℕ) : 0 ≤ boxErrorTail H :=
  add_nonneg (exponentialShellTail_nonneg H) (quadraticShellTail_nonneg H)

lemma boxErrorTail_tendsto : Tendsto boxErrorTail atTop (nhds 0) := by
  have he : Tendsto exponentialShellTail atTop (nhds 0) :=
    polynomialGeometricTail_tendsto 1 (Real.exp (-1/40))
  change Tendsto (fun H => exponentialShellTail H+quadraticShellTail H) atTop (nhds 0)
  simpa only [add_zero] using he.add quadraticShellTail_tendsto

lemma cofactor_boxErrorTail_tendsto (K : ℝ) :
    Tendsto (fun H => Real.exp (K*cofactorScale H)*boxErrorTail H) atTop (nhds 0) := by
  simpa only [boxErrorTail, mul_add, add_zero] using
    (cofactor_exponentialShellTail_tendsto K).add (cofactor_quadraticShellTail_tendsto K)

lemma quadraticShellTail_term {H h : ℕ} (hh : H ≤ h) :
    (h : ℝ)^2*rho^h ≤ quadraticShellTail H := by
  have hs0 : Summable (fun n : ℕ => (n : ℝ)^2*rho^n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2
      (by simpa only [Real.norm_eq_abs, abs_of_pos rho_pos] using rho_lt_one)
  have hs : Summable (fun n : ℕ => ((H+n : ℕ) : ℝ)^2*rho^(H+n)) :=
    hs0.comp_injective (fun _ _ he => Nat.add_left_cancel he)
  have hb := hs.sum_le_tsum {h-H} (fun _ _ => mul_nonneg (sq_nonneg _) (pow_nonneg rho_pos.le _))
  simpa only [Finset.sum_singleton, Nat.add_sub_of_le hh, quadraticShellTail] using hb

lemma boxSlackError_eq {x : ℝ} {H : ℕ} (i : Fin (R x H)) :
    boxSlackError x (i.val+1) = prefixPerturbation x H i+
      4*((m x-(i.val+1) : ℕ) : ℝ)^2 := rfl

/-- The total additive error has a tail bound with no dimension factor. -/
theorem uniform_box_error_cost (hren : FordRenewalInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ H ≤ m x,
      (R x H : ℝ)/B x*(boxTopError x+
        ∑ i : Fin (R x H), g (i.val+1)*boxSlackError x (i.val+1)) ≤ C*boxErrorTail H := by
  obtain ⟨A, hA, hexp⟩ := uniform_prefix_perturbation_cost hren
  obtain ⟨D, hD, hquad⟩ := prefix_cube_shell_cost hren
  have hlam := lam_pos
  refine ⟨A+4*D+8/lam, by positivity, ?_⟩
  filter_upwards [hexp, hquad, inverse_scale_bound,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hy hscale hB
  intro H hHm
  have hp := mul_pos hB (pow_pos rho_pos (m x))
  have hmB : (m x : ℝ)/B x ≤ (2/lam)*rho^(m x) := by
    have hh := (div_le_iff₀ hp).mp hscale
    apply (div_le_iff₀ hB).mpr
    nlinarith [hh]
  have htop : (R x H : ℝ)/B x*(m x : ℝ)^2 ≤ (2/lam)*quadraticShellTail H := by
    have hRm : (R x H : ℝ) ≤ m x := by exact_mod_cast Nat.sub_le (m x) H
    calc
      _ ≤ ((m x : ℝ)/B x)*(m x : ℝ)^2 := by gcongr
      _ ≤ ((2/lam)*rho^(m x))*(m x : ℝ)^2 :=
        mul_le_mul_of_nonneg_right hmB (sq_nonneg _)
      _ = (2/lam)*((m x : ℝ)^2*rho^(m x)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (quadraticShellTail_term hHm) (by positivity)
  have heq : (R x H : ℝ)/B x*(boxTopError x+
      ∑ i : Fin (R x H), g (i.val+1)*boxSlackError x (i.val+1)) =
      (R x H : ℝ)/B x*(topPerturbation x+
        ∑ i : Fin (R x H), g (i.val+1)*prefixPerturbation x H i)+
      4*((R x H : ℝ)/B x*(∑ i : Fin (R x H),
        g (i.val+1)*((m x-(i.val+1) : ℕ) : ℝ)^2))+
      4*((R x H : ℝ)/B x*(m x : ℝ)^2) := by
    simp only [boxTopError, boxSlackError_eq, mul_add, Finset.sum_add_distrib]
    simp_rw [show ∀ i : Fin (R x H), g (i.val+1)*(4*((m x-(i.val+1) : ℕ) : ℝ)^2) =
      4*(g (i.val+1)*((m x-(i.val+1) : ℕ) : ℝ)^2) by intro i; ring]
    rw [← Finset.mul_sum]
    ring
  rw [heq]
  have h1 := hx H hHm
  have h2 := hy H hHm
  have he0 := exponentialShellTail_nonneg H
  have hq0 := quadraticShellTail_nonneg H
  have ht := mul_le_mul_of_nonneg_left htop (by norm_num : (0 : ℝ)≤4)
  have he8 : 4*((2/lam)*quadraticShellTail H) = (8/lam)*quadraticShellTail H := by ring
  rw [he8] at ht
  have h8 : 0 ≤ 8/lam := by positivity
  dsimp [boxErrorTail]
  nlinarith [mul_nonneg h8 he0, mul_nonneg hA.le hq0,
    mul_nonneg hD.le he0]


/-- The same retained-coordinate cost with any larger ambient dimension
bounded by `m`; the harmless factor two uses `m ≥ 2H`. -/
theorem ambient_box_error_cost (hren : FordRenewalInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ H N : ℕ, 2*H ≤ m x → N ≤ m x →
      (N : ℝ)/B x*(boxTopError x+
        ∑ i : Fin (R x H), g (i.val+1)*boxSlackError x (i.val+1)) ≤ 2*C*boxErrorTail H := by
  obtain ⟨C, hC, hcost⟩ := uniform_box_error_cost hren
  refine ⟨C, hC, ?_⟩
  filter_upwards [hcost, B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hB
  intro H N hH hN
  have hnr : (N : ℝ) ≤ 2*(R x H : ℝ) := by
    have hh : N ≤ 2*R x H := by unfold R; omega
    exact_mod_cast hh
  have hE : 0 ≤ boxTopError x+∑ i : Fin (R x H), g (i.val+1)*boxSlackError x (i.val+1) :=
    add_nonneg (boxTopError_nonneg hB.le) (Finset.sum_nonneg
      (fun i _ => mul_nonneg (g_pos _).le (boxSlackError_nonneg _ _)))
  calc
    _ ≤ (2*(R x H : ℝ))/B x*(boxTopError x+
        ∑ i : Fin (R x H), g (i.val+1)*boxSlackError x (i.val+1)) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hnr hB.le) hE
    _ = 2*((R x H : ℝ)/B x*(boxTopError x+
        ∑ i : Fin (R x H), g (i.val+1)*boxSlackError x (i.val+1))) := by ring
    _ ≤ 2*(C*boxErrorTail H) :=
      mul_le_mul_of_nonneg_left (hx H (by omega)) (by norm_num)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
