import OAI.NumberTheory.TotientAsymptotic.PrefixRelaxation
import OAI.NumberTheory.TotientAsymptotic.CofactorShellDecay

namespace OAI

/-! The sum of all prefix perturbations, uniformly in dimension and phase. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def exponentialShellTail (H : ℕ) : ℝ :=
  polynomialGeometricTail 1 (Real.exp (-1/40)) H

lemma exp_shell_power (h : ℕ) :
    (Real.exp (-1/40))^h = Real.exp (-(h : ℝ)/40) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

lemma exponentialShellTail_nonneg (H : ℕ) : 0 ≤ exponentialShellTail H :=
  polynomialGeometricTail_nonneg 1 (Real.exp_pos _).le H

lemma exponentialShell_summable : Summable (fun h : ℕ => (h : ℝ)*Real.exp (-(h : ℝ)/40)) := by
  have hr : ‖Real.exp (-1/40)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    norm_num
  simpa only [pow_one, exp_shell_power] using
    summable_pow_mul_geometric_of_norm_lt_one 1 hr

lemma exponentialShellTail_term {H h : ℕ} (hh : H ≤ h) :
    (h : ℝ)*Real.exp (-(h : ℝ)/40) ≤ exponentialShellTail H := by
  have hs : Summable (fun n : ℕ => ((H+n : ℕ) : ℝ)*Real.exp (-((H+n : ℕ) : ℝ)/40)) :=
    exponentialShell_summable.comp_injective (fun n m (he : H+n=H+m) => by omega)
  have hb := hs.sum_le_tsum {h-H} (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
  simpa only [Finset.sum_singleton, Nat.add_sub_of_le hh, exponentialShellTail,
    polynomialGeometricTail, pow_one, exp_shell_power] using hb

lemma sum_prefix_exponentialShell {x : ℝ} {H : ℕ} (hHm : H ≤ m x) :
    (∑ i : Fin (R x H), ((m x-(i.val+1) : ℕ) : ℝ)*
      Real.exp (-((m x-(i.val+1) : ℕ) : ℝ)/40)) ≤ exponentialShellTail H := by
  unfold R
  rw [sum_reverse_prefix hHm (fun h => (h : ℝ)*Real.exp (-(h : ℝ)/40))]
  have hs : Summable (fun n : ℕ => ((H+n : ℕ) : ℝ)*Real.exp (-((H+n : ℕ) : ℝ)/40)) :=
    exponentialShell_summable.comp_injective (fun n m (he : H+n=H+m) => by omega)
  simpa only [exponentialShellTail, polynomialGeometricTail, pow_one, exp_shell_power] using
    hs.sum_le_tsum (Finset.range (m x-H))
      (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)

/-- The relaxation of every prefix inequality has a small total weighted
budget. The bound includes index zero and has no dimension factor. -/
theorem uniform_prefix_perturbation_cost (hford : FordRenewalInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ H ≤ m x,
      (R x H : ℝ)/B x*(topPerturbation x+
        ∑ i : Fin (R x H), g (i.val+1)*prefixPerturbation x H i) ≤
        C*exponentialShellTail H := by
  obtain ⟨K, hK, hslice⟩ := uniform_slice_bound hford
  let A := (11/100000 : ℝ)*(lam/rho)
  have hA : 0 < A := mul_pos (by norm_num) (div_pos lam_pos rho_pos)
  refine ⟨1+K*A, by positivity, ?_⟩
  filter_upwards [hslice, theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hθ hB
  intro H hHm
  have hRm : (R x H : ℝ) ≤ m x := by exact_mod_cast Nat.sub_le (m x) H
  have htop : (R x H : ℝ)/B x*topPerturbation x ≤ exponentialShellTail H := by
    have he : (R x H : ℝ)/B x*topPerturbation x =
        (1/10000 : ℝ)*(R x H : ℝ)*Real.exp (-(m x : ℝ)/40) := by
      simp only [topPerturbation, xi, Nat.sub_zero]
      field_simp
      ring
    rw [he]
    apply le_trans _ (exponentialShellTail_term hHm)
    have hR0 : (0 : ℝ) ≤ R x H := Nat.cast_nonneg _
    have hfac : (1/10000 : ℝ)*(R x H : ℝ) ≤ m x := by linarith
    exact mul_le_mul_of_nonneg_right hfac (Real.exp_pos _).le
  have hterm (i : Fin (R x H)) :
      (R x H : ℝ)/B x*(g (i.val+1)*prefixPerturbation x H i) ≤
        K*A*(((m x-(i.val+1) : ℕ) : ℝ)*Real.exp (-((m x-(i.val+1) : ℕ) : ℝ)/40)) := by
    let h := m x-(i.val+1)
    have hi : i.val+1 ≤ m x := by have := i.isLt; unfold R at *; omega
    have hs : (R x H : ℝ)*g (i.val+1)/B x ≤ K*rho^h :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hRm (g_pos _).le) hB.le).trans
        (hx (i.val+1) hi)
    have he : prefixPerturbation x H i =
        (11/100000 : ℝ)*alpha (theta x)*(h : ℝ)*(rho^h)⁻¹*Real.exp (-(h : ℝ)/40) := by
      dsimp [prefixPerturbation, xi, bandScale, h]
      ring
    rw [he]
    calc
      _ = ((R x H : ℝ)*g (i.val+1)/B x)*
          ((11/100000 : ℝ)*alpha (theta x)*h*(rho^h)⁻¹*Real.exp (-(h : ℝ)/40)) := by ring
      _ ≤ (K*rho^h)*((11/100000 : ℝ)*alpha (theta x)*h*(rho^h)⁻¹*Real.exp (-(h : ℝ)/40)) := by
        apply mul_le_mul_of_nonneg_right hs
        have := alpha_pos (theta x)
        have := pow_pos rho_pos h
        positivity
      _ = K*((11/100000 : ℝ)*alpha (theta x))*((h : ℝ)*Real.exp (-(h : ℝ)/40)) := by
        field_simp [rho_pos.ne']
      _ ≤ K*A*((h : ℝ)*Real.exp (-(h : ℝ)/40)) := by
        apply mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (alpha_le _ hθ) (by norm_num)) hK.le)
          (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
  calc
    _ = (R x H : ℝ)/B x*topPerturbation x+
        ∑ i : Fin (R x H), (R x H : ℝ)/B x*(g (i.val+1)*prefixPerturbation x H i) := by
      rw [mul_add, Finset.mul_sum]
    _ ≤ exponentialShellTail H +
        ∑ i : Fin (R x H), K*A*(((m x-(i.val+1) : ℕ) : ℝ)*
          Real.exp (-((m x-(i.val+1) : ℕ) : ℝ)/40)) :=
      add_le_add htop (Finset.sum_le_sum (fun i _ => hterm i))
    _ ≤ exponentialShellTail H+K*A*exponentialShellTail H := by
      rw [← Finset.mul_sum]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_prefix_exponentialShell hHm)
        (mul_nonneg hK.le hA.le))
    _ = _ := by ring

lemma cofactor_exponentialShellTail_tendsto (C : ℝ) :
    Tendsto (fun H => Real.exp (C*cofactorScale H)*exponentialShellTail H) atTop (nhds 0) := by
  apply cofactor_polynomialGeometricTail_tendsto C 1 (Real.exp_pos _).le
  rw [Real.exp_lt_one_iff]
  norm_num

end TotientAsymptotic

end

end OAI
