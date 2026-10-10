import OAI.NumberTheory.TotientAsymptotic.UniformPrefactor
import OAI.NumberTheory.TotientAsymptotic.SimplexShell

namespace OAI

/-! Simultaneous summation of the unit-box slack-shell costs. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma uniform_slice_bound (hford : FordRenewalInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ i ≤ m x,
      (m x : ℝ)*g i/B x ≤ C*rho^(m x-i) := by
  obtain ⟨_, K, hK, hg⟩ := normalizedRenewal_properties hford
  let C := 2*(K+1)/lam
  refine ⟨C, div_pos (mul_pos (by norm_num) (by linarith)) lam_pos, ?_⟩
  filter_upwards [inverse_scale_bound,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hB
  intro i hi
  have hgn : g i*rho^i ≤ K+1 := by
    have hh := hg i
    change |g i*rho^i| ≤ K at hh
    exact (le_abs_self _).trans (hh.trans (by linarith))
  have hg' : g i ≤ (K+1)/rho^i := (le_div_iff₀ (pow_pos rho_pos _)).mpr hgn
  have hpow : rho^i*rho^(m x-i) = rho^(m x) := by
    rw [← pow_add, Nat.add_sub_of_le hi]
  calc
    _ ≤ (m x : ℝ)*((K+1)/rho^i)/B x :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hg' (Nat.cast_nonneg _)) hB.le
    _ = ((K+1)*((m x : ℝ)/(B x*rho^(m x))))*rho^(m x-i) := by
      rw [← hpow]
      field_simp [rho_pos.ne']
    _ ≤ ((K+1)*(2/lam))*rho^(m x-i) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx (by linarith))
        (pow_nonneg rho_pos.le _)
    _ = C*rho^(m x-i) := by dsimp [C]; ring

lemma sum_reverse_prefix {m H : ℕ} (hHm : H ≤ m) (f : ℕ → ℝ) :
    (∑ i : Fin (m-H), f (m-(i.val+1))) =
      ∑ j ∈ Finset.range (m-H), f (H+j) := by
  apply Finset.sum_bij (fun i _ => m-H-1-i.val)
  · intro i _
    exact Finset.mem_range.mpr (by omega)
  · intro i _ j _ hij
    apply Fin.ext
    have := i.isLt
    have := j.isLt
    omega
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    refine ⟨⟨m-H-1-j, by omega⟩, Finset.mem_univ _, ?_⟩
    simp only
    omega
  · intro i _
    congr 1
    have := i.isLt
    omega

def quadraticShellTail (H : ℕ) : ℝ :=
  ∑' n : ℕ, ((H+n : ℕ) : ℝ)^2*rho^(H+n)

lemma quadraticShellTail_tendsto : Tendsto quadraticShellTail atTop (nhds 0) := by
  change Tendsto (fun H => ∑' n : ℕ, ((H+n : ℕ) : ℝ)^2*rho^(H+n)) atTop (nhds 0)
  simpa only [Nat.add_comm] using
    (_root_.tendsto_sum_nat_add (fun n : ℕ => (n : ℝ)^2*rho^n))

/-- Summing the slice bounds for all unit-box boundary errors has a vanishing
tail uniform in the moving dimension and phase. -/
theorem prefix_cube_shell_cost (hford : FordRenewalInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ H ≤ m x,
      (R x H : ℝ)/B x * (∑ i : Fin (R x H),
        g (i.val+1)*((m x-(i.val+1) : ℕ) : ℝ)^2) ≤ C*quadraticShellTail H := by
  obtain ⟨C, hC, hslice⟩ := uniform_slice_bound hford
  refine ⟨C, hC, ?_⟩
  filter_upwards [hslice, B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))]
    with x hx hB
  intro H hHm
  have hg : Summable (fun n : ℕ => (n : ℝ)^2*rho^n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2
      (by simpa only [Real.norm_eq_abs, abs_of_pos rho_pos] using rho_lt_one)
  have hterm (i : Fin (R x H)) :
      (R x H : ℝ)/B x*(g (i.val+1)*((m x-(i.val+1) : ℕ) : ℝ)^2) ≤
        C*(((m x-(i.val+1) : ℕ) : ℝ)^2*rho^(m x-(i.val+1))) := by
    have hi : i.val+1 ≤ m x := by have := i.isLt; unfold R at *; omega
    have hRm : (R x H : ℝ) ≤ m x := by exact_mod_cast Nat.sub_le (m x) H
    have hs : (R x H : ℝ)*g (i.val+1)/B x ≤ C*rho^(m x-(i.val+1)) :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hRm (g_pos _).le) hB.le).trans
        (hx (i.val+1) hi)
    calc
      _ = ((R x H : ℝ)*g (i.val+1)/B x)*((m x-(i.val+1) : ℕ) : ℝ)^2 := by ring
      _ ≤ (C*rho^(m x-(i.val+1)))*((m x-(i.val+1) : ℕ) : ℝ)^2 :=
        mul_le_mul_of_nonneg_right hs (sq_nonneg _)
      _ = _ := by ring
  rw [Finset.mul_sum]
  apply (Finset.sum_le_sum (fun i _ => hterm i)).trans
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ hC.le
  change (∑ i : Fin (m x-H), ((m x-(i.val+1) : ℕ) : ℝ)^2*rho^(m x-(i.val+1))) ≤
    ∑' n : ℕ, ((H+n : ℕ) : ℝ)^2*rho^(H+n)
  rw [sum_reverse_prefix hHm (fun n => (n : ℝ)^2*rho^n)]
  exact (hg.comp_injective (fun _ _ h => by omega)).sum_le_tsum _
    (fun _ _ => mul_nonneg (sq_nonneg _) (pow_nonneg rho_pos.le _))

end TotientAsymptotic

end

end OAI
