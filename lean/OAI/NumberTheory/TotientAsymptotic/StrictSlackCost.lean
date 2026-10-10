import OAI.NumberTheory.TotientAsymptotic.NormalizedShell

namespace OAI

/-! The additional polynomial-width shell needed to discard failures of strict slack. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def inverseSquareSum : ℝ := ∑' n : ℕ, 1/((n+1 : ℕ) : ℝ)^2

lemma inverseSquareSum_nonneg : 0 ≤ inverseSquareSum :=
  tsum_nonneg (fun _ => by positivity)

lemma inverseSquare_summable : Summable (fun n : ℕ => 1/((n+1 : ℕ) : ℝ)^2) := by
  exact (summable_nat_add_iff 1).mpr ((Real.summable_one_div_nat_pow).mpr (by norm_num))

lemma inverseCube_prefix_sum {H m : ℕ} (hH : 1 ≤ H) (hHm : H ≤ m) :
    (∑ i : Fin (m-H), 1/((m-(i.val+1) : ℕ) : ℝ)^3) ≤ inverseSquareSum/H := by
  rw [sum_reverse_prefix hHm (fun h => 1/(h : ℝ)^3)]
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  calc
    _ ≤ ∑ j ∈ Finset.range (m-H), (1/(H : ℝ))*(1/((j+1 : ℕ) : ℝ)^2) := by
      apply Finset.sum_le_sum
      intro j _
      have ha : (0 : ℝ) < (H+j : ℕ) := by exact_mod_cast (show 0 < H+j by omega)
      have hb : (0 : ℝ) < (j+1 : ℕ) := by positivity
      have h1 : (H : ℝ) ≤ (H+j : ℕ) := by exact_mod_cast (Nat.le_add_right H j)
      have h2 : ((j+1 : ℕ) : ℝ) ≤ (H+j : ℕ) := by exact_mod_cast (show j+1 ≤ H+j by omega)
      have hsq := pow_le_pow_left₀ hb.le h2 2
      have hprod := mul_le_mul h1 hsq (sq_nonneg _) ha.le
      have hden : (H : ℝ)*((j+1 : ℕ) : ℝ)^2 ≤ ((H+j : ℕ) : ℝ)^3 := by nlinarith
      calc
        _ ≤ 1/((H : ℝ)*((j+1 : ℕ) : ℝ)^2) :=
          one_div_le_one_div_of_le (mul_pos hH0 (sq_pos_of_pos hb)) hden
        _ = _ := by field_simp
    _ = (1/(H : ℝ))*∑ j ∈ Finset.range (m-H), 1/((j+1 : ℕ) : ℝ)^2 := by rw [Finset.mul_sum]
    _ ≤ (1/(H : ℝ))*inverseSquareSum :=
      mul_le_mul_of_nonneg_left (inverseSquare_summable.sum_le_tsum _ (fun _ _ => by positivity))
        (by positivity)
    _ = _ := by ring

/-- The strict-slack width, unlike the prime-grid width, only decays
polynomially. Its total slice cost is still small enough for all cofactors. -/
theorem uniform_strict_slack_cost (hren : FordRenewalInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ H N : ℕ,
      1 ≤ H → H ≤ m x → N ≤ m x →
      (N : ℝ)/B x*((B x)/(m x : ℝ)^4+
        ∑ i : Fin (R x H), g (i.val+1)*
          ((11/10 : ℝ)*bandScale x (i.val+1)/((m x-(i.val+1) : ℕ) : ℝ)^4)) ≤ C/H := by
  obtain ⟨A,hA,hslice⟩ := uniform_slice_bound hren
  have hlam := lam_pos
  have hrho := rho_pos
  let C := 1+(11/10 : ℝ)*A*(lam/rho)*inverseSquareSum
  have hC : 0 < C := by
    have := inverseSquareSum_nonneg
    dsimp [C]
    positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [hslice, theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hx htheta hB
  intro H N hH hHm hN
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hm0 : (0 : ℝ) < m x := by exact_mod_cast (show 0 < m x by omega)
  have htop : (N : ℝ)/B x*(B x/(m x : ℝ)^4) ≤ 1/(H : ℝ) := by
    have hn : (N : ℝ) ≤ m x := by exact_mod_cast hN
    have hmH : (H : ℝ) ≤ m x := by exact_mod_cast hHm
    have hm1 : (1 : ℝ) ≤ m x := by exact_mod_cast (show 1 ≤ m x by omega)
    have hm2 : (m x : ℝ)^2 ≤ (m x : ℝ)^4 := by nlinarith [sq_nonneg ((m x : ℝ)^2-1)]
    have hcross : (N : ℝ)*H ≤ (m x : ℝ)^4 :=
      (mul_le_mul hn hmH (Nat.cast_nonneg _) hm0.le).trans (by simpa [sq] using hm2)
    rw [show (N : ℝ)/B x*(B x/(m x : ℝ)^4) = (N : ℝ)/(m x : ℝ)^4 by field_simp]
    exact (div_le_div_iff₀ (pow_pos hm0 _) hH0).mpr (by simpa using hcross)
  have hrow (i : Fin (R x H)) :
      (N : ℝ)/B x*(g (i.val+1)*
        ((11/10 : ℝ)*bandScale x (i.val+1)/((m x-(i.val+1) : ℕ) : ℝ)^4)) ≤
      ((11/10 : ℝ)*A*(lam/rho))*(1/((m x-(i.val+1) : ℕ) : ℝ)^3) := by
    have hi := i.isLt
    have him : i.val+1 < m x := by unfold R at hi; omega
    have hp : (0 : ℝ)<(m x-(i.val+1) : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt him
    have hs : (N : ℝ)*g (i.val+1)/B x ≤ A*rho^(m x-(i.val+1)) :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hN)
        (g_pos _).le) hB.le).trans (hx _ him.le)
    calc
      _ = ((N : ℝ)*g (i.val+1)/B x)*
        ((11/10 : ℝ)*bandScale x (i.val+1)/((m x-(i.val+1) : ℕ) : ℝ)^4) := by ring
      _ ≤ (A*rho^(m x-(i.val+1)))*
        ((11/10 : ℝ)*bandScale x (i.val+1)/((m x-(i.val+1) : ℕ) : ℝ)^4) :=
        mul_le_mul_of_nonneg_right hs (div_nonneg
          (mul_nonneg (by norm_num) (bandScale_nonneg _ _)) (by positivity))
      _ = ((11/10 : ℝ)*A*alpha (theta x))*(1/((m x-(i.val+1) : ℕ) : ℝ)^3) := by
        unfold bandScale
        field_simp [(pow_pos rho_pos _).ne',hp.ne']
      _ ≤ _ := by
        gcongr
        exact alpha_le _ htheta
  rw [mul_add, Finset.mul_sum]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
  have hinv := inverseCube_prefix_sum hH hHm
  have hnn : 0 ≤ (11/10 : ℝ)*A*(lam/rho) := by positivity
  have hh := mul_le_mul_of_nonneg_left hinv hnn
  rw [Finset.mul_sum] at hh
  apply (add_le_add htop (hsum.trans hh)).trans_eq
  dsimp [C]
  ring

lemma cofactor_inverse_cutoff_tendsto (K : ℝ) :
    Tendsto (fun H : ℕ => Real.exp (K*cofactorScale H)/(H : ℝ)) atTop (nhds 0) := by
  apply (cofactor_envelope_power_decay K (by norm_num : (0 : ℝ)<1)).congr'
  filter_upwards [eventually_ge_atTop 1] with H hH
  have hH0 : (0 : ℝ)<H := by exact_mod_cast hH
  rw [one_mul, Real.exp_sub, Real.exp_log hH0]

end TotientAsymptotic

end

end OAI
