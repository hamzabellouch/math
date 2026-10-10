import OAI.NumberTheory.TotientAsymptotic.UnbandedCubeCost
import OAI.NumberTheory.TotientAsymptotic.EnlargementTail
import OAI.NumberTheory.TotientAsymptotic.MassMajorant

namespace OAI

/-! A uniform volume bound for unbanded enlarged prime-prefix grids. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma add_pow_le_exp_ratio {B D : ℝ} (hB : 0 < B) (hD : 0 ≤ D) (N : ℕ) :
    (B+D)^N ≤ Real.exp ((N:ℝ)*D/B)*B^N := by
  have hbase : 1+D/B ≤ Real.exp (D/B) := by
    simpa only [add_comm] using Real.add_one_le_exp (D/B)
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1+D/B) hbase N
  have he : B+D=(1+D/B)*B := by field_simp
  rw [he,mul_pow]
  apply (mul_le_mul_of_nonneg_right hpow (pow_nonneg hB.le N)).trans_eq
  rw [← Real.exp_nat_mul]
  congr 2
  ring

theorem unbanded_grid_uniform_volume : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ x : ℝ in atTop, ∀ H : ℕ, H < m x →
    ∀ K : Finset (Fin (m x-H) → ℕ),
      (∀ b ∈ K, ∃ u ∈ unitGridCell b,
        u ∈ enlargedSimplex (m x-H) (B x)
          (1+simplexBoxError 0 (m x))
          (fun i => 1+simplexBoxError 0 (m x-(i.val+1)))) →
      (K.card:ℝ) ≤ C*G x (m x-H) := by
  obtain ⟨A,hA,hcost⟩ := prefixCubeCost_relative_bound
  let E := Real.exp (simplexBoxTail 0 0)
  refine ⟨E*Real.exp A, mul_pos (Real.exp_pos _) (Real.exp_pos _), ?_⟩
  filter_upwards [hcost,B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hB
  intro H hH K hK
  let β : ℕ → ℝ := fun r => 1+simplexBoxError 0 (m x-r)
  have hβ (r) : 1 ≤ β r := by
    dsimp [β]
    linarith [simplexBoxError_nonneg (by norm_num : (0:ℝ) ≤ 0) (m x-r)]
  let κ : Fin (m x-H) → ℝ := enlargementScale β
  have hκ (i) : 1 ≤ κ i := (hβ 0).trans (enlargementScale_top hβ i)
  have hvol := unbanded_grid_volume_bound (Nat.sub_pos_of_lt hH) (B x) (β 0)
    (fun i => β (i.val+1)) κ K hB.le (zero_lt_one.trans_le (hβ 0))
    (fun i => zero_lt_one.trans_le (hβ (i.val+1))) hκ
    (enlargementScale_top hβ) (enlargementScale_step hβ) hK
  have hj : (∏ i, κ i) ≤ E := by
    have hh := enlargement_jacobian_bound (N:=m x-H) hβ
    have ht := reverse_perturbation_sum_le (Nat.le_of_lt hH)
      (simplexBoxError 0) (simplexBoxError_nonneg (by norm_num))
      (summable_simplexBoxError_weighted 0)
    have ht0 : (∑' n : ℕ, ((H+n:ℕ):ℝ)*simplexBoxError 0 (H+n)) ≤
        ∑' n : ℕ, (n:ℝ)*simplexBoxError 0 n := by
      have hs := summable_simplexBoxError_weighted 0
      have he := hs.sum_add_tsum_nat_add H
      have hn : 0 ≤ ∑ n ∈ Finset.range H, (n:ℝ)*simplexBoxError 0 n :=
        Finset.sum_nonneg (fun n _ => mul_nonneg (Nat.cast_nonneg n)
          (simplexBoxError_nonneg (by norm_num) n))
      have hh : (∑' n : ℕ, ((n+H:ℕ):ℝ)*simplexBoxError 0 (n+H)) ≤
          ∑' n : ℕ, (n:ℝ)*simplexBoxError 0 n := by linarith only [he,hn]
      simpa only [Nat.add_comm] using hh
    apply hh.trans
    apply Real.exp_le_exp.mpr
    simp only [β,add_sub_cancel_left]
    rw [simplexBoxTail_eq_tsum]
    simpa only [Nat.zero_add] using ht.trans ht0
  have hratio : ((m x-H:ℕ):ℝ)*prefixCubeCost (m x-H)/B x ≤ A := by
    exact (hx _ (Nat.sub_le _ _)).trans
      (mul_le_of_le_one_right hA.le (pow_le_one₀ rho_pos.le rho_lt_one.le))
  have hden : 0 < ((m x-H).factorial:ℝ)*∏ i : Fin (m x-H), g (i.val+1) :=
    mul_pos (by positivity) (Finset.prod_pos (fun i _ => g_pos _))
  calc
    _ ≤ (∏ i,κ i)*((B x+prefixCubeCost (m x-H))^(m x-H)/
        (((m x-H).factorial:ℝ)*∏ i : Fin (m x-H), g (i.val+1))) := hvol
    _ ≤ E*(Real.exp A*(B x)^(m x-H)/
        (((m x-H).factorial:ℝ)*∏ i : Fin (m x-H), g (i.val+1))) := by
      apply mul_le_mul hj _
        (div_nonneg (pow_nonneg (add_nonneg hB.le (prefixCubeCost_nonneg _)) _) hden.le)
        (Real.exp_pos _).le
      apply div_le_div_of_nonneg_right _ hden.le
      exact (add_pow_le_exp_ratio hB (prefixCubeCost_nonneg _) _).trans
        (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hratio) (pow_nonneg hB.le _))
    _ = E*Real.exp A*G x (m x-H) := by
      rw [G,prod_fin_shifted (m x-H) g]
      ring

end TotientAsymptotic

end

end OAI
