import OAI.NumberTheory.TotientAsymptotic.UnbandedTerminalCube
import OAI.NumberTheory.TotientAsymptotic.FixedTerminalRate
import OAI.NumberTheory.TotientAsymptotic.UnbandedGridVolume

namespace OAI

/-! Exponentially decaying prime-prefix grid counts a fixed distance from the natural dimension. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem fixed_terminal_grid_bound (H : ℕ) : ∃ C c : ℝ,0 < C ∧ 0 < c ∧
    ∀ᶠ x : ℝ in atTop,∀ N : ℕ,N+1+H=m x → ∀ t : ℝ,0 ≤ t →
    ∀ K : Finset (Fin (N+1) → ℕ),
    (∀ b ∈ K,∃ u ∈ unitGridCell b,
      u ∈ enlargedSimplex (N+1) (B x) (1+simplexBoxError 0 (m x))
        (fun i => 1+simplexBoxError 0 (m x-(i.val+1))) ∧ t ≤ u (Fin.last N)) →
    (K.card:ℝ) ≤ C*G x (N+1)*Real.exp (-c*t) := by
  obtain ⟨A,hA,hcost⟩ := prefixCubeCost_relative_bound
  let E := Real.exp (∑' n : ℕ,(n:ℝ)*simplexBoxError 0 n)
  have hE : 0 < E := Real.exp_pos _
  obtain ⟨c,hc,hrate⟩ := fixed_terminal_rate H hE
  refine ⟨E*Real.exp A,c,by positivity,hc,?_⟩
  filter_upwards [hcost,hrate,B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x hcost hrate hB
  intro N hNm t ht K hK
  let β : ℕ → ℝ := fun r => 1+simplexBoxError 0 (m x-r)
  let κ : Fin (N+1) → ℝ := enlargementScale β
  have hβ (r) : 1 ≤ β r := by
    dsimp [β]
    linarith [simplexBoxError_nonneg (by norm_num : (0:ℝ) ≤ 0) (m x-r)]
  have hκ (i) : 1 ≤ κ i := (hβ 0).trans (enlargementScale_top hβ i)
  have hκE (i) : κ i ≤ E := by
    have hh := reverse_enlargement_coordinate (m:=m x) (H:=0)
      (Nat.zero_le (m x)) (simplexBoxError 0) (simplexBoxError_nonneg (by norm_num))
      (summable_simplexBoxError_weighted 0) i (by have := i.isLt; omega)
    simpa only [Nat.zero_add] using hh
  have hj : (∏ i,κ i) ≤ E := by
    have hh := reverse_enlargement_jacobian (m:=N+1+H) (P:=H) (by omega)
      (simplexBoxError 0) (simplexBoxError_nonneg (by norm_num))
      (summable_simplexBoxError_weighted 0)
    rw [Nat.add_sub_cancel] at hh
    have ht : (∑' n : ℕ,((H+n:ℕ):ℝ)*simplexBoxError 0 (H+n)) ≤
        ∑' n : ℕ,(n:ℝ)*simplexBoxError 0 n := by
      have hs := summable_simplexBoxError_weighted 0
      have he := hs.sum_add_tsum_nat_add H
      have hn : 0 ≤ ∑ n ∈ Finset.range H,(n:ℝ)*simplexBoxError 0 n :=
        Finset.sum_nonneg (fun n _ => mul_nonneg (Nat.cast_nonneg _) (simplexBoxError_nonneg (by norm_num) n))
      have ht' : (∑' n : ℕ,((n+H:ℕ):ℝ)*simplexBoxError 0 (n+H)) ≤
          ∑' n : ℕ,(n:ℝ)*simplexBoxError 0 n := by linarith only [he,hn]
      simpa only [Nat.add_comm] using ht'
    have hh' : (∏ i,κ i) ≤ Real.exp (∑' n : ℕ,((H+n:ℕ):ℝ)*simplexBoxError 0 (H+n)) := by
      simpa only [κ,β,← hNm] using hh
    exact hh'.trans (Real.exp_le_exp.mpr ht)
  have hvol := unbanded_grid_terminal_exponential N (B x) (β 0) t
    (fun i => β (i.val+1)) κ K hB (zero_lt_one.trans_le (hβ 0))
    (fun i => zero_lt_one.trans_le (hβ (i.val+1))) ht hκ
    (enlargementScale_top hβ) (enlargementScale_step hβ) hK
  have hrate' := hrate (N+1) hNm (κ (Fin.last N)) (zero_lt_one.trans_le (hκ _)) (hκE _)
  have hexp : Real.exp (-((N+1:ℕ):ℝ)*(g (N+1)*(t/κ (Fin.last N)))/
      (B x+prefixCubeCost (N+1))) ≤ Real.exp (-c*t) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hrate' ht
    have he : -((N+1:ℕ):ℝ)*(g (N+1)*(t/κ (Fin.last N)))/
        (B x+prefixCubeCost (N+1))=
        -(((N+1:ℕ):ℝ)*g (N+1)/(κ (Fin.last N)*(B x+prefixCubeCost (N+1))))*t := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rw [he]
    linarith only [hh]
  have hr : ((N+1:ℕ):ℝ)*prefixCubeCost (N+1)/B x ≤ A := by
    have hh := hcost (N+1) (by omega)
    exact hh.trans (mul_le_of_le_one_right hA.le (pow_le_one₀ rho_pos.le rho_lt_one.le))
  have hp := (add_pow_le_exp_ratio hB (prefixCubeCost_nonneg (N+1)) (N+1)).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hr) (pow_nonneg hB.le _))
  have hden : 0 < (((N+1).factorial:ℝ)*∏ i : Fin (N+1),g (i.val+1)) :=
    mul_pos (by positivity) (Finset.prod_pos (fun i _ => g_pos _))
  have hmain : (∏ i,κ i)*((B x+prefixCubeCost (N+1))^(N+1)/
      (((N+1).factorial:ℝ)*∏ i : Fin (N+1),g (i.val+1))) ≤
      (E*Real.exp A)*G x (N+1) := by
    calc
      _ ≤ E*(Real.exp A*(B x)^(N+1)/
          (((N+1).factorial:ℝ)*∏ i : Fin (N+1),g (i.val+1))) := by
        apply mul_le_mul hj (div_le_div_of_nonneg_right hp hden.le)
          (div_nonneg (pow_nonneg (add_nonneg hB.le (prefixCubeCost_nonneg _)) _) hden.le) hE.le
      _ = _ := by rw [G,prod_fin_shifted (N+1) g]; ring
  calc
    _ ≤ (∏ i,κ i)*(Real.exp (-((N+1:ℕ):ℝ)*(g (N+1)*(t/κ (Fin.last N)))/
        (B x+prefixCubeCost (N+1)))*(B x+prefixCubeCost (N+1))^(N+1)/
          (((N+1).factorial:ℝ)*∏ i : Fin (N+1),g (i.val+1))) := hvol
    _ = Real.exp (-((N+1:ℕ):ℝ)*(g (N+1)*(t/κ (Fin.last N)))/
        (B x+prefixCubeCost (N+1)))*((∏ i,κ i)*
          ((B x+prefixCubeCost (N+1))^(N+1)/
            (((N+1).factorial:ℝ)*∏ i : Fin (N+1),g (i.val+1)))) := by ring
    _ ≤ Real.exp (-c*t)*((E*Real.exp A)*G x (N+1)) :=
      mul_le_mul hexp hmain
        (mul_nonneg (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hκ i)))
          (div_nonneg (pow_nonneg (add_nonneg hB.le (prefixCubeCost_nonneg _)) _) hden.le))
        (Real.exp_pos _).le
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
