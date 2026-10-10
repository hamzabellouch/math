import OAI.MeasureTheory.Falconer.Estimates.ScalarSeparatedTree

namespace OAI

/-! Strict projection growth for a separated cluster tree whose children
are sufficiently sparse relative to their gaps. -/
namespace Falconer
open scoped Pointwise

 theorem ScalarSeparatedTree.projection_log_gain {δ K κ : ℝ} (hδ : 0 < δ)
    (hK : 0 ≤ K) {N : ℕ} (T : ScalarSeparatedTree δ N)
    (B : Finset ℝ) (hB : B.Nonempty) (hBb : ∀ b ∈ B, |b| ≤ 1)
    (hball : ∀ u t : ℝ, δ ≤ t → t ≤ 1 →
      scalarBallMass B u t ≤ K*t^κ*(B.card : ℝ))
    (hscale : ∀ n < N, δ ≤ 5*T.radius n/T.gap n)
    (hporous : ∀ n < N,
      (T.branching n : ℝ)^4*K*(5*T.radius n/T.gap n)^κ ≤ 1/2) :
    ∀ n ≤ N, ∀ x ∈ T.nodes n, ∀ y ∈ T.nodes n,
      (3/2 : ℝ)*(∑ j ∈ Finset.range n, Real.log (T.branching j : ℝ)) ≤
        scalarAverage B (fun b => Real.log ((scalarCells δ
          (T.points n x+(T.points n y).image (fun z => b*z))).card : ℝ)) := by
  intro n hn
  induction n with
  | zero =>
    intro x hx y hy
    simp only [Finset.range_zero,Finset.sum_empty,mul_zero]
    have hpos (b : ℝ) : 0 < (scalarCells δ
        (T.points 0 x+(T.points 0 y).image (fun z => b*z))).card := by
      have hh := scalar_sum_cells_pos (δ := δ) (b := b) _ _
        (T.points_nonempty hδ (by omega) hx) (T.points_nonempty hδ (by omega) hy)
      exact_mod_cast hh
    have hh := scalarAverage_mono B (fun b _ => Real.log_nonneg
      (show (1 : ℝ) ≤ ((scalarCells δ
        (T.points 0 x+(T.points 0 y).image (fun z => b*z))).card : ℝ) by exact_mod_cast hpos b))
    simpa only [scalarAverage_const B hB 0] using hh
  | succ n ih =>
    intro x hx y hy
    have hnN : n < N := by omega
    have hr0 : 0 < T.radius n := hδ.trans_le (T.radius_ge n hnN)
    have hs1 : 5*T.radius n/T.gap n ≤ 1 :=
      (div_le_one (T.gap_pos n hnN)).2 (T.gap_gt n hnN).le
    have hs := scalar_porous_level_log_gain hδ (T.radius_ge n hnN) (T.gap_pos n hnN)
      (T.gap_gt n hnN) hK (hscale n hnN) hs1 B (T.children n x) (T.children n y)
      hB (T.child_nonempty hnN hx) (T.child_nonempty hnN hy) hBb
      (T.child_sep n hnN x hx) (T.child_sep n hnN y hy) hball
      (T.points n) (T.points n)
      (fun z hz => T.points_nonempty hδ (by omega) (T.child_subset n hnN x hx hz))
      (fun z hz => T.points_nonempty hδ (by omega) (T.child_subset n hnN y hy hz))
      (T.child_bound n hnN x hx) (T.child_bound n hnN y hy)
      (fun p hp => ih (by omega) p.1 (T.child_subset n hnN x hx (Finset.mem_product.mp hp).1)
        p.2 (T.child_subset n hnN y hy (Finset.mem_product.mp hp).2))
    rw [T.child_card n hnN x hx,T.child_card n hnN y hy,
      ← T.parent_eq n hnN x hx,← T.parent_eq n hnN y hy] at hs
    have hm : 0 < (T.branching n : ℝ) := by exact_mod_cast T.branch_pos n hnN
    have hm1 : 1 ≤ (T.branching n : ℝ) := by exact_mod_cast T.branch_pos n hnN
    have hl : Real.log ((T.branching n : ℝ)*(T.branching n : ℝ)) =
        2*Real.log (T.branching n : ℝ) := by rw [Real.log_mul hm.ne' hm.ne']; ring
    rw [hl] at hs
    have hp : (((T.branching n : ℝ)*(T.branching n : ℝ))^2*K*
        (5*T.radius n/T.gap n)^κ) ≤ 1/2 := by
      convert hporous n hnN using 1
      ring
    have hpl := mul_le_mul_of_nonneg_right hp (Real.log_nonneg hm1)
    rw [Finset.sum_range_succ]
    nlinarith

 theorem ScalarSeparatedTree.projection_gain {δ K κ : ℝ} (hδ : 0 < δ)
    (hK : 0 ≤ K) {N : ℕ} (T : ScalarSeparatedTree δ N)
    (B : Finset ℝ) (hB : B.Nonempty) (hBb : ∀ b ∈ B, |b| ≤ 1)
    (hball : ∀ u t : ℝ, δ ≤ t → t ≤ 1 →
      scalarBallMass B u t ≤ K*t^κ*(B.card : ℝ))
    (hscale : ∀ n < N, δ ≤ 5*T.radius n/T.gap n)
    (hporous : ∀ n < N,
      (T.branching n : ℝ)^4*K*(5*T.radius n/T.gap n)^κ ≤ 1/2)
    (x : ℝ) (hx : x ∈ T.nodes N) (y : ℝ) (hy : y ∈ T.nodes N) :
    ∃ b ∈ B, ((T.points N x).card : ℝ)^(3/2 : ℝ) ≤
      ((scalarCells δ (T.points N x+(T.points N y).image (fun z => b*z))).card : ℝ) := by
  have hg := T.projection_log_gain hδ hK B hB hBb hball hscale hporous N le_rfl x hx y hy
  let q := fun b : ℝ => ((scalarCells δ
    (T.points N x+(T.points N y).image (fun z => b*z))).card : ℝ)
  have hq : ∀ b ∈ B, 0 < q b := fun b _ => scalar_sum_cells_pos _ _
    (T.points_nonempty hδ le_rfl hx) (T.points_nonempty hδ le_rfl hy)
  have hc : 0 < ((T.points N x).card : ℝ) := by exact_mod_cast (T.points_nonempty hδ le_rfl hx).card_pos
  have hlog : Real.log ((T.points N x).card : ℝ) =
      ∑ j ∈ Finset.range N, Real.log (T.branching j : ℝ) := by
    rw [T.points_card hδ N le_rfl x hx,Nat.cast_prod]
    exact Real.log_prod (fun j hj => by exact_mod_cast (T.branch_pos j (Finset.mem_range.mp hj)).ne')
  have hrpow : ((T.points N x).card : ℝ)^(3/2 : ℝ) =
      Real.exp ((3/2 : ℝ)*(∑ j ∈ Finset.range N, Real.log (T.branching j : ℝ))) := by
    rw [Real.rpow_def_of_pos hc,hlog,mul_comm]
  have hmean : ((T.points N x).card : ℝ)^(3/2 : ℝ) ≤ scalarAverage B q := by
    rw [hrpow]
    exact (Real.exp_le_exp.mpr hg).trans (scalar_exp_average_log_le B hB q hq)
  apply Finset.exists_le_of_sum_le hB
  have hn : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hh := (le_div_iff₀ hn).1 hmean
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm,scalarAverage] using hh

end Falconer

end OAI
