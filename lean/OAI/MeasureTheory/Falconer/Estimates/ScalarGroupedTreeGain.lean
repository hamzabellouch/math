import OAI.MeasureTheory.Falconer.Estimates.ScalarPorousGroupingGain
import OAI.MeasureTheory.Falconer.Estimates.ScalarSeparatedTree

namespace OAI

/-! Iterating the grouped porous gain on the original cluster tree. The
 gain depends on selected local group sizes, not total branching. -/
namespace Falconer
open scoped Pointwise

 theorem ScalarSeparatedTree.grouped_projection_log_gain {δ K κ : ℝ} (hδ : 0 < δ)
    (hK : 0 ≤ K) {N : ℕ} (T : ScalarSeparatedTree δ N)
    (hbound : ∀ n ≤ N, ∀ x ∈ T.nodes n, |x| ≤ 1)
    (B : Finset ℝ) (hB : B.Nonempty) (hBb : ∀ b ∈ B, 1/3 ≤ b ∧ b ≤ 1)
    (hball : ∀ u t : ℝ, δ ≤ t → t ≤ 1 → scalarBallMass B u t ≤ K*t^κ*(B.card : ℝ))
    (M : ℕ → ℕ) (hM : ∀ n < N, 83521 ≤ M n)
    (hbranch : ∀ n < N, 2*M n ≤ T.branching n)
    (hgap : ∀ n < N, 15*T.radius n < T.gap n)
    (hscale : ∀ n < N, δ ≤ 5*T.radius n/T.gap n)
    (hsmall : ∀ n < N, 16*(M n:ℝ)^4*K*(5*T.radius n/T.gap n)^κ ≤ 1/4) :
    ∀ n ≤ N, ∀ x ∈ T.nodes n, ∀ y ∈ T.nodes n,
      (∑ j ∈ Finset.range n, (Real.log (T.branching j : ℝ)+(1/2 : ℝ)*Real.log (M j : ℝ))) ≤
        scalarAverage B (fun b => Real.log ((scalarCells δ
          (T.points n x+(T.points n y).image (fun z => b*z))).card : ℝ)) := by
  have hbnd (n : ℕ) (hn : n ≤ N) (x : ℝ) (hx : x ∈ T.nodes n) :
      0 ≤ x-(-1) ∧ x-(-1) ≤ 2 := by
    have hh := abs_le.mp (hbound n hn x hx)
    constructor <;> linarith
  intro n hn
  induction n with
  | zero =>
    intro x hx y hy
    simp only [Finset.range_zero,Finset.sum_empty]
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
    have hxy : (T.children n x).card = (T.children n y).card := by
      rw [T.child_card n hnN x hx,T.child_card n hnN y hy]
    have hmx : 2*M n ≤ (T.children n x).card := by
      rw [T.child_card n hnN x hx]
      exact hbranch n hnN
    have hs1 : 5*T.radius n/T.gap n ≤ 1 :=
      (div_le_one (T.gap_pos n hnN)).2 (T.gap_gt n hnN).le
    have hs := scalar_porous_grouping_gain hδ (T.radius_ge n hnN) (T.gap_pos n hnN)
      (hgap n hnN) hK (hscale n hnN) hs1 B (T.children n x) (T.children n y)
      hB (T.child_nonempty hnN hx) (T.child_nonempty hnN hy) hBb
      (fun z hz => hbnd n (by omega) z (T.child_subset n hnN x hx hz))
      (fun z hz => hbnd n (by omega) z (T.child_subset n hnN y hy hz))
      (T.child_sep n hnN x hx) (T.child_sep n hnN y hy) hxy hball
      (M n) (hM n hnN) hmx (hsmall n hnN) (T.points n) (T.points n)
      (fun z hz => T.points_nonempty hδ (by omega) (T.child_subset n hnN x hx hz))
      (fun z hz => T.points_nonempty hδ (by omega) (T.child_subset n hnN y hy hz))
      (T.child_bound n hnN x hx) (T.child_bound n hnN y hy)
      (fun p hp => ih (by omega) p.1 (T.child_subset n hnN x hx (Finset.mem_product.mp hp).1)
        p.2 (T.child_subset n hnN y hy (Finset.mem_product.mp hp).2))
    rw [T.child_card n hnN x hx,← T.parent_eq n hnN x hx,← T.parent_eq n hnN y hy] at hs
    rw [Finset.sum_range_succ]
    linarith

 theorem ScalarSeparatedTree.grouped_projection_gain {δ K κ : ℝ} (hδ : 0 < δ)
    (hK : 0 ≤ K) {N : ℕ} (T : ScalarSeparatedTree δ N)
    (hbound : ∀ n ≤ N, ∀ x ∈ T.nodes n, |x| ≤ 1)
    (B : Finset ℝ) (hB : B.Nonempty) (hBb : ∀ b ∈ B, 1/3 ≤ b ∧ b ≤ 1)
    (hball : ∀ u t : ℝ, δ ≤ t → t ≤ 1 → scalarBallMass B u t ≤ K*t^κ*(B.card : ℝ))
    (M : ℕ → ℕ) (hM : ∀ n < N, 83521 ≤ M n)
    (hbranch : ∀ n < N, 2*M n ≤ T.branching n)
    (hgap : ∀ n < N, 15*T.radius n < T.gap n)
    (hscale : ∀ n < N, δ ≤ 5*T.radius n/T.gap n)
    (hsmall : ∀ n < N, 16*(M n:ℝ)^4*K*(5*T.radius n/T.gap n)^κ ≤ 1/4)
    (x : ℝ) (hx : x ∈ T.nodes N) (y : ℝ) (hy : y ∈ T.nodes N) :
    ∃ b ∈ B, ((T.points N x).card : ℝ)*Real.exp ((1/2 : ℝ)*(∑ j ∈ Finset.range N, Real.log (M j : ℝ))) ≤
      ((scalarCells δ (T.points N x+(T.points N y).image (fun z => b*z))).card : ℝ) := by
  have hg := T.grouped_projection_log_gain hδ hK hbound B hB hBb hball M hM hbranch hgap hscale hsmall
    N le_rfl x hx y hy
  let q := fun b : ℝ => ((scalarCells δ
    (T.points N x+(T.points N y).image (fun z => b*z))).card : ℝ)
  have hq : ∀ b ∈ B, 0 < q b := fun b _ => scalar_sum_cells_pos _ _
    (T.points_nonempty hδ le_rfl hx) (T.points_nonempty hδ le_rfl hy)
  have hc : 0 < ((T.points N x).card : ℝ) := by exact_mod_cast (T.points_nonempty hδ le_rfl hx).card_pos
  have hlog : Real.log ((T.points N x).card : ℝ) =
      ∑ j ∈ Finset.range N, Real.log (T.branching j : ℝ) := by
    rw [T.points_card hδ N le_rfl x hx,Nat.cast_prod]
    exact Real.log_prod (fun j hj => by exact_mod_cast (T.branch_pos j (Finset.mem_range.mp hj)).ne')
  have he : Real.exp (∑ j ∈ Finset.range N,
      (Real.log (T.branching j : ℝ)+(1/2 : ℝ)*Real.log (M j : ℝ))) =
      ((T.points N x).card : ℝ)*Real.exp ((1/2 : ℝ)*(∑ j ∈ Finset.range N, Real.log (M j : ℝ))) := by
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← hlog,Real.exp_add,Real.exp_log hc]
  have hmean : ((T.points N x).card : ℝ)*Real.exp ((1/2 : ℝ)*(∑ j ∈ Finset.range N, Real.log (M j : ℝ))) ≤
      scalarAverage B q := by
    rw [← he]
    exact (Real.exp_le_exp.mpr hg).trans (scalar_exp_average_log_le B hB q hq)
  apply Finset.exists_le_of_sum_le hB
  have hn : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hh := (le_div_iff₀ hn).1 hmean
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm,scalarAverage] using hh

end Falconer

end OAI
