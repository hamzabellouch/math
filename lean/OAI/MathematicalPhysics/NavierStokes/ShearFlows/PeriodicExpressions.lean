import OAI.MathematicalPhysics.NavierStokes.ShearFlows.RationalEvaluation
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Extension

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

section PartPeriodicExpressions

open Set Filter
open scoped Topology BigOperators ContDiff
namespace ShearFlows

theorem periodize_eq_finite {L a b u v y : ℝ} (hL : 0 < L)
    {f : ℝ → ℝ} (hs : Function.support f ⊆ Icc a b) (hy : y ∈ Icc u v) :
    periodize L f y = ∑ n ∈ Finset.Icc ⌊(u-b)/L⌋ ⌈(v-a)/L⌉,
      f (y-L*(n : ℝ)) := by
  apply tsum_eq_sum
  intro n hn
  by_contra hfn
  have hb := hs hfn
  have hnlo : (u-b)/L ≤ (n : ℝ) := (div_le_iff₀ hL).2 (by nlinarith [hb.2,hy.1])
  have hnhi : (n : ℝ) ≤ (v-a)/L := (le_div_iff₀ hL).2 (by nlinarith [hb.1,hy.2])
  apply hn
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast (Int.floor_le ((u-b)/L)).trans hnlo
  · exact_mod_cast hnhi.trans (Int.le_ceil ((v-a)/L))

theorem periodize_deriv {L a b : ℝ} (hL : 0 < L)
    {f : ℝ → ℝ} (hs : Function.support f ⊆ Icc a b) (hf : ContDiff ℝ ∞ f) :
    deriv (periodize L f) = periodize L (deriv f) := by
  have hs' : Function.support (deriv f) ⊆ Icc a b :=
    support_deriv_subset.trans (closure_minimal hs isClosed_Icc)
  funext x
  let J := Finset.Icc ⌊(x-1-b)/L⌋ ⌈(x+1-a)/L⌉
  have he : periodize L f =ᶠ[𝓝 x] (fun y => ∑ n ∈ J, f (y-L*(n : ℝ))) := by
    filter_upwards [Ioo_mem_nhds (show x-1<x by linarith) (show x<x+1 by linarith)] with y hy
    exact periodize_eq_finite hL hs (Ioo_subset_Icc_self hy)
  rw [he.deriv_eq, periodize_eq_finite hL hs' (show x ∈ Icc (x-1) (x+1) from ⟨by linarith, by linarith⟩)]
  have hd := fun (n : ℤ) => (((hf.differentiable (by simp)) (x-L*(n : ℝ))).hasDerivAt.comp x
    ((hasDerivAt_id x).sub_const (L*(n : ℝ))))
  convert! (HasDerivAt.sum (u := J) fun n _ => hd n).deriv using 1
  · congr 1; funext y; simp [Finset.sum_apply, Function.comp_def]
  · simp [J]

structure PeriodicExpr where
  period : ℚ
  lower : ℚ
  upper : ℚ
  body : ProfileExpr
  deriving DecidableEq

namespace PeriodicExpr

local instance : Preorder ℤ := Int.instLinearOrder.toPartialOrder.toPreorder

def Valid (p : PeriodicExpr) : Prop :=
  0 < p.period ∧ Function.support p.body.val ⊆ Icc (p.lower : ℝ) p.upper

noncomputable def val (p : PeriodicExpr) : ℝ → ℝ := periodize p.period p.body.val

def diff (p : PeriodicExpr) : PeriodicExpr := { p with body := p.body.diff }

theorem valid_diff {p : PeriodicExpr} (hp : p.Valid) : p.diff.Valid := by
  refine ⟨hp.1, ?_⟩
  change Function.support p.body.diff.val ⊆ Icc (p.lower : ℝ) p.upper
  rw [ProfileExpr.val_diff]
  exact support_deriv_subset.trans (closure_minimal hp.2 isClosed_Icc)

theorem smooth {p : PeriodicExpr} (hp : p.Valid) : ContDiff ℝ ∞ p.val :=
  periodize_smooth (by exact_mod_cast hp.1) hp.2 p.body.smooth

theorem val_diff {p : PeriodicExpr} (hp : p.Valid) : p.diff.val = deriv p.val := by
  dsimp [diff,val]
  rw [ProfileExpr.val_diff, periodize_deriv (by exact_mod_cast hp.1) hp.2 p.body.smooth]

theorem hasDerivAt {p : PeriodicExpr} (hp : p.Valid) (x : ℝ) :
    HasDerivAt p.val (p.diff.val x) x := by
  rw [val_diff hp]
  exact (smooth hp).differentiable (by simp) x |>.hasDerivAt

def translates (p : PeriodicExpr) (q : ℚ) : Finset ℤ :=
  Finset.Icc ⌊(q-p.upper)/p.period⌋ ⌈(q-p.lower)/p.period⌉

def enclose (p : PeriodicExpr) (q : ℚ) (n : ℕ) : QBall :=
  ⟨∑ k ∈ p.translates q, (p.body.enclose (q-p.period*k) n).center,
   ∑ k ∈ p.translates q, (p.body.enclose (q-p.period*k) n).radius⟩

theorem val_eq_sum {p : PeriodicExpr} (hp : p.Valid) (q : ℚ) :
    p.val q = ∑ k ∈ p.translates q, p.body.val (q-p.period*(k : ℝ)) := by
  have h := periodize_eq_finite (L := (p.period : ℝ)) (by exact_mod_cast hp.1) hp.2
    (show (q : ℝ) ∈ Icc (q : ℝ) q from ⟨le_rfl,le_rfl⟩)
  convert! h using 1
  simp [translates, ← Rat.cast_sub, ← Rat.cast_div, Rat.floor_cast, Rat.ceil_cast]

theorem enclose_contains {p : PeriodicExpr} (hp : p.Valid) (q : ℚ) (n : ℕ) :
    (p.enclose q n).Contains (p.val q) := by
  dsimp [QBall.Contains,enclose]
  push_cast
  rw [val_eq_sum hp, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  simpa [QBall.Contains] using p.body.enclose_contains (q-p.period*k) n

theorem enclose_converges {p : PeriodicExpr} (hp : p.Valid) (q : ℚ) :
    QBall.Converges (p.enclose q) (p.val q) := by
  constructor
  · rw [val_eq_sum hp]
    convert! tendsto_finsetSum (p.translates q) (fun k _ => (p.body.enclose_converges (q-p.period*k)).1) using 1 <;>
      simp [enclose]
  · convert! tendsto_finsetSum (p.translates q) (fun k _ => (p.body.enclose_converges (q-p.period*k)).2) using 1 <;>
      simp [enclose]

def bound (p : PeriodicExpr) : ℚ :=
  (Finset.Icc ⌊(-p.upper)/p.period⌋ ⌈(p.period-p.lower)/p.period⌉).card *
    p.body.bound (|p.lower|+|p.upper|)

theorem bound_nonneg (p : PeriodicExpr) : 0 ≤ p.bound := by
  exact mul_nonneg (Nat.cast_nonneg _) (p.body.bound_nonneg _)

theorem val_bound {p : PeriodicExpr} (hp : p.Valid) (x : ℝ) :
    |p.val x| ≤ (p.bound : ℝ) := by
  have hL : (0 : ℝ) < p.period := by exact_mod_cast hp.1
  let k : ℤ := ⌊x/(p.period : ℝ)⌋
  let y : ℝ := x-(p.period : ℝ)*k
  have hy : y ∈ Icc 0 (p.period : ℝ) := by
    constructor
    · dsimp [y,k]; nlinarith [Int.floor_le (x/(p.period : ℝ)), div_mul_cancel₀ x hL.ne']
    · dsimp [y,k]; nlinarith [Int.lt_floor_add_one (x/(p.period : ℝ)), div_mul_cancel₀ x hL.ne']
  have he : p.val x = p.val y := by
    simpa [val,y,mul_comm] using (periodize_periodic (p.period : ℝ) p.body.val).int_mul k y
  rw [he]
  change |periodize _ _ y| ≤ _
  rw [periodize_eq_finite hL hp.2 hy]
  have hb (n : ℤ) : |p.body.val (y-p.period*(n : ℝ))| ≤
      (p.body.bound (|p.lower|+|p.upper|) : ℝ) := by
    by_cases hn : p.body.val (y-p.period*(n : ℝ)) = 0
    · simp only [hn,abs_zero]
      exact_mod_cast p.body.bound_nonneg (|p.lower|+|p.upper|)
    · have hs := hp.2 hn
      apply p.body.val_bound
      have hl := neg_abs_le (p.lower : ℝ)
      have hu := le_abs_self (p.upper : ℝ)
      simp only [Rat.cast_add, Rat.cast_abs]
      rw [abs_of_nonneg (show (0 : ℝ) ≤ |(p.lower : ℝ)|+|(p.upper : ℝ)| by positivity)]
      exact abs_le.mpr ⟨by linarith [hs.1,abs_nonneg (p.upper : ℝ)],
        by linarith [hs.2,abs_nonneg (p.lower : ℝ)]⟩
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  convert! Finset.sum_le_sum (fun n (_ : n ∈ Finset.Icc ⌊(0-(p.upper : ℝ))/p.period⌋
    ⌈((p.period : ℝ)-p.lower)/p.period⌉) => hb n) using 1
  simp [bound, ← Rat.cast_sub, ← Rat.cast_neg, ← Rat.cast_div, Rat.floor_cast, Rat.ceil_cast]

end PeriodicExpr
end ShearFlows

end PartPeriodicExpressions

end

end OAI
