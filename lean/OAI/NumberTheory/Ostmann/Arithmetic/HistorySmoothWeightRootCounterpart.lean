import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightArchimedeanDeriv
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightPivot

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
namespace Ostmann.Arithmetic
open Characters.RationalHistory HistorySymbolicStep
variable {κ ι : Type}

def keyProduct (keys : List κ) : Expr κ := product (keys.map Expr.atom)

theorem keyProduct_realEval (keys : List κ) (x : κ → ℝ) :
    (keyProduct keys).realEval x = (keys.map x).prod := by
  simp only [keyProduct,product_realEval,List.map_map,Expr.realEval,Function.comp_def]

theorem keyProduct_logSize (keys : List κ) : (keyProduct keys).logSize = keys.length := by
  simp [keyProduct,product_logSize,List.map_map,Function.comp_def,Expr.logSize]

theorem keyProduct_logBudget_one (keys : List κ) :
    (keyProduct keys).logBudget 1 = (keys.length : ℝ) := by
  simp only [Expr.logBudget,one_pow,mul_one,keyProduct_logSize]

theorem keyProduct_relativeControl (keys : List κ) (x : κ → ℝ) (hx : ∀ i, 0 < x i) :
    (keyProduct keys).RelativeControl x 1 := by
  apply product_relativeControl
  intro e he
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
  exact (hx i).ne'

theorem keyProduct_pos (keys : List κ) (x : κ → ℝ) (hx : ∀ i, 0 < x i) :
    0 < (keys.map x).prod := by
  apply List.prod_pos
  intro a ha
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
  exact hx i

def rootCounterpart (T U : ℝ) (Hkeys Ukeys : List κ) (S : Finset ι)
    (center : ι → ℝ) (cellKey : ι → κ) (x : κ → ℝ) : ℝ :=
  counterpartArchimedean T U ((Hkeys.map x).prod) ((Ukeys.map x).prod)
    S center (fun i => x (cellKey i))

theorem rootCounterpart_nonneg (T U : ℝ) (Hkeys Ukeys : List κ) (S : Finset ι)
    (center : ι → ℝ) (cellKey : ι → κ) (x : κ → ℝ) (hx : ∀ i, 0 < x i) :
    0 ≤ rootCounterpart T U Hkeys Ukeys S center cellKey x :=
  counterpartArchimedean_nonneg _ _ _ _ _ _ _
    (keyProduct_pos Hkeys x hx).le (keyProduct_pos Ukeys x hx).le

theorem rootCounterpart_abs_le (T U WH Wu : ℝ) (Hkeys Ukeys : List κ) (S : Finset ι)
    (center : ι → ℝ) (cellKey : ι → κ) (x : κ → ℝ) (hx : ∀ i, 0 < x i)
    (hH : T - WH ≤ Real.log ((Hkeys.map x).prod))
    (hu : Real.log ((Ukeys.map x).prod) ≤ U + Wu) :
    |rootCounterpart T U Hkeys Ukeys S center cellKey x| ≤ Real.exp (WH + Wu) := by
  rw [abs_of_nonneg (rootCounterpart_nonneg T U Hkeys Ukeys S center cellKey x hx)]
  exact counterpartArchimedean_le _ _ _ _ _ _ _ _ _
    (keyProduct_pos Hkeys x hx) (keyProduct_pos Ukeys x hx) hH hu

theorem rootCounterpart_norm_le (T U WH Wu : ℝ) (Hkeys Ukeys : List κ) (S : Finset ι)
    (center : ι → ℝ) (cellKey : ι → κ) (x : κ → ℝ) (hx : ∀ i, 0 < x i)
    (hH : T - WH ≤ Real.log ((Hkeys.map x).prod))
    (hu : Real.log ((Ukeys.map x).prod) ≤ U + Wu) :
    ‖(rootCounterpart T U Hkeys Ukeys S center cellKey x : ℂ)‖ ≤ Real.exp (WH + Wu) := by
  simpa only [Complex.norm_real,Real.norm_eq_abs] using
    rootCounterpart_abs_le T U WH Wu Hkeys Ukeys S center cellKey x hx hH hu

theorem rootCounterpart_contDiff_exp [Fintype κ] (T U : ℝ) (Hkeys Ukeys : List κ)
    (S : Finset ι) (center : ι → ℝ) (cellKey : ι → κ) :
    ContDiff ℝ ∞ (fun y : κ → ℝ =>
      rootCounterpart T U Hkeys Ukeys S center cellKey (fun i => Real.exp (y i))) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  have hprod (keys : List κ) : ContDiffAt ℝ ∞
      (fun z : κ → ℝ => (keys.map (fun i => Real.exp (z i))).prod) y := by
    have hh := (keyProduct keys).contDiffAt_logEval y
      (Expr.RelativeControl.regular _ _ 1 (keyProduct_relativeControl keys _ (fun i => Real.exp_pos _)))
    change ContDiffAt ℝ ∞ (fun z : κ → ℝ =>
      (keyProduct keys).realEval (fun i => Real.exp (z i))) y at hh
    simpa only [keyProduct_realEval] using hh
  apply counterpartArchimedean_contDiffAt T U _ _ S center _ y (hprod Hkeys) (hprod Ukeys)
  · intro i hi
    fun_prop
  · exact (keyProduct_pos Hkeys _ (fun i => Real.exp_pos _)).ne'

theorem rootCounterpart_logCurve_deriv_bound : ∃ D : ℝ, 0 < D ∧
    ∀ {κ ι : Type} [DecidableEq κ] (T U WH Wu : ℝ) (Hkeys Ukeys : List κ)
      (S : Finset ι) (center : ι → ℝ) (cellKey : ι → κ) (x : κ → ℝ) (j : κ),
      (∀ i, 0 < x i) → T - WH ≤ Real.log ((Hkeys.map x).prod) →
      Real.log ((Ukeys.map x).prod) ≤ U + Wu →
      |deriv (fun t => rootCounterpart T U Hkeys Ukeys S center cellKey (Expr.logCurve x j t)) 0| ≤
        Real.exp (WH + Wu) * ((Hkeys.length : ℝ) + (Ukeys.length : ℝ) + D * S.card) := by
  obtain ⟨D,hD,hbound⟩ := counterpartArchimedean_logCurve_deriv_bound
  refine ⟨D,hD,?_⟩
  intro κ ι _ T U WH Wu Hkeys Ukeys S center cellKey x j hx hH hu
  have hHpos : 0 < (keyProduct Hkeys).realEval x := by
    rw [keyProduct_realEval]
    exact keyProduct_pos Hkeys x hx
  have hupos : 0 < (keyProduct Ukeys).realEval x := by
    rw [keyProduct_realEval]
    exact keyProduct_pos Ukeys x hx
  have hh := hbound (keyProduct Hkeys) (keyProduct Ukeys) (fun i => Expr.atom (cellKey i))
    x j S center T U WH Wu 1 le_rfl
    (keyProduct_relativeControl Hkeys x hx) (keyProduct_relativeControl Ukeys x hx)
    (fun i hi => (hx (cellKey i)).ne') hHpos hupos
    (by simpa only [keyProduct_realEval] using hH) (by simpa only [keyProduct_realEval] using hu)
  simpa only [rootCounterpart,keyProduct_realEval,Expr.realEval,keyProduct_logBudget_one,
    Expr.logBudget,keyProduct_logSize,Expr.logSize,Expr.cancellationDepth,Nat.cast_one,pow_zero,one_pow,mul_one,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hh

end Ostmann.Arithmetic

end

end OAI
