import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepeatedSmoothPullback

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryActiveCoordinates
open Characters.RationalHistory
open scoped ContDiff
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def insert (I : Finset κ) (background : κ → ℝ) (x : I → ℝ) : κ → ℝ :=
  fun i => if hi : i∈I then x ⟨i,hi⟩ else background i

omit [Fintype κ] in
theorem insert_positive (I : Finset κ) (background : κ → ℝ) (x : I → ℝ)
    (hbackground : ∀ i, 0 < background i) (hx : ∀ i, 0 < x i) :
    ∀ i, 0 < insert I background x i := by
  intro i
  unfold insert
  split_ifs with hi
  · exact hx ⟨i,hi⟩
  · exact hbackground i

omit [Fintype κ] in
theorem insert_restriction (I : Finset κ) (background : κ → ℝ) :
    insert I background (fun i => background i.val) = background := by
  funext i
  simp [insert]

omit [Fintype κ] in
theorem insert_logCurve (I : Finset κ) (background : κ → ℝ) (x : I → ℝ)
    (i : I) (t : ℝ) :
    insert I background (Expr.logCurve x i t) = Expr.logCurve (insert I background x) i.val t := by
  funext j
  by_cases hj : j∈I
  · have hiff : (⟨j,hj⟩:I)=i ↔ j=i.val := Subtype.ext_iff
    simp only [insert,dite_eq_left hj,Expr.logCurve]
    by_cases he : j=i.val
    · simp only [he,ite_true]
    · simp only [he,ite_false]
      rw [ite_eq_right (hiff.not.mpr he)]
  · have hne : j≠i.val := by intro he; exact hj (he ▸ i.property)
    simp only [insert,dite_eq_right hj,Expr.logCurve,hne,ite_false,Real.exp_zero,mul_one]

def logInsert (I : Finset κ) (background : κ → ℝ) (y : I → ℝ) : κ → ℝ :=
  fun i => if hi : i∈I then y ⟨i,hi⟩ else Real.log (background i)

omit [Fintype κ] in
theorem insert_exp (I : Finset κ) (background : κ → ℝ) (y : I → ℝ)
    (hbackground : ∀ i, 0 < background i) :
    insert I background (fun i => Real.exp (y i)) = fun i => Real.exp (logInsert I background y i) := by
  funext i
  unfold insert logInsert
  split_ifs with hi
  · rfl
  · exact (Real.exp_log (hbackground i)).symm

theorem logInsert_contDiff (I : Finset κ) (background : κ → ℝ) :
    ContDiff ℝ ∞ (logInsert I background) := by
  apply contDiff_pi.mpr
  intro i
  unfold logInsert
  split_ifs <;> fun_prop

theorem log_contDiff_insert (f : (κ → ℝ) → ℂ) (I : Finset κ) (background : κ → ℝ)
    (hbackground : ∀ i, 0 < background i)
    (hf : ContDiff ℝ ∞ (fun y : κ → ℝ => f (fun i => Real.exp (y i)))) :
    ContDiff ℝ ∞ (fun y : I → ℝ => f (insert I background (fun i => Real.exp (y i)))) := by
  simpa only [Function.comp_def,← insert_exp I background _ hbackground] using
    hf.comp (logInsert_contDiff I background)

end Ostmann.Arithmetic.HistoryActiveCoordinates

end

end OAI
