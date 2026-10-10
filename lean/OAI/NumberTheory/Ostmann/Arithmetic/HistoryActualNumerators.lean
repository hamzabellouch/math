import OAI.NumberTheory.Ostmann.Arithmetic.HistoryIntegerFieldBridge
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPatternRows

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryActualNumerators
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistorySymbolicState HistorySymbolicEncoding HistorySymbolicLinearity HistoryNumeratorForms
open HistoryOccurrenceRows HistoryPatternRows HistoryRepeatedRenaming ClearedCoefficientFlags
open MvPolynomial

def actual : {l : ℕ} → (h : History l) → InternalKey h → ℤ
  | _, .leaf _ => fun i => nomatch i
  | _, .node a _ _ hp hm left right =>
      Sum.elim (fun _ => reversalNumerator left.root.frequency right.root.frequency
        ((a.giantPlus*(hp.map SmallSlot.value).prod:ℕ):ℤ)
        ((a.giantMinus*(hm.map SmallSlot.value).prod:ℕ):ℤ))
      (Sum.elim (actual left) (actual right))

theorem actual_divisible {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (i : InternalKey h) :
    ((internalSlot h i).value:ℤ) ∣ actual h i := by
  induction h with
  | leaf a => exact isEmptyElim i
  | @node l a p u hp hm left right ihl ihr =>
      rcases i with i | i
      · have hd : (u.get i).value ∣ (u.map SmallSlot.value).prod :=
          List.dvd_prod (List.mem_map.mpr ⟨u.get i,List.get_mem _ _,rfl⟩)
        have hd' : ((u.get i).value:ℤ) ∣ ((u.map SmallSlot.value).prod:ℤ) := by
          exact_mod_cast hd
        change ((u.get i).value:ℤ) ∣ reversalNumerator _ _ _ _
        rw [History.supported_reversal hs]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd' _) _
      · rcases i with i | i
        · exact ihl (History.supported_left hs) i
        · exact ihr (History.supported_right hs) i

variable {ι : Type*}

theorem rows_actual_eval {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (e : TreeExpr ι h) (x : ι → ℚ)
    (he : TreeCorrect x h e) (i : InternalKey h) :
    (rows V outside h hs e e i).1.rationalEval x = (actual h i:ℚ) := by
  induction h with
  | leaf a => exact isEmptyElim i
  | @node l a p u hp hm left right ihl ihr =>
      rcases i with i | i
      · simpa only [rows,actual,Sum.elim_inl,reversalNumerator,Int.cast_sub,Int.cast_mul]
          using nodeNumerator_eval hs e.1 x he.1
      · rcases i with i | i
        · exact ihl (History.supported_left hs) e.2.1 he.2.1 i
        · exact ihr (History.supported_right hs) e.2.2 he.2.2 i

theorem rows_linear {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (e c d : TreeExpr ι h) (x : ι → ℚ)
    (X Y : ℚ) (he : TreeLinear x X Y h e c d) (i : InternalKey h) :
    (rows V outside h hs e e i).1.rationalEval x =
      (rows V outside h hs c d i).1.rationalEval x*X+
        (rows V outside h hs c d i).2.rationalEval x*Y := by
  induction h with
  | leaf a => exact isEmptyElim i
  | @node l a p u hp hm left right ihl ihr =>
      rcases i with i | i
      · exact nodeNumerator_linear hs e.1 c.1 d.1 x X Y he.1
      · rcases i with i | i
        · exact ihl (History.supported_left hs) e.2.1 c.2.1 d.2.1 he.2.1 i
        · exact ihr (History.supported_right hs) e.2.2 c.2.2 d.2.2 he.2.2 i

theorem actual_linear {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (i : InternalKey h) :
    (actual h i:ℚ) =
      (canonical h hs i).1.rationalEval (rationalSample h)*(h.root.giantPlus:ℚ)+
        (canonical h hs i).2.rationalEval (rationalSample h)*(h.root.giantMinus:ℚ) := by
  have he := rows_linear h hs _ _ _ (rationalSample h) _ _
    (symbolicHistory_linear h hs (rationalSample h)) i
  rw [rows_actual_eval h hs _ _ (symbolicHistory_correct h hs) i] at he
  exact he

theorem actual_pattern_linear {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (i : InternalKey h) :
    (actual h i:ℚ) =
      (row h hs i).1.rationalEval (sample h)*(h.root.giantPlus:ℚ)+
        (row h hs i).2.rationalEval (sample h)*(h.root.giantMinus:ℚ) := by
  simpa only [row,Expr.rationalEval_rename,sample_comp] using actual_linear h hs i

theorem integer_linear_cleared {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (i : InternalKey h) :
    eval (fun j => patternSample h j.val) (commonDenominator (row h hs i).1 (row h hs i).2)*
      actual h i =
    eval (fun j => patternSample h j.val) (leftFlag h hs i)*(h.root.giantPlus:ℤ)+
      eval (fun j => patternSample h j.val) (rightFlag h hs i)*(h.root.giantMinus:ℤ) := by
  obtain ⟨ha,hb,_⟩ := row_regular_nonzero h hs i
  have hca := coefficients_cleared (row h hs i).1 (row h hs i).2 (sample h)
    ((Expr.fieldRegularAt_rat _ _).mpr ha) ((Expr.fieldRegularAt_rat _ _).mpr hb)
  simp only [Expr.fieldEval_rat] at hca
  have hQ : eval₂ (Int.castRingHom ℚ) (sample h)
      (commonDenominator (row h hs i).1 (row h hs i).2)*(actual h i:ℚ) =
      eval₂ (Int.castRingHom ℚ) (sample h) (leftFlag h hs i)*(h.root.giantPlus:ℚ)+
        eval₂ (Int.castRingHom ℚ) (sample h) (rightFlag h hs i)*(h.root.giantMinus:ℚ) := by
    rw [actual_pattern_linear h hs i]
    change _ = eval₂ _ _ (leftCoefficient _ _)*_+eval₂ _ _ (rightCoefficient _ _)*_
    rw [hca.2.1,hca.2.2]
    ring
  have hD : eval₂ (Int.castRingHom ℚ) (sample h)
      (commonDenominator (row h hs i).1 (row h hs i).2) =
      (eval (fun j : PatternKey h => patternSample h j.val)
        (commonDenominator (row h hs i).1 (row h hs i).2):ℚ) :=
    Expr.eval₂_cast_int _ (fun j : PatternKey h => patternSample h j.val)
  have hA : eval₂ (Int.castRingHom ℚ) (sample h) (leftFlag h hs i) =
      (eval (fun j : PatternKey h => patternSample h j.val) (leftFlag h hs i):ℚ) :=
    Expr.eval₂_cast_int _ (fun j : PatternKey h => patternSample h j.val)
  have hB : eval₂ (Int.castRingHom ℚ) (sample h) (rightFlag h hs i) =
      (eval (fun j : PatternKey h => patternSample h j.val) (rightFlag h hs i):ℚ) :=
    Expr.eval₂_cast_int _ (fun j : PatternKey h => patternSample h j.val)
  rw [hD,hA,hB] at hQ
  apply Int.cast_injective (α := ℚ)
  simpa only [Int.cast_mul,Int.cast_add,Int.cast_natCast] using hQ

theorem actual_line_zero {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (i : InternalKey h) :
    let p := (internalSlot h i).value
    eval₂ (Int.castRingHom (ZMod p)) (fun j => (patternSample h j.val:ZMod p))
        (leftFlag h hs i)*(h.root.giantPlus:ZMod p)+
      eval₂ (Int.castRingHom (ZMod p)) (fun j => (patternSample h j.val:ZMod p))
        (rightFlag h hs i)*(h.root.giantMinus:ZMod p) = 0 := by
  dsimp only
  rw [Expr.eval₂_cast_int,Expr.eval₂_cast_int]
  have he := congrArg (fun z : ℤ => (z:ZMod (internalSlot h i).value))
    (integer_linear_cleared h hs i)
  have hzero : (actual h i:ZMod (internalSlot h i).value) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (actual_divisible h hs i)
  simp only [Int.cast_mul,Int.cast_add,Int.cast_natCast,hzero,mul_zero] at he
  exact he.symm

end Ostmann.Arithmetic.HistoryActualNumerators

end

end OAI
