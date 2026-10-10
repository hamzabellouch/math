import OAI.Combinatorics.HoneycombChords.BoundarySystems

namespace OAI

/-! Planar rows for critical honeycomb strips.

The formulas follow the finite strip transfer calculation in the companion paper
on uniform marked polygon estimates. -/

section
namespace CriticalHoneycomb.Transfer.PlanarNormalization
open scoped Matrix
lemma act_congr_of_length (t : TileWeights) (i n : ℕ) (f g : DiluteState)
    (h : ∀ xs,xs.length=n→f xs=g xs) (xs : List Spin) (hx : xs.length=n) :
    act t i f xs=act t i g xs := by
  induction i generalizing xs f g n with
  | zero =>
    cases xs with
    | nil => rfl
    | cons a xs =>
      cases xs with
      | nil => rfl
      | cons b xs =>
        simp only [act]
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro d hd
        rw [h (c::d::xs) (by simpa using hx)]
  | succ i ih =>
    cases xs with
    | nil => rfl
    | cons a xs =>
      apply ih (n:=xs.length) (fun ys =>f (a::ys)) (fun ys=>g (a::ys)) _ xs rfl
      intro ys hy
      exact h (a::ys) (by simpa [hy] using hx)
lemma planarRow_congr_of_length (i n : ℕ) (ts : List TileWeights) (f g : DiluteState)
    (h : ∀ xs,xs.length=n→f xs=g xs) (xs : List Spin) (hx : xs.length=n) :
    planarRow i ts f xs=planarRow i ts g xs := by
  induction ts generalizing i f g with
  | nil => exact h xs hx
  | cons t ts ih =>
    apply ih
    intro ys hy
    exact act_congr_of_length t i n f g h ys hy
lemma act_suffix (t : TileWeights) (i : ℕ) (f : DiluteState)
    (xs tail : List Spin) (hi : i+1<xs.length) :
    act t i f (xs++tail)=act t i (fun ys=>f (ys++tail)) xs := by
  induction i generalizing xs f with
  | zero =>
    cases xs with
    | nil => simp at hi
    | cons a xs =>
      cases xs with
      | nil => simp at hi
      | cons b xs => rfl
  | succ i ih =>
    cases xs with
    | nil => simp at hi
    | cons a xs =>
      exact ih (fun ys=>f (a::ys)) xs (by simpa using hi)
lemma planarRow_suffix (i : ℕ) (ts : List TileWeights) (f : DiluteState)
    (xs tail : List Spin) (hi : i+ts.length<xs.length) :
    planarRow i ts f (xs++tail)=planarRow i ts (fun ys=>f (ys++tail)) xs := by
  induction ts generalizing i f with
  | nil => rfl
  | cons t ts ih =>
    simp only [planarRow]
    rw [ih (i+1) (act t i f) (by simp at hi;omega)]
    apply planarRow_congr_of_length (i+1) xs.length ts _ _ _ xs rfl
    intro ys hy
    exact act_suffix t i f ys tail (by simp at hi;omega)
lemma planarRow_zero (i : ℕ) (ts : List TileWeights) :
    planarRow i ts (fun _=>0)=(fun _=>0) := by
  induction ts generalizing i with
  | nil => rfl
  | cons t ts ih =>
    have hz : act t i (fun _=>0)=(fun _=>0) := by
      funext xs
      induction i generalizing xs with
      | zero => cases xs with
        | nil => rfl
        | cons a xs => cases xs <;> simp [act]
      | succ i ih => cases xs with
        | nil => rfl
        | cons a xs => exact ih xs
    simp only [planarRow,hz,ih]
noncomputable def seedAux (k : ℂ) (f : DiluteState) : DiluteState
  | a::b::xs => K k a b * f xs
  | _ => 0
lemma seedAux_zero (f : DiluteState) : seedAux 0 f=addAux f := by
  funext xs
  cases xs with
  | nil => rfl
  | cons a xs => cases xs with
    | nil => cases a <;> rfl
    | cons b xs => cases a <;> cases b <;> simp [seedAux,K,addAux]

noncomputable def hardDoubleRow (t : TileWeights) (n : ℕ) (f : DiluteState) : DiluteState :=
  fun xs=>∑ a : Spin,∑ b : Spin,K 0 a b*
    sourceTwoRows (List.replicate n t) (List.replicate n t) (seedAux 0 f) (a::b::xs)
lemma hardDoubleRow_eq_columns (t : TileWeights) (n : ℕ) (f : DiluteState)
    (xs : List Spin) (hx : xs.length=n) :
    hardDoubleRow t n f xs=vacuumColumn t n (vacuumColumn t n f) xs := by
  classical
  simp only [hardDoubleRow,Fintype.sum_option,Fintype.sum_bool,K,zero_mul,one_mul,add_zero,seedAux_zero]
  rw [←two_rows_eq (List.replicate n t) (List.replicate n t) (by simp) (by simp) _ xs hx none none]
  rw [show xs++[none,none]=(xs++[none])++[none] by simp]
  rw [planarRow_suffix 0 _ _ (xs++[none]) [none] (by simp [hx])]
  change _=planarRow 0 (List.replicate n t) (addOne (vacuumColumn t n f)) (xs++[none])
  apply planarRow_congr_of_length 0 (n+1) _ _ _ _ _ (by simp [hx])
  intro ys hy
  cases ys with
  | nil => simp at hy
  | cons a ys =>
    simp only [List.cons_append,planarRow_under]
    cases a with
    | none =>
      have hh : (fun us=>addAux f (none::us))=addOne f := by
        funext us
        cases us with
        | nil => rfl
        | cons a us => cases a <;> rfl
      rw [hh]
      rfl
    | some a =>
      have hh : (fun us=>addAux f (some a::us))=(fun _=>0) := by
        funext us
        cases us <;> rfl
      rw [hh,planarRow_zero]
      rfl
end CriticalHoneycomb.Transfer.PlanarNormalization

end

end OAI
