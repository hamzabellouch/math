import Mathlib

namespace OAI
noncomputable section
open Set Filter
namespace LocalSemigroupExtension
variable {M : Type*} [Monoid M]
def extend (U : ℝ → M) (t : ℝ) : M := U (t-(⌊t⌋₊:ℝ)) * U 1 ^ ⌊t⌋₊
variable (U : ℝ → M) (h0 : U 0=1)
  (hadd : ∀ s t : ℝ, 0 ≤ s → 0≤t → s+t≤1 → U (s+t)=U s*U t)
include hadd in
lemma carry (x y : ℝ) (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Icc (0:ℝ) 1) (hxy : 1≤x+y) :
    U x*U y=U (x+y-1)*U 1 := by
  have ha := hadd (x+y-1) (1-y) (by linarith) (by linarith [hy.2]) (by linarith [hx.2])
  have hb := hadd (1-y) y (by linarith [hy.2]) hy.1 (by linarith)
  have h1 : (x+y-1)+(1-y)=x := by ring
  have h2 : (1-y)+y=1 := by ring
  rw [h1] at ha
  rw [h2] at hb
  rw [ha,mul_assoc,←hb]
include hadd in
lemma commute_one (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : Commute (U 1) (U x) := by
  show U 1*U x=U x*U 1
  simpa only [add_sub_cancel_left] using carry U hadd 1 x ⟨zero_le_one,le_rfl⟩ hx (by linarith [hx.1])
include h0 in
lemma extend_rep (n : ℕ) (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) :
    extend U ((n:ℝ)+r)=U r*U 1^n := by
  by_cases hl : r<1
  · have hf : ⌊(n:ℝ)+r⌋₊=n := by
      apply (Nat.floor_eq_iff (by have := Nat.cast_nonneg (α := ℝ) n; linarith [hr.1] : 0≤(n:ℝ)+r)).mpr
      constructor <;> linarith [hr.1]
    simp only [extend,hf,add_sub_cancel_left]
  · have he : r=1 := by linarith [hr.2]
    subst r
    have hf : ⌊(n:ℝ)+1⌋₊=n+1 := by
      rw [←Nat.cast_one,←Nat.cast_add,Nat.floor_natCast]
    simp only [extend,hf,Nat.cast_add,Nat.cast_one,sub_self,h0,one_mul,pow_succ']
include h0 in
lemma extend_unit (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : extend U t=U t := by
  simpa using extend_rep U h0 0 t ht
include h0 hadd in
lemma extend_add (s t : ℝ) (hs : 0 ≤ s) (ht : 0≤t) :
    extend U (s+t)=extend U s*extend U t := by
  let n : ℕ := ⌊s⌋₊
  let m : ℕ := ⌊t⌋₊
  let a : ℝ := s-n
  let b : ℝ := t-m
  have ha : a ∈ Icc (0:ℝ) 1 := by
    dsimp [a,n]
    exact ⟨sub_nonneg.mpr (Nat.floor_le hs), (by linarith [Nat.lt_floor_add_one s])⟩
  have hb : b ∈ Icc (0:ℝ) 1 := by
    dsimp [b,m]
    exact ⟨sub_nonneg.mpr (Nat.floor_le ht),(by linarith [Nat.lt_floor_add_one t])⟩
  have hc := (commute_one U hadd b hb).pow_left n
  have hp : extend U s*extend U t=(U a*U b)*U 1^(n+m) := by
    change (U a*U 1^n)*(U b*U 1^m)=_
    rw [pow_add]
    calc
      (U a*U 1^n)*(U b*U 1^m)=U a*(U 1^n*U b)*U 1^m := by simp only [mul_assoc]
      _=U a*(U b*U 1^n)*U 1^m := by rw [hc.eq]
      _=_ := by simp only [mul_assoc]
  rw [hp]
  by_cases hab : a+b≤1
  · have he : s+t=((n+m:ℕ):ℝ)+(a+b) := by dsimp [a,b]; push_cast; ring
    rw [he,extend_rep U h0 (n+m) (a+b) ⟨by linarith [ha.1,hb.1],hab⟩,
      hadd a b ha.1 hb.1 hab]
  · have he : s+t=((n+m+1:ℕ):ℝ)+(a+b-1) := by dsimp [a,b]; push_cast; ring
    have hr : a+b-1 ∈ Icc (0:ℝ) 1 := ⟨by linarith,by linarith [ha.2,hb.2]⟩
    rw [he,extend_rep U h0 (n+m+1) (a+b-1) hr,carry U hadd a b ha hb (by linarith),pow_succ']
    simp only [mul_assoc]
end LocalSemigroupExtension

end

end OAI
