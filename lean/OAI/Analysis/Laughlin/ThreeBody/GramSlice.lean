import OAI.Analysis.Laughlin.Pair.PolynomialBridge
import OAI.Analysis.Laughlin.ThreeBody.Gram

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def sliceOrbital (Q z : ℕ) (hz : z ≤ Q) (p : Fin (z+1)) : Fin (Q+1) :=
  ⟨z-p.val,by omega⟩

noncomputable def threeBodyGramSlice (Q z : ℕ) (hz : z ≤ Q)
    (p q : Fin (z+1)) : ℝ :=
  (if p = q then 1 else 0) - 2*∑ t : Fin (Q+1),
    pairCoefficient Q p.val (sliceOrbital Q z hz q) t *
      pairCoefficient Q q.val (sliceOrbital Q z hz p) t

theorem threeBodyGramSlice_physical (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (p q : Fin (z+1)) :
    (threeBodyGramSlice Q z hz p q : ℂ) =
      occupationInner Q (threeBodyColumn Q p.val (sliceOrbital Q z hz p))
        (threeBodyColumn Q q.val (sliceOrbital Q z hz q)) := by
  rw [threeBodyColumn_gram Q p.val q.val hQ (by omega)]
  unfold threeBodyGramSlice
  push_cast
  congr 1
  by_cases h : p = q
  · subst q; simp
  · have hv : p.val ≠ q.val := by simpa only [Fin.ext_iff] using h
    simp [h,hv]

theorem pairCoefficient_base (Q : ℕ) (hQ : 2 ≤ Q) (x y : Fin (Q+1)) :
    pairCoefficient Q 0 x y =
      if x.val = 0 ∧ y.val = 1 then -(1/Real.sqrt 2) else
      if x.val = 1 ∧ y.val = 0 then 1/Real.sqrt 2 else 0 := by
  rw [pairCoefficient_choose Q 0 (by omega) (by omega)]
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have hr : (Q : ℝ)/(2*Q) = 1/2 := by field_simp
  by_cases hs : x.val+y.val=1
  · have hc : (x.val=0 ∧ y.val=1) ∨ (x.val=1 ∧ y.val=0) := by omega
    rcases hc with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · simp [hx,hy,hr]
    · simp [hx,hy,hr]
  · have h₀ : ¬(x.val=0 ∧ y.val=1) := by omega
    have h₁ : ¬(x.val=1 ∧ y.val=0) := by omega
    rw [ite_eq_right hs,ite_eq_right h₀,ite_eq_right h₁]

theorem swap_base_row (Q q : ℕ) (hQ : 2 ≤ Q) (i j : Fin (Q+1)) :
    (∑ t : Fin (Q+1), pairCoefficient Q 0 j t * pairCoefficient Q q i t) =
      if j.val=0 then -pairCoefficient Q q i ⟨1,by omega⟩ / Real.sqrt 2 else
      if j.val=1 then pairCoefficient Q q i ⟨0,by omega⟩ / Real.sqrt 2 else 0 := by
  simp_rw [pairCoefficient_base Q hQ]
  have ht₀ (t : Fin (Q+1)) : t.val=0 ↔ t=(⟨0,Nat.zero_lt_succ Q⟩ : Fin (Q+1)) := by
    constructor
    · intro h; exact Fin.ext h
    · intro h; exact congrArg Fin.val h
  have ht₁ (t : Fin (Q+1)) : t.val=1 ↔ t=(⟨1,Nat.lt_succ_of_le (le_trans (by decide : 1 ≤ 2) hQ)⟩ : Fin (Q+1)) := by
    constructor
    · intro h; exact Fin.ext h
    · intro h; exact congrArg Fin.val h
  by_cases hj₀ : j.val=0
  · simp [hj₀,ht₁]; ring
  · by_cases hj₁ : j.val=1
    · simp [hj₁,ht₀]; ring
    · simp [hj₀,hj₁]

end Laughlin.Fock

end OAI
