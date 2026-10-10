import OAI.Analysis.OInfinity.NuclearModel

namespace OAI

/-! # Finite words for the Fock approximation of O∞ -/

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

def oInfinityPositiveWord (N : ℕ) : {k : ℕ} → (Fin k → Fin N) → OInfinity
  | 0, _ => 1
  | _k + 1, w => oInfinityIsometry (w 0) * oInfinityPositiveWord N (Fin.tail w)

@[simp] lemma oInfinityPositiveWord_zero (N : ℕ) (w : Fin 0 → Fin N) :
    oInfinityPositiveWord N w = 1 := rfl

@[simp] lemma oInfinityPositiveWord_cons (N k : ℕ) (i : Fin N) (w : Fin k → Fin N) :
    oInfinityPositiveWord N (Fin.cons i w) =
      oInfinityIsometry i * oInfinityPositiveWord N w := by
  simp [oInfinityPositiveWord]

lemma oInfinityPositiveWord_relations (N k : ℕ) (v w : Fin k → Fin N) :
    star (oInfinityPositiveWord N v) * oInfinityPositiveWord N w =
      if v = w then 1 else 0 := by
  induction k with
  | zero => simp [Subsingleton.elim v w]
  | succ k ih =>
    have he : v = w ↔ v 0 = w 0 ∧ Fin.tail v = Fin.tail w := by
      constructor
      · intro h; subst w; exact ⟨rfl, rfl⟩
      · rintro ⟨h0, ht⟩
        rw [← Fin.cons_self_tail v, ← Fin.cons_self_tail w, h0, ht]
    change star (oInfinityIsometry (v 0) * oInfinityPositiveWord N (Fin.tail v)) *
      (oInfinityIsometry (w 0) * oInfinityPositiveWord N (Fin.tail w)) = _
    rw [star_mul]
    calc
      _ = star (oInfinityPositiveWord N (Fin.tail v)) *
          (star (oInfinityIsometry (v 0)) * oInfinityIsometry (w 0)) *
            oInfinityPositiveWord N (Fin.tail w) := by noncomm_ring
      _ = _ := by
        rw [oInfinityIsometry_relations]
        by_cases h0 : v 0 = w 0
        · rw [ite_eq_left (congrArg Fin.val h0), mul_one, ih]
          by_cases ht : Fin.tail v = Fin.tail w
          · simp only [ite_eq_left ht, ite_eq_left (he.mpr ⟨h0, ht⟩)]
          · rw [ite_eq_right ht, ite_eq_right (fun h => ht (he.mp h).2)]
        · have hn : ((v 0 : Fin N) : ℕ) ≠ ((w 0 : Fin N) : ℕ) :=
            fun h => h0 (Fin.ext h)
          rw [ite_eq_right hn, mul_zero, zero_mul,
            ite_eq_right (fun h => h0 (he.mp h).1)]

private lemma sum_fin_cons {M : Type*} [AddCommMonoid M] (N k : ℕ)
    (f : (Fin (k + 1) → Fin N) → M) :
    (∑ w, f w) = ∑ i : Fin N, ∑ w : Fin k → Fin N, f (Fin.cons i w) := by
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin N)).sum_comp]
  exact Fintype.sum_prod_type _

lemma oInfinityPositiveWord_sum_range (N k : ℕ) :
    (∑ w : Fin k → Fin N,
      oInfinityPositiveWord N w * star (oInfinityPositiveWord N w)) =
      oInfinityLevel N k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_fin_cons]
    simp only [oInfinityPositiveWord_cons, star_mul]
    calc
      _ = ∑ i : Fin N, oInfinityIsometry i *
          (∑ w : Fin k → Fin N,
            oInfinityPositiveWord N w * star (oInfinityPositiveWord N w)) *
          star (oInfinityIsometry i) := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      _ = _ := by rw [ih]; rfl

def oInfinityFiniteVacuum (N : ℕ) : OInfinity := 1 - oInfinityLevel N 1

lemma oInfinityPositiveWord_sum_vacuum (N k : ℕ) :
    (∑ w : Fin k → Fin N,
      oInfinityPositiveWord N w * oInfinityFiniteVacuum N *
        star (oInfinityPositiveWord N w)) = oInfinityLevelDifference N k := by
  simp only [oInfinityFiniteVacuum, mul_sub, mul_one, sub_mul,
    Finset.sum_sub_distrib, oInfinityPositiveWord_sum_range]
  unfold oInfinityLevelDifference
  congr 1
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_fin_cons]
    simp only [oInfinityPositiveWord_cons, star_mul]
    calc
      _ = ∑ i : Fin N, oInfinityIsometry i *
          (∑ w : Fin k → Fin N,
            oInfinityPositiveWord N w * oInfinityLevel N 1 *
              star (oInfinityPositiveWord N w)) * star (oInfinityIsometry i) := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      _ = _ := by rw [ih]; rfl

lemma oInfinityPositiveWord_fock (N k : ℕ) (w : Fin k → Fin N) :
    oInfinityEvaluation fockRepresentation (oInfinityPositiveWord N w) fockVacuum =
      lp.single 2 (List.ofFn fun i => (w i : ℕ)) 1 := by
  induction k with
  | zero =>
    simp only [oInfinityPositiveWord_zero, map_one]
    rfl
  | succ k ih =>
    change oInfinityEvaluation fockRepresentation
      (oInfinityIsometry (w 0) * oInfinityPositiveWord N (Fin.tail w)) fockVacuum = _
    rw [map_mul]
    change fockShift (w 0) (oInfinityEvaluation fockRepresentation
      (oInfinityPositiveWord N (Fin.tail w)) fockVacuum) = _
    rw [ih, fockShift_single, List.ofFn_succ]
    rfl

local instance : PartialOrder OInfinity := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing OInfinity := CStarAlgebra.spectralOrderedRing _

lemma oInfinityFiniteVacuum_nonneg (N : ℕ) : 0 ≤ oInfinityFiniteVacuum N := by
  unfold oInfinityFiniteVacuum
  apply sub_nonneg.mpr
  have h : oInfinityLevel N 1 ≤ oInfinityLevel N 0 :=
    oInfinityLevel_antitone N (show 0 ≤ 1 by omega)
  simpa only [oInfinityLevel_zero] using h

lemma oInfinityFiniteVacuum_star (N : ℕ) :
    star (oInfinityFiniteVacuum N) = oInfinityFiniteVacuum N :=
  (IsSelfAdjoint.of_nonneg (oInfinityFiniteVacuum_nonneg N)).star_eq

lemma oInfinityFiniteVacuum_idempotent (N : ℕ) :
    oInfinityFiniteVacuum N * oInfinityFiniteVacuum N = oInfinityFiniteVacuum N := by
  have h := oInfinityLevel_idempotent N 1
  unfold oInfinityFiniteVacuum
  noncomm_ring [h]

lemma oInfinityFiniteVacuum_generator (N : ℕ) (i : Fin N) :
    oInfinityFiniteVacuum N * oInfinityIsometry i = 0 := by
  have h (j : Fin N) : oInfinityIsometry j * star (oInfinityIsometry j) *
      oInfinityIsometry i = if j = i then oInfinityIsometry i else 0 := by
    rw [mul_assoc, oInfinityIsometry_relations]
    by_cases he : j = i
    · subst j
      simp
    · have hn : (j : ℕ) ≠ (i : ℕ) := fun h => he (Fin.ext h)
      simp [hn, he]
  have hsum : oInfinityLevel N 1 * oInfinityIsometry i = oInfinityIsometry i := by
    change (∑ j : Fin N, oInfinityIsometry j * 1 * star (oInfinityIsometry j)) *
      oInfinityIsometry i = _
    simp only [mul_one, Finset.sum_mul, h]
    simp
  unfold oInfinityFiniteVacuum
  rw [sub_mul, one_mul, hsum, sub_self]

lemma oInfinityFiniteVacuum_positiveWord (N : ℕ) {k : ℕ} (hk : 0 < k)
    (w : Fin k → Fin N) :
    oInfinityFiniteVacuum N * oInfinityPositiveWord N w = 0 := by
  cases k with
  | zero => omega
  | succ k =>
    change oInfinityFiniteVacuum N *
      (oInfinityIsometry (w 0) * oInfinityPositiveWord N (Fin.tail w)) = 0
    rw [← mul_assoc, oInfinityFiniteVacuum_generator, zero_mul]

end WeakPureInfiniteness

end

end OAI
