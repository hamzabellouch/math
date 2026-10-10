import OAI.Analysis.OInfinity.FockRangeProjection

namespace OAI

/-! # Finite Fock coefficients from an unused Cuntz generator

For words in the first `N` generators, the next generator has exactly the
vacuum annihilation relations.  This realizes every finite Fock compression
of such a word as a corner in the Cuntz algebra itself.
-/

noncomputable section
open scoped CStarAlgebra InnerProductSpace

namespace WeakPureInfiniteness

local instance : SMulWithZero ℂ OInfinity :=
  @MulActionWithZero.toSMulWithZero ℂ OInfinity _ _
    (@Module.toMulActionWithZero ℂ OInfinity _ _ inferInstance)
local instance : DistribSMul ℂ OInfinity :=
  @DistribMulAction.toDistribSMul ℂ OInfinity _ _
    (@Module.toDistribMulAction ℂ OInfinity _ _ inferInstance)

def oInfinityVacuumWord (N : ℕ) : List (Fin N) → OInfinity
  | [] => oInfinityIsometry N
  | p :: w => oInfinityIsometry p * oInfinityVacuumWord N w

lemma oInfinityVacuumWord_relations (N : ℕ) (v w : List (Fin N)) :
    star (oInfinityVacuumWord N v) * oInfinityVacuumWord N w =
      if v = w then 1 else 0 := by
  induction v generalizing w with
  | nil =>
    cases w with
    | nil => simp [oInfinityVacuumWord, oInfinityIsometry_relations]
    | cons q w =>
      simp only [oInfinityVacuumWord, (List.cons_ne_nil q w).symm, ite_false]
      rw [← mul_assoc, oInfinityIsometry_relations,
        ite_eq_right (ne_of_gt q.isLt), zero_mul]
  | cons p v ih =>
    cases w with
    | nil =>
      simp only [oInfinityVacuumWord, star_mul, List.cons_ne_nil, ite_false]
      rw [mul_assoc, oInfinityIsometry_relations, ite_eq_right (ne_of_lt p.isLt), mul_zero]
    | cons q w =>
      change star (oInfinityIsometry p * oInfinityVacuumWord N v) *
        (oInfinityIsometry q * oInfinityVacuumWord N w) = _
      rw [star_mul]
      calc
        _ = star (oInfinityVacuumWord N v) *
          (star (oInfinityIsometry p) * oInfinityIsometry q) * oInfinityVacuumWord N w := by
            noncomm_ring
        _ = _ := by
          rw [oInfinityIsometry_relations]
          by_cases hpq : p = q
          · subst q
            simp only [ite_true, mul_one, ih, List.cons.injEq, true_and]
          · have hpq' : p.val ≠ q.val := fun h => hpq (Fin.ext h)
            simp [hpq', hpq]

def finiteAlphabetWord (N : ℕ) (z : List (Fin N × Bool)) : OInfinity :=
  cuntzWord oInfinityIsometry (z.map fun p => (p.1.val, p.2))

@[simp] lemma finiteAlphabetWord_nil (N : ℕ) : finiteAlphabetWord N [] = 1 := rfl

@[simp] lemma finiteAlphabetWord_cons (N : ℕ) (p : Fin N) (b : Bool)
    (z : List (Fin N × Bool)) :
    finiteAlphabetWord N ((p, b) :: z) =
      (if b then oInfinityIsometry p else star (oInfinityIsometry p)) * finiteAlphabetWord N z := rfl

def finiteAlphabetPop {N : ℕ} (p : Fin N) : List (Fin N) → Option (List (Fin N))
  | [] => none
  | q :: w => if p = q then some w else none

def finiteAlphabetRun (N : ℕ) : List (Fin N × Bool) → List (Fin N) → Option (List (Fin N))
  | [], w => some w
  | (p, true) :: z, w => (finiteAlphabetRun N z w).map (List.cons p)
  | (p, false) :: z, w => (finiteAlphabetRun N z w).bind (finiteAlphabetPop p)

def vacuumRunValue {N : ℕ} (v : Option (List (Fin N))) : OInfinity :=
  v.elim 0 (oInfinityVacuumWord N)

lemma oInfinityVacuumWord_annihilate {N : ℕ} (p : Fin N) (w : List (Fin N)) :
    star (oInfinityIsometry p) * oInfinityVacuumWord N w =
      vacuumRunValue (finiteAlphabetPop p w) := by
  cases w with
  | nil =>
    simp only [oInfinityVacuumWord, oInfinityIsometry_relations,
      ite_eq_right (ne_of_lt p.isLt), finiteAlphabetPop, vacuumRunValue, Option.elim_none]
  | cons q w =>
    rw [oInfinityVacuumWord, ← mul_assoc, oInfinityIsometry_relations]
    by_cases hpq : p = q
    · subst q
      simp [finiteAlphabetPop, vacuumRunValue]
    · have hpq' : p.val ≠ q.val := fun h => hpq (Fin.ext h)
      simp [hpq', hpq, finiteAlphabetPop, vacuumRunValue]

lemma finiteAlphabetWord_vacuum_action {N : ℕ} (z : List (Fin N × Bool))
    (w : List (Fin N)) :
    finiteAlphabetWord N z * oInfinityVacuumWord N w =
      vacuumRunValue (finiteAlphabetRun N z w) := by
  induction z with
  | nil => simp [finiteAlphabetRun, vacuumRunValue]
  | cons pb z ih =>
    rcases pb with ⟨p, b⟩
    cases b with
    | false =>
      change (star (oInfinityIsometry p) * finiteAlphabetWord N z) *
        oInfinityVacuumWord N w = _
      rw [mul_assoc, ih]
      cases hrun : finiteAlphabetRun N z w with
      | none => simp [finiteAlphabetRun, hrun, vacuumRunValue]
      | some v =>
        simpa only [finiteAlphabetRun, hrun, Option.bind_some, vacuumRunValue,
          Option.elim_some] using oInfinityVacuumWord_annihilate p v
    | true =>
      change (oInfinityIsometry p * finiteAlphabetWord N z) *
        oInfinityVacuumWord N w = _
      rw [mul_assoc, ih]
      cases hrun : finiteAlphabetRun N z w with
      | none => simp [finiteAlphabetRun, hrun, vacuumRunValue]
      | some v => simp [finiteAlphabetRun, hrun, vacuumRunValue, oInfinityVacuumWord]

def finiteAlphabetBasis {N : ℕ} (w : List (Fin N)) : FockSpace :=
  lp.single 2 (w.map Fin.val) 1

def fockRunValue {N : ℕ} (v : Option (List (Fin N))) : FockSpace :=
  v.elim 0 finiteAlphabetBasis

lemma finiteAlphabetBasis_create {N : ℕ} (p : Fin N) (w : List (Fin N)) :
    fockShift p (finiteAlphabetBasis w) = finiteAlphabetBasis (p :: w) := by
  simp only [finiteAlphabetBasis, fockShift_single, List.map_cons]

lemma finiteAlphabetBasis_annihilate {N : ℕ} (p : Fin N) (w : List (Fin N)) :
    (fockShift p).toContinuousLinearMap.adjoint (finiteAlphabetBasis w) =
      fockRunValue (finiteAlphabetPop p w) := by
  cases w with
  | nil => simp [finiteAlphabetBasis, fockShift_adjoint_single_nil, finiteAlphabetPop, fockRunValue]
  | cons q w =>
    simp only [finiteAlphabetBasis, List.map_cons, fockShift_adjoint_single_cons,
      finiteAlphabetPop]
    by_cases hpq : p = q
    · subst q; simp [fockRunValue, finiteAlphabetBasis]
    · have hpq' : p.val ≠ q.val := fun h => hpq (Fin.ext h)
      simp [hpq', hpq, fockRunValue]

lemma finiteAlphabetWord_fock_action {N : ℕ} (z : List (Fin N × Bool))
    (w : List (Fin N)) :
    fockOperatorRepresentation (finiteAlphabetWord N z) (finiteAlphabetBasis w) =
      fockRunValue (finiteAlphabetRun N z w) := by
  induction z with
  | nil => simp [finiteAlphabetRun, fockRunValue]
  | cons pb z ih =>
    rcases pb with ⟨p, b⟩
    cases b with
    | false =>
      change (fockOperatorRepresentation (star (oInfinityIsometry p) * finiteAlphabetWord N z))
        (finiteAlphabetBasis w) = _
      rw [map_mul, mul_apply_eq_comp, ih]
      change (fockShift p).toContinuousLinearMap.adjoint (fockRunValue (finiteAlphabetRun N z w)) = _
      cases hrun : finiteAlphabetRun N z w with
      | none => simp [finiteAlphabetRun, hrun, fockRunValue]
      | some v =>
        simpa only [finiteAlphabetRun, hrun, Option.bind_some, fockRunValue,
          Option.elim_some] using finiteAlphabetBasis_annihilate p v
    | true =>
      change (fockOperatorRepresentation (oInfinityIsometry p * finiteAlphabetWord N z))
        (finiteAlphabetBasis w) = _
      rw [map_mul, mul_apply_eq_comp, ih]
      change fockShift p (fockRunValue (finiteAlphabetRun N z w)) = _
      cases hrun : finiteAlphabetRun N z w with
      | none => simp [finiteAlphabetRun, hrun, fockRunValue]
      | some v =>
        simpa only [finiteAlphabetRun, hrun, Option.map_some, fockRunValue,
          Option.elim_some] using finiteAlphabetBasis_create p v

lemma finiteAlphabetBasis_inner {N : ℕ} (v w : List (Fin N)) :
    inner ℂ (finiteAlphabetBasis v) (finiteAlphabetBasis w) = if v = w then 1 else 0 := by
  have he : v.map Fin.val = w.map Fin.val ↔ v = w :=
    (List.map_injective_iff.mpr Fin.val_injective).eq_iff
  simp [finiteAlphabetBasis, lp.inner_single_left, lp.single_apply, Pi.single_apply, he]

lemma finiteAlphabetWord_coefficient {N : ℕ} (z : List (Fin N × Bool))
    (v w : List (Fin N)) :
    star (oInfinityVacuumWord N v) * finiteAlphabetWord N z * oInfinityVacuumWord N w =
      (inner ℂ (finiteAlphabetBasis v)
        (fockOperatorRepresentation (finiteAlphabetWord N z) (finiteAlphabetBasis w))) •
          (1 : OInfinity) := by
  rw [mul_assoc, finiteAlphabetWord_vacuum_action, finiteAlphabetWord_fock_action]
  cases hrun : finiteAlphabetRun N z w with
  | none => simp [vacuumRunValue, fockRunValue]
  | some t =>
    simp only [vacuumRunValue, fockRunValue, Option.elim_some,
      oInfinityVacuumWord_relations, finiteAlphabetBasis_inner]
    split_ifs <;> simp

lemma oInfinityVacuumWord_ofFn (N k : ℕ) (w : Fin k → Fin N) :
    oInfinityVacuumWord N (List.ofFn w) =
      oInfinityPositiveWord N w * oInfinityIsometry N := by
  induction k with
  | zero => simp [oInfinityVacuumWord]
  | succ k ih =>
    rw [List.ofFn_succ]
    change oInfinityIsometry (w 0) * oInfinityVacuumWord N (List.ofFn (Fin.tail w)) =
      (oInfinityIsometry (w 0) * oInfinityPositiveWord N (Fin.tail w)) * oInfinityIsometry N
    rw [ih, mul_assoc]

def finiteVacuumCorner (N m : ℕ) (i : FiniteFockIndex N m) : OInfinity :=
  finiteFockAlgebraWord i * oInfinityIsometry N

lemma finiteVacuumCorner_relations (N m : ℕ) (i j : FiniteFockIndex N m) :
    star (finiteVacuumCorner N m i) * finiteVacuumCorner N m j =
      if i = j then 1 else 0 := by
  have he : List.ofFn i.2 = List.ofFn j.2 ↔ i = j := by
    constructor
    · intro h
      apply finiteFockWord_injective N m
      have hh := congrArg (List.map Fin.val) h
      simpa only [List.map_ofFn, Function.comp_def, finiteFockWord] using hh
    · rintro rfl; rfl
  change star (oInfinityPositiveWord N i.2 * oInfinityIsometry N) *
    (oInfinityPositiveWord N j.2 * oInfinityIsometry N) = _
  rw [← oInfinityVacuumWord_ofFn, ← oInfinityVacuumWord_ofFn, oInfinityVacuumWord_relations]
  simp only [he]

lemma finiteVacuumCorner_compression {N m : ℕ} (z : List (Fin N × Bool))
    (i j : FiniteFockIndex N m) :
    star (finiteVacuumCorner N m i) * finiteAlphabetWord N z * finiteVacuumCorner N m j =
      oInfinityFockCompression N m (finiteAlphabetWord N z) i j • (1 : OInfinity) := by
  have hi : finiteVacuumCorner N m i = oInfinityVacuumWord N (List.ofFn i.2) :=
    (oInfinityVacuumWord_ofFn N i.1.val i.2).symm
  have hj : finiteVacuumCorner N m j = oInfinityVacuumWord N (List.ofFn j.2) :=
    (oInfinityVacuumWord_ofFn N j.1.val j.2).symm
  rw [hi, hj, finiteAlphabetWord_coefficient, oInfinityFockCompression_apply]
  simp only [finiteAlphabetBasis, finiteFockVector, finiteFockWord, List.map_ofFn, Function.comp_def]

lemma exists_finiteAlphabet_lift {N : ℕ} (w : List (ℕ × Bool))
    (hw : ∀ p ∈ w, p.1 < N) :
    ∃ z : List (Fin N × Bool), z.map (fun p => (p.1.val, p.2)) = w := by
  induction w with
  | nil => exact ⟨[], rfl⟩
  | cons p w ih =>
    obtain ⟨z, hz⟩ := ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))
    refine ⟨(⟨p.1, hw p (List.mem_cons_self ..)⟩, p.2) :: z, ?_⟩
    simp only [List.map_cons, hz, Prod.mk.eta]

lemma finiteVacuumCorner_cuntzWord {N m : ℕ} (w : List (ℕ × Bool))
    (hw : ∀ p ∈ w, p.1 < N) (i j : FiniteFockIndex N m) :
    star (finiteVacuumCorner N m i) * cuntzWord oInfinityIsometry w * finiteVacuumCorner N m j =
      oInfinityFockCompression N m (cuntzWord oInfinityIsometry w) i j • (1 : OInfinity) := by
  obtain ⟨z, rfl⟩ := exists_finiteAlphabet_lift w hw
  exact finiteVacuumCorner_compression z i j

lemma finiteVacuumCorner_polynomial {N m : ℕ} (c : List (ℕ × Bool) →₀ ℂ)
    (hc : ∀ w ∈ c.support, ∀ p ∈ w, p.1 < N) (i j : FiniteFockIndex N m) :
    star (finiteVacuumCorner N m i) * cuntzPolynomial oInfinityIsometry c *
      finiteVacuumCorner N m j =
    oInfinityFockCompression N m (cuntzPolynomial oInfinityIsometry c) i j • (1 : OInfinity) := by
  have hentry (f : List (ℕ × Bool) → CStarMatrix (FiniteFockIndex N m) (FiniteFockIndex N m) ℂ) :
      (∑ w ∈ c.support, f w) i j = ∑ w ∈ c.support, f w i j :=
    map_sum (matrixEntryLinear i j) f c.support
  simp only [cuntzPolynomial, Finsupp.sum, Finset.mul_sum, Finset.sum_mul,
    mul_smul_comm, smul_mul_assoc, map_sum, map_smul, hentry,
    CStarMatrix.smul_apply, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro w hw
  rw [finiteVacuumCorner_cuntzWord w (hc w hw), smul_smul, smul_eq_mul]

lemma exists_polynomial_alphabet_bound (c : List (ℕ × Bool) →₀ ℂ) :
    ∃ N : ℕ, ∀ w ∈ c.support, ∀ p ∈ w, p.1 < N := by
  let s := c.support.biUnion (fun w => w.toFinset.image Prod.fst)
  refine ⟨s.sup id + 1, ?_⟩
  intro w hw p hp
  apply Nat.lt_succ_of_le
  apply Finset.le_sup (f := id)
  exact Finset.mem_biUnion.mpr ⟨w, hw,
    Finset.mem_image.mpr ⟨p, List.mem_toFinset.mpr hp, rfl⟩⟩

end WeakPureInfiniteness

end

end OAI
