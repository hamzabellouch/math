import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Defs
import OAI.NumberTheory.Catalan.Polynomial.FixedBaseCertificateTransfer

namespace OAI

section

noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem palindromicRatResidue_prod {p : ℕ} [Fact p.Prime] {ι : Type*}
    (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, ((f i).den : ZMod p) ≠ 0) :
    ((∏ i ∈ s, f i).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (∏ i ∈ s, f i) =
        ∏ i ∈ s, palindromicRatResidue p (f i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => intro hf; simp [palindromicRatResidue]
  | @insert a s ha ih =>
    intro hf
    have hfa := hf a (Finset.mem_insert_self a s)
    have hs := ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
    simp only [Finset.prod_insert ha]
    refine ⟨(rational_residue_mul hfa hs.1).1, ?_⟩
    rw [palindromicRatResidue_mul hfa hs.1, hs.2]

theorem palindromicRatResidue_det {p : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℚ)
    (hentry : ∀ i j, ((A i j).den : ZMod p) ≠ 0) :
    (A.det.den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p A.det =
        Matrix.det (fun i j => palindromicRatResidue p (A i j)) := by
  have hprod (σ : Equiv.Perm ι) :=
    palindromicRatResidue_prod (p := p) Finset.univ
      (fun i => A (σ i) i) (fun i _ => hentry (σ i) i)
  have hsum := palindromicRatResidue_int_sum (p := p) Finset.univ
    (fun σ : Equiv.Perm ι => (Equiv.Perm.sign σ : ℤ))
    (fun σ => ∏ i, A (σ i) i) (fun σ _ => (hprod σ).1)
  constructor
  · rw [Matrix.det_apply']
    exact hsum.1
  · calc
      palindromicRatResidue p A.det = palindromicRatResidue p
          (∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℚ) * ∏ i, A (σ i) i) :=
        congrArg (palindromicRatResidue p) (Matrix.det_apply' A)
      _ =
          ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ZMod p) *
            palindromicRatResidue p (∏ i, A (σ i) i) := hsum.2
      _ = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ZMod p) *
          ∏ i, palindromicRatResidue p (A (σ i) i) := by
        apply Finset.sum_congr rfl
        intro σ hσ
        rw [(hprod σ).2]
      _ = Matrix.det (fun i j => palindromicRatResidue p (A i j)) :=
        (Matrix.det_apply' (fun i j => palindromicRatResidue p (A i j))).symm

theorem fixedB0_det_residue {p : ℕ} [Fact p.Prime] (hp : 260 < p) :
    (fixedB0.det.den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p fixedB0.det = (fixedB0Residue p).det := by
  exact palindromicRatResidue_det fixedB0 (fixedB0_den_ne_zero hp)

theorem fixedB1_det_residue {p : ℕ} [Fact p.Prime] (hp : 260 < p) :
    (fixedB1.det.den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p fixedB1.det = (fixedB1Residue p).det := by
  exact palindromicRatResidue_det fixedB1 (fixedB1_den_ne_zero hp)

theorem fixedMatrix_one_det_residue {p : ℕ} [Fact p.Prime] (hp : 260 < p) :
    ((fixedMatrix 1).det.den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (fixedMatrix 1).det =
        (fixedB0Residue p + fixedB1Residue p).det := by
  have hentry (r k : Fin 48) : ((fixedMatrix 1 r k).den : ZMod p) ≠ 0 := by
    rw [fixedMatrix_one]
    exact (rational_residue_add (fixedB0_den_ne_zero hp r k)
      (fixedB1_den_ne_zero hp r k)).1
  have hdet := palindromicRatResidue_det (fixedMatrix 1) hentry
  have hmatrix : (fun r k => palindromicRatResidue p (fixedMatrix 1 r k) :
      Matrix (Fin 48) (Fin 48) (ZMod p)) = fixedB0Residue p + fixedB1Residue p := by
    ext r k
    exact fixedMatrix_one_residue hp r k
  exact ⟨hdet.1, hdet.2.trans (congrArg Matrix.det hmatrix)⟩

theorem fixedMatrix_neg_one_det_residue {p : ℕ} [Fact p.Prime] (hp : 260 < p) :
    ((fixedMatrix (-1)).det.den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (fixedMatrix (-1)).det =
        (fixedB0Residue p - fixedB1Residue p).det := by
  have hentry (r k : Fin 48) : ((fixedMatrix (-1) r k).den : ZMod p) ≠ 0 := by
    rw [fixedMatrix_neg_one]
    exact (rational_residue_sub (fixedB0_den_ne_zero hp r k)
      (fixedB1_den_ne_zero hp r k)).1
  have hdet := palindromicRatResidue_det (fixedMatrix (-1)) hentry
  have hmatrix : (fun r k => palindromicRatResidue p (fixedMatrix (-1) r k) :
      Matrix (Fin 48) (Fin 48) (ZMod p)) = fixedB0Residue p - fixedB1Residue p := by
    ext r k
    exact fixedMatrix_neg_one_residue hp r k
  exact ⟨hdet.1, hdet.2.trans (congrArg Matrix.det hmatrix)⟩

theorem rational_det_ne_zero_of_residue_det_ne_zero {p : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℚ)
    (hentry : ∀ i j, ((A i j).den : ZMod p) ≠ 0)
    (hcertificate :
      Matrix.det (fun i j => palindromicRatResidue p (A i j)) ≠ 0) :
    A.det ≠ 0 := by
  intro hzero
  apply hcertificate
  rw [← (palindromicRatResidue_det A hentry).2, hzero]
  simp [palindromicRatResidue]

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

theorem palindromicRatResidue_ne_zero_of_bounds {p : ℕ} [Fact p.Prime]
    (x : ℚ) (hx : x ≠ 0) (hn : x.num.natAbs < p) (hd : x.den < p) :
    palindromicRatResidue p x ≠ 0 := by
  unfold palindromicRatResidue
  apply div_ne_zero
  · intro hz
    have hdiv : p ∣ x.num.natAbs :=
      Int.natCast_dvd.mp
        ((ZMod.intCast_zmod_eq_zero_iff_dvd x.num p).mp hz)
    exact (Nat.not_dvd_of_pos_of_lt
      (Nat.pos_of_ne_zero
        (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hx))) hn) hdiv
  · intro hz
    exact (Nat.not_dvd_of_pos_of_lt x.den_pos hd)
      ((ZMod.natCast_eq_zero_iff x.den p).mp hz)

def fixedDeterminantPrimeCutoff : ℕ :=
  260 + (fixedMatrix 0).det.num.natAbs + (fixedMatrix 0).det.den +
    (fixedMatrix 1).det.num.natAbs + (fixedMatrix 1).det.den +
    (fixedMatrix (-1)).det.num.natAbs + (fixedMatrix (-1)).det.den

theorem fixedDeterminantPrimeCutoff_ge_260 : 260 ≤ fixedDeterminantPrimeCutoff := by
  unfold fixedDeterminantPrimeCutoff
  omega

theorem fixedDeterminants_residue_ne_zero_of_lt {p : ℕ} [Fact p.Prime]
    (hzero : (fixedMatrix 0).det ≠ 0)
    (hplus : (fixedMatrix 1).det ≠ 0)
    (hminus : (fixedMatrix (-1)).det ≠ 0)
    (hp : fixedDeterminantPrimeCutoff < p) :
    palindromicRatResidue p (fixedMatrix 0).det ≠ 0 ∧
      palindromicRatResidue p (fixedMatrix 1).det ≠ 0 ∧
      palindromicRatResidue p (fixedMatrix (-1)).det ≠ 0 := by
  unfold fixedDeterminantPrimeCutoff at hp
  exact ⟨palindromicRatResidue_ne_zero_of_bounds _ hzero (by omega) (by omega),
    palindromicRatResidue_ne_zero_of_bounds _ hplus (by omega) (by omega),
    palindromicRatResidue_ne_zero_of_bounds _ hminus (by omega) (by omega)⟩

theorem fixedDeterminants_mod_prime_ne_zero_of_lt {p : ℕ} [Fact p.Prime]
    (hzero : (fixedMatrix 0).det ≠ 0)
    (hplus : (fixedMatrix 1).det ≠ 0)
    (hminus : (fixedMatrix (-1)).det ≠ 0)
    (hp : fixedDeterminantPrimeCutoff < p) :
    (fixedB0Residue p).det ≠ 0 ∧
      (fixedB0Residue p + fixedB1Residue p).det ≠ 0 ∧
      (fixedB0Residue p - fixedB1Residue p).det ≠ 0 := by
  have hp260 : 260 < p := lt_of_le_of_lt fixedDeterminantPrimeCutoff_ge_260 hp
  have h := fixedDeterminants_residue_ne_zero_of_lt hzero hplus hminus hp
  constructor
  · rw [← (fixedB0_det_residue hp260).2]
    simpa only [fixedMatrix_zero] using h.1
  constructor
  · rw [← (fixedMatrix_one_det_residue hp260).2]
    exact h.2.1
  · rw [← (fixedMatrix_neg_one_det_residue hp260).2]
    exact h.2.2

theorem fixedDeterminants_mod_prime_eventually_ne_zero
    (hzero : (fixedMatrix 0).det ≠ 0)
    (hplus : (fixedMatrix 1).det ≠ 0)
    (hminus : (fixedMatrix (-1)).det ≠ 0) :
    ∃ C : ℕ, ∀ (p : ℕ) [Fact p.Prime], C < p →
      (fixedB0Residue p).det ≠ 0 ∧
        (fixedB0Residue p + fixedB1Residue p).det ≠ 0 ∧
        (fixedB0Residue p - fixedB1Residue p).det ≠ 0 := by
  refine ⟨fixedDeterminantPrimeCutoff, ?_⟩
  intro p hpPrime hp
  exact fixedDeterminants_mod_prime_ne_zero_of_lt hzero hplus hminus hp

theorem fixedDeterminants_mod_prime_ne_zero_of_base_certificate
    (A : Matrix (Fin 49) (Fin 48) ℤ) (den : ℤ)
    (hbase : ∀ (r : Fin 49) (k : Fin 48),
      (A r k : ℚ) = (den : ℚ) * fixedBaseEntryRat r k)
    (hzero : ((fixedIntegerMatrix A 0).map
      (fun x : ℤ => (x : ZMod 101))).det ≠ 0)
    (hplus : ((fixedIntegerMatrix A 1).map
      (fun x : ℤ => (x : ZMod 101))).det ≠ 0)
    (hminus : ((fixedIntegerMatrix A (-1)).map
      (fun x : ℤ => (x : ZMod 101))).det ≠ 0)
    {p : ℕ} [Fact p.Prime] (hp : fixedDeterminantPrimeCutoff < p) :
    (fixedB0Residue p).det ≠ 0 ∧
      (fixedB0Residue p + fixedB1Residue p).det ≠ 0 ∧
      (fixedB0Residue p - fixedB1Residue p).det ≠ 0 := by
  apply fixedDeterminants_mod_prime_ne_zero_of_lt ?_ ?_ ?_ hp
  · simpa only [Int.cast_zero] using
      fixedMatrix_det_ne_zero_of_base_certificate A den 0 hbase hzero
  · simpa only [Int.cast_one] using
      fixedMatrix_det_ne_zero_of_base_certificate A den 1 hbase hplus
  · simpa only [Int.cast_neg, Int.cast_one] using
      fixedMatrix_det_ne_zero_of_base_certificate A den (-1) hbase hminus

end InternalCatalan

end

end

end OAI
