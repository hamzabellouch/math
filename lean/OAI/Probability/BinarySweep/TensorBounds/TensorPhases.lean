import Mathlib
import OAI.Probability.BinarySweep.TensorBounds.TypeMass

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Density
variable {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
lemma wordCounts_le (n : ℕ) (w : Fin n → A) (a : A) : wordCounts w a ≤ n := by
  have h := Finset.single_le_sum (f := fun a => wordCounts w a)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  simpa only [wordCounts_sum, Fintype.card_fin] using h

lemma phase_star (n : ℕ) (j : ZMod (n+1)) :
    star (ZMod.stdAddChar j) = ZMod.stdAddChar (-j) := by
  change (starRingEnd ℂ) (ZMod.stdAddChar j) = _
  rw [AddChar.starComp_apply (by rw [ringChar.eq (ZMod (n+1)) (n+1)]; omega : 0 < ringChar (ZMod (n+1)))]
  rfl

omit [Fintype A] in
lemma phase_sum_prod (n : ℕ) (f : A → ZMod (n+1)) (s : Finset A) :
    ZMod.stdAddChar (∑ a ∈ s, f a) = ∏ a ∈ s, ZMod.stdAddChar (f a) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, Finset.prod_insert ha,
      AddChar.map_add_eq_mul, ih]

lemma phase_sum (n : ℕ) (b : A → ZMod (n+1)) :
    (∑ θ : A → ZMod (n+1), ZMod.stdAddChar (∑ a, θ a * b a)) =
      if b = 0 then ((n+1 : ℕ) : ℂ) ^ Fintype.card A else 0 := by
  classical
  simp_rw [phase_sum_prod]
  rw [← Fintype.prod_sum (fun a (x : ZMod (n+1)) => ZMod.stdAddChar (x * b a))]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar _), ZMod.card]
  by_cases hb : b = 0
  · simp [hb]
  · rw [ite_eq_right hb]
    obtain ⟨a, ha⟩ : ∃ a, b a ≠ 0 := by simpa only [funext_iff, not_forall, Pi.zero_apply] using hb
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [ha])

def tensorPhase (n : ℕ) (θ : A → ZMod (n+1)) (w : Fin n → A) : ℂ :=
  ∏ i, ZMod.stdAddChar (θ (w i))

lemma tensorPhase_counts (n : ℕ) (θ : A → ZMod (n+1)) (w : Fin n → A) :
    tensorPhase n θ w = ZMod.stdAddChar (∑ a, θ a * (wordCounts w a : ZMod (n+1))) := by
  rw [tensorPhase, prod_wordCounts (fun a => ZMod.stdAddChar (θ a)) w]
  simp_rw [phase_sum_prod, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  simp_rw [mul_comm]

lemma phase_pair_sum (n : ℕ) (w v : Fin n → A) :
    (∑ θ : A → ZMod (n+1), tensorPhase n θ w * star (tensorPhase n θ v)) =
      if wordCounts w = wordCounts v then ((n+1 : ℕ) : ℂ)^Fintype.card A else 0 := by
  simp_rw [tensorPhase_counts, phase_star, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg,
    ← Finset.sum_sub_distrib, ← mul_sub]
  rw [phase_sum]
  congr 1
  apply propext
  constructor
  · intro h
    apply Finsupp.ext
    intro a
    have h' := congrFun h a
    dsimp at h'
    have hh := congrArg ZMod.val (sub_eq_zero.mp h')
    simpa only [ZMod.val_natCast_of_lt (Nat.lt_succ_of_le (wordCounts_le n w a)),
      ZMod.val_natCast_of_lt (Nat.lt_succ_of_le (wordCounts_le n v a))] using hh
  · intro h
    simp only [h, sub_self, Pi.zero_def]

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density

variable {I T : Type*} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

def rankOne (v : I → ℂ) : Matrix I I ℂ := vecMulVec v (star v)

omit [DecidableEq I] in
lemma rankOne_psd (v : I → ℂ) : (rankOne v).PosSemidef := by
  let A : Matrix I Unit ℂ := fun i _ => v i
  have hA : rankOne v = A * Aᴴ := by
    ext i j
    change v i * star (v j) = ∑ _ : Unit, v i * star (v j)
    simp
  rw [hA]
  exact posSemidef_self_mul_conjTranspose A

def typeVector (f : I → T) (t : T) : I → ℂ := fun i => if f i = t then 1 else 0

def typeOnes (f : I → T) (t : T) : Matrix I I ℂ := rankOne (typeVector f t)

omit [Fintype I] [DecidableEq I] [Fintype T] in
lemma typeOnes_apply (f : I → T) (t : T) (i j : I) :
    typeOnes f t i j = if f i = t ∧ f j = t then 1 else 0 := by
  simp only [typeOnes, rankOne, vecMulVec, typeVector, Pi.star_apply]
  by_cases hi : f i = t <;> by_cases hj : f j = t <;> simp [hi, hj]

omit [DecidableEq I] [Fintype T] in
lemma typeOnes_psd (f : I → T) (t : T) : (typeOnes f t).PosSemidef := rankOne_psd _

omit [Fintype I] [DecidableEq I] in
lemma sum_typeOnes (f : I → T) (c : T → ℝ) (i j : I) :
    (∑ t, (c t : ℂ) • typeOnes f t : Matrix I I ℂ) i j = if f i = f j then (c (f i) : ℂ) else 0 := by
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, typeOnes_apply]
  rw [Finset.sum_eq_single (f i)]
  · by_cases h : f i = f j <;> simp [h, eq_comm]
  · intro b hb hba
    simp [Ne.symm hba]
  · simp

omit [DecidableEq I] in
lemma typeKernel_psd (f : I → T) (c : T → ℝ) (hc : ∀ t, 0 ≤ c t) :
    Matrix.PosSemidef (fun i j => if f i = f j then (c (f i) : ℂ) else 0 : Matrix I I ℂ) := by
  have hh : (fun i j => if f i = f j then (c (f i) : ℂ) else 0 : Matrix I I ℂ) =
      ∑ t, (c t : ℂ) • typeOnes f t := by ext i j; exact (sum_typeOnes f c i j).symm
  rw [hh]
  exact Matrix.posSemidef_sum _ (fun t _ => (typeOnes_psd f t).smul (by exact_mod_cast hc t))

omit [DecidableEq I] in
lemma typeKernel_mono (f : I → T) (c d : T → ℝ) (h : ∀ t, c t ≤ d t) :
    Matrix.PosSemidef ((fun i j => if f i = f j then (d (f i) : ℂ) else 0) -
      (fun i j => if f i = f j then (c (f i) : ℂ) else 0) : Matrix I I ℂ) := by
  have hkernel :
      ((fun i j => if f i = f j then (d (f i) : ℂ) else 0) -
        (fun i j => if f i = f j then (c (f i) : ℂ) else 0) : Matrix I I ℂ) =
      (fun i j => if f i = f j then ((d (f i) - c (f i) : ℝ) : ℂ) else 0) := by
    ext i j
    by_cases hh : f i = f j <;> simp [hh]
  rw [hkernel]
  exact typeKernel_psd f (fun t => d t - c t) (fun t => sub_nonneg.mpr (h t))

variable {A : Type*} [Fintype A] [DecidableEq A]

abbrev WordType (A : Type*) [Fintype A] [DecidableEq A] (n : ℕ) :=
  ↥(Finset.piAntidiag (Finset.univ : Finset A) n)

def wordType (n : ℕ) (w : Fin n → A) : WordType A n :=
  ⟨fun a => wordCounts w a, Finset.mem_piAntidiag.mpr ⟨by simpa using wordCounts_sum w, by simp⟩⟩

lemma wordType_eq_iff (n : ℕ) (w v : Fin n → A) :
    wordType n w = wordType n v ↔ wordCounts w = wordCounts v := by
  simp only [wordType, Subtype.ext_iff, funext_iff, Finsupp.ext_iff]

lemma wordType_total (n : ℕ) (c : WordType A n) : ∑ a, c.val a = n :=
  (Finset.mem_piAntidiag.mp c.property).1

lemma card_wordType (n : ℕ) (c : WordType A n) :
    Fintype.card {w : Fin n → A // wordType n w = c} = Nat.multinomial Finset.univ c.val := by
  have he : {w : Fin n → A // wordType n w = c} ≃
      {w : Fin n → A // ∀ a, wordCounts w a = c.val a} :=
    Equiv.subtypeEquivRight (fun w => by simp only [wordType, Subtype.ext_iff, funext_iff])
  rw [Fintype.card_congr he, card_words_counts_fun n c.val (wordType_total n c)]

def symmetricProjector (n : ℕ) : Matrix (Fin n → A) (Fin n → A) ℂ :=
  fun w v => if wordType n w = wordType n v then
    ((Nat.multinomial Finset.univ (wordType n w).val : ℝ)⁻¹ : ℂ) else 0

lemma symmetricProjector_psd (n : ℕ) : (symmetricProjector (A := A) n).PosSemidef := by
  unfold symmetricProjector
  simpa only [Complex.ofReal_inv] using typeKernel_psd (wordType (A := A) n)
    (fun c => (Nat.multinomial Finset.univ c.val : ℝ)⁻¹)
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _))

end BinaryCoordinateSweeps.Density

end

end OAI
