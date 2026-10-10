import OAI.LinearAlgebra.CirculantHadamard.MatrixBridge
import OAI.LinearAlgebra.CirculantHadamard.CyclicRing

namespace OAI

noncomputable section

namespace CirculantHadamard

open scoped BigOperators

/-- Every literal integer coefficient is a sign. -/
def CyclicSignRow {n : ℕ} (f : CyclicRing.Elem ℤ n) : Prop :=
  ∀ a, IsSign (f.coeff a)

section PositiveOrder

variable {n : ℕ} [NeZero n]

/-- The cyclic group-ring element whose coefficients are the given first row. -/
def cyclicRow (h : Fin n → ℤ) : CyclicRing.Elem ℤ n :=
  CyclicRing.ofCoeffs (fun a => h ((ZMod.finEquiv n).symm a))

/-- Recover the integer first row without changing the cyclic orientation. -/
def integerRow (f : CyclicRing.Elem ℤ n) : Fin n → ℤ :=
  fun j => f.coeff (ZMod.finEquiv n j)

@[simp] theorem cyclicRow_apply (h : Fin n → ℤ) (a : ZMod n) :
    (cyclicRow h).coeff a = h ((ZMod.finEquiv n).symm a) := by
  simp [cyclicRow]

@[simp] theorem integerRow_apply (f : CyclicRing.Elem ℤ n) (j : Fin n) :
    integerRow f j = f.coeff (ZMod.finEquiv n j) := rfl

@[simp] theorem cyclicRow_integerRow (f : CyclicRing.Elem ℤ n) :
    cyclicRow (integerRow f) = f := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro a
  simp [integerRow]

@[simp] theorem integerRow_cyclicRow (h : Fin n → ℤ) :
    integerRow (cyclicRow h) = h := by
  funext j
  simp [integerRow]

theorem sum_cyclicRow (h : Fin n → ℤ) :
    (∑ a : ZMod n, (cyclicRow h).coeff a) = ∑ j : Fin n, h j := by
  simpa only [cyclicRow_apply, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv,
    RingEquiv.symm_apply_apply] using
    ((ZMod.finEquiv n).toEquiv.sum_comp (fun a : ZMod n => (cyclicRow h).coeff a)).symm

theorem cyclicSignRow_cyclicRow_iff (h : Fin n → ℤ) :
    CyclicSignRow (cyclicRow h) ↔ ∀ j, IsSign (h j) := by
  constructor
  · intro hf j
    simpa using hf (ZMod.finEquiv n j)
  · intro hh a
    simpa using hh ((ZMod.finEquiv n).symm a)

/-- The norm coefficient uses the same `j - a` orientation as the row Gram. -/
theorem cyclicRow_norm_apply (h : Fin n → ℤ) (a : Fin n) :
    (cyclicRow h * CyclicRing.ringStar (cyclicRow h)).coeff (ZMod.finEquiv n a) =
      ∑ j : Fin n, h j * h (j - a) := by
  rw [CyclicRing.mul_ringStar_apply]
  simpa only [cyclicRow_apply, map_sub, RingEquiv.toEquiv_eq_coe,
    RingEquiv.coe_toEquiv, RingEquiv.symm_apply_apply, star_trivial] using
    ((ZMod.finEquiv n).toEquiv.sum_comp
      (fun j : ZMod n =>
        (cyclicRow h).coeff j * star ((cyclicRow h).coeff (j - ZMod.finEquiv n a)))).symm

theorem cyclicRow_norm_iff_autocorrelation (h : Fin n → ℤ) :
    cyclicRow h * CyclicRing.ringStar (cyclicRow h) =
        CyclicRing.scalar n (n : ℤ) ↔
      ∀ a : Fin n, (∑ j : Fin n, h j * h (j - a)) =
        if a = 0 then (n : ℤ) else 0 := by
  constructor
  · intro hn a
    have ha := congrArg
      (fun f : CyclicRing.Elem ℤ n => f.coeff (ZMod.finEquiv n a)) hn
    simpa only [cyclicRow_norm_apply, CyclicRing.scalar_apply,
      RingEquiv.map_eq_zero_iff] using ha
  · intro hh
    apply AddMonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro x
    obtain ⟨a, rfl⟩ := (ZMod.finEquiv n).surjective x
    simpa only [cyclicRow_norm_apply, CyclicRing.scalar_apply,
      RingEquiv.map_eq_zero_iff] using hh a

theorem cyclicRow_norm_iff_gram (h : Fin n → ℤ) :
    cyclicRow h * CyclicRing.ringStar (cyclicRow h) =
        CyclicRing.scalar n (n : ℤ) ↔
      rowCirculant h * (rowCirculant h).transpose =
        (n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) :=
  (cyclicRow_norm_iff_autocorrelation h).trans (gram_eq_iff_autocorrelation h).symm

theorem integerSignRow_iff_cyclicSignNorm (h : Fin n → ℤ) :
    IsIntegerSignRow h ↔
      CyclicSignRow (cyclicRow h) ∧
        cyclicRow h * CyclicRing.ringStar (cyclicRow h) =
          CyclicRing.scalar n (n : ℤ) := by
  exact and_congr (cyclicSignRow_cyclicRow_iff h).symm (cyclicRow_norm_iff_gram h).symm

/-- The literal sign norm equation is equivalent to the public real-matrix
existence predicate.  Neither direction assumes a mathematical bridge. -/
theorem exists_cyclicSignRow_iff_real :
    (∃ f : CyclicRing.Elem ℤ n,
      CyclicSignRow f ∧ f * CyclicRing.ringStar f = CyclicRing.scalar n (n : ℤ)) ↔
      ExistsRealCirculantHadamard n := by
  rw [← integerSignRow_iff_real]
  constructor
  · rintro ⟨f, hf, hn⟩
    refine ⟨integerRow f, (integerSignRow_iff_cyclicSignNorm _).2 ?_⟩
    simpa only [cyclicRow_integerRow] using And.intro hf hn
  · rintro ⟨h, hh⟩
    exact ⟨cyclicRow h, (integerSignRow_iff_cyclicSignNorm h).1 hh⟩

/-- The identity coefficient is the sum of the actual coefficient squares. -/
theorem cyclicNorm_identity_coeff (f : CyclicRing.Elem ℤ n) :
    (f * CyclicRing.ringStar f).coeff 0 = ∑ a : ZMod n, f.coeff a ^ 2 := by
  simp [CyclicRing.mul_ringStar_apply, pow_two]

theorem cyclicSignRow_identity_coeff (f : CyclicRing.Elem ℤ n)
    (hf : CyclicSignRow f) : (f * CyclicRing.ringStar f).coeff 0 = (n : ℤ) := by
  rw [cyclicNorm_identity_coeff]
  calc
    (∑ a : ZMod n, f.coeff a ^ 2) = ∑ _a : ZMod n, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro a _
      rcases hf a with ha | ha <;> simp [ha]
    _ = (n : ℤ) := by simp

/-- Evaluating the actual cyclic norm at the trivial character gives the
square of the coefficient sum. -/
theorem augmentation_sum_sq_of_norm (f : CyclicRing.Elem ℤ n)
    (hf : f * CyclicRing.ringStar f = CyclicRing.scalar n (n : ℤ)) :
    (∑ a : ZMod n, f.coeff a) ^ 2 = (n : ℤ) := by
  simpa only [CyclicRing.augmentation_apply] using
    CyclicRing.augmentation_norm f (n : ℤ) hf

end PositiveOrder

end CirculantHadamard

end

end OAI
