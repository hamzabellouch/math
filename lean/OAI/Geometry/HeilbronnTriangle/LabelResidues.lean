import OAI.Geometry.HeilbronnTriangle.EncodedDeterminant

namespace OAI


noncomputable section
namespace Problem355.LabelResidues

open DesignatedCoefficient EncodedDeterminant

def residue {R Λ : Type*} [AddCommMonoid R] (T : ℕ)
    (f : Fin 3 → Fin T → Λ → R) (i : Fin 3) (v : ℕ) (x : Λ) : R :=
  ∑ a : Fin T, if position T i a = v then f i a x else 0

@[simp]
theorem residue_at_position {R Λ : Type*} [AddCommMonoid R] (T : ℕ)
    (f : Fin 3 → Fin T → Λ → R) (i : Fin 3) (a : Fin T) (x : Λ) :
    residue T f i (position T i a) x = f i a x := by
  classical
  unfold residue
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    exact ite_eq_right (fun h => hba (position_injective T i h))
  · simp

theorem residue_eq_zero {R Λ : Type*} [AddCommMonoid R] (T : ℕ)
    (f : Fin 3 → Fin T → Λ → R) (i : Fin 3) (v : ℕ) (x : Λ)
    (hv : ∀ a : Fin T, position T i a ≠ v) : residue T f i v x = 0 := by
  simp [residue, hv]

theorem labeled_polynomial_obstruction {R Λ : Type*} [CommRing R]
    (φ : ℤ →+* R) (T : ℕ) (B L : ℤ) (hB : 2 ≤ B) (hL : 0 ≤ L)
    (hbase : 100 * ((T ^ 2 + 1 : ℕ) : ℤ) ^ 2 * L ^ 3 < B)
    (f : Fin 3 → Fin T → Λ → R) (labels : Fin 3 → Λ)
    (d : Fin 3 → Fin 3 → ℕ → ℤ)
    (hd : ∀ i j v, v < T ^ 2 + 1 → |d i j v| ≤ L)
    (hresidue : ∀ i j v, v < T ^ 2 + 1 → φ (d i j v) = residue T f i v (labels j))
    (hne : (∑ a : Fin T, Matrix.det (fun i j => f i a (labels j))) ≠ 0)
    {x : ℤ} (hx : x ≡ (DigitCoefficients.determinantPolynomial (T ^ 2 + 1) d).eval B
      [ZMOD B ^ (T ^ 2 + 1)]) : B ^ (T ^ 2) / 2 < |x| := by
  apply encoded_polynomial_obstruction φ T B L hB hL hbase d
    (fun i a j => f i a (labels j)) hd _ _ hne hx
  · intro i j a
    rw [hresidue i j (position T i a) (position_lt T i a), residue_at_position]
  · intro i j v hv hn
    rw [hresidue i j v hv, residue_eq_zero T f i v (labels j) hn]

theorem labeled_polynomial_obstruction_of_length {R Λ : Type*} [CommRing R]
    (φ : ℤ →+* R) (T K : ℕ) (hK : K = T ^ 2 + 1)
    (B L : ℤ) (hB : 2 ≤ B) (hL : 0 ≤ L)
    (hbase : 100 * (K : ℤ) ^ 2 * L ^ 3 < B)
    (f : Fin 3 → Fin T → Λ → R) (labels : Fin 3 → Λ)
    (d : Fin 3 → Fin 3 → ℕ → ℤ)
    (hd : ∀ i j v, v < K → |d i j v| ≤ L)
    (hresidue : ∀ i j v, v < K → φ (d i j v) = residue T f i v (labels j))
    (hne : (∑ a : Fin T, Matrix.det (fun i j => f i a (labels j))) ≠ 0)
    {x : ℤ} (hx : x ≡ (DigitCoefficients.determinantPolynomial K d).eval B
      [ZMOD B ^ K]) : B ^ (K - 1) / 2 < |x| := by
  subst K
  simpa only [Nat.add_sub_cancel] using
    labeled_polynomial_obstruction φ T B L hB hL hbase f labels d hd hresidue hne hx

theorem labeled_mixed_determinant_obstruction {R Λ : Type*} [CommRing R]
    (φ : ℤ →+* R) (T B : ℕ) (L : ℤ) (hB : 2 ≤ B) (hL : 0 ≤ L)
    (hbase : 100 * ((T ^ 2 + 1 : ℕ) : ℤ) ^ 2 * L ^ 3 < B)
    (f : Fin 3 → Fin T → Λ → R) (labels : Fin 3 → Λ)
    (d : Fin 3 → Fin 3 → ℕ → ℤ)
    (hd : ∀ i j v, v < T ^ 2 + 1 → |d i j v| ≤ L)
    (hresidue : ∀ i j v, v < T ^ 2 + 1 →
      φ (d i j v) = residue T f i v (labels j))
    (hne : (∑ a : Fin T, Matrix.det (fun i j => f i a (labels j))) ≠ 0)
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (G : Matrix.SpecialLinearGroup (Fin 3) (ZMod (B ^ (T ^ 2 + 1))))
    (hAC : A.map (Int.castRingHom (ZMod (B ^ (T ^ 2 + 1)))) =
      (G : Matrix (Fin 3) (Fin 3) (ZMod (B ^ (T ^ 2 + 1)))) *
        (Matrix.map (fun i j => ∑ v ∈ Finset.range (T ^ 2 + 1), d i j v * (B : ℤ) ^ v)
          (Int.castRingHom (ZMod (B ^ (T ^ 2 + 1)))))) :
    (B : ℤ) ^ (T ^ 2) / 2 < |A.det| := by
  apply encoded_mixed_determinant_obstruction φ T B L hB hL hbase d
    (fun i a j => f i a (labels j)) hd _ _ hne A G hAC
  · intro i j a
    rw [hresidue i j (position T i a) (position_lt T i a), residue_at_position]
  · intro i j v hv hn
    rw [hresidue i j v hv, residue_eq_zero T f i v (labels j) hn]

theorem small_determinant_forces_repeated_labels {R Λ : Type*} [CommRing R]
    (φ : ℤ →+* R) (T B : ℕ) (L : ℤ) (hB : 2 ≤ B) (hL : 0 ≤ L)
    (hbase : 100 * ((T ^ 2 + 1 : ℕ) : ℤ) ^ 2 * L ^ 3 < B)
    (f : Fin 3 → Fin T → Λ → R)
    (hseparates : ∀ labels : Fin 3 → Λ, Function.Injective labels →
      (∑ a : Fin T, Matrix.det (fun i j => f i a (labels j))) ≠ 0)
    (labels : Fin 3 → Λ) (d : Fin 3 → Fin 3 → ℕ → ℤ)
    (hd : ∀ i j v, v < T ^ 2 + 1 → |d i j v| ≤ L)
    (hresidue : ∀ i j v, v < T ^ 2 + 1 →
      φ (d i j v) = residue T f i v (labels j))
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (G : Matrix.SpecialLinearGroup (Fin 3) (ZMod (B ^ (T ^ 2 + 1))))
    (hAC : A.map (Int.castRingHom (ZMod (B ^ (T ^ 2 + 1)))) =
      (G : Matrix (Fin 3) (Fin 3) (ZMod (B ^ (T ^ 2 + 1)))) *
        (Matrix.map (fun i j => ∑ v ∈ Finset.range (T ^ 2 + 1), d i j v * (B : ℤ) ^ v)
          (Int.castRingHom (ZMod (B ^ (T ^ 2 + 1))))))
    (hsmall : |A.det| ≤ (B : ℤ) ^ (T ^ 2) / 2) :
    ∃ i j : Fin 3, i ≠ j ∧ labels i = labels j := by
  classical
  by_contra h
  have hinj : Function.Injective labels := by
    intro i j hij
    by_contra hne
    exact h ⟨i, j, hne, hij⟩
  exact (not_lt_of_ge hsmall)
    (labeled_mixed_determinant_obstruction φ T B L hB hL hbase f labels d hd hresidue
      (hseparates labels hinj) A G hAC)

end Problem355.LabelResidues

end

end OAI
