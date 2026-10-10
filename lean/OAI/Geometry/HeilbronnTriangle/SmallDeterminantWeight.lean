import OAI.Geometry.HeilbronnTriangle.AuxiliaryAffineWeights
import OAI.Geometry.HeilbronnTriangle.SmallDeterminantReduction

namespace OAI


noncomputable section

namespace Problem355.SmallDeterminantWeight

theorem intCast_ne_zero_of_abs_lt {q : ℕ} {t : ℤ}
    (ht : t ≠ 0) (hsmall : |t| < (q : ℤ)) : (t : ZMod q) ≠ 0 := by
  intro hzero
  have hdvd : (q : ℤ) ∣ t := (ZMod.intCast_zmod_eq_zero_iff_dvd t q).mp hzero
  have hle := Int.le_abs_of_dvd ht hdvd
  omega

theorem det_map_ne_zero {q : ℕ} (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hdet : A.det ≠ 0) (hsmall : |A.det| < (q : ℤ)) :
    (A.map (Int.castRingHom (ZMod q))).det ≠ 0 := by
  have hd := (Int.castRingHom (ZMod q)).map_det A
  change (A.det : ZMod q) = (A.map (Int.castRingHom (ZMod q))).det at hd
  rw [← hd]
  exact intCast_ne_zero_of_abs_lt hdet hsmall

theorem affineIndependent_columns {q : ℕ} [Fact q.Prime]
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hdet : A.det ≠ 0) (hsmall : |A.det| < (q : ℤ)) :
    AffineIndependent (ZMod q) (fun j i => (A i j : ZMod q)) := by
  exact (Matrix.linearIndependent_cols_of_det_ne_zero
    (det_map_ne_zero A hdet hsmall)).affineIndependent

theorem weight_le_eight {q : ℕ} [Fact q.Prime]
    [Fintype ((Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q))]
    (S : Finset (Fin 3 → ZMod q)) (hS : S.Nonempty)
    (T : Finset ((Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q)))
    (hT : T.Nonempty)
    (hsize : Fintype.card ((Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q)) ≤
      2 * T.card)
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hdet : A.det ≠ 0) (hsmall : |A.det| < (q : ℤ)) :
    AuxiliaryWeights.affineInclusionWeight S T (fun j i => (A i j : ZMod q)) ≤ 8 :=
  AuxiliaryWeights.affineInclusionWeight_le_eight S hS T hT hsize _
    (affineIndependent_columns A hdet hsmall)

theorem sum_weight_le_eight_mul_card {q : ℕ} [Fact q.Prime]
    [Fintype ((Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q))]
    (S : Finset (Fin 3 → ZMod q)) (hS : S.Nonempty)
    (T : Finset ((Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q)))
    (hT : T.Nonempty)
    (hsize : Fintype.card ((Fin 3 → ZMod q) ≃ᵃ[ZMod q] (Fin 3 → ZMod q)) ≤
      2 * T.card)
    (F : Finset (Matrix (Fin 3) (Fin 3) ℤ)) (t : ℤ)
    (ht : t ≠ 0) (hsmall : |t| < (q : ℤ))
    (hdet : ∀ A ∈ F, A.det = t) :
    (∑ A ∈ F, AuxiliaryWeights.affineInclusionWeight S T
      (fun j i => (A i j : ZMod q))) ≤ 8 * (F.card : ℝ) := by
  calc
    (∑ A ∈ F, AuxiliaryWeights.affineInclusionWeight S T
      (fun j i => (A i j : ZMod q))) ≤ ∑ _A ∈ F, (8 : ℝ) := by
      apply Finset.sum_le_sum
      intro A hA
      exact weight_le_eight S hS T hT hsize A
        (by simpa only [hdet A hA] using ht)
        (by simpa only [hdet A hA] using hsmall)
    _ = 8 * (F.card : ℝ) := by simp [mul_comm]

abbrev Space (q : ℕ) := Fin 3 → ZMod q
abbrev AffineGroup (q : ℕ) := Space q ≃ᵃ[ZMod q] Space q

variable (q : ℕ) [Fact q.Prime] [Fintype (AffineGroup q)]

theorem normalized_affine_weight_le_eight
    (M : Matrix (Fin 3) (Fin 3) ℤ) (hdet : M.det ≠ 0)
    (hsmall : |M.det| < (q : ℤ))
    (S : Finset (Space q)) (hS : S.Nonempty)
    (G : Finset (AffineGroup q)) (hG : G.Nonempty)
    (hsize : Fintype.card (AffineGroup q) ≤ 2 * G.card) :
    ((q : ℝ) ^ 3 / S.card) ^ 3 *
      (((G.filter (fun e => ∀ j, e.symm (fun i => (M i j : ZMod q)) ∈ S)).card : ℝ) /
        G.card) ≤ 8 := by
  classical
  let p : AuxiliaryWeights.AffineFamily (ZMod q) (Space q) (Fin 3) :=
    ⟨fun j i => (M i j : ZMod q),
      SmallDeterminantReduction.reduction_columns_affineIndependent q M hdet hsmall⟩
  simpa only [ZMod.card, p] using
    AuxiliaryWeights.affine_triple_weight_le_eight p S hS G hG hsize

theorem sum_normalized_affine_weight_le
    (T : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (hdet : ∀ M ∈ T, M.det ≠ 0 ∧ |M.det| < (q : ℤ))
    (S : Finset (Space q)) (hS : S.Nonempty)
    (G : Finset (AffineGroup q)) (hG : G.Nonempty)
    (hsize : Fintype.card (AffineGroup q) ≤ 2 * G.card) :
    (∑ M ∈ T, ((q : ℝ) ^ 3 / S.card) ^ 3 *
      (((G.filter (fun e => ∀ j, e.symm (fun i => (M i j : ZMod q)) ∈ S)).card : ℝ) /
        G.card)) ≤ 8 * T.card := by
  classical
  calc
    _ ≤ ∑ _M ∈ T, (8 : ℝ) := by
      apply Finset.sum_le_sum
      intro M hM
      exact normalized_affine_weight_le_eight q M (hdet M hM).1 (hdet M hM).2
        S hS G hG hsize
    _ = 8 * T.card := by simp [mul_comm]

end Problem355.SmallDeterminantWeight

end

end OAI
