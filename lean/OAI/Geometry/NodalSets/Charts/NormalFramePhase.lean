import OAI.Geometry.NodalSets.Elliptic.InitialPhasePolynomial

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

def normalFrameVector (a b : ℝ) : Fin 4 → ℂ := ![(a:ℂ), (b:ℂ)*Complex.I, 0, 0]

def normalRealHessian (a b : ℝ) (H : Fin 4 → Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun i j ↦ H i j - if i = j then Yau.contactEta a b (H 0 0) (H 1 1) else 0

def normalComplexHessian (a b : ℝ) (H : Fin 4 → Fin 4 → ℝ) : Fin 4 → Fin 4 → ℂ :=
  fun i j ↦ (normalRealHessian a b H i j : ℂ) +
    (Yau.imaginaryHessian a b (normalRealHessian a b H) i j : ℂ) * Complex.I

lemma normalFrameVector_null {a b : ℝ} (hlen : b^2 = a^2+4) :
    (∑ i, normalFrameVector a b i * normalFrameVector a b i) + 4 = 0 := by
  simp only [Fin.sum_univ_succ, normalFrameVector, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one, Fin.sum_univ_zero, add_zero, zero_mul]
  apply Complex.ext <;> simp
  nlinarith

lemma normalRealHessian_compatibility {a b : ℝ} (ha : a ≠ 0) (H : Fin 4 → Fin 4 → ℝ) :
    a^2 * normalRealHessian a b H 0 0 + b^2 * normalRealHessian a b H 1 1 = 0 := by
  simpa [normalRealHessian] using Yau.contactEta_compatibility (b := b) (h00 := H 0 0) (h11 := H 1 1) ha

lemma normalComplexHessian_symmetric {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (H : Fin 4 → Fin 4 → ℝ) (hH : ∀ i j, H i j = H j i) :
    ∀ i j, normalComplexHessian a b H i j = normalComplexHessian a b H j i := by
  intro i j
  have hK := Yau.imaginaryHessian_symmetric ha hb (normalRealHessian_compatibility ha H) i j
  have hR : normalRealHessian a b H i j = normalRealHessian a b H j i := by
    simp only [normalRealHessian, hH i j, eq_comm]
  simp only [normalComplexHessian, hK, hR]

lemma normalComplexHessian_real (a b : ℝ) (H : Fin 4 → Fin 4 → ℝ) (i j : Fin 4) :
    (normalComplexHessian a b H i j).re =
      H i j - if i = j then Yau.contactEta a b (H 0 0) (H 1 1) else 0 := by
  simp [normalComplexHessian, normalRealHessian]

lemma normalComplexHessian_contract {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (H : Fin 4 → Fin 4 → ℝ) (j : Fin 4) :
    (∑ i, normalFrameVector a b i * normalComplexHessian a b H i j) = 0 := by
  obtain ⟨h1,h2⟩ := Yau.imaginaryHessian_contractions ha hb (normalRealHessian a b H) j
  simp only [Fin.sum_univ_succ, normalFrameVector, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one, Fin.sum_univ_zero, add_zero, zero_mul]
  apply Complex.ext <;> simp [normalComplexHessian] <;> nlinarith

theorem normal_frame_initial_phase {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hlen : b^2 = a^2+4) (S : ℝ) (H : Fin 4 → Fin 4 → ℝ)
    (hH : ∀ i j, H i j = H j i)
    (hstrict : 0 < a^2*H 0 0+b^2*H 1 1)
    (g : ℕ → Fin 4 → Fin 4 → CPoly) (hg : ∀ i j, g 1 i j = 0) :
    let v := normalFrameVector a b
    let A := initialPhaseJet S v (normalComplexHessian a b H)
    (∀ k, (A k).IsHomogeneous k) ∧
    A 0 = C (S:ℂ) ∧
    (∀ i, pderiv i (A 1) = C (v i)) ∧
    (∑ i, v i*v i)+4 = 0 ∧
    eikonalCoefficient v g 0 A = 0 ∧
    0 < Yau.contactEta a b (H 0 0) (H 1 1) ∧
    ∀ i j, pderiv j (pderiv i (A 2)) = C (normalComplexHessian a b H i j) := by
  dsimp
  refine ⟨initialPhaseJet_homogeneous S _ _, by simp [initialPhaseJet],
    initialPhaseJet_first S _ _, normalFrameVector_null hlen, ?_,
    Yau.contactEta_pos ha hstrict, ?_⟩
  · exact initialPhaseJet_second S _ _ (normalComplexHessian_symmetric ha hb H hH)
      (normalComplexHessian_contract ha hb H) g hg
  · intro i j
    simpa [initialPhaseJet] using pderiv_twice_quadraticPhase
      (normalComplexHessian a b H) (normalComplexHessian_symmetric ha hb H hH) i j

end
end Yau.Jets

end OAI
