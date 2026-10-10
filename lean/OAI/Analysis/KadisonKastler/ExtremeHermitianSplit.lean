import OAI.Analysis.KadisonKastler.HermitianAnnihilatorBall

namespace OAI

/-! # A norm-budgeted splitting of an extreme Hermitian annihilator

The compression argument splits an extreme functional into two Hermitian
annihilators with complementary norm bounds. Extremality determines each
summand from that norm budget.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem scaled_hermitian_mem_annihilator_ball
    (φ : A →⋆ₐ[ℂ] B) (F : B →L[ℂ] ℂ) (t : ℝ) (ht : 0 < t)
    (hn : ‖F‖ ≤ t) (hstar : ∀ b, F (star b) = star (F b))
    (hann : ∀ a, F (φ a) = 0) :
    StrongDual.toWeakDual (t⁻¹ • F) ∈ hermitianAnnihilatorBall φ := by
  refine ⟨?_, ?_, ?_⟩
  · change ‖t⁻¹ • F‖ ≤ 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]
    exact (mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr ht.le)).trans_eq
      (inv_mul_cancel₀ ht.ne')
  · intro b
    change t⁻¹ • F (star b) = star (t⁻¹ • F b)
    rw [hstar]
    simp only [star_smul, star_trivial]
  · intro a
    change t⁻¹ • F (φ a) = 0
    rw [hann, smul_zero]

theorem extreme_hermitian_split
    (φ : A →⋆ₐ[ℂ] B) (F : WeakDual ℂ B)
    (hF : F ∈ (hermitianAnnihilatorBall φ).extremePoints ℝ)
    (G H : B →L[ℂ] ℂ) (t s : ℝ) (ht : 0 < t) (hs : 0 < s) (hts : t + s = 1)
    (hG : ‖G‖ ≤ t) (hH : ‖H‖ ≤ s)
    (hGs : ∀ b, G (star b) = star (G b)) (hHs : ∀ b, H (star b) = star (H b))
    (hGa : ∀ a, G (φ a) = 0) (hHa : ∀ a, H (φ a) = 0)
    (heq : G + H = F.toStrongDual) : G = t • F.toStrongDual := by
  let g := StrongDual.toWeakDual (t⁻¹ • G)
  let h := StrongDual.toWeakDual (s⁻¹ • H)
  have hg : g ∈ hermitianAnnihilatorBall φ :=
    scaled_hermitian_mem_annihilator_ball φ G t ht hG hGs hGa
  have hh : h ∈ hermitianAnnihilatorBall φ :=
    scaled_hermitian_mem_annihilator_ball φ H s hs hH hHs hHa
  have hseg : F ∈ openSegment ℝ g h := by
    refine ⟨t, s, ht, hs, hts, ?_⟩
    apply WeakDual.toStrongDual.injective
    change t • (t⁻¹ • G) + s • (s⁻¹ • H) = F.toStrongDual
    rw [smul_smul, smul_smul, mul_inv_cancel₀ ht.ne', mul_inv_cancel₀ hs.ne',
      one_smul, one_smul]
    exact heq
  have hgf := (mem_extremePoints.mp hF).2 g hg h hh hseg |>.1
  have he : t⁻¹ • G = F.toStrongDual := congrArg WeakDual.toStrongDual hgf
  calc
    G = t • (t⁻¹ • G) := by rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    _ = t • F.toStrongDual := congrArg (fun K : B →L[ℂ] ℂ => t • K) he

end

end KadisonKastler

end OAI
