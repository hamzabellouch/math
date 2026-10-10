import OAI.Combinatorics.Progressions.Dynamics.InactiveShortHeightBudget
import OAI.Combinatorics.Progressions.Sampling.ForecastInactiveFixedSupport

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedGridSide_zero_normalizable_or_height_exp
    (j : Fin m) (i : Fin (n j)) (q : ℕ) {P : ℝ}
    (hP : 0 ≤ P) (hR : 0 < R j) (hRP : (R j)⁻¹ ≤ Real.exp P)
    (hslots : ((layerIntegerPrincipalSlots (G := G) B j i).card : ℝ) ≤ P)
    (hq : 0 < q) (hqP : (q : ℝ) ≤ Real.exp P) (hsize : q ≤ S.value) :
    let γ := principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card
    (2 * inactiveDenominator γ ≤ basisAxisScale (b j) i ∧
      ∀ (a : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)),
        q ≤ allocatedPrincipalSides B U b S ⟨⟨j, Sum.inr i⟩, a, v⟩) ∨
      (basisAxisScale (b j) i : ℝ) ≤ Real.exp (((m : ℝ) + 5) * (P + 8)) := by
  dsimp only
  let γ := principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card
  have hγ : 0 < γ := principalProfileSize_pos hR _
  have hγP : γ⁻¹ ≤ Real.exp (4 * (P + 8)) := by
    exact (allocatedProfile_inverse_exp_bounds
      (layerIntegerPrincipalSlots (G := G) B j i).card
      (σ := 1) hP hR (by norm_num) hRP
      (by simpa only [inv_one] using Real.one_le_exp hP) hslots).2.1
  have hside := allocatedGridSide_normalizable_or_bounded B U b S
    (α := Empty) q j i hq (by simpa using hsize)
  simp only [Fintype.card_empty, zero_add, one_mul] at hside
  rcases hside with hlong | hshort
  · exact Or.inl hlong
  · right
    have hheight := inactiveShortHeightBound_le_exp (j.val + 1) q hγ
      (by positivity : 0 ≤ 4 * (P + 8)) hP hγP hqP
    have hjm : ((j.val + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast j.isLt
    calc
      (basisAxisScale (b j) i : ℝ) ≤
          (max (2 * inactiveDenominator γ)
            (integerAxisShortBound (j.val + 1) q γ) : ℕ) := by exact_mod_cast hshort
      _ ≤ Real.exp (4 * (P + 8) + 2 + (j.val + 1 : ℕ) * (P + 1)) := hheight
      _ ≤ Real.exp (4 * (P + 8) + 2 + (m : ℝ) * (P + 1)) :=
        by
        apply Real.exp_le_exp.mpr
        nlinarith only [hjm, hP]
      _ ≤ Real.exp (((m : ℝ) + 5) * (P + 8)) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [hP, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

end Erdos3.VectorPolynomial

end

end OAI
