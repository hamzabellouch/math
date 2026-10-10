import OAI.MeasureTheory.Falconer.Fourier.InverseJetShell
import OAI.MeasureTheory.Falconer.Fourier.BaseJetAmplitude
import OAI.MeasureTheory.Falconer.Estimates.RegularizationSubpower

namespace OAI

/-! # Polynomial cost of the actual root inverse family -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem exists_two_profile_root_shell_cost (m k : ℕ) (A B : Fin (k+1) → ℝ)
    (U δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F G : Finset PolicyDescriptor) (L : ℕ),
      descriptorInverseShellCost (descriptorRootSymbol (m+1) F L)
        (descriptorRootSymbol (m+1) G L) k A B 1 1 U δ W hδ hW ≤
        C*((1+(2+F.card+G.card)*(m+3):ℕ):ℝ)^(4*k) := by
  let c : Fin (k+1) → ℝ := fun j => MaskJetExpansion.inverseMultiplicity (m+2) j.val
  let b : Fin (k+1) → ℝ := fun j =>
    ((|U*A j| *|U*B j| *|(1:ℝ)⁻¹| *|(1:ℝ)⁻¹|)*4^(((m+2:ℕ):ℝ)/2))^2*
      (spatialFourierCost (d := m+3) δ W hδ hW j.val)^2
  let C₁ : ℝ := ∑ j, c j
  let C₂ : ℝ := ∑ j, b j
  have hc (j) : 0 ≤ c j := Nat.cast_nonneg _
  have hb (j) : 0 ≤ b j := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hC₁ : 0 ≤ C₁ := Finset.sum_nonneg (fun j _ => hc j)
  have hC₂ : 0 ≤ C₂ := Finset.sum_nonneg (fun j _ => hb j)
  refine ⟨C₁^2*C₂,mul_nonneg (sq_nonneg _) hC₂,?_⟩
  intro F G L
  let f := descriptorRootSymbol (m+1) F L
  let g := descriptorRootSymbol (m+1) G L
  let I := DescriptorInverseFamilyIndex f g k
  let Q : ℝ := ((1+(2+F.card+G.card)*(m+3):ℕ):ℝ)
  have hQ : 1 ≤ Q := by dsimp [Q]; exact_mod_cast Nat.le_add_right 1 _
  have hcard : (Fintype.card I : ℝ) ≤ C₁*Q^(2*k) := by
    have he : (Fintype.card I : ℝ) = ∑ j : Fin (k+1), c j*Q^(2*j.val) := by
      simp only [I,DescriptorInverseFamilyIndex,Fintype.card_sigma,card_descriptorInverseIndex,
        Nat.cast_sum,Nat.cast_mul,Nat.cast_pow,c,Q]
    rw [he]
    dsimp only [C₁]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (hc j)
    exact pow_le_pow_right₀ hQ (by have := j.isLt; omega)
  have hsum : (∑ z : I, b z.1) ≤ (Fintype.card I:ℝ)*C₂ := by
    calc
      _ ≤ ∑ _z : I, C₂ := Finset.sum_le_sum (fun z _ =>
        Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ z.1))
      _ = _ := by simp
  have hcost : descriptorInverseShellCost f g k A B 1 1 U δ W hδ hW ≤
      (Fintype.card I:ℝ)^2*C₂ := by
    change (Fintype.card I:ℝ)*(∑ z : I, b z.1) ≤ _
    exact (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)).trans_eq (by ring)
  apply hcost.trans
  calc
    _ ≤ (C₁*Q^(2*k))^2*C₂ := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) hC₂
    _ = (C₁^2*C₂)*Q^(4*k) := by
      rw [mul_pow,← pow_mul]
      have he : 2*k*2 = 4*k := by omega
      rw [he]
      ring

theorem eventual_two_profile_root_shell_cost (m k : ℕ) (A B : Fin (k+1) → ℝ)
    (U δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (F G : Finset PolicyDescriptor) (L : ℕ),
      F.card ≤ (N+1)^4 → G.card ≤ (N+1)^4 →
      descriptorInverseShellCost (descriptorRootSymbol (m+1) F L)
        (descriptorRootSymbol (m+1) G L) k A B 1 1 U δ W hδ hW ≤ ((2:ℝ)^N)^ε := by
  obtain ⟨C,hC,hbound⟩ := exists_two_profile_root_shell_cost m k A B U δ W hδ hW
  let H : ℝ := 1+4*(m+3:ℕ)
  obtain ⟨N₁,hN₁⟩ := PlanarFalconer.fixed_polynomial_subpower (16*k) (half_pos hε)
  obtain ⟨N₂,hN₂⟩ := Regularization.fixed_constant_absorbed (half_pos hε) (C*H^(4*k))
  refine ⟨max N₁ N₂,?_⟩
  intro N hN F G L hF hG
  have hx : (1:ℝ) ≤ (N:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hX : (1:ℝ) ≤ ((N:ℝ)+1)^4 := one_le_pow₀ hx
  have hFc : (F.card:ℝ) ≤ ((N:ℝ)+1)^4 := by exact_mod_cast hF
  have hGc : (G.card:ℝ) ≤ ((N:ℝ)+1)^4 := by exact_mod_cast hG
  have hM : (0:ℝ) ≤ (m+3:ℕ) := Nat.cast_nonneg _
  have hQ : ((1+(2+F.card+G.card)*(m+3):ℕ):ℝ) ≤ H*((N:ℝ)+1)^4 := by
    dsimp [H]
    push_cast at hM ⊢
    calc
      _ ≤ 1+(2+((N:ℝ)+1)^4+((N:ℝ)+1)^4)*((m:ℝ)+3) := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hM (sub_nonneg.mpr hX)]
  have hp : ((1+(2+F.card+G.card)*(m+3):ℕ):ℝ)^(4*k) ≤
      H^(4*k)*((N:ℝ)+1)^(16*k) := by
    calc
      _ ≤ (H*((N:ℝ)+1)^4)^(4*k) := pow_le_pow_left₀ (Nat.cast_nonneg _) hQ _
      _ = _ := by rw [mul_pow,← pow_mul]; congr 2; omega
  calc
    _ ≤ C*((1+(2+F.card+G.card)*(m+3):ℕ):ℝ)^(4*k) := hbound F G L
    _ ≤ (C*H^(4*k))*((N:ℝ)+1)^(16*k) := by
      convert mul_le_mul_of_nonneg_left hp hC using 1
      ring
    _ ≤ (C*H^(4*k))*(4*(N:ℝ)+1)^(16*k) := by
      gcongr
      linarith [Nat.cast_nonneg (α := ℝ) N]
    _ ≤ ((2:ℝ)^N)^(ε/2)*((2:ℝ)^N)^(ε/2) :=
      mul_le_mul (hN₂ N ((le_max_right _ _).trans hN))
        (hN₁ N ((le_max_left _ _).trans hN)) (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end Falconer

end OAI
