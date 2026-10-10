import OAI.MeasureTheory.Falconer.Fourier.JetStateNearFar
import OAI.MeasureTheory.Falconer.Measures.FarOriginalSupport

namespace OAI

/-! # Actual angular energy bounded on the reassembled original far law -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor)
attribute [local instance] Classical.propDecidable

 theorem jetState_energy_near_original_far {m K L a h : ℕ} {Dq : ℝ}
    {F G : Finset PolicyDescriptor}
    (f : DescriptorJetSymbol (m+1) K L F Dq) (g : DescriptorJetSymbol (m+1) K L G Dq)
    (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (hQ : Q.side = 1)
    (ρ : Measure (Space (m+3))) [IsFiniteMeasure ρ]
    (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (hah : a ≤ h)
    (X Y : List (Fin (m+3) → Bool)) (hX : X.length = a) (hY : Y.length = a)
    (v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    ENNReal.ofReal (jetStateEnergy Q ρ (fun s => profile (s/N)) N σ J i S A
      (ρ.restrict (Q.descendant X).carrier) (ρ.restrict (Q.descendant Y).carrier)
      (profileModelMass profile N a) (profileModelMass profile N a) a v Ψ f g) ≤
    ENNReal.ofReal (profileNearEnergy (Q.descendant X) (Q.descendant Y) ρ profile N a h v Ψ
      (f.value Q ρ (fun s => profile (s/N)) N σ J i S A)
      (g.value Q ρ (fun s => profile (s/N)) N σ J i S A)) +
    ENNReal.ofReal ((2:ℝ)^(((m+3:ℕ):ℝ)*(v-a))*(profileModelMass profile N a)⁻¹^4)*
      ∫⁻ z in farDisplacementRegion (m+3) a h,
        ENNReal.ofReal ‖jetStateOriginalKernel f g w₀ Q ρ (fun s => profile (s/N))
          N σ J i S A A v Ψ z‖
        ∂originalFourPointMeasure (Q.descendant X) (Q.descendant Y) ρ ρ := by
  let V := (Q.descendant X).occupiedPaths ρ (h-a) ×ˢ (Q.descendant Y).occupiedPaths ρ (h-a)
  let kernel := jetStateOriginalKernel f g w₀ Q ρ (fun s => profile (s/N)) N σ J i S A A v Ψ
  let near := nearDyadicEdge (Q.descendant X) (Q.descendant Y)
    (10*(((m+3:ℕ):ℝ)+1)/(2:ℝ)^h)
  have hterm (row col : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool)) :
      0 ≤ if near row col then 0 else ‖∫ z, kernel z
        ∂fourPointChildMeasure (Q.descendant X) (Q.descendant Y) ρ ρ
          (row.1,col.1) (row.2,col.2)‖ := by split_ifs <;> positivity
  have hsum : ENNReal.ofReal (∑ row ∈ V, ∑ col ∈ V,
      if near row col then 0 else ‖∫ z, kernel z
        ∂fourPointChildMeasure (Q.descendant X) (Q.descendant Y) ρ ρ
          (row.1,col.1) (row.2,col.2)‖) ≤
    ∑ row ∈ V, ∑ col ∈ V, if near row col then 0 else
      ∫⁻ z, ENNReal.ofReal ‖kernel z‖
        ∂fourPointChildMeasure (Q.descendant X) (Q.descendant Y) ρ ρ
          (row.1,col.1) (row.2,col.2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun row _ => Finset.sum_nonneg (fun col _ => hterm row col))]
    apply Finset.sum_le_sum
    intro row _
    rw [ENNReal.ofReal_sum_of_nonneg (fun col _ => hterm row col)]
    apply Finset.sum_le_sum
    intro col _
    by_cases hn : near row col
    · simp only [ite_eq_left hn,ENNReal.ofReal_zero,le_refl]
    · simp only [ite_eq_right hn]
      simpa only [← ofReal_norm] using
        (enorm_integral_le_lintegral_enorm (μ := fourPointChildMeasure
          (Q.descendant X) (Q.descendant Y) ρ ρ (row.1,col.1) (row.2,col.2)) kernel)
  have hfar := originalFourPoint_far_rows_le Q hQ ρ hah X Y hX hY
    (fun z => ENNReal.ofReal ‖kernel z‖)
  have hc : 0 ≤ (2:ℝ)^(((m+3:ℕ):ℝ)*(v-a))*(profileModelMass profile N a)⁻¹^4 := by positivity
  have hn : 0 ≤ profileNearEnergy (Q.descendant X) (Q.descendant Y) ρ profile N a h v Ψ
      (f.value Q ρ (fun s => profile (s/N)) N σ J i S A)
      (g.value Q ρ (fun s => profile (s/N)) N σ J i S A) := by
    unfold profileNearEnergy
    positivity
  have hb := ENNReal.ofReal_le_ofReal (jetState_energy_near_far f g w₀ Q ρ profile N σ J i S
    hF hG hA (Q.descendant X) (Q.descendant Y) a h v Ψ)
  have hsum0 := Finset.sum_nonneg (fun row (_ : row ∈ V) =>
    Finset.sum_nonneg (fun col (_ : col ∈ V) => hterm row col))
  rw [ENNReal.ofReal_add hn (mul_nonneg hc hsum0),ENNReal.ofReal_mul hc] at hb
  exact hb.trans (add_le_add le_rfl (mul_le_mul' le_rfl (hsum.trans hfar)))

end Falconer

end OAI
