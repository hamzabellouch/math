import OAI.Geometry.SurfaceImmersion.Geometry.ComplexMixedJets

namespace OAI

/-! Additivity in each degree-one complex direction slot of the actual
mixed polynomial variation. -/
noncomputable section
namespace ClosedSurfaceR4.JetPolynomial.MixedExpression

private theorem degree_addition {j : Fin 3} {e : MixedExpression} {n : ℕ}
    (he : DegreeIn j e n) (G : Base → Space) (J₁ J₂ J₃ : JetData) (z : Base × ℝ)
    (h₂ : ∀ i, i ≠ j.succ → ∀ w a, J₂ i w a z.1 = J₁ i w a z.1)
    (h₃ : ∀ i, i ≠ j.succ → ∀ w a, J₃ i w a z.1 = J₁ i w a z.1)
    (hadd : ∀ w a, J₃ j.succ w a z.1 = J₁ j.succ w a z.1 + J₂ j.succ w a z.1) :
    (n = 0 → e.evalComplex G J₁ z = e.evalComplex G J₂ z ∧
      e.evalComplex G J₃ z = e.evalComplex G J₁ z) ∧
    (n = 1 → e.evalComplex G J₃ z = e.evalComplex G J₁ z + e.evalComplex G J₂ z) := by
  induction he with
  | coeff c =>
    constructor
    · intro _; exact ⟨rfl, rfl⟩
    · intro hn; omega
  | zero k => simp [evalComplex]
  | other i w a hi h ih =>
    constructor
    · intro hn
      obtain ⟨h12, h31⟩ := ih.1 hn
      simp only [evalComplex, h₂ i hi, h₃ i hi, h12, h31, and_self]
    · intro hn
      simp only [evalComplex, h₂ i hi, h₃ i hi, ih.2 hn, mul_add]
  | @same e k w a h ih =>
    constructor
    · intro hn; omega
    · intro hn
      have hk : k = 0 := by omega
      obtain ⟨h12, h31⟩ := ih.1 hk
      simp only [evalComplex, hadd, h31, ← h12, add_mul]
  | add he hf ihe ihf =>
    constructor
    · intro hn
      obtain ⟨he12, he31⟩ := ihe.1 hn
      obtain ⟨hf12, hf31⟩ := ihf.1 hn
      simp only [evalComplex, he12, he31, hf12, hf31, and_self]
    · intro hn
      simp only [evalComplex, ihe.2 hn, ihf.2 hn]
      ring

theorem DegreeIn.evalComplex_add {j : Fin 3} {e : MixedExpression}
    (he : DegreeIn j e 1) (G : Base → Space) (J₁ J₂ J₃ : JetData) (z : Base × ℝ)
    (h₂ : ∀ i, i ≠ j.succ → ∀ w a, J₂ i w a z.1 = J₁ i w a z.1)
    (h₃ : ∀ i, i ≠ j.succ → ∀ w a, J₃ i w a z.1 = J₁ i w a z.1)
    (hadd : ∀ w a, J₃ j.succ w a z.1 = J₁ j.succ w a z.1 + J₂ j.succ w a z.1) :
    e.evalComplex G J₃ z = e.evalComplex G J₁ z + e.evalComplex G J₂ z :=
  (degree_addition he G J₁ J₂ J₃ z h₂ h₃ hadd).2 rfl

theorem DegreeIn.evalComplex_independent {j : Fin 3} {e : MixedExpression}
    (he : DegreeIn j e 0) (G : Base → Space) (J₁ J₂ : JetData) (z : Base × ℝ)
    (h₂ : ∀ i, i ≠ j.succ → ∀ w a, J₂ i w a z.1 = J₁ i w a z.1) :
    e.evalComplex G J₁ z = e.evalComplex G J₂ z := by
  let J₃ : JetData := fun i w a p => if i = j.succ then J₁ i w a p + J₂ i w a p else J₁ i w a p
  exact ((degree_addition he G J₁ J₂ J₃ z h₂
    (fun i hi w a => by simp only [J₃, hi, ↓reduceIte])
    (fun w a => by simp only [J₃, ↓reduceIte])).1 rfl).1

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
