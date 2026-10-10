import OAI.MeasureTheory.Falconer.Fourier.JetStateAmbient
import OAI.MeasureTheory.Falconer.Estimates.DescriptorPairBudget

namespace OAI

/-! # The actual masked amplitude is the zero-jet root state -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorJetSymbol

theorem base_ambient {n : ℕ} (F : Finset PolicyDescriptor) (K L : ℕ)
    (D : ℝ) (hD : 0 ≤ D) (c : Space (n+2) → ℂ)
    (hc : Measurable c) (hcb : ∀ x, ‖c x‖ ≤ 1)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x z : Space (n+2)) :
    (base F K L D hD c hc hcb).ambient Q ρ profile N σ J i S A x z =
      (descriptorAmbientProduct Q ρ profile N σ J i F S x z : ℂ)*(c x*(A⁻¹ : ℝ)) := by
  have hzero (b : PolicyDescriptor) :
      normalizedAmbientDescriptorJet Q ρ profile N σ J i b (S b)
        (MaskJetIndex.zero (n+2)).order (MaskJetIndex.zero (n+2)).vectors x z =
      descriptorAmbientMask Q ρ profile N σ J i b (S b) x z := by
    simp only [normalizedAmbientDescriptorJet,MaskJetIndex.zero,pow_zero,one_mul]
    rfl
  simp only [ambient,base,hzero,mul_one,descriptorAmbientProduct]
  ring

theorem base_pair_amplitude {m : ℕ} (F : Finset PolicyDescriptor) (K L : ℕ)
    (D : ℝ) (hD : 0 ≤ D)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (x y z : Space (m+3)) :
    let f := base (n := m+1) F K L D hD (fun _ => 1) measurable_const (by simp)
    f.ambient Q ρ profile N σ J i S 1 x z *
      f.ambient Q ρ profile N σ J i S 1 y z =
        descriptorPairAmplitude Q ρ profile N σ J i F S x y z := by
  simp only [base_ambient,inv_one,Complex.ofReal_one,mul_one,descriptorPairAmplitude]

end DescriptorJetSymbol

noncomputable def descriptorRootSymbol (n : ℕ) (F : Finset PolicyDescriptor) (L : ℕ) :
    DescriptorJetSymbol n 0 L F 1 :=
  DescriptorJetSymbol.base F 0 L 1 (by norm_num) (fun _ => 1) measurable_const (by simp)

theorem descriptorRootSymbol_pair {m : ℕ} (F : Finset PolicyDescriptor) (L : ℕ)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3))) :
    (fun x y z => (descriptorRootSymbol (m+1) F L).ambient Q ρ profile N σ J i S 1 x z *
      (descriptorRootSymbol (m+1) F L).ambient Q ρ profile N σ J i S 1 y z) =
      descriptorPairAmplitude Q ρ profile N σ J i F S := by
  funext x y z
  exact DescriptorJetSymbol.base_pair_amplitude F 0 L 1 (by norm_num) Q ρ profile N σ J i S x y z

end Falconer

end OAI
