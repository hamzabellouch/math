import OAI.MeasureTheory.Falconer.Angular.FactorizedAngularState

namespace OAI

/-! # Root symbols and Fourier operations in the exact descriptor class -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)
open scoped ContDiff

namespace DescriptorJetSymbol
variable {n K L : ℕ} {F : Finset PolicyDescriptor} {D : ℝ}

noncomputable def spatialMultiplier (f : DescriptorJetSymbol n K L F D)
    (c : Space (n+2) → ℂ) (hc : Measurable c) (hcb : ∀ x, ‖c x‖ ≤ 1) :
    DescriptorJetSymbol n K L F D where
  jet := f.jet
  order_le := f.order_le
  angular := f.angular
  angular_smooth := f.angular_smooth
  angular_derivative := f.angular_derivative
  angular_control := f.angular_control
  spatial := fun x => c x*f.spatial x
  spatial_measurable := hc.mul f.spatial_measurable
  spatial_bound := by
    intro x
    rw [norm_mul]
    calc
      _ ≤ (1:ℝ)*1 := mul_le_mul (hcb x) (f.spatial_bound x) (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1

 theorem spatialMultiplier_value (f : DescriptorJetSymbol n K L F D)
    (c : Space (n+2) → ℂ) (hc : Measurable c) (hcb : ∀ x, ‖c x‖ ≤ 1)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x : Space (n+2)) (w : Sphere (n+2)) :
    (f.spatialMultiplier c hc hcb).value Q ρ m N σ J i S A x w =
      c x*f.value Q ρ m N σ J i S A x w := by
  simp only [value,multiplier,spatialMultiplier]
  ring

noncomputable def base (F : Finset PolicyDescriptor) (K L : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (c : Space (n+2) → ℂ) (hc : Measurable c) (hcb : ∀ x, ‖c x‖ ≤ 1) :
    DescriptorJetSymbol n K L F D where
  jet := fun _ => MaskJetIndex.zero (n+2)
  order_le := by simp [MaskJetIndex.zero]
  angular := fun _ => 1
  angular_smooth := contDiff_const
  angular_derivative := by
    intro t _ w
    cases t with
    | zero => simp
    | succ t => simpa only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero] using pow_nonneg hD (t+1)
  angular_control := by
    refine ⟨measurable_const,?_,?_,?_⟩
    · intro x w; simp
    · intro x e y; exact contDiff_const
    · intro e t _ x y _ u _
      cases t with
      | zero => simp [rotatedChartAmplitude,chartAmplitude]
      | succ t =>
        change ‖iteratedDeriv (t+1) (fun _ : ℝ => (1:ℂ)) u‖ ≤ 1*D^(t+1)
        simpa [iteratedDeriv_const] using pow_nonneg hD (t+1)
  spatial := c
  spatial_measurable := hc
  spatial_bound := hcb

 theorem base_value (F : Finset PolicyDescriptor) (K L : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (c : Space (n+2) → ℂ) (hc : Measurable c) (hcb : ∀ x, ‖c x‖ ≤ 1)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x : Space (n+2)) (w : Sphere (n+2)) :
    (base F K L D hD c hc hcb).value Q ρ m N σ J i S A x w =
      (descriptorProduct Q ρ m N σ J i F S x w : ℂ)*(c x*(A⁻¹ : ℝ)) := by
  simp only [value,multiplier,base,descriptorJetProduct,MaskJetIndex.zero,
    normalizedDescriptorJet_zero,mul_one,descriptorProduct,Complex.ofReal_prod,id_eq]

noncomputable def conj (f : DescriptorJetSymbol n K L F D) : DescriptorJetSymbol n K L F D where
  jet := f.jet
  order_le := f.order_le
  angular := fun z => star (f.angular z)
  angular_smooth := Complex.conjCLE.contDiff.comp f.angular_smooth
  angular_derivative := by
    intro t ht w
    have he := Complex.conjLIE.norm_iteratedFDeriv_comp_left f.angular (w : Space (n+2)) t
    exact he.le.trans (f.angular_derivative t ht w)
  angular_control := f.angular_control.conj
  spatial := fun x => star (f.spatial x)
  spatial_measurable := continuous_star.measurable.comp f.spatial_measurable
  spatial_bound := fun x => (norm_star _).le.trans (f.spatial_bound x)

 theorem conj_value (f : DescriptorJetSymbol n K L F D)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x : Space (n+2)) (w : Sphere (n+2)) :
    f.conj.value Q ρ m N σ J i S A x w = star (f.value Q ρ m N σ J i S A x w) := by
  simp only [value,multiplier,conj,map_mul,map_prod,descriptorJetProduct,
    normalizedDescriptorJet,Complex.star_def,Complex.conj_ofReal]
  rfl

end DescriptorJetSymbol
end Falconer

end OAI
