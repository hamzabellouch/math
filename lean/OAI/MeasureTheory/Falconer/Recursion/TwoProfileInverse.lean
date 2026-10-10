import OAI.MeasureTheory.Falconer.Estimates.InverseClassExpansion

namespace OAI

/-! # Exact inverse factors with two independent original profiles

The finite output symbols are the same uniformly constructed symbols.
Only their endpoint evaluations use the two distinct cubes, laws, profiles
and mask families. Radius powers still charge only new derivatives.
-/

namespace Falconer
open MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorInverseSymbols
variable {m KL KR L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}
  {f : DescriptorJetSymbol (m+1) KL L F D}
  {g : DescriptorJetSymbol (m+1) KR L G D} {j R : ℕ} {A B : ℝ}

theorem two_profile_expansion (T : DescriptorInverseSymbols f g j R A B)
    (hD : 0 < D) (hA : 0 < A) (hB : 0 < B)
    (Q₁ Q₂ : DyadicCube (m+3)) (ρ₁ ρ₂ : Measure (Space (m+3)))
    (profile₁ profile₂ : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S₁ S₂ : PolicyDescriptor → Finset (Sphere (m+3)))
    (Af Ag : ℝ) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (x y : Space (m+3)) (e : Sphere (m+3)) :
    localInverseAmplitude m
      (fun z => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af x z *
        g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag y z) j e =
      ∑ a : DescriptorInverseIndex f g j,
        ((descriptorInverseWeight f g j N σ a*(U*A)*(V*B)*Af⁻¹*Ag⁻¹ : ℝ) : ℂ)*
          ((T.left a).value Q₁ ρ₁ profile₁ N σ J i S₁ U x e *
            (T.right a).value Q₂ ρ₂ profile₂ N σ J i S₂ V y e) := by
  let k := descriptorInverseSeed f g
  let r := descriptorInverseRadius f g N σ
  let F₁ := f.seedMask Q₁ ρ₁ profile₁ N σ J i S₁
  let F₂ := g.seedMask Q₂ ρ₂ profile₂ N σ J i S₂
  let H := fun z => (∏ l, (f.seedJet l).scaledValue (f.seedRadius N σ l) (F₁ l x) z)*
    (∏ l, (g.seedJet l).scaledValue (g.seedRadius N σ l) (F₂ l y) z)
  have hH : ContDiff ℝ ∞ H :=
    (contDiff_prod (fun l _ => MaskJetIndex.scaledValue_contDiff _ _ _
      (f.seedMask_smooth Q₁ ρ₁ profile₁ N σ J i S₁ l x))).mul
    (contDiff_prod (fun l _ => MaskJetIndex.scaledValue_contDiff _ _ _
      (g.seedMask_smooth Q₂ ρ₂ profile₂ N σ J i S₂ l y)))
  have heq : (fun z => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af x z *
      g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag y z) =
      fun z => ((f.spatial x*(Af⁻¹ : ℝ))*(g.spatial y*(Ag⁻¹ : ℝ)))*H z := by
    funext z
    rw [f.ambient_eq_seedProduct,g.ambient_eq_seedProduct]
    dsimp only [H,F₁,F₂]
    ring
  rw [heq,localInverseAmplitude_const_mul m j _ H hH]
  have hinv := seededJetSeparation_exact m j k r
    (fun l => (descriptorInverseRadius_pos f g hD N σ l).ne') F₁ F₂
    (f.seedMask_smooth Q₁ ρ₁ profile₁ N σ J i S₁)
    (g.seedMask_smooth Q₂ ρ₂ profile₂ N σ J i S₂) x y e
  change localInverseAmplitude m H j e = _ at hinv
  rw [hinv]
  change (f.spatial x*(Af⁻¹ : ℝ))*(g.spatial y*(Ag⁻¹ : ℝ))*
    (∑ a : DescriptorInverseIndex f g j,
      (descriptorInverseWeight f g j N σ a : ℂ)*
        (descriptorInverseSeparation f g j Q₁ ρ₁ profile₁ N σ J i S₁).left a x e *
        (descriptorInverseSeparation f g j Q₂ ρ₂ profile₂ N σ J i S₂).right a y e) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hl := T.left_restore Q₁ ρ₁ profile₁ N σ J i S₁ hU hA a x e
  have hr := T.right_restore Q₂ ρ₂ profile₂ N σ J i S₂ hV hB a y e
  simp only [Complex.ofReal_mul]
  calc
    _ = ((Af⁻¹ : ℝ) : ℂ)*((Ag⁻¹ : ℝ) : ℂ)*
        (descriptorInverseWeight f g j N σ a : ℂ)*
        (f.spatial x*(descriptorInverseSeparation f g j Q₁ ρ₁ profile₁ N σ J i S₁).left a x e)*
        (g.spatial y*(descriptorInverseSeparation f g j Q₂ ρ₂ profile₂ N σ J i S₂).right a y e) := by ring
    _ = _ := by rw [← hl,← hr]; simp only [Complex.ofReal_mul]; ring

end DescriptorInverseSymbols
end Falconer

end OAI
