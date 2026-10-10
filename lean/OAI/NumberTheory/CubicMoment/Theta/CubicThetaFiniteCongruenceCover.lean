import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFullRows

namespace OAI

/-! A finite set of coset charts for the actual principal level-three
subgroup. Finiteness comes from the already constructed residue ring. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaFiniteCongruenceCover :
    ∃ S : Finset SL(2,Eisenstein), ∀ g : SL(2,Eisenstein),
      ∃ δ ∈ S, ∃ k : cubicThetaPrincipalGroup, g=δ*k.val := by
  classical
  let : Finite (Residues (3:Eisenstein)) := finite_residues (by norm_num)
  let : Fintype (Residues (3:Eisenstein)) := Fintype.ofFinite _
  let f : SL(2,Eisenstein) →* SL(2,Residues (3:Eisenstein)) := Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (modulus (3:Eisenstein)))
  let R := f.range
  let : Fintype R := Fintype.ofFinite R
  let rep : R → SL(2,Eisenstein) := fun x => Classical.choose x.property
  have hrep (x : R) : f (rep x)=x.val := Classical.choose_spec x.property
  refine ⟨Finset.univ.image rep,?_⟩
  intro g
  let x : R := ⟨f g,g,rfl⟩
  let δ := rep x
  have hδ : f δ=f g := hrep x
  have hk : δ⁻¹*g ∈ cubicThetaPrincipalGroup := by
    change f (δ⁻¹*g)=1
    rw [map_mul,map_inv,hδ,inv_mul_cancel]
  let k : cubicThetaPrincipalGroup := ⟨δ⁻¹*g,hk⟩
  refine ⟨δ,Finset.mem_image.mpr ⟨x,Finset.mem_univ x,rfl⟩,k,?_⟩
  change g=δ*(δ⁻¹*g)
  group

end CubicFirstMoment

end

end OAI
