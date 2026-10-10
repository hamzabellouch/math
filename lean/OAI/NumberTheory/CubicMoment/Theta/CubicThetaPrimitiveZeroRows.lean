import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimitiveKernel

namespace OAI

/-! The zero-first-coordinate rows are exactly the finitely many units.
Their cutoff heat contribution has uniform exponential decay. -/
noncomputable section
namespace CubicFirstMoment

abbrev CubicThetaZeroFirstRow := {r : CubicThetaPrimitiveRow // r.c=0}

def cubicThetaUnitRow (u : Eisensteinˣ) : CubicThetaZeroFirstRow :=
  ⟨⟨0,u,⟨0,(u⁻¹:Eisensteinˣ),by simp⟩⟩,rfl⟩

lemma cubicThetaUnitRow_injective : Function.Injective cubicThetaUnitRow := by
  intro u v h
  apply Units.ext
  exact congrArg (fun r : CubicThetaZeroFirstRow => r.val.d) h

lemma cubicThetaUnitRow_surjective : Function.Surjective cubicThetaUnitRow := by
  intro r
  have hu : IsUnit r.val.d := isCoprime_zero_left.mp (by simpa only [r.property] using r.val.coprime)
  obtain ⟨u,hu⟩ := hu
  refine ⟨u,?_⟩
  apply Subtype.ext
  apply CubicThetaPrimitiveRow.ext
  · exact r.property.symm
  · exact hu

def cubicThetaZeroFirstRowEquiv : Eisensteinˣ ≃ CubicThetaZeroFirstRow :=
  Equiv.ofBijective cubicThetaUnitRow ⟨cubicThetaUnitRow_injective,cubicThetaUnitRow_surjective⟩

lemma cubicThetaUnitRow_height (u : Eisensteinˣ) (p : ℂ × ℝ) :
    (cubicThetaUnitRow u).val.height p=p.2 := by
  change p.2/(Complex.normSq ((0:ℂ)*p.1+((u:Eisenstein):ℂ))+norm (0:Eisenstein)*p.2^2)=p.2
  rw [zero_mul,zero_add,show Complex.normSq ((u:Eisenstein):ℂ)=1 from norm_of_isUnit u.isUnit]
  simp [norm]

lemma cubicThetaZeroFirstRows_finite : Finite CubicThetaZeroFirstRow := by
  let : Finite (Eisensteinˣ) := idealTheta_units_finite
  exact Finite.of_equiv (Eisensteinˣ) cubicThetaZeroFirstRowEquiv

end CubicFirstMoment

end

end OAI
