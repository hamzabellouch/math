import Mathlib
import OAI.Analysis.Commutator.AtomicDecomposition
import OAI.Analysis.Commutator.AtomicShift

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.AtomicFactor.Decomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} (D : Decomposition M p)

theorem two_isometries [Infinite D.I] :
    ∃ s t : M,star s*s=1 ∧ star t*t=1 ∧ star s*t=0 := by
  classical
  obtain ⟨e⟩ : Nonempty (D.I ≃ D.I×Bool) := by
    apply Cardinal.eq.mp
    rw [Cardinal.mk_prod,Cardinal.mk_bool]
    simpa using (Cardinal.mul_eq_left (Cardinal.aleph0_le_mk D.I)
      ((Cardinal.natCast_le_aleph0 (n:=2)).trans (Cardinal.aleph0_le_mk D.I)) (by norm_num)).symm
  let f : D.I → D.I := fun i => e.symm (i,false)
  let g : D.I → D.I := fun i => e.symm (i,true)
  have hf : Function.Injective f := by
    intro i j h
    exact congrArg Prod.fst (e.symm.injective h)
  have hg : Function.Injective g := by
    intro i j h
    exact congrArg Prod.fst (e.symm.injective h)
  have hfg : ∀ i j,f i≠g j := by
    intro i j h
    have he := congrArg Prod.snd (e.symm.injective h)
    exact Bool.false_ne_true he
  obtain ⟨W,hWM,hW⟩ := D.exists_shift f hf
  obtain ⟨V,hVM,hV⟩ := D.exists_shift g hg
  refine ⟨⟨W,hWM⟩,⟨V,hVM⟩,?_,?_,?_⟩
  · apply Subtype.ext
    exact D.shift_isometry f hf hW
  · apply Subtype.ext
    exact D.shift_isometry g hg hV
  · apply Subtype.ext
    exact D.shifts_orthogonal f g hfg hW hV

end Kadison.AtomicFactor.Decomposition

end

end
end

end OAI
