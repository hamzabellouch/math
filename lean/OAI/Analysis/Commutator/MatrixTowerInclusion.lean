import Mathlib
import OAI.Analysis.Commutator.MatrixTower

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (F : ℕ → Stage M)

variable [Nontrivial M] (hF : Monotone (fun n => (F n).hom.range))

lemma stage_injective (n : ℕ) : Function.Injective (F n).hom :=
  (F n).hom.toAlgHom.toRingHom.injective

def stageInclusion {n m : ℕ} (h : n ≤ m) :
    Matrix (F n).I (F n).I ℂ →⋆ₐ[ℂ] Matrix (F m).I (F m).I ℂ :=
  (StarAlgEquiv.ofInjective (F m).hom (stage_injective M F m)).symm.toStarAlgHom.comp
    ((StarSubalgebra.inclusion (hF h)).comp (F n).hom.rangeRestrict)

lemma stageInclusion_commutes {n m : ℕ} (h : n ≤ m) (a : Matrix (F n).I (F n).I ℂ) :
    (F m).hom (stageInclusion M F hF h a)=(F n).hom a := by
  let e := StarAlgEquiv.ofInjective (F m).hom (stage_injective M F m)
  let b : (F m).hom.range := ⟨(F n).hom a,hF h ⟨a,rfl⟩⟩
  exact congrArg Subtype.val (e.apply_symm_apply b)

omit [Nontrivial M] in
lemma unbounded_above_of_sizes (hsize : ∀ n,n+1 ≤ Fintype.card (F n).I) (n q : ℕ) :
    ∃ m,n ≤ m ∧ q ≤ Fintype.card (F m).I := by
  refine ⟨max n q,le_max_left _ _,?_⟩
  exact (le_max_right n q).trans ((Nat.le_succ _).trans (hsize _))

end Kadison.MatrixTower

end

end
end

end OAI
