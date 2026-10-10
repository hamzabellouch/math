import OAI.Analysis.KadisonKastler.TypeICyclicGeneration
import OAI.Analysis.KadisonKastler.HilbertMatrixGeneration
import OAI.Analysis.KadisonKastler.MatrixFactorDixmier

namespace OAI

/-! # Finite type I averaging in the original representation -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] {M : VonNeumannAlgebra H}

/-- A finite orthonormal basis in the minimal cyclic representation supplies
the full matrix average in the given ambient representation. -/
theorem publishedDixmierOfFiniteTypeICyclic (hM : ScalarCenter M)
    (p : AlgebraProjection M) (hp : IsMinimalProjectionIn M p)
    (ξ : H) (hξ : ξ ≠ 0) (hpξ : p.val.val ξ = ξ)
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (typeICyclicSpace M ξ)) :
    PublishedDixmierAveraging M := by
  let e := typeICyclicEquiv hM p hp ξ hξ hpξ
  let E := (orthonormalMatrixUnits b).map e.symm.toStarAlgHom
  have hE : Function.Surjective E.hom := by
    intro a
    obtain ⟨c, hc⟩ := orthonormalMatrixUnits_surjective b (e a)
    refine ⟨c, ?_⟩
    rw [matrixUnits_map_hom, hc]
    exact e.symm_apply_apply a
  exact publishedDixmierOfFullMatrix E hE

end

end KadisonKastler

end OAI
