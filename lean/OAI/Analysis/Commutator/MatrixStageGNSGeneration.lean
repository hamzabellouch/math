import Mathlib
import OAI.Analysis.Commutator.MatrixTowerGNS

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison.NormalGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hnormal : BoundedWOTContinuous M τ)
  (I : ℕ → Type*) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)]
  (φ : ∀ n,Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] M)

def representedStages : StarSubalgebra ℂ (H →L[ℂ] H) :=
  iSup fun n => (M.toStarSubalgebra.subtype.comp (φ n)).range

lemma representedStages_le : representedStages M I φ≤M.toStarSubalgebra := by
  apply iSup_le
  intro n
  rintro a ⟨b,rfl⟩
  exact (φ n b).property

include hnormal in
theorem matrix_stages_gns (a : M)
    (ha : (a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer
      (representedStages M I φ : Set (H →L[ℂ] H)))) :
    τ.gnsStarAlgHom a∈Set.centralizer (Set.centralizer
      (TracialGNS.stageAlgebra τ I φ : Set _)) := by
  let S := TracialGNS.stageAlgebra τ I φ
  let N := bicommutant S
  let T := (N.toStarSubalgebra.comap τ.gnsStarAlgHom).map M.toStarSubalgebra.subtype
  have hST : representedStages M I φ≤T := by
    apply iSup_le
    intro n
    rintro x ⟨b,rfl⟩
    refine ⟨φ n b,?_,rfl⟩
    exact subset_bicommutant S
      ((le_iSup (TracialGNS.operatorStage τ I φ) n) ⟨b,rfl⟩)
  have hSN (b : M) (hb : (b:H →L[ℂ] H)∈representedStages M I φ) :
      τ.gnsStarAlgHom b∈N := by
    obtain ⟨c,hc,hcb⟩ := hST hb
    have he : c=b := Subtype.ext hcb
    change τ.gnsStarAlgHom c∈N at hc
    simpa only [he] using hc
  exact (mem_bicommutant S _).mp
    (image_bicommutant_general M τ hnormal (representedStages M I φ)
      (representedStages_le M I φ) N hSN a ha)

end Kadison.NormalGNS

end

end
end

end OAI
