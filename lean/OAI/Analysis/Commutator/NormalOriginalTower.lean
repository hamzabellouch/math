import Mathlib
import OAI.Analysis.Commutator.MatrixTowerGNS
import OAI.Analysis.Commutator.OperatorAmplification

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison.MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (F : ℕ → Stage M)

variable (τ : M →ₚ[ℂ] ℂ) (hnormal : NormalGNS.BoundedWOTContinuous M τ)

include hnormal in
theorem original_gns_generated (a : M) (ha : (a:H →L[ℂ] H)∈generated M F) :
    τ.gnsStarAlgHom a∈Set.centralizer (Set.centralizer
      ((⨆ n,(τ.gnsStarAlgHom.comp (F n).hom).range : StarSubalgebra ℂ (τ.GNS →L[ℂ] τ.GNS)) : Set _)) := by
  let S : StarSubalgebra ℂ (τ.GNS →L[ℂ] τ.GNS) := ⨆ n,(τ.gnsStarAlgHom.comp (F n).hom).range
  let N := NormalGNS.bicommutant S
  let T := (N.toStarSubalgebra.comap τ.gnsStarAlgHom).map M.toStarSubalgebra.subtype
  have hST : stageAlgebra M F≤T := by
    apply iSup_le
    intro n
    rintro x ⟨b,rfl⟩
    refine ⟨(F n).hom b,?_,rfl⟩
    exact NormalGNS.subset_bicommutant S
      ((le_iSup (fun n => (τ.gnsStarAlgHom.comp (F n).hom).range) n) ⟨b,rfl⟩)
  have hSN (b : M) (hb : (b:H →L[ℂ] H)∈stageAlgebra M F) : τ.gnsStarAlgHom b∈N := by
    have hbT := hST hb
    obtain ⟨c,hc,hcb⟩ := hbT
    have he : c=b := Subtype.ext hcb
    change τ.gnsStarAlgHom c∈N at hc
    simpa only [he] using hc
  exact (NormalGNS.mem_bicommutant S _).mp
    (NormalGNS.image_bicommutant_general M τ hnormal (stageAlgebra M F)
      (stageAlgebra_le M F) N hSN a ((mem_generated M F a).mp ha))

private lemma map_stage_range_le {A B : Type*}
    [Semiring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    [Semiring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
    (φ : M →⋆ₐ[ℂ] A) (ψ : A →⋆ₐ[ℂ] B) :
    (⨆ n,(φ.comp (F n).hom).range).map ψ≤
      ⨆ n,(ψ.comp (φ.comp (F n).hom)).range := by
  rw [StarSubalgebra.map_le_iff_le_comap]
  apply iSup_le
  intro n
  rintro x ⟨b,rfl⟩
  exact (le_iSup (fun n => (ψ.comp (φ.comp (F n).hom)).range) n) ⟨b,rfl⟩

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

private lemma copies_generated_of {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (φ : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (a : M)
    (ha : φ a∈Set.centralizer (Set.centralizer
      ((⨆ n,(φ.comp (F n).hom).range : StarSubalgebra ℂ (K →L[ℂ] K)) : Set _))) :
    OperatorAmplification.diagonal (H:=K) ι (φ a)∈Set.centralizer (Set.centralizer
      ((⨆ n,((OperatorAmplification.diagonal (H:=K) ι).comp (φ.comp (F n).hom)).range :
        StarSubalgebra ℂ (OperatorAmplification.SumSpace (H:=K) ι →L[ℂ]
          OperatorAmplification.SumSpace (H:=K) ι)) : Set _)) := by
  let S : StarSubalgebra ℂ (K →L[ℂ] K) := ⨆ n,(φ.comp (F n).hom).range
  let ρ := OperatorAmplification.diagonal (H:=K) ι
  have hSR := map_stage_range_le M F φ ρ
  have h := OperatorAmplification.diagonal_bicommutant ι S ha
  intro T hT
  exact h T (fun x hx => hT x (hSR hx))

include hnormal in
theorem original_copies_generated (a : M) (ha : (a:H →L[ℂ] H)∈generated M F) :
    OperatorAmplification.diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)∈
      Set.centralizer (Set.centralizer
        ((⨆ n,((OperatorAmplification.diagonal (H:=τ.GNS) ι).comp
          (τ.gnsStarAlgHom.comp (F n).hom)).range :
          StarSubalgebra ℂ (OperatorAmplification.SumSpace (H:=τ.GNS) ι →L[ℂ]
            OperatorAmplification.SumSpace (H:=τ.GNS) ι)) : Set _)) := by
  exact copies_generated_of M F ι (K:=τ.GNS) τ.gnsStarAlgHom a
    (original_gns_generated M F τ hnormal a ha)

end Kadison.MatrixTower

end

end
end

end OAI
