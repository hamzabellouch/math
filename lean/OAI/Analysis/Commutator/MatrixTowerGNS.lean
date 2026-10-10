import Mathlib
import OAI.Analysis.Commutator.MatrixTowerClosure
import OAI.Analysis.Commutator.NormalGNSClosure
import OAI.Analysis.Commutator.StageGeneration

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.NormalGNS

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def bicommutant (S : StarSubalgebra ℂ (K →L[ℂ] K)) : VonNeumannAlgebra K where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ (S : Set (K →L[ℂ] K)))
  centralizer_centralizer' := by
    have h : ((StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ (S : Set (K →L[ℂ] K)))) :
        StarSubalgebra ℂ (K →L[ℂ] K)).carrier =
        Set.centralizer (Set.centralizer (S : Set (K →L[ℂ] K))) := by
      exact (StarSubalgebra.coe_centralizer_centralizer ℂ _).trans (by
        rw [StarMemClass.star_coe_eq,Set.union_self])
    change _ = ((StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (S : Set (K →L[ℂ] K)))) : StarSubalgebra ℂ (K →L[ℂ] K)).carrier
    rw [h]
    simp only [Set.centralizer_centralizer_centralizer]

lemma mem_bicommutant (S : StarSubalgebra ℂ (K →L[ℂ] K)) (a : K →L[ℂ] K) :
    a∈bicommutant S ↔ a∈Set.centralizer (Set.centralizer (S : Set (K →L[ℂ] K))) := by
  change a∈(StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ (S : Set (K →L[ℂ] K)))) ↔ _
  rw [←SetLike.mem_coe,StarSubalgebra.coe_centralizer_centralizer,StarMemClass.star_coe_eq,Set.union_self]

lemma subset_bicommutant (S : StarSubalgebra ℂ (K →L[ℂ] K)) : S≤(bicommutant S).toStarSubalgebra := by
  intro a ha
  exact (mem_bicommutant S a).mpr (Set.subset_centralizer_centralizer ha)

end Kadison.NormalGNS

namespace Kadison.MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (F : ℕ → Stage M)

variable (τ : generated M F →ₚ[ℂ] ℂ)

variable (hnormal : NormalGNS.BoundedWOTContinuous (generated M F) τ)

include hnormal in
theorem generated_gns_dense (a : generated M F) :
    τ.gnsStarAlgHom a∈Set.centralizer (Set.centralizer
      (TracialGNS.stageAlgebra τ (fun n => (F n).I) (stageHom M F) : Set _)) := by
  let S := TracialGNS.stageAlgebra τ (fun n => (F n).I) (stageHom M F)
  let N := NormalGNS.bicommutant S
  let T := (N.toStarSubalgebra.comap τ.gnsStarAlgHom).map (generated M F).toStarSubalgebra.subtype
  have hST : stageAlgebra M F≤T := by
    apply iSup_le
    intro n
    rintro x ⟨b,rfl⟩
    refine ⟨stageHom M F n b,?_,rfl⟩
    exact NormalGNS.subset_bicommutant S
      ((le_iSup (TracialGNS.operatorStage τ (fun n => (F n).I) (stageHom M F)) n) ⟨b,rfl⟩)
  have hSN (b : generated M F) (hb : (b:H →L[ℂ] H)∈stageAlgebra M F) : τ.gnsStarAlgHom b∈N := by
    obtain ⟨c,hc,hcb⟩ := hST hb
    have he : c=b := Subtype.ext hcb
    change τ.gnsStarAlgHom c∈N at hc
    simpa only [he] using hc
  have hSM : stageAlgebra M F≤(generated M F).toStarSubalgebra := by
    intro b hb
    exact (mem_generated M F b).mpr (Set.subset_centralizer_centralizer hb)
  exact (NormalGNS.mem_bicommutant S _).mp
    (NormalGNS.image_bicommutant_general (generated M F) τ hnormal (stageAlgebra M F)
      hSM N hSN a ((mem_generated M F a).mp a.property))

end Kadison.MatrixTower

end

end
end

end OAI
