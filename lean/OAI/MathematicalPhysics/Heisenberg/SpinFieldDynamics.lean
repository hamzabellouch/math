import OAI.MathematicalPhysics.Heisenberg.SpinDeep

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace GibbsStrip
variable {E : Type*} [CStarAlgebra E]
local instance : NormedAlgebra ℚ E:=NormedAlgebra.restrictScalars ℚ ℂ E

lemma evolve_hamiltonian_add (H K : E) (hHK : Commute H K) (z : ℂ) (A : E) :
    evolve (H+K) z A=evolve H z (evolve K z A) := by
  unfold evolve
  rw [smul_add,NormedSpace.exp_add_of_commute ((hHK.smul_left _).smul_right _)]
  have he : (-(Complex.I*z)) • (H+K)=(-(Complex.I*z)) • K+(-(Complex.I*z)) • H:=by module
  rw [he,NormedSpace.exp_add_of_commute ((hHK.symm.smul_left _).smul_right _)]
  simp only [mul_assoc]

lemma evolve_of_commute (K A : E) (hKA : Commute K A) (z : ℂ) : evolve K z A=A := by
  rw [evolve,((hKA.smul_left (Complex.I*z)).exp_left).eq,mul_assoc,exp_cancel_left,mul_one]

lemma evolve_smul_real (K A : E) (h : ℝ) (z : ℂ) :
    evolve (h • K) z A=evolve K ((h:ℂ)*z) A := by
  rw [←IsScalarTower.algebraMap_smul ℂ h K]
  simp only [evolve,smul_smul,Complex.coe_algebraMap]
  congr 2 <;> congr 1 <;> ring_nf

lemma evolve_sub (K A B : E) (z : ℂ) : evolve K z (A-B)=evolve K z A-evolve K z B := by
  simp only [evolve,mul_sub,sub_mul]

lemma real_evolve_dist (K : E) (hK : IsSelfAdjoint K) (t : ℝ) (A B : E) :
    dist (evolve K t A) (evolve K t B)=dist A B := by
  rw [dist_eq_norm,←evolve_sub,real_evolve_norm hK,dist_eq_norm]

end GibbsStrip
namespace Heisenberg
variable {d ℓ : ℕ}

lemma totalZ_mem_localAlgebra (F : Finset (Site d)) :
    totalZ (ℓ:=ℓ) F∈localAlgebra d ℓ (F : Set (Site d)) := by
  apply (localAlgebra d ℓ (F : Set (Site d))).sum_mem
  intro x hx
  exact spinZ_mem_localAlgebra d ℓ _ hx

lemma totalZ_commute (F G : Finset (Site d)) : Commute (totalZ (ℓ:=ℓ) F) (totalZ G) := by
  apply Commute.sum_left
  intro x hx
  apply Commute.sum_right
  intro y hy
  by_cases hxy : x=y
  · subst y
    exact Commute.refl _
  · exact singleton_local_commute hxy (spinZ_mem_localAlgebra d ℓ {x} rfl)
      (spinZ_mem_localAlgebra d ℓ {y} rfl)

lemma totalZ_split {F Γ : Finset (Site d)} (hF : F⊆Γ) :
    totalZ (ℓ:=ℓ) Γ=totalZ F+totalZ (Γ\F) := by
  unfold totalZ
  exact (Finset.sum_sdiff hF).symm.trans (add_comm _ _)

lemma local_field_evolve {F Γ : Finset (Site d)} (hF : F⊆Γ) {A : QuasiLocal d ℓ}
    (hA : A∈localAlgebra d ℓ (F : Set (Site d))) (z : ℂ) :
    GibbsStrip.evolve (totalZ Γ) z A=GibbsStrip.evolve (totalZ F) z A := by
  rw [totalZ_split hF,GibbsStrip.evolve_hamiltonian_add _ _ (totalZ_commute F (Γ\F))]
  rw [GibbsStrip.evolve_of_commute _ _ (localAlgebras_commute _ (totalZ_mem_localAlgebra (Γ\F)) hA)]
  exact Set.disjoint_left.mpr (fun _ hx hy=>(Finset.mem_sdiff.mp hx).2 hy)

lemma shiftedField_evolve (Γ : Finset (Site d)) (h t : ℝ) (A : QuasiLocal d ℓ) :
    GibbsStrip.evolve (shiftedField Γ h) t A=
      finiteDynamics d ℓ Γ t (GibbsStrip.evolve (totalZ Γ) ((-h*t:ℝ):ℂ) A) := by
  let c : ℝ:=(Fintype.card (SlotTensor.SiteEdges (fun x y : Γ=>NearestNeighbor x.val y.val)):ℝ)*(ℓ:ℝ)^2/8
  have hc : Commute (hamiltonian d ℓ Γ+c • (1:QuasiLocal d ℓ)) (h • totalZ (ℓ:=ℓ) Γ) :=
    ((field_commute (ℓ:=ℓ) Γ).smul_right h).add_left ((Commute.one_left (h • totalZ (ℓ:=ℓ) Γ)).smul_left c)
  change GibbsStrip.evolve (hamiltonian d ℓ Γ+c • (1:QuasiLocal d ℓ)-h • totalZ (ℓ:=ℓ) Γ) t A=_
  rw [sub_eq_add_neg,GibbsStrip.evolve_hamiltonian_add _ _ hc.neg_right]
  rw [GibbsStrip.evolve_hamiltonian_add _ _ ((Commute.one_right _).smul_right c)]
  rw [GibbsStrip.evolve_of_commute (c • (1:QuasiLocal d ℓ)) _ ((Commute.one_left _).smul_left c)]
  rw [←neg_smul,GibbsStrip.evolve_smul_real]
  simp only [Complex.ofReal_mul,Complex.ofReal_neg]
  rfl

end Heisenberg
end

end OAI
