import OAI.MathematicalPhysics.Heisenberg.SpinFieldDynamics

namespace OAI

section
noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace Heisenberg
variable {d ℓ : ℕ}

lemma hom_ext_localUnit (f g : QuasiLocal d ℓ →⋆ₐ[ℂ] QuasiLocal d ℓ)
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x a b,f (localUnit d ℓ x a b)=g (localUnit d ℓ x a b)) : f=g := by
  apply DFunLike.ext
  intro A
  have hs : (localCore d ℓ : Set (QuasiLocal d ℓ))⊆{B | f B=g B} := by
    intro B hB
    exact StarAlgHom.adjoin_le_equalizer f g (by rintro _ ⟨x,a,b,rfl⟩; exact h x a b) hB
  exact (isClosed_eq hf hg).closure_subset_iff.mpr hs ((localCore_dense d ℓ) A)

lemma translation_add (x y : Site d) (A : QuasiLocal d ℓ) :
    translation d ℓ x (translation d ℓ y A)=translation d ℓ (x+y) A := by
  have h : (translation d ℓ x).comp (translation d ℓ y)=translation d ℓ (x+y) := by
    apply hom_ext_localUnit
    · exact (translationLinear d ℓ x).continuous.comp (translationLinear d ℓ y).continuous
    · exact (translationLinear d ℓ (x+y)).continuous
    · intro z a b
      simp only [StarAlgHom.comp_apply,translation_localUnit,add_assoc]
  exact DFunLike.congr_fun h A

lemma translation_zero (A : QuasiLocal d ℓ) : translation d ℓ 0 A=A := by
  have h : translation d ℓ 0=StarAlgHom.id ℂ (QuasiLocal d ℓ) := by
    apply hom_ext_localUnit (hf:=(translationLinear d ℓ 0).continuous) (hg:=continuous_id)
    intro z a b
    change translation d ℓ 0 (localUnit d ℓ z a b)=localUnit d ℓ z a b
    simp only [translation_localUnit,zero_add]
  exact DFunLike.congr_fun h A

lemma nearestNeighbor_add (x y z : Site d) : NearestNeighbor (x+y) (x+z) ↔ NearestNeighbor y z := by
  simp only [NearestNeighbor,Pi.add_apply,add_sub_add_left_eq_sub]

lemma translation_bond (x y z : Site d) : translation d ℓ x (bond d ℓ y z)=bond d ℓ (x+y) (x+z) := by
  have hadd (A B : QuasiLocal d ℓ) :
      translation d ℓ x (A + B) = translation d ℓ x A + translation d ℓ x B :=
    (translation d ℓ x).map_add' A B
  have hmul (A B : QuasiLocal d ℓ) :
      translation d ℓ x (A * B) = translation d ℓ x A * translation d ℓ x B :=
    (translation d ℓ x).map_mul' A B
  simp only [bond, hadd, hmul, translation_spinX, translation_spinY, translation_spinZ]

lemma directed_bond_double_sum (Λ : Finset (Site d)) :
    (∑ x∈Λ,∑ y∈Λ,if NearestNeighbor x y then bond d ℓ x y else 0)=2 • (-hamiltonian d ℓ Λ) := by
  rw [←directed_bond_sum Λ,sum_siteEdges (fun x y : Λ=>NearestNeighbor x.val y.val) (fun x y : Λ=>bond d ℓ x.val y.val),Fintype.sum_prod_type]
  rw [←Finset.sum_coe_sort Λ]
  apply Finset.sum_congr rfl
  intro x _
  exact (Finset.sum_coe_sort Λ _).symm

lemma translation_hamiltonian (x : Site d) (Λ : Finset (Site d)) :
    translation d ℓ x (hamiltonian d ℓ Λ)=hamiltonian d ℓ (Λ.image (fun y=>x+y)) := by
  have he :=congrArg (translation d ℓ x) (directed_bond_double_sum (ℓ:=ℓ) Λ)
  have hsum : translation d ℓ x (∑ y∈Λ,∑ z∈Λ,if NearestNeighbor y z then bond d ℓ y z else 0)=
      ∑ y∈Λ.image (fun y=>x+y),∑ z∈Λ.image (fun y=>x+y),if NearestNeighbor y z then bond d ℓ y z else 0 := by
    rw [Finset.sum_image (fun _ _ _ _ he=>add_left_cancel he)]
    simp_rw [Finset.sum_image (fun _ _ _ _ he=>add_left_cancel he)]
    simp only [map_sum,apply_ite,map_zero,translation_bond,nearestNeighbor_add]
  rw [hsum,directed_bond_double_sum,map_nsmul,map_neg] at he
  have he2 : (2:ℂ) • (-hamiltonian d ℓ (Λ.image (fun y=>x+y)))=(2:ℂ) • (-translation d ℓ x (hamiltonian d ℓ Λ)) := by
    simpa only [two_smul] using he
  have he' := congrArg (fun A : QuasiLocal d ℓ=>(1/2:ℂ) • A) he2
  norm_num only [smul_smul,one_div,inv_mul_cancel₀ (by norm_num : (2:ℂ)≠0),one_smul] at he'
  exact neg_injective he'.symm

lemma translation_exp (x : Site d) (A : QuasiLocal d ℓ) :
    translation d ℓ x (NormedSpace.exp A)=NormedSpace.exp (translation d ℓ x A) := by
  let : NormedAlgebra ℚ (QuasiLocal d ℓ):=NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.map_exp (translation d ℓ x) (translationLinear d ℓ x).continuous A

lemma translation_finiteDynamics (x : Site d) (Λ : Finset (Site d)) (t : ℝ) (A : QuasiLocal d ℓ) :
    translation d ℓ x (finiteDynamics d ℓ Λ t A)=
      finiteDynamics d ℓ (Λ.image (fun y=>x+y)) t (translation d ℓ x A) := by
  have hmul (B C : QuasiLocal d ℓ) :
      translation d ℓ x (B * C) = translation d ℓ x B * translation d ℓ x C :=
    (translation d ℓ x).map_mul' B C
  have hsmul (scalar : ℂ) (B : QuasiLocal d ℓ) :
      translation d ℓ x (scalar • B) = scalar • translation d ℓ x B :=
    (translation d ℓ x).toAlgHom.toLinearMap.map_smul scalar B
  simp only [finiteDynamics, hmul, translation_exp, hsmul, translation_hamiltonian]

end Heisenberg
end
end

end OAI
