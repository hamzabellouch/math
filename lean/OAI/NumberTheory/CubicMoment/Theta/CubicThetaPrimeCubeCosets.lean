import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeTrace

namespace OAI

/-! Concrete bottom-row coordinates for the cubed-prime correspondence.
The first chart is represented by integral lower unipotents in level three. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaPrimeCubeCoset (p : Eisenstein) (g : cubicThetaPrincipalGroup) :
    cubicThetaPrimeCubeTransversal p :=
  ((cubicThetaPrimeCubeTransversal_complement p).equiv g).snd

lemma cubicThetaPrimeCubeCoset_eq_iff (p : Eisenstein)
    (g h : cubicThetaPrincipalGroup) :
    cubicThetaPrimeCubeCoset p g=cubicThetaPrimeCubeCoset p h ↔
      p^3 ∣ h.val 1 0*g.val 1 1-h.val 1 1*g.val 1 0 := by
  rw [cubicThetaPrimeCubeCoset,cubicThetaPrimeCubeCoset,
    (cubicThetaPrimeCubeTransversal_complement p).equiv_snd_eq_iff_rightCosetEquivalence]
  rw [RightCosetEquivalence,rightCoset_eq_iff]
  change p^3 ∣ (h.val*g.val⁻¹) 1 0 ↔ _
  simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.mul_apply,Fin.sum_univ_two,Matrix.adjugate_fin_two,sub_eq_add_neg]

def cubicThetaPrincipalLower (m : Eisenstein) : cubicThetaPrincipalGroup :=
  let g : SL(2,Eisenstein) := ⟨!![1,0;3*m,1],by simp [Matrix.det_fin_two]⟩
  ⟨g,(cubicThetaPrincipalGroup_mem_iff g).mpr
    ⟨primary_one,dvd_zero _,⟨m,rfl⟩,primary_one⟩⟩

lemma cubicThetaPrincipalLower_value (m : Eisenstein) :
    cubicThetaKubotaValue (cubicThetaPrincipalLower m)=1 := by
  rw [cubicThetaKubotaValue_eq_symbol]
  exact cubicSymbol_one_lower _

lemma cubicThetaPrimeCubeCoset_lower_eq_iff {p : Eisenstein} (hp : primaryPrime p)
    (m n : Eisenstein) :
    cubicThetaPrimeCubeCoset p (cubicThetaPrincipalLower m)=
      cubicThetaPrimeCubeCoset p (cubicThetaPrincipalLower n) ↔ p^3 ∣ n-m := by
  rw [cubicThetaPrimeCubeCoset_eq_iff]
  change p^3 ∣ 3*n*1-1*(3*m) ↔ p^3 ∣ n-m
  rw [mul_one,one_mul,←mul_sub]
  constructor
  · exact (primary_coprime_three (cubicThetaPrimeCube_primary hp)).dvd_of_dvd_mul_left
  · exact fun h => dvd_mul_of_dvd_right h 3

def cubicThetaPrimeCubeLowerChart (p : Eisenstein) (r : Residues (p^3)) :
    cubicThetaPrimeCubeTransversal p :=
  cubicThetaPrimeCubeCoset p (cubicThetaPrincipalLower (residueRepresentative (p^3) r))

theorem cubicThetaPrimeCubeLowerChart_injective {p : Eisenstein} (hp : primaryPrime p) :
    Function.Injective (cubicThetaPrimeCubeLowerChart p) := by
  intro r s h
  have hd := (cubicThetaPrimeCubeCoset_lower_eq_iff hp _ _).mp h
  have he := residue_eq_of_dvd_sub hd
  simpa only [residueRepresentative_spec] using he.symm

end CubicFirstMoment

end

end OAI
