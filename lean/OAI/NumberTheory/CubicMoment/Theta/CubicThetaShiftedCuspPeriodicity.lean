import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedInvertedRows

namespace OAI

/-! Periodicity of the actual translated-cusp row phase. Conjugating a
translation by the cusp matrix gives a principal level-nine matrix with
trivial Kubota value, proved from the supplementary laws. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaCuspTranslationMatrix (b m : Eisenstein) : SL(2,Eisenstein) :=
  ⟨!![1-9*b*m,9*b^2*m;-9*m,1+9*b*m],by
    rw [Matrix.det_fin_two_of]
    ring⟩

lemma cubicThetaCuspTranslationMatrix_mem (b m : Eisenstein) :
    cubicThetaCuspTranslationMatrix b m ∈ cubicThetaPrincipalGroup := by
  apply (cubicThetaPrincipalGroup_mem_iff _).mpr
  change primary (1-9*b*m) ∧ (3:Eisenstein)∣9*b^2*m ∧
    (3:Eisenstein)∣-9*m ∧ primary (1+9*b*m)
  exact ⟨⟨-3*b*m,by ring⟩,⟨3*b^2*m,by ring⟩,⟨-3*m,by ring⟩,⟨3*b*m,by ring⟩⟩

def cubicThetaCuspTranslation (b m : Eisenstein) : cubicThetaPrincipalGroup :=
  ⟨cubicThetaCuspTranslationMatrix b m,cubicThetaCuspTranslationMatrix_mem b m⟩

lemma cubicThetaCuspTranslation_value (b m : Eisenstein) :
    cubicThetaKubotaValue (cubicThetaCuspTranslation b m)=1 := by
  unfold cubicThetaKubotaValue
  split_ifs
  · rfl
  · change cubicSymbol (1-9*b*m) (-9*m)=1
    apply cubicThetaKubota_symbol_one
    · exact ⟨-3*b*m,by ring⟩
    · exact ⟨-b*m,by ring⟩
    · exact ⟨b,by ring⟩

def cubicThetaShiftedRowTranslate (r : CubicThetaInvertedRow) (m : Eisenstein) :
    CubicThetaInvertedRow where
  c := r.c
  d := r.d+9*m*r.c
  c_primary := r.c_primary
  d_three := dvd_add r.d_three ⟨3*m*r.c,by ring⟩
  coprime := by
    obtain ⟨u,v,h⟩ := r.coprime
    refine ⟨u-9*m*v,v,?_⟩
    linear_combination h

lemma cubicThetaShiftedRowTranslate_action (b m : Eisenstein) (r : CubicThetaInvertedRow) :
    ((cubicThetaShiftedInvertedRowEquiv b).symm r).rightMul (cubicThetaCuspTranslation b m) =
      (cubicThetaShiftedInvertedRowEquiv b).symm (cubicThetaShiftedRowTranslate r m) := by
  apply CubicThetaBottomRow.ext
  · rw [CubicThetaBottomRow.rightMul_c]
    change (-r.d)*(1-9*b*m)+(r.c+b*r.d)*(-9*m)= -(r.d+9*m*r.c)
    ring
  · rw [CubicThetaBottomRow.rightMul_d]
    change (-r.d)*(9*b^2*m)+(r.c+b*r.d)*(1+9*b*m)=r.c+b*(r.d+9*m*r.c)
    ring

def cubicThetaShiftedRowPhase (b : Eisenstein) (r : CubicThetaInvertedRow) : ℂ :=
  cubicSymbol (r.c+b*r.d) r.d

lemma cubicThetaShiftedRowPhase_eq (b : Eisenstein) (r : CubicThetaInvertedRow) :
    cubicThetaShiftedRowPhase b r=
      star (((cubicThetaShiftedInvertedRowEquiv b).symm r).phase) := by
  change cubicSymbol (r.c+b*r.d) r.d=star (star (cubicSymbol (r.c+b*r.d) (-r.d)))
  rw [star_star,cubicSymbol_neg (cubicTheta_primary_add_three_mul r.c_primary r.d_three b)]

lemma cubicThetaShiftedRowPhase_periodic (b m : Eisenstein) (r : CubicThetaInvertedRow) :
    cubicThetaShiftedRowPhase b (cubicThetaShiftedRowTranslate r m)=
      cubicThetaShiftedRowPhase b r := by
  have he := ((cubicThetaShiftedInvertedRowEquiv b).symm r).phase_rightMul
    (cubicThetaCuspTranslation b m)
  rw [cubicThetaShiftedRowTranslate_action,cubicThetaCuspTranslation_value,mul_one] at he
  rw [cubicThetaShiftedRowPhase_eq,cubicThetaShiftedRowPhase_eq,he]

lemma cubicThetaShiftedRowPhase_norm (b : Eisenstein) (r : CubicThetaInvertedRow) :
    ‖cubicThetaShiftedRowPhase b r‖=1 := by
  rw [cubicThetaShiftedRowPhase_eq,norm_star,CubicThetaBottomRow.phase_norm]

end CubicFirstMoment

end

end OAI
