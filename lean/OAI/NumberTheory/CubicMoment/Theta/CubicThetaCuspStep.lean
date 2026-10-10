import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedRowWeight

namespace OAI

/-! The three-step translation character of a shifted cusp. It supplies
the ramified finite Fourier factor before the unramified Gauss sum. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaCuspStepMatrix (b m : Eisenstein) : SL(2,Eisenstein) :=
  ⟨!![1-3*b*m,3*b^2*m;-3*m,1+3*b*m],by rw [Matrix.det_fin_two_of]; ring⟩

lemma cubicThetaCuspStepMatrix_mem (b m : Eisenstein) :
    cubicThetaCuspStepMatrix b m∈cubicThetaPrincipalGroup := by
  apply (cubicThetaPrincipalGroup_mem_iff _).mpr
  change primary (1-3*b*m) ∧ (3:Eisenstein)∣3*b^2*m ∧
    (3:Eisenstein)∣-3*m ∧ primary (1+3*b*m)
  exact ⟨⟨-b*m,by ring⟩,⟨b^2*m,by ring⟩,⟨-m,by ring⟩,⟨b*m,by ring⟩⟩

def cubicThetaCuspStep (b m : Eisenstein) : cubicThetaPrincipalGroup :=
  ⟨cubicThetaCuspStepMatrix b m,cubicThetaCuspStepMatrix_mem b m⟩

lemma cubicThetaCuspStep_add (b m n : Eisenstein) :
    cubicThetaCuspStep b (m+n)=cubicThetaCuspStep b m*cubicThetaCuspStep b n := by
  apply Subtype.ext
  apply Subtype.ext
  change (!![1-3*b*(m+n),3*b^2*(m+n);-3*(m+n),1+3*b*(m+n)] : Matrix (Fin 2) (Fin 2) Eisenstein)=
    !![1-3*b*m,3*b^2*m;-3*m,1+3*b*m]*!![1-3*b*n,3*b^2*n;-3*n,1+3*b*n]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two] <;> ring

lemma cubicThetaCuspStep_triple (b m : Eisenstein) :
    cubicThetaCuspStep b (3*m)=cubicThetaCuspTranslation b m := by
  apply Subtype.ext
  apply Subtype.ext
  change (!![1-3*b*(3*m),3*b^2*(3*m);-3*(3*m),1+3*b*(3*m)] : Matrix (Fin 2) (Fin 2) Eisenstein)=
    !![1-9*b*m,9*b^2*m;-9*m,1+9*b*m]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num <;> ring

def cubicThetaCuspStepValue (b m : Eisenstein) : ℂ :=
  cubicThetaKubotaValue (cubicThetaCuspStep b m)

lemma cubicThetaCuspStepValue_add (b m n : Eisenstein) :
    cubicThetaCuspStepValue b (m+n)=cubicThetaCuspStepValue b m*cubicThetaCuspStepValue b n := by
  unfold cubicThetaCuspStepValue
  rw [cubicThetaCuspStep_add,cubicThetaKubotaValue_mul]

lemma cubicThetaCuspStepValue_triple (b m : Eisenstein) : cubicThetaCuspStepValue b (3*m)=1 := by
  rw [cubicThetaCuspStepValue,cubicThetaCuspStep_triple,cubicThetaCuspTranslation_value]

lemma cubicThetaCuspStepValue_periodic (b m n : Eisenstein) :
    cubicThetaCuspStepValue b (m+3*n)=cubicThetaCuspStepValue b m := by
  rw [cubicThetaCuspStepValue_add,cubicThetaCuspStepValue_triple,mul_one]

def cubicThetaShiftedRowStep (r : CubicThetaInvertedRow) (m : Eisenstein) :
    CubicThetaInvertedRow where
  c := r.c
  d := r.d+3*m*r.c
  c_primary := r.c_primary
  d_three := dvd_add r.d_three ⟨m*r.c,by ring⟩
  coprime := (cubicTheta_coprime_add_right r.c r.d (3*m)).mpr r.coprime

lemma cubicThetaShiftedRowStep_action (b m : Eisenstein) (r : CubicThetaInvertedRow) :
    ((cubicThetaShiftedInvertedRowEquiv b).symm r).rightMul (cubicThetaCuspStep b m) =
      (cubicThetaShiftedInvertedRowEquiv b).symm (cubicThetaShiftedRowStep r m) := by
  apply CubicThetaBottomRow.ext
  · rw [CubicThetaBottomRow.rightMul_c]
    change (-r.d)*(1-3*b*m)+(r.c+b*r.d)*(-3*m)= -(r.d+3*m*r.c)
    ring
  · rw [CubicThetaBottomRow.rightMul_d]
    change (-r.d)*(3*b^2*m)+(r.c+b*r.d)*(1+3*b*m)=r.c+b*(r.d+3*m*r.c)
    ring

lemma cubicThetaShiftedRowPhase_step (b m : Eisenstein) (r : CubicThetaInvertedRow) :
    cubicThetaShiftedRowPhase b (cubicThetaShiftedRowStep r m)=
      star (cubicThetaCuspStepValue b m)*cubicThetaShiftedRowPhase b r := by
  have he := ((cubicThetaShiftedInvertedRowEquiv b).symm r).phase_rightMul (cubicThetaCuspStep b m)
  rw [cubicThetaShiftedRowStep_action] at he
  rw [cubicThetaShiftedRowPhase_eq,cubicThetaShiftedRowPhase_eq,he,star_mul]
  rfl

lemma cubicThetaShiftedRowWeight_step {c : Eisenstein} (hc : primary c)
    (b u m : Eisenstein) :
    cubicThetaShiftedRowWeight b c (u+c*m)=
      star (cubicThetaCuspStepValue b m)*cubicThetaShiftedRowWeight b c u := by
  have hd : 3*(u+c*m)=3*u+3*m*c := by ring
  by_cases hcop : IsCoprime c (3*u)
  · let r : CubicThetaInvertedRow := ⟨c,3*u,hc,⟨u,rfl⟩,hcop⟩
    have he := cubicThetaShiftedRowPhase_step b m r
    simpa only [cubicThetaShiftedRowPhase,cubicThetaShiftedRowStep,r,
      cubicThetaShiftedRowWeight,hd] using he
  · have hz (v : Eisenstein) (hv : ¬IsCoprime c (3*v)) : cubicThetaShiftedRowWeight b c v=0 := by
      apply cubicSymbol_eq_zero_of_not_isCoprime (cubicTheta_primary_add_three_mul hc ⟨v,rfl⟩ b)
      rwa [cubicTheta_coprime_add_left]
    have hcop' : ¬IsCoprime c (3*(u+c*m)) := by
      rw [hd,cubicTheta_coprime_add_right]
      exact hcop
    rw [hz _ hcop',hz _ hcop,mul_zero]

end CubicFirstMoment

end

end OAI
