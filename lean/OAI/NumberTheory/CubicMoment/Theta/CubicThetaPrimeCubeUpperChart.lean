import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeLowerChart

namespace OAI

/-! The complementary chart of the cubed-prime correspondence. Its
parameters are the residue classes divisible by the prime. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeWeylDenominator {p : Eisenstein} (hp : primaryPrime p) : Eisenstein :=
  Classical.choose (residue_crt_one (primary_coprime_three (cubicThetaPrimeCube_primary hp)) 0)

lemma cubicThetaPrimeCubeWeylDenominator_dvd {p : Eisenstein} (hp : primaryPrime p) :
    p^3 ∣ cubicThetaPrimeCubeWeylDenominator hp := by
  change p^3 ∣ Classical.choose (residue_crt_one
    (primary_coprime_three (cubicThetaPrimeCube_primary hp)) 0)
  simpa only [sub_zero] using
    (Classical.choose_spec (residue_crt_one
      (primary_coprime_three (cubicThetaPrimeCube_primary hp)) 0)).1

lemma cubicThetaPrimeCubeWeylDenominator_primary {p : Eisenstein} (hp : primaryPrime p) :
    primary (cubicThetaPrimeCubeWeylDenominator hp) :=
  (Classical.choose_spec (residue_crt_one
    (primary_coprime_three (cubicThetaPrimeCube_primary hp)) 0)).2

def cubicThetaPrimeCubeWeylRow {p : Eisenstein} (hp : primaryPrime p) : CubicThetaBottomRow :=
  ⟨3,cubicThetaPrimeCubeWeylDenominator hp,dvd_refl _,
    cubicThetaPrimeCubeWeylDenominator_primary hp,
    (primary_coprime_three (cubicThetaPrimeCubeWeylDenominator_primary hp)).symm⟩

def cubicThetaPrimeCubeWeyl {p : Eisenstein} (hp : primaryPrime p) : cubicThetaPrincipalGroup :=
  (cubicThetaPrimeCubeWeylRow hp).completion

lemma cubicThetaPrimeCubeWeyl_c {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeCubeWeyl hp).val 1 0=3 :=
  congrArg CubicThetaBottomRow.c (cubicThetaPrimeCubeWeylRow hp).completion_row

lemma cubicThetaPrimeCubeWeyl_d {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeCubeWeyl hp).val 1 1=cubicThetaPrimeCubeWeylDenominator hp :=
  congrArg CubicThetaBottomRow.d (cubicThetaPrimeCubeWeylRow hp).completion_row

def cubicThetaPrimeCubeUpperParameter (p : Eisenstein) :=
  {r : Residues (p^3) // p ∣ residueRepresentative (p^3) r}

def cubicThetaPrimeCubeUpperRepresentative {p : Eisenstein} (hp : primaryPrime p)
    (r : cubicThetaPrimeCubeUpperParameter p) : cubicThetaPrincipalGroup :=
  cubicThetaPrimeCubeWeyl hp*cubicThetaPrincipalTranslation (residueRepresentative (p^3) r.val)

lemma cubicThetaPrimeCubeUpperRepresentative_c {p : Eisenstein} (hp : primaryPrime p)
    (r : cubicThetaPrimeCubeUpperParameter p) :
    (cubicThetaPrimeCubeUpperRepresentative hp r).val 1 0=3 := by
  change (((cubicThetaPrimeCubeWeyl hp).val : Matrix (Fin 2) (Fin 2) Eisenstein)*
    !![1,3*residueRepresentative (p^3) r.val;0,1]) 1 0=3
  simp [Matrix.mul_apply,Fin.sum_univ_two,cubicThetaPrimeCubeWeyl_c]

lemma cubicThetaPrimeCubeUpperRepresentative_d {p : Eisenstein} (hp : primaryPrime p)
    (r : cubicThetaPrimeCubeUpperParameter p) :
    (cubicThetaPrimeCubeUpperRepresentative hp r).val 1 1=
      cubicThetaPrimeCubeWeylDenominator hp+9*residueRepresentative (p^3) r.val := by
  change (((cubicThetaPrimeCubeWeyl hp).val : Matrix (Fin 2) (Fin 2) Eisenstein)*
    !![1,3*residueRepresentative (p^3) r.val;0,1]) 1 1=_
  simp only [Matrix.mul_apply,Fin.sum_univ_two]
  change (cubicThetaPrimeCubeWeyl hp).val 1 0*(3*residueRepresentative (p^3) r.val)+
    (cubicThetaPrimeCubeWeyl hp).val 1 1*1=_
  rw [cubicThetaPrimeCubeWeyl_c,cubicThetaPrimeCubeWeyl_d]
  ring

def cubicThetaPrimeCubeUpperChart {p : Eisenstein} (hp : primaryPrime p)
    (r : cubicThetaPrimeCubeUpperParameter p) : cubicThetaPrimeCubeTransversal p :=
  cubicThetaPrimeCubeCoset p (cubicThetaPrimeCubeUpperRepresentative hp r)

theorem cubicThetaPrimeCubeUpperChart_injective {p : Eisenstein} (hp : primaryPrime p) :
    Function.Injective (cubicThetaPrimeCubeUpperChart hp) := by
  intro r s h
  have hd := (cubicThetaPrimeCubeCoset_eq_iff p _ _).mp h
  rw [cubicThetaPrimeCubeUpperRepresentative_c,cubicThetaPrimeCubeUpperRepresentative_c,
    cubicThetaPrimeCubeUpperRepresentative_d,cubicThetaPrimeCubeUpperRepresentative_d] at hd
  have he : p^3 ∣ 27*(residueRepresentative (p^3) r.val-residueRepresentative (p^3) s.val) := by
    convert hd using 1
    ring
  have hc : IsCoprime (p^3) (27:Eisenstein) := by
    convert (primary_coprime_three (cubicThetaPrimeCube_primary hp)).pow_right (n := 3) using 1
    norm_num
  apply Subtype.ext
  simpa only [residueRepresentative_spec] using
    residue_eq_of_dvd_sub (hc.dvd_of_dvd_mul_left he)

end CubicFirstMoment

end

end OAI
