import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeBranchCoordinates

namespace OAI

/-! Each triangular branch depends only on its residue parameter, with
the period-three automorphy and the cubic phase both retained. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeBranchPoint_translate {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (b m : Eisenstein) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeBranchPoint hp k (b+p^(3-k.val)*m) x=
      cubicThetaPrincipalTranslation m • cubicThetaPrimeCubeBranchPoint hp k b x := by
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  apply Subtype.ext
  change _=cubicThetaMobius (cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation m)) _
  rw [cubicThetaPrincipalTranslation_complex,cubicThetaMobius_translation]
  apply Prod.ext
  · change (p:ℂ)^k.val/(p:ℂ)^(3-k.val)*x.val.1+
      ((3*(b+p^(3-k.val)*m):Eisenstein):ℂ)/(p:ℂ)^(3-k.val)=
        ((p:ℂ)^k.val/(p:ℂ)^(3-k.val)*x.val.1+((3*b:Eisenstein):ℂ)/(p:ℂ)^(3-k.val))+
          ((3*m:Eisenstein):ℂ)
    push_cast
    field_simp
    ring
  · rfl

lemma cubicThetaPrimeCubeBranch_section_congr {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (b c : Eisenstein) (hbc : p^(3-k.val)∣b-c)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    F.val (cubicThetaPrimeCubeBranchPoint hp k b x)=
      F.val (cubicThetaPrimeCubeBranchPoint hp k c x) := by
  obtain ⟨m,hm⟩ := hbc
  have hb : b=c+p^(3-k.val)*m := by linear_combination hm
  rw [hb,cubicThetaPrimeCubeBranchPoint_translate,F.property,
    cubicThetaPrincipalTranslation_value,one_mul]

lemma cubicThetaPrimeCubeBranch_term_congr {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (b c : Eisenstein) (hbc : p^(3-k.val)∣b-c)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    (cubicSymbol p (3*b))^k.val*F.val (cubicThetaPrimeCubeBranchPoint hp k b x)=
      (cubicSymbol p (3*c))^k.val*F.val (cubicThetaPrimeCubeBranchPoint hp k c x) := by
  have hd : p∣3*b-3*c := by
    rw [←mul_sub]
    exact dvd_mul_of_dvd_right
      ((dvd_pow_self p (by have := k.isLt; omega)).trans hbc) 3
  rw [cubicSymbol_congr (residue_eq_of_dvd_sub hd),
    cubicThetaPrimeCubeBranch_section_congr hp k b c hbc]

end CubicFirstMoment

end

end OAI
