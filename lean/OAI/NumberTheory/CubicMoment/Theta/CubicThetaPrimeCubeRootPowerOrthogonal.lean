import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootPowerCharacter

namespace OAI

/-! Vanishing of the second and fourth dilation pairings on the actual
cubic root cover, forced by their nontrivial diagonal characters. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRoot_diagonal_character {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootCoverGroup hp) : cubicSymbol p (g.val.val 0 0)=1 := by
  have hc : p^2∣g.val.val 1 0 := (show p^2∣(p^3)^2 from ⟨p^4,by ring⟩).trans g.property.1
  have hd : p∣g.val.val 0 0-g.val.val 1 1 := (dvd_pow_self p (by decide : 3≠0)).trans g.property.2
  exact cubicThetaPrimeRoot_diagonal_character hp (⟨g.val,hc,hd⟩ : cubicThetaPrimeRootSubgroup p)

def cubicThetaPrimeSixthPowerIwahori {p : Eisenstein} (n : ℕ) (hn : n≤6)
    (g : cubicThetaPrimeIwahori (p^6)) : cubicThetaPrimeIwahori (p^n) :=
  ⟨g.val,(pow_dvd_pow p hn).trans g.property⟩

lemma cubicThetaPrimeCubeRootPower_pair_invariant {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (hn : n≤6) (F G : CubicThetaSection)
    (g : cubicThetaPrimeCubeRootCoverGroup hp) (x : CubicThetaPoint) :
    star (F.val (g • x))*
        G.val (cubicThetaPrimeDilation (pow_ne_zero n hp.2.ne_zero) • (g • x))=
      star (F.val x)*G.val (cubicThetaPrimeDilation (pow_ne_zero n hp.2.ne_zero) • x) := by
  have hc6 : p^6∣g.val.val 1 0 := by simpa only [←pow_mul] using g.property.1
  let i : cubicThetaPrimeIwahori (p^n) := ⟨g.val,(pow_dvd_pow p hn).trans hc6⟩
  have hG := cubicThetaPrimePowerDilation_transform hp n i G x
  have hχ : cubicSymbol p (i.val.val 0 0)=1 := cubicThetaPrimeCubeRoot_diagonal_character hp g
  rw [hχ,one_pow,star_one,one_mul] at hG
  change star (F.val (g.val • x))*
    G.val (cubicThetaPrimeDilation (pow_ne_zero n hp.2.ne_zero) • (g.val • x))=_
  rw [F.property,hG,star_mul]
  have hk : star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  calc
    _ = (star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val)*
        (star (F.val x)*G.val (cubicThetaPrimeDilation (pow_ne_zero n hp.2.ne_zero) • x)) := by ring
    _ = _ := by rw [hk,one_mul]

lemma cubicThetaPrimeCubeRootPower_pair_zero_of_character {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (hn : n≤6) (g : cubicThetaPrimeIwahori (p^6))
    (hχ : (cubicSymbol p (g.val.val 0 0))^n≠1) (F G : CubicThetaSection) :
    (∫ x in cubicThetaPrimeCubeRootCoverDomain hp,
      star (F.val x)*G.val (cubicThetaPrimeDilation (pow_ne_zero n hp.2.ne_zero) • x)
        ∂cubicThetaPointMeasure)=0 := by
  let f : CubicThetaPoint → ℂ := fun x =>
    star (F.val x)*G.val (cubicThetaPrimeDilation (pow_ne_zero n hp.2.ne_zero) • x)
  let c := star ((cubicSymbol p (g.val.val 0 0))^n)
  have hc : c≠1 := by
    intro he
    apply hχ
    simpa only [c,star_star,star_one] using congrArg star he
  have hi := (cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).setIntegral_eq (f:=f)
    (cubicThetaPrimeCubeRootIwahoriImage_fundamental hp (cubicThetaPrimeSixthCubeIwahori g))
    (cubicThetaPrimeCubeRootPower_pair_invariant hp n hn F G)
  have hm := (measurePreserving_smul g.val cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul g.val) f (cubicThetaPrimeCubeRootCoverDomain hp)
  have he : (∫ x in cubicThetaPrimeCubeRootCoverDomain hp,f x ∂cubicThetaPointMeasure)=
      ∫ x in cubicThetaPrimeCubeRootCoverDomain hp,f (g.val • x) ∂cubicThetaPointMeasure := hi.trans hm
  have hfun : (fun x => f (g.val • x))=fun x => c*f x := by
    funext x
    have hG := cubicThetaPrimePowerDilation_transform hp n
      (cubicThetaPrimeSixthPowerIwahori n hn g) G x
    change G.val (cubicThetaPrimeDilation (pow_ne_zero n hp.2.ne_zero) • (g.val • x))=
      star ((cubicSymbol p (g.val.val 0 0))^n)*cubicThetaKubotaValue g.val*
        G.val (cubicThetaPrimeDilation (pow_ne_zero n hp.2.ne_zero) • x) at hG
    dsimp only [f,c]
    rw [F.property,hG,star_mul]
    have hk : star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val=1 := by
      rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
      norm_num
    calc
      _ = (star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val)*
        (star ((cubicSymbol p (g.val.val 0 0))^n)*
          (star (F.val x)*G.val (cubicThetaPrimeDilation (pow_ne_zero n hp.2.ne_zero) • x))) := by ring
      _ = _ := by rw [hk,one_mul]
  rw [hfun,integral_const_mul] at he
  exact eq_zero_of_mul_eq_self_left hc he.symm

theorem cubicThetaPrimeCubeRootSquare_pair_zero {p : Eisenstein} (hp : primaryPrime p)
    (F G : CubicThetaSection) :
    (∫ x in cubicThetaPrimeCubeRootCoverDomain hp,
      star (F.val x)*G.val (cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero) • x)
        ∂cubicThetaPointMeasure)=0 := by
  obtain ⟨g,hg⟩ := cubicThetaPrimeSixthCharacter_nontrivial hp
  have hc : cubicSymbol p (g.val.val 0 0)≠1 := hg
  have h3 : (cubicSymbol p (g.val.val 0 0))^3=1 :=
    cubicThetaPrimeIwahoriCharacter_cube hp (cubicThetaPrimeSixthIwahori g)
  apply cubicThetaPrimeCubeRootPower_pair_zero_of_character hp 2 (by decide) g _ F G
  intro h2
  rw [pow_succ,h2,one_mul] at h3
  exact hc h3

theorem cubicThetaPrimeCubeRootFourth_pair_zero {p : Eisenstein} (hp : primaryPrime p)
    (F G : CubicThetaSection) :
    (∫ x in cubicThetaPrimeCubeRootCoverDomain hp,
      star (F.val x)*G.val (cubicThetaPrimeDilation (pow_ne_zero 4 hp.2.ne_zero) • x)
        ∂cubicThetaPointMeasure)=0 := by
  obtain ⟨g,hg⟩ := cubicThetaPrimeSixthCharacter_nontrivial hp
  have hc : cubicSymbol p (g.val.val 0 0)≠1 := hg
  have h3 : (cubicSymbol p (g.val.val 0 0))^3=1 :=
    cubicThetaPrimeIwahoriCharacter_cube hp (cubicThetaPrimeSixthIwahori g)
  apply cubicThetaPrimeCubeRootPower_pair_zero_of_character hp 4 (by decide) g _ F G
  intro h4
  rw [show (cubicSymbol p (g.val.val 0 0))^4=(cubicSymbol p (g.val.val 0 0))^3*
    cubicSymbol p (g.val.val 0 0) by ring,h3,one_mul] at h4
  exact hc h4

end CubicFirstMoment

end

end OAI
