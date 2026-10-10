import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootDilationOrthogonal

namespace OAI

/-! The second dilation has the other nontrivial cubic character on
the subgroup with lower-left entry divisible by the prime square. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeSquareIwahori {p : Eisenstein} (g : cubicThetaPrimeIwahori (p^2)) :
    cubicThetaPrimeIwahori p :=
  ⟨g.val,(dvd_pow_self p (by decide : 2≠0)).trans g.property⟩

def cubicThetaPrimeSquareConjugate {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^2)) : cubicThetaPrimeIwahori p :=
  ⟨cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareIwahori g),by
    change p∣g.val.val 1 0/p
    obtain ⟨b,hb⟩ := g.property
    rw [hb,pow_two,mul_assoc,mul_div_cancel_left₀ _ hp.2.ne_zero]
    exact dvd_mul_right p b⟩

lemma cubicThetaPrimeSquareConjugate_kubota {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^2)) :
    cubicThetaKubotaValue (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareConjugate hp g))=
      cubicThetaPrimeIwahoriCharacter p hp (cubicThetaPrimeSquareIwahori g)*
        cubicThetaKubotaValue g.val := by
  let c := cubicThetaPrimeIwahoriCharacter p hp (cubicThetaPrimeSquareIwahori g)
  have h1 := cubicThetaPrimeConjugate_kubota hp (cubicThetaPrimeSquareIwahori g)
  have h2 := cubicThetaPrimeConjugate_kubota hp (cubicThetaPrimeSquareConjugate hp g)
  have hc : cubicThetaPrimeIwahoriCharacter p hp (cubicThetaPrimeSquareConjugate hp g)=c := rfl
  rw [hc] at h2
  change cubicThetaKubotaValue (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareIwahori g))=
    c*cubicThetaKubotaValue (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareConjugate hp g)) at h2
  change cubicThetaKubotaValue g.val=c*
    cubicThetaKubotaValue (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareIwahori g)) at h1
  have he := h1.trans (congrArg (fun z : ℂ => c*z) h2)
  have h3 : c^3=1 := cubicThetaPrimeIwahoriCharacter_cube hp (cubicThetaPrimeSquareIwahori g)
  change _=c*cubicThetaKubotaValue g.val
  rw [he]
  calc
    _ = 1*cubicThetaKubotaValue
        (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareConjugate hp g)) := by rw [one_mul]
    _ = c^3*cubicThetaKubotaValue
        (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareConjugate hp g)) := by rw [h3]
    _ = _ := by ring

theorem cubicThetaPrimeSquareCharacter_nontrivial {p : Eisenstein} (hp : primaryPrime p) :
    ∃ g : cubicThetaPrimeIwahori (p^2),
      cubicThetaPrimeIwahoriCharacter p hp (cubicThetaPrimeSquareIwahori g)≠1 := by
  obtain ⟨d,hd,hpd,hχ⟩ := cubicThetaPrime_primary_nontrivial hp
  let r : CubicThetaBottomRow :=
    ⟨3*p^2,d,dvd_mul_right 3 (p^2),hd,(primary_coprime_three hd).symm.mul_left hpd.pow_left⟩
  let g : cubicThetaPrimeIwahori (p^2) := ⟨r.completion,by
    have hc := congrArg CubicThetaBottomRow.c r.completion_row
    change r.completion.val 1 0=3*p^2 at hc
    change p^2∣r.completion.val 1 0
    rw [hc]
    exact dvd_mul_left (p^2) 3⟩
  refine ⟨g,?_⟩
  have hr := congrArg CubicThetaBottomRow.d r.completion_row
  change r.completion.val 1 1=d at hr
  have he : p∣g.val.val 0 0*d-1 := by
    have hg := cubicThetaPrincipalGroup_det g.val
    rw [show g.val.val 1 1=d from hr] at hg
    rw [show g.val.val 0 0*d-1=g.val.val 0 1*g.val.val 1 0 by linear_combination hg]
    exact dvd_mul_of_dvd_right (cubicThetaPrimeSquareIwahori g).property _
  have hone : cubicSymbol p (g.val.val 0 0*d)=1 := by
    rw [cubicSymbol_congr (residue_eq_of_dvd_sub he)]
    simpa only [pow_zero] using cubicSymbol_pow_upper hp.1 1 0
  rw [cubicSymbol_mul_upper hp.1] at hone
  intro htriv
  change cubicSymbol p (g.val.val 0 0)=1 at htriv
  rw [htriv,one_mul] at hone
  exact hχ hone

end CubicFirstMoment

end

end OAI
