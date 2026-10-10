import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoreCoordinates
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticSupportedSum

namespace OAI

/-! Uniqueness of the supported/free primary split used in the actual
dual cube expansion. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicTheta_primarySmallPart_mul {r a b : Eisenstein}
    (hr : r≠0) (ha : primary a) (hb : primary b)
    (hs : ∃ k : ℕ, a∣r^k) (hcop : IsCoprime b r) :
    primarySmallPart r (a*b)=a := by
  have hab := primary_mul ha hb
  apply primary_eq_of_idealExponentOf_eq (primarySmallPart_primary r hab) ha
  rw [primarySmallPart,idealExponentOf_primaryGenerator,
    idealExponentOf_mul (primary_ne_zero ha) (primary_ne_zero hb)]
  have hs' := idealExponent_support_of_dvd_power (primary_ne_zero ha) hr hs
  have hc := (isCoprime_iff_idealExponent_disjoint (primary_ne_zero hb) hr).mp hcop
  ext p
  change (if p∈(idealExponentOf r).support then
    (idealExponentOf a+idealExponentOf b) p else 0)=idealExponentOf a p
  by_cases hp : p∈(idealExponentOf r).support
  · rw [ite_eq_left hp,Finsupp.add_apply]
    have hbp : idealExponentOf b p=0 := (hc p).resolve_right (Finsupp.mem_support_iff.mp hp)
    rw [hbp,add_zero]
  · rw [ite_eq_right hp]
    exact (Finsupp.notMem_support_iff.mp (fun h => hp (hs' h))).symm

lemma cubicTheta_primaryOutsidePart_mul {r a b : Eisenstein}
    (hr : r≠0) (ha : primary a) (hb : primary b)
    (hs : ∃ k : ℕ, a∣r^k) (hcop : IsCoprime b r) :
    primaryOutsidePart r (a*b)=b := by
  have h := primary_small_outside_mul r (primary_mul ha hb)
  rw [cubicTheta_primarySmallPart_mul hr ha hb hs hcop] at h
  exact mul_left_cancel₀ (primary_ne_zero ha) h

lemma cubicTheta_supported_free_unique {r a b c d : Eisenstein}
    (hr : r≠0) (ha : primary a) (hb : primary b) (hc : primary c) (hd : primary d)
    (has : ∃ k : ℕ, a∣r^k) (hcs : ∃ k : ℕ, c∣r^k)
    (hbr : IsCoprime b r) (hdr : IsCoprime d r) (he : a*b=c*d) :
    a=c ∧ b=d := by
  have h1 := congrArg (primarySmallPart r) he
  have h2 := congrArg (primaryOutsidePart r) he
  rw [cubicTheta_primarySmallPart_mul hr ha hb has hbr,
    cubicTheta_primarySmallPart_mul hr hc hd hcs hdr] at h1
  rw [cubicTheta_primaryOutsidePart_mul hr ha hb has hbr,
    cubicTheta_primaryOutsidePart_mul hr hc hd hcs hdr] at h2
  exact ⟨h1,h2⟩

end CubicFirstMoment

end

end OAI
