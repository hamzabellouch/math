import Mathlib
import OAI.Analysis.Commutator.PartialUnitaryAlgebra
import OAI.Analysis.Commutator.TracialL2Tools

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching.PartialUnitary

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
@[ext] lemma ext {v w : PartialUnitary A} (h : v.val=w.val) : v=w := by
  have hp : v.support=w.support := by rw [←v.star_mul,←w.star_mul,h]
  cases v
  cases w
  cases h
  cases hp
  rfl

instance : PartialOrder (PartialUnitary A) where
  le v w := v.support ≤ w.support ∧ w.val*v.support=v.val
  le_refl v := ⟨le_rfl,v.mul_support⟩
  le_trans v w u hvw hwu := by
    refine ⟨hvw.1.trans hwu.1,?_⟩
    have h := (v.projection.le_iff_mul_eq_right w.projection).mp hvw.1
    calc
      _=u.val*(w.support*v.support) := by rw [h]
      _=v.val := by rw [←mul_assoc,hwu.2,hvw.2]
  le_antisymm v w hvw hwv := by
    apply ext
    have h := le_antisymm hvw.1 hwv.1
    calc
      v.val=w.val*v.support := hvw.2.symm
      _=w.val := by rw [h,w.mul_support]

lemma le_def (v w : PartialUnitary A) : v ≤ w ↔
    v.support ≤ w.support ∧ w.val*v.support=v.val := Iff.rfl

lemma star_mul_of_le {v w : PartialUnitary A} (h : v ≤ w) :
    star v.val*w.val=v.support := by
  calc
    _=star (w.val*v.support)*w.val := by rw [h.2]
    _=v.support*w.support := by
      rw [StarMul.star_mul,v.projection.isSelfAdjoint.star_eq,mul_assoc,w.star_mul]
    _=v.support := (v.projection.le_iff_mul_eq_left w.projection).mp h.1

lemma mul_star_of_le {v w : PartialUnitary A} (h : v ≤ w) :
    w.val*star v.val=v.support := by
  calc
    _=w.val*(v.support*star v.val) := by rw [v.support_mul_star]
    _=v.support := by rw [←mul_assoc,h.2,v.mul_star]

lemma support_mul_of_le {v w : PartialUnitary A} (h : v ≤ w) :
    v.support*w.val=v.val := by
  rw [←v.mul_star,mul_assoc,star_mul_of_le h,v.mul_support]

lemma star_sub_mul_sub {v w : PartialUnitary A} (h : v ≤ w) :
    star (w.val-v.val)*(w.val-v.val)=w.support-v.support := by
  have h' : star w.val*v.val=v.support := by
    simpa only [StarMul.star_mul,star_star,v.projection.isSelfAdjoint.star_eq] using
      congrArg star (star_mul_of_le h)
  rw [star_sub,sub_mul,mul_sub,mul_sub,w.star_mul,v.star_mul,star_mul_of_le h,h']
  noncomm_ring

lemma norm_sub_sq (τ : A →ₚ[ℂ] ℂ) {v w : PartialUnitary A} (h : v ≤ w) :
    TracialL2.norm τ (w.val-v.val)^2=(τ w.support).re-(τ v.support).re := by
  rw [TracialL2.norm_sq,star_sub_mul_sub h,map_sub,Complex.sub_re]

lemma le_add (v w : PartialUnitary A) (h : v.support*w.support=0) : v ≤ v.add w h := by
  refine ⟨le_add_of_nonneg_right w.projection.nonneg,?_⟩
  change (v.val+w.val)*v.support=v.val
  have hz := power_mul_power_zero (orthogonal_support_symm h) 1 0
  simp [power] at hz
  rw [add_mul,v.mul_support,hz,add_zero]

lemma zero_le (v : PartialUnitary A) : PartialUnitary.zero ≤ v := by
  exact ⟨v.projection.nonneg,by simp [PartialUnitary.zero]⟩

end Kadison.FinitePatching.PartialUnitary

end

end
end

end OAI
