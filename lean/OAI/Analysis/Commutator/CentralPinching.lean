import Mathlib
import OAI.Analysis.Commutator.UnitaryOrbitHull

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.CentralAverage

open UnitaryOrbit

section Algebra

variable {A : Type*} [Ring A] [StarRing A]

def reflection (p : A) (hp : IsStarProjection p) : unitary A :=
  ⟨p+p-1,by
    have hs : star (p+p-1)=p+p-1 := by simp only [star_sub,star_add,star_one,hp.isSelfAdjoint.star_eq]
    have hsq : (p+p-1)*(p+p-1)=1 := by noncomm_ring [hp.isIdempotentElem.eq]
    exact ⟨by rw [hs,hsq],by rw [hs,hsq]⟩⟩

lemma reflection_star (p : A) (hp : IsStarProjection p) :
    star (reflection p hp:A)=p+p-1 := by
  simp only [reflection,star_sub,star_add,star_one,hp.isSelfAdjoint.star_eq]

lemma pinch_commutes (p T : A) (hp : IsStarProjection p) :
    (T+(p+p-1)*T*(p+p-1))*p=p*(T+(p+p-1)*T*(p+p-1)) := by
  have hpp (x : A) : p*(p*x)=p*x := by rw [←mul_assoc,hp.isIdempotentElem.eq]
  noncomm_ring [hp.isIdempotentElem.eq,hpp]

end Algebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

def CentralProjection := {p : H →L[ℂ] H // p∈M ∧ IsStarProjection p ∧
  p∈Set.centralizer (M : Set (H →L[ℂ] H))}

def projectionElement (p : CentralProjection M) : M := ⟨p.val,p.property.1⟩

lemma projectionElement_projection (p : CentralProjection M) : IsStarProjection (projectionElement M p) := by
  constructor
  · apply Subtype.ext
    exact p.property.2.1.isIdempotentElem.eq
  · apply Subtype.ext
    exact p.property.2.1.isSelfAdjoint.star_eq

def pinch (p : CentralProjection M) (T : H →L[ℂ] H) : H →L[ℂ] H :=
  (1/2:ℝ) • T+(1/2:ℝ) • conjugate M
    (reflection (projectionElement M p) (projectionElement_projection M p)) T

lemma pinch_mem {Y T : H →L[ℂ] H} (p : CentralProjection M) (hT : T∈hull M Y) :
    pinch M p T∈hull M Y :=
  midpoint_mem M hT (conjugate_mem_hull M _ hT)

lemma pinch_formula (p : CentralProjection M) (T : H →L[ℂ] H) :
    pinch M p T=(1/2:ℝ) • (T+(p.val+p.val-1)*T*(p.val+p.val-1)) := by
  change (1/2:ℝ) • T+(1/2:ℝ) • ((p.val+p.val-1)*T*star (p.val+p.val-1))=_
  simp only [star_sub,star_add,star_one,p.property.2.1.isSelfAdjoint.star_eq,smul_add]

lemma pinch_commutes_projection (p : CentralProjection M) (T : H →L[ℂ] H) :
    pinch M p T*p.val=p.val*pinch M p T := by
  rw [pinch_formula,smul_mul_assoc,mul_smul_comm,pinch_commutes _ _ p.property.2.1]

lemma pinch_preserves (p q : CentralProjection M) {T : H →L[ℂ] H}
    (hT : T*q.val=q.val*T) : pinch M p T*q.val=q.val*pinch M p T := by
  have hpq : Commute p.val q.val := (p.property.2.2 _ q.property.1).symm
  have hU : Commute (p.val+p.val-1) q.val := (hpq.add_left hpq).sub_left (Commute.one_left _)
  have hr := (show Commute T q.val from hT).add_left
    ((hU.mul_left hT).mul_left hU)
  rw [pinch_formula,smul_mul_assoc,mul_smul_comm,hr.eq]

theorem exists_finite_average (Y : H →L[ℂ] H) (s : Finset (CentralProjection M)) :
    ∃ T : H →L[ℂ] H,T∈hull M Y ∧ ∀ p∈s,T*p.val=p.val*T := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Y,hull_self M Y,by simp⟩
  | @insert p s hp ih =>
    obtain ⟨T,hT,hc⟩ := ih
    refine ⟨pinch M p T,pinch_mem M p hT,?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with hqp|hq
    · subst q
      exact pinch_commutes_projection M p T
    · exact pinch_preserves M p q (hc q hq)

end Kadison.CentralAverage

end

end
end

end OAI
