import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure Link (M : VonNeumannAlgebra H) (e f : H →L[ℂ] H) where
  val : H →L[ℂ] H
  mem : val∈M
  triple : val*star val*val=val
  source_le : star val*val≤e
  target_le : val*star val≤f

namespace Link

variable {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}

@[ext] lemma ext {v w : Link M e f} (h : v.val=w.val) : v=w := by
  cases v; cases w; cases h; rfl

def initial (v : Link M e f) : H →L[ℂ] H := star v.val*v.val

def final (v : Link M e f) : H →L[ℂ] H := v.val*star v.val

lemma initial_projection (v : Link M e f) : IsStarProjection v.initial := by
  constructor
  · change (star v.val*v.val)*(star v.val*v.val)=star v.val*v.val
    calc
      _=star v.val*(v.val*star v.val*v.val) := by noncomm_ring
      _=star v.val*v.val := by rw [v.triple]
  · exact IsSelfAdjoint.star_mul_self v.val

lemma final_projection (v : Link M e f) : IsStarProjection v.final := by
  constructor
  · change (v.val*star v.val)*(v.val*star v.val)=v.val*star v.val
    calc
      _=(v.val*star v.val*v.val)*star v.val := by noncomm_ring
      _=v.val*star v.val := by rw [v.triple]
  · exact IsSelfAdjoint.mul_star_self v.val

lemma mul_initial (v : Link M e f) : v.val*v.initial=v.val := by
  rw [initial,←mul_assoc,v.triple]

lemma final_mul (v : Link M e f) : v.final*v.val=v.val := v.triple

lemma norm_le_one (v : Link M e f) : ‖v.val‖≤1 := by
  have h := (v.initial_projection).norm_le v.initial
  change ‖star v.val*v.val‖≤1 at h
  rw [CStarRing.norm_star_mul_self] at h
  nlinarith [norm_nonneg v.val]

lemma mul_source (v : Link M e f) (he : IsStarProjection e) : v.val*e=v.val := by
  have h := (v.initial_projection.le_iff_mul_eq_left he).mp v.source_le
  calc
    _=(v.val*v.initial)*e := by rw [v.mul_initial]
    _=v.val := by rw [mul_assoc,h,v.mul_initial]

lemma target_mul (v : Link M e f) (hf : IsStarProjection f) : f*v.val=v.val := by
  have h := (v.final_projection.le_iff_mul_eq_right hf).mp v.target_le
  calc
    _=f*(v.final*v.val) := by rw [v.final_mul]
    _=v.val := by rw [←mul_assoc,h,v.final_mul]

instance : PartialOrder (Link M e f) where
  le v w := v.initial≤w.initial ∧ w.val*v.initial=v.val
  le_refl v := ⟨le_rfl,v.mul_initial⟩
  le_trans v w u hvw hwu := by
    refine ⟨hvw.1.trans hwu.1,?_⟩
    have h := (v.initial_projection.le_iff_mul_eq_right w.initial_projection).mp hvw.1
    calc
      _=u.val*(w.initial*v.initial) := by rw [h]
      _=v.val := by rw [←mul_assoc,hwu.2,hvw.2]
  le_antisymm v w hvw hwv := by
    apply ext
    have h := le_antisymm hvw.1 hwv.1
    calc
      v.val=w.val*v.initial := hvw.2.symm
      _=w.val := by rw [h,w.mul_initial]

lemma le_def (v w : Link M e f) : v≤w ↔ v.initial≤w.initial ∧ w.val*v.initial=v.val := Iff.rfl

end Link

end Kadison.PartialIsometryOrder

end

end
end

end OAI
