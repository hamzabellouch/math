import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.GeometricMutation

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M E : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
variable (e : M →+ E) (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : M)

def realShearVector (x : E) : E := x+S (e p) x • e p
lemma realShearCovector_eval (h : Module.Dual ℝ E) (x : E) :
    realShearCovector e S p h x=h (realShearVector e S p x) := by
  simp only [realShearCovector,realShearVector,LinearMap.add_apply,LinearMap.smul_apply,
    map_add,map_smul,smul_eq_mul]
  ring

lemma mutated_pos_of_nonneg (h : Module.Dual ℝ E) (x : E) (hc : 0≤S (e p) x) :
    0<realMutationCovector e S p h x ↔ 0<h x ∧ 0<h (realShearVector e S p x) := by
  have heq:=realShearCovector_eval e S p h x
  have hw : h (realShearVector e S p x)=h x+h (e p)*S (e p) x := by
    rw [←heq]; rfl
  rw [realMutationCovector]
  split_ifs with hp
  · rw [hw]
    exact ⟨fun hh=>⟨hh,lt_of_lt_of_le hh (le_add_of_nonneg_right (mul_nonneg hp hc))⟩,And.left⟩
  · rw [heq,hw]
    have hm : h (e p)*S (e p) x≤0:=mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge hp)) hc
    exact ⟨fun hh=>⟨by linarith,hh⟩,And.right⟩

lemma mutated_pos_of_nonpos (h : Module.Dual ℝ E) (x : E) (hc : S (e p) x≤0) :
    0<realMutationCovector e S p h x ↔ 0<h x ∨ 0<h (realShearVector e S p x) := by
  have heq:=realShearCovector_eval e S p h x
  have hw : h (realShearVector e S p x)=h x+h (e p)*S (e p) x := by
    rw [←heq]; rfl
  rw [realMutationCovector]
  split_ifs with hp
  · rw [hw]
    have hm : h (e p)*S (e p) x≤0:=mul_nonpos_of_nonneg_of_nonpos hp hc
    constructor
    · exact Or.inl
    · rintro (hh|hh) <;> linarith
  · rw [heq,hw]
    have hm : 0≤h (e p)*S (e p) x:=mul_nonneg_of_nonpos_of_nonpos (le_of_lt (lt_of_not_ge hp)) hc
    constructor
    · exact Or.inr
    · rintro (hh|hh) <;> linarith

lemma real_convex_pos (a b t : ℝ) (ha : 0<a) (hb : 0<b) (ht : 0≤t) (ht1 : t≤1) :
    0<(1-t)*a+t*b := by
  have h0:=mul_nonneg (sub_nonneg.mpr ht1) ha.le
  have h1:=mul_nonneg ht hb.le
  by_cases hz : t=0
  · subst t; simpa using ha
  · have hh:=mul_pos (lt_of_le_of_ne ht (Ne.symm hz)) hb
    linarith

lemma mutation_segment_with_both (a h : Module.Dual ℝ E) (x : E)
    (ha : 0<realMutationCovector e S p a x)
    (hh : 0<h x ∧ 0<h (realShearVector e S p x))
    (t : ℝ) (ht : 0≤t) (ht1 : t≤1) :
    0<realMutationCovector e S p ((1-t) • a+t • h) x := by
  have hp (y : E) (hay : 0<a y) (hhy : 0<h y) :
      0<((1-t) • a+t • h) y := by
    simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
    exact real_convex_pos _ _ _ hay hhy ht ht1
  by_cases hc : 0≤S (e p) x
  · have HA:=(mutated_pos_of_nonneg e S p a x hc).mp ha
    exact (mutated_pos_of_nonneg e S p _ x hc).mpr ⟨hp x HA.1 hh.1,hp _ HA.2 hh.2⟩
  · have hc':=le_of_lt (lt_of_not_ge hc)
    apply (mutated_pos_of_nonpos e S p _ x hc').mpr
    rcases (mutated_pos_of_nonpos e S p a x hc').mp ha with HA|HA
    · exact Or.inl (hp x HA hh.1)
    · exact Or.inr (hp _ HA hh.2)

lemma mutation_segment_same_side (a b : Module.Dual ℝ E) (x : E)
    (ha : 0<realMutationCovector e S p a x) (hb : 0<realMutationCovector e S p b x)
    (hs : (0≤a (e p) ∧ 0≤b (e p)) ∨ (a (e p)≤0 ∧ b (e p)≤0))
    (t : ℝ) (ht : 0≤t) (ht1 : t≤1) :
    0<realMutationCovector e S p ((1-t) • a+t • b) x := by
  have heval (y : E) : ((1-t) • a+t • b) y=(1-t)*a y+t*b y := rfl
  have hpos (h : Module.Dual ℝ E) (hh : 0≤h (e p)) : realMutationCovector e S p h=h := ite_eq_left hh
  have hneg (h : Module.Dual ℝ E) (hh : h (e p)≤0) :
      realMutationCovector e S p h=realShearCovector e S p h := by
    by_cases hz : h (e p)=0
    · rw [realMutationCovector,ite_eq_left (by rw [hz]),realShearCovector,hz,zero_smul,add_zero]
    · exact ite_eq_right (by intro hh'; exact hz (le_antisymm hh hh'))
  rcases hs with hs|hs
  · have hv : 0≤((1-t) • a+t • b) (e p):=by
      rw [heval]
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) hs.1) (mul_nonneg ht hs.2)
    rw [hpos _ hv,heval]
    rw [hpos _ hs.1] at ha
    rw [hpos _ hs.2] at hb
    exact real_convex_pos _ _ _ ha hb ht ht1
  · have hv : ((1-t) • a+t • b) (e p)≤0:=by
      rw [heval]
      exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1) hs.1)
        (mul_nonpos_of_nonneg_of_nonpos ht hs.2)
    rw [hneg _ hv,realShearCovector_eval,heval]
    rw [hneg _ hs.1,realShearCovector_eval] at ha
    rw [hneg _ hs.2,realShearCovector_eval] at hb
    exact real_convex_pos _ _ _ ha hb ht ht1
end
end ElementaryPositivity.QuantumTorus

end

end OAI
