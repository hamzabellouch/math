import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.QuantumTorus

namespace OAI

section
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ)

 def supportedSubring (C : AddSubmonoid M) : Subring (Torus v Ω) where
  carrier := {f | ∀m,m∉C → f m=0}
  zero_mem' := by intro m hm; rfl
  one_mem' := by
    intro m hm
    change Finsupp.single 0 (1:R) m=0
    exact Finsupp.single_eq_of_ne (fun he=>hm (he ▸ C.zero_mem))
  add_mem' := by intro f g hf hg m hm; change f m+g m=0; rw [hf m hm,hg m hm,add_zero]
  neg_mem' := by intro f hf m hm; change -f m=0; rw [hf m hm,neg_zero]
  mul_mem' := by
    classical
    intro f g hf hg m hm
    change (Torus.multiply v Ω f g) m=0
    simp only [Torus.multiply,Finsupp.sum,Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro x hx
    apply Finset.sum_eq_zero
    intro y hy
    have hxC : x∈C := by
      by_contra hn
      exact (Finsupp.mem_support_iff.mp hx) (hf x hn)
    have hyC : y∈C := by
      by_contra hn
      exact (Finsupp.mem_support_iff.mp hy) (hg y hn)
    apply Finsupp.single_eq_of_ne
    intro he
    apply hm
    exact he ▸ C.add_mem hxC hyC

variable (h : M →+ ℝ)
 def nonpositiveCone : AddSubmonoid M where
  carrier := {m | h m≤0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change h a≤0 at ha
    change h b≤0 at hb
    change h (a+b)≤0
    rw [map_add]
    linarith
 def positiveProject : Torus v Ω →+ Torus v Ω :=
  Finsupp.filterAddHom (fun m=>0<h m)
 def zeroProject : Torus v Ω →+ Torus v Ω :=
  Finsupp.filterAddHom (fun m=>h m=0)

lemma nonpositive_iff (f : Torus v Ω) :
    f∈supportedSubring v Ω (nonpositiveCone h) ↔ positiveProject v Ω h f=0 := by
  classical
  change (∀m,¬h m≤0 → f m=0) ↔ Finsupp.filter (fun m=>0<h m) f=0
  constructor
  · intro hf
    ext m
    simp only [Finsupp.filter_apply,Finsupp.zero_apply]
    split_ifs with hm
    · exact hf m (not_le.mpr hm)
    · rfl
  · intro hf m hm
    have hh:=congrArg (fun f : M →₀ R=>f m) hf
    simpa only [Finsupp.filter_apply,not_le.mp hm,ite_true,Finsupp.zero_apply] using hh

lemma positiveProject_idem (f : Torus v Ω) :
    positiveProject v Ω h (positiveProject v Ω h f)=positiveProject v Ω h f := by
  classical
  ext m
  change (f.filter (fun m=>0<h m) |>.filter (fun m=>0<h m)) m = (f.filter (fun m=>0<h m)) m
  simp only [Finsupp.filter_apply]
  split_ifs <;> rfl
lemma zeroProject_idem (f : Torus v Ω) :
    zeroProject v Ω h (zeroProject v Ω h f)=zeroProject v Ω h f := by
  classical
  ext m
  change (f.filter (fun m=>h m=0) |>.filter (fun m=>h m=0)) m = (f.filter (fun m=>h m=0)) m
  simp only [Finsupp.filter_apply]
  split_ifs <;> rfl
lemma positive_zero_project (f : Torus v Ω) :
    positiveProject v Ω h (zeroProject v Ω h f)=0 := by
  classical
  ext m
  change (f.filter (fun m=>h m=0) |>.filter (fun m=>0<h m)) m = 0
  simp only [Finsupp.filter_apply]
  split_ifs <;> first | rfl | linarith

end
end ElementaryPositivity.QuantumTorus
end
end

end OAI
