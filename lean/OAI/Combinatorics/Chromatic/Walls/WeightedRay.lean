import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.WeightedTorusSeries
import OAI.Combinatorics.Chromatic.Walls.QuantumTorusRaySeries
import OAI.Combinatorics.Chromatic.GradedAlgebra.NoncommExpand

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesDilate
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ)
local instance weightedRayAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

def weightedRay (w : ℕ) (a : M) (f : PowerSeries R) : PowerSeries (Torus v Ω) :=
  dilate w (raySeries v Ω a f)

@[simp] lemma coeff_weightedRay (w : ℕ) (a : M) (f : PowerSeries R) (n : ℕ) :
    coeff n (weightedRay v Ω w a f)=
      if w∣n then Torus.monomial v Ω ((n/w) • a) (coeff (n/w) f) else 0 := by
  rw [weightedRay,coeff_dilate,coeff_raySeries]

lemma weightedRay_one (w : ℕ) (a : M) : weightedRay v Ω w a 1=1 := by
  rw [weightedRay,raySeries_one]
  simpa only [map_one] using dilate_C w (R:=Torus v Ω) 1

lemma weightedRay_mul (w : ℕ) (hw : 0<w) (a : M) (ha : Ω a a=0) (f g : PowerSeries R) :
    weightedRay v Ω w a (f*g)=weightedRay v Ω w a f*weightedRay v Ω w a g := by
  rw [weightedRay,raySeries_mul v Ω a ha,dilate_mul w hw]
  rfl

lemma weightedRay_twist (hΩ : ∀m,Ω m m=0) (w : ℕ) (hw : 0<w) (a m : M) (f : PowerSeries R) :
    weightedRay v Ω w a f*PowerSeries.C (Torus.X v Ω m)=
      PowerSeries.C (Torus.X v Ω m)*weightedRay v Ω w a
        (PowerSeries.rescale (↑(v^(2*Ω a m)):R) f) := by
  have H:=congrArg (dilate w) (raySeries_twist v Ω hΩ a m f)
  simpa only [dilate_mul w hw,dilate_C,weightedRay] using H

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.WeightedTorusSeries
open QuantumTorus PowerSeries
noncomputable section
variable {I : Type*} [Fintype I]
variable (w : I→ℕ) [Fact (∀i,0<w i)]

lemma weight_pos (δ : I→ℕ) (hδ : δ≠0) : 0<weight w δ := by
  obtain ⟨i,hi⟩:=Function.ne_iff.mp hδ
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero hi) (coord_le_weight w δ i)

variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M)
local instance pushRayAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

lemma push_on_ray (δ : I→ℕ) (f : (I→ℕ)→R) (F : PowerSeries R)
    (hon : ∀n:ℕ,f (n • δ)=coeff n F)
    (hoff : ∀d,(∀n:ℕ,n • δ≠d) → f d=0) :
    push w v Ω P f=weightedRay v Ω (weight w δ) (P δ) F := by
  classical
  apply PowerSeries.ext
  intro n
  rw [push,coeff_mk,coeff_weightedRay]
  change (∑d : Slice w n,Torus.monomial v Ω (P d.val) (f d.val))=_
  split_ifs with hd
  · let d : Slice w n:=⟨(n/weight w δ) • δ,by
      rw [map_nsmul]
      exact Nat.div_mul_cancel hd⟩
    rw [Finset.sum_eq_single d]
    · change Torus.monomial v Ω (P ((n/weight w δ) • δ)) (f ((n/weight w δ) • δ))=_
      rw [hon,map_nsmul]
    · intro e he hne
      rw [hoff]
      · simp [Torus.monomial]
      intro m hm
      have hh:=congrArg (weight w) hm
      rw [map_nsmul,e.property] at hh
      have hw : weight w δ≠0 := by
        intro hz
        have hn : n=0 := by simpa only [hz,smul_zero] using hh.symm
        subst n
        have hδ : δ=0 := by
          funext i
          exact Nat.eq_zero_of_le_zero (by simpa only [hz] using coord_le_weight w δ i)
        apply hne
        apply Subtype.ext
        simpa only [d,hδ,smul_zero] using hm.symm
      have hm' : m=n/weight w δ := by
        change m*weight w δ=n at hh
        rw [←hh,Nat.mul_div_left _ (Nat.pos_of_ne_zero hw)]
      apply hne
      exact Subtype.ext (by simpa only [d,hm'] using hm.symm)
    · simp
  · apply Finset.sum_eq_zero
    intro d hd'
    rw [hoff]
    · simp [Torus.monomial]
    intro m hm
    apply hd
    have hh:=congrArg (weight w) hm
    rw [map_nsmul,d.property] at hh
    exact ⟨m,by simpa [nsmul_eq_mul,mul_comm] using hh.symm⟩
end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
