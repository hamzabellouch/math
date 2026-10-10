import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.QuantumTorusSignFactors
import OAI.Combinatorics.Chromatic.GradedAlgebra.WeightedTorusSeries
import OAI.Combinatorics.Chromatic.Shuffle.HNSlope

namespace OAI

section
namespace ElementaryPositivity.EnergyLaurent
noncomputable section
lemma series_eq_zero_of_isEmpty {A : Type*} [IsEmpty A] (e : A → ℤ) (he : Admissible e) :
    series e he=0 := by
  ext j
  simp [series_coeff]
end
end ElementaryPositivity.EnergyLaurent

namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic EnergyLaurent
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0<c i)
  [Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

lemma highSeries_support (θ : ℝ) (d : I → ℕ) (hd : highSeries a κ c η hc θ d≠0) :
    d=0 ∨ 0<slopeValue c η θ d := by
  by_contra H
  let : IsEmpty (HighHNIndex a c η hc θ d) := ⟨fun x=>H (highIndex_sign a c η hc θ d x)⟩
  exact hd (series_eq_zero_of_isEmpty _ _)
lemma lowSeries_support (θ : ℝ) (d : I → ℕ) (hd : lowSeries a κ c η hc θ d≠0) :
    slopeValue c η θ d≤0 := by
  by_contra H
  let : IsEmpty (LowHNIndex a c η hc θ d) := ⟨fun x=>H (lowIndex_sign a c η hc θ d x)⟩
  exact hd (series_eq_zero_of_isEmpty _ _)

lemma literalInput_hnSeries (ε : I → Bool) (ha : ∀i,a i i=elementaryDiagonal ε i) (d : I → ℕ) :
    literalInputCoefficient a κ ε d=hnSeries a κ c η hc d := by
  rw [literalInputCoefficient_eq a κ ε ha,finiteReordering_rows a κ c η hc ε ha]
  exact series_equiv _ _ (decorateOutput a c η hc d)
    (fun x=>decoratedEnergy_rows a κ c η hc x.1.val x.2)

end
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.WeightedTorusSeries
open ElementaryPositivity.RawShuffle ElementaryPositivity.QuantumTorus PowerSeries
noncomputable section
universe u
variable {I : Type u} [Fintype I]
variable (w : I → ℕ) [hw : Fact (∀i,0<w i)]

lemma weight_eq_zero_iff (d : I → ℕ) : weight w d=0 ↔ d=0 := by
  constructor
  · intro H
    funext i
    have h:=coord_le_weight w d i
    rw [H] at h
    exact Nat.eq_zero_of_le_zero h
  · intro H; subst d; exact map_zero _

instance sliceZeroUnique : Unique (Slice w 0) where
  default:=⟨0,map_zero _⟩
  uniq d:=Subtype.ext ((weight_eq_zero_iff w d.val).mp d.property)

variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)
local instance : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid

lemma pushCoeff_zero (f : (I→ℕ) → R) :
    pushCoeff w v Ω P f 0=Torus.monomial v Ω 0 (f 0) := by
  classical
  rw [pushCoeff,Fintype.sum_unique]
  change Torus.monomial v Ω (P 0) (f 0)=_
  rw [map_zero]
lemma push_constant (f : (I→ℕ) → R) (hf : f 0=1) : constantCoeff (push w v Ω P f)=1 := by
  rw [push,constantCoeff_mk,pushCoeff_zero,hf]
  rfl

lemma filter_monomial (p : M → Prop) [DecidablePred p] (m : M) (r : R) :
    (Finsupp.filterAddHom p : Torus v Ω →+ Torus v Ω) (Torus.monomial v Ω m r)=
      if p m then Torus.monomial v Ω m r else 0 := by
  classical
  change (Finsupp.single m r).filter p=_
  ext x
  by_cases H : x=m
  · subst x
    by_cases hp : p m <;> simp [Torus.monomial,hp]
  · by_cases hp : p m <;> simp [Torus.monomial,hp,Finsupp.single_eq_of_ne H]

lemma project_push_fixed (h : M →+ ℝ) (f : (I→ℕ) → R)
    (hf : ∀d,f d≠0 → d=0 ∨ 0<h (P d)) (n : ℕ) :
    positiveProject v Ω h (coeff (n+1) (push w v Ω P f))=coeff (n+1) (push w v Ω P f) := by
  classical
  simp only [push,coeff_mk,pushCoeff,map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  change (Finsupp.filterAddHom (fun m=>0<h m) : Torus v Ω →+ Torus v Ω) _=_
  rw [filter_monomial]
  by_cases H : f d.val=0
  · simp [H,Torus.monomial_zero]
  · have hp : 0<h (P d.val) := (hf d.val H).resolve_left (by
      intro hz
      have hh:=d.property
      rw [hz,map_zero] at hh
      omega)
    simp only [hp,ite_true]

lemma project_push_killed (h : M →+ ℝ) (f : (I→ℕ) → R)
    (hf : ∀d,f d≠0 → h (P d)≤0) (n : ℕ) :
    positiveProject v Ω h (coeff n (push w v Ω P f))=0 := by
  classical
  simp only [push,coeff_mk,pushCoeff,map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  change (Finsupp.filterAddHom (fun m=>0<h m) : Torus v Ω →+ Torus v Ω) _=0
  rw [filter_monomial]
  by_cases H : f d.val=0
  · simp [H,Torus.monomial_zero]
  · simp only [not_lt.mpr (hf d.val H),ite_false]

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
