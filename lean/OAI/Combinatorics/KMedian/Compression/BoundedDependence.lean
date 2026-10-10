import Mathlib
import OAI.Combinatorics.KMedian.Compression.GramDependence
import OAI.Combinatorics.KMedian.Compression.GramBounds
import OAI.Combinatorics.KMedian.Compression.IntegerCoefficientBounds

namespace OAI

namespace MetricKMedian.Compression
open Finset Matrix

theorem small_integer_dependence {R Ω : Type} [Fintype R] [Fintype Ω]
    (V : Matrix R Ω ℤ) (L : ℕ) (hV : ∀ r i, |V r i| ≤ (2:ℤ)^L)
    (hsize : Fintype.card R < Fintype.card Ω) :
    ∃ (K : Type) (inst : Fintype K), letI := inst;
      ∃ (a : K → Ω) (z : K → ℤ), Function.Injective a ∧
        Fintype.card K ≤ Fintype.card R+1 ∧ (∃ k, z k ≠ 0) ∧
        (∀ k, |z k| ≤ (2:ℤ)^(2*Fintype.card R*(Fintype.card R+L))) ∧
        ∀ r, ∑ k, z k*V r (a k)=0 := by
  classical
  let v : Ω → R → ℚ := fun i r => V r i
  obtain ⟨κ,a,ha,hspan,hi⟩ := exists_linearIndependent' ℚ v
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ ≤ Fintype.card R := by
    simpa using hi.fintype_card_le_finrank
  have hns : ¬ Function.Surjective a := by
    intro hs
    have hh := Fintype.card_le_of_surjective a hs
    omega
  simp only [Function.Surjective,not_forall,not_exists] at hns
  obtain ⟨w,hw⟩ := hns
  let A : Matrix R κ ℤ := fun r c => V r (a c)
  let wv : R → ℤ := fun r => V r w
  let B := A.transpose*A
  let D := B.det
  let b := B.cramer (A.transpose*ᵥwv)
  have hAi : LinearIndependent ℚ (fun c r => (A r c:ℚ)) := hi
  have hwm : (fun r => (wv r:ℚ)) ∈ Submodule.span ℚ (Set.range (fun c r => (A r c:ℚ))) := by
    change v w ∈ Submodule.span ℚ (Set.range (v ∘ a))
    rw [hspan]
    exact Submodule.subset_span (Set.mem_range_self w)
  have hD : D ≠ 0 := gram_det_ne_zero A hAi
  have heq : ∀ r, (A*ᵥb) r=D*wv r := gram_span_relation A wv hAi hwm
  have hbnd := gram_coefficient_bit_bound (Fintype.card R) (Fintype.card κ) L hcard
  have hAb : ∀ r c, |A r c| ≤ (2:ℤ)^L := fun r c => hV r (a c)
  have hwv : ∀ r, |wv r| ≤ (2:ℤ)^L := fun r => hV r w
  have hDb : |D| ≤ (2:ℤ)^(2*Fintype.card R*(Fintype.card R+L)) :=
    (gram_det_bound A _ (by positivity) hAb).trans hbnd
  have hbb : ∀ c, |b c| ≤ (2:ℤ)^(2*Fintype.card R*(Fintype.card R+L)) :=
    fun c => (gram_cramer_bound A wv _ (by positivity) hAb hwv c).trans hbnd
  let a' : Option κ → Ω := fun k => k.elim w a
  let z : Option κ → ℤ := fun k => k.elim D (fun c => -b c)
  refine ⟨Option κ,inferInstance,a',z,?_,?_,⟨none,hD⟩,?_,?_⟩
  · intro c d he
    cases c with
    | none =>
      cases d with
      | none => rfl
      | some d => exact False.elim (hw d he.symm)
    | some c =>
      cases d with
      | none => exact False.elim (hw c he)
      | some d => exact congrArg some (ha he)
  · simp only [Fintype.card_option]
    omega
  · intro k
    cases k with
    | none => exact hDb
    | some c => simpa only [z,Option.elim_some,abs_neg] using hbb c
  · intro r
    rw [Fintype.sum_option]
    change D*wv r+(∑ c, (-b c)*A r c)=0
    have hh := heq r
    change (∑ c, A r c*b c)=D*wv r at hh
    simp only [neg_mul,sum_neg_distrib,mul_comm (b _) (A _ _)]
    rw [hh]
    ring

end MetricKMedian.Compression

end OAI
