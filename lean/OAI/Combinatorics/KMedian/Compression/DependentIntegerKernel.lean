import Mathlib
import OAI.Combinatorics.KMedian.Compression.GramDependence
import OAI.Combinatorics.KMedian.Compression.GramBounds
import OAI.Combinatorics.KMedian.Compression.IntegerCoefficientBounds

namespace OAI

namespace MetricKMedian.Compression
open Finset Matrix

theorem small_integer_dependence_of_dependent {R Ω : Type} [Fintype R] [Fintype Ω]
    (V : Matrix R Ω ℤ) (L : ℕ) (hV : ∀ r i, |V r i| ≤ (2:ℤ)^L)
    (hdep : ¬ LinearIndependent ℚ (fun i r => (V r i:ℚ))) :
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
    apply hdep
    let e := Equiv.ofBijective a ⟨ha,hs⟩
    have hh := hi.comp e.symm e.symm.injective
    have he : (v ∘ a) ∘ e.symm=v := by
      funext i
      change v (e (e.symm i))=v i
      rw [e.apply_symm_apply]
    rw [he] at hh
    exact hh
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

theorem full_integer_kernel_of_dependent {R Ω : Type} [Fintype R] [Fintype Ω]
    (V : Matrix R Ω ℤ) (L : ℕ) (hV : ∀ r i, |V r i| ≤ (2:ℤ)^L)
    (hdep : ¬ LinearIndependent ℚ (fun i r => (V r i:ℚ))) :
    ∃ z : Ω → ℤ, (∃ i, z i ≠ 0) ∧
      (∀ i, |z i| ≤ (2:ℤ)^(2*Fintype.card R*(Fintype.card R+L))) ∧
      ∀ r, ∑ i, z i*V r i=0 := by
  classical
  obtain ⟨K,inst,a,z,ha,_,hne,hbound,hker⟩ := small_integer_dependence_of_dependent V L hV hdep
  let zz : Ω → ℤ := fun i => ∑ k, if a k=i then z k else 0
  have hzval : ∀ k, zz (a k)=z k := by
    intro k
    simp only [zz,ha.eq_iff]
    simpa only [mem_univ,ite_true] using sum_ite_eq' univ k z
  have hzout : ∀ i, (¬∃ k, a k=i) → zz i=0 := by
    intro i hi
    apply sum_eq_zero
    intro k _
    exact ite_eq_right (fun hk => hi ⟨k,hk⟩)
  refine ⟨zz,?_,?_,?_⟩
  · obtain ⟨k,hk⟩ := hne
    exact ⟨a k,by rwa [hzval]⟩
  · intro i
    by_cases hi : ∃ k, a k=i
    · obtain ⟨k,rfl⟩ := hi
      rw [hzval]
      exact hbound k
    · rw [hzout i hi,abs_zero]
      positivity
  · intro r
    change (∑ i, (∑ k, if a k=i then z k else 0)*V r i)=0
    simp only [sum_mul,ite_mul,zero_mul]
    rw [sum_comm]
    simpa using hker r

end MetricKMedian.Compression

end OAI
