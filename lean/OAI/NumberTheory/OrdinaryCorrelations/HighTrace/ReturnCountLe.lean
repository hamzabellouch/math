import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GlobalRecord

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical
namespace GlobalRecord
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀}
variable {h ℓ L n N : ℕ} {hh : 0 < h}

lemma return_count_le (w : ClosedLine h ℓ) : (returnSteps w).card ≤ ℓ := by
  exact (card_le_card (subset_univ _)).trans_eq (by simp)

lemma subtype_sum_as_ite {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P]
    [Fintype {x // P x}] (f : α → ℝ) :
    (∑ x : {x // P x}, f x.val) = ∑ x : α, if P x then f x else 0 := by
  have he := Finset.sum_subtype (F:=inferInstance) (p:=P) (univ.filter P) (by simp) f
  simpa only [sum_filter] using he.symm

lemma fiber_sum_as_ite (r : ℕ) (t : Topology ℓ r) (f : GlobalRecord D L h ℓ hh n N → ℝ) :
    (∑ x : Fiber (D:=D) (L:=L) (h:=h) (hh:=hh) (n:=n) (N:=N) r t, f x.val) =
      ∑ x : GlobalRecord D L h ℓ hh n N,
        if ∃ hr : (returnSteps x.line).card=r, encodeTopology x.line r hr=t then f x else 0 := by
  exact subtype_sum_as_ite _ _

lemma sum_topology_indicator (x : GlobalRecord D L h ℓ hh n N) (r : ℕ) (z : ℝ) :
    (∑ t : Topology ℓ r,
      if ∃ hr : (returnSteps x.line).card=r, encodeTopology x.line r hr=t then z else 0) =
      if (returnSteps x.line).card=r then z else 0 := by
  by_cases hr : (returnSteps x.line).card=r
  · have he (t : Topology ℓ r) : (∃ hr : (returnSteps x.line).card=r,
        encodeTopology x.line r hr=t) ↔ encodeTopology x.line r hr=t := by
      exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨hr,h⟩⟩
    simp only [hr,ite_true]
    simp
  · simp only [hr,IsEmpty.exists_iff,ite_false,sum_const_zero]

lemma sum_return_indicator (x : GlobalRecord D L h ℓ hh n N) (z : ℝ) :
    (∑ r : Fin (ℓ+1), if (returnSteps x.line).card=r.val then z else 0) = z := by
  let r₀ : Fin (ℓ+1) := ⟨(returnSteps x.line).card,by have := return_count_le x.line; omega⟩
  have he (r : Fin (ℓ+1)) : (returnSteps x.line).card=r.val ↔ r₀=r := by
    exact ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  simp only [he]
  simp

theorem majorantSum_partition (T err : ℝ) :
    majorantSum (D:=D) (L:=L) (h:=h) (ℓ:=ℓ) (hh:=hh) (n:=n) (N:=N) T err =
      ∑ r : Fin (ℓ+1), ∑ t : Topology ℓ r.val,
        ∑ x : Fiber (D:=D) (L:=L) (h:=h) (hh:=hh) (n:=n) (N:=N) r.val t,
          traceIntegrationMajorant x.val.line hh x.val.primitives x.val.record T err := by
  symm
  let f := fun x : GlobalRecord D L h ℓ hh n N =>
    traceIntegrationMajorant x.line hh x.primitives x.record T err
  change (∑ r : Fin (ℓ+1), ∑ t : Topology ℓ r.val,
    ∑ x : Fiber (D:=D) (L:=L) (h:=h) (hh:=hh) (n:=n) (N:=N) r.val t, f x.val) = ∑ x, f x
  simp_rw [fiber_sum_as_ite]
  conv_lhs =>
    arg 2
    ext r
    rw [sum_comm]
  rw [sum_comm]
  simp_rw [sum_topology_indicator,sum_return_indicator]

end GlobalRecord
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
