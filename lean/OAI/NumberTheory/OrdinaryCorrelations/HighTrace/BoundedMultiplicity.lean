import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Fiber

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.TypeFibers
open Finset Classical
variable {P T : Type*} [Fintype P] [Fintype T]

abbrev BoundedMultiplicity (P T : Type*) [Fintype P] := T → Fin (Fintype.card P+1)

noncomputable def boundedMultiplicity (f : P → Option T) : BoundedMultiplicity P T :=
  fun t => ⟨multiplicity f t,Nat.lt_succ_of_le (card_le_card (filter_subset _ _))⟩

abbrev FiberCode (P T : Type*) [Fintype P] :=
  (j : BoundedMultiplicity P T) × FactorialAssignments.Unordered (P := P) (fun t => (j t).val)

noncomputable def encode (f : P → Option T) : FiberCode P T :=
  ⟨boundedMultiplicity f,unordered f⟩

omit [Fintype T] in
theorem encode_injective : Function.Injective (encode (P := P) (T := T)) := by
  intro f g he
  have hfib (t : T) : fiber f t=fiber g t :=
    congrArg (fun z : FiberCode P T => (z.2 t).val) he
  funext p
  rcases hf : f p with _ | t <;> rcases hg : g p with _ | u
  · rfl
  · have hgu := (mem_fiber g p u).mpr hg
    rw [← hfib] at hgu
    have hfu := (mem_fiber f p u).mp hgu
    rw [hf] at hfu
    contradiction
  · have hft := (mem_fiber f p t).mpr hf
    rw [hfib] at hft
    have hgt := (mem_fiber g p t).mp hft
    rw [hg] at hgt
    contradiction
  · have hft := (mem_fiber f p t).mpr hf
    rw [hfib] at hft
    have hgt := (mem_fiber g p t).mp hft
    rw [hgt] at hg
    exact hg

theorem encoded_sum_le (W : FiberCode P T → ℝ) (hW : ∀ z, 0 ≤ W z) :
    (∑ f : P → Option T, W (encode f)) ≤ ∑ j : BoundedMultiplicity P T,
      ∑ U : FactorialAssignments.Unordered (P := P) (fun t => (j t).val), W ⟨j,U⟩ := by
  rw [← Fintype.sum_sigma]
  calc
    _ = ∑ z ∈ univ.image encode, W z :=
      (sum_image (fun x _ y _ h => encode_injective h)).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _ => hW x)

end OrdinaryCorrelations.TypeFibers

end

end OAI
