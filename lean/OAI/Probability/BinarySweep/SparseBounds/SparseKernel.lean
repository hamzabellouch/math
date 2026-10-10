import Mathlib
import OAI.Probability.BinarySweep.Trajectories.IsolatedCancellation
import OAI.Probability.BinarySweep.Conditional.PlacementAlternation

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
open Sparse

variable {b h : ℕ} {bits : Fin b → ℕ} {I : Type*} [Fintype I] [DecidableEq I]

def centeredEndpointKernel (H : PathFamily bits h) (z : ℝ)
    (e : I → GridSlot bits × GridSlot bits) : ℝ :=
  (gridSize bits:ℝ)⁻¹ ^ Fintype.card I *
    alternatingSubsetSum Finset.univ (gridSize bits) (fun A => endpointProbability H z A e)

lemma centeredEndpointKernel_isolated (H : PathFamily bits h) (z : ℝ)
    (e : I → GridSlot bits × GridSlot bits) (i : I)
    (hh : ∀j k, (fun a : {a : Fin b // a≠j} => H.position j.castSucc k a) ≠ endpointLine (e i) j)
    (ha : ∀j a, a≠i → endpointLine (e a) j≠endpointLine (e i) j) :
    centeredEndpointKernel H z e=0 := by
  unfold centeredEndpointKernel
  rw [alternatingSubsetSum_of_isolated Finset.univ
    (by exact_mod_cast (gridSize_pos bits).ne') _ i (Finset.mem_univ _) ?_,mul_zero]
  intro A hA
  exact endpointProbability_insert_isolated H z A e i hh
    (fun j a haA => ha j a (Finset.mem_erase.mp (hA haA)).1)

def pathEndpoints (H : PathFamily bits h) (k : Fin h) : GridSlot bits × GridSlot bits :=
  (H.position 0 k,H.position (Fin.last b) k)

lemma endpointLine_path (H : PathFamily bits h) (k : Fin h) (j : Fin b) :
    endpointLine (pathEndpoints H k) j=(fun a : {a : Fin b // a≠j} => H.position j.castSucc k a) := by
  unfold endpointLine pathEndpoints
  rw [independentPosition_of_path (fun t => H.position t k) (fun j i hi => H.changes_only_stage j k i hi)]

def shareLine (e f : GridSlot bits × GridSlot bits) : Prop :=
  ∃j, endpointLine e j=endpointLine f j

lemma shareLine_symmetric :
    ∀ ⦃first second : GridSlot bits × GridSlot bits⦄,
      shareLine first second → shareLine second first := by
  rintro e f ⟨j,hj⟩
  exact ⟨j,hj.symm⟩

lemma shareLine_probability (f : GridSlot bits × GridSlot bits) :
    finiteProbability uniformWeight (fun e => shareLine (bits:=bits) e f) ≤
      ∑j : Fin b, (1:ℝ)/Fintype.card (GridOutside bits j) := by
  have he := finiteProbability_union uniformWeight uniformWeight_nonneg
    (fun (j : Fin b) (e : GridSlot bits × GridSlot bits) => endpointLine e j=endpointLine f j)
  have hj (j : Fin b) : finiteProbability uniformWeight
      (fun e : GridSlot bits × GridSlot bits => endpointLine e j=endpointLine f j)=
      (1:ℝ)/Fintype.card (GridOutside bits j) :=
    independent_line_uniform j (endpointLine f j)
  simpa only [hj,shareLine] using he

lemma centeredEndpointKernel_support (H : PathFamily bits h) (z : ℝ)
    (e : I → GridSlot bits × GridSlot bits) (he : centeredEndpointKernel H z e≠0) :
    incidentSet shareLine (pathEndpoints H) e=Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  by_contra hi
  have hn : ¬((∃a, i≠a ∧ shareLine (e i) (e a)) ∨ ∃k, shareLine (e i) (pathEndpoints H k)) := by
    simpa only [incidentSet,Finset.mem_filter,Finset.mem_univ,true_and] using hi
  apply he
  apply centeredEndpointKernel_isolated H z e i
  · intro j k hk
    apply hn
    exact Or.inr ⟨k,j,hk.symm.trans (endpointLine_path H k j).symm⟩
  · intro j a hai hj
    exact hn (Or.inl ⟨a,Ne.symm hai,j,hj.symm⟩)

theorem centeredEndpointKernel_exceptional_probability (H : PathFamily bits h) (z : ℝ)
    (hsmall : ((Fintype.card I+h:ℕ):ℝ) *
      (∑j : Fin b, (1:ℝ)/Fintype.card (GridOutside bits j)) ≤ 1) :
    productProbability (uniformWeight (Ω:=GridSlot bits × GridSlot bits))
      (fun e : I → GridSlot bits × GridSlot bits => centeredEndpointKernel H z e≠0) ≤
      (2:ℝ)^Fintype.card I *
        (((Fintype.card I+h:ℕ):ℝ) * (∑j : Fin b, (1:ℝ)/Fintype.card (GridOutside bits j))) ^
          ((Fintype.card I+1)/2) := by
  have hh := sharing_probability_le (I:=I) uniformWeight uniformWeight_nonneg uniformWeight_sum
      shareLine shareLine_symmetric (pathEndpoints H) _ (by positivity)
      shareLine_probability (Fintype.card I) (by simpa only [Fintype.card_fin] using hsmall)
  simp only [Fintype.card_fin] at hh
  apply (productProbability_mono uniformWeight_nonneg ?_).trans hh
  intro e he
  rw [centeredEndpointKernel_support H z e he,Finset.card_univ]

end BinaryCoordinateSweeps

end

end OAI
