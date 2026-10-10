import OAI.Analysis.BoundedHochschild.CompactFamilyAverages

namespace OAI

/-! Simultaneous right-module averaging for an arbitrary family, by compactness
of its joint orbit and the finite isometry-column construction. -/

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {I : Type*}

def WeakRightAverageFixed (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (F : M → WeakDual ℂ X) : Prop :=
  ∀ (n : ℕ) (m : Fin n → M), (∑ j, m j * star (m j) = 1) → weakRightAverage e m F = F

omit [PartialOrder M] [StarOrderedRing M] in
lemma weakRightAverageFixed_isClosed (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    IsClosed {F : M → WeakDual ℂ X | WeakRightAverageFixed e F} := by
  simp only [WeakRightAverageFixed, Set.ofPred_forall]
  exact isClosed_iInter (fun n => isClosed_iInter (fun m => isClosed_iInter
    (fun _ => isClosed_eq (weakRightAverage_continuous e m) continuous_id)))

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma weakRightAverageFixed_of_module (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : M →L[ℂ] M) (hT : ∀ a b, T (a*b) = T a * b) :
    WeakRightAverageFixed e (weakOperatorImage e T) := by
  have hf := (fixed_right_averages_iff T).mpr (right_module_eq_left_multiplication T hT)
  intro n m hm
  rw [weakRightAverage_image, hf n m hm]

theorem exists_simultaneous_right_module_average [Nontrivial M]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (hno : NoFiniteCentralSummand M)
    (T : I → M →L[ℂ] M) (C : I → ℝ)
    (hT : ∀ i, CompletelyBoundedEstimate (T i) (C i)) :
    ∃ S : I → M →L[ℂ] M,
      (∀ i, ‖S i‖ ≤ C i ∧ ∀ a b, S i (a*b) = S i a * b) ∧
      (fun i => weakOperatorImage e (S i)) ∈ weakFamilyAverageOrbit e T := by
  classical
  let B := weakFamilyAverageOrbit e T
  let A (s : Finset I) := B ∩ {F : I → M → WeakDual ℂ X |
    ∀ i ∈ s, WeakRightAverageFixed e (F i)}
  have hfixclosed (i : I) : IsClosed {F : I → M → WeakDual ℂ X |
      WeakRightAverageFixed e (F i)} := by
    have hc : Continuous (fun F : I → M → WeakDual ℂ X => F i) := continuous_apply i
    exact (weakRightAverageFixed_isClosed e).preimage hc
  have hclosed (s : Finset I) : IsClosed (A s) := by
    apply isClosed_closure.inter
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_iInter (fun _ => hfixclosed i))
  have hne (s : Finset I) : (A s).Nonempty := by
    by_cases hs : s.Nonempty
    · let : Nonempty s := hs.to_subtype
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := s))
      let q : s ≃ Fin (n+1) := Fintype.equivFinOfCardEq hn
      let f : Fin (n+1) → I := fun j => (q.symm j).val
      obtain ⟨U, hU, hUorb⟩ := exists_finite_right_module_average e hno
        (T ∘ f) (C ∘ f) (fun j => hT (f j))
      obtain ⟨F, hF, hEq⟩ := weakFamilyAverageOrbit_restriction_lift e hno T C hT f hUorb
      refine ⟨F, hF, ?_⟩
      intro i hi
      have he := congrFun hEq (q ⟨i, hi⟩)
      have hf : f (q ⟨i, hi⟩) = i := by simp [f]
      change F (f (q ⟨i, hi⟩)) = weakOperatorImage e (U (q ⟨i, hi⟩)) at he
      rw [hf] at he
      rw [he]
      exact weakRightAverageFixed_of_module e _ (hU _).2
    · obtain ⟨F, hF⟩ := weakFamilyAverageOrbit_nonempty e T
      exact ⟨F, hF, fun i hi => (hs ⟨i, hi⟩).elim⟩
  have hcompact (s : Finset I) : IsCompact (A s) :=
    (weakFamilyAverageOrbit_isCompact e hno T C hT).of_isClosed_subset
      (hclosed s) (fun _ h => h.1)
  obtain ⟨F, hF⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed A
    (fun s t => ⟨s ∪ t,
      fun G hG => ⟨hG.1, fun i hi => hG.2 i (Finset.mem_union_left t hi)⟩,
      fun G hG => ⟨hG.1, fun i hi => hG.2 i (Finset.mem_union_right s hi)⟩⟩)
    hne hcompact hclosed
  have hFB : F ∈ B := (Set.mem_iInter.mp hF ∅).1
  have hfix (i : I) : WeakRightAverageFixed e (F i) :=
    (Set.mem_iInter.mp hF {i}).2 i (Finset.mem_singleton_self i)
  have hb (i : I) : F i ∈ weakOperatorBall (C i) :=
    weakRightAverageOrbit_subset_ball e hno (T i) (hT i)
      (weakFamilyAverageOrbit_component e T i hFB)
  choose b hn he using fun i => weak_fixed_right_averages_realize e (hT i).1 (hb i) (hfix i)
  refine ⟨fun i => ContinuousLinearMap.mul ℂ M (b i), fun i => ⟨hn i, ?_⟩, ?_⟩
  · intro a c
    exact (mul_assoc (b i) a c).symm
  · have hEq : (fun i => weakOperatorImage e (ContinuousLinearMap.mul ℂ M (b i))) = F := funext he
    rwa [hEq]

end BoundedHochschild.KadisonRingrose

end

end OAI
