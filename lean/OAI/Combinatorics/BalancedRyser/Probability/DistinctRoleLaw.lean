import OAI.Combinatorics.BalancedRyser.Candidates.Candidates
import OAI.Combinatorics.BalancedRyser.Probability.UniformRestriction

namespace OAI

noncomputable section
open scoped BigOperators ENNReal Classical

namespace Balanced.DistinctRole

theorem uniform_filter_eq_map_subtype {A : Type*} [Fintype A] [Nonempty A]
    (s : Set A) [Fintype s] [Nonempty s]
    (h : ∃ a ∈ s, a ∈ (PMF.uniformOfFintype A).support) :
    (PMF.uniformOfFintype A).filter s h =
      (PMF.uniformOfFintype s).map Subtype.val := by
  classical
  ext a
  rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply]
  by_cases ha : a ∈ s
  · rw [Set.indicator_of_mem ha, PMF.uniformOfFintype_apply, PMF.map_apply]
    have hsum : (∑' b : s, if a = b.val then
        PMF.uniformOfFintype s b else 0) = PMF.uniformOfFintype s ⟨a, ha⟩ := by
      rw [tsum_eq_single ⟨a, ha⟩]
      · simp
      · intro b hb
        have hne : a ≠ b.val := by
          intro heq
          apply hb
          exact Subtype.ext heq.symm
        simp [hne]
    rw [hsum, PMF.uniformOfFintype_apply]
    simp [div_eq_mul_inv, ENNReal.mul_inv, Fintype.card_ne_zero,
      mul_comm, mul_left_comm]
    rw [← mul_assoc, ENNReal.mul_inv_cancel
      (by exact_mod_cast Fintype.card_ne_zero (α := A))
      (ENNReal.natCast_ne_top _), one_mul]
  · rw [Set.indicator_of_notMem ha, zero_mul, PMF.map_apply]
    symm
    apply ENNReal.tsum_eq_zero.mpr
    intro b
    have hne : a ≠ b.val := fun heq => ha (heq.symm ▸ b.property)
    simp [hne]

variable {D F : Type*} [Field F]

def distinctEquiv :
    {M : D → Bool → F // ∀ d, M d false ≠ M d true} ≃
      (D → F) × (D → {x : F // x ≠ 0}) where
  toFun M := (fun d => M.val d true,
    fun d => ⟨M.val d false - M.val d true, sub_ne_zero.mpr (M.property d)⟩)
  invFun x := ⟨fun d b => if b then x.1 d else (x.2 d).val + x.1 d, by
    intro d
    simpa using (x.2 d).property⟩
  left_inv M := by
    apply Subtype.ext
    funext d b
    cases b <;> simp
  right_inv x := by
    rcases x with ⟨y, z⟩
    apply Prod.ext
    · rfl
    · funext d
      apply Subtype.ext
      simp

variable [Fintype D] [Fintype F]

instance distinctNonempty :
    Nonempty {M : D → Bool → F // ∀ d, M d false ≠ M d true} :=
  ⟨⟨fun _ b => if b then 0 else 1, by simp⟩⟩

theorem uniform_distinct_map_role_one :
    (PMF.uniformOfFintype
      {M : D → Bool → F // ∀ d, M d false ≠ M d true}).map
      (fun M d => M.val d true) = PMF.uniformOfFintype (D → F) := by
  classical
  let : Nonempty {x : F // x ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  have h := congrArg (fun p => p.map Prod.fst)
    (TupleAlignment.uniform_map_equiv (distinctEquiv (D := D) (F := F)))
  rw [PMF.map_comp, TupleAlignment.uniform_map_fst] at h
  exact h

theorem distinct_support : ∃ M ∈ {M : MergedPairs F | DistinctConstituents M},
    M ∈ (offsetLaw F).support := by
  refine ⟨fun _ b => if b then 0 else 1, ?_, ?_⟩
  · simp [DistinctConstituents]
  · simp [offsetLaw]

theorem offsetLaw_filter_distinct_map_role_one :
    ((offsetLaw F).filter {M | DistinctConstituents M} distinct_support).map
      (fun M d => M d true) = PMF.uniformOfFintype (Direction F → F) := by
  classical
  let : Nonempty {M : MergedPairs F // DistinctConstituents M} :=
    ⟨⟨fun _ b => if b then 0 else 1, by simp [DistinctConstituents]⟩⟩
  have ho : offsetLaw F = PMF.uniformOfFintype (MergedPairs F) := rfl
  simp only [ho]
  have hf := @uniform_filter_eq_map_subtype (MergedPairs F) inferInstance inferInstance
    {M : MergedPairs F | DistinctConstituents M} inferInstance
    ⟨⟨fun _ b => if b then 0 else 1, by simp [DistinctConstituents]⟩⟩
    (distinct_support (F := F))
  rw [hf, PMF.map_comp]
  let : Nonempty {x : F // x ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  let e : {M : MergedPairs F // DistinctConstituents M} ≃
      (Direction F → F) × (Direction F → {x : F // x ≠ 0}) := distinctEquiv
  have hm := congrArg (fun p => p.map Prod.fst) (TupleAlignment.uniform_map_equiv e)
  rw [PMF.map_comp, TupleAlignment.uniform_map_fst] at hm
  exact hm

theorem offsetLaw_map_role_one :
    (offsetLaw F).map (fun M d => M d true) =
      PMF.uniformOfFintype (Direction F → F) := by
  let e : Direction F ↪ Direction F × Bool :=
    ⟨fun d => (d, true), fun _ _ h => congrArg Prod.fst h⟩
  let c : MergedPairs F ≃ (Direction F × Bool → F) := (Equiv.curry _ _ _).symm
  have hc := TupleAlignment.uniform_map_equiv c
  calc
    _ = ((offsetLaw F).map c).map (fun o d => o (e d)) := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by
      change ((PMF.uniformOfFintype (MergedPairs F)).map c).map _ = _
      rw [hc]
      exact TupleAlignment.uniform_map_restrict e

theorem map_role_one_observable {A : Type*} (f : (Direction F → F) → A) :
    ((offsetLaw F).filter {M | DistinctConstituents M} distinct_support).map
      (fun M => f (fun d => M d true)) =
    (offsetLaw F).map (fun M => f (fun d => M d true)) := by
  have h := congrArg (fun p => p.map f)
    (offsetLaw_filter_distinct_map_role_one (F := F))
  have h' := congrArg (fun p => p.map f) (offsetLaw_map_role_one (F := F))
  rw [PMF.map_comp] at h h'
  exact h.trans h'.symm

end Balanced.DistinctRole

end

end OAI
