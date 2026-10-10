import OAI.NumberTheory.DukePrimeDegree.Entropy.ReturnCellEntropy

namespace OAI

/-! # A measurable return partition with finite transverse refinements -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree

def returnRefinementAtom {Y : Type*} (T : Y → Y) (S : Set Y)
    {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n)) : Option (Σ n : ℕ, Fin (K n)) → Set Y
  | none => firstReturnPartitionAtom T S 0
  | some z => {x | x ∈ firstReturnLevel T S z.1 ∧ B z.1 x=z.2}

lemma returnRefinement_covers {Y : Type*} (T : Y → Y) (S : Set Y)
    {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n)) (x : Y) :
    ∃ z, x ∈ returnRefinementAtom T S B z := by
  classical
  by_cases h : ∃ n, x ∈ firstReturnLevel T S n
  · obtain ⟨n,hn⟩ := h
    exact ⟨some ⟨n,B n x⟩,hn,rfl⟩
  · exact ⟨none,by simpa only [returnRefinementAtom,firstReturnPartitionAtom,
      mem_compl_iff,mem_iUnion,not_exists] using h⟩

lemma returnRefinementAtom_unique {Y : Type*} (T : Y → Y) (S : Set Y)
    {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n))
    {a b : Option (Σ n : ℕ, Fin (K n))} {x : Y}
    (ha : x ∈ returnRefinementAtom T S B a)
    (hb : x ∈ returnRefinementAtom T S B b) : a=b := by
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some b => exact (ha (mem_iUnion.mpr ⟨b.1,hb.1⟩)).elim
  | some a =>
      cases b with
      | none => exact (hb (mem_iUnion.mpr ⟨a.1,ha.1⟩)).elim
      | some b =>
          rcases a with ⟨n,i⟩
          rcases b with ⟨m,j⟩
          have he := firstReturnLevel_unique T S ha.1 hb.1
          dsimp at he
          subst m
          have hij : i=j := ha.2.symm.trans hb.2
          subst j
          rfl

def returnRefinement {Y : Type*} (T : Y → Y) (S : Set Y)
    {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n)) (x : Y) :
    Option (Σ n : ℕ, Fin (K n)) := (returnRefinement_covers T S B x).choose

lemma returnRefinement_fiber {Y : Type*} (T : Y → Y) (S : Set Y)
    {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n)) (z : Option (Σ n : ℕ, Fin (K n))) :
    {x | returnRefinement T S B x=z}=returnRefinementAtom T S B z := by
  ext x
  constructor
  · intro hx
    have hm : x ∈ returnRefinementAtom T S B (returnRefinement T S B x) :=
      (returnRefinement_covers T S B x).choose_spec
    rwa [hx] at hm
  · intro hx
    exact returnRefinementAtom_unique T S B (returnRefinement_covers T S B x).choose_spec hx

lemma measurable_returnRefinement
    {Y : Type*} [MeasurableSpace Y] {T : Y → Y} (hT : Measurable T)
    {S : Set Y} (hS : MeasurableSet S)
    {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n)) (hB : ∀ n, Measurable (B n)) :
    @Measurable Y (Option (Σ n : ℕ, Fin (K n))) _ ⊤ (returnRefinement T S B) := by
  let : MeasurableSpace (Option (Σ n : ℕ, Fin (K n))) := ⊤
  apply measurable_to_countable'
  intro z
  change MeasurableSet {x | returnRefinement T S B x=z}
  rw [returnRefinement_fiber]
  cases z with
  | none => exact (MeasurableSet.iUnion (fun n => measurableSet_firstReturnLevel hT hS n)).compl
  | some z =>
      exact (measurableSet_firstReturnLevel hT hS z.1).inter
        (hB z.1 (measurableSet_singleton z.2))

theorem returnRefinement_information_summable
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (hE : MeasurableEmbedding T)
    {S : Set Y} (hS : MeasurableSet S)
    (K : ℕ → ℕ) (B : ∀ n, Y → Fin (K n)) (hB : ∀ n, Measurable (B n))
    (C : ℝ) (hcard : ∀ n, Real.log (K n) ≤ C*(n+1)) :
    Summable (fun z : Option (Σ n : ℕ, Fin (K n)) =>
      Real.negMulLog (μ.real {x | returnRefinement T S B x=z})) := by
  let f := fun z : Option (Σ n : ℕ, Fin (K n)) =>
    Real.negMulLog (μ.real {x | returnRefinement T S B x=z})
  have hs : Summable (fun z : Σ n : ℕ, Fin (K n) => f (some z)) := by
    simpa only [f,returnRefinement_fiber,returnRefinementAtom] using
      firstReturn_cells_information_summable μ hT hE hS K B hB C hcard
  let e : Option (Σ n : ℕ, Fin (K n)) ≃ (Σ n : ℕ, Fin (K n)) ⊕ PUnit.{1} :=
    Equiv.optionEquivSumPUnit (Σ n : ℕ, Fin (K n))
  have H : Summable (fun z : (Σ n : ℕ, Fin (K n)) ⊕ PUnit.{1} => f (e.symm z)) := by
    apply Summable.sum
    · simpa only [Function.comp_def,e,Equiv.optionEquivSumPUnit_symm_inl] using hs
    · exact (hasSum_fintype _).summable
  simpa only [Function.comp_def,Equiv.symm_apply_apply,f] using
    H.comp_injective e.injective

end DukePrimeDegree

end

end OAI
