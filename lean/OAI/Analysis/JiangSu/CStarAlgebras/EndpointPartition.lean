import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks

namespace OAI

section

noncomputable section
namespace EndpointPartition
open Set Function

variable {X E ι : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup E] [Fintype ι]

theorem exists_partition (a b : X) (f : ι → C(X,E)) {δ : ℝ} (hδ : 0<δ) :
    ∃ T : Finset X, ∃ ρ g : T → C(X,ℝ),
      (∀ t x,0≤ρ t x ∧ ρ t x≤1) ∧ (∀ x,∑ t,ρ t x=1) ∧
      (∀ t x,0≤g t x ∧ g t x≤1) ∧
      (∀ t,t.val≠a → g t a=0) ∧ (∀ t,t.val≠b → g t b=0) ∧
      (∀ t x,ρ t x≠0 → g t x=1) ∧
      (∀ t x,ρ t x≠0 → ∀ l,‖f l x-f l t.val‖<δ) := by
  classical
  let K : X → Set X := fun t => (if t=a then ∅ else {a}) ∪ (if t=b then ∅ else {b})
  have hK (t : X) : IsClosed (K t) := by
    dsimp [K]
    split_ifs <;> simp
  have htK (t : X) : t∉K t := by
    dsimp [K]
    split_ifs <;> simp_all
  have haK (t : X) (h : t≠a) : a∈K t := by simp [K,h]
  have hbK (t : X) (h : t≠b) : b∈K t := by simp [K,h]
  let V : X → Set X := fun t => {x | ∀ l,‖f l x-f l t‖<δ} ∩ (K t)ᶜ
  have hV (t : X) : IsOpen (V t) := by
    apply IsOpen.inter _ (hK t).isOpen_compl
    rw [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro l
    exact isOpen_lt (by fun_prop) continuous_const
  have htV (t : X) : t∈V t := ⟨by intro l; simpa using hδ,htK t⟩
  obtain ⟨T,hT⟩ := isCompact_univ.elim_finite_subcover V hV
    (show univ⊆⋃ t,V t from fun x _ => Set.mem_iUnion.mpr ⟨x,htV x⟩)
  have hc : univ⊆⋃ t : T,V t.val := by
    intro x hx
    obtain ⟨t,ht,hxt⟩ := Set.mem_iUnion₂.mp (hT hx)
    exact Set.mem_iUnion.mpr ⟨⟨t,ht⟩,hxt⟩
  obtain ⟨ρ,hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun t:T => V t.val) (fun t => hV t.val) hc
  have hg (t : T) : ∃ g : C(X,ℝ), EqOn g 0 (K t.val) ∧
      EqOn g 1 (tsupport (ρ t)) ∧ ∀ x,g x∈Icc (0:ℝ) 1 := by
    apply exists_continuous_zero_one_of_isClosed (hK t.val) (isClosed_tsupport (ρ t))
    apply Set.disjoint_left.mpr
    intro x hxK hxS
    exact (hρ t hxS).2 hxK
  choose g hg0 hg1 hgb using hg
  refine ⟨T,ρ,g,fun t x => ⟨ρ.nonneg t x,ρ.le_one t x⟩,?_,
    fun t x => hgb t x,?_,?_,?_,?_⟩
  · intro x
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x)
  · intro t ht
    exact hg0 t (haK t.val ht)
  · intro t ht
    exact hg0 t (hbK t.val ht)
  · intro t x hx
    exact hg1 t (subset_closure hx)
  · intro t x hx
    exact (hρ t (subset_closure hx)).1

end EndpointPartition

end
end

end OAI
