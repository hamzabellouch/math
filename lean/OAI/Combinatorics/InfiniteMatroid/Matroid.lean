import OAI.Combinatorics.InfiniteMatroid.Basic

namespace OAI

section

open Set Matroid

namespace InfiniteMatroidCounterexample

def IntervalAlternative {α : Type*} (Bases : Set (Set α)) : Prop :=
  ∀ I Y, I ⊆ Y → (Y \ I).Infinite →
    ∃ B ∈ Bases, B ⊆ I ∨ (I ⊆ B ∧ B ⊆ Y) ∨ Y ⊆ B

/-- The purely set-theoretic assumptions supplied by the prototype assembly. -/
structure BasisSystem (α : Type*) where
  bases : Set (Set α)
  nonempty : bases.Nonempty
  antichain : ∀ ⦃B C⦄, B ∈ bases → C ∈ bases → B ⊆ C → B = C
  compl_closed : ∀ ⦃B⦄, B ∈ bases → Bᶜ ∈ bases
  swap : ∀ ⦃B⦄, B ∈ bases → ∀ e ∈ B, ∀ f ∉ B, insert f (B \ {e}) ∈ bases
  intervals : IntervalAlternative bases

namespace BasisSystem

variable {α : Type*} (S : BasisSystem α)

def Independent (I : Set α) : Prop := ∃ B ∈ S.bases, I ⊆ B

lemma independent_mono {I J : Set α} (hJ : S.Independent J) (hIJ : I ⊆ J) :
    S.Independent I := by
  obtain ⟨B, hB, hJB⟩ := hJ
  exact ⟨B, hB, hIJ.trans hJB⟩

lemma maximal_of_base {B : Set α} (hB : B ∈ S.bases) {Y : Set α} (hBY : B ⊆ Y) :
    Maximal (fun K ↦ S.Independent K ∧ K ⊆ Y) B := by
  refine ⟨⟨⟨B, hB, Subset.rfl⟩, hBY⟩, ?_⟩
  intro C hC hBC
  obtain ⟨B', hB', hCB'⟩ := hC.1
  have heq := S.antichain hB hB' (hBC.trans hCB')
  exact heq ▸ hCB'

lemma exists_maximal_finite_gap {I Y : Set α} (hI : S.Independent I) (hIY : I ⊆ Y)
    (hgap : (Y \ I).Finite) :
    ∃ J, I ⊆ J ∧ Maximal (fun K ↦ S.Independent K ∧ K ⊆ Y) J := by
  let F : Set (Set α) := {J | I ⊆ J ∧ S.Independent J ∧ J ⊆ Y}
  have hF : F.Finite := by
    apply ((hgap.finite_subsets).image (fun H ↦ I ∪ H)).subset
    intro J hJ
    refine ⟨J \ I, (fun x hx ↦ ⟨hJ.2.2 hx.1, hx.2⟩), ?_⟩
    ext x
    simp only [Set.mem_union, Set.mem_sdiff]
    have := @hJ.1 x
    tauto
  obtain ⟨J, hJ, hmax⟩ := hF.exists_maximal ⟨I, Subset.rfl, hI, hIY⟩
  refine ⟨J, hJ.1, ⟨hJ.2, ?_⟩⟩
  intro K hK hJK
  exact hmax ⟨hJ.1.trans hJK, hK⟩ hJK

lemma exists_maximal {I Y : Set α} (hI : S.Independent I) (hIY : I ⊆ Y) :
    ∃ J, I ⊆ J ∧ Maximal (fun K ↦ S.Independent K ∧ K ⊆ Y) J := by
  by_cases hgap : (Y \ I).Finite
  · exact S.exists_maximal_finite_gap hI hIY hgap
  obtain ⟨B, hB, hBI | ⟨hIB, hBY⟩ | hYB⟩ := S.intervals I Y hIY hgap
  · obtain ⟨B', hB', hIB'⟩ := hI
    have heq := S.antichain hB hB' (hBI.trans hIB')
    have hIB : I ⊆ B := heq ▸ hIB'
    exact ⟨B, hIB, S.maximal_of_base hB (hBI.trans hIY)⟩
  · exact ⟨B, hIB, S.maximal_of_base hB hBY⟩
  · refine ⟨Y, hIY, ⟨⟨⟨B, hB, hYB⟩, Subset.rfl⟩, ?_⟩⟩
    exact fun _ h _ ↦ h.2

lemma exchange : Matroid.ExchangeProperty (· ∈ S.bases) := by
  intro B C hB hC e he
  have hn : ¬ C ⊆ B := by
    intro hCB
    have heq := S.antichain hC hB hCB
    exact he.2 (heq ▸ he.1)
  obtain ⟨f, hfC, hfB⟩ := Set.not_subset.mp hn
  exact ⟨f, ⟨hfC, hfB⟩, S.swap hB e he.1 f hfB⟩

noncomputable def matroid : Matroid α :=
  Matroid.ofBase univ (· ∈ S.bases) S.nonempty S.exchange
    (fun _ _ _ hI hIY ↦ S.exists_maximal hI hIY)
    (fun _ _ ↦ subset_univ _)

@[simp] lemma ground : S.matroid.E = univ := rfl
@[simp] lemma isBase_iff (B : Set α) : S.matroid.IsBase B ↔ B ∈ S.bases := Iff.rfl
@[simp] lemma indep_iff (I : Set α) : S.matroid.Indep I ↔ S.Independent I := Iff.rfl

lemma self_dual : S.matroid.dual = S.matroid := by
  apply Matroid.ext_isBase Matroid.dual_ground
  intro B _
  rw [Matroid.dual_isBase_iff, ground, ← Set.compl_eq_univ_sdiff, isBase_iff, isBase_iff]
  exact ⟨fun h ↦ by simpa using S.compl_closed h, fun h ↦ S.compl_closed h⟩

lemma insert_indep_of_not_base {I : Set α} (hI : S.matroid.Indep I)
    (hnot : ¬ S.matroid.IsBase I) (e : α) : S.matroid.Indep (insert e I) := by
  obtain ⟨B, hB, hIB⟩ := hI
  by_cases heB : e ∈ B
  · exact ⟨B, hB, Set.insert_subset heB hIB⟩
  have hn : ¬ B ⊆ I := by
    intro hBI
    exact hnot ((Subset.antisymm hIB hBI) ▸ hB)
  obtain ⟨f, hfB, hfI⟩ := Set.not_subset.mp hn
  refine ⟨insert e (B \ {f}), S.swap hB f hfB e heB, ?_⟩
  intro x hx
  rcases hx with rfl | hx
  · exact Set.mem_insert _ _
  · right
    exact ⟨hIB hx, fun hxf ↦ hfI (Set.mem_singleton_iff.mp hxf ▸ hx)⟩

end BasisSystem
end InfiniteMatroidCounterexample
end

end OAI
