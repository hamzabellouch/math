import Mathlib
import OAI.Analysis.Conductivity.Branching.RecoverJoinChild

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Set Filter Topology

def joinHull (U : Set DiagonalTriple) : Set DiagonalTriple :=
  U ∪ {δ | ∃ i θ α β, 0 ≤ θ ∧ θ ≤ 1 ∧ α ∈ U ∧ β ∈ U ∧
    coordinateJoin i θ α β = δ}

lemma subset_joinHull (U : Set DiagonalTriple) : U ⊆ joinHull U := fun _ => Or.inl

lemma joinHull_mono {U V : Set DiagonalTriple} (h : U ⊆ V) : joinHull U ⊆ joinHull V := by
  rintro δ (hδ | ⟨i, θ, α, β, hθ₀, hθ₁, hα, hβ, rfl⟩)
  · exact Or.inl (h hδ)
  · exact Or.inr ⟨i, θ, α, β, hθ₀, hθ₁, h hα, h hβ, rfl⟩

lemma joinHull_subset_laminate {a b : ℝ} {U : Set DiagonalTriple}
    (hU : ∀ α ∈ U, IsFiniteLaminate a b α) :
    ∀ α ∈ joinHull U, IsFiniteLaminate a b α := by
  rintro δ (hδ | ⟨i, θ, α, β, hθ₀, hθ₁, hα, hβ, rfl⟩)
  · exact hU δ hδ
  · exact .join i θ hθ₀ hθ₁ (hU α hα) (hU β hβ)

lemma isOpen_joinHull {a b : ℝ} (ha : 0 < a) {U : Set DiagonalTriple}
    (hU : IsOpen U) (hsub : ∀ α ∈ U, IsFiniteLaminate a b α) : IsOpen (joinHull U) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro δ (hδ | ⟨i, θ, α, β, hθ₀, hθ₁, hα, hβ, rfl⟩)
  · exact mem_of_superset (hU.mem_nhds hδ) (subset_joinHull U)
  · by_cases hθ : θ = 0
    · rw [hθ, coordinateJoin_zero]
      exact mem_of_superset (hU.mem_nhds hβ) (subset_joinHull U)
    · have hαi : α i ≠ 0 := (ha.trans ((hsub α hα).bounds ha i).1).ne'
      have hδi : coordinateJoin i θ α β i ≠ 0 :=
        (ha.trans (coordinateJoin_bounds ha ((hsub α hα).bounds ha)
          ((hsub β hβ).bounds ha) i ⟨hθ₀, hθ₁⟩ i).1).ne'
      have hc := continuousAt_recoverJoinChild i hθ α β hαi hδi
      have he := recoverJoinChild_join i hθ α β
      have hm : ∀ᶠ δ' in 𝓝 (coordinateJoin i θ α β), recoverJoinChild i θ β δ' ∈ U :=
        hc.preimage_mem_nhds (by rw [he]; exact hU.mem_nhds hα)
      filter_upwards [hm] with δ' hδ'
      exact Or.inr ⟨i, θ, recoverJoinChild i θ β δ', β,
        hθ₀, hθ₁, hδ', hβ, coordinateJoin_recoverJoinChild i hθ β δ'⟩

lemma joinHull_permute {U : Set DiagonalTriple}
    (hU : ∀ α ∈ U, ∀ e : Equiv.Perm (Fin 3), α ∘ e ∈ U) :
    ∀ α ∈ joinHull U, ∀ e : Equiv.Perm (Fin 3), α ∘ e ∈ joinHull U := by
  rintro δ (hδ | ⟨i, θ, α, β, hθ₀, hθ₁, hα, hβ, rfl⟩) e
  · exact Or.inl (hU δ hδ e)
  · refine Or.inr ⟨e.symm i, θ, α ∘ e, β ∘ e, hθ₀, hθ₁, hU α hα e, hU β hβ e, ?_⟩
    ext j
    simp only [Function.comp_apply, coordinateJoin]
    congr 1
    exact propext ⟨fun h => by simpa using congrArg e h,
      fun h => by simpa using congrArg e.symm h⟩

def depthClass (U : Set DiagonalTriple) : ℕ → Set DiagonalTriple
  | 0 => U
  | n+1 => joinHull (depthClass U n)

lemma depthClass_subset_succ (U : Set DiagonalTriple) (n : ℕ) :
    depthClass U n ⊆ depthClass U (n+1) := subset_joinHull _

lemma depthClass_mono (U : Set DiagonalTriple) : Monotone (depthClass U) :=
  monotone_nat_of_le_succ (depthClass_subset_succ U)

lemma depthClass_subset_laminate {a b : ℝ} {U : Set DiagonalTriple}
    (hU : ∀ α ∈ U, IsFiniteLaminate a b α) (n : ℕ) :
    ∀ α ∈ depthClass U n, IsFiniteLaminate a b α := by
  induction n with
  | zero => exact hU
  | succ n ih => exact joinHull_subset_laminate ih

lemma isOpen_depthClass {a b : ℝ} (ha : 0 < a) {U : Set DiagonalTriple}
    (hU : IsOpen U) (hsub : ∀ α ∈ U, IsFiniteLaminate a b α) (n : ℕ) :
    IsOpen (depthClass U n) := by
  induction n with
  | zero => exact hU
  | succ n ih => exact isOpen_joinHull ha ih (depthClass_subset_laminate hsub n)

lemma depthClass_permute {U : Set DiagonalTriple}
    (hU : ∀ α ∈ U, ∀ e : Equiv.Perm (Fin 3), α ∘ e ∈ U) (n : ℕ) :
    ∀ α ∈ depthClass U n, ∀ e : Equiv.Perm (Fin 3), α ∘ e ∈ depthClass U n := by
  induction n with
  | zero => exact hU
  | succ n ih => exact joinHull_permute ih

theorem IsFiniteLaminate.mem_some_depth {a b : ℝ} {U : Set DiagonalTriple}
    (hU : ∀ s, a < s → s < b → (fun _ => s) ∈ U)
    {α : DiagonalTriple} (hα : IsFiniteLaminate a b α) :
    ∃ n, α ∈ depthClass U n := by
  induction hα with
  | scalar s has hsb => exact ⟨0, hU s has hsb⟩
  | @join i θ hθ₀ hθ₁ α β hα hβ ihα ihβ =>
    obtain ⟨n, hn⟩ := ihα
    obtain ⟨m, hm⟩ := ihβ
    exact ⟨max n m + 1, Or.inr ⟨i, θ, α, β, hθ₀, hθ₁,
      depthClass_mono U (le_max_left n m) hn,
      depthClass_mono U (le_max_right n m) hm, rfl⟩⟩

theorem depthClass_plan {a b : ℝ} {U : Set DiagonalTriple}
    (hsub : ∀ α ∈ U, IsFiniteLaminate a b α) {n : ℕ} {δ : DiagonalTriple}
    (hδ : δ ∈ depthClass U (n+1)) (hn : δ ∉ depthClass U n) :
    ∃ i θ α β, 0 < θ ∧ θ < 1 ∧ α ∈ depthClass U n ∧ β ∈ depthClass U n ∧
      coordinateJoin i θ α β = δ ∧
      ∀ t ∈ Icc (0 : ℝ) 1, IsFiniteLaminate a b (coordinateJoin i t α β) := by
  rcases hδ with hδ | ⟨i, θ, α, β, hθ₀, hθ₁, hα, hβ, rfl⟩
  · exact (hn hδ).elim
  have hθne : θ ≠ 0 := by
    intro he
    apply hn
    simpa [he, coordinateJoin_zero] using hβ
  have hθne' : θ ≠ 1 := by
    intro he
    apply hn
    simpa [he, coordinateJoin_one] using hα
  refine ⟨i, θ, α, β, lt_of_le_of_ne hθ₀ (Ne.symm hθne),
    lt_of_le_of_ne hθ₁ hθne', hα, hβ, rfl, ?_⟩
  intro t ht
  exact .join i t ht.1 ht.2
    (depthClass_subset_laminate hsub n α hα) (depthClass_subset_laminate hsub n β hβ)

def scalarNeighbourhood (a b ε : ℝ) : Set DiagonalTriple :=
  {α | IsFiniteLaminate a b α ∧ ∃ s : ℝ, ‖α - (fun _ => s)‖ < ε}

lemma isOpen_scalarNeighbourhood {a b ε : ℝ} (ha : 0 < a) :
    IsOpen (scalarNeighbourhood a b ε) := by
  have he : IsOpen {α : DiagonalTriple | ∃ s : ℝ, ‖α - (fun _ => s)‖ < ε} := by
    simp only [ofPred_exists]
    apply isOpen_iUnion
    intro s
    exact isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
  exact (isOpen_finiteLaminate ha).inter he

lemma scalar_mem_scalarNeighbourhood {a b ε s : ℝ} (hε : 0 < ε)
    (has : a < s) (hsb : s < b) : (fun _ => s) ∈ scalarNeighbourhood a b ε := by
  refine ⟨.scalar s has hsb, s, ?_⟩
  simpa using hε

lemma scalarNeighbourhood_permute {a b ε : ℝ} {α : DiagonalTriple}
    (hα : α ∈ scalarNeighbourhood a b ε) (e : Equiv.Perm (Fin 3)) :
    α ∘ e ∈ scalarNeighbourhood a b ε := by
  rcases hα with ⟨hα, s, hs⟩
  refine ⟨hα.permute e, s, ?_⟩
  have he : ‖(α - (fun _ => s)) ∘ e‖ = ‖α - (fun _ => s)‖ :=
    le_antisymm
      ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
        (fun i => norm_le_pi_norm (α - fun _ => s) (e i)))
      ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun i => by
        simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
          norm_le_pi_norm ((α - fun _ => s) ∘ e) (e.symm i)))
  change ‖(α - (fun _ => s)) ∘ e‖ < ε
  rw [he]
  exact hs

def endpointGraph {P X : Type*} (a b : P) (G U V : Set X) : Set (P × X) :=
  {p | p.2 ∈ G ∧ (p.1 ≠ a ∨ p.2 ∈ U) ∧ (p.1 ≠ b ∨ p.2 ∈ V)}

lemma isOpen_endpointGraph {P X : Type*} [TopologicalSpace P] [T1Space P]
    [TopologicalSpace X] (a b : P) {G U V : Set X}
    (hG : IsOpen G) (hU : IsOpen U) (hV : IsOpen V) :
    IsOpen (endpointGraph a b G U V) := by
  exact (hG.preimage continuous_snd).inter
    (((isOpen_ne.preimage continuous_fst).union
      (hU.preimage continuous_snd)).inter
      ((isOpen_ne.preimage continuous_fst).union
      (hV.preimage continuous_snd)))

lemma path_mem_endpointGraph {P X : Type*} (a b : P) (C : P → X)
    {K : Set P} {G U V : Set X} (hG : ∀ p ∈ K, C p ∈ G)
    (ha : C a ∈ U) (hb : C b ∈ V) :
    ∀ p ∈ K, (p, C p) ∈ endpointGraph a b G U V := by
  intro p hp
  refine ⟨hG p hp, ?_, ?_⟩
  · by_cases h : p = a
    · exact Or.inr (h ▸ ha)
    · exact Or.inl h
  · by_cases h : p = b
    · exact Or.inr (h ▸ hb)
    · exact Or.inl h

end ScalarConductivity

end

end OAI
