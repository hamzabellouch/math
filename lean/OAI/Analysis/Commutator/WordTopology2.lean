import Mathlib

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.Topology

open Set

lemma exists_stage_pi {ι : Type*} [Fintype ι] {E : ι → Type*}
    (S : ℕ → (i : ι) → Set (E i)) (hmono : ∀ i, Monotone (fun n => S n i))
    (v : ∀ i, E i) (hv : ∀ i, v i ∈ ⋃ n, S n i) :
    ∃ n, ∀ i, v i ∈ S n i := by
  classical
  have hv' (i) : ∃ n, v i ∈ S n i := Set.mem_iUnion.mp (hv i)
  choose a ha using hv'
  refine ⟨Finset.univ.sup a, fun i => ?_⟩
  exact hmono i (Finset.le_sup (Finset.mem_univ i)) (ha i)

lemma dense_iUnion_pi {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, TopologicalSpace (E i)]
    (S : ℕ → (i : ι) → Set (E i)) (hmono : ∀ i, Monotone (fun n => S n i))
    (hd : ∀ i, Dense (⋃ n, S n i)) : Dense (⋃ n, Set.pi Set.univ (S n)) := by
  apply (dense_pi Set.univ (fun i _ => hd i)).mono
  intro v hv
  obtain ⟨n, hn⟩ := exists_stage_pi S hmono v (fun i => hv i (Set.mem_univ i))
  exact Set.mem_iUnion.mpr ⟨n, fun i _ => hn i⟩

lemma dense_iUnion_prod {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (S : ℕ → Set E) (T : ℕ → Set F) (hS : Monotone S) (hT : Monotone T)
    (hSd : Dense (⋃ n, S n)) (hTd : Dense (⋃ n, T n)) :
    Dense (⋃ n, S n ×ˢ T n) := by
  apply (hSd.prod hTd).mono
  intro x hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx.1
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx.2
  exact Set.mem_iUnion.mpr ⟨max n m, hS (le_max_left n m) hn, hT (le_max_right n m) hm⟩

end Kadison.Topology
end

end OAI
