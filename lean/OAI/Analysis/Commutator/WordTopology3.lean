import Mathlib
import OAI.Analysis.Commutator.WordTopology
import OAI.Analysis.Commutator.WordTopology2

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

namespace Kadison.PreHilbert

def stageWordArgs (E F : PreHilbert) (S : ℕ → Set E) (R : ℕ → Set F)
    (j n : ℕ) : Set (E × (Fin j → F)) := S n ×ˢ Set.pi Set.univ (fun _ => R n)

lemma stageWordArgs_mono (E F : PreHilbert) (S : ℕ → Set E) (R : ℕ → Set F)
    (hS : Monotone S) (hR : Monotone R) (j : ℕ) :
    Monotone (stageWordArgs E F S R j) := by
  intro n m hnm x hx
  exact ⟨hS hnm hx.1, fun i hi => hR hnm (hx.2 i hi)⟩

lemma dense_stageWordArgs (E F : PreHilbert) (S : ℕ → Set E) (R : ℕ → Set F)
    (hS : Monotone S) (hR : Monotone R) (hSd : Dense (⋃ n, S n))
    (hRd : Dense (⋃ n, R n)) (j : ℕ) : Dense (⋃ n, stageWordArgs E F S R j n) := by
  exact Topology.dense_iUnion_prod S (fun n => Set.pi Set.univ (fun _ : Fin j => R n)) hS
    (fun n m hnm x hx i hi => hR hnm (hx i hi)) hSd
    (Topology.dense_iUnion_pi (fun n (_ : Fin j) => R n) (fun _ => hR) (fun _ => hRd))

lemma continuous_wordCoefficient (E F : PreHilbert) (k l : ℕ)
    (T : wordSpace E F k →L[ℂ] wordSpace E F l) :
    Continuous (fun z : (E × (Fin k → F)) × (E × (Fin l → F)) =>
      inner ℂ (word E F l z.2.1 z.2.2) (T (word E F k z.1.1 z.1.2))) := by
  exact (((continuous_word E F l).comp continuous_snd).inner
    (T.continuous.comp ((continuous_word E F k).comp continuous_fst)))

theorem operator_ext_dense_stages (E F : PreHilbert) (k l : ℕ)
    (S : ℕ → Set E) (R : ℕ → Set F) (hS : Monotone S) (hR : Monotone R)
    (hSd : Dense (⋃ n, S n)) (hRd : Dense (⋃ n, R n))
    (T U : wordSpace E F k →L[ℂ] wordSpace E F l)
    (h : ∀ n d, d ∈ S n → ∀ x, (∀ i, x i ∈ R n) → ∀ c, c ∈ S n →
      ∀ y, (∀ j, y j ∈ R n) →
      inner ℂ (word E F l c y) (T (word E F k d x)) =
        inner ℂ (word E F l c y) (U (word E F k d x))) : T = U := by
  let W := stageWordArgs E F S R
  have hd : Dense (⋃ n, W k n ×ˢ W l n) :=
    Topology.dense_iUnion_prod (W k) (W l)
      (stageWordArgs_mono E F S R hS hR k) (stageWordArgs_mono E F S R hS hR l)
      (dense_stageWordArgs E F S R hS hR hSd hRd k)
      (dense_stageWordArgs E F S R hS hR hSd hRd l)
  apply continuousLinearMap_ext_word_inner E F k l T U
  intro d x c y
  refine hd.induction (P := fun z =>
    inner ℂ (word E F l z.2.1 z.2.2) (T (word E F k z.1.1 z.1.2)) =
      inner ℂ (word E F l z.2.1 z.2.2) (U (word E F k z.1.1 z.1.2))) ?_ ?_ ((d, x), (c, y))
  · intro z hz
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
    exact h n z.1.1 hn.1.1 z.1.2 (fun i => hn.1.2 i (Set.mem_univ i))
      z.2.1 hn.2.1 z.2.2 (fun j => hn.2.2 j (Set.mem_univ j))
  · exact isClosed_eq (continuous_wordCoefficient E F k l T)
      (continuous_wordCoefficient E F k l U)

end Kadison.PreHilbert
end

end OAI
