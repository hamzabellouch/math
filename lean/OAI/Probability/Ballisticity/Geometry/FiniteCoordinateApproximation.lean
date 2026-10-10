import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

open Filter UniformSpace
open scoped Uniformity Topology
namespace DirectionalTransience.Entropy

lemma finite_coordinates_of_entourage {I R : Type*} [UniformSpace R]
    {V : Set ((I → R) × (I → R))} (hV : V ∈ 𝓤 (I → R)) :
    ∃ S : Finset I, ∀ x y : I → R, (∀ i ∈ S, x i=y i) → (x,y)∈V := by
  classical
  rw [Pi.uniformity] at hV
  refine Filter.iInf_sets_induct hV ?_ ?_
  · exact ⟨∅,fun _ _ _ => Set.mem_univ _⟩
  · intro i V W hV hW
    obtain ⟨S,hS⟩ := hW
    obtain ⟨U,hU,hUV⟩ := Filter.mem_comap.mp hV
    refine ⟨insert i S,fun x y hxy => ⟨?_,hS x y (fun j hj => hxy j (Finset.mem_insert_of_mem hj))⟩⟩
    apply hUV
    change (x i,y i)∈U
    rw [hxy i (Finset.mem_insert_self _ _)]
    exact refl_mem_uniformity hU

lemma finite_coordinates_of_uniformContinuous {I R : Type*} [UniformSpace R]
    (f : (I → R) → ℝ) (hf : UniformContinuous f) {ε : ℝ} (hε : 0<ε) :
    ∃ S : Finset I, ∀ x y : I → R, (∀ i ∈ S, x i=y i) → |f x-f y|<ε := by
  have h := hf (Metric.dist_mem_uniformity hε)
  obtain ⟨S,hS⟩ := finite_coordinates_of_entourage h
  exact ⟨S,fun x y hxy => by simpa only [Set.mem_preimage,Set.mem_ofPred_eq,Real.dist_eq] using hS x y hxy⟩

noncomputable def finiteFiller {I R : Type*} (r : I → R) (S : Finset I) (x : S → R) : I → R := by
  classical
  exact fun i => if h : i∈S then x ⟨i,h⟩ else r i

lemma finiteFiller_continuous {I R : Type*} [TopologicalSpace R] (r : I → R) (S : Finset I) :
    Continuous (finiteFiller r S) := by
  classical
  apply continuous_pi
  intro i
  by_cases hi : i∈S
  · simpa only [finiteFiller, dite_eq_left hi] using (continuous_apply (⟨i,hi⟩ : S) : Continuous (fun x : S → R => x ⟨i,hi⟩))
  · simp only [finiteFiller, dite_eq_right hi]
    exact continuous_const

lemma finiteFiller_approx {I R : Type*} [UniformSpace R] [CompactSpace R]
    (f : C((I → R),ℝ)) (r : I → R) {ε : ℝ} (hε : 0<ε) :
    ∃ S : Finset I, ∀ x, |f x-f (finiteFiller r S (fun i => x i))|<ε := by
  obtain ⟨S,hS⟩ := finite_coordinates_of_uniformContinuous f (CompactSpace.uniformContinuous_of_continuous f.continuous) hε
  refine ⟨S,fun x => hS x _ ?_⟩
  intro i hi
  simp [finiteFiller,hi]

end DirectionalTransience.Entropy

end

end OAI
