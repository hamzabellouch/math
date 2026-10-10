import OAI.GroupTheory.PolycyclicRecognition.Algebra.ParameterizedAdmissibleWords

namespace OAI

/-! # Conjugate schemes remain admissible near zero amplitudes -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {G V I : Type*} [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem mem_generatorWordBase_zero_cons
    (U : Set G) (Exp : V → G) (hExp0 : Exp 0 = 1) (X : I → V)
    (i : I) (w : List (I × ℝ)) (g : G) :
    g ∈ generatorWordBase U Exp X ((i, 0) :: w) ↔ g ∈ generatorWordBase U Exp X w := by
  constructor
  · intro h
    simpa [hExp0] using h.2
  · intro h
    constructor
    · intro r _hr
      simpa [hExp0] using generatorWordBase_subset U Exp hExp0 X w h
    · simpa [hExp0] using h

theorem mem_generatorWordBase_conjugate_zero
    (U : Set G) (Exp : V → G) (hExp0 : Exp 0 = 1)
    (hneg : ∀ v, Exp (-v) = (Exp v)⁻¹)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (X : I → V) (w : List (I × ℝ)) (i : I) {g : G}
    (hg : g ∈ generatorWordBase U Exp X w) :
    g ∈ generatorWordBase U Exp X (w ++ [(i, 0)] ++ inverseGeneratorWord w) := by
  rw [List.append_assoc, mem_generatorWordBase_append U Exp hExp0]
  refine ⟨hg, ?_⟩
  rw [List.singleton_append, mem_generatorWordBase_zero_cons U Exp hExp0]
  exact mem_generatorWordBase_inverse U Exp hExp0 hneg hadd X w hg

theorem generatorGroupWord_conjugate_zero
    (Exp : V → G) (hExp0 : Exp 0 = 1) (hneg : ∀ v, Exp (-v) = (Exp v)⁻¹)
    (X : I → V) (w : List (I × ℝ)) (i : I) :
    generatorGroupWord X Exp (w ++ [(i, 0)] ++ inverseGeneratorWord w) = 1 := by
  have he : generatorGroupWord X Exp (w ++ [(i, 0)] ++ inverseGeneratorWord w) =
      generatorGroupWord X Exp w * generatorGroupWord X Exp (inverseGeneratorWord w) := by
    simp [generatorGroupWord, List.map_append, List.prod_append, hExp0]
  rw [he, generatorGroupWord_inverse_of_exp_neg Exp hneg X w, mul_inv_cancel]

theorem mem_generatorWordBase_flatten_loops
    (U : Set G) (Exp : V → G) (hExp0 : Exp 0 = 1) (X : I → V)
    (ws : List (List (I × ℝ))) {g : G}
    (hg : g ∈ U)
    (hws : ∀ w ∈ ws, g ∈ generatorWordBase U Exp X w ∧ generatorGroupWord X Exp w = 1) :
    g ∈ generatorWordBase U Exp X ws.flatten := by
  induction ws with
  | nil => exact hg
  | cons w ws ih =>
    rw [List.flatten_cons, mem_generatorWordBase_append U Exp hExp0]
    obtain ⟨hw, he⟩ := hws w (List.mem_cons_self ..)
    refine ⟨hw, ?_⟩
    rw [he, mul_one]
    exact ih (fun z hz => hws z (List.mem_cons_of_mem _ hz))

theorem mem_generatorScheme_zero
    (U : Set G) (Exp : V → G) (hExp0 : Exp 0 = 1)
    (hneg : ∀ v, Exp (-v) = (Exp v)⁻¹)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (X : I → V) {n : ℕ} (w : Fin n → List (I × ℝ)) (i : Fin n → I)
    {g : G} (hg : g ∈ U) (hw : ∀ k, g ∈ generatorWordBase U Exp X (w k)) :
    g ∈ generatorWordBase U Exp X (generatorSchemeWord w i 0) := by
  apply mem_generatorWordBase_flatten_loops U Exp hExp0 X _ hg
  intro z hz
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hz
  exact ⟨mem_generatorWordBase_conjugate_zero U Exp hExp0 hneg hadd X (w k) (i k) (hw k),
    generatorGroupWord_conjugate_zero Exp hExp0 hneg X (w k) (i k)⟩

end PolycyclicRecognition

end

end OAI
