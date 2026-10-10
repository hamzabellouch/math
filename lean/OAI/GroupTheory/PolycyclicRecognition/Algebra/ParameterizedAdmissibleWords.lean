import OAI.GroupTheory.PolycyclicRecognition.Algebra.AdmissibleWordOperations
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExpandedSchemeAmplitudes

namespace OAI

/-! # Admissibility is stable under perturbing all word amplitudes -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {G V I P : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace P]

theorem eventually_parameterized_generatorWord
    (U : Set G) (hU : IsOpen U) (Exp : V → G) (hExp : Continuous Exp) (X : I → V)
    (w : List (I × (P → ℝ))) (hc : ∀ p ∈ w, Continuous p.2)
    (g : P → G) (hg : Continuous g) {p₀ : P}
    (hbase : g p₀ ∈ generatorWordBase U Exp X (w.map (fun q => (q.1, q.2 p₀)))) :
    ∀ᶠ p in 𝓝 p₀, g p ∈ generatorWordBase U Exp X (w.map (fun q => (q.1, q.2 p))) := by
  induction w generalizing g with
  | nil => exact hg.continuousAt.eventually (hU.mem_nhds hbase)
  | cons q w ih =>
    have hq : Continuous q.2 := hc q (List.mem_cons_self ..)
    have htail := ih (fun p hp => hc p (List.mem_cons_of_mem _ hp))
      (fun p => g p * Exp (q.2 p • X q.1)) (by fun_prop) hbase.2
    let F : P → C(ℝ, G) := fun p =>
      ⟨fun r => g p * Exp (r • (q.2 p • X q.1)), by fun_prop⟩
    have hF : Continuous F := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : P × ℝ => g z.1 * Exp (z.2 • (q.2 z.1 • X q.1)))
      fun_prop
    have ho := ContinuousMap.continuous_compactOpen.mp hF
      (Icc (0 : ℝ) 1) isCompact_Icc U hU
    have hfirst : ∀ᶠ p in 𝓝 p₀, g p ∈ flowLineBase U Exp (q.2 p • X q.1) 1 :=
      ho.mem_nhds hbase.1
    filter_upwards [hfirst, htail] with p hp hptail
    exact ⟨hp, hptail⟩

theorem eventually_generatorScheme
    (U : Set G) (hU : IsOpen U) (Exp : V → G) (hExp : Continuous Exp) (X : I → V)
    {n : ℕ} (w : Fin n → List (I × ℝ)) (i : Fin n → I)
    {g : G} (hbase : g ∈ generatorWordBase U Exp X (generatorSchemeWord w i 0)) :
    ∀ᶠ t : Fin n → ℝ in 𝓝 0,
      g ∈ generatorWordBase U Exp X (generatorSchemeWord w i t) := by
  let l := (schemeAmplitudeSlots w i).map
    (fun q => (q.1, fun t : Fin n → ℝ => evaluateAmplitudeSlot t q.2))
  have hcont : ∀ p ∈ l, Continuous p.2 := by
    intro p hp
    obtain ⟨q, _hq, rfl⟩ := List.mem_map.mp hp
    cases q.2 with
    | inl r => exact continuous_const
    | inr j => exact continuous_apply j
  have he (t : Fin n → ℝ) : l.map (fun q => (q.1, q.2 t)) = generatorSchemeWord w i t := by
    simp only [l, List.map_map, Function.comp_def]
    exact map_schemeAmplitudeSlots w i t
  have h := eventually_parameterized_generatorWord U hU Exp hExp X l hcont
    (fun _ => g) continuous_const (p₀ := 0) (by rwa [he])
  simpa only [he] using h

end PolycyclicRecognition

end

end OAI
