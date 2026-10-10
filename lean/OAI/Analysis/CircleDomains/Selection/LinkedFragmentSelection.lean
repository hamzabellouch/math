import OAI.Analysis.CircleDomains.Topology.CollarFragmentSelection
import OAI.Analysis.CircleDomains.Modulus.InterleavedCollarCost

namespace OAI

/-! Simultaneous selection of actual fragments and joining arcs. Both ends
of each chosen fragment lie in the neighborhoods needed by its two neighbors. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_linked_fragment_selection
    (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (γ : ℕ → ℕ → TaggedPhysicalPath d) (x : ℕ → X) (C T : ℕ → Set X)
    (hΓ : ∀n j, j ≤ n → AllowedTaggedPath d ν N ((γ n j).1.val, (γ n j).2))
    (hstart : ∀n j, j ≤ n → (γ n j).1.val ⊥ ∈ C (j+1))
    (hstop : ∀n j, j ≤ n → (γ n j).1.val ⊤ ∈ C j)
    (hstartlim : ∀j, Tendsto (fun n => (γ n j).1.val ⊥) atTop (𝓝 (x (j+1))))
    (hstoplim : ∀j, Tendsto (fun n => (γ n j).1.val ⊤) atTop (𝓝 (x j)))
    (c ε δ : ℕ → ℝ≥0∞) (A E : ℝ≥0∞) (hA : A < ∞)
    (hcostlim : ∀j, Tendsto (fun n => physicalTollCost d g m (γ n j).1) atTop (𝓝 (c j)))
    (hc : (∑'j, c j) ≤ A) (hε : ∀j, 0 < ε j) (hεsum : (∑'j, ε j) ≤ E)
    (hbridge : ∀j, ∃ U : Set X, U ∈ 𝓝 (x (j+1)) ∧
      ∀a ∈ U ∩ C (j+1), ∀b ∈ U ∩ C (j+1),
        ∃ ρ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
          ρ.1.val ⊥ = a ∧ ρ.1.val ⊤ = b ∧ range ρ.1.val ⊆ T j ∧
          physicalTollCost d g m ρ.1 ≤ δ j) :
    ∃ (M : ℕ → ℕ) (b : ℕ → TaggedPhysicalPath d),
      (∀j, j ≤ M j) ∧
      (∀j, AllowedTaggedPath d ν N ((γ (M j) j).1.val, (γ (M j) j).2)) ∧
      (∀j, AllowedTaggedPath d ν N ((b j).1.val, (b j).2)) ∧
      (∀j, (b j).1.val ⊥ = (γ (M (j+1)) (j+1)).1.val ⊤) ∧
      (∀j, (b j).1.val ⊤ = (γ (M j) j).1.val ⊥) ∧
      (∀j, range (b j).1.val ⊆ T j) ∧
      ((∑'j, physicalTollCost d g m (γ (M j) j).1) ≤ A + E) ∧
      ((∑'j, physicalTollCost d g m (b j).1) ≤ ∑'j, δ j) := by
  classical
  choose U hU hlink using hbridge
  let V : ℕ → Set X := fun j => match j with
    | 0 => univ
    | j+1 => U j
  have hV (j : ℕ) : V j ∈ 𝓝 (x j) := by
    cases j with
    | zero => exact univ_mem
    | succ j => exact hU j
  have hfinite (j : ℕ) : c j ≠ ∞ := ne_top_of_le_ne_top hA.ne
    ((ENNReal.le_tsum j).trans hc)
  obtain ⟨M, hM⟩ := exists_close_fragment_selection
    (fun n j => (γ n j).1.val ⊥) (fun n j => (γ n j).1.val ⊤)
    (fun n j => physicalTollCost d g m (γ n j).1)
    (fun j => x (j+1)) x c ε hstartlim hstoplim hcostlim hfinite
    (fun j => (hε j).ne') U V hU hV
  have hlinks (j : ℕ) : ∃ ρ : TaggedPhysicalPath d,
      AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
      ρ.1.val ⊥ = (γ (M (j+1)) (j+1)).1.val ⊤ ∧
      ρ.1.val ⊤ = (γ (M j) j).1.val ⊥ ∧ range ρ.1.val ⊆ T j ∧
      physicalTollCost d g m ρ.1 ≤ δ j := by
    apply hlink j _ ⟨(hM (j+1)).2.2.1, hstop _ _ (hM (j+1)).1⟩
      _ ⟨(hM j).2.1, hstart _ _ (hM j).1⟩
  choose b hb using hlinks
  refine ⟨M, b, fun j => (hM j).1, fun j => hΓ _ _ (hM j).1,
    fun j => (hb j).1, fun j => (hb j).2.1, fun j => (hb j).2.2.1,
    fun j => (hb j).2.2.2.1, ?_, ?_⟩
  · exact selected_fragment_total_cost (fun n j => physicalTollCost d g m (γ n j).1)
      M c ε A E (fun j => (hM j).2.2.2) hc hεsum
  · exact ENNReal.tsum_le_tsum (fun j => (hb j).2.2.2.2)

end CircleDomainRigidity

end

end OAI
