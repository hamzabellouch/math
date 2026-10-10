import OAI.Analysis.CircleDomains.Selection.LinkedFragmentSelection

namespace OAI

/-! The one-ended collar assembled from convergent actual fragments and
short joining arcs. This is the constructive gluing step of Section 3. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_collar_path_from_fragment_limits
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (p : X) (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (γ : ℕ → ℕ → TaggedPhysicalPath d) (x : ℕ → X) (C T : ℕ → Set X)
    (hΓ : ∀n j, j ≤ n → AllowedTaggedPath d ν N ((γ n j).1.val, (γ n j).2))
    (hstart : ∀n j, j ≤ n → (γ n j).1.val ⊥ ∈ C (j+1))
    (hstop : ∀n j, j ≤ n → (γ n j).1.val ⊤ ∈ C j)
    (hstartlim : ∀j, Tendsto (fun n => (γ n j).1.val ⊥) atTop (𝓝 (x (j+1))))
    (hstoplim : ∀j, Tendsto (fun n => (γ n j).1.val ⊤) atTop (𝓝 (x j)))
    (c ε δ : ℕ → ℝ≥0∞) (A E F : ℝ≥0∞)
    (hA : A < ∞) (hE : E < ∞) (hF : F < ∞)
    (hcostlim : ∀j, Tendsto (fun n => physicalTollCost d g m (γ n j).1) atTop (𝓝 (c j)))
    (hc : (∑'j, c j) ≤ A) (hε : ∀j, 0 < ε j) (hεsum : (∑'j, ε j) ≤ E)
    (hδsum : (∑'j, δ j) ≤ F)
    (hbridge : ∀j, ∃ U : Set X, U ∈ 𝓝 (x (j+1)) ∧
      ∀a ∈ U ∩ C (j+1), ∀b ∈ U ∩ C (j+1),
        ∃ ρ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
          ρ.1.val ⊥ = a ∧ ρ.1.val ⊤ = b ∧ range ρ.1.val ⊆ T j ∧
          physicalTollCost d g m ρ.1 ≤ δ j)
    (hm : ∀n j, j ≤ n → m ((γ n j).1.val ⊥) = 0 ∧ m ((γ n j).1.val ⊤) = 0)
    (hγtail : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, ∀n ≥ j, ∀s, (γ n j).1.val s ∈ V)
    (hTtail : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, T j ⊆ V)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀y ∈ d.physicalDomain, w ≤ g y)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ (k : ℕ) (η : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (η.val, θ) ∧ η.val ⊥ = p ∧ η.val ⊤ = (γ k 0).1.val ⊤ ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint η) +
        timeToll η.val (Ioo (⊥ : PathTime) ⊤) m ≤ A + E + F := by
  obtain ⟨M, b, hM, ha, hb, hleft, hright, hbT, hacost, hbcost⟩ :=
    exists_linked_fragment_selection d ν N g m γ x C T hΓ hstart hstop hstartlim hstoplim
      c ε δ A E hA hcostlim hc hε hεsum hbridge
  let a : ℕ → TaggedPhysicalPath d := fun j => γ (M j) j
  have hatail : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, ∀s, (a j).1.val s ∈ V := by
    intro V hV
    obtain ⟨k, hk⟩ := hγtail V hV
    exact ⟨k, fun j hj s => hk j hj (M j) (hM j) s⟩
  have hbtail : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, ∀s, (b j).1.val s ∈ V := by
    intro V hV
    obtain ⟨k, hk⟩ := hTtail V hV
    exact ⟨k, fun j hj s => hk j hj (hbT j (mem_range_self s))⟩
  have hb0 (j : ℕ) : m ((b j).1.val ⊥) = 0 := by
    rw [hleft j]
    exact (hm _ _ (hM (j+1))).2
  have hb1 (j : ℕ) : m ((b j).1.val ⊤) = 0 := by
    rw [hright j]
    exact (hm _ _ (hM j)).1
  obtain ⟨η, θ, hη, hη0, hη1, hcost⟩ := exists_allowed_interleaved_collar d hU hG ν N
    p a b ha hb hleft hright hatail hbtail g hg m w hw hpos
    (fun j => (hm _ _ (hM j)).1) (fun j => (hm _ _ (hM j)).2) hb0 hb1
    (A+E) F (ENNReal.add_lt_top.mpr ⟨hA, hE⟩) hF hacost (hbcost.trans hδsum) hpoint
  exact ⟨M 0, η, θ, hη, hη0, hη1, hcost⟩

end CircleDomainRigidity

end

end OAI
