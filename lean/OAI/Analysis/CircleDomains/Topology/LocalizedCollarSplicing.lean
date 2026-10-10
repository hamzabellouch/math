import OAI.Analysis.CircleDomains.Topology.CollarSplicingFromFragments

namespace OAI

/-! The collar endpoint may be selected in any prescribed neighborhood of
its limiting outer hit point, for attaching a common middle fragment. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_collar_path_from_fragment_limits_near
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
    (O : Set X) (hO : O ∈ 𝓝 (x 0))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀y ∈ d.physicalDomain, w ≤ g y)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ (k : ℕ) (η : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (η.val, θ) ∧ η.val ⊥ = p ∧ η.val ⊤ = (γ k 0).1.val ⊤ ∧ η.val ⊤ ∈ O ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint η) +
        timeToll η.val (Ioo (⊥ : PathTime) ⊤) m ≤ A + E + F := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp ((hstoplim 0).eventually hO)
  let σ : ℕ → ℕ := fun n => n + K
  have hσ : Tendsto σ atTop atTop := tendsto_add_atTop_nat K
  have hle (n : ℕ) : n ≤ σ n := Nat.le_add_right n K
  obtain ⟨k, η, θ, hη, hη0, hη1, hcost⟩ := exists_collar_path_from_fragment_limits
    d hU hG ν N p g hg m (fun n j => γ (σ n) j) x C T
    (fun n j hj => hΓ _ _ (hj.trans (hle n)))
    (fun n j hj => hstart _ _ (hj.trans (hle n)))
    (fun n j hj => hstop _ _ (hj.trans (hle n)))
    (fun j => (hstartlim j).comp hσ) (fun j => (hstoplim j).comp hσ)
    c ε δ A E F hA hE hF (fun j => (hcostlim j).comp hσ) hc hε hεsum hδsum hbridge
    (fun n j hj => hm _ _ (hj.trans (hle n)))
    (by
      intro V hV
      obtain ⟨l, hl⟩ := hγtail V hV
      exact ⟨l, fun j hj n hn s => hl j hj (σ n) (hn.trans (hle n)) s⟩)
    hTtail w hw hpos hpoint
  exact ⟨σ k, η, θ, hη, hη0, hη1, hη1 ▸ hK (σ k) (Nat.le_add_left K k), hcost⟩

end CircleDomainRigidity

end

end OAI
