import OAI.Analysis.CircleDomains.Selection.FinitePaidConcatenation

namespace OAI

/-! Approximate pieces can be concatenated across singleton anchors, with
one prescribed budget at each internal junction and one total error. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_allowed_approximate_finite_concatenation
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (n : ℕ) (E : Fin (n+2) → Set X) (A : Fin (n+1) → ℝ≥0∞)
    (J : Fin n → ℝ≥0∞)
    (hsingle : ∀i : Fin n, (E i.succ.castSucc).Subsingleton)
    (hpaid : ∀i : Fin n, ∀x ∈ E i.succ.castSucc, m x ≤ J i)
    (hpiece : ∀i : Fin (n+1), ∀ε : ℝ, 0 < ε →
      ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
        AllowedTaggedPath d ν N (ρ.val, θ) ∧
        ρ.val ⊥ ∈ E i.castSucc ∧ ρ.val ⊤ ∈ E i.succ ∧
        interiorPhysicalTollCost d g m ρ ≤ A i + ENNReal.ofReal ε)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧
      ρ.val ⊥ ∈ E 0 ∧ ρ.val ⊤ ∈ E (Fin.last (n+1)) ∧
      interiorPhysicalTollCost d g m ρ ≤ (∑i, A i) + (∑i, J i) + ENNReal.ofReal η := by
  induction n generalizing η with
  | zero =>
      obtain ⟨ρ, θ, hρ, hρ0, hρ1, hc⟩ := hpiece 0 η hη
      exact ⟨ρ, θ, hρ, hρ0, hρ1, by simpa using hc⟩
  | succ n ih =>
      have hh : 0 < η/2 := by positivity
      let E' : Fin (n+2) → Set X := fun i => E i.castSucc
      let A' : Fin (n+1) → ℝ≥0∞ := fun i => A i.castSucc
      let J' : Fin n → ℝ≥0∞ := fun i => J i.castSucc
      have hs' (i : Fin n) : (E' i.succ.castSucc).Subsingleton := hsingle i.castSucc
      have hp' (i : Fin n) (x : X) (hx : x ∈ E' i.succ.castSucc) : m x ≤ J' i :=
        hpaid i.castSucc x hx
      have hpieces' (i : Fin (n+1)) (ε : ℝ) (hε : 0 < ε) :
          ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
            AllowedTaggedPath d ν N (ρ.val, θ) ∧
            ρ.val ⊥ ∈ E' i.castSucc ∧ ρ.val ⊤ ∈ E' i.succ ∧
            interiorPhysicalTollCost d g m ρ ≤ A' i + ENNReal.ofReal ε :=
        hpiece i.castSucc ε hε
      obtain ⟨α, θα, hα, hα0, hα1, hαc⟩ := ih E' A' J' hs' hp' hpieces' hh
      obtain ⟨β, θβ, hβ, hβ0, hβ1, hβc⟩ := hpiece (Fin.last (n+1)) (η/2) hh
      have hj : α.val ⊤ = β.val ⊥ := hsingle (Fin.last n) hα1 hβ0
      obtain ⟨ρ, θ, hρ, hρ0, hρ1, hc⟩ := exists_allowed_joined_junction_cost
        d hU ν N (α, θα) (β, θβ) hα hβ hj g hg m hpoint
      refine ⟨ρ, θ, hρ, hρ0.symm ▸ hα0, hρ1.symm ▸ hβ1, ?_⟩
      have herr : ENNReal.ofReal (η/2) + ENNReal.ofReal (η/2) = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add hh.le hh.le]
        congr 1
        ring
      have hsA := Fin.sum_univ_castSucc A
      have hsJ := Fin.sum_univ_castSucc J
      calc
        interiorPhysicalTollCost d g m ρ =
            interiorPhysicalTollCost d g m α + interiorPhysicalTollCost d g m β + m (α.val ⊤) := hc
        _ ≤ ((∑i, A' i) + (∑i, J' i) + ENNReal.ofReal (η/2)) +
            (A (Fin.last (n+1)) + ENNReal.ofReal (η/2)) + J (Fin.last n) :=
          add_le_add (add_le_add hαc hβc) (hpaid (Fin.last n) _ hα1)
        _ = (∑i, A i) + (∑i, J i) + ENNReal.ofReal η := by
          rw [hsA, hsJ, ← herr]
          dsimp [A', J']
          ac_rfl

end CircleDomainRigidity

end

end OAI
