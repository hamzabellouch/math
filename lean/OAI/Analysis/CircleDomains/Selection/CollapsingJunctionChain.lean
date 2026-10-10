import OAI.Analysis.CircleDomains.Selection.ApproximateFiniteConcatenation

namespace OAI

/-! In a chain of limiting junctions an equal consecutive pair requires
no extra path or pause. Only distinct pairs are connected, and every
actually used junction is paid once. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_allowed_collapsing_junction_prefix
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (F : Set X) (n : ℕ) (p : Fin (n+1) → X)
    (A : Fin (n+1) → ℝ≥0∞) (J : Fin n → ℝ≥0∞)
    (hpaid : ∀i : Fin n, m (p i.castSucc) ≤ J i)
    (hfirst : ∀ε : ℝ, 0 < ε →
      ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
        AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∧ ρ.val ⊤ = p 0 ∧
        interiorPhysicalTollCost d g m ρ ≤ A 0 + ENNReal.ofReal ε)
    (hstep : ∀i : Fin n, p i.castSucc ≠ p i.succ → ∀ε : ℝ, 0 < ε →
      ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
        AllowedTaggedPath d ν N (ρ.val, θ) ∧
        ρ.val ⊥ = p i.castSucc ∧ ρ.val ⊤ = p i.succ ∧
        interiorPhysicalTollCost d g m ρ ≤ A i.succ + ENNReal.ofReal ε)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∧ ρ.val ⊤ = p (Fin.last n) ∧
      interiorPhysicalTollCost d g m ρ ≤ (∑i, A i) + (∑i, J i) + ENNReal.ofReal η := by
  classical
  induction n generalizing η with
  | zero =>
      obtain ⟨ρ, θ, hρ, hρ0, hρ1, hc⟩ := hfirst η hη
      exact ⟨ρ, θ, hρ, hρ0, hρ1, by simpa using hc⟩
  | succ n ih =>
      have hh : 0 < η/2 := by positivity
      let p' : Fin (n+1) → X := fun i => p i.castSucc
      let A' : Fin (n+1) → ℝ≥0∞ := fun i => A i.castSucc
      let J' : Fin n → ℝ≥0∞ := fun i => J i.castSucc
      have hp' (i : Fin n) : m (p' i.castSucc) ≤ J' i := hpaid i.castSucc
      have hf' : ∀ε : ℝ, 0 < ε →
          ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
            AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∧ ρ.val ⊤ = p' 0 ∧
            interiorPhysicalTollCost d g m ρ ≤ A' 0 + ENNReal.ofReal ε := hfirst
      have hs' (i : Fin n) (hne : p' i.castSucc ≠ p' i.succ) (ε : ℝ) (hε : 0 < ε) :
          ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
            AllowedTaggedPath d ν N (ρ.val, θ) ∧
            ρ.val ⊥ = p' i.castSucc ∧ ρ.val ⊤ = p' i.succ ∧
            interiorPhysicalTollCost d g m ρ ≤ A' i.succ + ENNReal.ofReal ε :=
        hstep i.castSucc hne ε hε
      obtain ⟨α, θα, hα, hα0, hα1, hαc⟩ := ih p' A' J' hp' hf' hs' hh
      have hsA := Fin.sum_univ_castSucc A
      have hsJ := Fin.sum_univ_castSucc J
      by_cases heq : p (Fin.last n).castSucc = p (Fin.last (n+1))
      · refine ⟨α, θα, hα, hα0, hα1.trans heq, ?_⟩
        have he : ENNReal.ofReal (η/2) ≤ ENNReal.ofReal η :=
          ENNReal.ofReal_le_ofReal (by linarith)
        calc
          interiorPhysicalTollCost d g m α ≤ (∑i, A' i) + (∑i, J' i) + ENNReal.ofReal η :=
            hαc.trans (add_le_add le_rfl he)
          _ ≤ ((∑i, A' i) + A (Fin.last (n+1))) +
              ((∑i, J' i) + J (Fin.last n)) + ENNReal.ofReal η :=
            add_le_add (add_le_add (le_add_right le_rfl) (le_add_right le_rfl)) le_rfl
          _ = (∑i, A i) + (∑i, J i) + ENNReal.ofReal η := by
            rw [hsA, hsJ]
      · obtain ⟨β, θβ, hβ, hβ0, hβ1, hβc⟩ := hstep (Fin.last n) heq (η/2) hh
        obtain ⟨ρ, θ, hρ, hρ0, hρ1, hc⟩ := exists_allowed_joined_junction_cost
          d hU ν N (α, θα) (β, θβ) hα hβ (hα1.trans hβ0.symm) g hg m hpoint
        refine ⟨ρ, θ, hρ, hρ0.symm ▸ hα0, hρ1.trans hβ1, ?_⟩
        have herr : ENNReal.ofReal (η/2) + ENNReal.ofReal (η/2) = ENNReal.ofReal η := by
          rw [← ENNReal.ofReal_add hh.le hh.le]
          congr 1
          ring
        calc
          interiorPhysicalTollCost d g m ρ =
              interiorPhysicalTollCost d g m α + interiorPhysicalTollCost d g m β + m (p' (Fin.last n)) := by
            rw [hc, hα1]
          _ ≤ ((∑i, A' i) + (∑i, J' i) + ENNReal.ofReal (η/2)) +
              (A (Fin.last (n+1)) + ENNReal.ofReal (η/2)) + J (Fin.last n) :=
            add_le_add (add_le_add hαc hβc) (hpaid (Fin.last n))
          _ = (∑i, A i) + (∑i, J i) + ENNReal.ofReal η := by
            rw [hsA, hsJ, ← herr]
            dsimp [A', J']
            ac_rfl

end CircleDomainRigidity

end

end OAI
