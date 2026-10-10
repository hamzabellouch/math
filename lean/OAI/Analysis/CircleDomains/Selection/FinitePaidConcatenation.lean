import OAI.Analysis.CircleDomains.Modulus.JoinedJunctionCost

namespace OAI

/-! Finite allowed concatenation with exact multiplicity: each interior
piece contributes its interior cost and each junction contributes one toll. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_allowed_finite_paid_concatenation
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (n : ℕ) (Γ : Fin (n+1) → TaggedPhysicalPath d)
    (hΓ : ∀i, AllowedTaggedPath d ν N ((Γ i).1.val, (Γ i).2))
    (hjoin : ∀i : Fin n, (Γ i.castSucc).1.val ⊤ = (Γ i.succ).1.val ⊥) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧
      ρ.val ⊥ = (Γ 0).1.val ⊥ ∧ ρ.val ⊤ = (Γ (Fin.last n)).1.val ⊤ ∧
      interiorPhysicalTollCost d g m ρ =
        (∑i, interiorPhysicalTollCost d g m (Γ i).1) +
        ∑i : Fin n, m ((Γ i.castSucc).1.val ⊤) := by
  induction n with
  | zero =>
      refine ⟨(Γ 0).1, (Γ 0).2, hΓ 0, rfl, rfl, ?_⟩
      simp
  | succ n ih =>
      let Γ' : Fin (n+1) → TaggedPhysicalPath d := fun i => Γ i.castSucc
      have hΓ' (i : Fin (n+1)) : AllowedTaggedPath d ν N ((Γ' i).1.val, (Γ' i).2) :=
        hΓ i.castSucc
      have hj' (i : Fin n) : (Γ' i.castSucc).1.val ⊤ = (Γ' i.succ).1.val ⊥ :=
        hjoin i.castSucc
      obtain ⟨α, θα, hα, hα0, hα1, hαcost⟩ := ih Γ' hΓ' hj'
      have hj : α.val ⊤ = (Γ (Fin.last (n+1))).1.val ⊥ :=
        hα1.trans (hjoin (Fin.last n))
      obtain ⟨ρ, θ, hρ, hρ0, hρ1, hρcost⟩ := exists_allowed_joined_junction_cost
        d hU ν N (α, θα) (Γ (Fin.last (n+1))) hα (hΓ _) hj g hg m hpoint
      refine ⟨ρ, θ, hρ, hρ0.trans hα0, hρ1, ?_⟩
      have hs₁ := Fin.sum_univ_castSucc
        (fun i : Fin (n+2) => interiorPhysicalTollCost d g m (Γ i).1)
      have hs₂ := Fin.sum_univ_castSucc
        (fun i : Fin (n+1) => m ((Γ i.castSucc).1.val ⊤))
      rw [hρcost, hαcost, hα1, hs₁, hs₂]
      dsimp [Γ']
      ac_rfl

end CircleDomainRigidity

end

end OAI
