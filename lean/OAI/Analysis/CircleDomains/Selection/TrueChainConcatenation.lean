import OAI.Analysis.CircleDomains.Selection.FiniteJumpSystems
import OAI.Analysis.CircleDomains.Modulus.JoinedDomainCost
import OAI.Analysis.CircleDomains.Topology.ConstantPhysicalPath

namespace OAI

/-! A finite chain containing only true paths concatenates to one allowed
true path with exactly the same full cost. This supplies the initial stage. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_path_of_true_paid_chain
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    {x y : X} {c : ℝ≥0∞}
    (hc : PaidChain ((FiniteJumpSystem.empty : FiniteJumpSystem X).edge d ν N g m) x y c)
    (hx : x ∈ d.quotientDomain) (hy : y ∈ d.quotientDomain) :
    ∃Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) ∧
      Γ.1.val ⊥ = x ∧ Γ.1.val ⊤ = y ∧ physicalTollCost d g m Γ.1 = c := by
  induction hc with
  | refl x =>
      obtain ⟨γ, θ, hγ, heq, hcost⟩ := exists_allowed_constant_physical_path
        d hdisj ν N hx g m (hm _ hx)
      exact ⟨(γ, θ), hγ, heq ⊥, heq ⊤, hcost⟩
  | @cons x y z a b hedge _ ih =>
      rcases hedge with ⟨Γ, hΓ, hΓ0, hΓ1, hxU, hyU, hΓcost⟩ | ⟨i, _⟩
      · obtain ⟨Δ, hΔ, hΔ0, hΔ1, hΔcost⟩ := ih hyU hy
        obtain ⟨ρ, hρ, hρ0, hρ1, hρcost⟩ := exists_allowed_joined_full_cost
          d hU ν N g hg m hm Γ Δ hΓ hΔ (hΓ0.symm ▸ hxU) (hΓ1.symm ▸ hyU)
          (hΔ1.symm ▸ hy) (hΓ1.trans hΔ0.symm) hpoint
        refine ⟨ρ, hρ, hρ0.trans hΓ0, hρ1.trans hΔ1, ?_⟩
        rw [hρcost, hΓcost, hΔcost]
      · exact PEmpty.elim i

end CircleDomainRigidity

end

end OAI
