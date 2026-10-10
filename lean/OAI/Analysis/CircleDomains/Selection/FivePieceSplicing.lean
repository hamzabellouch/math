import OAI.Analysis.CircleDomains.Modulus.InteriorPhysicalCost

namespace OAI

/-! The exact five-piece attachment used by collar splicing: initial tail,
short arc, retained middle, short arc, final tail. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_allowed_five_piece_splicing (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (a b c e f : TaggedPhysicalPath d)
    (ha : AllowedTaggedPath d ν N (a.1.val, a.2))
    (hb : AllowedTaggedPath d ν N (b.1.val, b.2))
    (hc : AllowedTaggedPath d ν N (c.1.val, c.2))
    (he : AllowedTaggedPath d ν N (e.1.val, e.2))
    (hf : AllowedTaggedPath d ν N (f.1.val, f.2))
    (hab : a.1.val ⊤ = b.1.val ⊥) (hbc : b.1.val ⊤ = c.1.val ⊥)
    (hce : c.1.val ⊤ = e.1.val ⊥) (hef : e.1.val ⊤ = f.1.val ⊥)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hma : m (a.1.val ⊤) = 0) (hmb : m (b.1.val ⊤) = 0)
    (hmc : m (c.1.val ⊤) = 0) (hme : m (e.1.val ⊤) = 0)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ = a.1.val ⊥ ∧ ρ.val ⊤ = f.1.val ⊤ ∧
      interiorPhysicalTollCost d g m ρ = interiorPhysicalTollCost d g m a.1 +
        interiorPhysicalTollCost d g m b.1 + interiorPhysicalTollCost d g m c.1 +
        interiorPhysicalTollCost d g m e.1 + interiorPhysicalTollCost d g m f.1 := by
  obtain ⟨ab, tab, habA, hab0, hab1, habcost⟩ :=
    exists_allowed_joined_interior_cost d hU ν N a b ha hb hab g hg m hma hpoint
  obtain ⟨abc, tabc, habcA, habc0, habc1, habccost⟩ :=
    exists_allowed_joined_interior_cost d hU ν N (ab, tab) c habA hc
      (hab1.trans hbc) g hg m (by rw [hab1]; exact hmb) hpoint
  obtain ⟨abce, tabce, habceA, habce0, habce1, habcecost⟩ :=
    exists_allowed_joined_interior_cost d hU ν N (abc, tabc) e habcA he
      (habc1.trans hce) g hg m (by rw [habc1]; exact hmc) hpoint
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hρcost⟩ :=
    exists_allowed_joined_interior_cost d hU ν N (abce, tabce) f habceA hf
      (habce1.trans hef) g hg m (by rw [habce1]; exact hme) hpoint
  refine ⟨ρ, θ, hρ, hρ0.trans (habce0.trans (habc0.trans hab0)), hρ1, ?_⟩
  rw [hρcost, habcecost, habccost, habcost]

end CircleDomainRigidity

end

end OAI
