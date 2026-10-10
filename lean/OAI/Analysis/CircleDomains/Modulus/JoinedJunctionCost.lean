import OAI.Analysis.CircleDomains.Modulus.JoinedPhysicalCost

namespace OAI

/-! Joining at a dust point incurs exactly one junction toll. This is
the accounting used to replace collapsing jumps by actual paths. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem joinedPath_interior_toll_with_junction
    (γ δ : C(PathTime, X)) (h : γ ⊤ = δ ⊥) (m : X → ℝ≥0∞) :
    timeToll (joinedPath γ δ h) (Ioo (⊥ : PathTime) ⊤) m =
      timeToll γ (Ioo (⊥ : PathTime) ⊤) m +
        timeToll δ (Ioo (⊥ : PathTime) ⊤) m + m (γ ⊤) := by
  let c := collarTime 1
  have hc0 : (⊥ : PathTime) < c := collarTime_pos 1
  have hc1 : c < (⊤ : PathTime) :=
    collarTime_zero ▸ collarTime_strictAnti (by omega : 0 < 1)
  have hmid : joinedPath γ δ h c = γ ⊤ := by
    simpa only [affinePathTime_one] using joinedPath_first γ δ h ⊤
  have hset : Ioo (⊥ : PathTime) ⊤ = (Ioo ⊥ c ∪ Ioo c ⊤) ∪ {c} := by
    ext t
    constructor
    · intro ht
      rcases lt_trichotomy t c with hlt | heq | hgt
      · exact Or.inl (Or.inl ⟨ht.1, hlt⟩)
      · exact Or.inr heq
      · exact Or.inl (Or.inr ⟨hgt, ht.2⟩)
    · rintro ((ht | ht) | ht)
      · exact ⟨ht.1, ht.2.trans hc1⟩
      · exact ⟨hc0.trans ht.1, ht.2⟩
      · exact ht.symm ▸ ⟨hc0, hc1⟩
  have hd : Disjoint (Ioo (⊥ : PathTime) c) (Ioo c ⊤) := by
    apply disjoint_left.mpr
    intro t ht hs
    exact ht.2.not_gt hs.1
  have hdc : Disjoint (Ioo (⊥ : PathTime) c ∪ Ioo c ⊤) {c} := by
    apply disjoint_singleton_right.mpr
    simp
  have hsingle : timeToll (joinedPath γ δ h) {c} m = m (γ ⊤) := by
    rw [timeToll_eq_indicator]
    simp [hmid]
  conv_lhs => rw [hset]
  rw [timeToll_union _ _ hdc, timeToll_union _ _ hd, hsingle]
  congr 1
  congr 1
  · rw [← interiorToll_affine (joinedPath γ δ h) m hc0]
    exact timeToll_congr_path m (fun t _ => joinedPath_first γ δ h t)
  · rw [← interiorToll_affine (joinedPath γ δ h) m hc1]
    exact timeToll_congr_path m (fun t _ => joinedPath_second γ δ h t)

variable {Y : Type*} [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem interiorPhysicalTollCost_joined_with_junction (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (γ δ : FinitePhysicalPath d.domainEquiv d.basePoint) (h : γ.val ⊤ = δ.val ⊥) :
    interiorPhysicalTollCost d g m (joinedFinitePhysicalPath d.domainEquiv hU d.basePoint γ δ h) =
      interiorPhysicalTollCost d g m γ + interiorPhysicalTollCost d g m δ + m (γ.val ⊤) := by
  unfold interiorPhysicalTollCost
  rw [physicalCost_joined d.domainEquiv hU d.basePoint γ δ h g hg]
  change _ + timeToll (joinedPath γ.val δ.val h) (Ioo (⊥ : PathTime) ⊤) m = _
  rw [joinedPath_interior_toll_with_junction γ.val δ.val h m]
  ac_rfl

theorem exists_allowed_joined_junction_cost (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ Δ : TaggedPhysicalPath d)
    (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    (hΔ : AllowedTaggedPath d ν N (Δ.1.val, Δ.2))
    (h : Γ.1.val ⊤ = Δ.1.val ⊥)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ = Γ.1.val ⊥ ∧ ρ.val ⊤ = Δ.1.val ⊤ ∧
      interiorPhysicalTollCost d g m ρ =
        interiorPhysicalTollCost d g m Γ.1 + interiorPhysicalTollCost d g m Δ.1 + m (Γ.1.val ⊤) := by
  obtain ⟨θ, hθ⟩ := exists_allowed_joined_path d hU ν N Γ Δ hΓ hΔ h hpoint
  exact ⟨joinedFinitePhysicalPath d.domainEquiv hU d.basePoint Γ.1 Δ.1 h, θ, hθ,
    joinedPath_zero _ _ h, joinedPath_one _ _ h,
    interiorPhysicalTollCost_joined_with_junction d hU g hg m Γ.1 Δ.1 h⟩

end CircleDomainRigidity

end

end OAI
