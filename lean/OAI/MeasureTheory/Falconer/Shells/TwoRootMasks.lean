import OAI.MeasureTheory.Falconer.Shells.RestoredMaskCoverage

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

noncomputable def twoRootPairMask (Q₀ Q₁ : DyadicSquare) (ρ ν : Measure Plane)
    (m₀ m₁ : ℝ → ℝ) (N : ℕ) (lam sig kap β : ℝ) (z : Plane × Plane) : ENNReal :=
  let c := outerEntry m₀ m₁ N β
  ENNReal.ofReal (outerEndpointMask Q₀ ρ m₀ N lam sig kap c z.1 (sourceRadialUnit z.1 z.2) *
    outerEndpointMask Q₁ ν m₁ N lam sig kap c z.2 (sourceRadialUnit z.1 z.2))

@[fun_prop] theorem measurable_twoRootPairMask (Q₀ Q₁ : DyadicSquare) (ρ ν : Measure Plane)
    (m₀ m₁ : ℝ → ℝ) (N : ℕ) (lam sig kap β : ℝ) :
    Measurable (twoRootPairMask Q₀ Q₁ ρ ν m₀ m₁ N lam sig kap β) := by
  let entry := outerEntry m₀ m₁ N β
  let leftMask : Plane × UnitCircle → ℝ := fun endpoint =>
    outerEndpointMask Q₀ ρ m₀ N lam sig kap entry endpoint.1 endpoint.2
  let rightMask : Plane × UnitCircle → ℝ := fun endpoint =>
    outerEndpointMask Q₁ ν m₁ N lam sig kap entry endpoint.1 endpoint.2
  have hleft : Measurable leftMask :=
    measurable_outerEndpointMask Q₀ ρ m₀ N lam sig kap entry
  have hright : Measurable rightMask :=
    measurable_outerEndpointMask Q₁ ν m₁ N lam sig kap entry
  change Measurable (fun point : Plane × Plane => ENNReal.ofReal
    (leftMask (point.1, sourceRadialUnit point.1 point.2) *
      rightMask (point.2, sourceRadialUnit point.1 point.2)))
  exact ((hleft.comp (measurable_fst.prodMk measurable_sourceRadialUnit_joint)).mul
    (hright.comp (measurable_snd.prodMk measurable_sourceRadialUnit_joint))).ennreal_ofReal

theorem twoRootPairMask_le_one (Q₀ Q₁ : DyadicSquare) (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side)
    (ρ ν : Measure Plane) (m₀ m₁ : ℝ → ℝ) (N : ℕ) (lam sig kap β : ℝ) (z : Plane × Plane) :
    twoRootPairMask Q₀ Q₁ ρ ν m₀ m₁ N lam sig kap β z ≤ 1 := by
  apply ENNReal.ofReal_le_one.mpr
  have h₀ := outerEndpointMask_bounds Q₀ hQ₀ ρ m₀ N lam sig kap (outerEntry m₀ m₁ N β) z.1 (sourceRadialUnit z.1 z.2)
  have h₁ := outerEndpointMask_bounds Q₁ hQ₁ ν m₁ N lam sig kap (outerEntry m₀ m₁ N β) z.2 (sourceRadialUnit z.1 z.2)
  nlinarith

noncomputable def retainedRootPairs (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (N B₀ B₁ : ℕ) (lam : ℝ) : Finset (List ℕ × List ℕ) :=
  (retainedClassLabels Q₀ μ N B₀ (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))).product
    (retainedClassLabels Q₁ ν N B₁ (ENNReal.ofReal (((2:ℝ)^N)^(-lam))))

noncomputable def twoRootRetainedMask (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (m₀ m₁ : List ℕ → ℝ → ℝ) (N B₀ B₁ : ℕ) (lam sig kap β : ℝ)
    (a : List ℕ × List ℕ) (z : Plane × Plane) : ENNReal :=
  (actualClassDomain Q₀ μ N B₀ a.1 ×ˢ actualClassDomain Q₁ ν N B₁ a.2).indicator
    (twoRootPairMask Q₀ Q₁ (actualClassMeasure Q₀ μ N B₀ a.1)
      (actualClassMeasure Q₁ ν N B₁ a.2) (m₀ a.1) (m₁ a.2) N lam sig kap β) z

noncomputable def restoredTwoRootMask (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (m₀ m₁ : List ℕ → ℝ → ℝ) (N B₀ B₁ : ℕ) (lam sig kap β : ℝ) (z : Plane × Plane) : ENNReal :=
  ∑ a ∈ retainedRootPairs Q₀ Q₁ μ ν N B₀ B₁ lam,
    twoRootRetainedMask Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β a z

@[fun_prop] theorem measurable_twoRootRetainedMask (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (m₀ m₁ : List ℕ → ℝ → ℝ) (N B₀ B₁ : ℕ) (lam sig kap β : ℝ) (a : List ℕ × List ℕ) :
    Measurable (twoRootRetainedMask Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β a) :=
  (measurable_twoRootPairMask ..).indicator
    ((measurableSet_actualClassDomain ..).prod (measurableSet_actualClassDomain ..))

@[fun_prop] theorem measurable_restoredTwoRootMask (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (m₀ m₁ : List ℕ → ℝ → ℝ) (N B₀ B₁ : ℕ) (lam sig kap β : ℝ) :
    Measurable (restoredTwoRootMask Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β) :=
  Finset.measurable_sum _ (fun _ _ => measurable_twoRootRetainedMask ..)

theorem twoRoot_domain_unique (Q₀ Q₁ : DyadicSquare) (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side)
    (μ ν : Measure Plane) (N B₀ B₁ : ℕ) {a b : List ℕ × List ℕ} {z : Plane × Plane}
    (ha : z ∈ actualClassDomain Q₀ μ N B₀ a.1 ×ˢ actualClassDomain Q₁ ν N B₁ a.2)
    (hb : z ∈ actualClassDomain Q₀ μ N B₀ b.1 ×ˢ actualClassDomain Q₁ ν N B₁ b.2) : a = b := by
  apply Prod.ext
  · by_contra hn
    exact Set.disjoint_left.mp (actualClassDomain_disjoint Q₀ hQ₀ μ N B₀ hn) ha.1 hb.1
  · by_contra hn
    exact Set.disjoint_left.mp (actualClassDomain_disjoint Q₁ hQ₁ ν N B₁ hn) ha.2 hb.2

theorem restoredTwoRootMask_on_pair (Q₀ Q₁ : DyadicSquare) (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side)
    (μ ν : Measure Plane) (m₀ m₁ : List ℕ → ℝ → ℝ) (N B₀ B₁ : ℕ) (lam sig kap β : ℝ)
    {a : List ℕ × List ℕ} (ha : a ∈ retainedRootPairs Q₀ Q₁ μ ν N B₀ B₁ lam) {z : Plane × Plane}
    (hz : z ∈ actualClassDomain Q₀ μ N B₀ a.1 ×ˢ actualClassDomain Q₁ ν N B₁ a.2) :
    restoredTwoRootMask Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β z =
      twoRootPairMask Q₀ Q₁ (actualClassMeasure Q₀ μ N B₀ a.1)
        (actualClassMeasure Q₁ ν N B₁ a.2) (m₀ a.1) (m₁ a.2) N lam sig kap β z := by
  classical
  rw [restoredTwoRootMask, Finset.sum_eq_single a]
  · exact Set.indicator_of_mem hz _
  · intro b _ hba
    apply Set.indicator_of_notMem
    exact fun hb => hba (twoRoot_domain_unique Q₀ Q₁ hQ₀ hQ₁ μ ν N B₀ B₁ hb hz)
  · exact fun hn => (hn ha).elim

theorem restoredTwoRootMask_discarded (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (m₀ m₁ : List ℕ → ℝ → ℝ) (N B₀ B₁ : ℕ) (lam sig kap β : ℝ) {z : Plane × Plane}
    (hz : z.1 ∉ retainedClassUnion Q₀ μ N B₀ (ENNReal.ofReal (((2:ℝ)^N)^(-lam))) ∨
      z.2 ∉ retainedClassUnion Q₁ ν N B₁ (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))) :
    restoredTwoRootMask Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β z = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  have ha := Finset.mem_product.mp ha
  apply Set.indicator_of_notMem
  intro h
  rcases hz with hz | hz
  · exact hz (mem_iUnion₂.mpr ⟨a.1,ha.1,h.1⟩)
  · exact hz (mem_iUnion₂.mpr ⟨a.2,ha.2,h.2⟩)

theorem restoredTwoRootMask_le_one (Q₀ Q₁ : DyadicSquare) (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side)
    (μ ν : Measure Plane) (m₀ m₁ : List ℕ → ℝ → ℝ) (N B₀ B₁ : ℕ) (lam sig kap β : ℝ) (z : Plane × Plane) :
    restoredTwoRootMask Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β z ≤ 1 := by
  classical
  by_cases hx : z.1 ∈ retainedClassUnion Q₀ μ N B₀ (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
  · by_cases hy : z.2 ∈ retainedClassUnion Q₁ ν N B₁ (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
    · obtain ⟨T,hT,hx⟩ := mem_iUnion₂.mp hx
      obtain ⟨U,hU,hy⟩ := mem_iUnion₂.mp hy
      rw [restoredTwoRootMask_on_pair Q₀ Q₁ hQ₀ hQ₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β
        (a := (T,U)) (Finset.mem_product.mpr ⟨hT,hU⟩) ⟨hx,hy⟩]
      exact twoRootPairMask_le_one Q₀ Q₁ hQ₀ hQ₁ ..
    · rw [restoredTwoRootMask_discarded Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β (Or.inr hy)]
      exact zero_le_one
  · rw [restoredTwoRootMask_discarded Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β (Or.inl hx)]
    exact zero_le_one

theorem restoredTwoRootMask_empty (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (m₀ m₁ : List ℕ → ℝ → ℝ) (N B₀ B₁ : ℕ) (lam sig kap β : ℝ)
    (h : retainedRootPairs Q₀ Q₁ μ ν N B₀ B₁ lam = ∅) :
    restoredTwoRootMask Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β = 0 := by
  funext z
  simp [restoredTwoRootMask,h]

end PlanarFalconer

end OAI
