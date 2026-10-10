import OAI.MeasureTheory.Falconer.Estimates.ClassPairCandidate

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

noncomputable def actualClassDomain (Q : DyadicSquare) (μ : Measure Plane) (N B : ℕ) (T : List ℕ) : Set Plane :=
  leafUnion Q (classLeaves (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T)

noncomputable def actualClassMeasure (Q : DyadicSquare) (μ : Measure Plane) (N B : ℕ) (T : List ℕ) : Measure Plane :=
  normalizedClass Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T

theorem actualClassDomain_disjoint (Q : DyadicSquare) (hQ : 0 < Q.side) (μ : Measure Plane)
    (N B : ℕ) {T U : List ℕ} (hTU : T ≠ U) :
    Disjoint (actualClassDomain Q μ N B T) (actualClassDomain Q μ N B U) := by
  apply leafUnion_disjoint Q hQ (N := N)
  · intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  · intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  · exact classLeaves_disjoint _ _ hTU

theorem measurableSet_actualClassDomain (Q : DyadicSquare) (μ : Measure Plane) (N B : ℕ) (T : List ℕ) :
    MeasurableSet (actualClassDomain Q μ N B T) := leafUnion_measurable _ _

noncomputable def retainedPairs (Q : DyadicSquare) (μ ν : Measure Plane) (N B₁ B₂ : ℕ) (lam : ℝ) :
    Finset (List ℕ × List ℕ) :=
  (retainedClassLabels Q μ N B₁ (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))).product
    (retainedClassLabels Q ν N B₂ (ENNReal.ofReal (((2:ℝ)^N)^(-lam))))

noncomputable def retainedPairMask (Q : DyadicSquare) (μ ν : Measure Plane)
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ)
    (a : List ℕ × List ℕ) (z : Plane × Plane) : ℝ≥0∞ := by
  classical
  exact if z.1 ∈ actualClassDomain Q μ N B₁ a.1 ∧ z.2 ∈ actualClassDomain Q ν N B₂ a.2 then
    classPairMask Q (actualClassMeasure Q μ N B₁ a.1) (actualClassMeasure Q ν N B₂ a.2)
      (m₁ a.1) (m₂ a.2) N lam sig kap β z else 0

noncomputable def restoredShellMask (Q : DyadicSquare) (μ ν : Measure Plane)
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ) (z : Plane × Plane) : ℝ≥0∞ :=
  (retainedPairs Q μ ν N B₁ B₂ lam).sup
    (fun a => retainedPairMask Q μ ν m₁ m₂ N B₁ B₂ lam sig kap β a z)

@[fun_prop] theorem measurable_retainedPairMask (Q : DyadicSquare) (μ ν : Measure Plane)
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ) (a : List ℕ × List ℕ) :
    Measurable (retainedPairMask Q μ ν m₁ m₂ N B₁ B₂ lam sig kap β a) := by
  classical
  apply Measurable.ite
    (((measurableSet_actualClassDomain _ _ _ _ _).preimage measurable_fst).inter
      ((measurableSet_actualClassDomain _ _ _ _ _).preimage measurable_snd))
  · exact measurable_classPairMask _ _ _ _ _ _ _ _ _ _
  · exact measurable_const

@[fun_prop] theorem measurable_restoredShellMask (Q : DyadicSquare) (μ ν : Measure Plane)
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ) :
    Measurable (restoredShellMask Q μ ν m₁ m₂ N B₁ B₂ lam sig kap β) := by
  classical
  have hs (S : Finset (List ℕ × List ℕ)) : Measurable (fun z : Plane × Plane =>
      S.sup (fun a => retainedPairMask Q μ ν m₁ m₂ N B₁ B₂ lam sig kap β a z)) := by
    induction S using Finset.induction_on with
    | empty => simpa only [Finset.sup_empty] using (measurable_const : Measurable (fun _ : Plane × Plane => (⊥:ENNReal)))
    | @insert pair pairs _ measurable_masks =>
      simp only [Finset.sup_insert]
      exact (measurable_retainedPairMask Q μ ν m₁ m₂ N B₁ B₂ lam sig kap β pair).sup measurable_masks
  exact hs _

theorem restoredShellMask_le_one (Q : DyadicSquare) (hQ : 0 < Q.side) (μ ν : Measure Plane)
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ) (z : Plane × Plane) :
    restoredShellMask Q μ ν m₁ m₂ N B₁ B₂ lam sig kap β z ≤ 1 := by
  apply Finset.sup_le
  intro a _
  unfold retainedPairMask
  split_ifs
  · exact classPairMask_le_one Q hQ _ _ _ _ _ _ _ _ _ _
  · exact zero_le_one

theorem restoredShellMask_on_pair (Q : DyadicSquare) (hQ : 0 < Q.side) (μ ν : Measure Plane)
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ)
    {a : List ℕ × List ℕ} (ha : a ∈ retainedPairs Q μ ν N B₁ B₂ lam) {z : Plane × Plane}
    (hx : z.1 ∈ actualClassDomain Q μ N B₁ a.1) (hy : z.2 ∈ actualClassDomain Q ν N B₂ a.2) :
    restoredShellMask Q μ ν m₁ m₂ N B₁ B₂ lam sig kap β z =
      classPairMask Q (actualClassMeasure Q μ N B₁ a.1) (actualClassMeasure Q ν N B₂ a.2)
        (m₁ a.1) (m₂ a.2) N lam sig kap β z := by
  classical
  have he : retainedPairMask Q μ ν m₁ m₂ N B₁ B₂ lam sig kap β a z =
      classPairMask Q (actualClassMeasure Q μ N B₁ a.1) (actualClassMeasure Q ν N B₂ a.2)
        (m₁ a.1) (m₂ a.2) N lam sig kap β z := by
    rw [retainedPairMask,ite_eq_left ⟨hx,hy⟩]
  apply le_antisymm
  · apply Finset.sup_le
    intro b _
    unfold retainedPairMask
    split_ifs with hb
    · have h₁ : b.1 = a.1 := by
        by_contra hn
        exact Set.disjoint_left.mp (actualClassDomain_disjoint Q hQ μ N B₁ hn) hb.1 hx
      have h₂ : b.2 = a.2 := by
        by_contra hn
        exact Set.disjoint_left.mp (actualClassDomain_disjoint Q hQ ν N B₂ hn) hb.2 hy
      simp only [h₁,h₂]
      exact le_rfl
    · exact bot_le
  · rw [← he]
    exact Finset.le_sup (f := fun b => retainedPairMask Q μ ν m₁ m₂ N B₁ B₂ lam sig kap β b z) ha

theorem restoredShellMask_discarded (Q : DyadicSquare) (μ ν : Measure Plane)
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ) {z : Plane × Plane}
    (hz : z.1 ∉ retainedClassUnion Q μ N B₁ (ENNReal.ofReal (((2:ℝ)^N)^(-lam))) ∨
      z.2 ∉ retainedClassUnion Q ν N B₂ (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))) :
    restoredShellMask Q μ ν m₁ m₂ N B₁ B₂ lam sig kap β z = 0 := by
  classical
  apply le_antisymm _ bot_le
  apply Finset.sup_le
  intro a ha
  have ha := Finset.mem_product.mp ha
  unfold retainedPairMask
  split_ifs with h
  · exfalso
    rcases hz with hz | hz
    · exact hz (mem_iUnion₂.mpr ⟨a.1,ha.1,h.1⟩)
    · exact hz (mem_iUnion₂.mpr ⟨a.2,ha.2,h.2⟩)
  · exact le_rfl

end PlanarFalconer

end OAI
