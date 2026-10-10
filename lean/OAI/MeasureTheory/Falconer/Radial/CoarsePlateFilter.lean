import OAI.MeasureTheory.Falconer.Radial.HeavyPlateCells

namespace OAI

/-! # Decreasing coarse dyadic filters and their unnormalized fiber bounds -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def coarsePlateFilter (ρ : Measure (Space d)) (Q : DyadicCube d)
    (j₀ J : ℕ) (r m : ℕ → ℝ) : Set (Space d × Space d) :=
  (Q.carrier ×ˢ Q.carrier) \ ⋃ j ∈ Finset.Icc j₀ J, heavyPlateCellPairs ρ Q j (r j) (m j)

theorem measurableSet_coarsePlateFilter (ρ : Measure (Space d)) (Q : DyadicCube d)
    (j₀ J : ℕ) (r m : ℕ → ℝ) : MeasurableSet (coarsePlateFilter ρ Q j₀ J r m) := by
  apply (Q.measurable.prod Q.measurable).diff
  exact MeasurableSet.iUnion (fun j => MeasurableSet.iUnion (fun _ =>
    measurableSet_heavyPlateCellPairs ρ Q j (r j) (m j)))

theorem coarsePlateFilter_antitone (ρ : Measure (Space d)) (Q : DyadicCube d)
    (j₀ : ℕ) (r m : ℕ → ℝ) : Antitone (fun J => coarsePlateFilter ρ Q j₀ J r m) := by
  intro J K hJK p hp
  refine ⟨hp.1,?_⟩
  intro h
  apply hp.2
  obtain ⟨j,hj,hp'⟩ := mem_iUnion₂.mp h
  exact mem_iUnion₂.mpr ⟨j,Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hj).1,(Finset.mem_Icc.mp hj).2.trans hJK⟩,hp'⟩

theorem coarsePlateFilter_avoids (ρ : Measure (Space d)) (Q : DyadicCube d)
    (j₀ J : ℕ) (r m : ℕ → ℝ) {j : ℕ} (hj : j ∈ Finset.Icc j₀ J)
    {p : Space d × Space d} (hp : p ∈ coarsePlateFilter ρ Q j₀ J r m) :
    p ∉ heavyPlateCellPairs ρ Q j (r j) (m j) := by
  intro h
  exact hp.2 (mem_iUnion₂.mpr ⟨j,hj,h⟩)

theorem coarsePlateFilter_fiber_slab_bound (μ ρ : Measure (Space d))
    (Q : DyadicCube d) (j₀ J : ℕ) (r m : ℕ → ℝ)
    (hμ : μ ≤ ρ) {j : ℕ} (hj : j ∈ Finset.Icc j₀ J)
    (x w : Space d) (a : ℝ) (hw : ‖w‖ = 1)
    (hxw : |inner ℝ w x-a| ≤ r j) :
    μ {y | (x,y) ∈ coarsePlateFilter ρ Q j₀ J r m ∧
      |inner ℝ w y-a| ≤ r j} ≤ ENNReal.ofReal (m j) := by
  by_cases hh : ρ {y | |inner ℝ w y-a| ≤ r j} ≤ ENNReal.ofReal (m j)
  · exact (measure_mono (fun _ hy => hy.2)).trans ((hμ _).trans hh)
  · have hheavy := (not_le.mp hh).le
    have hempty : {y | (x,y) ∈ coarsePlateFilter ρ Q j₀ J r m ∧
        |inner ℝ w y-a| ≤ r j} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact coarsePlateFilter_avoids ρ Q j₀ J r m hj hy.1
        (heavyPlateCellPairs_of_points ρ Q j (r j) (m j) hy.1.1.1 hy.1.1.2
          hw hheavy hxw hy.2)
    rw [hempty,measure_empty]
    exact bot_le

end Falconer

end OAI
