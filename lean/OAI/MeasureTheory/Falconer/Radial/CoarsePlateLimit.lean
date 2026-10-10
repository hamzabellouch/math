import OAI.MeasureTheory.Falconer.Radial.CoarsePlateFilter

namespace OAI

/-! # Exact limiting set of the decreasing coarse plate filters -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem iInter_coarsePlateFilter {d : ℕ} (ρ : Measure (Space d)) (Q : DyadicCube d)
    (j₀ : ℕ) (r m : ℕ → ℝ) :
    (⋂ J : ℕ, coarsePlateFilter ρ Q j₀ J r m) =
      (Q.carrier ×ˢ Q.carrier) \ ⋃ n : ℕ, heavyPlateCellPairs ρ Q (j₀+n) (r (j₀+n)) (m (j₀+n)) := by
  ext xy
  constructor
  · intro h
    have hall := mem_iInter.mp h
    refine ⟨(hall 0).1,?_⟩
    intro hex
    obtain ⟨n,hn⟩ := mem_iUnion.mp hex
    exact (hall (j₀+n)).2 (mem_iUnion₂.mpr
      ⟨j₀+n,Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩,hn⟩)
  · rintro ⟨hroot,hgood⟩
    apply mem_iInter.mpr
    intro J
    refine ⟨hroot,?_⟩
    intro hex
    obtain ⟨j,hj,hxy⟩ := mem_iUnion₂.mp hex
    have hj₀ := (Finset.mem_Icc.mp hj).1
    apply hgood
    exact mem_iUnion.mpr ⟨j-j₀,by simpa only [Nat.add_sub_of_le hj₀] using hxy⟩

theorem coarsePlateFilter_limit_pos {d : ℕ} (ξ : Measure (Space d × Space d))
    (ρ : Measure (Space d)) (Q : DyadicCube d) (j₀ : ℕ) (r m : ℕ → ℝ)
    (hroot : ξ (Q.carrier ×ˢ Q.carrier) = 1)
    (hloss : ξ (⋃ n : ℕ, heavyPlateCellPairs ρ Q (j₀+n) (r (j₀+n)) (m (j₀+n))) < 1) :
    0 < ξ (⋂ J : ℕ, coarsePlateFilter ρ Q j₀ J r m) := by
  rw [iInter_coarsePlateFilter]
  apply pos_iff_ne_zero.mpr
  intro hz
  have hbound := (measure_le_inter_add_sdiff ξ (Q.carrier ×ˢ Q.carrier)
    (⋃ n : ℕ, heavyPlateCellPairs ρ Q (j₀+n) (r (j₀+n)) (m (j₀+n)))).trans
    (add_le_add (measure_mono inter_subset_right) le_rfl)
  rw [hz,add_zero,hroot] at hbound
  exact (not_le_of_gt hloss) hbound

end Falconer

end OAI
