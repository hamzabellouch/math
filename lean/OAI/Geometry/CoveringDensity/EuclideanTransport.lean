import OAI.Geometry.CoveringDensity.Model
import OAI.Geometry.LatticeCovering.Main

namespace OAI

/-! The coordinate map is a continuous linear equivalence and preserves volume.
The Euclidean norm and the coordinate supremum norm need not agree. -/
noncomputable section
open Set MeasureTheory
open scoped Pointwise ENNReal
namespace CoveringOrder

theorem euclidean_lattice_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∀ K : Set (EuclideanSpace ℝ (Fin n)), TranslativeCovering.ConvexBody K →
        ∃ (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (_ : DiscreteTopology L),
          IsZLattice ℝ L ∧ (∀ y, ∃ l : L, y - l.val ∈ K) ∧
            volume K / ENNReal.ofReal (ZLattice.covolume L volume) ≤
              ENNReal.ofReal (C * (n : ℝ) * Real.log n) := by
  obtain ⟨C, hC, hupper⟩ := SingleLatticeCovering.single_lattice_covering
  refine ⟨C, hC, ?_⟩
  intro n hn K hK
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toContinuousLinearEquiv
  have hp : MeasurePreserving e volume volume := PiLp.volume_preserving_ofLp (Fin n)
  have hc : IsCompact (e '' K) := hK.1.image e.continuous
  have hbody : SingleLatticeCovering.IsConvexBody (e '' K) := by
    refine ⟨hc, hK.2.1.linear_image e.toLinearMap, ?_⟩
    change (interior (e.toHomeomorph '' K)).Nonempty
    rw [← e.toHomeomorph.image_interior]
    exact hK.2.2.image e
  have hvol : volume (e '' K) = volume K := by
    have hm := hp.measure_preimage hc.measurableSet.nullMeasurableSet
    rw [Set.preimage_image_eq _ e.injective] at hm
    exact hm.symm
  obtain ⟨L, hd, hf, hcover, hbound⟩ := hupper n hn (e '' K) hbody
  let : DiscreteTopology L := hd
  let : IsZLattice ℝ L := hf
  let Λ := ZLattice.comap ℝ L e.toLinearMap
  have hcov : ZLattice.covolume Λ volume = ZLattice.covolume L volume :=
    ZLattice.covolume_comap L volume volume hp
  refine ⟨Λ, inferInstance, inferInstance, ?_, ?_⟩
  · intro y
    have hy : e y ∈ e '' K + (L : Set (Fin n → ℝ)) := by
      rw [hcover]
      trivial
    obtain ⟨k, ⟨x, hx, rfl⟩, l, hl, heq⟩ := hy
    have hl' : e.symm l ∈ Λ := by
      change e (e.symm l) ∈ L
      rw [e.apply_symm_apply]
      exact hl
    refine ⟨⟨e.symm l, hl'⟩, ?_⟩
    have hxy : x + e.symm l = y := by
      apply e.injective
      simpa only [map_add, e.apply_symm_apply] using heq
    have hdiff : y - e.symm l = x := by rw [← hxy]; abel
    simpa only [hdiff] using hx
  · rw [hvol] at hbound
    have hpos : 0 < ZLattice.covolume L volume := ZLattice.covolume_pos L volume
    rw [hcov]
    calc
      volume K / ENNReal.ofReal (ZLattice.covolume L volume) =
          ENNReal.ofReal ((volume K).toReal / ZLattice.covolume L volume) := by
            rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_toReal hK.1.measure_ne_top]
      _ ≤ ENNReal.ofReal (C * (n : ℝ) * Real.log n) := ENNReal.ofReal_le_ofReal hbound

end CoveringOrder

end

end OAI
