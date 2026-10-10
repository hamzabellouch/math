import OAI.GroupTheory.Thompson.StandardPL
import OAI.GroupTheory.Thompson.SortedSubdivision

namespace OAI

/-!
# Composition by a finite common subdivision

For `h ∘ g`, take every knot of `g` and the inverse image under `g` of every
knot of `h`.  Consecutive points of their sorted union lie in one piece of
`g` and map into one piece of `h`.  The two genuine affine equalities then
compose, adding their integer slope exponents.
-/

namespace ThompsonNonamenability
namespace DyadicPLWitness

/-- Composition of actual finite dyadic PL witnesses, using the sorted union
of the inner breakpoints and pulled-back outer breakpoints. -/
noncomputable def mul {h g : IntervalHomeomorph}
    (wh : DyadicPLWitness h) (wg : DyadicPLWitness g)
    (_hhmono : StrictMono h) (hgmono : StrictMono g) : DyadicPLWitness (h * g) := by
  classical
  let s : Finset UnitInterval := Finset.univ.image wg.knots ∪
    Finset.univ.image (fun j => g⁻¹ (wh.knots j))
  have hgmem (j : Fin (wg.pieceCount + 1)) : wg.knots j ∈ s := by
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  have hhmem (j : Fin (wh.pieceCount + 1)) : g⁻¹ (wh.knots j) ∈ s := by
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  have hs0 : unitIntervalZero ∈ s := by simpa only [wg.first] using hgmem 0
  have hs1 : unitIntervalOne ∈ s := by
    simpa only [wg.last] using hgmem (Fin.last wg.pieceCount)
  let r := SortedSubdivision.ofFinset s hs0 hs1
  have hgPieces (i : Fin r.pieceCount) : ∃ j : Fin wg.pieceCount,
      wg.knots j.castSucc ≤ r.knots i.castSucc ∧
        r.knots i.succ ≤ wg.knots j.succ :=
    r.adjacent_contained wg.knots wg.strictMono_knots wg.cover hgmem i
  have hhcover (x : UnitInterval) : ∃ j : Fin wh.pieceCount,
      g⁻¹ (wh.knots j.castSucc) ≤ x ∧ x ≤ g⁻¹ (wh.knots j.succ) := by
    obtain ⟨j, hj0, hj1⟩ := wh.cover (g x)
    refine ⟨j, ?_, ?_⟩
    · simpa only [IntervalHomeomorph.inv_apply_apply] using
        (IntervalHomeomorph.strictMono_inv hgmono).monotone hj0
    · simpa only [IntervalHomeomorph.inv_apply_apply] using
        (IntervalHomeomorph.strictMono_inv hgmono).monotone hj1
  have hhPieces (i : Fin r.pieceCount) : ∃ j : Fin wh.pieceCount,
      g⁻¹ (wh.knots j.castSucc) ≤ r.knots i.castSucc ∧
        r.knots i.succ ≤ g⁻¹ (wh.knots j.succ) :=
    r.adjacent_contained (fun j => g⁻¹ (wh.knots j))
      ((IntervalHomeomorph.strictMono_inv hgmono).comp wh.strictMono_knots)
      hhcover hhmem i
  let gi (i : Fin r.pieceCount) := Classical.choose (hgPieces i)
  let hi (i : Fin r.pieceCount) := Classical.choose (hhPieces i)
  have hgi (i : Fin r.pieceCount) :
      wg.knots (gi i).castSucc ≤ r.knots i.castSucc ∧
        r.knots i.succ ≤ wg.knots (gi i).succ := Classical.choose_spec (hgPieces i)
  have hhi (i : Fin r.pieceCount) :
      g⁻¹ (wh.knots (hi i).castSucc) ≤ r.knots i.castSucc ∧
        r.knots i.succ ≤ g⁻¹ (wh.knots (hi i).succ) :=
    Classical.choose_spec (hhPieces i)
  refine {
    pieceCount := r.pieceCount
    positive := r.positive
    knots := r.knots
    strictMono_knots := r.strictMono_knots
    first := r.first
    last := r.last
    dyadic := ?_
    cover := r.cover
    exponent := fun i => wh.exponent (hi i) + wg.exponent (gi i)
    affine := ?_ }
  · intro i
    have hmem := r.knots_mem i
    rcases Finset.mem_union.mp hmem with hmem | hmem
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
      rw [← hj]
      exact wg.dyadic j
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
      rw [← hj]
      exact (wg.inverse hgmono).map_dyadic
        (IntervalHomeomorph.strictMono_inv hgmono) (wh.dyadic j)
  · intro i x hx0 hx1
    have hab : r.knots i.castSucc ≤ r.knots i.succ :=
      (r.strictMono_knots (Fin.castSucc_lt_succ_iff.mpr le_rfl)).le
    have hga0 : wh.knots (hi i).castSucc ≤ g (r.knots i.castSucc) := by
      simpa only [IntervalHomeomorph.apply_inv_apply] using
        hgmono.monotone (hhi i).1
    have hgb1 : g (r.knots i.succ) ≤ wh.knots (hi i).succ := by
      simpa only [IntervalHomeomorph.apply_inv_apply] using
        hgmono.monotone (hhi i).2
    have hgx := wg.affine (gi i) x ((hgi i).1.trans hx0) (hx1.trans (hgi i).2)
    have hga := wg.affine (gi i) (r.knots i.castSucc)
      (hgi i).1 (hab.trans (hgi i).2)
    have hhgx := wh.affine (hi i) (g x)
      (hga0.trans (hgmono.monotone hx0)) ((hgmono.monotone hx1).trans hgb1)
    have hhga := wh.affine (hi i) (g (r.knots i.castSucc))
      hga0 ((hgmono.monotone hab).trans hgb1)
    simp only [IntervalHomeomorph.mul_apply]
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [hhgx, hhga, hgx, hga]
    ring

end DyadicPLWitness

theorem HasDyadicPLPieces.mul {h g : IntervalHomeomorph}
    (hh : HasDyadicPLPieces h) (hg : HasDyadicPLPieces g)
    (hhmono : StrictMono h) (hgmono : StrictMono g) : HasDyadicPLPieces (h * g) := by
  obtain ⟨wh⟩ := hh
  obtain ⟨wg⟩ := hg
  exact ⟨wh.mul wg hhmono hgmono⟩

end ThompsonNonamenability

end OAI
