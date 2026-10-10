import OAI.Geometry.Immersion.ClosedSurface.GridPartition

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGrid
open Set

lemma isOpen_cell (h R : ℝ) (a : Index) : IsOpen (cell h R a) :=
  (isOpen_lt ((continuous_fst.sub continuous_const).abs) continuous_const).inter
    (isOpen_lt ((continuous_snd.sub continuous_const).abs) continuous_const)


def coverRegion (s : Finset Index) (h : ℝ) : Set Base := ⋃ a ∈ s, cell h 1 a

lemma coverRegion_open (s : Finset Index) (h : ℝ) : IsOpen (coverRegion s h) :=
  isOpen_iUnion (fun a => isOpen_iUnion (fun _ => isOpen_cell h 1 a))

lemma coverRegion_covers (s : Finset Index) (h : ℝ) {x : Base}
    (hx : x ∈ coverRegion s h) : ∃ a ∈ s, x ∈ cell h 1 a := by
  simpa only [coverRegion,mem_iUnion,exists_prop] using hx




theorem compact_polynomial_square_partition {K U : Set Base}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ z₀ D : ℝ, ∃ C : ℕ → ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < D ∧ (∀ j, 1 ≤ C j) ∧
      ∀ z : ℝ, 0 < z → z ≤ z₀ → ∃ s : Finset Index,
        (s.card : ℝ) ≤ D/z^12 ∧ IsOpen (coverRegion s (z^6)) ∧
        K ⊆ coverRegion s (z^6) ∧ coverRegion s (z^6) ⊆ U ∧
        (∀ a ∈ s, z^6 • center a ∈ U ∧ tsupport (cutoff (z^6) a) ⊆ U) ∧
        (∀ a, ContDiffOn ℝ ∞ (normalizedCutoff s (z^6) a) (coverRegion s (z^6))) ∧
        (∀ a j x, x ∈ coverRegion s (z^6) →
          ‖iteratedFDeriv ℝ j (normalizedCutoff s (z^6) a) x‖ ≤ C j / z^(6*j)) ∧
        (∀ x ∈ coverRegion s (z^6), ∑ a ∈ s, (normalizedCutoff s (z^6) a x)^2 = 1) ∧
        (∀ a ∈ s, tsupport (normalizedCutoff s (z^6) a) ⊆ U) := by
  obtain ⟨z₀,D,hz₀,hz₀1,hD,hgrid⟩ := compact_subpatch_polynomial_grid hK hU hKU
  obtain ⟨C,hC,hderiv⟩ := normalizedCutoff_polynomial_derivatives
  refine ⟨z₀,D,C,hz₀,hz₀1,hD,hC,fun z hz hzsmall => ?_⟩
  obtain ⟨s,hcard,hcover,hsub⟩ := hgrid z hz hzsmall
  have hopen := coverRegion_open s (z^6)
  have hinner : K ⊆ coverRegion s (z^6) := by
    intro x hx
    simpa only [coverRegion,mem_iUnion,exists_prop] using hcover x hx
  have houter : coverRegion s (z^6) ⊆ U := by
    intro x hx
    obtain ⟨a,ha,hax⟩ := coverRegion_covers s (z^6) hx
    apply (hsub a ha).2
    apply subset_closure
    change cutoff (z^6) a x ≠ 0
    rw [cutoff_one_on_cell (pow_pos hz _) a hax]
    norm_num
  refine ⟨s,hcard,hopen,hinner,houter,hsub,?_,?_,?_,?_⟩
  · exact fun a => normalizedCutoff_smooth (pow_pos hz _) (fun x hx => coverRegion_covers s (z^6) hx) a
  · exact fun a j x hx => hderiv z hz s _ hopen (fun x hx => coverRegion_covers s (z^6) hx) a j x hx
  · intro x hx
    apply normalizedCutoff_squares
    exact zero_lt_one.trans_le (squareSum_ge_one (pow_pos hz _) (coverRegion_covers s (z^6) hx))
  · exact fun a ha => (normalizedCutoff_tsupport s (z^6) a).trans (hsub a ha).2

end ClosedSurfaceR4.PhaseGrid

end

end OAI
