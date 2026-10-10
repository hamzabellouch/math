import OAI.Probability.InvariantIsing.Arrays.OverlapPathCompact

namespace OAI

/-! Tied overlap levels remain tied in an almost-everywhere limit. A
monotone factor through the overlap is then constructed explicitly;
no invertibility or absence of plateaus is assumed. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

private def cavityFiberValues (p B : OverlapPath) (D : Set ℝ) (z : ℝ) : Set ℝ :=
  insert 0 (B.val '' {s | s ∈ D ∧ p s ≤ z})

private lemma cavityFiberValues_bdd (p B : OverlapPath) (D : Set ℝ) (z : ℝ) :
    BddAbove (cavityFiberValues p B D z) := by
  refine ⟨1, ?_⟩
  rintro y (rfl | ⟨s, _, rfl⟩)
  · norm_num
  · exact B.le_one s

private lemma cavityFiberFactor_mono (p B : OverlapPath) (D : Set ℝ) :
    Monotone (fun z => sSup (cavityFiberValues p B D z)) := by
  intro x y hxy
  apply csSup_le_csSup (cavityFiberValues_bdd p B D y) (insert_nonempty _ _)
  rintro z (rfl | ⟨s, hs, rfl⟩)
  · exact mem_insert _ _
  · exact mem_insert_of_mem _ ⟨s, ⟨hs.1, hs.2.trans hxy⟩, rfl⟩

private lemma cavityFiberFactor_bounds (p B : OverlapPath) (D : Set ℝ) (z : ℝ) :
    0 ≤ sSup (cavityFiberValues p B D z) ∧ sSup (cavityFiberValues p B D z) ≤ 1 := by
  constructor
  · exact le_csSup (cavityFiberValues_bdd p B D z) (mem_insert _ _)
  · apply csSup_le (insert_nonempty _ _)
    rintro y (rfl | ⟨s, _, rfl⟩)
    · norm_num
    · exact B.le_one s

private lemma cavityFiberFactor_eq (p B : OverlapPath) (D : Set ℝ)
    (hD : ∀ x ∈ D, ∀ y ∈ D, p x = p y → B x = B y)
    {x : ℝ} (hx : x ∈ D) : sSup (cavityFiberValues p B D (p x)) = B x := by
  apply le_antisymm
  · apply csSup_le (insert_nonempty _ _)
    rintro y (rfl | ⟨s, hs, rfl⟩)
    · exact B.nonneg x
    · rcases le_or_gt s x with h | h
      · exact B.monotone h
      · have he : p s = p x := le_antisymm hs.2 (p.monotone h.le)
        exact (hD s hs.1 x hx he).le
  · exact le_csSup (cavityFiberValues_bdd p B D (p x))
      (mem_insert_of_mem _ ⟨x, ⟨hx, le_rfl⟩, rfl⟩)

/-- An a.e. limit of functions constant on every overlap fiber is still
a measurable function of that overlap, even on positive-mass plateaus. -/
theorem cavity_limit_factors_through_overlap_on (p B : OverlapPath) (Bseq : ℕ → ℝ → ℝ)
    (D : Set ℝ) (hDae : ∀ᵐ s ∂pathMeasure, s ∈ D)
    (htied : ∀ n x, x ∈ D → ∀ y, y ∈ D → p x = p y → Bseq n x = Bseq n y)
    (hlim : ∀ᵐ s ∂pathMeasure, Tendsto (fun n => Bseq n s) atTop (𝓝 (B s))) :
    ∃ g : ℝ → ℝ, Monotone g ∧ (∀ z, 0 ≤ g z ∧ g z ≤ 1) ∧
      B.val =ᵐ[pathMeasure] fun s => g (p s) := by
  let E := D ∩ {s | Tendsto (fun n => Bseq n s) atTop (𝓝 (B s))}
  have hE : ∀ x ∈ E, ∀ y ∈ E, p x = p y → B x = B y := by
    intro x hx y hy hxy
    have he : (fun n => Bseq n x) = (fun n => Bseq n y) :=
      funext (fun n => htied n x hx.1 y hy.1 hxy)
    exact tendsto_nhds_unique hx.2 (he ▸ hy.2)
  refine ⟨fun z => sSup (cavityFiberValues p B E z),
    cavityFiberFactor_mono p B E, cavityFiberFactor_bounds p B E, ?_⟩
  filter_upwards [hDae, hlim] with s hs hls
  exact (cavityFiberFactor_eq p B E hE ⟨hs, hls⟩).symm

theorem cavity_limit_factors_through_overlap (p B : OverlapPath) (Bseq : ℕ → ℝ → ℝ)
    (htied : ∀ n x y, p x = p y → Bseq n x = Bseq n y)
    (hlim : ∀ᵐ s ∂pathMeasure, Tendsto (fun n => Bseq n s) atTop (𝓝 (B s))) :
    ∃ g : ℝ → ℝ, Monotone g ∧ (∀ z, 0 ≤ g z ∧ g z ≤ 1) ∧
      B.val =ᵐ[pathMeasure] fun s => g (p s) :=
  cavity_limit_factors_through_overlap_on p B Bseq Set.univ
    (ae_of_all _ fun _ => Set.mem_univ _) (fun n x _ y _ => htied n x y) hlim

end InvariantIsing

end

end OAI
