import OAI.Analysis.LipschitzHilbert.Trees.SourceMaskedAmplitude

namespace OAI

/-! Exact assembly of the single-top source amplitudes into the shared
finite analytic family. All masses retain the original top index set. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable
variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Regrouping the actual packet family by assigned top introduces exactly
the eligible tops in the angular node. Empty packet fibers contribute zero. -/
theorem sourcePacketAmplitude_top_fibers (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (K : ℕ) (gap : ℕ → ℝ)
    (bands : Finset σ) (stop : ι → σ → ℕ) (value : ι → σ → E)
    (he : ∀ t ∈ tops, ∀ j ∈ bands, g.eligible cutoff (precision t) (stop t j))
    (phase : ℕ → ℂ) (a : ℝ) (z : X) (level : ℕ) (cell : ℤ) :
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap (tops ×ˢ bands)
      Prod.fst (fun p => stop p.1 p.2) (fun p => value p.1 p.2) phase a z level cell =
      ∑ t ∈ g.cellTops tops slope precision cutoff level cell,
        g.sourcePacketAmplitude tops slope precision cutoff weight K gap bands
          (fun _ => t) (stop t) (value t) phase a z level (g.index level (slope t)) := by
  simp only [sourcePacketAmplitude, packetAmplitude, packetSet, Finset.sum_filter,
    Finset.sum_product, cellTops]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hc : g.index level (slope t) = cell
  · by_cases hel : g.eligible cutoff (precision t) level
    · simp [hc, hel, sourcePacketBase]
    · have hnone (j : σ) (hj : j ∈ bands) : ¬level ≤ stop t j := by
        intro hle
        exact hel (g.eligible_of_le (hp t ht) hle (he t ht j hj))
      simp only [hc, hel, and_false, ite_false]
      apply Finset.sum_eq_zero
      intro j hj
      simp [hnone j hj]
  · simp [hc]

/-- The complete source family satisfies the linear node-mass envelope,
including arbitrary original-length restrictions and insignificant masks. -/
theorem sourcePacketAmplitude_node_envelope (grid : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t z, 0 < weight t z)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (M : ι → ℕ) (hM : ∀ t ∈ tops, grid.eligible cutoff (precision t) (M t))
    (hMmax : ∀ t ∈ tops, ∀ k, grid.eligible cutoff (precision t) k → k ≤ M t)
    (a Z : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hZ : 0 ≤ Z)
    (hz0 : ∀ t ∈ tops, ∀ j < M t, 0 ≤ (phase j).re)
    (hz : ∀ t ∈ tops, ∀ j < M t, ‖phase j‖ ≤ Z)
    {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    (P : ι → SourceLabeledLattice N κ Label Item)
    (coeff : ∀ t j (l : (P t).labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (stop : ι → Fin N → ℕ)
    (hstop : ∀ t ∈ tops, Antitone (stop t))
    (hmax : ∀ t ∈ tops, ∀ j, stop t j ≤ M t)
    (x y : ι → ℝ) (B C ε : ℝ) (hB : 0 ≤ B) (hC : 1 ≤ C) (hε : 0 ≤ ε)
    (z : X) (hweight : ∀ t ∈ tops, weight t z ≤ C)
    (hinterval : ∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N →
      ‖(P t).rawInterval (coeff t) jet l u (x t) (y t)‖ ≤ B*(weight t z)^8)
    (lower upper : ℕ) (q : ι → ℂ) (level : ℕ) (cell : ℤ)
    (hq : ∀ t ∈ grid.cellTops tops slope precision cutoff level cell, ‖q t‖ ≤ ε) :
    ‖grid.sourcePacketAmplitude tops slope precision cutoff weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (fun p => q p.1 • (P p.1).rawBand
        ((P p.1).restrictCoefficient (coeff p.1) lower upper) jet p.2 (x p.1) (y p.1))
      phase a z level cell‖ ≤
      (C^8*B*(1+(a+Z*K)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))*ε*C^3) *
        grid.mass tops slope precision cutoff weight level cell z := by
  let A := C^8*B*(1+(a+Z*K)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))
  have hlog : 0 ≤ Real.log (max 1 (∑ t ∈ tops, weight t z)) :=
    Real.log_nonneg (le_max_left _ _)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have he (t : ι) (ht : t ∈ tops) (j : Fin N) (_hj : j ∈ Finset.univ) :
      grid.eligible cutoff (precision t) (stop t j) :=
    grid.eligible_of_le (hp t ht) (hmax t ht j) (hM t ht)
  rw [grid.sourcePacketAmplitude_top_fibers tops slope precision cutoff weight hp K gap
    Finset.univ stop (fun t j => q t • (P t).rawBand
      ((P t).restrictCoefficient (coeff t) lower upper) jet j (x t) (y t))
    he phase a z level cell]
  apply grid.node_amplitude_fourth_envelope tops slope precision cutoff weight _
    level cell z (A*ε) C (mul_nonneg hA hε)
  · intro t _
    exact (hw t z).le
  · intro t ht
    exact hweight t ((grid.mem_cellTops _ _ _ _ _ _ _).mp ht).1
  · intro t ht
    obtain ⟨htt,hcell,hel⟩ := (grid.mem_cellTops _ _ _ _ _ _ _).mp ht
    have hb := grid.sourcePacketAmplitude_masked_restricted_envelope tops slope precision
      cutoff weight hp hw hK gap phase (M t) t htt (hM t htt) z a Z ha0 ha1 hZ
      (hz0 t htt) (hz t htt) (P t) (coeff t) jet (stop t) (hstop t htt) level
      (hMmax t htt level hel) (hmax t htt) (x t) (y t) B C hB hC (hweight t htt)
      (hinterval t htt) lower upper (q t)
    have hq' : ‖q t‖ ≤ ε := hq t ((grid.mem_cellTops _ _ _ _ _ _ _).mpr ⟨htt,hcell,hel⟩)
    calc
      _ ≤ A*‖q t‖*(weight t z)^4 := hb
      _ ≤ A*ε*(weight t z)^4 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hq' hA) (by positivity)

end LipschitzHilbert.AngularGrid

end

end OAI
