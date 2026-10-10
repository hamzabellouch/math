import OAI.Analysis.LipschitzHilbert.Estimates.StoppingScaleIntervals
import OAI.Analysis.LipschitzHilbert.Estimates.SegmentAmplitudes
import OAI.Analysis.LipschitzHilbert.Phase.AngularSourceWeight

namespace OAI

/-! Interval concentration controls the actual source sums weighted by
angular stopping levels. The finite regrouping and summation by parts
introduce no factor depending on the number of scales. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem stopping_weighted_sum_eq {N : ℕ} (stop : Fin N → ℕ) (f : Fin N → E)
    (w : ℕ → ℂ) (start M : ℕ) (hstop : ∀ j, stop j ≤ M) :
    (∑ j ∈ Finset.univ.filter (fun j => start ≤ stop j), w (stop j) • f j) =
      ∑ k ∈ Finset.Ico start (M+1), w k •
        ∑ j ∈ Finset.univ.filter (fun j => stop j = k), f j := by
  have heq : (∑ k ∈ Finset.Ico start (M+1), w k •
      ∑ j ∈ Finset.univ.filter (fun j => stop j = k), f j) =
      ∑ k ∈ Finset.Ico start (M+1),
        ∑ j ∈ Finset.univ.filter (fun j => stop j = k), w (stop j) • f j := by
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [(Finset.mem_filter.mp hj).2]
  rw [heq, sum_stopping_fibers]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨h, by have := hstop j; omega⟩, And.left⟩

namespace SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem angular_stopping_amplitude_bound (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (stop : Fin N → ℕ) (hstop : Antitone stop)
    (start M K : ℕ) (hstart : start ≤ M) (hmax : ∀ j, stop j ≤ M)
    (n m : ℕ → ℝ) (phase : ℕ → ℂ) (a lower Z B : ℝ)
    (ha : 0 ≤ a) (hlower : 0 < lower) (hZ : 0 ≤ Z) (hB : 0 ≤ B)
    (hn : ∀ j ≤ M, lower ≤ n j) (hmono : AntitoneOn n (Set.Iic M))
    (hm : ∀ j < M, n (j+1) ≤ m j ∧ m j ≤ n (j+1-K))
    (hz0 : ∀ j < M, 0 ≤ (phase j).re) (hz : ∀ j < M, ‖phase j‖ ≤ Z)
    (x y : ℝ)
    (hinterval : ∀ l u, l ≤ u → u ≤ N → ‖P.rawInterval coeff jet l u x y‖ ≤ B) :
    ‖∑ j ∈ Finset.univ.filter (fun j => start ≤ stop j),
      segmentWeight n (boundaryLog n m) phase a start (stop j) •
        P.rawBand coeff jet j x y‖ ≤
      (lower^(-a) * (1+(a+Z*K)*Real.log (n 0/n M))) * B := by
  let f := fun k => ∑ j ∈ Finset.univ.filter (fun j => stop j = k), P.rawBand coeff jet j x y
  have hpartial (k : ℕ) (_hsk : start ≤ k) (_hk : k ≤ M) :
      ‖∑ i ∈ Finset.Ico start (k+1), f i‖ ≤ B := by
    dsimp only [f]
    rw [sum_stopping_fibers]
    obtain ⟨l,u,hlu,hu,heq⟩ := P.stopping_band_eq_rawInterval coeff jet stop hstop start (k+1) x y
    rw [heq]
    exact hinterval l u hlu hu
  rw [stopping_weighted_sum_eq stop (fun j => P.rawBand coeff jet j x y) _ start M hmax]
  exact boundary_segment_amplitude_bound n m phase f start M K a lower Z B hstart
    ha hlower hZ hB hn hmono hm hz0 hz hpartial

end SourceLabeledLattice

/-- Specialization to the actual angular mass and boundary sets. The
individual top weight supplies the positive endpoint normalization. -/
theorem source_angular_stopping_amplitude_bound
    {ι X : Type*} (grid : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i z, 0 < weight i z)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (M : ℕ) (top : ι) (htop : top ∈ tops)
    (he : grid.eligible cutoff (precision top) M) (z : X)
    (a Z : ℝ) (ha : 0 ≤ a) (hZ : 0 ≤ Z)
    (hz0 : ∀ j < M, 0 ≤ (phase j).re) (hz : ∀ j < M, ‖phase j‖ ≤ Z)
    {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (stop : Fin N → ℕ) (hstop : Antitone stop)
    (start : ℕ) (hstart : start ≤ M) (hmax : ∀ j, stop j ≤ M)
    (x y B : ℝ) (hB : 0 ≤ B)
    (hinterval : ∀ l u, l ≤ u → u ≤ N → ‖P.rawInterval coeff jet l u x y‖ ≤ B) :
    let n := fun j => grid.mass tops slope precision cutoff weight j (grid.index j (slope top)) z
    let m := fun j => grid.sourceBoundaryMass tops slope precision cutoff weight K gap j
      (grid.index (j+1) (slope top)) z
    ‖∑ j ∈ Finset.univ.filter (fun j => start ≤ stop j),
      segmentWeight n (boundaryLog n m) phase a start (stop j) • P.rawBand coeff jet j x y‖ ≤
      ((weight top z)^(-a) * (1+(a+Z*K)*Real.log (n 0/n M))) * B := by
  dsimp only
  let n := fun j => grid.mass tops slope precision cutoff weight j (grid.index j (slope top)) z
  have hn (j : ℕ) (hj : j ≤ M) : weight top z ≤ n j := by
    apply Finset.single_le_sum (fun i _ => (hw i z).le)
    exact (grid.mem_cellTops _ _ _ _ _ _ _).mpr
      ⟨htop,rfl,grid.eligible_of_le (hp top htop) hj he⟩
  apply P.angular_stopping_amplitude_bound coeff jet stop hstop start M K hstart hmax
    n _ phase a (weight top z) Z B ha (hw top z) hZ hB hn
    ((grid.path_mass_antitone tops slope precision cutoff weight hp
      (fun i z => (hw i z).le) top z).antitoneOn _)
  · intro j _
    exact grid.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
      (fun i z => (hw i z).le) hK gap j (slope top) z
  · exact hz0
  · exact hz
  · exact hinterval

end LipschitzHilbert

end

end OAI
