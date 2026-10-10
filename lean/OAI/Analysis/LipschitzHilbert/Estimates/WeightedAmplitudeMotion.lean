import OAI.Analysis.LipschitzHilbert.Phase.SourceAngularAmplitude
import OAI.Analysis.LipschitzHilbert.Fourier.CovariantLineMotion

namespace OAI

/-! Summation by parts for moving packet amplitudes. The unweighted
interval motion and the endpoint-weight motion are charged separately. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem weighted_interval_motion (w w' : ℕ → ℂ) (f f' : ℕ → E)
    (start N : ℕ) (hstart : start ≤ N) (A D B ε : ℝ)
    (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hweight : ‖w' N‖+(∑ j ∈ Finset.Ico start N, ‖w' (j+1)-w' j‖) ≤ A)
    (hweightdiff : ‖w' N-w N‖+
      (∑ j ∈ Finset.Ico start N, ‖(w' (j+1)-w (j+1))-(w' j-w j)‖) ≤ D)
    (hpartial : ∀ k, start ≤ k → k ≤ N → ‖∑ j ∈ Finset.Ico start (k+1), f j‖ ≤ B)
    (hmotion : ∀ k, start ≤ k → k ≤ N →
      ‖∑ j ∈ Finset.Ico start (k+1), (f' j-f j)‖ ≤ ε) :
    ‖(∑ j ∈ Finset.Ico start (N+1), w' j • f' j)-
      (∑ j ∈ Finset.Ico start (N+1), w j • f j)‖ ≤ A*ε+D*B := by
  have heq : (∑ j ∈ Finset.Ico start (N+1), w' j • f' j)-
      (∑ j ∈ Finset.Ico start (N+1), w j • f j) =
      (∑ j ∈ Finset.Ico start (N+1), w' j • (f' j-f j))+
      (∑ j ∈ Finset.Ico start (N+1), (w' j-w j) • f j) := by
    simp only [smul_sub, sub_smul, Finset.sum_sub_distrib]
    abel
  have hfirst := norm_weighted_Ico_le_variation w' (fun j => f' j-f j)
    start N ε hstart hmotion
  have hsecond := norm_weighted_Ico_le_variation (fun j => w' j-w j) f
    start N B hstart hpartial
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add
    (hfirst.trans (mul_le_mul_of_nonneg_right hweight hε))
    (hsecond.trans (mul_le_mul_of_nonneg_right hweightdiff hB)))

namespace SourceLabeledLattice

attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

/-- Motion of all original intervals controls the stopped source sum.
The unitary may be the common diagonal carrier on the reference line. -/
theorem stopping_amplitude_motion (P : SourceLabeledLattice N κ Label Item)
    (coeff coeff' : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (stop : Fin N → ℕ) (hstop : Antitone stop)
    (start M : ℕ) (hstart : start ≤ M) (hmax : ∀ j, stop j ≤ M)
    (w w' : ℕ → ℂ) (x0 y0 x1 y1 A D B ε : ℝ)
    (U : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hweight : ‖w' M‖+(∑ j ∈ Finset.Ico start M, ‖w' (j+1)-w' j‖) ≤ A)
    (hweightdiff : ‖w' M-w M‖+
      (∑ j ∈ Finset.Ico start M, ‖(w' (j+1)-w (j+1))-(w' j-w j)‖) ≤ D)
    (hinterval : ∀ l u, l ≤ u → u ≤ N → ‖P.rawInterval coeff jet l u x0 y0‖ ≤ B)
    (hmotion : ∀ l u, l ≤ u → u ≤ N →
      (∀ j : Fin N, l ≤ j.val → j.val < u → start ≤ stop j) →
      ‖P.rawInterval coeff' jet l u x1 y1-U (P.rawInterval coeff jet l u x0 y0)‖ ≤ ε) :
    ‖(∑ j ∈ Finset.univ.filter (fun j => start ≤ stop j),
        w' (stop j) • P.rawBand coeff' jet j x1 y1)-
      U (∑ j ∈ Finset.univ.filter (fun j => start ≤ stop j),
        w (stop j) • P.rawBand coeff jet j x0 y0)‖ ≤ A*ε+D*B := by
  let f0 := fun k => ∑ j ∈ Finset.univ.filter (fun j => stop j = k), P.rawBand coeff jet j x0 y0
  let f1 := fun k => ∑ j ∈ Finset.univ.filter (fun j => stop j = k), P.rawBand coeff' jet j x1 y1
  have hpartial (k : ℕ) (_hsk : start ≤ k) (_hk : k ≤ M) :
      ‖∑ i ∈ Finset.Ico start (k+1), U (f0 i)‖ ≤ B := by
    rw [← map_sum]
    rw [U.norm_map]
    dsimp only [f0]
    rw [sum_stopping_fibers]
    obtain ⟨l,u,hlu,hu,heq⟩ := P.stopping_band_eq_rawInterval coeff jet stop hstop start (k+1) x0 y0
    rw [heq]
    exact hinterval l u hlu hu
  have hpartialdiff (k : ℕ) (_hsk : start ≤ k) (_hk : k ≤ M) :
      ‖∑ i ∈ Finset.Ico start (k+1), (f1 i-U (f0 i))‖ ≤ ε := by
    rw [Finset.sum_sub_distrib, ← map_sum]
    dsimp only [f0,f1]
    rw [sum_stopping_fibers, sum_stopping_fibers]
    -- The same stopping-band bounds are used at both spatial points.
    have hcommon := antitone_stopping_band_interval stop hstop start (k+1)
    obtain ⟨lo,hi,hlo,hhi,hband⟩ := hcommon
    have hb (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (x y : ℝ) :
        (∑ j ∈ Finset.univ.filter (fun j => start ≤ stop j ∧ stop j < k+1),
          P.rawBand c jet j x y) = P.rawInterval c jet lo hi x y := by
      rw [P.rawInterval_eq_band_sum c jet lo hi hlo x y]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hband j
    rw [hb coeff' x1 y1, hb coeff x0 y0]
    exact hmotion lo hi hlo hhi (fun j hjl hju => ((hband j).mpr ⟨hjl,hju⟩).1)
  rw [stopping_weighted_sum_eq stop (fun j => P.rawBand coeff' jet j x1 y1) w' start M hmax,
    stopping_weighted_sum_eq stop (fun j => P.rawBand coeff jet j x0 y0) w start M hmax,
    map_sum]
  simp only [map_smul]
  exact weighted_interval_motion w w' (fun k => U (f0 k)) f1 start M hstart A D B ε
    hB hε hweight hweightdiff hpartial hpartialdiff

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
