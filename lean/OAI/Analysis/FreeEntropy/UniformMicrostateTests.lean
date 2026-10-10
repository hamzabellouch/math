import OAI.Analysis.FreeEntropy.FisherDeficit

namespace OAI

noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace FiniteEntropySeparation
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ} (X : Fin n → H →L[ℂ] H)
 theorem diagonalMicrostates_uniform_open (R : ℝ) (O : Set (List (Fin n) → ℂ)) (hO : IsOpen O)
    (hX : wordMoment τ X ∈ O) :
    ∀ᶠk : ℕ in atTop,∀d : ℕ,∀a : MatrixCoordinates n d,a∈diagonalMicrostates τ X R k d → matrixMoment a∈O := by
  classical
  by_contra h
  have hb : ∀N : ℕ,∃k,N≤k ∧ ∃d : ℕ,∃a : MatrixCoordinates n d,
      a∈diagonalMicrostates τ X R k d ∧ matrixMoment a∉O := by
    simpa only [eventually_atTop,not_exists,not_forall,Classical.not_imp,exists_prop] using h
  obtain ⟨I,hI,hi⟩ := exists_strictMono_diagonal (fun _ k => ∃d : ℕ,∃a : MatrixCoordinates n d,
    a∈diagonalMicrostates τ X R k d ∧ matrixMoment a∉O) (by
      intro k L
      obtain ⟨j,hj,hh⟩ := hb (L+1)
      exact ⟨j,by omega,hh⟩)
  choose D a ha hbad using hi
  have hlim : Tendsto (fun k => matrixMoment (a k)) atTop (𝓝 (wordMoment τ X)) := by
    apply tendsto_pi_nhds.mpr
    intro w
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun k => norm_nonneg _))
    · filter_upwards [hI.tendsto_atTop.eventually (eventually_ge_atTop w.length)] with k hk
      exact ((ha k).2 w hk).le
    · exact (show Tendsto (fun k : ℕ => (k+1:ℝ)⁻¹) atTop (𝓝 0) by
        simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hI.tendsto_atTop
  have hev := hlim.eventually (hO.mem_nhds hX)
  obtain ⟨k,hk⟩ := hev.exists
  exact hbad k hk
end FiniteEntropySeparation

end

end OAI
