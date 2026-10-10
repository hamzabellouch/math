import OAI.NumberTheory.JointDickman.Probability.HistogramProductError
import OAI.NumberTheory.JointDickman.Probability.ResidueFourierProjection

namespace OAI

/-! # Replacing histogram cell averages by a chosen cell value -/

namespace JointDickman
open Finset MeasureTheory

theorem manuscriptChannel_cell_norm_le {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (g : (auxiliaryPrimes B → Bool) → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (i : Fin (channelFineCount m B)) (r : (ZMod q)ˣ) :
    ‖((channelMesh (channelFineCount m B)/(q.totient : ℝ))*manuscriptChannel m B q g (i,r) : ℝ)‖ ≤
      (channelMesh (channelFineCount m B)/(q.totient : ℝ))*manuscriptChannel m B q (fun _ => 1) (i,r) := by
  have hh := manuscriptCellSum_norm_le hm hB g hg (fun _ => 1) 1 i r (by simp)
  have he : manuscriptCellSum m B q g (fun _ => 1) i r =
      (((channelMesh (channelFineCount m B)/(q.totient : ℝ))*manuscriptChannel m B q g (i,r) : ℝ) : ℂ) := by
    unfold manuscriptCellSum
    simp only [mul_one]
    rw [← manuscriptChannel_cell_mass hm hB g (i,r)]
    simp only [Complex.ofReal_sum,apply_ite,Complex.ofReal_zero]
  rw [he,Complex.norm_real] at hh
  simpa only [one_mul] using hh

noncomputable def cellCoefficientFourier (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B))) (g : (auxiliaryPrimes B → Bool) → ℝ)
    (F : Fin (channelFineCount m B) → ℂ) (h : ZMod q) : ℂ :=
  unitResidueFourier (fun r => ∑ i ∈ J,
    (((channelMesh (channelFineCount m B)/(q.totient : ℝ))*manuscriptChannel m B q g (i,r) : ℝ) : ℂ)*F i) h

theorem cellCoefficientFourier_square_le {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (F : Fin (channelFineCount m B) → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ i ∈ J, ‖F i‖ ≤ M) :
    (∑ h : ZMod q, ‖cellCoefficientFourier m B q J g F h‖^2) ≤
      manuscriptAmplitudeEnergy m B q J*M^2 := by
  have hδ := (channelMesh_pos (channelFineCount_pos hm hB)).le
  have hh := cellAmplitude_fourier_bound J hδ hM
    (fun i r => manuscriptChannel m B q (fun _ => 1) (i,r))
    (fun i r => (((channelMesh (channelFineCount m B)/(q.totient : ℝ))*
      manuscriptChannel m B q g (i,r) : ℝ) : ℂ)*F i) (by
      intro i hi r
      have hw := manuscriptChannel_cell_norm_le hm hB g hg i r
      rw [norm_mul,Complex.norm_real]
      exact (mul_le_mul hw (hF i hi) (norm_nonneg _)
        ((norm_nonneg _).trans hw)).trans_eq (by ring))
  exact hh.trans_eq (by unfold manuscriptAmplitudeEnergy; ring)

theorem cellCoefficientFourier_sub (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B))) (g : (auxiliaryPrimes B → Bool) → ℝ)
    (F G : Fin (channelFineCount m B) → ℂ) (h : ZMod q) :
    cellCoefficientFourier m B q J g F h-cellCoefficientFourier m B q J g G h =
      cellCoefficientFourier m B q J g (fun i => F i-G i) h := by
  simp only [cellCoefficientFourier,unitResidueFourier,mul_sub,sum_sub_distrib]

theorem averaged_to_sampled_square_error {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (F : ℝ → ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hI : ∀ i ∈ J, IntervalIntegrable F volume
      (channelLower (channelFineCount m B) i) (channelUpper (channelFineCount m B) i))
    (hLip : ∀ i ∈ J, ∀ u ∈ Set.Icc (channelLower (channelFineCount m B) i)
        (channelUpper (channelFineCount m B) i),
      ∀ v ∈ Set.Icc (channelLower (channelFineCount m B) i)
        (channelUpper (channelFineCount m B) i), ‖F u-F v‖ ≤ L*|u-v|) :
    (∑ h : ZMod q, ‖manuscriptApproxFourier m B q J g F h-
      cellCoefficientFourier m B q J g (fun i => F (channelLower (channelFineCount m B) i)) h‖^2) ≤
      manuscriptAmplitudeEnergy m B q J*(L*channelMesh (channelFineCount m B))^2 := by
  let A := fun i => complexCellAverage (channelLower (channelFineCount m B) i)
    (channelUpper (channelFineCount m B) i) F
  have he (h : ZMod q) : manuscriptApproxFourier m B q J g F h = cellCoefficientFourier m B q J g A h := rfl
  simp_rw [he,cellCoefficientFourier_sub]
  apply cellCoefficientFourier_square_le hm hB J g hg _ (by
    exact mul_nonneg hL (channelMesh_pos (channelFineCount_pos hm hB)).le)
  intro i hi
  have hw := channel_width (channelFineCount m B) i
  have hab : channelLower (channelFineCount m B) i < channelUpper (channelFineCount m B) i := by
    linarith [channelMesh_pos (channelFineCount_pos hm hB)]
  have hh := complexCellAverage_lipschitz_error hab hL (hI i hi)
    (show channelLower (channelFineCount m B) i ∈ Set.Icc
      (channelLower (channelFineCount m B) i) (channelUpper (channelFineCount m B) i) from ⟨le_rfl,hab.le⟩)
    (hLip i hi)
  rw [hw,norm_sub_rev] at hh
  exact hh

end JointDickman

end OAI
