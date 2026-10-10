import OAI.NumberTheory.JointDickman.Probability.ManuscriptHistogramFourier
import OAI.NumberTheory.JointDickman.Probability.ResidueChannelRate

namespace OAI

/-! # Residue projection in the actual finite histogram -/

namespace JointDickman
open Finset MeasureTheory

/-- Finite form of (39) for a signed cell vector and arbitrary complex tests. -/
theorem histogram_cell_vector_bound {ι : Type*} [DecidableEq ι]
    {q : ℕ} [NeZero q] (J : Finset ι) {δ M : ℝ}
    (hδ : 0 ≤ δ) (hM : 0 ≤ M) (U : ι → (ZMod q)ˣ → ℝ)
    (F : ι → ℂ) (hF : ∀ i ∈ J, ‖F i‖ ≤ M) :
    (∑ h : ZMod q, ‖unitResidueFourier
      (fun r => ∑ i ∈ J, (δ : ℂ)*(U i r : ℂ)*F i) h/(q.totient : ℂ)‖^2) ≤
      ((q : ℝ)/(q.totient : ℝ))*((J.card : ℝ)*δ)*M^2*
        (∑ i ∈ J, ∑ r : (ZMod q)ˣ, (δ/(q.totient : ℝ))*U i r^2) := by
  have hv (r : (ZMod q)ˣ) : ‖∑ i ∈ J, (δ : ℂ)*(U i r : ℂ)*F i‖ ≤
      δ*M*(∑ i ∈ J, |U i r|) := by
    calc
      _ ≤ ∑ i ∈ J, ‖(δ : ℂ)*(U i r : ℂ)*F i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ J, δ*M*|U i r| := by
        apply sum_le_sum
        intro i hi
        rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
          Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hδ]
        exact (mul_le_mul_of_nonneg_left (hF i hi) (mul_nonneg hδ (abs_nonneg _))).trans_eq (by ring)
      _ = _ := (mul_sum _ _ _).symm
  simpa only [sq_abs] using finite_histogram_fourier_bound J hδ hM
    (fun i r => |U i r|) _ hv

/-- The residue-dependent part of the manuscript channel is controlled by
its proved squared residue norm, on any selected collection of cells. -/
theorem manuscript_histogram_residue_projection {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : Fin (channelFineCount m B) → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ i ∈ J, ‖F i‖ ≤ M) :
    (∑ h : ZMod q, ‖unitResidueFourier
      (fun r => ∑ i ∈ J, (channelMesh (channelFineCount m B) : ℂ)*
        ((manuscriptChannel m B q g (i,r)-
          finiteResidueAverage (fun s => manuscriptChannel m B q g (i,s))) : ℝ)*F i)
      h/(q.totient : ℂ)‖^2) ≤
      ((q : ℝ)/(q.totient : ℝ))*((J.card : ℝ)*channelMesh (channelFineCount m B))*M^2*
        (∑ i ∈ J, ∑ r : (ZMod q)ˣ,
          (channelMesh (channelFineCount m B)/(q.totient : ℝ))*
            (manuscriptChannel m B q g (i,r)-
              finiteResidueAverage (fun s => manuscriptChannel m B q g (i,s)))^2) :=
  histogram_cell_vector_bound J (channelMesh_pos (channelFineCount_pos hm hB)).le hM _ F hF

/-- Summing disjoint local squared errors is bounded by the global channel
residue norm. The only arithmetic inputs are the published channel inputs. -/
theorem manuscript_histogram_residue_projection_rate
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in Filter.atTop,
      ∀ q : ℕ, [NeZero q] → q ≤ B →
      ∀ J : Finset (Fin (channelFineCount m B)),
      ∀ g : (auxiliaryPrimes B → Bool) → ℝ,
      ∀ (F : Fin (channelFineCount m B) → ℂ) (M : ℝ), 0 ≤ M →
      (∀ i ∈ J, ‖F i‖ ≤ M) →
      (∑ h : ZMod q, ‖unitResidueFourier
        (fun r => ∑ i ∈ J, (channelMesh (channelFineCount m B) : ℂ)*
          ((manuscriptChannel m B q g (i,r)-
            finiteResidueAverage (fun s => manuscriptChannel m B q g (i,s))) : ℝ)*F i)
        h/(q.totient : ℂ)‖^2) ≤
        ((q : ℝ)/(q.totient : ℝ))*((J.card : ℝ)*channelMesh (channelFineCount m B))*M^2*
          (K*(B : ℝ)^(-(1/40 : ℝ)))*
            (∑ x, fullPrimeMass (auxiliaryPrimes B) x*g x^2) := by
  obtain ⟨K,hK,hbound⟩ := manuscriptChannel_residue_rate hSD hSW hM hMP
  refine ⟨K,hK,?_⟩
  intro m hm
  filter_upwards [hbound m hm,Filter.eventually_gt_atTop 0] with B hboundB hB
  intro q _ hq J g F M hM0 hF
  have hδ := (channelMesh_pos (channelFineCount_pos hm hB)).le
  have hlocal := manuscript_histogram_residue_projection (q := q) hm hB J g F hM0 hF
  have hrestrict : (∑ i ∈ J, ∑ r : (ZMod q)ˣ,
      (channelMesh (channelFineCount m B)/(q.totient : ℝ))*
        (manuscriptChannel m B q g (i,r)-
          finiteResidueAverage (fun s => manuscriptChannel m B q g (i,s)))^2) ≤
      (∑ a : Fin (channelFineCount m B) × (ZMod q)ˣ,
        (channelMesh (channelFineCount m B)/(q.totient : ℝ))*
          (manuscriptChannel m B q g a-
            finiteResidueAverage (fun s => manuscriptChannel m B q g (a.1,s)))^2) := by
    rw [Fintype.sum_prod_type]
    apply sum_le_sum_of_subset_of_nonneg (subset_univ J)
    intro i _ _
    apply sum_nonneg
    intro r _
    positivity
  calc
    _ ≤ _ := hlocal
    _ ≤ _ := by
      have hh := hrestrict.trans (hboundB q hq g)
      have hc : 0 ≤ ((q : ℝ)/(q.totient : ℝ))*((J.card : ℝ)*channelMesh (channelFineCount m B))*M^2 := by positivity
      exact (mul_le_mul_of_nonneg_left hh hc).trans_eq (by ring)

end JointDickman

end OAI
