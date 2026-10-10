import OAI.NumberTheory.TotientAsymptotic.BoundaryEnclosure
import OAI.NumberTheory.TotientAsymptotic.NormalizedShell
import OAI.NumberTheory.TotientAsymptotic.NormalizedConcentration
import OAI.NumberTheory.TotientAsymptotic.CofactorWitnessAggregation
import OAI.NumberTheory.TotientAsymptotic.BandRemoval

namespace OAI

/-! Tail-box aggregation of all prefix boxes crossing a witness boundary. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

/-- A simultaneous boundary estimate for any measurable union of crossing
boxes, uniformly in the witnesses and the number of coordinates. -/
theorem witness_boundary_aggregation (hbox : FordUnitPrimeBoxInput)
    (hmertens : MertensProductInput) (hren : FordRenewalInput)
    (hford : FordCoordinateConcentrationInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ W : Finset (TailDatum H), (∀ η ∈ W, IsWitness H (theta x) η) →
      ∀ S : TailDatum H → Set (Fin (R x H) → ℝ), (∀ η ∈ W, MeasurableSet (S η)) →
      (∀ η ∈ W, ∀ u ∈ S η,
        ∃ u₀ ∈ perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H,
          (∀ i, |u₀ i-u i| ≤ 1) ∧
          ∃ w, w ∉ perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H ∧
            ∀ i, |w i-u i| ≤ 1) →
      (∑ η ∈ W, ((w η).totient : ℝ)⁻¹*volume.real (S η))/G x (m x) ≤ ε H := by
  obtain ⟨C, hC, hagg⟩ := all_cofactor_witness_aggregation hbox hmertens
  obtain ⟨δ, hδ, hshell⟩ := normalized_additive_shell_loss hren (4*(lam/rho))
  obtain ⟨ζ, hζ, hband⟩ := normalized_retained_band_loss hford hren (4*(lam/rho))
  refine ⟨fun H => C*(δ H+ζ H), by simpa using (hδ.add hζ).const_mul C, ?_⟩
  have hlarge : ∀ᶠ H : ℕ in atTop, 100 < lam*(H : ℝ) :=
    ((tendsto_natCast_atTop_atTop.const_mul_atTop lam_pos)).eventually (eventually_gt_atTop (100 : ℝ))
  have hcut : ∀ᶠ H : ℕ in atTop, 4 ≤ lam*(P H : ℝ) :=
    ((tendsto_natCast_atTop_atTop.comp P_tendsto).const_mul_atTop lam_pos).eventually
      (eventually_ge_atTop (4 : ℝ))
  filter_upwards [hshell, hband, hlarge, hcut, eventually_tail_cut_separated,
    eventually_ge_atTop 2] with H hS hB hlargeH hcutH hcuts hH
  have hPH := P_lt_self hH
  filter_upwards [hS, hB, theta_eventually_mem, eventually_scale_product_lower,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
    m_tendsto.eventually (eventually_ge_atTop (H+2))] with x hSx hBx hs hBr hBpos hm
  intro W hW S hSm hcross
  have hdim : L x H=R x H+(H-P H) := by unfold L R; omega
  have hn : 0 < R x H+(H-P H) := by unfold R; omega
  have hnormS : Real.exp ((4*(lam/rho))*cofactorScale H)*
      volume.real (additiveBoxShell x (R x H) (R x H+(H-P H)) (Nat.le_add_right _ _))/
        G x (m x) ≤ δ H := by
    rw [hdim] at hSx
    exact hSx (Nat.le_add_right _ _)
  have hnormB : Real.exp ((4*(lam/rho))*cofactorScale H)*
      volume.real (retainedPhaseBad x H (R x H+(H-P H)) (Nat.le_add_right _ _))/
        G x (m x) ≤ ζ H := by
    obtain ⟨N, heq⟩ : ∃ N, R x H+(H-P H)=N+2 := ⟨R x H+(H-P H)-2, by omega⟩
    have hh := hBx N (hdim.trans heq)
    rw [← heq] at hh
    exact hh (Nat.le_add_right _ _)
  let T := additiveBoxShell x (R x H) (R x H+(H-P H)) (Nat.le_add_right _ _) ∪
    retainedPhaseBad x H (R x H+(H-P H)) (Nat.le_add_right _ _)
  have hfT : volume T ≠ ⊤ := (measure_union_lt_top
    (additiveBoxShell_volume_ne_top x (Nat.le_add_right _ _) hn).lt_top
    (retainedPhaseBad_volume_ne_top x H hn (Nat.le_add_right _ _)).lt_top).ne
  have hsum := hagg hs hPH.le W S T hW hSm hfT (by
    intro η hη u hu v hv
    obtain ⟨u₀, hu₀, hdu, w₀, hw₀, hdw⟩ := hcross η hη u hu
    apply witness_boundary_enclosure hs.1 hBpos.le hcutH hcuts.1 hPH (by omega)
      hBr (hW η hη) _ hu₀ hdu hw₀ hdw hv
    intro i
    have hi := i.isLt
    have hh : H ≤ m x-(i.val+1) := by unfold R at hi; omega
    have hcast : (H : ℝ) ≤ (m x-(i.val+1) : ℕ) := by exact_mod_cast hh
    exact (hlargeH.trans_le (mul_le_mul_of_nonneg_left hcast lam_pos.le)).trans_le
      (bandScale_lower hs.1 (i.val+1)))
  have hnormT : Real.exp ((4*(lam/rho))*cofactorScale H)*volume.real T/G x (m x) ≤ δ H+ζ H := by
    have hv := measureReal_union_le (μ := volume)
      (additiveBoxShell x (R x H) (R x H+(H-P H)) (Nat.le_add_right _ _))
      (retainedPhaseBad x H (R x H+(H-P H)) (Nat.le_add_right _ _))
    apply (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le) (G_pos hBpos _).le).trans
    simpa only [mul_add, add_div] using add_le_add hnormS hnormB
  calc
    _ ≤ (C*Real.exp ((4*(lam/rho))*cofactorScale H)*volume.real T)/G x (m x) :=
      div_le_div_of_nonneg_right hsum (G_pos hBpos _).le
    _ = C*(Real.exp ((4*(lam/rho))*cofactorScale H)*volume.real T/G x (m x)) := by ring
    _ ≤ C*(δ H+ζ H) := mul_le_mul_of_nonneg_left hnormT hC.le

end TotientAsymptotic

end

end OAI
