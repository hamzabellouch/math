import OAI.NumberTheory.TotientAsymptotic.BoundaryGrid
import OAI.NumberTheory.TotientAsymptotic.PrimeErrorDecay

namespace OAI

/-! A uniform majorant for the outer boxes in the prime-volume sandwich. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma fullBoxSimplex_volume_bound {x : ℝ} {H : ℕ} (hB : 0 < B x) (hL : 0 < L x H) :
    volume.real (fullBoxSimplex x (L x H)) ≤ Real.exp (simplexBoxTail 4 (P H))*G x (L x H) := by
  let β : ℕ → ℝ := fun r => 1+simplexBoxError 4 (m x-r)
  have hβ : ∀ r, 1 ≤ β r := fun r => by
    dsimp [β]
    linarith [simplexBoxError_nonneg (by norm_num : (0 : ℝ)≤4) (m x-r)]
  have hPm : P H ≤ m x := by unfold L at hL; omega
  have hj := fullBoxScale_jacobian (H := H) hPm
  have he : volume (fullBoxSimplex x (L x H)) ≤
      ENNReal.ofReal (Real.exp (simplexBoxTail 4 (P H))*G x (L x H)) := by
    calc
      _ ≤ ENNReal.ofReal (∏ i : Fin (L x H), enlargementScale β i)*
          volume (prefixRegion (L x H) (B x) 0 0) :=
        volume_enlargedSimplex_product_bound (B x) β hβ
      _ ≤ ENNReal.ofReal (Real.exp (simplexBoxTail 4 (P H)))*
          volume (prefixRegion (L x H) (B x) 0 0) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hj) le_rfl
      _ = _ := by
        rw [volume_zero_prefixRegion hB.le hL, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (G_pos hB _).le))

lemma outer_grid_union_card {x : ℝ} {H : ℕ} (hs : theta x ∈ Set.Ico (0 : ℝ) 1) (d : ℕ) :
    ((gridOuter (bandGrid x H) (bandedWitnessRegion x H d)).card : ℝ) ≤
      ∑ η ∈ witnessFinset H (theta x) d,
        ((gridOuter (bandGrid x H) (witnessBandedRegion x H η)).card : ℝ) := by
  have hsub : gridOuter (bandGrid x H) (bandedWitnessRegion x H d) ⊆
      (witnessFinset H (theta x) d).biUnion
        (fun η => gridOuter (bandGrid x H) (witnessBandedRegion x H η)) := by
    intro b hb
    obtain ⟨hbK, u, hub, hu⟩ := Finset.mem_filter.mp hb
    rw [bandedWitnessRegion_eq hs] at hu
    obtain ⟨η, hη⟩ := Set.mem_iUnion.mp hu
    obtain ⟨hη, huη⟩ := Set.mem_iUnion.mp hη
    exact Finset.mem_biUnion.mpr ⟨η, hη, Finset.mem_filter.mpr ⟨hbK, u, hub, huη⟩⟩
  exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le

/-- The whole outer-box volume has only the subpolynomial cofactor cost. -/
theorem outer_grid_mass_bound (hbox : FordUnitPrimeBoxInput)
    (hmertens : MertensProductInput) (hren : FordRenewalInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      (∑ d ∈ Finset.Icc 1 (tailValueBound H), (d : ℝ)⁻¹*
        (gridOuter (bandGrid x H) (bandedWitnessRegion x H d)).card) ≤
      C*Real.exp ((4*(lam/rho))*cofactorScale H)*G x (m x) := by
  obtain ⟨C, hC, hagg⟩ := all_cofactor_witness_aggregation hbox hmertens
  obtain ⟨J, hJ, hproj⟩ := uniform_projected_volume_bound hren
  have hfac : Tendsto (fun H => Real.exp (simplexBoxTail 4 (P H))*projectedEnvelope J (P H))
      atTop (nhds 0) := by
    have he := (Real.continuous_exp.tendsto (0 : ℝ)).comp (simplexBoxTail_tendsto 4 |>.comp P_tendsto)
    simpa only [Function.comp_def, Real.exp_zero, one_mul] using
      he.mul ((summable_projectedEnvelope hJ).tendsto_atTop_zero.comp P_tendsto)
  have hcut : ∀ᶠ H : ℕ in atTop, 4 ≤ lam*(P H : ℝ) :=
    ((tendsto_natCast_atTop_atTop.comp P_tendsto).const_mul_atTop lam_pos).eventually
      (eventually_ge_atTop (4 : ℝ))
  refine ⟨C, hC, ?_⟩
  filter_upwards [hfac.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)),
    hcut, eventually_tail_cut_separated, eventually_ge_atTop 2] with H hfacH hcutH hcuts hH
  have hPH := P_lt_self hH
  filter_upwards [theta_eventually_mem, eventually_scale_product_lower, hproj,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
    m_tendsto.eventually (eventually_ge_atTop (H+1))] with x hs hBr hp hB hm
  have hdim : L x H=R x H+(H-P H) := by unfold R L; omega
  have hL : 0 < L x H := by unfold L; omega
  have hvol := fullBoxSimplex_volume_bound hB hL
  have hG := (div_le_iff₀ (G_pos hB (m x))).mp (hp (P H) (by omega))
  change G x (L x H) ≤ projectedEnvelope J (P H)*G x (m x) at hG
  have hvol' : volume.real (fullBoxSimplex x (R x H+(H-P H))) ≤ G x (m x) := by
    rw [hdim] at hvol
    calc
      _ ≤ Real.exp (simplexBoxTail 4 (P H))*G x (R x H+(H-P H)) := hvol
      _ ≤ Real.exp (simplexBoxTail 4 (P H))*(projectedEnvelope J (P H)*G x (m x)) := by
        rw [← hdim]
        exact mul_le_mul_of_nonneg_left hG (Real.exp_pos _).le
      _ ≤ G x (m x) := by
        simpa only [mul_assoc, one_mul] using
          mul_le_mul_of_nonneg_right hfacH.le (G_pos hB (m x)).le
  let S := fun η : TailDatum H => gridRegion (gridOuter (bandGrid x H) (witnessBandedRegion x H η))
  have hsum := hagg hs hPH.le (activeWitnesses H (theta x)) S
    (fullBoxSimplex x (R x H+(H-P H)))
    (fun η hη => (mem_activeWitnesses hs).mp hη)
    (fun η _ => (gridOuter (bandGrid x H) (witnessBandedRegion x H η)).measurableSet_biUnion
      (fun b _ => measurableSet_unitGridCell b))
    (fullBoxSimplex_volume_ne_top x (by unfold R; omega)) (by
      intro η hη u hu v hv
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hu
      obtain ⟨hb, hub⟩ := Set.mem_iUnion.mp hb
      obtain ⟨_, u₀, h₀b, h₀⟩ := Finset.mem_filter.mp hb
      exact (witness_full_cube_enclosure hs.1 hcutH hcuts.1 hPH (by omega) hBr
        ((mem_activeWitnesses hs).mp hη) h₀ (unitGridCell_coordinate_distance h₀b hub) hv).1)
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 (tailValueBound H), (d : ℝ)⁻¹*
        ∑ η ∈ witnessFinset H (theta x) d,
          ((gridOuter (bandGrid x H) (witnessBandedRegion x H η)).card : ℝ) :=
      Finset.sum_le_sum (fun d _ => mul_le_mul_of_nonneg_left (outer_grid_union_card hs d) (by positivity))
    _ = ∑ η ∈ activeWitnesses H (theta x), ((w η).totient : ℝ)⁻¹*volume.real (S η) := by
      rw [weighted_witness_fibers hs]
      apply Finset.sum_congr rfl
      intro η _
      rw [show volume.real (S η) = (gridOuter (bandGrid x H) (witnessBandedRegion x H η)).card from
        gridRegion_volume_real _]
    _ ≤ C*Real.exp ((4*(lam/rho))*cofactorScale H)*
        volume.real (fullBoxSimplex x (R x H+(H-P H))) := hsum
    _ ≤ _ := mul_le_mul_of_nonneg_left hvol' (by positivity)

end TotientAsymptotic

end

end OAI
