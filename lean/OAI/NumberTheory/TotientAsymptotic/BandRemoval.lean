import OAI.NumberTheory.TotientAsymptotic.NormalizedConcentration
import OAI.NumberTheory.TotientAsymptotic.ThickenedWitness
import OAI.NumberTheory.TotientAsymptotic.CofactorWitnessAggregation
import OAI.NumberTheory.TotientAsymptotic.UnionVolume

namespace OAI

/-! Removing the retained bands after aggregating complete witness boxes. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

lemma measurableSet_prefixBandRegion (x : ℝ) (H : ℕ) :
    MeasurableSet (prefixBandRegion x H) := by
  unfold prefixBandRegion
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i =>
    (measurableSet_le measurable_const (measurable_pi_apply i)).inter
      (measurableSet_le (measurable_pi_apply i) measurable_const))

lemma fullBoxSimplex_volume_ne_top (x : ℝ) {N : ℕ} (hN : 0 < N) :
    volume (fullBoxSimplex x N) ≠ ⊤ := by
  let β : ℕ → ℝ := fun r => 1+simplexBoxError 4 (m x-r)
  have hβ : ∀ r, 1 ≤ β r := fun r => by
    dsimp [β]
    linarith [simplexBoxError_nonneg (by norm_num : (0 : ℝ) ≤ 4) (m x-r)]
  have hv := volume_enlargedSimplex_product_bound (N := N) (B x) β hβ
  change volume (fullBoxSimplex x N) ≤ _ at hv
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (prefixRegion_volume_ne_top hN (B x))) hv

lemma retainedPhaseBad_volume_ne_top (x : ℝ) (H : ℕ) {N : ℕ}
    (hN : 0 < N) (hRN : R x H ≤ N) : volume (retainedPhaseBad x H N hRN) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (fullBoxSimplex_volume_ne_top x hN)
  apply measure_mono
  intro u hu
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hu
  exact hi.1

lemma eventually_scale_product_lower : ∀ᶠ x : ℝ in atTop, 1 ≤ B x*rho^(m x) := by
  have hgrow : Tendsto (fun x : ℝ => lam*(m x : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp m_tendsto).const_mul_atTop lam_pos
  filter_upwards [inverse_scale_bound,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
    hgrow.eventually (eventually_ge_atTop (2 : ℝ))] with x hscale hB hm
  have hp : 0 < B x*rho^(m x) := mul_pos hB (pow_pos rho_pos _)
  have hh := (div_le_iff₀ hp).mp hscale
  rw [show 2/lam*(B x*rho^(m x)) = 2*(B x*rho^(m x))/lam by ring] at hh
  have hh' := (le_div_iff₀ lam_pos).mp hh
  nlinarith

lemma band_loss_enclosure {x : ℝ} {H : ℕ} {η : TailDatum H}
    (henclose : ∀ {u : Fin (R x H) → ℝ}, u ∈ tailPrefixRegion x H η →
      ∀ {v : Fin (H-P H) → ℝ}, (∀ i, |tailVector η i-v i| ≤ 1) →
      joinCoordinates (R x H) (H-P H) (u,v) ∈ fullBoxSimplex x (R x H+(H-P H)))
    {u : Fin (R x H) → ℝ}
    (hu : u ∈ tailPrefixRegion x H η \ prefixBandRegion x H)
    {v : Fin (H-P H) → ℝ} (hv : ∀ i, |tailVector η i-v i| ≤ 1) :
    joinCoordinates (R x H) (H-P H) (u,v) ∈
      retainedPhaseBad x H (R x H+(H-P H)) (Nat.le_add_right _ _) := by
  have hbad := hu.2
  change ¬ ∀ i, (9/10 : ℝ)*bandScale x (i.val+1) ≤ u i ∧
    u i ≤ (11/10 : ℝ)*bandScale x (i.val+1) at hbad
  push Not at hbad
  obtain ⟨i, hi⟩ := hbad
  change _ ∈ ⋃ i : Fin (R x H), fullBoxSimplex x _ ∩
    phaseCoordinateBad x (Fin.castLE (Nat.le_add_right _ _) i)
  refine Set.mem_iUnion.mpr ⟨i, henclose hu.1 hv, ?_⟩
  change _ < _ ∨ _ < _
  have he : Fin.castLE (Nat.le_add_right (R x H) (H-P H)) i =
      Fin.castAdd (H-P H) i := Fin.ext rfl
  rw [he, joinCoordinates_left]
  simp only [Fin.val_castAdd] at *
  by_cases hlo : (9/10 : ℝ)*bandScale x (i.val+1) ≤ u i
  · right
    have hh := hi hlo
    have hb := bandScale_nonneg x (i.val+1)
    linarith
  · left
    have hh := lt_of_not_ge hlo
    have hb := bandScale_nonneg x (i.val+1)
    linarith

/-- The entire reciprocal-totient weighted loss from removing retained
bands is negligible, uniformly over finite families of actual witnesses. -/
theorem witness_band_removal (hbox : FordUnitPrimeBoxInput)
    (hmertens : MertensProductInput) (hren : FordRenewalInput)
    (hford : FordCoordinateConcentrationInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ W : Finset (TailDatum H), (∀ η ∈ W, IsWitness H (theta x) η) →
      (∑ η ∈ W, ((w η).totient : ℝ)⁻¹*
        volume.real (tailPrefixRegion x H η \ prefixBandRegion x H))/G x (m x) ≤ ε H := by
  obtain ⟨C, hC, hagg⟩ := all_cofactor_witness_aggregation hbox hmertens
  obtain ⟨δ, hδ, hnorm⟩ := normalized_retained_band_loss hford hren (4*(lam/rho))
  refine ⟨fun H => C*δ H, by simpa using hδ.const_mul C, ?_⟩
  filter_upwards [hnorm, eventually_thickened_witness_enclosure hren,
    eventually_tail_cut_separated, eventually_ge_atTop 2] with H hnormH hencloseH hcuts hH
  have hPH : P H < H := P_lt_self hH
  filter_upwards [hnormH, theta_eventually_mem, eventually_scale_product_lower,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
    m_tendsto.eventually (eventually_ge_atTop (H+2))] with x hnormX hs hBr hB hm
  intro W hW
  have hdim : L x H=R x H+(H-P H) := by unfold L R; omega
  have hJ : 2 ≤ R x H+(H-P H) := by unfold R; omega
  obtain ⟨N, hN⟩ : ∃ N, R x H+(H-P H)=N+2 := ⟨R x H+(H-P H)-2, by omega⟩
  have hnorm' : Real.exp ((4*(lam/rho))*cofactorScale H)*
      volume.real (retainedPhaseBad x H (R x H+(H-P H)) (Nat.le_add_right _ _))/
        G x (m x) ≤ δ H := by
    have hh := hnormX N (hdim.trans hN)
    rw [← hN] at hh
    exact hh (Nat.le_add_right _ _)
  have hsum := hagg hs hPH.le W
    (fun η => tailPrefixRegion x H η \ prefixBandRegion x H)
    (retainedPhaseBad x H (R x H+(H-P H)) (Nat.le_add_right _ _)) hW
    (fun η _ => (measurableSet_tailPrefixRegion x H η).diff (measurableSet_prefixBandRegion x H))
    (retainedPhaseBad_volume_ne_top x H (by omega) (Nat.le_add_right _ _))
    (by
      intro η hη u hu v hv
      exact band_loss_enclosure
        (hencloseH hs.1 (by omega) hPH hB.le hBr (hW η hη)) hu hv)
  calc
    _ ≤ (C*Real.exp ((4*(lam/rho))*cofactorScale H)*
        volume.real (retainedPhaseBad x H (R x H+(H-P H)) (Nat.le_add_right _ _)))/
          G x (m x) := div_le_div_of_nonneg_right hsum (G_pos hB _).le
    _ = C*(Real.exp ((4*(lam/rho))*cofactorScale H)*
        volume.real (retainedPhaseBad x H (R x H+(H-P H)) (Nat.le_add_right _ _))/
          G x (m x)) := by ring
    _ ≤ C*δ H := mul_le_mul_of_nonneg_left hnorm' hC.le

end TotientAsymptotic

end

end OAI
