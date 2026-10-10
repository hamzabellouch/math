import Mathlib
import OAI.Analysis.VlasovMaxwell.Flow.PhaseHits

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal RealInnerProductSpace

namespace RVM

lemma labelOccupation_le_duration_mass {f₀ : Phase → ℝ} {H : Phase → Set ℝ}
    {Z : Set Phase} (hZ : MeasurableSet Z) {D : ℝ}
    (hD : ∀ z, volume (H z)≤ENNReal.ofReal D)
    (hz : ∀ z, (H z).Nonempty → z∈Z) :
    labelOccupation f₀ H ≤ ENNReal.ofReal D * ∫⁻ z in Z, ENNReal.ofReal (f₀ z) := by
  rw [← lintegral_indicator hZ,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro z
  dsimp only
  by_cases he : (H z).Nonempty
  · rw [indicator_of_mem (hz z he)]
    calc
      _ ≤ ENNReal.ofReal (f₀ z)*ENNReal.ofReal D := by gcongr; exact hD z
      _ = _ := mul_comm _ _
  · simp only [not_nonempty_iff_eq_empty.mp he,measure_empty,mul_zero,zero_le]

lemma PhaseFlowOn.restricted_label_mass_bound {s : Solution} {T t p : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (ht : t∈Icc 0 T)
    {Z : Set Phase} (hZ : MeasurableSet Z) {G : Set (ℝ × Phase)}
    (hmom : ∀ z∈Z, p≤q (F.flow z t).2)
    (hG : ∀ z∈Z, (t,F.flow z t)∈G) :
    ENNReal.ofReal p * (∫⁻ z in Z, ENNReal.ofReal (s.f (0,z))) ≤
      ∫⁻ z : Phase, G.indicator (fun p => ENNReal.ofReal (q p.2.2 * s.f p)) (t,z) := by
  rw [← lintegral_indicator hZ,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← F.lintegral_comp ht (fun z => G.indicator (fun p => ENNReal.ofReal (q p.2.2 * s.f p)) (t,z))]
  apply lintegral_mono
  intro z
  dsimp only
  by_cases hz : z∈Z
  · rw [indicator_of_mem hz,indicator_of_mem (hG z hz),F.transport hs.f_smooth hs.vlasov ht,
      ENNReal.ofReal_mul (q_pos _).le]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hmom z hz)) le_rfl
  · rw [indicator_of_notMem hz,mul_zero]
    exact zero_le

lemma PhaseFlowOn.averaged_cell_occupation {s : Solution} {T a b p D : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (hCT : Icc a b⊆Icc (0:ℝ) T) {H : Phase → Set ℝ}
    {Z : Set Phase} (hZ : MeasurableSet Z) {G : Set (ℝ × Phase)}
    (hD : ∀ z, volume (H z)≤ENNReal.ofReal D)
    (hz : ∀ z, (H z).Nonempty → z∈Z)
    (hmom : ∀ t∈Icc a b, ∀ z∈Z, p≤q (F.flow z t).2)
    (hG : ∀ t∈Icc a b, ∀ z∈Z, (t,F.flow z t)∈G) :
    ENNReal.ofReal (b-a) * ENNReal.ofReal p * labelOccupation (fun z => s.f (0,z)) H ≤
      ENNReal.ofReal D * ∫⁻ t in Icc a b, ∫⁻ z : Phase,
        G.indicator (fun p => ENNReal.ofReal (q p.2.2 * s.f p)) (t,z) := by
  have hbnd := lintegral_mono_ae (μ:=volume.restrict (Icc a b))
    (ae_restrict_of_forall_mem measurableSet_Icc (fun t ht =>
      F.restricted_label_mass_bound hs (hCT ht) hZ (hmom t ht) (hG t ht)))
  rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc] at hbnd
  have hocc := labelOccupation_le_duration_mass hZ hD hz (f₀:=fun z => s.f (0,z))
  calc
    _ ≤ ENNReal.ofReal (b-a)*ENNReal.ofReal p*(ENNReal.ofReal D*
        ∫⁻ z in Z, ENNReal.ofReal (s.f (0,z))) := mul_le_mul' le_rfl hocc
    _ = ENNReal.ofReal D*((ENNReal.ofReal p * ∫⁻ z in Z, ENNReal.ofReal (s.f (0,z))) *
        ENNReal.ofReal (b-a)) := by ac_rfl
    _ ≤ _ := by gcongr

end RVM

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma PhaseFlowOn.position_lipschitz {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (z : Phase) :
    LipschitzOnWith 1 (fun t => (F.flow z t).1) (Icc 0 T) := by
  apply (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => (F.ode z t ht).fst)
  intro t _
  exact_mod_cast (norm_velocity_lt_one (F.flow z t).2).le

lemma PhaseFlowOn.continuousOn_joint {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T)
    (hE : ContinuousOn E (Icc 0 T ×ˢ (univ : Set Vec)))
    (hB : ContinuousOn B (Icc 0 T ×ˢ (univ : Set Vec))) :
    ContinuousOn (fun p : ℝ × Phase => F.flow p.2 p.1)
      (Icc 0 T ×ˢ (univ : Set Phase)) := by
  intro p hp
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod (isCompact_closedBall p.2.1 (T+1))).bddAbove_image
    ((hE.norm.add hB.norm).mono (prod_mono Subset.rfl (subset_univ _)))
  let L : ℝ≥0 := ⟨max 1 M, zero_le_one.trans (le_max_left _ _)⟩
  have hpos (z : Phase) (hz : z ∈ ball p.2 (1/2:ℝ)) (t : ℝ) (ht : t ∈ Icc 0 T) :
      (F.flow z t).1 ∈ closedBall p.2.1 (T+1) := by
    have hh := (F.position_lipschitz z).dist_le_mul t ht 0 ⟨le_rfl,hT⟩
    simp only [F.initial,NNReal.coe_one,one_mul,Real.dist_eq,sub_zero,abs_of_nonneg ht.1] at hh
    have hz' : dist z.1 p.2.1 < (1/2:ℝ) := (le_max_left _ _).trans_lt hz
    exact (dist_triangle _ z.1 _).trans (add_le_add hh hz'.le) |>.trans (by linarith [ht.2])
  have hLip (z : Phase) (hz : z ∈ ball p.2 (1/2:ℝ)) :
      LipschitzOnWith L (F.flow z) (Icc 0 T) := by
    apply (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (F.ode z)
    intro t ht
    apply NNReal.coe_le_coe.mp
    change ‖lorentzField E B (t,F.flow z t)‖ ≤ max 1 M
    rw [lorentzField,lorentzPhase,Prod.norm_def]
    apply max_le
    · exact (norm_velocity_lt_one _).le.trans (le_max_left _ _)
    · calc
        _ ≤ ‖E (t,(F.flow z t).1)‖+‖B (t,(F.flow z t).1)‖ := by
          exact (norm_add_le _ _).trans (add_le_add le_rfl
            ((norm_cross_le _ _).trans
              (mul_le_of_le_one_left (norm_nonneg _) (norm_velocity_lt_one _).le)))
        _ ≤ M := hM ⟨(t,(F.flow z t).1),⟨ht,hpos z hz t ht⟩,rfl⟩
        _ ≤ _ := le_max_right _ _
  have hc : ContinuousAt (fun z => F.flow z p.1) p.2 := (F.label p.2 p.1 hp.1).continuousAt
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ,hδ,hlabel⟩ := Metric.continuousAt_iff.mp hc (ε/2) (by positivity)
  refine ⟨min (1/2:ℝ) (min δ (ε/(2*((L:ℝ)+1)))),by positivity,?_⟩
  intro q hq hdist
  have hd₁ : dist q.1 p.1 < ε/(2*((L:ℝ)+1)) :=
    (le_max_left _ _).trans_lt (hdist.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hd₂ : dist q.2 p.2 < δ :=
    (le_max_right _ _).trans_lt (hdist.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hqball : q.2 ∈ ball p.2 (1/2:ℝ) :=
    (le_max_right _ _).trans_lt (hdist.trans_le (min_le_left _ _))
  have hh : (L:ℝ)*dist q.1 p.1 < ε/2 := by
    have hh := (lt_div_iff₀ (show 0<2*((L:ℝ)+1) by positivity)).mp hd₁
    nlinarith [dist_nonneg (x := q.1) (y := p.1)]
  exact (dist_triangle _ (F.flow q.2 p.1) _).trans_lt
    (add_lt_add_of_le_of_lt ((hLip q.2 hqball).dist_le_mul q.1 hq.1 p.1 hp.1)
      (hlabel hd₂) |>.trans_le (by linarith))

lemma compact_hit_labels {A : Type*} [TopologicalSpace A] [T2Space A]
    {S : Set A} {T : ℝ} (hS : IsCompact S) {H : Set (ℝ × ℝ × A)}
    (hH : IsClosed H) :
    IsCompact {a | a ∈ S ∧ ∃ t ∈ Icc 0 T, ∃ s ∈ Icc 0 T, (t,s,a) ∈ H} := by
  have hc : IsCompact ((Icc 0 T ×ˢ (Icc 0 T ×ˢ S)) ∩ H) :=
    (isCompact_Icc.prod (isCompact_Icc.prod hS)).inter_right hH
  have heq : (fun p : ℝ × ℝ × A => p.2.2) '' ((Icc 0 T ×ˢ (Icc 0 T ×ˢ S)) ∩ H) =
      {a | a ∈ S ∧ ∃ t ∈ Icc 0 T, ∃ s ∈ Icc 0 T, (t,s,a) ∈ H} := by
    ext a
    constructor
    · rintro ⟨⟨t,s,b⟩,⟨⟨ht,hs,hb⟩,hh⟩,rfl⟩
      exact ⟨hb,t,ht,s,hs,hh⟩
    · rintro ⟨ha,t,ht,s,hs,hh⟩
      exact ⟨(t,s,a),⟨⟨ht,hs,ha⟩,hh⟩,rfl⟩
  rw [← heq]
  exact hc.image (continuous_snd.comp continuous_snd)

end RVM

end

end OAI
