import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.WeakFieldLimitBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.LocalArzelaAscoliBarrier
import OAI.Analysis.CoulombIonization.FieldAnalysis.SphericalMeanFieldBarrier

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom

lemma rotation_spatial_integral {v : Space → ℝ} (hm : Measurable v) (hi : Integrable v) :
    Integrable (fun x => sphereMean v x) ∧ (∫ x, sphereMean v x) = ∫ x, v x := by
  have he (g : SpatialRotation) (w : Space → ℝ) :
      (∫ x, w (rotate g x)) = ∫ x, w x :=
    (rotate g).measurePreserving.integral_comp (rotate g).toHomeomorph.measurableEmbedding w
  have hip : Integrable (fun q : SpatialRotation × Space => v (rotate q.1 q.2))
      (rotationMeasure.prod volume) := by
    apply (integrable_prod_iff (hm.comp rotate_continuous.measurable).aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ (fun g => (rotate g).measurePreserving.integrable_comp_of_integrable hi),?_⟩
    change Integrable (fun g : SpatialRotation => ∫ x, (fun z => ‖v z‖) (rotate g x)) rotationMeasure
    have hh : (fun g : SpatialRotation => ∫ x, (fun z => ‖v z‖) (rotate g x)) =
        fun _ => ∫ x, ‖v x‖ := funext (fun g => he g (fun z => ‖v z‖))
    rw [hh]
    exact integrable_const _
  refine ⟨hip.swap.integral_prod_left,?_⟩
  change (∫ x, ∫ g : SpatialRotation, v (rotate g x) ∂rotationMeasure) = _
  rw [←integral_integral_swap (f := fun g x => v (rotate g x)) hip]
  simp only [he,integral_const,probReal_univ,smul_eq_mul,one_mul]

lemma sphereMean_indicator {K : Set Space} {u : Space → ℝ}
    (hrot : ∀ g : SpatialRotation, ∀ x, rotate g x ∈ K ↔ x ∈ K) (x : Space) :
    sphereMean (K.indicator u) x = K.indicator (sphereMean u) x := by
  by_cases hx : x ∈ K
  · rw [indicator_of_mem hx]
    apply integral_congr_ae
    exact ae_of_all _ (fun g => indicator_of_mem ((hrot g x).mpr hx) _)
  · rw [indicator_of_notMem hx]
    change (∫ g : SpatialRotation, K.indicator u (rotate g x) ∂rotationMeasure) = 0
    have he : (fun g : SpatialRotation => K.indicator u (rotate g x)) = 0 := by
      funext g
      exact indicator_of_notMem (fun hg => hx ((hrot g x).mp hg)) _
    rw [he]
    exact integral_zero SpatialRotation ℝ

theorem rotation_annular_L1 {K : Set Space} (hK : MeasurableSet K)
    (hfin : volume K ≠ ⊤)
    (hrot : ∀ g : SpatialRotation, ∀ x, rotate g x ∈ K ↔ x ∈ K)
    {u : Space → ℝ} (hm : Measurable u) (hi : IntegrableOn u K)
    {M L : ℝ} (hM : 0 ≤ M) (hcap : ∀ x ∈ K, u x ≤ M)
    (hmean : ∀ x ∈ K, -L ≤ sphereMean u x) :
    (∫ x in K, |u x|) ≤ (2*M+L)*(volume K).toReal := by
  have hv := hi.integrable_indicator hK
  have hrotInt := rotation_spatial_integral (hm.indicator hK) hv
  have he : sphereMean (K.indicator u) = K.indicator (sphereMean u) :=
    funext (sphereMean_indicator hrot)
  rw [he] at hrotInt
  have hsmi : IntegrableOn (sphereMean u) K :=
    (integrable_indicator_iff hK).mp hrotInt.1
  have htotal : (∫ x in K, sphereMean u x) = ∫ x in K, u x := by
    simpa only [integral_indicator hK] using hrotInt.2
  have hconst : IntegrableOn (fun _ : Space => -L) K := integrableOn_const hfin
  have hlow : -L * (volume K).toReal ≤ ∫ x in K, u x := by
    rw [←htotal]
    have hh := integral_mono_ae hconst hsmi (ae_restrict_of_forall_mem hK hmean)
    simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hh
  have hupper : (∫ x in K, |u x|) ≤ 2*M*(volume K).toReal-∫ x in K, u x := by
    have hc : IntegrableOn (fun _ : Space => 2*M) K := integrableOn_const hfin
    have hh := integral_mono_ae hi.abs (hc.sub hi) (ae_restrict_of_forall_mem hK (fun x hx => by
      change |u x| ≤ 2*M-u x
      rw [abs_le]
      constructor <;> linarith [hcap x hx, hM]))
    change (∫ x in K, |u x|) ≤ ∫ x in K, 2*M-u x at hh
    rw [integral_sub hc hi] at hh
    simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hh
  linarith only [hlow,hupper]

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom

lemma compact_away_zero_annulus {K : Set Space} (hK : IsCompact K) (h0 : K ⊆ {0}ᶜ) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ K ⊆ {x : Space | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} := by
  rcases K.eq_empty_or_nonempty with he | hn
  · refine ⟨1,1,by norm_num,by norm_num,?_⟩
    rw [he]
    exact empty_subset _
  · obtain ⟨z,hz,hmin⟩ := hK.exists_isMinOn hn continuous_norm.continuousOn
    obtain ⟨b,hb,hmax⟩ := hK.isBounded.exists_pos_norm_le
    refine ⟨‖z‖,b,norm_pos_iff.mpr (h0 hz),hb,?_⟩
    exact fun x hx => ⟨hmin hx,hmax x hx⟩

lemma compact_closed_annulus (a b : ℝ) :
    IsCompact {x : Space | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} := by
  apply (isCompact_closedBall (0:Space) b).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))
  exact fun x hx => by simpa only [mem_closedBall,dist_zero_right,mem_ofPred_eq] using hx.2

lemma screened_field_continuousOn {ρ : Space → ℝ} {Z M : ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) (hM : 0 ≤ M)
    (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ M) :
    ContinuousOn (fun x => Z/‖x‖-tfPotential ρ x) {0}ᶜ := by
  apply (continuousOn_const.div continuous_norm.continuousOn (fun x hx => norm_ne_zero_iff.mpr hx)).sub
  exact (bounded_L1_potential_lipschitz hm hi hM hn hb).continuous.continuousOn

lemma screened_field_measurable {ρ : Space → ℝ} {Z M : ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) (hM : 0 ≤ M)
    (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ M) :
    Measurable (fun x => Z/‖x‖-tfPotential ρ x) :=
  (measurable_const.div measurable_norm).sub
    (bounded_L1_potential_lipschitz hm hi hM hn hb).continuous.measurable

theorem screened_field_local_L1 {ρ : ℕ → Space → ℝ} {Z : ℕ → ℝ} {Q : ℝ}
    (hm : ∀ n, Measurable (ρ n)) (hi : ∀ n, Integrable (ρ n))
    (hn : ∀ n x, 0 ≤ ρ n x) (hglobal : ∀ n, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ρ n x ≤ M)
    (hQ : 0 ≤ Q) (hq : ∀ n, |Z n-∫ x, ρ n x| ≤ Q)
    (hcap : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ n x, x ∈ K → Z n/‖x‖-tfPotential (ρ n) x ≤ M)
    {K : Set Space} (hK : IsCompact K) (hK0 : K ⊆ {0}ᶜ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n, (∫ x in K, |Z n/‖x‖-tfPotential (ρ n) x|) ≤ A := by
  obtain ⟨a,b,ha,_hb,hKS⟩ := compact_away_zero_annulus hK hK0
  let S : Set Space := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}
  have hS := compact_closed_annulus a b
  have hS0 : S ⊆ {0}ᶜ := fun _ hx => norm_pos_iff.mp (ha.trans_le hx.1)
  obtain ⟨M,hM,hc⟩ := hcap S hS hS0
  let A := (2*M+Q/a)*(volume S).toReal
  refine ⟨A,by dsimp [A]; positivity,?_⟩
  intro n
  obtain ⟨B,hB,hρB⟩ := hglobal n
  have hcont := screened_field_continuousOn (Z := Z n) (hm n) (hi n) hB (hn n) hρB
  have hii : IntegrableOn (fun z => Z n/‖z‖-tfPotential (ρ n) z) S :=
    (hcont.mono hS0).integrableOn_compact hS
  have hmean : ∀ x ∈ S, -(Q/a) ≤ sphereMean (fun z => Z n/‖z‖-tfPotential (ρ n) z) x := by
    intro x hx
    have hnx : 0 < ‖x‖ := ha.trans_le hx.1
    have hbr := (sphereMean_field_bracket (hm n) (hi n) hB (hn n) hρB (Z n) (hS0 hx)).1
    have hres := (abs_le.mp (hq n)).1
    have hl := div_le_div_of_nonneg_left hQ ha hx.1
    have hr := div_le_div_of_nonneg_right hres hnx.le
    rw [neg_div] at hr
    linarith
  have hrot : ∀ g : SpatialRotation, ∀ x, rotate g x ∈ S ↔ x ∈ S := by
    intro g x
    simp only [S,mem_ofPred_eq,(rotate g).norm_map]
  have hbound := rotation_annular_L1 hS.measurableSet hS.measure_lt_top.ne hrot
    (screened_field_measurable (Z := Z n) (hm n) (hi n) hB (hn n) hρB) hii hM (hc n) hmean
  exact (setIntegral_mono_set hii.abs (ae_of_all _ (fun _ => abs_nonneg _))
    (ae_of_all _ (fun _ hx => hKS hx))).trans hbound

theorem screened_field_normal_family {ρ : ℕ → Space → ℝ} {Z : ℕ → ℝ} {Q : ℝ}
    (hm : ∀ n, Measurable (ρ n)) (hi : ∀ n, Integrable (ρ n))
    (hn : ∀ n x, 0 ≤ ρ n x) (hglobal : ∀ n, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ρ n x ≤ M)
    (hQ : 0 ≤ Q) (hq : ∀ n, |Z n-∫ x, ρ n x| ≤ Q)
    (hcap : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ n x, x ∈ K → Z n/‖x‖-tfPotential (ρ n) x ≤ M)
    (hρcap : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ n x, x ∈ K → ρ n x ≤ M) :
    ∃ u : Space → ℝ, ContinuousOn u {0}ᶜ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ K, IsCompact K → K ⊆ {0}ᶜ →
        TendstoUniformlyOn (fun n x => Z (φ n)/‖x‖-tfPotential (ρ (φ n)) x) u atTop K := by
  apply punctured_poisson_normal_family (f := fun n x => Z n/‖x‖-tfPotential (ρ n) x) (ρ := ρ) _ hm hn _
  · intro K hK hK0
    obtain ⟨M,hM,hMbound⟩ := hρcap K hK hK0
    obtain ⟨A,hA,hAbound⟩ := screened_field_local_L1 hm hi hn hglobal hQ hq hcap hK hK0
    exact ⟨M,A,hM,hA,hMbound,hAbound⟩
  · intro n
    obtain ⟨M,hM,hMb⟩ := hglobal n
    exact screened_field_continuousOn (hm n) (hi n) hM (hn n) hMb
  · intro n
    obtain ⟨M,hM,hMb⟩ := hglobal n
    exact screened_field_punctured_poisson (hm n) (hi n) hM (hn n) hMb

end CoulombAnalysis

end

end OAI
