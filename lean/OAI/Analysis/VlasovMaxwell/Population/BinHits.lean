import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.ReceiverQ
import OAI.Analysis.VlasovMaxwell.Regularity.RealJointEnergyBudget
import OAI.Analysis.VlasovMaxwell.Continuation.PrefixParticle

namespace OAI

noncomputable section

namespace RVM

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
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal


def closedBinHits (α : Phase → ℝ → Phase) (zX : Phase) (B : ClosedConeBin)
    (S : Set Phase) (a b c d : ℝ) (z : Phase) : Set ℝ :=
  {r | z∈S ∧ r∈Icc c d ∧ ∃ t∈Icc a b, InClosedConeBin α zX B t r z}

lemma PhaseFlowOn.compact_closedBinHits_labels {s : Solution} {T a b c d : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (hJ : Icc a b ⊆ Icc 0 T) (hC : Icc c d ⊆ Icc 0 T) :
    IsCompact {z | (closedBinHits F.flow zX B S a b c d z).Nonempty} := by
  convert F.compact_closed_bin_hit_labels (a:=a) (b:=b) (c:=c) (d:=d) hs hT zX B hS using 1
  ext z
  constructor
  · rintro ⟨r,hz,hr,t,ht,hbin⟩
    exact ⟨hz,t,hJ ht,r,hC hr,ht,hr,hbin⟩
  · rintro ⟨hz,t,_,r,_,ht,hr,hbin⟩
    exact ⟨r,hz,hr,t,ht,hbin⟩

lemma PhaseFlowOn.averaged_cell_occupation_interior {s : Solution} {T a b p D : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (hCT : Icc a b ⊆ Icc (0:ℝ) T) {H : Phase → Set ℝ}
    {Z : Set Phase} (hZ : MeasurableSet Z) {G : Set (ℝ × Phase)}
    (hD : ∀ z, volume (H z) ≤ ENNReal.ofReal D)
    (hz : ∀ z, (H z).Nonempty → z∈Z)
    (hmom : ∀ t∈Ioo a b, ∀ z∈Z, p ≤ q (F.flow z t).2)
    (hG : ∀ t∈Ioo a b, ∀ z∈Z, (t,F.flow z t)∈G) :
    ENNReal.ofReal (b-a) * ENNReal.ofReal p * labelOccupation (fun z => s.f (0,z)) H ≤
      ENNReal.ofReal D * ∫⁻ t in Icc a b, ∫⁻ z : Phase,
        G.indicator (fun q => ENNReal.ofReal (RVM.q q.2.2*s.f q)) (t,z) := by
  have hbnd := lintegral_mono_ae (μ:=volume.restrict (Ioo a b))
    (ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht =>
      F.restricted_label_mass_bound hs (hCT (Ioo_subset_Icc_self ht)) hZ (hmom t ht) (hG t ht)))
  rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo] at hbnd
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ:=volume) (a:=a) (b:=b))] at hbnd
  have hocc := labelOccupation_le_duration_mass hZ hD hz (f₀:=fun z => s.f (0,z))
  calc
    _ ≤ ENNReal.ofReal (b-a)*ENNReal.ofReal p*(ENNReal.ofReal D*
        ∫⁻ z in Z, ENNReal.ofReal (s.f (0,z))) := mul_le_mul' le_rfl hocc
    _ = ENNReal.ofReal D*((ENNReal.ofReal p * ∫⁻ z in Z, ENNReal.ofReal (s.f (0,z))) *
        ENNReal.ofReal (b-a)) := by ac_rfl
    _ ≤ _ := by gcongr

lemma dyadicWindow_momentum_enlarged {Q : ℝ} {n : ℕ} (hQ : 0 < Q)
    (hlo : (2:ℝ)^n/4 ≤ Q) (hhi : Q ≤ 4*(2:ℝ)^n) :
    DyadicWindow 4 n Q⁻¹ := by
  norm_num [DyadicWindow]
  rw [← div_eq_mul_inv,le_div_iff₀ hQ,div_le_iff₀ hQ]
  constructor <;> nlinarith [pow_pos (show (0:ℝ)<2 by norm_num) n]

lemma dyadicWindow_angle_enlarged {r : ℝ} {n : ℕ}
    (hlo : (2:ℝ)⁻¹^n/4 ≤ r) (hhi : r ≤ 6*(2:ℝ)⁻¹^n) :
    DyadicWindow 4 n r := by
  have he : (2:ℝ)^n*(2:ℝ)⁻¹^n=1 := by
    rw [← mul_pow]; norm_num
  have hl := mul_le_mul_of_nonneg_left hlo (show 0 ≤ (2:ℝ)^n by positivity)
  have hh := mul_le_mul_of_nonneg_left hhi (show 0 ≤ (2:ℝ)^n by positivity)
  norm_num [DyadicWindow]
  constructor <;> nlinarith

lemma small_closed_bin_hit_geometry {α : Phase → ℝ → Phase} {zX z : Phase}
    {B : ClosedConeBin} {t r φ : ℝ} (hbin : InClosedConeBin α zX B t r z)
    (hr : 0 < B.rmin) (hφ : 0 < φ)
    (hd : B.dmax ≤ φ^2/32) (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2)
    (hw : 4 ≤ φ*B.wmin) :
    ∃ n : Vec, ‖n‖=1 ∧ (α zX t).1-(α z r).1=(t-r) • n ∧
      ‖velocity (α zX t).2-n‖ ≤ 4*φ ∧
      φ/2 ≤ ‖velocity (α z r).2-velocity (α zX t).2‖ ∧
      ‖velocity (α z r).2-velocity (α zX t).2‖ ≤ 5*φ := by
  have hR : 0 < t-r := hr.trans_le hbin.2.1.1
  have hb := (inClosedConeBin_iff hR).mp hbin
  let n : Vec := (t-r)⁻¹ • ((α zX t).1-(α z r).1)
  have hn : ‖n‖=1 := by
    dsimp only [n]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR),← hb.1,
      inv_mul_cancel₀ hR.ne']
  have hgeom : (α zX t).1-(α z r).1=(t-r) • n := by
    dsimp only [n]
    rw [smul_smul,mul_inv_cancel₀ hR.ne',one_smul]
  have hsrc : ‖n-velocity (α z r).2‖ ≤ φ/4 := by
    have hid := cone_angle_identity (α z r).2 n hn
    have hbound := hb.2.2.2.2.1.2.trans hd
    nlinarith [sq_nonneg ((q (α z r).2)⁻¹),norm_nonneg (n-velocity (α z r).2)]
  have hlo : φ^2/2 ≤ 1-dot n (velocity (α zX t).2) :=
    hDlo.trans hb.2.2.2.2.2.1.1
  have hhi : 1-dot n (velocity (α zX t).2) ≤ 8*φ^2 :=
    hb.2.2.2.2.2.1.2.trans hDhi
  have hinv : (q (α zX t).2)⁻¹ ≤ φ/4 := by
    rw [inv_le_iff_one_le_mul₀ (q_pos _)]
    have hh := mul_le_mul_of_nonneg_left hb.2.2.2.1.1 hφ.le
    nlinarith
  have hrec : ‖velocity (α zX t).2-n‖ ≤ 4*φ := by
    rw [norm_sub_rev]
    have hid := cone_angle_identity (α zX t).2 n hn
    nlinarith [sq_nonneg ((q (α zX t).2)⁻¹),norm_nonneg (n-velocity (α zX t).2)]
  exact ⟨n,hn,hgeom,hrec,actual_small_sector_velocity hn hφ.le hinv hsrc hlo hhi⟩

lemma PhaseFlowOn.small_closed_bin_cell_data {s : Solution}
    {T M A P L lo hi a b c d massScale φ C p : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (B : ClosedConeBin) {S : Set Phase}
    (hlo0 : 0 ≤ lo) (hhiT : hi ≤ T)
    (hJ : Icc a b ⊆ Icc lo hi) (hC : Icc c d ⊆ Icc lo hi)
    (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
    (hm : 0 < massScale) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hconst : 128 ≤ C)
    (hlen : hi-lo ≤ (C*(P/massScale)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2)
    (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
    (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
    (hr : 0 < B.rmin) (hd : B.dmax ≤ φ^2/32)
    (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2) (hw : 4 ≤ φ*B.wmin)
    (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
    (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L) :
    ∀ z, (closedBinHits F.flow zX B S a b c d z).Nonempty →
      volume (closedBinHits F.flow zX B S a b c d z) ≤ ENNReal.ofReal (40*B.rmax) ∧
      ∀ t∈Icc c d, p/256 ≤ q (F.flow z t).2 ∧ q (F.flow z t).2 ≤ p/16 ∧
        φ/4 ≤ ‖velocity (F.flow z t).2-velocity (F.flow zX t).2‖ ∧
        ‖velocity (F.flow z t).2-velocity (F.flow zX t).2‖ ≤ 6*φ := by
  let U := Icc lo hi
  have hUT : U ⊆ Icc 0 T := Icc_subset_Icc hlo0 hhiT
  have hCT : Icc c d ⊆ Icc 0 T := hC.trans hUT
  have hstable (z : Phase) (H : IncrementBootstrap (fun t => (F.flow z t).2) T M A P L)
      (r : ℝ) (hr : r∈U) (hqm : massScale ≤ q (F.flow z r).2) :=
    H.velocity_stability_scale hlo0 hhiT hr ((F.continuousOn_time z).snd.mono hUT)
      hM hA hP hL hm hφ hφ1 hconst hqm hlen
  intro z hz
  obtain ⟨r₀,hzS,hr₀,t₀,ht₀,hbin₀⟩ := hz
  have hsource := hstable z (HZ z hzS) r₀ (hC hr₀) (hmq.trans hbin₀.2.2.1.1)
  have hreceiver := hstable zX HX t₀ (hJ ht₀) (hmw.trans hbin₀.2.2.2.1.1)
  obtain ⟨n₀,_,_,_,hsep₀,hupper₀⟩ := small_closed_bin_hit_geometry hbin₀ hr hφ hd hDlo hDhi hw
  have href (t : ℝ) (ht : t∈U) :
      ‖velocity (F.flow z t).2-velocity (F.flow zX t).2-
        (velocity (F.flow z r₀).2-velocity (F.flow zX t₀).2)‖ ≤ φ/16 := by
    have hh := relative_ref_triangle (hsource t ht).2.1 (hreceiver t ht).2.1
    linarith
  constructor
  · have hsep (r : ℝ) (hrH : r∈closedBinHits F.flow zX B S a b c d z) :
        ‖(F.flow z r).1-(F.flow zX r).1‖ ≤ 5*B.rmax*φ := by
      obtain ⟨_,hrC,t,htJ,hbin⟩ := hrH
      obtain ⟨n,_,hgeom,hangle,_,_⟩ := small_closed_bin_hit_geometry hbin hr hφ hd hDlo hDhi hw
      have hrt : r ≤ t := by linarith [hbin.2.1.1]
      have hsub : Icc r t ⊆ U := Icc_subset_Icc (hC hrC).1 (hJ htJ).2
      have hh := retarded_same_time_separation hrt
        (fun u hu => ((F.ode zX u (hUT (hsub hu))).mono (hsub.trans hUT)).fst)
        (fun u hu => velocity_ref_triangle (hreceiver u (hsub hu)).2.1
          (hreceiver t (hJ htJ)).2.1 hangle) hgeom
      have hrad : 0 ≤ B.rmax := (sub_nonneg.mpr hrt).trans hbin.2.1.2
      calc
        _ ≤ (4*φ+2*(φ/32))*(t-r) := hh
        _ ≤ (5*φ)*B.rmax := mul_le_mul (by linarith) hbin.2.1.2
          (sub_nonneg.mpr hrt) (by positivity)
        _ = _ := by ring
    have hh := stable_cell_duration (convex_Icc c d)
      (show closedBinHits F.flow zX B S a b c d z ⊆ Icc c d from fun _ h => h.2.1)
      (half_pos hφ) hsep₀ ((F.continuousOn_time zX).fst.mono hCT)
      ((F.continuousOn_time z).fst.mono hCT)
      (fun r hr => ((F.ode zX r (hCT (interior_subset hr))).mono hCT).hasDerivAt
        (mem_interior_iff_mem_nhds.mp hr) |>.fst)
      (fun r hr => ((F.ode z r (hCT (interior_subset hr))).mono hCT).hasDerivAt
        (mem_interior_iff_mem_nhds.mp hr) |>.fst)
      (fun r hr => (href r (hC (interior_subset hr))).trans (by linarith)) hsep
    convert hh using 1
    congr 1
    field_simp; ring
  · intro t ht
    have hq := (hsource t (hC ht)).2.2
    have hqlo := hqmin.trans hbin₀.2.2.1.1
    have hqhi := hbin₀.2.2.1.2.trans hqmax
    refine ⟨by linarith,by linarith,?_,?_⟩
    · have hn := norm_sub_norm_le
        (velocity (F.flow z r₀).2-velocity (F.flow zX t₀).2)
        (velocity (F.flow z t).2-velocity (F.flow zX t).2)
      have hh : ‖(velocity (F.flow z r₀).2-velocity (F.flow zX t₀).2)-
          (velocity (F.flow z t).2-velocity (F.flow zX t).2)‖ ≤ φ/16 := by
        rw [norm_sub_rev]
        exact href t (hC ht)
      linarith
    · have hn := norm_sub_norm_le
        (velocity (F.flow z t).2-velocity (F.flow zX t).2)
        (velocity (F.flow z r₀).2-velocity (F.flow zX t₀).2)
      linarith [href t (hC ht)]

lemma PhaseFlowOn.small_closed_bin_cell_payment {s : Solution}
    {T M A P L lo hi a b c d massScale φ C p : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (np nf : ℕ) (hp : p=64*(2:ℝ)^np) (hφeq : φ=(2:ℝ)⁻¹^nf)
    (hlo0 : 0 ≤ lo) (hhiT : hi ≤ T)
    (hJ : Icc a b ⊆ Icc lo hi) (hC : Icc c d ⊆ Icc lo hi)
    (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
    (hm : 0 < massScale) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hconst : 128 ≤ C)
    (hlen : hi-lo ≤ (C*(P/massScale)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2)
    (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
    (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
    (hr : 0 < B.rmin) (hd : B.dmax ≤ φ^2/32)
    (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2) (hw : 4 ≤ φ*B.wmin)
    (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
    (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L) :
    ENNReal.ofReal (d-c) * ENNReal.ofReal (p/256) *
        labelOccupation (fun z => s.f (0,z)) (closedBinHits F.flow zX B S a b c d) ≤
      ENNReal.ofReal (40*B.rmax) * ∫⁻ t in Icc c d, ∫⁻ z : Phase,
        (sameTimeBudgetSet F.flow zX T 4 (np,nf)).indicator
          (fun q => ENNReal.ofReal (RVM.q q.2.2*s.f q)) (t,z) := by
  have hUT : Icc lo hi ⊆ Icc 0 T := Icc_subset_Icc hlo0 hhiT
  have hCT := hC.trans hUT
  have hdata := F.small_closed_bin_cell_data zX B hlo0 hhiT hJ hC hM hA hP hL
    hm hφ hφ1 hconst hlen hqmin hqmax hmq hmw hr hd hDlo hDhi hw HX HZ
  have hlabels := F.compact_closedBinHits_labels hs hT zX B hS (hJ.trans hUT) hCT
  apply F.averaged_cell_occupation_interior hs hCT hlabels.measurableSet
  · intro z
    by_cases hz : (closedBinHits F.flow zX B S a b c d z).Nonempty
    · exact (hdata z hz).1
    · simp only [not_nonempty_iff_eq_empty.mp hz,measure_empty,zero_le]
  · exact fun _ hz => hz
  · exact fun t ht z hz => ((hdata z hz).2 t (Ioo_subset_Icc_self ht)).1
  · intro t ht z hz
    obtain ⟨hqlo,hqhi,hvlo,hvhi⟩ := (hdata z hz).2 t (Ioo_subset_Icc_self ht)
    refine ⟨⟨?_,?_⟩,dyadicWindow_momentum_enlarged (q_pos _) ?_ ?_,
      dyadicWindow_angle_enlarged ?_ ?_⟩
    · have hct : 0 ≤ c := (hCT (left_mem_Icc.mpr (le_of_lt (ht.1.trans ht.2)))).1
      exact hct.trans_lt ht.1
    · have hdt : d ≤ T := (hCT (right_mem_Icc.mpr (le_of_lt (ht.1.trans ht.2)))).2
      exact ht.2.trans_le hdt
    · rw [hp] at hqlo
      linarith
    · rw [hp] at hqhi
      linarith
    · simpa only [← hφeq] using hvlo
    · simpa only [← hφeq] using hvhi

lemma sameTimeBudget_energy_le_joint {s : Solution} {α : Phase → ℝ → Phase}
    {zX : Phase} {T a b I : ℝ} {k : ℕ} {n : ℕ × ℕ}
    (hJ : Icc a b ⊆ Icc (0:ℝ) T) (hI : 0 < I) :
    (∫⁻ t in Icc a b, ∫⁻ z : Phase,
      (sameTimeBudgetSet α zX T k n).indicator
        (fun q => ENNReal.ofReal (RVM.q q.2.2*s.f q)) (t,z)) ≤
      ENNReal.ofReal I * jointEnergyBudget s α zX T k a b I n := by
  rw [jointEnergyBudget_eq k hJ n,← mul_assoc,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr hI) ENNReal.ofReal_ne_top,one_mul]
  exact lintegral_mono fun t => lintegral_mono fun z => le_add_right le_rfl

lemma closedBinHits_clip_receiver (α : Phase → ℝ → Phase) (zX : Phase)
    (B : ClosedConeBin) (S : Set Phase) (a b c d : ℝ) :
    closedBinHits α zX B S a b c d =
      closedBinHits α zX B S (max a c) (min b (d+B.rmax)) c d := by
  funext z
  ext r
  constructor
  · rintro ⟨hz,hr,t,ht,hbin⟩
    have hrt : r ≤ t := by
      have hh := hbin.1
      linarith [norm_nonneg ((α zX t).1-(α z r).1)]
    exact ⟨hz,hr,t,⟨max_le ht.1 (hr.1.trans hrt),le_min ht.2 (by
      have hh := hbin.2.1.2
      linarith [hr.2])⟩,hbin⟩
  · rintro ⟨hz,hr,t,ht,hbin⟩
    exact ⟨hz,hr,t,⟨(le_max_left a c).trans ht.1,ht.2.trans (min_le_left _ _)⟩,hbin⟩

lemma PhaseFlowOn.compact_closedBinHits_joint {s : Solution} {T a b c d : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (hJ : Icc a b ⊆ Icc 0 T) (hC : Icc c d ⊆ Icc 0 T) :
    IsCompact {p : ℝ × Phase | p.1∈closedBinHits F.flow zX B S a b c d p.2} := by
  let K : Set (ℝ × ℝ × Phase) := (Icc a b ×ˢ (Icc c d ×ˢ S)) ∩
    {p | InClosedConeBin (prefixFlow F.flow T) zX B p.1 p.2.1 p.2.2}
  have hK : IsCompact K := (isCompact_Icc.prod (isCompact_Icc.prod hS)).inter_right
    (isClosed_inClosedConeBin (F.continuous_prefixFlow hs hT) zX B)
  convert hK.image continuous_snd using 1
  ext p
  constructor
  · rintro ⟨hz,hr,t,ht,hbin⟩
    refine ⟨(t,p),⟨⟨ht,hr,hz⟩,?_⟩,rfl⟩
    change InClosedConeBin (prefixFlow F.flow T) zX B t p.1 p.2
    simpa only [InClosedConeBin,prefixFlow,prefixClamp_eq (hJ ht),
      prefixClamp_eq (hC hr)] using hbin
  · rintro ⟨⟨t,r,z⟩,⟨⟨ht,hr,hz⟩,hbin⟩,rfl⟩
    refine ⟨hz,hr,t,ht,?_⟩
    change InClosedConeBin (prefixFlow F.flow T) zX B t r z at hbin
    simpa only [InClosedConeBin,prefixFlow,prefixClamp_eq (hJ ht),
      prefixClamp_eq (hC hr)] using hbin

lemma PhaseFlowOn.measurable_closedBinHits_duration {s : Solution} {T a b c d : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (hJ : Icc a b ⊆ Icc 0 T) (hC : Icc c d ⊆ Icc 0 T) :
    Measurable fun z => volume (closedBinHits F.flow zX B S a b c d z) :=
  measurable_measure_prodMk_right (F.compact_closedBinHits_joint hs hT zX B hS hJ hC).measurableSet

lemma PhaseFlowOn.closedBinHits_occupation_le_sum {s : Solution} {T a b c d : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    {ι : Type*} (N : Finset ι) (l u : ι → ℝ)
    (hJ : Icc a b ⊆ Icc 0 T) (hC : ∀ i∈N, Icc (l i) (u i) ⊆ Icc 0 T)
    (hcover : Icc c d ⊆ ⋃ i∈N, Icc (l i) (u i)) :
    labelOccupation (fun z => s.f (0,z)) (closedBinHits F.flow zX B S a b c d) ≤
      ∑ i∈N, labelOccupation (fun z => s.f (0,z))
        (closedBinHits F.flow zX B S a b (l i) (u i)) := by
  have hfm : Measurable (fun z : Phase => ENNReal.ofReal (s.f (0,z))) :=
    (hs.f_smooth.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨⟨le_rfl,hT⟩,mem_univ _⟩)).measurable.ennreal_ofReal
  have hsub (z : Phase) : closedBinHits F.flow zX B S a b c d z ⊆
      ⋃ i∈N, closedBinHits F.flow zX B S a b (l i) (u i) z := by
    rintro r ⟨hz,hr,t,ht,hbin⟩
    obtain ⟨i,hi,hrC⟩ := mem_iUnion₂.mp (hcover hr)
    exact mem_iUnion₂.mpr ⟨i,hi,hz,hrC,t,ht,hbin⟩
  unfold labelOccupation
  rw [← lintegral_finsetSum (f := fun i z => ENNReal.ofReal (s.f (0,z)) *
    volume (closedBinHits F.flow zX B S a b (l i) (u i) z)) N (fun i hi => hfm.mul
    (F.measurable_closedBinHits_duration hs hT zX B hS hJ (hC i hi)))]
  apply lintegral_mono
  intro z
  calc
    _ ≤ ENNReal.ofReal (s.f (0,z))*∑ i∈N,
        volume (closedBinHits F.flow zX B S a b (l i) (u i) z) :=
      mul_le_mul' le_rfl ((measure_mono (hsub z)).trans (measure_biUnion_finset_le _ _))
    _ = _ := Finset.mul_sum _ _ _

lemma PhaseFlowOn.small_closed_bin_cells_payment {s : Solution}
    {T M A P L a b massScale φ C p len aStar bStar I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    {ι : Type*} (N : Finset ι) (l u lo hi : ι → ℝ)
    (np nf : ℕ) (hp : p=64*(2:ℝ)^np) (hφeq : φ=(2:ℝ)⁻¹^nf)
    (hlo0 : ∀ i∈N, 0 ≤ lo i) (hhiT : ∀ i∈N, hi i ≤ T)
    (hJ : ∀ i∈N, Icc (max a (l i)) (min b (u i+B.rmax)) ⊆ Icc (lo i) (hi i))
    (hC : ∀ i∈N, Icc (l i) (u i) ⊆ Icc (lo i) (hi i))
    (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
    (hm : 0 < massScale) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hconst : 128 ≤ C)
    (hstable : ∀ i∈N, hi i-lo i ≤ (C*(P/massScale)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2)
    (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
    (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
    (hr : 0 < B.rmin) (hd : B.dmax ≤ φ^2/32)
    (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2) (hw : 4 ≤ φ*B.wmin)
    (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
    (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L)
    (hlen : ∀ i∈N, u i-l i=len)
    (hdisj : Set.PairwiseDisjoint (↑N) (fun i => Ioc (l i) (u i)))
    (hsub : ∀ i∈N, Ioc (l i) (u i)⊆Icc aStar bStar)
    (hStar : Icc aStar bStar ⊆ Icc 0 T) (hI : 0 < I) :
    ENNReal.ofReal len * ENNReal.ofReal (p/256) *
        (∑ i∈N, labelOccupation (fun z => s.f (0,z))
          (closedBinHits F.flow zX B S a b (l i) (u i))) ≤
      ENNReal.ofReal (40*B.rmax) * ENNReal.ofReal I *
        jointEnergyBudget s F.flow zX T 4 aStar bStar I (np,nf) := by
  let g : ℝ → ℝ≥0∞ := fun t => ∫⁻ z : Phase,
    (sameTimeBudgetSet F.flow zX T 4 (np,nf)).indicator
      (fun q => ENNReal.ofReal (RVM.q q.2.2*s.f q)) (t,z)
  calc
    _ = ∑ i∈N, ENNReal.ofReal len * ENNReal.ofReal (p/256) *
        labelOccupation (fun z => s.f (0,z))
          (closedBinHits F.flow zX B S a b (l i) (u i)) := Finset.mul_sum _ _ _
    _ ≤ ∑ i∈N, ENNReal.ofReal (40*B.rmax) * ∫⁻ t in Icc (l i) (u i), g t := by
      apply Finset.sum_le_sum
      intro i hiN
      rw [closedBinHits_clip_receiver]
      exact hlen i hiN ▸ F.small_closed_bin_cell_payment hs hT zX B hS np nf hp hφeq
        (hlo0 i hiN) (hhiT i hiN) (hJ i hiN) (hC i hiN) hM hA hP hL hm hφ hφ1
        hconst (hstable i hiN) hqmin hqmax hmq hmw hr hd hDlo hDhi hw HX HZ
    _ = ENNReal.ofReal (40*B.rmax) * (∑ i∈N, ∫⁻ t in Icc (l i) (u i), g t) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ ENNReal.ofReal (40*B.rmax) * ∫⁻ t in Icc aStar bStar, g t :=
      mul_le_mul' le_rfl (sum_cell_lintegral_le N l u g hdisj hsub)
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul' le_rfl (sameTimeBudget_energy_le_joint hStar hI)

lemma PhaseFlowOn.small_closed_bin_cell_crude {s : Solution}
    {T M A P L lo hi a b c d massScale φ C p : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (t₀ : ℝ) (ht₀ : t₀∈Icc c d) (zX : Phase) (B : ClosedConeBin) {S : Set Phase}
    (hlo0 : 0 ≤ lo) (hhiT : hi ≤ T)
    (hJ : Icc a b ⊆ Icc lo hi) (hC : Icc c d ⊆ Icc lo hi)
    (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
    (hm : 0 < massScale) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hconst : 128 ≤ C)
    (hlen : hi-lo ≤ (C*(P/massScale)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2)
    (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
    (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
    (hr : 0 < B.rmin) (hd : B.dmax ≤ φ^2/32)
    (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2) (hw : 4 ≤ φ*B.wmin)
    (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
    (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L) :
    ENNReal.ofReal (p/256) *
        labelOccupation (fun z => s.f (0,z)) (closedBinHits F.flow zX B S a b c d) ≤
      ENNReal.ofReal (40*B.rmax) * ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) := by
  have hdata := F.small_closed_bin_cell_data zX B hlo0 hhiT hJ hC hM hA hP hL
    hm hφ hφ1 hconst hlen hqmin hqmax hmq hmw hr hd hDlo hDhi hw HX HZ
  apply F.label_occupation_cell_bound hs ((hC.trans (Icc_subset_Icc hlo0 hhiT)) ht₀)
  · intro z
    by_cases hz : (closedBinHits F.flow zX B S a b c d z).Nonempty
    · exact (hdata z hz).1
    · simp only [not_nonempty_iff_eq_empty.mp hz,measure_empty,zero_le]
  · exact fun z hz => ((hdata z hz).2 t₀ ht₀).1



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
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal


lemma closedBinHits_clip_source (α : Phase → ℝ → Phase) (zX : Phase)
    (B : ClosedConeBin) (S : Set Phase) (a b T : ℝ) :
    closedBinHits α zX B S a b 0 T =
      closedBinHits α zX B S a b (max 0 (a-B.rmax)) (min T b) := by
  funext z
  ext r
  constructor
  · rintro ⟨hz,hr,t,ht,hbin⟩
    have hrt : r ≤ t := by
      have hh := hbin.1
      linarith [norm_nonneg ((α zX t).1-(α z r).1)]
    refine ⟨hz,⟨max_le hr.1 ?_,le_min hr.2 (hrt.trans ht.2)⟩,t,ht,hbin⟩
    linarith [hbin.2.1.2,ht.1]
  · rintro ⟨hz,hr,t,ht,hbin⟩
    exact ⟨hz,⟨(le_max_left _ _).trans hr.1,hr.2.trans (min_le_left _ _)⟩,t,ht,hbin⟩

lemma ennreal_sum_le_erase_add {ι : Type*} [DecidableEq ι] (S : Finset ι) (i : ι) (f : ι → ℝ≥0∞) :
    ∑ j∈S, f j ≤ (∑ j∈S.erase i, f j)+f i := by
  classical
  by_cases hi : i∈S
  · exact le_of_eq (Finset.sum_erase_add _ _ hi).symm
  · rw [Finset.erase_eq_self.mpr hi]
    exact le_add_right le_rfl

lemma PhaseFlowOn.small_closed_bin_refined_stable {s : Solution}
    {T M A P L a b massScale φ C p len I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (np nf : ℕ) (hp : p=64*(2:ℝ)^np) (hφeq : φ=(2:ℝ)⁻¹^nf)
    (ha : 0 ≤ a) (hb : b ≤ T) (hlen : 0 < len)
    (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
    (hm : 0 < massScale) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hconst : 128 ≤ C)
    (hstable : 2*len ≤ (C*(P/massScale)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2)
    (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
    (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
    (hr : 0 < B.rmin) (hrmax : 0 ≤ B.rmax) (hrad : B.rmax ≤ len)
    (hd : B.dmax ≤ φ^2/32)
    (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2) (hw : 4 ≤ φ*B.wmin)
    (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
    (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L)
    (hI : 0 < I) :
    ENNReal.ofReal len * ENNReal.ofReal (p/256) *
        labelOccupation (fun z => s.f (0,z)) (closedBinHits F.flow zX B S a b 0 T) ≤
      ENNReal.ofReal (40*B.rmax) *
        (ENNReal.ofReal len * ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) +
          ENNReal.ofReal I * jointEnergyBudget s F.flow zX T 4
            (max 0 (a-B.rmax-len)) (min T (b+len)) I (np,nf)) := by
  classical
  let l := sourceCellLo len
  let u := sourceCellHi T len
  let w := fun i => min T (u i+B.rmax)
  let N := selectedSourceCells T len a b B.rmax
  let last := sourceCellLast T len
  let full := N.erase last
  let O : ℕ → ℝ≥0∞ := fun i => labelOccupation (fun z => s.f (0,z))
    (closedBinHits F.flow zX B S a b (l i) (u i))
  have hgrid (i : ℕ) (hi : i ≤ last) :
      0 ≤ l i ∧ l i ≤ u i ∧ u i ≤ T ∧ u i-l i ≤ len :=
    sourceCell_mem_prefix hT hlen hi
  have hN (i : ℕ) (hi : i∈N) : i ≤ last := by
    have hh := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    omega
  have hfullN (i : ℕ) (hi : i∈full) : i∈N := Finset.mem_of_mem_erase hi
  have hJC (i : ℕ) : Icc (max a (l i)) (min b (u i+B.rmax)) ⊆ Icc (l i) (w i) := by
    intro t ht
    exact ⟨(le_max_right _ _).trans ht.1,
      le_min ((ht.2.trans (min_le_left _ _)).trans hb) (ht.2.trans (min_le_right _ _))⟩
  have hCC (i : ℕ) (hi : i ≤ last) : Icc (l i) (u i) ⊆ Icc (l i) (w i) := by
    intro t ht
    exact ⟨ht.1,le_min (ht.2.trans (hgrid i hi).2.2.1) (by linarith [ht.2])⟩
  have hST (i : ℕ) (hi : i ≤ last) :
      w i-l i ≤ (C*(P/massScale)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2 := by
    have hg := (hgrid i hi).2.2.2
    have hw : w i ≤ u i+B.rmax := min_le_right _ _
    linarith
  have hsum : labelOccupation (fun z => s.f (0,z)) (closedBinHits F.flow zX B S a b 0 T) ≤
      (∑ i∈full, O i)+O last := by
    refine le_trans ?_ (ennreal_sum_le_erase_add N last O)
    rw [closedBinHits_clip_source]
    apply F.closedBinHits_occupation_le_sum hs hT zX B hS N l u (Icc_subset_Icc ha hb)
    · intro i hi
      exact Icc_subset_Icc (hgrid i (hN i hi)).1 (hgrid i (hN i hi)).2.2.1
    · exact selectedSourceCells_cover hlen
  have hpay : ENNReal.ofReal len * ENNReal.ofReal (p/256) * (∑ i∈full, O i) ≤
      ENNReal.ofReal (40*B.rmax) * ENNReal.ofReal I * jointEnergyBudget s F.flow zX T 4
        (max 0 (a-B.rmax-len)) (min T (b+len)) I (np,nf) := by
    apply F.small_closed_bin_cells_payment hs hT zX B hS full l u l w np nf hp hφeq
      (fun i hi => (hgrid i (hN i (hfullN i hi))).1) (fun _ _ => min_le_left _ _)
      (fun i _ => hJC i) (fun i hi => hCC i (hN i (hfullN i hi)))
      hM hA hP hL hm hφ hφ1 hconst (fun i hi => hST i (hN i (hfullN i hi)))
      hqmin hqmax hmq hmw hr hd hDlo hDhi hw HX HZ
    · intro i hi
      apply sourceCell_full hT hlen
      have hn := hN i (hfullN i hi)
      have hne := (Finset.mem_erase.mp hi).1
      omega
    · exact fun i _ j _ hij => sourceCells_pairwise_disjoint hlen hij
    · intro i hi
      exact Ioc_subset_Icc_self.trans (selectedSourceCells_enlargement hT hlen (hfullN i hi))
    · exact Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
    · exact hI
  have hclip : ENNReal.ofReal (p/256) * O last ≤
      ENNReal.ofReal (40*B.rmax) * ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) := by
    dsimp only [O]
    rw [closedBinHits_clip_receiver]
    exact F.small_closed_bin_cell_crude hs (l last) (left_mem_Icc.mpr (hgrid last le_rfl).2.1)
      zX B (hgrid last le_rfl).1 (min_le_left _ _) (hJC last) (hCC last le_rfl)
      hM hA hP hL hm hφ hφ1 hconst (hST last le_rfl)
      hqmin hqmax hmq hmw hr hd hDlo hDhi hw HX HZ
  calc
    _ ≤ ENNReal.ofReal len * ENNReal.ofReal (p/256) * ((∑ i∈full, O i)+O last) :=
      mul_le_mul' le_rfl hsum
    _ = ENNReal.ofReal len * ENNReal.ofReal (p/256) * (∑ i∈full, O i)+
        ENNReal.ofReal len * (ENNReal.ofReal (p/256)*O last) := by ring
    _ ≤ ENNReal.ofReal (40*B.rmax) * ENNReal.ofReal I * jointEnergyBudget s F.flow zX T 4
        (max 0 (a-B.rmax-len)) (min T (b+len)) I (np,nf) +
        ENNReal.ofReal len * (ENNReal.ofReal (40*B.rmax) * ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x))) :=
      add_le_add hpay (mul_le_mul' le_rfl hclip)
    _ = _ := by ring

lemma jointEnergyBudget_mono_interval (s : Solution) (α : Phase → ℝ → Phase)
    (zX : Phase) (T : ℝ) (k : ℕ) {a b c d I : ℝ} (n : ℕ × ℕ)
    (hsub : Icc a b ⊆ Icc c d) :
    jointEnergyBudget s α zX T k a b I n ≤ jointEnergyBudget s α zX T k c d I n := by
  unfold jointEnergyBudget
  exact mul_le_mul' le_rfl (lintegral_mono_set hsub)

lemma stable_source_enlargement {a b T r len I : ℝ} (hr : r ≤ len) (hlen : len ≤ I) :
    Icc (max 0 (a-r-len)) (min T (b+len)) ⊆ Icc (max 0 (a-2*I)) (min T (b+I)) := by
  apply Icc_subset_Icc
  · apply max_le_max le_rfl
    linarith
  · exact min_le_min le_rfl (by linarith)

lemma stable_source_enlargement_length {a b T I : ℝ} (hab : b-a ≤ I) :
    min T (b+I)-max 0 (a-2*I) ≤ 4*I := by
  linarith [min_le_right T (b+I),le_max_right 0 (a-2*I)]

lemma PhaseFlowOn.stable_small_jointBudget_uniform {s : Solution} {T a b I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (hI : 0 < I) (hab : b-a ≤ I) :
    (∑' n : ℕ × ℕ, jointEnergyBudget s F.flow zX T 4
      (max 0 (a-2*I)) (min T (b+I)) I n) ≤
      (3*(4*4+1)^2:ℕ) * ENNReal.ofReal 4 * ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) := by
  exact F.jointEnergyBudget_uniform hs zX 4
    (Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)) hI (by norm_num)
    (stable_source_enlargement_length hab)

lemma occupation_divide_cell {p len r I O E B : ℝ≥0∞}
    (hp : p ≠ 0) (hpfin : p ≠ ⊤) (hl : len ≠ 0) (hlfin : len ≠ ⊤)
    (h : len*p*O ≤ r*(len*E+I*B)) :
    O ≤ r/p*(E+I/len*B) := by
  have hh := mul_le_mul' (le_refl ((len*p)⁻¹)) h
  have hprod : len*p ≠ 0 := mul_ne_zero hl hp
  have hprodfin : len*p ≠ ⊤ := ENNReal.mul_ne_top hlfin hpfin
  rw [← mul_assoc,ENNReal.inv_mul_cancel hprod hprodfin,one_mul] at hh
  calc
    O ≤ (len*p)⁻¹*(r*(len*E+I*B)) := hh
    _ = r/p*(E+I/len*B) := by
      rw [ENNReal.mul_inv (Or.inl hl) (Or.inl hlfin),mul_add,div_eq_mul_inv,div_eq_mul_inv,mul_add]
      have he : len⁻¹*(p⁻¹*(r*(len*E))) = r*p⁻¹*E := by
        calc
          _ = r*p⁻¹*(len⁻¹*len)*E := by ac_rfl
          _ = _ := by rw [ENNReal.inv_mul_cancel hl hlfin,mul_one]
      rw [mul_assoc _ _ (r*(len*E)),he]
      ring



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
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace


lemma signedPrimitive_decomposition (a u n : Vec) (hD : 1-dot n a ≠ 0) :
    signedPrimitive a u n = (u-n)+
      ((1-dot n a-(1-dot a u))/(1-dot n a)) • n := by
  ext i
  simp only [signedPrimitive,PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  field_simp
  ring

lemma small_deficit_difference {a u n : Vec} {θ φ : ℝ}
    (hn : ‖n‖=1) (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (hsmall : θ ≤ φ)
    (hd0 : 0 ≤ 1-dot n u) (hd : 1-dot n u ≤ 8*θ^2)
    (hun : ‖u-n‖ ≤ 4*θ) (han : ‖a-n‖ ≤ 4*φ) :
    |(1-dot a u)-(1-dot n a)| ≤ 24*φ*θ := by
  have he : (1-dot a u)-(1-dot n a)=(1-dot n u)+dot (a-n) (n-u) := by
    simp only [dot_sub_left,dot_sub_right,dot_self,hn,one_pow,dot_comm a n]
    ring
  rw [he]
  calc
    _ ≤ |1-dot n u|+|dot (a-n) (n-u)| := abs_add_le _ _
    _ ≤ 8*θ^2+‖a-n‖*‖n-u‖ := by
      gcongr
      · rwa [abs_of_nonneg hd0]
      · rw [dot_eq_inner]
        exact abs_real_inner_le_norm _ _
    _ ≤ 8*θ^2+(4*φ)*(4*θ) := by
      gcongr
      rwa [norm_sub_rev]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hsmall hθ]

lemma small_primitive_norm {a u n : Vec} {θ φ : ℝ}
    (hn : ‖n‖=1) (hθ : 0 ≤ θ) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hD : φ^2/2 ≤ 1-dot n a)
    (hun : ‖u-n‖ ≤ 4*θ)
    (he : |(1-dot a u)-(1-dot n a)| ≤ 24*φ*θ) :
    ‖signedPrimitive a u n‖ ≤ 52*θ/φ := by
  have hDpos : 0 < 1-dot n a := lt_of_lt_of_le (by positivity) hD
  have hratio : |(1-dot n a-(1-dot a u))/(1-dot n a)| ≤ 48*θ/φ := by
    rw [abs_div,abs_of_pos hDpos,abs_sub_comm]
    apply (div_le_iff₀ hDpos).mpr
    have hm := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 48*θ/φ)
    have hh : 48*θ/φ*(φ^2/2)=24*φ*θ := by field_simp; ring
    rw [hh] at hm
    exact he.trans hm
  rw [signedPrimitive_decomposition a u n hDpos.ne']
  calc
    _ ≤ ‖u-n‖+‖((1-dot n a-(1-dot a u))/(1-dot n a)) • n‖ := norm_add_le _ _
    _ ≤ 4*θ+48*θ/φ := by simpa only [norm_smul,Real.norm_eq_abs,hn,mul_one] using add_le_add hun hratio
    _ ≤ _ := by
      apply (le_div_iff₀ hφ).mpr
      have hm := mul_le_mul_of_nonneg_left hφ1 (by positivity : 0 ≤ 4*θ)
      field_simp
      nlinarith

lemma transverseProjection_add (w h k : Vec) :
    transverseProjection w (h+k)=transverseProjection w h+transverseProjection w k :=
  velocityProjection_add _ _ _

lemma transverseProjection_smul (w h : Vec) (c : ℝ) :
    transverseProjection w (c • h)=c • transverseProjection w h := velocityProjection_smul _ _ _

lemma transverseProjection_normal_dist (w n : Vec) :
    ‖transverseProjection w n‖ ≤ ‖n-velocity w‖ := by
  have he : transverseProjection w n=transverseProjection w (n-velocity w) := by
    have hh := transverseProjection_add w (n-velocity w) (velocity w)
    rw [sub_add_cancel,transverseProjection_velocity,add_zero] at hh
    exact hh
  rw [he]
  exact transverseProjection_norm _ _

lemma small_primitive_transverse {w u n : Vec} {θ φ : ℝ}
    (hθ : 0 ≤ θ) (hφ : 0 < φ)
    (hD : φ^2/2 ≤ 1-dot n (velocity w))
    (hun : ‖u-n‖ ≤ 4*θ) (han : ‖velocity w-n‖ ≤ 4*φ)
    (he : |(1-dot (velocity w) u)-(1-dot n (velocity w))| ≤ 24*φ*θ) :
    ‖transverseProjection w (signedPrimitive (velocity w) u n)‖ ≤ 196*θ := by
  have hDpos : 0 < 1-dot n (velocity w) := lt_of_lt_of_le (by positivity) hD
  have hratio : |(1-dot n (velocity w)-(1-dot (velocity w) u))/(1-dot n (velocity w))| ≤ 48*θ/φ := by
    rw [abs_div,abs_of_pos hDpos,abs_sub_comm]
    apply (div_le_iff₀ hDpos).mpr
    have hm := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 48*θ/φ)
    have hh : 48*θ/φ*(φ^2/2)=24*φ*θ := by field_simp; ring
    rw [hh] at hm
    exact he.trans hm
  have hpn : ‖transverseProjection w n‖ ≤ 4*φ :=
    (transverseProjection_normal_dist w n).trans (by rwa [norm_sub_rev])
  rw [signedPrimitive_decomposition _ _ _ hDpos.ne',transverseProjection_add,transverseProjection_smul]
  calc
    _ ≤ ‖transverseProjection w (u-n)‖+
        ‖((1-dot n (velocity w)-(1-dot (velocity w) u))/(1-dot n (velocity w))) • transverseProjection w n‖ := norm_add_le _ _
    _ ≤ 4*θ+(48*θ/φ)*(4*φ) := by
      rw [norm_smul,Real.norm_eq_abs]
      exact add_le_add ((transverseProjection_norm _ _).trans hun) (mul_le_mul hratio hpn (norm_nonneg _) (by positivity))
    _ = _ := by field_simp; ring

lemma small_primitive_acceleration_pairing {a u n b : Vec} {θ φ K : ℝ}
    (hθ : 0 ≤ θ) (hφ : 0 < φ) (hK : 0 ≤ K)
    (hD : φ^2/2 ≤ 1-dot n a) (hun : ‖u-n‖ ≤ 4*θ)
    (he : |(1-dot a u)-(1-dot n a)| ≤ 24*φ*θ)
    (hb : ‖b‖ ≤ K) (hbn : |dot b n| ≤ 20*φ*K) :
    |dot b (signedPrimitive a u n)| ≤ 964*θ*K := by
  have hDpos : 0 < 1-dot n a := lt_of_lt_of_le (by positivity) hD
  have hratio : |(1-dot n a-(1-dot a u))/(1-dot n a)| ≤ 48*θ/φ := by
    rw [abs_div,abs_of_pos hDpos,abs_sub_comm]
    apply (div_le_iff₀ hDpos).mpr
    have hm := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 48*θ/φ)
    have hh : 48*θ/φ*(φ^2/2)=24*φ*θ := by field_simp; ring
    rw [hh] at hm
    exact he.trans hm
  rw [signedPrimitive_decomposition _ _ _ hDpos.ne',dot_add_right,dot_smul_right]
  calc
    _ ≤ |dot b (u-n)|+|(1-dot n a-(1-dot a u))/(1-dot n a)*dot b n| := abs_add_le _ _
    _ ≤ ‖b‖*‖u-n‖+|(1-dot n a-(1-dot a u))/(1-dot n a)| *|dot b n| := by
      rw [abs_mul]
      apply add_le_add _ le_rfl
      rw [dot_eq_inner]
      exact abs_real_inner_le_norm _ _
    _ ≤ K*(4*θ)+(48*θ/φ)*(20*φ*K) := by gcongr
    _ = _ := by field_simp; ring

lemma receiver_acceleration_bounds (w K n : Vec) {φ : ℝ}
    (hn : ‖n‖=1) (hφ : 0 ≤ φ) (hD : 1-dot n (velocity w) ≤ 8*φ^2) :
    ‖fderiv ℝ velocity w K‖ ≤ ‖K‖/q w ∧
    |dot (fderiv ℝ velocity w K) n| ≤ 4*φ*(‖K‖/q w) := by
  have hp : ‖velocityProjection (velocity w) n‖ ≤ 4*φ := by
    apply (norm_velocityProjection_normal _ _ (norm_velocity_lt_one w).le hn).trans
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith⟩
  have he : fderiv ℝ velocity w K=(q w)⁻¹ • velocityProjection (velocity w) K := by
    rw [fderiv_velocity_apply]
    rfl
  constructor
  · rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (q_pos w))]
    have hh := mul_le_mul_of_nonneg_left
      (velocityProjection_norm (velocity w) K (norm_velocity_lt_one w).le)
      (inv_pos.mpr (q_pos w)).le
    simpa only [div_eq_mul_inv,mul_comm] using hh
  · rw [he,dot_smul_left,abs_mul,abs_of_pos (inv_pos.mpr (q_pos w)),
      dot_comm (velocityProjection _ _) n,velocityProjection_dot_symm]
    calc
      _ ≤ (q w)⁻¹*(‖velocityProjection (velocity w) n‖*‖K‖) := by
        apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr (q_pos w)).le
        rw [dot_eq_inner]
        exact abs_real_inner_le_norm _ _
      _ ≤ (q w)⁻¹*((4*φ)*‖K‖) := by
        gcongr
        exact (inv_pos.mpr (q_pos w)).le
      _ = _ := by ring

lemma receiver_small_primitive_pairing (w K u n : Vec) {θ φ : ℝ}
    (hn : ‖n‖=1) (hθ : 0 ≤ θ) (hφ : 0 < φ)
    (hD : φ^2/2 ≤ 1-dot n (velocity w))
    (hDu : 1-dot n (velocity w) ≤ 8*φ^2)
    (hun : ‖u-n‖ ≤ 4*θ)
    (he : |(1-dot (velocity w) u)-(1-dot n (velocity w))| ≤ 24*φ*θ) :
    |dot (fderiv ℝ velocity w K) (signedPrimitive (velocity w) u n)| ≤
      964*θ*(‖K‖/q w) := by
  have hb := receiver_acceleration_bounds w K n hn hφ.le hDu
  have hK : 0 ≤ ‖K‖/q w := div_nonneg (norm_nonneg _) (q_pos w).le
  apply small_primitive_acceleration_pairing hθ hφ hK hD hun he hb.1
  exact hb.2.trans (mul_le_mul_of_nonneg_right (by nlinarith) hK)

lemma receiver_bulk_vector_bound {w n : Vec} (hn : ‖n‖=1) :
    ‖((1-dot (velocity w) (velocity w))/(1-dot n (velocity w))) • n-velocity w‖ ≤ 3 := by
  have hD : 0 < 1-dot n (velocity w) := cone_denom_pos w n hn
  have hnon : 0 ≤ 1-dot (velocity w) (velocity w) := by
    rw [dot_self]
    nlinarith [norm_velocity_lt_one w,norm_nonneg (velocity w)]
  have hfrac : |(1-dot (velocity w) (velocity w))/(1-dot n (velocity w))| ≤ 2 := by
    rw [abs_of_nonneg (div_nonneg hnon hD.le)]
    apply (div_le_iff₀ hD).mpr
    have hh := sq_nonneg ‖n-velocity w‖
    rw [norm_sub_sq_real,← dot_eq_inner,hn,one_pow] at hh
    rw [dot_self]
    linarith
  calc
    _ ≤ ‖((1-dot (velocity w) (velocity w))/(1-dot n (velocity w))) • n‖+
        ‖velocity w‖ := norm_sub_le _ _
    _ ≤ 2+1 := by
      rw [norm_smul,Real.norm_eq_abs,hn,mul_one]
      exact add_le_add hfrac (norm_velocity_lt_one w).le
    _ = _ := by norm_num

lemma receiver_bulk_transverse_bound {w n : Vec} {φ : ℝ}
    (hn : ‖n‖=1) (hφ : 0 ≤ φ) (hD : 1-dot n (velocity w) ≤ 8*φ^2) :
    ‖transverseProjection w (((1-dot (velocity w) (velocity w))/(1-dot n (velocity w))) •
      n-velocity w)‖ ≤ 8*φ := by
  have hDp : 0 < 1-dot n (velocity w) := cone_denom_pos w n hn
  have hnon : 0 ≤ 1-dot (velocity w) (velocity w) := by
    rw [dot_self]
    nlinarith [norm_velocity_lt_one w,norm_nonneg (velocity w)]
  have hfrac : |(1-dot (velocity w) (velocity w))/(1-dot n (velocity w))| ≤ 2 := by
    rw [abs_of_nonneg (div_nonneg hnon hDp.le)]
    apply (div_le_iff₀ hDp).mpr
    have hh := sq_nonneg ‖n-velocity w‖
    rw [norm_sub_sq_real,← dot_eq_inner,hn,one_pow] at hh
    rw [dot_self]
    linarith
  have hpn : ‖transverseProjection w n‖ ≤ 4*φ := by
    apply (transverseProjection_normal_bound w n hn).trans
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith⟩
  have he : transverseProjection w
      (((1-dot (velocity w) (velocity w))/(1-dot n (velocity w))) • n-velocity w)=
      ((1-dot (velocity w) (velocity w))/(1-dot n (velocity w))) • transverseProjection w n := by
    rw [sub_eq_add_neg,transverseProjection_add,show -velocity w=(-1:ℝ) • velocity w by simp,
      transverseProjection_smul,transverseProjection_smul,transverseProjection_velocity,smul_zero,add_zero]
  rw [he,norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul hfrac hpn (norm_nonneg _) (by norm_num)).trans_eq (by ring)

lemma small_energy_ratio {a u n : Vec} {θ φ : ℝ}
    (_hθ : 0 ≤ θ) (hφ : 0 < φ) (hsmall : θ ≤ φ)
    (hD : φ^2/2 ≤ 1-dot n a)
    (he : |(1-dot a u)-(1-dot n a)| ≤ 24*φ*θ) :
    |(1-dot a u)/(1-dot n a)| ≤ 49 := by
  have hDp : 0<1-dot n a := lt_of_lt_of_le (by positivity) hD
  rw [abs_div,abs_of_pos hDp]
  apply (div_le_iff₀ hDp).mpr
  have hab : |1-dot a u| ≤ |(1-dot a u)-(1-dot n a)|+|1-dot n a| :=
    calc
      _ = |((1-dot a u)-(1-dot n a))+(1-dot n a)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  rw [abs_of_pos hDp] at hab
  have hm := mul_le_mul_of_nonneg_left hsmall (by positivity : 0≤24*φ)
  nlinarith

lemma signedRemainder_physical_decomposition {r f : ℝ} {a u n b : Vec}
    (hr : r≠0) (hD : 1-dot n a≠0) :
    (f*(1-dot n a)) • signedRemainder r a u n b =
      (f/r^2*((1-dot a u)/(1-dot n a))) •
        (((1-dot a a)/(1-dot n a)) • n-a) +
      (f/r*(dot b (signedPrimitive a u n)/(1-dot n a))) • n := by
  ext i
  simp only [signedRemainder,PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,smul_eq_mul]
  field_simp

lemma signedRemainder_small_norm {r f θ φ : ℝ} (w K u n : Vec)
    (hr : 0<r) (hf : 0≤f) (hn : ‖n‖=1) (hθ : 0≤θ) (hφ : 0<φ)
    (hsmall : θ≤φ) (hD : φ^2/2≤1-dot n (velocity w))
    (hDu : 1-dot n (velocity w)≤8*φ^2) (hun : ‖u-n‖≤4*θ)
    (he : |(1-dot (velocity w) u)-(1-dot n (velocity w))|≤24*φ*θ) :
    ‖(f*(1-dot n (velocity w))) •
      signedRemainder r (velocity w) u n (fderiv ℝ velocity w K)‖ ≤
      147*f/r^2+1928*f*θ*(‖K‖/q w)/(r*φ^2) := by
  have hDp : 0<1-dot n (velocity w) := cone_denom_pos w n hn
  have hpair := receiver_small_primitive_pairing w K u n hn hθ hφ hD hDu hun he
  have hratio := small_energy_ratio hθ hφ hsmall hD he
  have hK : 0≤‖K‖/q w := div_nonneg (norm_nonneg _) (q_pos w).le
  have hpairD : |dot (fderiv ℝ velocity w K) (signedPrimitive (velocity w) u n)/
      (1-dot n (velocity w))| ≤ 1928*θ*(‖K‖/q w)/φ^2 := by
    rw [abs_div,abs_of_pos hDp]
    apply (div_le_iff₀ hDp).mpr
    have hm := mul_le_mul_of_nonneg_left hD
      (by positivity : 0≤1928*θ*(‖K‖/q w)/φ^2)
    have heq : 1928*θ*(‖K‖/q w)/φ^2*(φ^2/2)=964*θ*(‖K‖/q w) := by field_simp; ring
    rw [heq] at hm
    exact hpair.trans hm
  rw [signedRemainder_physical_decomposition hr.ne' hDp.ne']
  calc
    _ ≤ ‖(f/r^2*((1-dot (velocity w) u)/(1-dot n (velocity w)))) •
        (((1-dot (velocity w) (velocity w))/(1-dot n (velocity w))) • n-velocity w)‖+
      ‖(f/r*(dot (fderiv ℝ velocity w K) (signedPrimitive (velocity w) u n)/(1-dot n (velocity w)))) • n‖ :=
      norm_add_le _ _
    _ ≤ (f/r^2*49)*3+(f/r*(1928*θ*(‖K‖/q w)/φ^2))*1 := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (div_nonneg hf (sq_nonneg r)),
        abs_of_nonneg (div_nonneg hf hr.le)]
      exact add_le_add (mul_le_mul
        (mul_le_mul_of_nonneg_left hratio (by positivity)) (receiver_bulk_vector_bound hn)
        (norm_nonneg _) (by positivity))
        (by rw [hn,mul_one,mul_one]; exact mul_le_mul_of_nonneg_left hpairD (by positivity))
    _ = _ := by field_simp; ring


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal


lemma PhaseFlowOn.cone_occupation_joint_budget {s : Solution} {T p a b I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hT : 0 ≤ T) (hs : EnergyPrefix s T)
    (zX : Phase) (k : ℕ) (n : ℕ × ℕ) {H : Set (ℝ × Phase)}
    (hH : MeasurableSet H) (hsub : H⊆spaceConeDomain F.flow zX T)
    (hp : 0 ≤ p) (hI : 0<I) (hJ : Icc a b⊆Icc 0 T)
    (htime : ∀ t z, (t,z)∈H → t∈Icc a b)
    (hmom : ∀ t z, (t,z)∈H → p≤q z.2)
    (harrival : H⊆arrivalBudgetSet F.flow zX T k n) :
    ENNReal.ofReal p * coneOccupation F.flow zX T s.f H ≤
      ENNReal.ofReal I * jointEnergyBudget s F.flow zX T k a b I n := by
  rw [F.cone_occupation_identity hT zX hs.f_smooth hs.vlasov hH hsub,
    ← F.phase_occupation_identity hT hs.f_smooth hs.vlasov hH,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    jointEnergyBudget_eq k hJ n,← mul_assoc,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hI).ne' ENNReal.ofReal_ne_top,one_mul]
  let e : ℝ × Phase → ℝ≥0∞ := fun p => ENNReal.ofReal (q p.2.2*s.f p)
  let G : ℝ → ℝ≥0∞ := fun t => ∫⁻ z : Phase,
    (sameTimeBudgetSet F.flow zX T k n).indicator e (t,z)+
      (arrivalBudgetSet F.flow zX T k n).indicator e (t,z)
  have hpnt (t : ℝ) (ht : t∈Ioo 0 T) :
      ENNReal.ofReal p*(∫⁻ z : Phase,H.indicator (fun z => ENNReal.ofReal (s.f z)) (t,z)) ≤
        (Icc a b).indicator G t := by
    by_cases hti : t∈Icc a b
    · rw [indicator_of_mem hti,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono
      intro z
      dsimp only
      by_cases hz : (t,z)∈H
      · rw [indicator_of_mem hz,indicator_of_mem (harrival hz),← ENNReal.ofReal_mul hp]
        exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hmom t z hz)
          (hs.nonnegative t (Ioo_subset_Icc_self ht) z))).trans (le_add_left le_rfl)
      · rw [indicator_of_notMem hz,mul_zero]
        exact bot_le
    · rw [indicator_of_notMem hti]
      have hz : (∫⁻ z : Phase,H.indicator (fun z => ENNReal.ofReal (s.f z)) (t,z))=0 := by
        apply lintegral_eq_zero_of_ae_eq_zero
        apply ae_of_all
        intro z
        exact indicator_of_notMem (fun he => hti (htime t z he)) _
      rw [hz,mul_zero]
  calc
    _ ≤ ∫⁻ t in Ioo (0:ℝ) T, (Icc a b).indicator G t :=
      lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ioo hpnt)
    _ ≤ ∫⁻ t : ℝ, (Icc a b).indicator G t :=
      lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ = _ := lintegral_indicator measurableSet_Icc _

def closedBinEulerian (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ)
    (B : ClosedConeBin) (S : Set Phase) (a b c d : ℝ) : Set (ℝ × Phase) :=
  (fun p : ℝ × Phase => (p.1,prefixFlow α T p.2 p.1)) ''
    {p : ℝ × Phase | p.1∈closedBinHits α zX B S a b c d p.2}
      ∩ spaceConeDomain α zX T

lemma measurableSet_spaceConeDomain (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ) :
    MeasurableSet (spaceConeDomain α zX T) := by
  exact (measurable_fst measurableSet_Ioo).inter
    (measurableSet_lt (measurable_snd.fst.sub measurable_const).norm
      (measurable_const.sub measurable_fst))

lemma PhaseFlowOn.measurable_closedBinEulerian {s : Solution} {T a b c d : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (hJ : Icc a b⊆Icc 0 T) (hC : Icc c d⊆Icc 0 T) :
    MeasurableSet (closedBinEulerian F.flow zX T B S a b c d) :=
  ((F.compact_closedBinHits_joint hs hT zX B hS hJ hC).image
    (continuous_fst.prodMk (F.continuous_prefixFlow hs hT))).measurableSet.inter
      (measurableSet_spaceConeDomain _ _ _)

lemma PhaseFlowOn.mem_closedBinEulerian_iff {E B : Field} {T a b c d r : ℝ}
    (F : PhaseFlowOn E B T) (zX z : Phase) (C : ClosedConeBin) (S : Set Phase)
    (hC : Icc c d⊆Icc 0 T) :
    (r,F.flow z r)∈closedBinEulerian F.flow zX T C S a b c d ↔
      r∈closedBinHits F.flow zX C S a b c d z ∧
        (r,F.flow z r)∈spaceConeDomain F.flow zX T := by
  constructor
  · rintro ⟨⟨⟨r',z'⟩,hh,he⟩,hd⟩
    have hr : r'=r := congrArg Prod.fst he
    subst r'
    have heq : F.flow z' r=F.flow z r := by
      have h := congrArg Prod.snd he
      simpa only [prefixFlow,prefixClamp_eq (hC hh.2.1)] using h
    have hz : z'=z := (F.bijective r (hC hh.2.1)).1 heq
    subst z'
    exact ⟨hh,hd⟩
  · rintro ⟨hh,hd⟩
    refine ⟨⟨(r,z),hh,?_⟩,hd⟩
    simp only [prefixFlow,prefixClamp_eq (hC hh.2.1)]

lemma PhaseFlowOn.closedBinEulerian_occupation_le {s : Solution} {T a b c d : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (hJ : Icc a b⊆Icc 0 T) (hC : Icc c d⊆Icc 0 T) :
    coneOccupation F.flow zX T s.f (closedBinEulerian F.flow zX T B S a b c d) ≤
      labelOccupation (fun z => s.f (0,z)) (closedBinHits F.flow zX B S a b c d) := by
  rw [F.cone_occupation_identity hT zX hs.f_smooth hs.vlasov
    (F.measurable_closedBinEulerian hs hT zX B hS hJ hC) inter_subset_right]
  unfold labelOccupation
  apply lintegral_mono
  intro z
  apply mul_le_mul' le_rfl
  apply measure_mono
  intro r hr
  exact ((F.mem_closedBinEulerian_iff zX z B S hC).mp hr.2).1



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
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal


lemma PhaseFlowOn.closedBinEulerian_properties {E B : Field} {T a b c d : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (C : ClosedConeBin) (S : Set Phase)
    (hC : Icc c d ⊆ Icc 0 T) :
    ∀ p ∈ closedBinEulerian F.flow zX T C S a b c d,
      p.1 ∈ Icc c d ∧ C.qmin ≤ q p.2.2 ∧
      ∃ z, p.2 = F.flow z p.1 ∧ ∃ t∈Icc a b, InClosedConeBin F.flow zX C t p.1 z := by
  rintro p ⟨⟨⟨r,z⟩,⟨_,hr,t,ht,hbin⟩,he⟩,_⟩
  dsimp only at he
  have heq : (r,F.flow z r)=p := by
    simpa only [prefixFlow,prefixClamp_eq (hC hr)] using he
  clear he
  subst p
  exact ⟨hr,hbin.2.2.1.1,z,rfl,t,ht,hbin⟩

lemma PhaseFlowOn.closedBinEulerian_in_arrivalBudget {E B : Field} {T a b c d : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (C : ClosedConeBin) (S : Set Phase) (i j : ℕ)
    (hJ : Icc a b ⊆ Icc 0 T) (hC : Icc c d ⊆ Icc 0 T) (hR : 0<C.rmin)
    (hiq : (2:ℝ)^i/2≤C.qmin) (hiQ : C.qmax≤2*(2:ℝ)^i)
    (hjD : ((2:ℝ)^j)⁻¹^2/2≤C.Dmin) (hjU : C.Dmax≤8*((2:ℝ)^j)⁻¹^2) :
    closedBinEulerian F.flow zX T C S a b c d ⊆ arrivalBudgetSet F.flow zX T 1 (i,j) := by
  intro p hp
  obtain ⟨_,_,z,hz,t,ht,hbin⟩ := F.closedBinEulerian_properties zX C S hC p hp
  have hr : p.1∈Ioo 0 T := hp.2.1
  have hb := F.closedBinHit_in_arrivalBudget zX z C i j hr (hJ ht) hR hiq hiQ hjD hjU hbin
  simpa only [← hz] using hb

lemma PhaseFlowOn.closedBinEulerian_joint_occupation {s : Solution} {T a b c d I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (C : ClosedConeBin) {S : Set Phase} (hS : IsCompact S) (i j : ℕ)
    (hJ : Icc a b ⊆ Icc 0 T) (hC : Icc c d ⊆ Icc 0 T)
    (hI : 0<I) (hR : 0<C.rmin)
    (hiq : (2:ℝ)^i/2≤C.qmin) (hiQ : C.qmax≤2*(2:ℝ)^i)
    (hjD : ((2:ℝ)^j)⁻¹^2/2≤C.Dmin) (hjU : C.Dmax≤8*((2:ℝ)^j)⁻¹^2) :
    ENNReal.ofReal C.qmin * coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T C S a b c d) ≤
    ENNReal.ofReal I * jointEnergyBudget s F.flow zX T 1 c d I (i,j) := by
  apply F.cone_occupation_joint_budget hT hs zX 1 (i,j)
    (F.measurable_closedBinEulerian hs hT zX C hS hJ hC) inter_subset_right
    (le_trans (by positivity) hiq) hI hC
  · intro r z hz
    exact (F.closedBinEulerian_properties zX C S hC (r,z) hz).1
  · intro r z hz
    exact (F.closedBinEulerian_properties zX C S hC (r,z) hz).2.1
  · exact F.closedBinEulerian_in_arrivalBudget zX C S i j hJ hC hR hiq hiQ hjD hjU


open Set MeasureTheory
open scoped ENNReal


lemma lintegral_add_left_Ioo (s T : ℝ) (f : ℝ → ℝ≥0∞) :
    (∫⁻ r in Ioo (0:ℝ) (T-s), f (s+r)) = ∫⁻ t in Ioo s T, f t := by
  rw [← lintegral_indicator measurableSet_Ioo,← lintegral_indicator measurableSet_Ioo]
  calc
    _ = ∫⁻ r : ℝ, (Ioo s T).indicator f (s+r) := by
      apply lintegral_congr
      intro r
      have he : r∈Ioo 0 (T-s) ↔ s+r∈Ioo s T := by
        simp only [mem_Ioo]
        constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
      by_cases hr : r∈Ioo 0 (T-s)
      · rw [indicator_of_mem hr,indicator_of_mem (he.mp hr)]
      · rw [indicator_of_notMem hr,indicator_of_notMem (mt he.mpr hr)]
    _ = _ := lintegral_add_left_eq_self _ _

lemma lintegral_retarded_triangle (T : ℝ) {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ s in Ioo (0:ℝ) T, ∫⁻ r in Ioo (0:ℝ) (T-s), f (s+r,s)) =
      ∫⁻ t in Ioo (0:ℝ) T, ∫⁻ s in Ioo (0:ℝ) t, f (t,s) := by
  let H : Set (ℝ × ℝ) := {p | 0<p.1 ∧ p.1<p.2 ∧ p.2<T}
  let g : ℝ × ℝ → ℝ≥0∞ := H.indicator (fun p => f (p.2,p.1))
  have hH : MeasurableSet H :=
    (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const))
  have hg : Measurable g := (hf.comp (measurable_snd.prodMk measurable_fst)).indicator hH
  calc
    _ = ∫⁻ s : ℝ, ∫⁻ t : ℝ, g (s,t) := by
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro s
      by_cases hs : s∈Ioo 0 T
      · rw [indicator_of_mem hs,lintegral_add_left_Ioo s T (fun t => f (t,s)),← lintegral_indicator measurableSet_Ioo]
        apply lintegral_congr
        intro t
        have he : (s,t)∈H ↔ t∈Ioo s T := by simp only [H,mem_ofPred_eq,mem_Ioo,hs.1,true_and]
        by_cases ht : t∈Ioo s T
        · simp only [g,indicator_of_mem ht,indicator_of_mem (he.mpr ht)]
        · simp only [g,indicator_of_notMem ht,indicator_of_notMem (mt he.mp ht)]
      · rw [indicator_of_notMem hs]
        symm
        apply lintegral_eq_zero_of_ae_eq_zero
        apply ae_of_all
        intro t
        exact indicator_of_notMem (fun hh => hs ⟨hh.1,hh.2.1.trans hh.2.2⟩) _
    _ = ∫⁻ t : ℝ, ∫⁻ s : ℝ, g (s,t) := lintegral_lintegral_swap hg.aemeasurable
    _ = _ := by
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro t
      by_cases ht : t∈Ioo 0 T
      · rw [indicator_of_mem ht,← lintegral_indicator measurableSet_Ioo]
        apply lintegral_congr
        intro s
        have he : (s,t)∈H ↔ s∈Ioo 0 t := by simp only [H,mem_ofPred_eq,mem_Ioo,ht.2,and_true]
        by_cases hs : s∈Ioo 0 t
        · simp only [g,indicator_of_mem hs,indicator_of_mem (he.mpr hs)]
        · simp only [g,indicator_of_notMem hs,indicator_of_notMem (mt he.mp hs)]
      · rw [indicator_of_notMem ht]
        apply lintegral_eq_zero_of_ae_eq_zero
        apply ae_of_all
        intro s
        exact indicator_of_notMem (fun hh => ht ⟨hh.1.trans hh.2.1,hh.2.2⟩) _

lemma lintegral_retarded_triangle_parameter {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (T : ℝ) {f : ℝ × ℝ × Ω → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ s in Ioo (0:ℝ) T, ∫⁻ n : Ω, ∫⁻ r in Ioo (0:ℝ) (T-s), f (s+r,s,n) ∂volume ∂μ) =
      ∫⁻ t in Ioo (0:ℝ) T, ∫⁻ s in Ioo (0:ℝ) t, ∫⁻ n : Ω, f (t,s,n) ∂μ := by
  have hm : Measurable (fun p : (ℝ × ℝ) × Ω => f (p.1.1,p.1.2,p.2)) :=
    hf.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  calc
    _ = ∫⁻ s in Ioo (0:ℝ) T, ∫⁻ r in Ioo (0:ℝ) (T-s), ∫⁻ n : Ω, f (s+r,s,n) ∂μ := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro s _
      have hg : Measurable (fun p : Ω × ℝ => f (s+p.2,s,p.1)) :=
        hf.comp ((measurable_const.add measurable_snd).prodMk
          (measurable_const.prodMk measurable_fst))
      exact lintegral_lintegral_swap hg.aemeasurable
    _ = _ := lintegral_retarded_triangle T hm.lintegral_prod_right'

end RVM

end

end OAI
