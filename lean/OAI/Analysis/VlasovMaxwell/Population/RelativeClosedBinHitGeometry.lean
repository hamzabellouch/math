import Mathlib
import OAI.Analysis.VlasovMaxwell.Flow.ClosedEulerianCrudeBudget

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
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma relative_closed_bin_hit_geometry {α : Phase → ℝ → Phase} {zX z : Phase}
    {B : ClosedConeBin} {t r φ σ : ℝ} (hbin : InClosedConeBin α zX B t r z)
    (hr : 0 < B.rmin) (hφ : 0 < φ) (hσ : 0 < σ)
    (hDhi : B.Dmax ≤ 8*φ^2) (helo : σ^2/2 ≤ B.emin) (hehi : B.emax ≤ 8*σ^2)
    (hq : 4 ≤ σ*B.qmin) (hw : 4 ≤ σ*B.wmin) :
    ∃ n : Vec, ‖n‖=1 ∧ (α zX t).1-(α z r).1=(t-r) • n ∧
      ‖velocity (α zX t).2-n‖ ≤ 4*φ ∧
      σ/2 ≤ ‖velocity (α z r).2-velocity (α zX t).2‖ ∧
      ‖velocity (α z r).2-velocity (α zX t).2‖ ≤ 4*σ := by
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
  have hhi : 1-dot n (velocity (α zX t).2) ≤ 8*φ^2 :=
    hb.2.2.2.2.2.1.2.trans hDhi
  have hinv (z' : Phase) (qlo : ℝ) (hlo : qlo ≤ q z'.2)
      (hsmall : 4 ≤ σ*qlo) : (q z'.2)⁻¹ ≤ σ/4 := by
    rw [inv_le_iff_one_le_mul₀ (q_pos _)]
    have hh := mul_le_mul_of_nonneg_left hlo hσ.le
    nlinarith
  have hsource := hinv (α z r) B.qmin hb.2.2.1.1 hq
  have hreceiver := hinv (α zX t) B.wmin hb.2.2.2.1.1 hw
  have hlower := actual_relative_separation hσ.le hsource hreceiver
    (helo.trans hb.2.2.2.2.2.2.1)
  have hupper : ‖velocity (α z r).2-velocity (α zX t).2‖ ≤ 4*σ := by
    have hid := relative_angle_identity (α z r).2 (α zX t).2
    have hh := hb.2.2.2.2.2.2.2.trans hehi
    nlinarith [sq_nonneg ((q (α z r).2)⁻¹),sq_nonneg ((q (α zX t).2)⁻¹),
      norm_nonneg (velocity (α z r).2-velocity (α zX t).2)]
  have hrec : ‖velocity (α zX t).2-n‖ ≤ 4*φ := by
    rw [norm_sub_rev]
    have hid := cone_angle_identity (α zX t).2 n hn
    nlinarith [sq_nonneg ((q (α zX t).2)⁻¹),norm_nonneg (n-velocity (α zX t).2)]
  exact ⟨n,hn,hgeom,hrec,hlower,hupper⟩

lemma PhaseFlowOn.relative_closed_bin_cell_data {s : Solution}
    {T M A P L lo hi a b c d massScale φ σ C p : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (B : ClosedConeBin) {S : Set Phase}
    (hlo0 : 0 ≤ lo) (hhiT : hi ≤ T)
    (hJ : Icc a b ⊆ Icc lo hi) (hC : Icc c d ⊆ Icc lo hi)
    (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
    (hm : 0 < massScale) (hφ : 0 < φ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hconst : 128 ≤ C)
    (hlen : hi-lo ≤ (C*(P/massScale)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2)
    (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
    (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
    (hr : 0 < B.rmin) (hDhi : B.Dmax ≤ 8*φ^2)
    (helo : σ^2/2 ≤ B.emin) (hehi : B.emax ≤ 8*σ^2)
    (hq : 4 ≤ σ*B.qmin) (hw : 4 ≤ σ*B.wmin)
    (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
    (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L) :
    ∀ z, (closedBinHits F.flow zX B S a b c d z).Nonempty →
      volume (closedBinHits F.flow zX B S a b c d z) ≤ ENNReal.ofReal (40*B.rmax*(1+φ/σ)) ∧
      ∀ t∈Icc c d, p/256 ≤ q (F.flow z t).2 ∧ q (F.flow z t).2 ≤ p/16 ∧
        σ/4 ≤ ‖velocity (F.flow z t).2-velocity (F.flow zX t).2‖ ∧
        ‖velocity (F.flow z t).2-velocity (F.flow zX t).2‖ ≤ 5*σ := by
  let U := Icc lo hi
  have hUT : U ⊆ Icc 0 T := Icc_subset_Icc hlo0 hhiT
  have hCT : Icc c d ⊆ Icc 0 T := hC.trans hUT
  have hstable (z : Phase) (H : IncrementBootstrap (fun t => (F.flow z t).2) T M A P L)
      (r : ℝ) (hr : r∈U) (hqm : massScale ≤ q (F.flow z r).2) :=
    H.velocity_stability_scale hlo0 hhiT hr ((F.continuousOn_time z).snd.mono hUT)
      hM hA hP hL hm hσ hσ1 hconst hqm hlen
  intro z hz
  obtain ⟨r₀,hzS,hr₀,t₀,ht₀,hbin₀⟩ := hz
  have hsource := hstable z (HZ z hzS) r₀ (hC hr₀) (hmq.trans hbin₀.2.2.1.1)
  have hreceiver := hstable zX HX t₀ (hJ ht₀) (hmw.trans hbin₀.2.2.2.1.1)
  obtain ⟨n₀,_,_,_,hsep₀,hupper₀⟩ := relative_closed_bin_hit_geometry hbin₀ hr hφ hσ hDhi helo hehi hq hw
  have href (t : ℝ) (ht : t∈U) :
      ‖velocity (F.flow z t).2-velocity (F.flow zX t).2-
        (velocity (F.flow z r₀).2-velocity (F.flow zX t₀).2)‖ ≤ σ/16 := by
    have hh := relative_ref_triangle (hsource t ht).2.1 (hreceiver t ht).2.1
    linarith
  constructor
  · have hsep (r : ℝ) (hrH : r∈closedBinHits F.flow zX B S a b c d z) :
        ‖(F.flow z r).1-(F.flow zX r).1‖ ≤ 5*B.rmax*(φ+σ) := by
      obtain ⟨_,hrC,t,htJ,hbin⟩ := hrH
      obtain ⟨n,_,hgeom,hangle,_,_⟩ := relative_closed_bin_hit_geometry hbin hr hφ hσ hDhi helo hehi hq hw
      have hrt : r ≤ t := by linarith [hbin.2.1.1]
      have hsub : Icc r t ⊆ U := Icc_subset_Icc (hC hrC).1 (hJ htJ).2
      have hh := retarded_same_time_separation hrt
        (fun u hu => ((F.ode zX u (hUT (hsub hu))).mono (hsub.trans hUT)).fst)
        (fun u hu => velocity_ref_triangle (hreceiver u (hsub hu)).2.1
          (hreceiver t (hJ htJ)).2.1 hangle) hgeom
      have hrad : 0 ≤ B.rmax := (sub_nonneg.mpr hrt).trans hbin.2.1.2
      calc
        _ ≤ (4*φ+2*(σ/32))*(t-r) := hh
        _ ≤ (5*(φ+σ))*B.rmax := mul_le_mul (by linarith) hbin.2.1.2
          (sub_nonneg.mpr hrt) (by positivity)
        _ = _ := by ring
    have hh := stable_cell_duration (convex_Icc c d)
      (show closedBinHits F.flow zX B S a b c d z ⊆ Icc c d from fun _ h => h.2.1)
      (half_pos hσ) hsep₀ ((F.continuousOn_time zX).fst.mono hCT)
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
          (velocity (F.flow z t).2-velocity (F.flow zX t).2)‖ ≤ σ/16 := by
        rw [norm_sub_rev]
        exact href t (hC ht)
      linarith
    · have hn := norm_sub_norm_le
        (velocity (F.flow z t).2-velocity (F.flow zX t).2)
        (velocity (F.flow z r₀).2-velocity (F.flow zX t₀).2)
      linarith [href t (hC ht)]

lemma PhaseFlowOn.relative_closed_bin_cell_crude {s : Solution}
    {T M A P L lo hi a b c d massScale φ σ C p : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (t₀ : ℝ) (ht₀ : t₀∈Icc c d) (zX : Phase) (B : ClosedConeBin) {S : Set Phase}
    (hlo0 : 0 ≤ lo) (hhiT : hi ≤ T)
    (hJ : Icc a b ⊆ Icc lo hi) (hC : Icc c d ⊆ Icc lo hi)
    (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
    (hm : 0 < massScale) (hφ : 0 < φ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hconst : 128 ≤ C)
    (hlen : hi-lo ≤ (C*(P/massScale)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2)
    (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
    (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
    (hr : 0 < B.rmin) (hDhi : B.Dmax ≤ 8*φ^2)
    (helo : σ^2/2 ≤ B.emin) (hehi : B.emax ≤ 8*σ^2)
    (hq : 4 ≤ σ*B.qmin) (hw : 4 ≤ σ*B.wmin)
    (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
    (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L) :
    ENNReal.ofReal (p/256) *
        labelOccupation (fun z => s.f (0,z)) (closedBinHits F.flow zX B S a b c d) ≤
      ENNReal.ofReal (40*B.rmax*(1+φ/σ)) * ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) := by
  have hdata := F.relative_closed_bin_cell_data zX B hlo0 hhiT hJ hC hM hA hP hL
    hm hφ hσ hσ1 hconst hlen hqmin hqmax hmq hmw hr hDhi helo hehi hq hw HX HZ
  apply F.label_occupation_cell_bound hs ((hC.trans (Icc_subset_Icc hlo0 hhiT)) ht₀)
  · intro z
    by_cases hz : (closedBinHits F.flow zX B S a b c d z).Nonempty
    · exact (hdata z hz).1
    · simp only [not_nonempty_iff_eq_empty.mp hz,measure_empty,zero_le]
  · exact fun z hz => ((hdata z hz).2 t₀ ht₀).1

lemma selectedSourceCells_card {T len a b r : ℝ} (hlen : 0<len)
    (hab : a≤b) (hr : 0≤r) :
    ((selectedSourceCells T len a b r).card:ℝ)≤2+(b-a+r)/len := by
  classical
  let N := selectedSourceCells T len a b r
  by_cases hN : N.Nonempty
  · let lo := N.min' hN
    let hi := N.max' hN
    have hlo : lo∈N := Finset.min'_mem _ _
    have hhi : hi∈N := Finset.max'_mem _ _
    have hlh : lo≤hi := Finset.min'_le _ _ hhi
    have hsub : N⊆Finset.Icc lo hi := by
      intro i hiN
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hiN,Finset.le_max' _ _ hiN⟩
    have hc : N.card≤hi+1-lo := by
      simpa only [Nat.card_Icc] using Finset.card_le_card hsub
    have hc' : (N.card:ℝ)≤(hi:ℝ)+1-(lo:ℝ) := by
      have hh : (N.card:ℝ)≤((hi+1-lo:ℕ):ℝ) := Nat.cast_le.mpr hc
      simpa only [Nat.cast_sub (by omega : lo≤hi+1),Nat.cast_add,Nat.cast_one] using hh
    have hu : (hi:ℝ)*len≤b := (Finset.mem_filter.mp hhi).2.1
    have hl : a-r≤((lo:ℝ)+1)*len := by
      have hh := (Finset.mem_filter.mp hlo).2.2
      exact hh.trans (by simpa only [sourceCellHi,Nat.cast_add,Nat.cast_one] using
        (min_le_right T (((lo+1:ℕ):ℝ)*len)))
    apply (mul_le_mul_iff_left₀ hlen).mp
    have he : (2+(b-a+r)/len)*len=2*len+(b-a+r) := by field_simp
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right hc' hlen.le]
  · have hz : N=∅ := Finset.not_nonempty_iff_eq_empty.mp hN
    change (N.card:ℝ)≤_
    rw [hz,Finset.card_empty,Nat.cast_zero]
    have : 0≤(b-a+r)/len := div_nonneg (by linarith) hlen.le
    linarith

lemma PhaseFlowOn.relative_closed_bin_stable {s : Solution}
    {T M A P L a b massScale φ σ C p len : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (ha : 0≤a) (hb : b≤T) (hab : a≤b) (hlen : 0<len)
    (hM : 0<M) (hA : 0≤A) (hP : 0<P) (hL : 0≤L)
    (hm : 0 < massScale) (hφ : 0<φ) (hσ : 0<σ) (hσ1 : σ≤1) (hconst : 128≤C)
    (hstable : 2*len≤(C*(P/massScale)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2)
    (hqmin : p/128≤B.qmin) (hqmax : B.qmax≤p/32)
    (hmq : massScale≤B.qmin) (hmw : massScale≤B.wmin)
    (hr : 0<B.rmin) (hrmax : 0≤B.rmax) (hrad : B.rmax≤len)
    (hDhi : B.Dmax≤8*φ^2) (helo : σ^2/2≤B.emin) (hehi : B.emax≤8*σ^2)
    (hq : 4≤σ*B.qmin) (hw : 4≤σ*B.wmin)
    (HX : IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L)
    (HZ : ∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) :
    ENNReal.ofReal (p/256)*labelOccupation (fun z=>s.f (0,z))
      (closedBinHits F.flow zX B S a b 0 T)≤
      ENNReal.ofReal (40*B.rmax*(1+φ/σ))*
        ENNReal.ofReal ((2+(b-a+B.rmax)/len)*(∫x : Vec,totalEnergy s (0,x))) := by
  classical
  let l := sourceCellLo len
  let u := sourceCellHi T len
  let w := fun i=>min T (u i+B.rmax)
  let N := selectedSourceCells T len a b B.rmax
  let E := ∫x : Vec,totalEnergy s (0,x)
  let D := 40*B.rmax*(1+φ/σ)
  let O := fun i=>labelOccupation (fun z=>s.f (0,z))
    (closedBinHits F.flow zX B S a b (l i) (u i))
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hD : 0≤D := by dsimp [D]; positivity
  have hgrid (i : ℕ) (hi : i∈N) :
      0≤l i ∧ l i≤u i ∧ u i≤T ∧ u i-l i≤len :=
    selectedSourceCells_subset_prefix hT hlen hi
  have hJC (i : ℕ) : Icc (max a (l i)) (min b (u i+B.rmax))⊆Icc (l i) (w i) := by
    intro t ht
    exact ⟨(le_max_right _ _).trans ht.1,
      le_min ((ht.2.trans (min_le_left _ _)).trans hb) (ht.2.trans (min_le_right _ _))⟩
  have hCC (i : ℕ) (hi : i∈N) : Icc (l i) (u i)⊆Icc (l i) (w i) := by
    intro t ht
    exact ⟨ht.1,le_min (ht.2.trans (hgrid i hi).2.2.1) (by linarith [ht.2])⟩
  have hST (i : ℕ) (hi : i∈N) :
      w i-l i≤(C*(P/massScale)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2 := by
    have hg := (hgrid i hi).2.2.2
    have hw' : w i≤u i+B.rmax := min_le_right _ _
    linarith
  have hsum : labelOccupation (fun z=>s.f (0,z)) (closedBinHits F.flow zX B S a b 0 T)≤
      ∑i∈N,O i := by
    rw [closedBinHits_clip_source]
    apply F.closedBinHits_occupation_le_sum hs hT zX B hS N l u (Icc_subset_Icc ha hb)
    · intro i hi
      exact Icc_subset_Icc (hgrid i hi).1 (hgrid i hi).2.2.1
    · exact selectedSourceCells_cover hlen
  have hpay (i : ℕ) (hi : i∈N) : ENNReal.ofReal (p/256)*O i≤ENNReal.ofReal D*ENNReal.ofReal E := by
    dsimp only [O]
    rw [closedBinHits_clip_receiver]
    exact F.relative_closed_bin_cell_crude hs (l i) (left_mem_Icc.mpr (hgrid i hi).2.1)
      zX B (hgrid i hi).1 (min_le_left _ _) (hJC i) (hCC i hi)
      hM hA hP hL hm hφ hσ hσ1 hconst (hST i hi)
      hqmin hqmax hmq hmw hr hDhi helo hehi hq hw HX HZ
  have hcount : (N.card:ℝ≥0∞)≤ENNReal.ofReal (2+(b-a+B.rmax)/len) := by
    rw [←ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (selectedSourceCells_card hlen hab hrmax)
  calc
    _ ≤ ENNReal.ofReal (p/256)*(∑i∈N,O i) := mul_le_mul' le_rfl hsum
    _ = ∑i∈N,ENNReal.ofReal (p/256)*O i := Finset.mul_sum _ _ _
    _ ≤ ∑i∈N,ENNReal.ofReal D*ENNReal.ofReal E := Finset.sum_le_sum hpay
    _ = (N.card:ℝ≥0∞)*(ENNReal.ofReal D*ENNReal.ofReal E) := by simp
    _ ≤ ENNReal.ofReal (2+(b-a+B.rmax)/len)*(ENNReal.ofReal D*ENNReal.ofReal E) :=
      mul_le_mul' hcount le_rfl
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity : 0≤2+(b-a+B.rmax)/len)]
      dsimp only [D,E]
      ac_rfl

lemma PhaseFlowOn.relative_closedEulerian_stable {s : Solution}
    {T M A P L a b massScale φ σ C p len : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (ha : 0≤a) (hb : b≤T) (hab : a≤b) (hp : 0<p) (hlen : 0<len)
    (hM : 0<M) (hA : 0≤A) (hP : 0<P) (hL : 0≤L)
    (hm : 0 < massScale) (hφ : 0<φ) (hσ : 0<σ) (hσ1 : σ≤1) (hconst : 128≤C)
    (hstable : 2*len≤(C*(P/massScale)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2)
    (hqmin : p/128≤B.qmin) (hqmax : B.qmax≤p/32)
    (hmq : massScale≤B.qmin) (hmw : massScale≤B.wmin)
    (hr : 0<B.rmin) (hrmax : 0≤B.rmax) (hrad : B.rmax≤len)
    (hDhi : B.Dmax≤8*φ^2) (helo : σ^2/2≤B.emin) (hehi : B.emax≤8*σ^2)
    (hq : 4≤σ*B.qmin) (hw : 4≤σ*B.wmin)
    (HX : IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L)
    (HZ : ∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) :
    coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))≤
      ENNReal.ofReal (40*B.rmax*(1+φ/σ))/ENNReal.ofReal (p/256)*
        ENNReal.ofReal ((2+(b-a+B.rmax)/len)*(∫x : Vec,totalEnergy s (0,x))) := by
  have ho := F.relative_closed_bin_stable hs hT zX B hS ha hb hab hlen hM hA hP hL
    hm hφ hσ hσ1 hconst hstable hqmin hqmax hmq hmw hr hrmax hrad hDhi helo hehi hq hw HX HZ
  have hbnd := mul_le_mul' (le_refl ((ENNReal.ofReal (p/256))⁻¹)) ho
  rw [←mul_assoc,ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (by positivity : 0<p/256)).ne'
    ENNReal.ofReal_ne_top,one_mul] at hbnd
  have he := F.closedBinEulerian_occupation_le (c:=max 0 (a-B.rmax)) (d:=min T (b-B.rmin))
    hs hT zX B hS (Icc_subset_Icc ha hb)
    (Icc_subset_Icc (le_max_left _ _) (min_le_left _ _))
  refine he.trans ((show labelOccupation (fun z=>s.f (0,z))
      (closedBinHits F.flow zX B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) ≤
      labelOccupation (fun z=>s.f (0,z)) (closedBinHits F.flow zX B S a b 0 T) from ?_).trans ?_)
  · unfold labelOccupation
    apply lintegral_mono
    intro z
    apply mul_le_mul' le_rfl
    apply measure_mono
    rintro u ⟨hz,hu,t,ht,hbin⟩
    exact ⟨hz,⟨(le_max_left _ _).trans hu.1,hu.2.trans (min_le_left _ _)⟩,t,ht,hbin⟩
  · exact hbnd.trans_eq (by simp only [div_eq_mul_inv]; ac_rfl)

lemma PhaseFlowOn.relative_closedEulerian_baseline {s : Solution}
    {T M A P L a b massScale φ σ C p len I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (ha : 0≤a) (hb : b≤T) (hab : a≤b) (hp : 0<p) (hlen : 0<len)
    (hlenI : len≤I) (hJI : b-a≤I)
    (hM : 0<M) (hA : 0≤A) (hP : 0<P) (hL : 0≤L)
    (hm : 0 < massScale) (hφ : 0<φ) (hσ : 0<σ) (hσ1 : σ≤1) (hconst : 128≤C)
    (hstable : 2*len≤(C*(P/massScale)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2)
    (hqmin : p/128≤B.qmin) (hqmax : B.qmax≤p/32)
    (hmq : massScale≤B.qmin) (hmw : massScale≤B.wmin)
    (hr : 0<B.rmin) (hrmax : 0≤B.rmax)
    (hDhi : B.Dmax≤8*φ^2) (helo : σ^2/2≤B.emin) (hehi : B.emax≤8*σ^2)
    (hq : 4≤σ*B.qmin) (hw : 4≤σ*B.wmin)
    (HX : IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L)
    (HZ : ∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) :
    coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))≤
      ENNReal.ofReal (30720*B.rmax/p*(1+φ/σ)*(1+I/len))*
        ENNReal.ofReal (∫x : Vec,totalEnergy s (0,x)) := by
  have hI : 0<I := hlen.trans_le hlenI
  have hq0 : 0<B.qmin := (div_pos hp (by norm_num)).trans_le hqmin
  by_cases hrad : B.rmax≤len
  · have ho := F.relative_closedEulerian_stable hs hT zX B hS ha hb hab hp hlen
      hM hA hP hL hm hφ hσ hσ1 hconst hstable hqmin hqmax hmq hmw hr hrmax hrad
      hDhi helo hehi hq hw HX HZ
    have hcount : 0≤2+(b-a+B.rmax)/len := by
      have : 0≤b-a+B.rmax := by linarith
      positivity
    have hfactor : 2+(b-a+B.rmax)/len≤3*(1+I/len) := by
      have hh := (div_le_div_iff_of_pos_right hlen).mpr (show b-a+B.rmax≤I+len by linarith)
      have he : (I+len)/len=I/len+1 := by field_simp
      rw [he] at hh
      nlinarith [div_nonneg hI.le hlen.le]
    rw [ENNReal.ofReal_mul hcount,←mul_assoc,←ENNReal.ofReal_div_of_pos (by positivity : 0<p/256),
      ←ENNReal.ofReal_mul (by positivity : 0≤(40*B.rmax*(1+φ/σ))/(p/256))] at ho
    apply ho.trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (40*B.rmax*(1+φ/σ))/(p/256)*(3*(1+I/len)) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = _ := by ring
  · have ho := F.closedEulerian_crude_budget hs hT zX B hS (Icc_subset_Icc ha hb) hJI hr.le hq0
    apply ho.trans
    apply mul_le_mul' _ le_rfl
    rw [←ENNReal.ofReal_div_of_pos hq0]
    apply ENNReal.ofReal_le_ofReal
    have hlenr : len≤B.rmax := (lt_of_not_ge hrad).le
    have hn : 0≤I+B.rmax := by positivity
    have hj : 1≤1+φ/σ := le_add_of_nonneg_right (div_nonneg hφ.le hσ.le)
    calc
      (I+B.rmax)/B.qmin≤(I+B.rmax)/(p/128) :=
        div_le_div_of_nonneg_left hn (by positivity) hqmin
      _ ≤ (B.rmax*(1+I/len))/(p/128) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hi : I≤B.rmax*(I/len) := by
          have hh := mul_le_mul_of_nonneg_right hlenr (div_nonneg hI.le hlen.le)
          have he : len*(I/len)=I := by field_simp
          rwa [he] at hh
        nlinarith
      _ ≤ 30720*B.rmax/p*(1+φ/σ)*(1+I/len) := by
        have he : (B.rmax*(1+I/len))/(p/128)=128*B.rmax/p*1*(1+I/len) := by ring
        rw [he]
        gcongr
        norm_num

end RVM

end

end OAI
