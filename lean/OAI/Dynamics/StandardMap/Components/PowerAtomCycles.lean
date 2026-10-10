import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Components.BirkhoffAtoms

namespace OAI

section
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace BoundedSubadditive
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

structure PowerAtomFamily (e : X ≃ᵐ X) (μ : Measure X) where
  atom : ℕ → Set X
  measurable : ∀ n,MeasurableSet (atom n)
  positive : ∀ n,0<μ (atom n)
  invariant : ∀ n,(e^[n+1]) ⁻¹' (atom n)=atom n
  ergodic : ∀ n,Ergodic (e^[n+1]) (μ.restrict (atom n))
  common : ∃ D : Set X,0<μ D ∧ ∀ n,D⊆atom n

namespace PowerAtomFamily
variable {e : X ≃ᵐ X} (F : PowerAtomFamily e μ) (he : MeasurePreserving e μ μ)

lemma refinement {n m : ℕ} (hdiv : n+1 ∣ m+1) : F.atom m ≤ᵐ[μ] F.atom n := by
  obtain ⟨D,hD,hDA⟩ := F.common
  have hi : 0<μ (F.atom m∩F.atom n) := hD.trans_le (measure_mono (fun x hx => ⟨hDA m hx,hDA n hx⟩))
  apply ergodic_restrict_subset_of_inter (F.measurable m) (F.measurable n) (F.ergodic m).toPreErgodic _ hi
  obtain ⟨q,hq⟩ := hdiv
  simpa only [hq,Function.iterate_mul,Function.IsFixedPt] using Function.IsFixedPt.preimage_iterate (F.invariant n) q

noncomputable def cycle (n : ℕ) : CyclicAtom e μ (F.atom 0) (F.atom n) (n+1) :=
  Classical.choice (finite_cycle_of_ergodic_atom e he (F.measurable 0) (F.measurable n) (F.positive n)
    (F.refinement (by simp)) (by simpa only [zero_add,Function.iterate_one] using F.invariant 0)
    (by simpa only [zero_add,Function.iterate_one] using F.ergodic 0) (Nat.succ_pos n) (F.invariant n) (F.ergodic n))

lemma periods_bounded : BddAbove (Set.range (fun n => (F.cycle he n).period)) := by
  obtain ⟨D,hD,hDA⟩ := F.common
  have hDr : 0<(μ D).toReal := ENNReal.toReal_pos hD.ne' (measure_ne_top μ D)
  obtain ⟨B,hB⟩ := exists_nat_gt ((μ (F.atom 0)).toReal/(μ D).toReal)
  refine ⟨B,?_⟩
  rintro p ⟨n,rfl⟩
  have hh : ((F.cycle he n).period : ℝ≥0∞)*μ D≤μ (F.atom 0) := by
    calc
      _ ≤ ((F.cycle he n).period : ℝ≥0∞)*μ (F.atom n) := mul_le_mul_right (measure_mono (hDA n)) _
      _ = _ := (F.cycle he n).mass
  have hr := ENNReal.toReal_mono (measure_ne_top μ (F.atom 0)) hh
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast] at hr
  have hd : ((F.cycle he n).period : ℝ)≤(μ (F.atom 0)).toReal/(μ D).toReal :=
    (le_div_iff₀ hDr).mpr hr
  exact le_of_lt (by exact_mod_cast hd.trans_lt hB)

lemma exists_max_period : ∃ n : ℕ,∀ m,(F.cycle he m).period≤(F.cycle he n).period := by
  let S := Set.range (fun n => (F.cycle he n).period)
  have hb : BddAbove S := F.periods_bounded he
  have hf : S.Finite := Set.finite_iff_bddAbove.mpr hb
  obtain ⟨n,hn⟩ := (show S.Nonempty from ⟨(F.cycle he 0).period,mem_range_self 0⟩).csSup_mem hf
  refine ⟨n,?_⟩
  intro m
  change (F.cycle he n).period=sSup S at hn
  rw [hn]
  exact le_csSup hb (mem_range_self m)

theorem exists_totally_ergodic_cycle : ∃ n : ℕ,∀ r : ℕ,0 < r →
    ∀ j : Fin (F.cycle he n).period,
      Ergodic ((e^[(F.cycle he n).period])^[r])
        (μ.restrict ((e.symm^[j.val]) ⁻¹' F.atom n)) := by
  obtain ⟨n,hn⟩ := F.exists_max_period he
  refine ⟨n,?_⟩
  intro r hr j
  let C := F.cycle he n
  let m := (n+1)*r-1
  have hm : m+1=(n+1)*r := by
    have hpos : 0<(n+1)*r := Nat.mul_pos (Nat.succ_pos n) hr
    exact Nat.sub_add_cancel hpos
  have hmn : n+1 ∣ m+1 := ⟨r,hm⟩
  have hsub := F.refinement hmn
  have hmasses : μ (F.atom n)≤μ (F.atom m) := by
    have hmul : (C.period : ℝ≥0∞)*μ (F.atom n)≤(C.period : ℝ≥0∞)*μ (F.atom m) := by
      calc
        _ = μ (F.atom 0) := C.mass
        _ = ((F.cycle he m).period : ℝ≥0∞)*μ (F.atom m) := (F.cycle he m).mass.symm
        _ ≤ _ := mul_le_mul_left (by exact_mod_cast hn m) _
    exact (ENNReal.mul_le_mul_iff_right (by exact_mod_cast C.positive.ne') (by simp)).mp hmul
  have heq : F.atom m =ᵐ[μ] F.atom n := ae_eq_of_ae_subset_of_measure_ge hsub hmasses
    (F.measurable m).nullMeasurableSet (measure_ne_top μ (F.atom n))
  have herm : Ergodic (e^[m+1]) (μ.restrict (F.atom n)) := ergodic_restrict_congr (F.ergodic m) heq
  have hbase : Ergodic (e^[C.period]) (μ.restrict (F.atom n)) := by
    simpa only [Function.iterate_zero,preimage_id_eq,id_eq] using C.ergodic ⟨0,C.positive⟩
  have ht : Ergodic ((e^[C.period])^[r]) (μ.restrict (F.atom n)) := by
    refine ⟨hbase.toMeasurePreserving.iterate r,?_⟩
    obtain ⟨q,hq⟩ := C.divides
    apply PreErgodic.of_iterate q
    have hnum : m+1=(C.period*r)*q := by
      calc
        m+1=(n+1)*r := hm
        _ = (C.period*q)*r := congrArg (fun a : ℕ => a*r) hq
        _ = _ := by ac_rfl
    simpa only [hnum,Function.iterate_mul] using herm.toPreErgodic
  have ht' : Ergodic (e^[C.period*r]) (μ.restrict (F.atom n)) := by
    simpa only [Function.iterate_mul] using ht
  simpa only [Function.iterate_mul] using ergodic_translate e he (F.measurable n) ht' j.val

end PowerAtomFamily
end BoundedSubadditive

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal
open NonlinearStable

theorem exists_reversibleRectangleBlock (k : ℝ) (hk : 0≤k) {χ : ℝ} (hχ : 0<χ)
    (hgap : 0<area (spectralGapRegion k hk χ)) : Nonempty (ReversibleRectangleBlock k χ) := by
  obtain ⟨ε,δ₀,hε,hδ₀,hδ₀',hq₀,hslow₀,_⟩ := fine_holonomy_parameters hχ (by norm_num : (0 : ℝ)<1)
  obtain ⟨C,hC,hCpos,hCG,hdata,hreg⟩ := compact_lift_reversible_block k hk hχ hε hgap
  obtain ⟨w,hwC,hw⟩ := positive_compact_neighborhood hC hCpos
  have hwreg : wedge (stableVector k (complexProjection w)) (unstableVector k (complexProjection w))≠0 :=
    (hreg w hwC).1 0 |>.1.1
  have hwRreg : wedge (stableVector k (complexProjection (tangentReversal w)))
      (unstableVector k (complexProjection (tangentReversal w)))≠0 := (hreg w hwC).2.1 0 |>.1.1
  obtain ⟨α,β,hα,hβ,hswap⟩ := fine_reversal_frame_swap k χ ε (complexProjection w) hwreg
    (by simpa only [complexProjection_tangentReversal] using hwRreg)
    (by simpa only [complexProjection_tangentReversal] using (hreg w hwC).2.2.2.1)
    (by simpa only [complexProjection_tangentReversal] using (hreg w hwC).2.2.2.2)
  let η := min (1/16) (|α|/(16*|β|))
  have hη : 0<η := lt_min (by norm_num) (div_pos (abs_pos.mpr hα) (by positivity))
  have hηsmall : η≤1/16 := min_le_left _ _
  have hηscale : (|β|/|α|)*((8/3)*η)≤1/2 := by
    have hh := (le_div_iff₀ (by positivity : 0<16*|β|)).mp
      (show η≤|α|/(16*|β|) from min_le_right _ _)
    have he : (|β|/|α|)*((8/3)*η)=(|β| *((8/3)*η))/|α| := by ring
    rw [he]
    apply (div_le_iff₀ (abs_pos.mpr hα)).mpr
    nlinarith [abs_pos.mpr hα]
  obtain ⟨δ,hδ,hδ',hq,hslow,hslope⟩ := shrink_fine_holonomy_delta hδ₀ hδ₀' hq₀ hslow₀ hη
  let R := codingRadius k χ ε δ (complexProjection w)/2
  let R' := codingRadius k χ ε δ (complexProjection (tangentReversal w))/2
  have hR : 0<R := half_pos (codingRadius_pos k χ ε hδ _)
  have hR' : 0<R' := half_pos (codingRadius_pos k χ ε hδ _)
  obtain ⟨r,hr,hrsmall,hsize⟩ := small_chart_radius (fineScale k ε δ) R (fineScale_pos k ε hδ).le hR
  obtain ⟨r',hr',hrsmall',hsize'⟩ := small_chart_radius (fineScale k ε δ) R' (fineScale_pos k ε hδ).le hR'
  let ρ := min (r/8) (|α| *r'/8)
  have hρ : 0<ρ := lt_min (by positivity) (by positivity)
  have hρr : ρ≤r/8 := min_le_left _ _
  have hρr' : ρ≤|α| *r'/8 := min_le_right _ _
  have hdc : Continuous (fun v : C => (orbitChartData k χ ε (complexProjection v),
      orbitChartData k χ ε (complexProjection (tangentReversal v)))) :=
    continuousOn_iff_continuous_domRestrict.mp hdata
  have hd0 : Continuous (fun v : C => lyapunovChartData k χ ε (complexProjection v)) :=
    ((continuous_apply 0).comp hdc.fst).fst
  have hdR0 : Continuous (fun v : C => lyapunovChartData k χ ε (complexProjection (tangentReversal v))) :=
    ((continuous_apply 0).comp hdc.snd).fst
  have hF : ContinuousOn (fun v => fineFrame k χ ε δ (complexProjection v)) C :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_fineFrame_of_data k χ ε δ _ hd0)
  have hI : ContinuousOn (fun v => fineInverse k χ ε δ (complexProjection v)) C :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_fineInverse_of_data k χ ε δ hδ _ hd0)
  have hFR : ContinuousOn (fun v => fineFrame k χ ε δ (complexProjection (tangentReversal v))) C :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_fineFrame_of_data k χ ε δ _ hdR0)
  have hIR : ContinuousOn (fun v => fineInverse k χ ε δ (complexProjection (tangentReversal v))) C :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_fineInverse_of_data k χ ε δ hδ _ hdR0)
  have hrad : ContinuousOn (fun v => codingRadius k χ ε δ (complexProjection v)) C :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_const.mul (hd0.snd.snd.pow 2))
  have hradR : ContinuousOn (fun v => codingRadius k χ ε δ (complexProjection (tangentReversal v))) C :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_const.mul (hdR0.snd.snd.pow 2))
  have hIF : (fineInverse k χ ε δ (complexProjection w)).comp (fineFrame k χ ε δ (complexProjection w))=
      ContinuousLinearMap.id ℝ Plane := by
    apply ContinuousLinearMap.ext
    exact fineInverse_frame k χ ε hδ _ hwreg
  have hIFR : (fineInverse k χ ε δ (complexProjection (tangentReversal w))).comp
      (fineFrame k χ ε δ (complexProjection (tangentReversal w)))=ContinuousLinearMap.id ℝ Plane := by
    apply ContinuousLinearMap.ext
    exact fineInverse_frame k χ ε hδ _ hwRreg
  have hclose : ∀ᶠ v in 𝓝[C] w,‖(fineInverse k χ ε δ (complexProjection w)).comp
      (fineFrame k χ ε δ (complexProjection v))-ContinuousLinearMap.id ℝ Plane‖<η := by
    have hc : ContinuousWithinAt (fun v => ‖(fineInverse k χ ε δ (complexProjection w)).comp
        (fineFrame k χ ε δ (complexProjection v))-ContinuousLinearMap.id ℝ Plane‖) C w := (((continuousOn_const.clm_comp hF).sub continuousOn_const).norm w hwC)
    apply hc.eventually (p := fun y : ℝ => y<η)
    simp only [hIF,sub_self,norm_zero]
    exact eventually_lt_nhds hη
  have hcloseR : ∀ᶠ v in 𝓝[C] w,‖(fineInverse k χ ε δ (complexProjection (tangentReversal w))).comp
      (fineFrame k χ ε δ (complexProjection (tangentReversal v)))-ContinuousLinearMap.id ℝ Plane‖<η := by
    have hc : ContinuousWithinAt (fun v => ‖(fineInverse k χ ε δ (complexProjection (tangentReversal w))).comp
        (fineFrame k χ ε δ (complexProjection (tangentReversal v)))-ContinuousLinearMap.id ℝ Plane‖) C w := (((continuousOn_const.clm_comp hFR).sub continuousOn_const).norm w hwC)
    apply hc.eventually (p := fun y : ℝ => y<η)
    simp only [hIFR,sub_self,norm_zero]
    exact eventually_lt_nhds hη
  have hco : ∀ᶠ v in 𝓝[C] w,‖(fineInverse k χ ε δ (complexProjection v)).comp
      (fineFrame k χ ε δ (complexProjection w))-ContinuousLinearMap.id ℝ Plane‖<1/4 := by
    have hc : ContinuousWithinAt (fun v => ‖(fineInverse k χ ε δ (complexProjection v)).comp
        (fineFrame k χ ε δ (complexProjection w))-ContinuousLinearMap.id ℝ Plane‖) C w := (((hI.clm_comp continuousOn_const).sub continuousOn_const).norm w hwC)
    apply hc.eventually (p := fun y : ℝ => y<1/4)
    simp only [hIF,sub_self,norm_zero]
    exact eventually_lt_nhds (by norm_num)
  have hcoR : ∀ᶠ v in 𝓝[C] w,‖(fineInverse k χ ε δ (complexProjection (tangentReversal v))).comp
      (fineFrame k χ ε δ (complexProjection (tangentReversal w)))-ContinuousLinearMap.id ℝ Plane‖<1/4 := by
    have hc : ContinuousWithinAt (fun v => ‖(fineInverse k χ ε δ (complexProjection (tangentReversal v))).comp
        (fineFrame k χ ε δ (complexProjection (tangentReversal w)))-ContinuousLinearMap.id ℝ Plane‖) C w := (((hIR.clm_comp continuousOn_const).sub continuousOn_const).norm w hwC)
    apply hc.eventually (p := fun y : ℝ => y<1/4)
    simp only [hIFR,sub_self,norm_zero]
    exact eventually_lt_nhds (by norm_num)
  have hRl : ∀ᶠ v in 𝓝[C] w,R<codingRadius k χ ε δ (complexProjection v) := by
    apply (hrad w hwC).eventually
    exact eventually_gt_nhds (by dsimp only [R]; linarith [codingRadius_pos k χ ε hδ (complexProjection w)])
  have hRRl : ∀ᶠ v in 𝓝[C] w,R'<codingRadius k χ ε δ (complexProjection (tangentReversal v)) := by
    apply (hradR w hwC).eventually
    exact eventually_gt_nhds (by dsimp only [R']; linarith [codingRadius_pos k χ ε hδ (complexProjection (tangentReversal w))])
  have hcentral : ∀ᶠ v in 𝓝[C] w,‖fineInverse k χ ε δ (complexProjection w) (v-w)‖<ρ/100 := by
    have hc : Continuous (fun v : ℂ => ‖fineInverse k χ ε δ (complexProjection w) (v-w)‖) := by fun_prop
    apply (hc.continuousWithinAt (s := C) (x := w)).eventually (p := fun y : ℝ => y<ρ/100)
    simp only [sub_self,map_zero,norm_zero]
    exact eventually_lt_nhds (by positivity)
  have hcentralR : ∀ᶠ v in 𝓝[C] w,‖fineInverse k χ ε δ (complexProjection (tangentReversal w))
      (tangentReversal v-tangentReversal w)‖<r'/4 := by
    have hc : Continuous (fun v : ℂ => ‖fineInverse k χ ε δ (complexProjection (tangentReversal w))
        (tangentReversal v-tangentReversal w)‖) := by fun_prop
    apply (hc.continuousWithinAt (s := C) (x := w)).eventually (p := fun y : ℝ => y<r'/4)
    simp only [sub_self,map_zero,norm_zero]
    exact eventually_lt_nhds (by positivity)
  obtain ⟨K,hKC,hK,hKpos,hKP⟩ := hw
    (fun v => R<codingRadius k χ ε δ (complexProjection v) ∧
      R'<codingRadius k χ ε δ (complexProjection (tangentReversal v)) ∧
      ‖(fineInverse k χ ε δ (complexProjection w)).comp (fineFrame k χ ε δ (complexProjection v))-
        ContinuousLinearMap.id ℝ Plane‖<η ∧
      ‖(fineInverse k χ ε δ (complexProjection (tangentReversal w))).comp
        (fineFrame k χ ε δ (complexProjection (tangentReversal v)))-ContinuousLinearMap.id ℝ Plane‖<η ∧
      ‖(fineInverse k χ ε δ (complexProjection v)).comp (fineFrame k χ ε δ (complexProjection w))-
        ContinuousLinearMap.id ℝ Plane‖<1/4 ∧
      ‖(fineInverse k χ ε δ (complexProjection (tangentReversal v))).comp
        (fineFrame k χ ε δ (complexProjection (tangentReversal w)))-ContinuousLinearMap.id ℝ Plane‖<1/4 ∧
      ‖fineInverse k χ ε δ (complexProjection w) (v-w)‖<ρ/100 ∧
      ‖fineInverse k χ ε δ (complexProjection (tangentReversal w)) (tangentReversal v-tangentReversal w)‖<r'/4)
    (hRl.and (hRRl.and (hclose.and (hcloseR.and (hco.and (hcoR.and (hcentral.and hcentralR)))))))
  exact ⟨{
    ε := ε,δ := δ,ε_pos := hε,δ_pos := hδ,δ_small := hδ',contraction := hq,slow := hslow,
    carrier := K,compact := hK,positive := hKpos,centre := w,centre_regular := hwreg,reverse_regular := hwRreg,
    α := α,β := β,α_ne := hα,β_ne := hβ,
    swap := by simpa only [complexProjection_tangentReversal] using hswap δ hδ.ne',
    η := η,η_pos := hη,η_small := hηsmall,slope := hslope,reverse_slope := hηscale,
    r := r,r' := r',R := R,R' := R',ρ := ρ,r_pos := hr,r'_pos := hr',R_pos := hR,R'_pos := hR',ρ_pos := hρ,
    r_small := hrsmall,r'_small := hrsmall',ρ_small := hρr,ρ_reverse := hρr',size := hsize,reverse_size := hsize',
    data := hdata.mono hKC,
    regular := fun v hv n => ((hreg v (hKC hv)).1 n).1,
    reversed := fun v hv n => ((hreg v (hKC hv)).2.1 n).1,
    radius := fun v hv => (hKP v hv).1.le,
    reverse_radius := fun v hv => (hKP v hv).2.1.le,
    frames := fun v hv => (hKP v hv).2.2.1.le,
    reverse_frames := fun v hv => (hKP v hv).2.2.2.1.le,
    coframes := fun v hv => (hKP v hv).2.2.2.2.1.le,
    reverse_coframes := fun v hv => (hKP v hv).2.2.2.2.2.1.le,
    central := fun v hv => (hKP v hv).2.2.2.2.2.2.1.le,
    reverse_central := fun v hv => (hKP v hv).2.2.2.2.2.2.2.le }⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
open BoundedSubadditive

theorem actual_hyperbolic_ergodic_component (k : ℝ) (hk : 0≤k) {χ : ℝ} (hχ : 0<χ)
    (hgap : 0<area (spectralGapRegion k hk χ)) :
    ∃ E : Set Torus,MeasurableSet E ∧ 0<area E ∧
      standardMap k ⁻¹' E=E ∧ Ergodic (standardMap k) (normalizedArea E) ∧
      (∀ᵐ z ∂normalizedArea E,∃ l : ℝ,0<l ∧ LyapunovSpectrumAt k z l) := by
  obtain ⟨B⟩ := exists_reversibleRectangleBlock k hk hχ hgap
  obtain ⟨F⟩ := reversible_graph_families B
  obtain ⟨R⟩ := reversible_graph_rectangle F hk
  obtain ⟨C⟩ := exists_continuousBirkhoffCode (measurePreserving_standardMap k) (measurePreserving_inverseMap k)
    (inverseMap_standardMap k) (standardMap_inverseMap k)
  obtain ⟨c,hc⟩ := actual_rectangle_hopf_atom hk R C
  let E := {z | C.value z=c}
  let H := {z | 0<standardLyapunov k hk z}
  have hE : MeasurableSet E := C.measurableSet_atom c
  have hH : MeasurableSet H := measurableSet_lt measurable_const (measurable_standardLyapunov k hk)
  have hpos : 0<area E := hc.trans_le (measure_mono inter_subset_left)
  have hTH : standardMap k ⁻¹' H=H := by
    ext z
    simp only [H,mem_preimage,mem_ofPred_eq,standardLyapunov_invariant]
  have herg : Ergodic (standardMap k) (normalizedArea E) := C.ergodic_atom (measurePreserving_standardMap k) hpos
  have hHinE : 0<normalizedArea E H := by
    unfold normalizedArea
    rw [Measure.smul_apply,Measure.restrict_apply hH,smul_eq_mul,inter_comm H E]
    exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr (measure_ne_top area E)) hc.ne'
  have hAE : ∀ᵐ z ∂normalizedArea E,z∈H := by
    rcases herg.toPreErgodic.ae_mem_or_ae_notMem hH hTH with h|h
    · exact h
    · have hz : normalizedArea E H=0 := by
        simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using h
      exact (hHinE.ne' hz).elim
  have hac : normalizedArea E≪area := smul_absolutelyContinuous.trans Measure.absolutelyContinuous_restrict
  refine ⟨E,hE,hpos,C.invariant_atom c,herg,?_⟩
  filter_upwards [hAE,hac.ae_le (ae_standardLyapunov_spectrum k hk)] with z hz hs
  exact ⟨standardLyapunov k hk z,hz,hs⟩

lemma exists_positive_spectral_gap (k : ℝ) (hk : 0≤k)
    (hpos : 0<area {z | 0<standardLyapunov k hk z}) :
    ∃ χ : ℝ,0<χ ∧ 0<area (spectralGapRegion k hk χ) := by
  by_contra h
  push Not at h
  have hz (n : ℕ) : area (spectralGapRegion k hk (1/((n : ℝ)+1)))=0 :=
    le_antisymm (h _ (by positivity)) (bot_le)
  have hsub : {z | 0<standardLyapunov k hk z}⊆⋃ n : ℕ,spectralGapRegion k hk (1/((n : ℝ)+1)) := by
    intro z hzL
    obtain ⟨n,hn⟩ := exists_nat_gt (1/standardLyapunov k hk z)
    apply mem_iUnion.mpr
    refine ⟨n,?_⟩
    change 1/((n : ℝ)+1)<standardLyapunov k hk z
    apply (div_lt_iff₀ (by positivity : (0:ℝ)<(n : ℝ)+1)).mpr
    have ha := (div_lt_iff₀ hzL).mp hn
    nlinarith
  exact hpos.ne' (measure_mono_null hsub (measure_iUnion_null hz))

theorem eventually_actual_hyperbolic_ergodic_component :
    ∃ k₀ : ℝ,0<k₀ ∧ ∀ k : ℝ,k₀≤k →
      ∃ E : Set Torus,MeasurableSet E ∧ 0<area E ∧
        standardMap k ⁻¹' E=E ∧ Ergodic (standardMap k) (normalizedArea E) ∧
        (∀ᵐ z ∂normalizedArea E,∃ l : ℝ,0<l ∧ LyapunovSpectrumAt k z l) := by
  obtain ⟨K,hK,hdef⟩ := eventually_meanDeficit_small (1/8 : ℝ) (by norm_num)
  refine ⟨K,hK,?_⟩
  intro k hk
  have hk0 : 0≤k := hK.le.trans hk
  obtain ⟨χ,hχ,hgap⟩ := exists_positive_spectral_gap k hk0 (positive_standardLyapunov_of_deficit k hk0 (hdef k hk))
  exact actual_hyperbolic_ergodic_component k hk0 hχ hgap

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
open BoundedSubadditive

theorem actual_powerAtomFamily (k : ℝ) (hk : 0≤k) {χ : ℝ} (hχ : 0<χ)
    (hgap : 0<area (spectralGapRegion k hk χ)) :
    ∃ F : PowerAtomFamily (standardMap_measurableEquiv k) area,
      0<area (F.atom 0∩{z | 0<standardLyapunov k hk z}) := by
  obtain ⟨B⟩ := exists_reversibleRectangleBlock k hk hχ hgap
  obtain ⟨G⟩ := reversible_graph_families B
  obtain ⟨R⟩ := reversible_graph_rectangle G hk
  obtain ⟨C⟩ := exists_powerBirkhoffCodes k
  obtain ⟨c,hc⟩ := actual_rectangle_all_powers_atom hk R C
  let D := {z | ∀ m,(C m).value z=c m}∩{z | 0<standardLyapunov k hk z}
  let A (n : ℕ) : Set Torus := {z | (C n).value z=c n}
  have hD (n : ℕ) : D⊆A n := fun _ hx => hx.1 n
  have hpos (n : ℕ) : 0<area (A n) := hc.trans_le (measure_mono (hD n))
  let F : PowerAtomFamily (standardMap_measurableEquiv k) area := {
    atom := A
    measurable := fun n => (C n).measurableSet_atom (c n)
    positive := hpos
    invariant := fun n => (C n).invariant_atom (c n)
    ergodic := fun n => ergodic_restrict_of_normalized (hpos n)
      ((C n).ergodic_atom ((measurePreserving_standardMap k).iterate (n+1)) (hpos n))
    common := ⟨D,hc,hD⟩ }
  exact ⟨F,hc.trans_le (measure_mono (fun _ hx => ⟨hx.1 0,hx.2⟩))⟩

lemma positive_spectrum_on_ergodic_component (k : ℝ) (hk : 0≤k) {E : Set Torus}
    (hE : MeasurableSet E) (herg : Ergodic (standardMap k) (normalizedArea E))
    (hpos : 0<area (E∩{z | 0<standardLyapunov k hk z})) :
    ∀ᵐ z ∂normalizedArea E,∃ l : ℝ,0<l ∧ LyapunovSpectrumAt k z l := by
  let H := {z | 0<standardLyapunov k hk z}
  have hH : MeasurableSet H := measurableSet_lt measurable_const (measurable_standardLyapunov k hk)
  have hTH : standardMap k ⁻¹' H=H := by
    ext z
    simp only [H,mem_preimage,mem_ofPred_eq,standardLyapunov_invariant]
  have hHinE : 0<normalizedArea E H := by
    unfold normalizedArea
    rw [Measure.smul_apply,Measure.restrict_apply' hE,smul_eq_mul,inter_comm H E]
    exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr (measure_ne_top area E)) hpos.ne'
  have hAE : ∀ᵐ z ∂normalizedArea E,z∈H := by
    rcases herg.toPreErgodic.ae_mem_or_ae_notMem hH hTH with h|h
    · exact h
    · have hz : normalizedArea E H=0 := by
        simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using h
      exact (hHinE.ne' hz).elim
  have hac : normalizedArea E≪area := smul_absolutelyContinuous.trans Measure.absolutelyContinuous_restrict
  filter_upwards [hAE,hac.ae_le (ae_standardLyapunov_spectrum k hk)] with z hz hs
  exact ⟨standardLyapunov k hk z,hz,hs⟩

theorem actual_cyclic_totally_ergodic_component (k : ℝ) (hk : 0≤k) {χ : ℝ} (hχ : 0<χ)
    (hgap : 0<area (spectralGapRegion k hk χ)) :
    ∃ E : Set Torus,MeasurableSet E ∧ 0<area E ∧
      (standardMap k ⁻¹' E=E) ∧ Ergodic (standardMap k) (normalizedArea E) ∧
      (∀ᵐ z ∂normalizedArea E,∃ l : ℝ,0<l ∧ LyapunovSpectrumAt k z l) ∧
      ∃ (N : ℕ) (hN : 0<N) (P : Fin N → Set Torus),
        (∀ j,MeasurableSet (P j)) ∧ ((⋃ j,P j) =ᵐ[area] E) ∧
        (∀ i j,i≠j → area (P i∩P j)=0) ∧
        (∀ j,(standardMap k '' P j) =ᵐ[area] P ⟨(j.val+1)%N,Nat.mod_lt _ hN⟩) ∧
        (∀ j,area (P j)=area E/(N : ℝ≥0∞) ∧ 0<area (P j)) ∧
        (∀ j,∀ r : ℕ,0<r → Ergodic (((standardMap k)^[N])^[r]) (normalizedArea (P j))) := by
  obtain ⟨F,hFH⟩ := actual_powerAtomFamily k hk hχ hgap
  have he : MeasurePreserving (standardMap_measurableEquiv k) area area := measurePreserving_standardMap k
  obtain ⟨n,hn⟩ := F.exists_totally_ergodic_cycle he
  let C := F.cycle he n
  let P (j : Fin C.period) : Set Torus := ((standardMap_measurableEquiv k).symm^[j.val]) ⁻¹' F.atom n
  have hP (j : Fin C.period) : MeasurableSet (P j) :=
    (F.measurable n).preimage ((standardMap_measurableEquiv k).symm.measurable.iterate j.val)
  have hPmass (j : Fin C.period) : area (P j)=area (F.atom n) :=
    ((he.symm (standardMap_measurableEquiv k)).iterate j.val).measure_preimage (F.measurable n).nullMeasurableSet
  have hEerg : Ergodic (standardMap k) (normalizedArea (F.atom 0)) := by
    have hh := (F.ergodic 0).smul_measure (area (F.atom 0))⁻¹
    simp only [zero_add,Function.iterate_one] at hh
    exact hh
  refine ⟨F.atom 0,F.measurable 0,F.positive 0,?_,hEerg,
    positive_spectrum_on_ergodic_component k hk (F.measurable 0) hEerg hFH,
    C.period,C.positive,P,hP,C.cover,C.disjoint,C.forward,?_,?_⟩
  · have hh := F.invariant 0
    simp only [zero_add,Function.iterate_one] at hh
    exact hh
  · intro j
    rw [hPmass]
    exact ⟨(ENNReal.eq_div_iff (by exact_mod_cast C.positive.ne') (by simp)).mpr C.mass,F.positive n⟩
  · intro j r hr
    exact (hn r hr j).smul_measure (area (P j))⁻¹

theorem eventually_actual_cyclic_totally_ergodic_component :
    ∃ k₀ : ℝ,0<k₀ ∧ ∀ k : ℝ,k₀≤k →
    ∃ E : Set Torus,MeasurableSet E ∧ 0<area E ∧
      (standardMap k ⁻¹' E=E) ∧ Ergodic (standardMap k) (normalizedArea E) ∧
      (∀ᵐ z ∂normalizedArea E,∃ l : ℝ,0<l ∧ LyapunovSpectrumAt k z l) ∧
      ∃ (N : ℕ) (hN : 0<N) (P : Fin N → Set Torus),
        (∀ j,MeasurableSet (P j)) ∧ ((⋃ j,P j) =ᵐ[area] E) ∧
        (∀ i j,i≠j → area (P i∩P j)=0) ∧
        (∀ j,(standardMap k '' P j) =ᵐ[area] P ⟨(j.val+1)%N,Nat.mod_lt _ hN⟩) ∧
        (∀ j,area (P j)=area E/(N : ℝ≥0∞) ∧ 0<area (P j)) ∧
        (∀ j,∀ r : ℕ,0<r → Ergodic (((standardMap k)^[N])^[r]) (normalizedArea (P j))) := by
  obtain ⟨K,hK,hdef⟩ := eventually_meanDeficit_small (1/8 : ℝ) (by norm_num)
  refine ⟨K,hK,?_⟩
  intro k hk
  have hk0 : 0≤k := hK.le.trans hk
  obtain ⟨χ,hχ,hgap⟩ := exists_positive_spectral_gap k hk0 (positive_standardLyapunov_of_deficit k hk0 (hdef k hk))
  exact actual_cyclic_totally_ergodic_component k hk0 hχ hgap

end StandardMapEntropy

end
end

end OAI
