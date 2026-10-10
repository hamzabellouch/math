import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.SelectedDirection
import OAI.Analysis.VlasovMaxwell.Retarded.ConeForceSplit

namespace OAI

noncomputable section

namespace RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


private lemma SmoothClassicalPrefix.directionCountsEnergyPrefix
    {datum : Datum} {solution : Solution} {horizon : ℝ}
    (hs : SmoothClassicalPrefix datum solution horizon) : EnergyPrefix solution horizon := by
  refine ⟨(hs.f_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.E_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.B_smooth.of_le (by decide)).mono (fun _ hp => hp.1),hs.nonnegative,
    hs.E_L2,hs.B_L2,hs.compact,?_,?_⟩
  · intro time ht position momentum
    have hh := (hs.equations time ht.1.le ht.2).1 position momentum
    rwa [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at hh
  · intro time ht position
    have he := (hs.equations time ht.1.le ht.2).2.1 position
    have hb := (hs.equations time ht.1.le ht.2).2.2.1 position
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at he hb
    exact ⟨he,hb⟩

def directionRemaining : Set (Fin 4→ℕ) :=
  {k | cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1)}

lemma direction_unselected_source_sum {T w P : ℝ} (f g h : (Fin 4→ℕ)→ℝ≥0∞)
    (hfg : ∀k,f k≤ENNReal.ofReal 64*g k) (hfh : ∀k,f k≤h k)
    (hzero : ∀k,¬sourceRepresentative (k 0)≤128*P→h k=0) :
    (∑'k,(directionSelection T)ᶜ.indicator f k)≤
      ENNReal.ofReal 64*(∑'k,directionRemaining.indicator g k)+
        (∑'k,(directionSourceFar T w P).indicator h k)+
        (∑'k,(directionSourceLow w).indicator h k) := by
  classical
  rw [←ENNReal.tsum_mul_left,←ENNReal.tsum_add,←ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : k∈(directionSelection T)ᶜ
  · rw [Set.indicator_of_mem hk]
    by_cases hr : k∈directionRemaining
    · rw [Set.indicator_of_mem hr]
      exact (hfg k).trans ((le_add_of_nonneg_right bot_le).trans (le_add_of_nonneg_right bot_le))
    · have hθ : cappedRepresentative (k 1)≤(1/1024)*cappedRepresentative (k 2) := by
        have hpos := cappedRepresentative_pos (k 1)
        have hn : ¬cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1) := hr
        linarith only [lt_of_not_ge hn,hpos]
      have hsmall : cappedRepresentative (k 1)≤ cappedRepresentative (k 2)/16 := by
        have hpos := cappedRepresentative_pos (k 2)
        linarith only [hθ,hpos]
      have hprod : 1<sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3)) := by
        by_contra hh
        exact hk ⟨hθ,le_of_not_gt hh⟩
      by_cases hp : sourceRepresentative (k 0)≤128*P
      · by_cases hl : cappedRepresentative (k 2)*w≤32
        · rw [Set.indicator_of_mem (show k∈directionSourceLow w from ⟨hsmall,hl⟩)]
          exact (hfh k).trans (le_add_of_nonneg_left bot_le)
        · rw [Set.indicator_of_mem (show k∈directionSourceFar T w P from
            ⟨hp,hsmall,(lt_of_not_ge hl).le,by linarith only [hprod]⟩)]
          exact (hfh k).trans ((le_add_of_nonneg_left bot_le).trans (le_add_of_nonneg_right bot_le))
      · exact (hfh k).trans ((hzero k hp) ▸ bot_le)
  · rw [Set.indicator_of_notMem hk]
    exact bot_le

lemma PhaseFlowOn.unselected_source_label_physical_sum {s : Solution} {T w P : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (hw : 0<w) (zX : Phase) {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    (hq : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖)
    (hP : 1≤P) (hL : 1≤Real.log (2+P))
    (hsource : ∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) :
    let X := fun t=>(prefixFlow F.flow T zX t).1
    let V := fun t=>(prefixFlow F.flow T zX t).2
    let Q := directionSelection T
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator (prefixAngularMultiplier s F.flow T w hw zX)
      (labelReceiverTime F.flow zX T p)
      (labelSelectedCutoff F.flow zX T Qᶜ p • labelConeKernel s F.flow zX T (sourceOnlyConeKernel s F.flow zX) p)‖)≤
    ENNReal.ofReal 64*(∑'k,directionRemaining.indicator (fun k=>∫⁻z : ConeCoordinate,
      physicalSourceMajorantDensity s X V (representativeClosedBin T w k) z
        ∂physicalBinMeasure V (representativeClosedBin T w k) J) k)+
    (∑'k,(directionSourceFar T w P).indicator (fun k=>∫⁻z : ConeCoordinate,
      physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
        ∂physicalBinMeasure V (representativeClosedBin T w k) J) k)+
    (∑'k,(directionSourceLow w).indicator (fun k=>∫⁻z : ConeCoordinate,
      physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
        ∂physicalBinMeasure V (representativeClosedBin T w k) J) k) := by
  classical
  dsimp only
  have hA : ContinuousOn (sourceOnlyConeKernel s F.flow zX) (coneKernelInterior T) :=
    (F.sourceOnlyConeKernel_continuousOn hs zX).mono inter_subset_left
  have hW := (F.prefixAngular_regular hs hT hw zX).1.measurable
  rw [F.selectedConeTriangle_norm_transfer hs hT zX (directionSelection T)ᶜ hA hW hJ]
  apply (F.selectedConeTriangle_physical_sum hs hT zX (directionSelection T)ᶜ hA hW hJ hJT hq).trans
  have hα := (F.continuous_prefixFlow hs hT).comp
    (continuous_id.prodMk continuous_const : Continuous (fun t : ℝ=>(t,zX)))
  apply direction_unselected_source_sum
  · intro k
    rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hα.snd.measurable (representativeClosedBin T w k) hJ)] with z hz
    exact F.selectedSourceTriangle_majorant_le hs hw zX _ hJT hband _ hz
  · intro k
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hα.snd.measurable (representativeClosedBin T w k) hJ)] with z hz
    exact F.selectedSourceTriangle_density_le hw zX _ _ hJT hband _ hz
  · intro k hk
    obtain ⟨Cn,hCn,hcount⟩ := exists_direct_dyadic_count
    obtain ⟨N,hN,_⟩ := hcount P hP hL
    have h1024 : 1024*P≤(2:ℝ)^N := by linarith only [hN,hP]
    apply F.physicalProjectedSource_integral_source_truncate hs hsource N h1024
      (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>(prefixFlow F.flow T zX t).2)
      (directionSelection T) hα.snd.measurable hJ hJT w k
    intro hc
    exact hk hc.2.2

lemma PhaseFlowOn.selected_transport_label_le {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (hw : 0<w) (zX : Phase) (Q : Set (Fin 4→ℕ)) {J : Set ℝ}
    (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator (prefixAngularMultiplier s F.flow T w hw zX)
      (labelReceiverTime F.flow zX T p)
      (labelSelectedCutoff F.flow zX T Q p • labelConeKernel s F.flow zX T (transportOnlyConeKernel F.flow zX) p)‖)≤
      ENNReal.ofReal 64*(∫⁻p,directTriangleDensity s (fun t=>(prefixFlow F.flow T zX t).1) T J
        (directTransportTriangleKernel (fun t=>(prefixFlow F.flow T zX t).2)) p ∂trianglePhaseMeasure) := by
  have hA : ContinuousOn (transportOnlyConeKernel F.flow zX) (coneKernelInterior T) :=
    (F.transportOnlyConeKernel_continuousOn zX).mono inter_subset_left
  have hW := (F.prefixAngular_regular hs hT hw zX).1.measurable
  rw [F.selectedConeTriangle_norm_transfer hs hT zX Q hA hW hJ,
    ←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_mono (F.selectedTransportTriangle_le hw zX Q hJT hband)

lemma PhaseFlowOn.unselected_force_label_integral_split {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) {J : Set ℝ} (hJ : MeasurableSet J) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator W (labelReceiverTime F.flow zX T p)
      ((1-labelSelectedCutoff F.flow zX T Q p) • actualLabelSignedForce s F.flow zX T p)‖)≤
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator W (labelReceiverTime F.flow zX T p)
      (labelSelectedCutoff F.flow zX T Qᶜ p • labelConeKernel s F.flow zX T (transportOnlyConeKernel F.flow zX) p)‖)+
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator W (labelReceiverTime F.flow zX T p)
      (labelSelectedCutoff F.flow zX T Qᶜ p • labelConeKernel s F.flow zX T (sourceOnlyConeKernel s F.flow zX) p)‖) := by
  apply (lintegral_mono (F.unselected_force_norm_split zX Q W J)).trans_eq
  apply lintegral_add_left
  exact ((continuous_fst.clm_apply continuous_snd).measurable.comp
    (((hW.indicator hJ).comp (F.labelReceiverTime_measurable zX)).prodMk
      ((F.selectedCutoff_measurable zX Qᶜ).smul
        (F.measurable_labelConeKernel hs zX (F.transportOnlyConeKernel_continuousOn zX))))).norm.ennreal_ofReal

lemma Admissible.direction_unselected_label_log_bound {d : Datum} (hd₀ : Admissible d)
    (T₀ : ℝ) :
    ∃Ct Cr Cf Cl : ℝ,0≤Ct ∧ 0≤Cr ∧ 0≤Cf ∧ 0≤Cl ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → T≤T₀ → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (a b w M A P : ℝ) (hw : 0<w),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → a≤b → b-a≤(w/P)^2 →
      0<M → 0≤A → 1≤P → 1≤Real.log (2+P) → 1≤w → w≤P → P≤w^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖(Icc a b).indicator (prefixAngularMultiplier s F.flow T w hw zX)
        (labelReceiverTime F.flow zX T p)
        ((1-labelSelectedCutoff F.flow zX T (directionSelection T) p) • actualLabelSignedForce s F.flow zX T p)‖)≤
      ENNReal.ofReal (Ct*(1+E)*(1+16384*(M+Real.sqrt A))*max 1 T*w*(Real.log (2+P))^5)+
      ENNReal.ofReal (Cr*(1+E)*(1+M+Real.sqrt A)*w*(Real.log (2+P))^5)+
      ENNReal.ofReal (Cf*E*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^5)+
      ENNReal.ofReal (Cl*(1+E)*(max 1 T)^2*(Real.log (2+P))^2) := by
  classical
  obtain ⟨Ct,hCt,htransport⟩ := hd₀.direct_transport_sharp_physical_log_bound
  obtain ⟨Cr,hCr,hremaining⟩ := hd₀.source_majorant_remaining_log_sum
  obtain ⟨Cf,hCf,hfar⟩ := hd₀.projected_source_stable_far_log_sum T₀
  obtain ⟨Cl,hCl,hlow⟩ := hd₀.projected_source_low_receiver_log_sum
  refine ⟨64*Ct,64*Cr,Cf,Cl,by positivity,by positivity,hCf,hCl,?_⟩
  intro s T F hs hT hTT h0 zX S a b w M A P hw hS hS0 ha hb hab hJI hM hA hP hL hw1 hwP hPw hsource hq hW HX HZ
  dsimp only
  let E := ∫x : Vec,totalEnergy s (0,x)
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have ht := (F.selected_transport_label_le hs hT hw zX (directionSelection T)ᶜ measurableSet_Icc hJ hW).trans
    (mul_le_mul' le_rfl (htransport s T F hs hT h0 zX S a b w M A P hS hS0 ha hb hJI hM hA hw1 hP hwP hL hsource hq HX HZ))
  have hr := hremaining s T F hs hT h0 zX S a b w M A P hS hS0 ha hb hab hJI hM hA hP hL hw hwP hsource HX HZ
  have hf := hfar s T F hs hT hTT h0 zX S (directionSelection T) a b w M A P hS hS0 ha hb hJI hM hA
    (zero_lt_one.trans_le hP) hL hw1 hwP hW HX HZ
  have hl := hlow s T F hs hT h0 zX S (directionSelection T) a b w P hS hS0 ha hb hJI hw hwP hPw
    (zero_lt_one.trans_le hP) hL hsource hW
  have hsour := (F.unselected_source_label_physical_sum hs hT hw zX measurableSet_Icc hJ hq hW hP hL hsource).trans
    (add_le_add (add_le_add (mul_le_mul' le_rfl hr) hf) hl)
  have hu := (F.unselected_force_label_integral_split hs zX (directionSelection T)
    (F.prefixAngular_regular hs hT hw zX).1.measurable measurableSet_Icc).trans (add_le_add ht hsour)
  apply hu.trans_eq
  rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤64),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤64)]
  simp only [mul_assoc,add_assoc]

lemma Admissible.supported_boundary_force_uniform_bound {d : Datum} (hd : Admissible d)
    (T₀ : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (T : ℝ), 0≤T → T≤T₀ → ∀ (E B : Field) (F : PhaseFlowOn E B T) (zX : Phase),
      zX∈tsupport d.f₀ → ∀t∈Ioc (0:ℝ) T,
      ‖boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1
        (velocity (F.flow zX t).2)‖ ≤ C := by
  obtain ⟨R,hR⟩ := hd.2.1.bddAbove_image
    (show ContinuousOn (fun z : Phase=>‖z.1‖) (tsupport d.f₀) from continuous_fst.norm.continuousOn)
  obtain ⟨C,hC,hb⟩ := boundaryLorentzForce_datum_bound hd T₀ (R+T₀)
  refine ⟨C,hC,?_⟩
  intro T hT hTT E B F zX hz t ht
  have hx0 : ‖zX.1‖ ≤ R := hR ⟨zX,hz,rfl⟩
  have hh := (F.position_lipschitz zX).dist_le_mul t ⟨ht.1.le,ht.2⟩ 0 ⟨le_rfl,hT⟩
  simp only [F.initial,NNReal.coe_one,one_mul,Real.dist_eq,sub_zero,abs_of_nonneg ht.1.le] at hh
  apply hb t ⟨ht.1,ht.2.trans hTT⟩ (F.flow zX t).1 _ _ (norm_velocity_lt_one _).le
  rw [mem_closedBall,dist_zero_right]
  calc
    ‖(F.flow zX t).1‖=‖((F.flow zX t).1-zX.1)+zX.1‖ := by rw [sub_add_cancel]
    _ ≤ ‖(F.flow zX t).1-zX.1‖+‖zX.1‖ := norm_add_le _ _
    _ ≤ t+R := add_le_add (by simpa only [dist_eq_norm] using hh) hx0
    _ ≤ R+T₀ := by linarith only [ht.2,hTT]

lemma Admissible.direction_family_datum_uniform_bound {d : Datum} (hd : Admissible d)
    (T₀ : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (T : ℝ), 0≤T → T≤T₀ → ∀ (E B : Field) (F : PhaseFlowOn E B T) (zX : Phase),
      zX∈tsupport d.f₀ → ∀(w c e : ℝ),0<w → c ≤ e →
      ∀(ι : Type) (S : Finset ι) (a b ℓ : ι→ℝ),
      (∀i∈S,0<ℓ i) → (∀i∈S,2*ℓ i ≤ b i-a i) →
      (∀i∈S,Icc (a i) (b i)⊆Icc c e) →
      (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) →
      (∀i∈S,∀t∈Icc (a i) (b i),w/16 ≤ ‖(F.flow zX t).2‖) →
      (∑i∈S,‖∫t in Ioo (0:ℝ) T,directionWeight (a i) (b i) (ℓ i) t •
        angularMultiplierCLM w (F.flow zX t).2
          (boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1
            (velocity (F.flow zX t).2))‖) ≤ C*(e-c) := by
  obtain ⟨C,hC,hbound⟩ := hd.supported_boundary_force_uniform_bound T₀
  refine ⟨64*C,by positivity,?_⟩
  intro T hT hTT E B F zX hz w c e hw hce ι S a b ℓ hℓ hlen hcell hdis hband
  have hbnd (i : ι) (hi : i∈S) :
      ‖∫t in Ioo (0:ℝ) T,directionWeight (a i) (b i) (ℓ i) t •
        angularMultiplierCLM w (F.flow zX t).2
          (boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1
            (velocity (F.flow zX t).2))‖ ≤
      64*C*(∫t in Ioo (0:ℝ) T,|directionWeight (a i) (b i) (ℓ i) t|) := by
    rw [←integral_const_mul]
    apply norm_integral_le_of_norm_le ((directionWeight_integrable (hℓ i hi) (hlen i hi)).norm.const_mul _).integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    by_cases hψ : directionWeight (a i) (b i) (ℓ i) t=0
    · simp only [hψ,zero_smul,norm_zero,mul_zero,le_refl]
    · have htc := (directionWeight_ne_zero_interior (hℓ i hi) (hlen i hi) hψ)
      have hG := angularMultiplierCLM_norm_le hw
        (show w/64 ≤ ‖(F.flow zX t).2‖ by linarith only [hw,hband i hi t (Ioo_subset_Icc_self htc)])
      have hB := hbound T hT hTT E B F zX hz t ⟨ht.1,ht.2.le⟩
      rw [norm_smul,Real.norm_eq_abs]
      calc
        _ ≤ |directionWeight (a i) (b i) (ℓ i) t| * (64*C) :=
          mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul hG hB (norm_nonneg _) (by norm_num))) (abs_nonneg _)
        _ = _ := by ring
  calc
    _ ≤ ∑i∈S,64*C*(∫t in Ioo (0:ℝ) T,|directionWeight (a i) (b i) (ℓ i) t|) := Finset.sum_le_sum hbnd
    _ = 64*C*(∑i∈S,∫t in Ioo (0:ℝ) T,|directionWeight (a i) (b i) (ℓ i) t|) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (directionWeight_family_mass S a b ℓ hℓ hlen hdis hce hcell) (by positivity)

lemma Admissible.direction_lorentz_uniform_log_bound {d : Datum} (hd₀ : Admissible d)
    (T₀ : ℝ) :
    ∃ Cb Ct Cs : ℝ,0≤Cb ∧ 0≤Ct ∧ 0≤Cs ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T), 0≤T → T≤T₀ → SmoothClassicalPrefix d s T →
    ∀ (zX : Phase) (S : Set Phase) (a b w M A P : ℝ),
      zX∈tsupport d.f₀ → IsCompact S → tsupport d.f₀⊆S →
      0≤a → b≤T → a≤b → b-a≤(w/P)^2 →
      0<M → 0≤A → 1≤P → 1≤Real.log (2+P) → 1≤w → w≤P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∫⁻t in Icc a b,ENNReal.ofReal ‖s.E (t,(F.flow zX t).1)+
          cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))‖) ≤
      ENNReal.ofReal (Cb*(b-a)) + ENNReal.ofReal (4*Real.pi)⁻¹ *
       (ENNReal.ofReal (Ct*(1+E)*(1+16384*(M+Real.sqrt A))*max 1 T*w*(Real.log (2+P))^5) +
        ENNReal.ofReal (Cs*(1+E)*(1+M+Real.sqrt A)*w*Real.sqrt w*(Real.log (2+P))^5)) := by
  obtain ⟨Cb,hCb,hdatum⟩ := hd₀.supported_boundary_force_uniform_bound T₀
  obtain ⟨Ct,hCt,htrans⟩ := hd₀.direct_transport_sharp_physical_log_bound
  obtain ⟨Cs,hCs,hsource⟩ := hd₀.direct_source_physical_log_bound
  refine ⟨Cb,Ct,Cs,hCb,hCt,hCs,?_⟩
  intro s T F hT hTT hs zX S a b w M A P hzX hS hS0 ha hb hab hJI hM hA hP hL hw hwP hPbound hW HX HZ
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  have hcon := (F.continuous_prefixFlow hs.directionCountsEnergyPrefix hT).comp
    (continuous_id.prodMk continuous_const : Continuous (fun t : ℝ=>(t,zX)))
  have hX : Measurable X := hcon.fst.measurable
  have hV : Measurable V := hcon.snd.measurable
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hdata : (fun z=>s.f (0,z))=d.f₀ := funext hs.initial_f
  have hS0' : tsupport (fun z=>s.f (0,z))⊆S := by rw [hdata]; exact hS0
  have hDb : ∀t∈Ioo 0 T∩Icc a b,
      ‖boundaryLorentzForce (datumBoundarySolution d) t (X t) (velocity (V t))‖≤Cb := by
    intro t ht
    dsimp only [X,V,prefixFlow]
    rw [prefixClamp_eq (hJ ht.2)]
    exact hdatum T hT hTT s.E s.B F zX hzX t ⟨ht.1.1,ht.1.2.le⟩
  have hraw : (∫⁻t in Icc a b,ENNReal.ofReal ‖s.E (t,(F.flow zX t).1)+
      cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))‖)=
      ∫⁻t in Icc a b,ENNReal.ofReal ‖s.E (t,X t)+cross (velocity (V t)) (s.B (t,X t))‖ := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp only [X,V,prefixFlow,prefixClamp_eq (hJ ht)]
  rw [hraw]
  apply (hs.direct_lorentz_triangle_bound hT X V hX hV measurableSet_Icc hJ Cb hCb hDb).trans
  have hD : ENNReal.ofReal Cb*volume (Icc a b)=ENNReal.ofReal (Cb*(b-a)) := by
    rw [Real.volume_Icc,ENNReal.ofReal_mul hCb]
  rw [hD]
  apply add_le_add le_rfl
  apply mul_le_mul' le_rfl
  exact add_le_add
    (htrans s T F hs.directionCountsEnergyPrefix hT hs.initial_f zX S a b w M A P hS hS0' ha hb hJI hM hA hw hP hwP hL hPbound hW HX HZ)
    (hsource s T F hs.directionCountsEnergyPrefix hT hs.initial_f zX S a b w M A P hS hS0' ha hb hab hJI hM hA hP hL hw hwP
      hPbound hW HX HZ)

def directionUnionBudget (E T w M A P Ct Cr Cf Cl Cg : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Ct*(1+E)*(1+16384*(M+Real.sqrt A))*max 1 T*w*(Real.log (2+P))^5)+
  ENNReal.ofReal (Cr*(1+E)*(1+M+Real.sqrt A)*w*(Real.log (2+P))^5)+
  ENNReal.ofReal (Cf*E*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^5)+
  ENNReal.ofReal (Cl*(1+E)*(max 1 T)^2*(Real.log (2+P))^2)+
  ENNReal.ofReal (Cg*max 1 T*(1+E)*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^3)

lemma Admissible.direction_physical_family_log_bound {d : Datum} (hd₀ : Admissible d)
    (T₀ : ℝ) :
    ∃Ct Cr Cf Cl Cg Ci Ck Cw : ℝ,
      0≤Ct ∧ 0≤Cr ∧ 0≤Cf ∧ 0≤Cl ∧ 0≤Cg ∧ 0≤Ci ∧ 0≤Ck ∧ 0≤Cw ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (S : Set Phase) (a b w M A P : ℝ) (_ : 0<w),
      IsCompact S → tsupport d.f₀⊆S →
      0≤a → b≤T → a≤b → b-a≤(w/P)^2 →
      0<M → 0≤A → 1≤P → 1≤Real.log (2+P) → 1≤w → w≤P → P≤w^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀(ι : Type) (D : Finset ι) (c e ℓ : ι→ℝ),
      (∀i∈D,0<ℓ i) → (∀i∈D,2*ℓ i≤e i-c i) →
      (∀i∈D,Icc (c i) (e i)⊆Icc a b) →
      (D:Set ι).Pairwise (fun i j=>Disjoint (Ioo (c i) (e i)) (Ioo (c j) (e j))) →
      let G := fun t=>angularMultiplierCLM w (F.flow zX t).2
      (∑i∈D,ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,directionWeight (c i) (e i) (ℓ i) t • G t
        (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
          boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2))‖)≤
      ENNReal.ofReal (4*Real.pi)⁻¹ *
       (directionUnionBudget (∫x : Vec,totalEnergy s (0,x)) T w M A P Ct Cr Cf Cl Cg+
        ENNReal.ofReal (Ci*T*(b-a))+
        (D.card:ℝ≥0∞)*ENNReal.ofReal (2*Cw*Real.sqrt (max 1 T)*(Real.log (2+P))^2)+
        (∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)*
          ENNReal.ofReal (Ck*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w)) := by
  classical
  obtain ⟨Ct,Cr,Cf,Cl,hCt,hCr,hCf,hCl,hun⟩ := hd₀.direction_unselected_label_log_bound T₀
  obtain ⟨Ce,Cf',Cl',Cg,Ck,hCe,hCf',hCl',hCg,hCk,hbulk⟩ := hd₀.direction_selected_bulk_log_bound T₀
  obtain ⟨Ci,hCi,hinit⟩ := hd₀.direction_family_initial_bound
  obtain ⟨Cm,hCm,hmove⟩ := hd₀.direction_family_moving_log_bound
  obtain ⟨Cw,hCw,hweight⟩ := hd₀.direction_family_weight_log_bound
  refine ⟨Ct,Cr+Ce,Cf+Cf',Cl+Cl',Cg,Ci,Ck+Cm,Cw,hCt,by positivity,by positivity,by positivity,hCg,hCi,by positivity,hCw,?_⟩
  intro s T F hs hT hTT zX S a b w M A P hw hS hS0 ha hb hab hJI hM hA hP hL hw1 hwP hPw hsource hq hV HX HZ ι D c e ℓ hℓ hlen hcell hdis
  dsimp only
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hdata : (fun z=>s.f (0,z))=d.f₀ := funext hs.initial_f
  have hS0' : tsupport (fun z=>s.f (0,z))⊆S := by rw [hdata]; exact hS0
  have hQ (k) (hk : k∈directionSelection T) :
      cappedRepresentative (k 1)≤cappedRepresentative (k 2) ∧
        sourceRepresentative (k 0)*cappedRepresentative (k 1)*Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1 := by
    refine ⟨hk.1.trans ?_,hk.2⟩
    have hp := (cappedRepresentative_pos (k 2)).le
    linarith
  have hu := hun s T F hs.directionCountsEnergyPrefix hT hTT hs.initial_f zX S a b w M A P hw hS hS0' ha hb hab hJI
    hM hA hP hL hw1 hwP hPw hsource hq hV HX HZ
  have hbu := hbulk s T F hs.directionCountsEnergyPrefix hT hTT hs.initial_f zX S a b w M A P hw hS hS0' ha hb hab hJI
    hM hA hP hL hw1 hwP hPw hsource hq hV HX HZ
  have hm := hmove s T F hs.directionCountsEnergyPrefix hT hs.initial_f zX (Icc a b) w P (directionSelection T)
    (zero_lt_one.trans_le hP) hL hsource hQ measurableSet_Icc hJ hw hq hV ι D c e ℓ hℓ hlen hcell hdis
  have hwc := hweight s T F hs.directionCountsEnergyPrefix hT hs.initial_f zX (Icc a b) w P (directionSelection T)
    (zero_lt_one.trans_le hP) hL hsource hQ measurableSet_Icc hJ hw hq hV ι D c e ℓ hℓ hlen hcell
  have hic := hinit s T F hs.directionCountsEnergyPrefix hT hs.initial_f zX w a b hw hab ι D c e ℓ (fun _=>directionSelection T)
    hℓ hlen hcell (fun i hi=>(hcell i hi).trans hJ) hdis (fun i hi t ht=>hV t (hcell i hi ht))
  have hi : (∑i∈D,ENNReal.ofReal ‖∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z))
      (directionSelection T) (directionWeight (c i) (e i) (ℓ i)) (fun t=>angularMultiplierCLM w (F.flow zX t).2) z‖)≤
      ENNReal.ofReal (Ci*T*(b-a)) := by
    rw [←ENNReal.ofReal_sum_of_nonneg (fun i _=>norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hic
  have hforce : (∫⁻t in Icc a b,ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖)=
      ∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖ := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp only [prefixMomentumForce,prefixFlow,prefixClamp_eq (hJ ht)]
  rw [hforce] at hm
  let G := fun t=>angularMultiplierCLM w (F.flow zX t).2
  let W := prefixAngularMultiplier s F.flow T w hw zX
  have heq (t : ℝ) (ht : t∈Icc a b) : W t=G t :=
    (prefixAngular_highband hw zX (hJ ht) (hV t ht)).1
  have huEq (p : ℝ×Phase) :
      {p : ℝ×Phase | labelReceiverTime F.flow zX T p∈Icc a b}.indicator
        (fun p=>ENNReal.ofReal ‖G (labelReceiverTime F.flow zX T p)
          ((1-labelSelectedCutoff F.flow zX T (directionSelection T) p) • actualLabelSignedForce s F.flow zX T p)‖) p=
      ENNReal.ofReal ‖(Icc a b).indicator W (labelReceiverTime F.flow zX T p)
        ((1-labelSelectedCutoff F.flow zX T (directionSelection T) p) • actualLabelSignedForce s F.flow zX T p)‖ := by
    by_cases ht : labelReceiverTime F.flow zX T p∈Icc a b
    · simp only [indicator_of_mem ht,indicator_of_mem (show p∈{p : ℝ×Phase | labelReceiverTime F.flow zX T p∈Icc a b} from ht),heq _ ht]
    · simp only [indicator_of_notMem ht,indicator_of_notMem (show p∉{p : ℝ×Phase | labelReceiverTime F.flow zX T p∈Icc a b} from ht),zero_apply,norm_zero,ENNReal.ofReal_zero]
  have hbEq (p : ℝ×Phase) :
      {p : ℝ×Phase | labelReceiverTime F.flow zX T p∈Icc a b}.indicator
        (selectedMultiplierBulkDensity s F.flow zX T (directionSelection T) G) p=
      selectedMultiplierBulkDensity s F.flow zX T (directionSelection T) ((Icc a b).indicator W) p := by
    by_cases ht : labelReceiverTime F.flow zX T p∈Icc a b
    · simp only [indicator_of_mem (show p∈{p : ℝ×Phase | labelReceiverTime F.flow zX T p∈Icc a b} from ht),selectedMultiplierBulkDensity,indicator_of_mem ht,heq _ ht]
    · simp only [indicator_of_notMem (show p∉{p : ℝ×Phase | labelReceiverTime F.flow zX T p∈Icc a b} from ht),selectedMultiplierBulkDensity,indicator_of_notMem ht,zero_apply,norm_zero,ENNReal.ofReal_zero,add_zero]
  have hf := hs.actual_angular_family_bound hT hw F zX (directionSelection T) D c e ℓ hℓ hlen hdis
    (Icc a b) hJ hcell hV
  dsimp only at hf
  change _≤ENNReal.ofReal (4*Real.pi)⁻¹*(_+_+_+_+_) at hf
  rw [lintegral_congr huEq,lintegral_congr hbEq] at hf
  apply hf.trans
  apply mul_le_mul' le_rfl
  apply (add_le_add (add_le_add (add_le_add (add_le_add hu hi) hwc) hbu) hm).trans_eq
  have hE : 0≤ ∫x : Vec,totalEnergy s (0,x) := integral_nonneg (hs.directionCountsEnergyPrefix.total_energy_nonneg ⟨le_rfl,hT⟩)
  dsimp only [directionUnionBudget]
  rw [show (Cr+Ce)*(1+(∫x : Vec,totalEnergy s (0,x)))*(1+M+Real.sqrt A)*w*(Real.log (2+P))^5=
      Cr*(1+(∫x : Vec,totalEnergy s (0,x)))*(1+M+Real.sqrt A)*w*(Real.log (2+P))^5+
      Ce*(1+(∫x : Vec,totalEnergy s (0,x)))*(1+M+Real.sqrt A)*w*(Real.log (2+P))^5 by ring,
    show (Cf+Cf')*(∫x : Vec,totalEnergy s (0,x))*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^5=
      Cf*(∫x : Vec,totalEnergy s (0,x))*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^5+
      Cf'*(∫x : Vec,totalEnergy s (0,x))*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^5 by ring,
    show (Cl+Cl')*(1+(∫x : Vec,totalEnergy s (0,x)))*(max 1 T)^2*(Real.log (2+P))^2=
      Cl*(1+(∫x : Vec,totalEnergy s (0,x)))*(max 1 T)^2*(Real.log (2+P))^2+
      Cl'*(1+(∫x : Vec,totalEnergy s (0,x)))*(max 1 T)^2*(Real.log (2+P))^2 by ring,
    show (Ck+Cm)*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w=
      Ck*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w+Cm*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w by ring]
  rw [ENNReal.ofReal_add (by positivity) (by positivity),ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),ENNReal.ofReal_add (by positivity) (by positivity),mul_add]
  simp only [mul_add]
  ac_rfl



section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff NNReal


structure WeightedDirectionPartition (V K : ℝ → Vec) (a b w δ : ℝ) where
  count : ℕ
  time : ℕ → ℝ
  ramp : ℕ → ℝ
  initial : time 0 = a
  terminal : time count = b
  time_mem : ∀ i ≤ count, time i ∈ Icc a b
  strict : StrictMonoOn time (Iic count)
  direction_control : ∀ i < count, ∀ t ∈ Icc (time i) (time (i+1)),
    ‖momentumDirection (V t) - momentumDirection (V (time i))‖ ≤ δ
  exit : ∀ i < count-1,
    ‖momentumDirection (V (time (i+1))) - momentumDirection (V (time i))‖ = δ
  ramp_pos : ∀ i < count-1, 0 < ramp i
  ramp_separation : ∀ i < count-1, 2*ramp i ≤ time (i+1)-time i
  signed_exit : ∀ i < count-1,
    w*δ/2 ≤ ‖∫ t in time i..time (i+1),
      directionWeight (time i) (time (i+1)) (ramp i) t • angularMultiplier w (V t) (K t)‖
  variation : ∀ i < count-1,
    (∫ t in time i..time (i+1), |deriv (directionWeight (time i) (time (i+1)) (ramp i)) t|) = 2

lemma IncrementBootstrap.weighted_direction_partition {V K : ℝ → Vec}
    {T M A P L a b δ : ℝ} (H : IncrementBootstrap V T M A P L)
    (k : ℕ) (hk : 16 ≤ (2:ℝ)^k) (hab : a ≤ b)
    (hJ : Icc a b ⊆ Icc 0 T) (hV : ContinuousOn V (Icc a b))
    (hK : ContinuousOn K (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt V (K t) t)
    (hband : ∀ t ∈ Icc a b, (2:ℝ)^k/8 ≤ q (V t) ∧ q (V t) ≤ 8*(2:ℝ)^k)
    (hM : 0 < M) (hA : 0 < A) (hP : 0 < P) (hL : 0 < L) (hδ : 0 < δ) :
    Nonempty (WeightedDirectionPartition V K a b ((2:ℝ)^k) δ) := by
  classical
  obtain ⟨n,t,ht0,htn,htmem,hstep⟩ :=
    H.finite_direction_stops k hk hab hV hJ hband hM hA hP hL hδ
  have hcell (i : ℕ) (hi : i < n) : Icc (t i) (t (i+1)) ⊆ Icc a b :=
    Icc_subset_Icc (htmem i (by omega)).1 (htmem (i+1) (by omega)).2
  have hwit (i : ℕ) (hi : i < n-1) :
      ∃ ℓ : ℝ, 0 < ℓ ∧ 2*ℓ ≤ t (i+1)-t i ∧
        ((2:ℝ)^k*δ/2 ≤ ‖∫ u in t i..t (i+1),
          directionWeight (t i) (t (i+1)) ℓ u • angularMultiplier ((2:ℝ)^k) (V u) (K u)‖) ∧
        (∫ u in t i..t (i+1), |deriv (directionWeight (t i) (t (i+1)) ℓ) u|)=2 ∧
        tsupport (directionWeight (t i) (t (i+1)) ℓ) ⊆ Icc (t i) (t (i+1)) := by
    have hin : i < n := by omega
    apply H.exists_weighted_angular_exit k hk ((hcell i hin).trans hJ) (hstep i hin).1.le
      (hV.mono (hcell i hin)) (hK.mono (hcell i hin))
    · intro u hu
      exact hd u ⟨(htmem i (by omega)).1.trans_lt hu.1,
        hu.2.trans_le (htmem (i+1) (by omega)).2⟩
    · exact fun u hu => hband u (hcell i hin hu)
    · exact hM
    · exact hA
    · exact hP
    · exact hL
    · exact hδ
    · exact ((hstep i hin).2.2 (by omega)).1.ge
  let ℓ : ℕ → ℝ := fun i => if hi : i < n-1 then (hwit i hi).choose else 1
  have hℓ (i : ℕ) (hi : i < n-1) : ℓ i = (hwit i hi).choose := dite_eq_left hi
  refine ⟨{
    count := n, time := t, ramp := ℓ, initial := ht0, terminal := htn,
    time_mem := htmem,
    strict := strictMonoOn_Iic_of_lt_succ (fun i hi => (hstep i hi).1),
    direction_control := fun i hi => (hstep i hi).2.1,
    exit := fun i hi => ((hstep i (by omega)).2.2 (by omega)).1,
    ramp_pos := ?_, ramp_separation := ?_, signed_exit := ?_, variation := ?_ }⟩
  · intro i hi
    rw [hℓ i hi]
    exact (hwit i hi).choose_spec.1
  · intro i hi
    rw [hℓ i hi]
    exact (hwit i hi).choose_spec.2.1
  · intro i hi
    rw [hℓ i hi]
    exact (hwit i hi).choose_spec.2.2.1
  · intro i hi
    rw [hℓ i hi]
    exact (hwit i hi).choose_spec.2.2.2.1

namespace WeightedDirectionPartition
variable {V K : ℝ → Vec} {a b w δ : ℝ}

lemma cell_subset (D : WeightedDirectionPartition V K a b w δ)
    {i : ℕ} (hi : i < D.count) : Icc (D.time i) (D.time (i+1)) ⊆ Icc a b :=
  Icc_subset_Icc (D.time_mem i (by omega)).1 (D.time_mem (i+1) (by omega)).2

lemma interiors_disjoint (D : WeightedDirectionPartition V K a b w δ) :
    (Finset.range (D.count-1) : Set ℕ).Pairwise
      (fun i j => Disjoint (Ioo (D.time i) (D.time (i+1)))
        (Ioo (D.time j) (D.time (j+1)))) := by
  intro i hi j hj hne
  have hi' : i < D.count-1 := Finset.mem_range.mp hi
  have hj' : j < D.count-1 := Finset.mem_range.mp hj
  apply Ioo_disjoint_Ioo.mpr
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact (min_le_left _ _).trans ((D.strict.monotoneOn (by simp only [mem_Iic]; omega)
      (by simp only [mem_Iic]; omega) (by omega)).trans (le_max_right _ _))
  · exact (min_le_right _ _).trans ((D.strict.monotoneOn (by simp only [mem_Iic]; omega)
      (by simp only [mem_Iic]; omega) (by omega)).trans (le_max_left _ _))

lemma weight_sum (D : WeightedDirectionPartition V K a b w δ) (t : ℝ) :
    (∑ i ∈ Finset.range (D.count-1),
      |directionWeight (D.time i) (D.time (i+1)) (D.ramp i) t|) ≤ 1 := by
  have hnonneg (i : ℕ) (hi : i ∈ Finset.range (D.count-1)) :
      0 ≤ directionWeight (D.time i) (D.time (i+1)) (D.ramp i) t :=
    (directionWeight_bounds (D.ramp_pos i (Finset.mem_range.mp hi))
      (D.ramp_separation i (Finset.mem_range.mp hi))).1
  simp_rw [Finset.sum_congr rfl (fun i hi => abs_of_nonneg (hnonneg i hi))]
  exact directionWeight_sum_le_one (Finset.range (D.count-1)) D.time
    (fun i => D.time (i+1)) D.ramp
    (fun i hi => D.ramp_pos i (Finset.mem_range.mp hi))
    (fun i hi => D.ramp_separation i (Finset.mem_range.mp hi)) D.interiors_disjoint t

lemma complete_force_lower (D : WeightedDirectionPartition V K a b w δ) :
    (D.count-1 : ℕ)*w*δ/2 ≤ ∑ i ∈ Finset.range (D.count-1),
      ‖∫ t in D.time i..D.time (i+1),
        directionWeight (D.time i) (D.time (i+1)) (D.ramp i) t •
          angularMultiplier w (V t) (K t)‖ := by
  calc
    _ = ∑ i ∈ Finset.range (D.count-1), w*δ/2 := by simp; ring
    _ ≤ _ := Finset.sum_le_sum (fun i hi => D.signed_exit i (Finset.mem_range.mp hi))

lemma total_variation (D : WeightedDirectionPartition V K a b w δ) :
    (∑ i ∈ Finset.range (D.count-1), ∫ t in D.time i..D.time (i+1),
      |deriv (directionWeight (D.time i) (D.time (i+1)) (D.ramp i)) t|) =
        2*(D.count-1 : ℕ) := by
  rw [Finset.sum_congr rfl (fun i hi => D.variation i (Finset.mem_range.mp hi))]
  simp [mul_comm]

end WeightedDirectionPartition

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


private lemma vec_integrable_smul {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X→Vec} (h : Integrable f μ) (c : ℝ) :
    Integrable (fun x=>c • f x) μ := by
  exact ⟨h.1.const_smul c,HasFiniteIntegral.smul c h.2⟩

lemma SmoothClassicalPrefix.multiplier_retarded_force_integrable {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hT : 0≤T)
    (F : PhaseFlowOn s.E s.B T) (zX : Phase)
    {W : ℝ→Vec→L[ℝ]Vec} (hW : ContinuousOn W (Icc 0 T)) :
    IntegrableOn (fun t=>W t
      (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
        boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2)))
      (Ioo (0:ℝ) T) := by
  classical
  let A := sourceForceConeKernel s F.flow zX
  have hA : ContinuousOn A (coneKernelDomain T) :=
    F.normalised_source_force_continuousOn hs.directionCountsEnergyPrefix zX
  let B : ConeKernelState→Vec := fun q=>W q.1.1 (A q)
  have hB : ContinuousOn B (coneKernelDomain T) :=
    (hW.comp continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1)).clm_apply hA
  have hg := F.triangleConeKernel_integrable hs.directionCountsEnergyPrefix hT zX hA
  have hb := F.triangleConeKernel_integrable hs.directionCountsEnergyPrefix hT zX hB
  have hi : Integrable (fun z : ConeCoordinate=>∫v : Vec,triangleConeKernel s F.flow zX T A (z,v))
      (volume.prod (volume.prod sphereMeasure)) := hg.integral_prod_left
  have hib : Integrable (fun t : ℝ=>(4*Real.pi)⁻¹ •
      ∫p : ℝ×Sphere,∫v : Vec,triangleConeKernel s F.flow zX T B ((t,p),v)
        ∂volume ∂volume.prod sphereMeasure) := by
    exact vec_integrable_smul hb.integral_prod_left.integral_prod_left _
  apply (integrable_indicator_iff measurableSet_Ioo).mp
  apply hib.congr
  have hvi := Measure.ae_ae_of_ae_prod hg.prod_right_ae
  filter_upwards [hi.prod_right_ae,hvi] with t ht hvt
  have he : (∫p : ℝ×Sphere,∫v : Vec,triangleConeKernel s F.flow zX T B ((t,p),v)
        ∂volume ∂volume.prod sphereMeasure)=
      W t (∫p : ℝ×Sphere,∫v : Vec,triangleConeKernel s F.flow zX T A ((t,p),v)
        ∂volume ∂volume.prod sphereMeasure) := by
    rw [←(W t).integral_comp_comm ht]
    apply integral_congr_ae
    filter_upwards [hvt] with p hp
    rw [←(W t).integral_comp_comm hp]
    apply integral_congr_ae
    exact ae_of_all _ (fun v=>triangleConeKernel_receiver_multiplier s F.flow zX T A W ((t,p),v))
  rw [he]
  by_cases htT : t∈Ioo 0 T
  · rw [indicator_of_mem htT,F.triangleConeKernel_fiber_sphere zX A htT ht,
      hs.retarded_force_source_polar htT.1 htT.2 _ _ (norm_velocity_lt_one _),add_sub_cancel_left,map_smul]
    rfl
  · rw [indicator_of_notMem htT]
    have hz : ∀p : ℝ×Sphere,∀v : Vec,triangleConeKernel s F.flow zX T A ((t,p),v)=0 := by
      intro p v
      have hp : ((t,p),v)∉trianglePhaseDomain T := fun hp=>htT hp.1
      simp only [triangleConeKernel,indicator_of_notMem hp]
    simp only [hz,integral_zero,map_zero,smul_zero]

lemma SmoothClassicalPrefix.direction_weighted_force_integrable {d : Datum} {s : Solution} {T w : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hT : 0≤T) (hw : 0<w)
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) {a b ℓ : ℝ}
    (hℓ : 0<ℓ) (hlen : 2*ℓ≤b-a) (hcell : Icc a b⊆Icc 0 T)
    (hband : ∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) :
    IntegrableOn (fun t=>directionWeight a b ℓ t • angularMultiplierCLM w (F.flow zX t).2
      (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1)))) (Ioo (0:ℝ) T) ∧
    IntegrableOn (fun t=>directionWeight a b ℓ t • angularMultiplierCLM w (F.flow zX t).2
      (boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2))) (Ioo (0:ℝ) T) := by
  let W := fun t=>directionWeight a b ℓ t • prefixAngularMultiplier s F.flow T w hw zX t
  have hW : Continuous W := (directionWeight_lipschitz a b ℓ).continuous.smul
    (F.prefixAngular_regular hs.directionCountsEnergyPrefix hT hw zX).1
  have he (t : ℝ) (K : Vec) :
      W t K=directionWeight a b ℓ t • angularMultiplierCLM w (F.flow zX t).2 K := by
    by_cases ht : t∈tsupport (directionWeight a b ℓ)
    · have hc := directionWeight_tsupport hℓ hlen ht
      simp only [W,smul_apply,(prefixAngular_highband hw zX (hcell hc) (hband t hc)).1]
    · simp only [W,smul_apply,image_eq_zero_of_notMem_tsupport ht,zero_smul]
  have hi : IntegrableOn (fun t=>W t (prefixMomentumForce s F.flow T zX t)) (Ioo (0:ℝ) T) :=
    ((hW.clm_apply (F.continuous_prefixMomentumForce hs.directionCountsEnergyPrefix hT zX)).continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hiK : IntegrableOn (fun t=>directionWeight a b ℓ t • angularMultiplierCLM w (F.flow zX t).2
      (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1)))) (Ioo (0:ℝ) T) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [he,prefixMomentumForce,prefixFlow,prefixClamp_eq (Ioo_subset_Icc_self ht),lorentzField,lorentzPhase]
  have hiD := hs.multiplier_retarded_force_integrable hT F zX hW.continuousOn
  have hiD' : IntegrableOn (fun t=>directionWeight a b ℓ t • angularMultiplierCLM w (F.flow zX t).2
      (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
        boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2))) (Ioo (0:ℝ) T) := by
    simpa only [he] using hiD
  refine ⟨hiK,?_⟩
  apply (hiK.sub hiD').congr
  exact ae_of_all _ (fun t=>by simp only [Pi.sub_apply,map_sub,smul_sub,sub_sub_cancel])

lemma directionWeight_interval_eq_global {a b ℓ T : ℝ} (hℓ : 0<ℓ)
    (hlen : 2*ℓ≤b-a) (hcell : Icc a b⊆Icc 0 T) (H : ℝ→Vec) :
    (∫t in a..b,directionWeight a b ℓ t • H t)=
      ∫t in Ioo (0:ℝ) T,directionWeight a b ℓ t • H t := by
  have hab : a≤b := by linarith
  rw [intervalIntegral.integral_of_le hab,integral_Ioc_eq_integral_Ioo]
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
  · intro t ht
    exact ⟨(hcell ⟨le_rfl,hab⟩).1.trans_lt ht.1,ht.2.trans_le (hcell ⟨hab,le_rfl⟩).2⟩
  · intro t ht
    have hz : directionWeight a b ℓ t=0 := by
      by_contra hn
      exact ht.2 (directionWeight_ne_zero_interior hℓ hlen hn)
    rw [hz,zero_smul]

lemma SmoothClassicalPrefix.direction_force_family_triangle {d : Datum} {s : Solution} {T w : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hT : 0≤T) (hw : 0<w)
    (F : PhaseFlowOn s.E s.B T) (zX : Phase)
    {ι : Type*} (D : Finset ι) (a b ℓ : ι→ℝ)
    (hℓ : ∀i∈D,0<ℓ i) (hlen : ∀i∈D,2*ℓ i≤b i-a i)
    (hcell : ∀i∈D,Icc (a i) (b i)⊆Icc 0 T)
    (hband : ∀i∈D,∀t∈Icc (a i) (b i),w/16≤‖(F.flow zX t).2‖) :
    let G := fun t=>angularMultiplierCLM w (F.flow zX t).2
    let K := fun t=>s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))
    let B := fun t=>boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2)
    (∑i∈D,ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,directionWeight (a i) (b i) (ℓ i) t • G t (K t)‖)≤
      (∑i∈D,ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,directionWeight (a i) (b i) (ℓ i) t • G t (K t-B t)‖)+
      (∑i∈D,ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,directionWeight (a i) (b i) (ℓ i) t • G t (B t)‖) := by
  classical
  dsimp only
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  obtain ⟨hiK,hiB⟩ := hs.direction_weighted_force_integrable hT hw F zX (hℓ i hi) (hlen i hi) (hcell i hi) (hband i hi)
  simp only [map_sub,smul_sub]
  rw [integral_sub hiK hiB,←ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_le_norm_sub_add _ _)

lemma Admissible.direction_complete_count_cost_bound {d : Datum} (hd₀ : Admissible d)
    (T₀ : ℝ) :
    ∃ Ct Cr Cf Cl Cg Ci Ck Cw Cb : ℝ,
      0≤Ct ∧ 0≤Cr ∧ 0≤Cf ∧ 0≤Cl ∧ 0≤Cg ∧ 0≤Ci ∧ 0≤Ck ∧ 0≤Cw ∧ 0≤Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (S : Set Phase) (a b w M A P δ : ℝ) (_ : 0<w),
      zX∈tsupport d.f₀ → IsCompact S → tsupport d.f₀⊆S →
      0≤a → b≤T → a≤b → b-a≤(w/P)^2 →
      0<M → 0≤A → 1≤P → 1≤Real.log (2+P) → 1≤w → w≤P → P≤w^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ D : WeightedDirectionPartition (fun t=>(F.flow zX t).2)
        (fun t=>s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))) a b w δ,
      ENNReal.ofReal ((D.count-1:ℕ)*w*δ/2)≤
      ENNReal.ofReal (4*Real.pi)⁻¹ *
       (directionUnionBudget (∫x : Vec,totalEnergy s (0,x)) T w M A P Ct Cr Cf Cl Cg+
        ENNReal.ofReal (Ci*T*(b-a))+
        (D.count-1:ℕ)*ENNReal.ofReal (2*Cw*Real.sqrt (max 1 T)*(Real.log (2+P))^2)+
        (∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)*
          ENNReal.ofReal (Ck*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w))+
      ENNReal.ofReal (Cb*(b-a)) := by
  classical
  obtain ⟨Ct,Cr,Cf,Cl,Cg,Ci,Ck,Cw,hCt,hCr,hCf,hCl,hCg,hCi,hCk,hCw,hfam⟩ :=
    hd₀.direction_physical_family_log_bound T₀
  obtain ⟨Cb,hCb,hdatum⟩ := hd₀.direction_family_datum_uniform_bound T₀
  refine ⟨Ct,Cr,Cf,Cl,Cg,Ci,Ck,Cw,Cb,hCt,hCr,hCf,hCl,hCg,hCi,hCk,hCw,hCb,?_⟩
  intro s T F hs hT hTT zX S a b w M A P δ hw hzX hS hS0 ha hb hab hJI hM hA hP hL hw1 hwP hPw hsource hq hV HX HZ D
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  let I := Finset.range (D.count-1)
  have hℓ i (hi : i∈I) := D.ramp_pos i (Finset.mem_range.mp hi)
  have hlen i (hi : i∈I) := D.ramp_separation i (Finset.mem_range.mp hi)
  have hcell i (hi : i∈I) : Icc (D.time i) (D.time (i+1))⊆Icc a b :=
    D.cell_subset (by have := Finset.mem_range.mp hi; omega)
  have hf := hfam s T F hs hT hTT zX S a b w M A P hw hS hS0 ha hb hab hJI hM hA hP hL hw1 hwP hPw
    hsource hq hV HX HZ ℕ I D.time (fun i=>D.time (i+1)) D.ramp hℓ hlen hcell D.interiors_disjoint
  have hd := hdatum T hT hTT s.E s.B F zX hzX w a b hw hab ℕ I D.time (fun i=>D.time (i+1)) D.ramp
    hℓ hlen hcell D.interiors_disjoint (fun i hi t ht=>hV t (hcell i hi ht))
  have htri := hs.direction_force_family_triangle hT hw F zX I D.time (fun i=>D.time (i+1)) D.ramp
    hℓ hlen (fun i hi=>(hcell i hi).trans hJ) (fun i hi t ht=>hV t (hcell i hi ht))
  have hlo := ENNReal.ofReal_le_ofReal D.complete_force_lower
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _=>norm_nonneg _)] at hlo
  have he i (hi : i∈I) := directionWeight_interval_eq_global (hℓ i hi) (hlen i hi) ((hcell i hi).trans hJ)
    (fun t=>angularMultiplier w (F.flow zX t).2
      (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))))
  have hlo' : ENNReal.ofReal ((D.count-1:ℕ)*w*δ/2)≤
      ∑i∈I,ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,directionWeight (D.time i) (D.time (i+1)) (D.ramp i) t •
        angularMultiplierCLM w (F.flow zX t).2
          (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1)))‖ := by
    apply hlo.trans_eq
    apply Finset.sum_congr rfl
    intro i hi
    rw [he i hi]
    simp only [angularMultiplierCLM_apply]
  have hd' := ENNReal.ofReal_le_ofReal hd
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _=>norm_nonneg _)] at hd'
  have hh := hlo'.trans (htri.trans (add_le_add hf hd'))
  simpa only [I,Finset.card_range] using hh

def directionUnionConstant (E H M A Ct Cr Cf Cl Cg : ℝ) : ℝ :=
  Ct*(1+E)*(1+16384*(M+Real.sqrt A))*H+
  Cr*(1+E)*(1+M+Real.sqrt A)+Cf*E*(1+16384*(M+Real.sqrt A))+
  Cl*(1+E)*H^2+Cg*H*(1+E)*(1+16384*(M+Real.sqrt A))

lemma directionUnionConstant_nonneg {E H M A Ct Cr Cf Cl Cg : ℝ}
    (hE : 0≤E) (hH : 0≤H) (hM : 0≤M) (hCt : 0≤Ct) (hCr : 0≤Cr)
    (hCf : 0≤Cf) (hCl : 0≤Cl) (hCg : 0≤Cg) :
    0≤directionUnionConstant E H M A Ct Cr Cf Cl Cg := by
  unfold directionUnionConstant
  positivity

lemma directionUnionBudget_scalar_bound {E T H w M A P Ct Cr Cf Cl Cg : ℝ}
    (hE : 0≤E) (hH : max 1 T≤H) (hM : 0≤M) (hw : 1≤w) (hL : 1≤Real.log (2+P))
    (hCt : 0≤Ct) (hCr : 0≤Cr) (hCf : 0≤Cf) (hCl : 0≤Cl) (hCg : 0≤Cg) :
    directionUnionBudget E T w M A P Ct Cr Cf Cl Cg≤
      ENNReal.ofReal (directionUnionConstant E H M A Ct Cr Cf Cl Cg*w*(Real.log (2+P))^5) := by
  have hh : 0≤H := (by positivity : (0:ℝ)≤ max 1 T).trans hH
  have hw0 := zero_le_one.trans hw
  have hL0 := zero_le_one.trans hL
  have h2 : (Real.log (2+P))^2≤w*(Real.log (2+P))^5 := by
    exact (pow_le_pow_right₀ hL (by omega : 2≤5)).trans (le_mul_of_one_le_left (by positivity) hw)
  have h3 : (Real.log (2+P))^3≤(Real.log (2+P))^5 := pow_le_pow_right₀ hL (by omega)
  have ht : Ct*(1+E)*(1+16384*(M+Real.sqrt A))*max 1 T*w*(Real.log (2+P))^5≤
      Ct*(1+E)*(1+16384*(M+Real.sqrt A))*H*w*(Real.log (2+P))^5 := by gcongr
  have hl : Cl*(1+E)*(max 1 T)^2*(Real.log (2+P))^2≤
      Cl*(1+E)*H^2*w*(Real.log (2+P))^5 := by
    calc
      _≤Cl*(1+E)*H^2*(Real.log (2+P))^2 := by gcongr
      _≤Cl*(1+E)*H^2*(w*(Real.log (2+P))^5) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _=_ := by ring
  have hg : Cg*max 1 T*(1+E)*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^3≤
      Cg*H*(1+E)*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^5 := by gcongr
  unfold directionUnionBudget
  apply (add_le_add (add_le_add (add_le_add (add_le_add (ENNReal.ofReal_le_ofReal ht) le_rfl) le_rfl)
    (ENNReal.ofReal_le_ofReal hl)) (ENNReal.ofReal_le_ofReal hg)).trans_eq
  rw [←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_add (by positivity) (by positivity),
    ←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  unfold directionUnionConstant
  ring

lemma direction_receiver_charge_scalar_bound {F C H w L : ℝ}
    (hF : 0≤F) (hC : 0≤C) (hH : 0≤H) (hw : 0<w) (hL : 0≤L)
    (hLs : L≤Real.sqrt w) :
    ENNReal.ofReal (F*w*Real.sqrt w*L^5)*ENNReal.ofReal (C*Real.sqrt H*L^2/w)≤
      ENNReal.ofReal (F*C*Real.sqrt H*w*L^6) := by
  rw [←ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hs : Real.sqrt w*L≤w := by nlinarith [Real.sq_sqrt hw.le,Real.sqrt_nonneg w]
  calc
    _ = F*C*Real.sqrt H*(Real.sqrt w*L)*L^6 := by field_simp
    _ ≤ F*C*Real.sqrt H*w*L^6 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs
        (mul_nonneg (mul_nonneg hF hC)
          (Real.sqrt_zero.symm.le.trans (Real.sqrt_le_sqrt hH))))
        (pow_nonneg hL 6)

lemma direction_force_budget_scalar_bound {E T H w M A P Cb Ct Cs I : ℝ}
    (hE : 0≤E) (hH : max 1 T≤H) (hM : 0≤M) (hw : 1≤w) (hL : 1≤Real.log (2+P))
    (hCb : 0≤Cb) (hCt : 0≤Ct) (hCs : 0≤Cs) (hI : I≤1) :
    ENNReal.ofReal (Cb*I)+ENNReal.ofReal (4*Real.pi)⁻¹ *
      (ENNReal.ofReal (Ct*(1+E)*(1+16384*(M+Real.sqrt A))*max 1 T*w*(Real.log (2+P))^5)+
       ENNReal.ofReal (Cs*(1+E)*(1+M+Real.sqrt A)*w*Real.sqrt w*(Real.log (2+P))^5))≤
    ENNReal.ofReal ((Cb+(4*Real.pi)⁻¹*(Ct*(1+E)*(1+16384*(M+Real.sqrt A))*H+
      Cs*(1+E)*(1+M+Real.sqrt A)))*w*Real.sqrt w*(Real.log (2+P))^5) := by
  have hh : 0≤H := (by positivity : (0:ℝ)≤ max 1 T).trans hH
  have hw0 := zero_le_one.trans hw
  have hL0 := zero_le_one.trans hL
  have hs : 1≤Real.sqrt w := Real.one_le_sqrt.mpr hw
  have hden : 1≤w*Real.sqrt w*(Real.log (2+P))^5 := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hw hs) (one_le_pow₀ hL)
  have hb : Cb*I≤Cb*w*Real.sqrt w*(Real.log (2+P))^5 := by nlinarith
  have ht : Ct*(1+E)*(1+16384*(M+Real.sqrt A))*max 1 T*w*(Real.log (2+P))^5≤
      Ct*(1+E)*(1+16384*(M+Real.sqrt A))*H*w*Real.sqrt w*(Real.log (2+P))^5 := by
    calc
      _≤Ct*(1+E)*(1+16384*(M+Real.sqrt A))*H*w*(Real.log (2+P))^5 := by gcongr
      _≤Ct*(1+E)*(1+16384*(M+Real.sqrt A))*H*w*(Real.log (2+P))^5*Real.sqrt w :=
        le_mul_of_one_le_right (by positivity) hs
      _=_ := by ring
  apply (add_le_add (ENNReal.ofReal_le_ofReal hb) (mul_le_mul' le_rfl
    (add_le_add (ENNReal.ofReal_le_ofReal ht) le_rfl))).trans_eq
  rw [←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_mul (by positivity),
    ←ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

lemma eventually_direction_absorption (C : ℝ) :
    ∀ᶠ P : ℝ in atTop, 1≤P ∧ 1≤Real.log (2+P) ∧
      ∀ w δ : ℝ, P^(3/5:ℝ)≤w → w^(-3/5:ℝ)≤δ →
        1≤w ∧ 16≤w ∧ P≤w^2 ∧ Real.log (2+P)≤Real.sqrt w ∧
          4*C*(Real.log (2+P))^2≤w*δ := by
  have ht (k : ℕ) (ε : ℝ) (hε : 0<ε) (D : ℝ) :
      ∀ᶠ P : ℝ in atTop, D*(Real.log (2+P))^k≤P^ε := by
    have ho := (isLittleO_log_rpow_rpow_atTop (k:ℝ) hε).const_mul_left (D*2^k)
    filter_upwards [ho.bound (by norm_num : (0:ℝ)<1),eventually_ge_atTop (2:ℝ)] with P hp hP
    have hp0 : 0<P := by linarith
    have hlog : 0≤Real.log P := Real.log_nonneg (by linarith)
    have hlog2nonneg : 0≤Real.log (2+P) := Real.log_nonneg (by linarith)
    have hlog2 : Real.log (2+P)≤2*Real.log P := by
      calc
        _≤Real.log (P^2) := Real.log_le_log (by positivity) (by nlinarith)
        _=_ := by rw [Real.log_pow]; norm_num
    have hbo : |D*2^k| * (Real.log P)^k≤P^ε := by
      simpa only [Real.norm_eq_abs,Real.rpow_natCast,abs_mul,abs_of_nonneg (pow_nonneg hlog _),
        one_mul,abs_of_pos (Real.rpow_pos_of_pos hp0 _)] using hp
    calc
      D*(Real.log (2+P))^k≤|D| * (Real.log (2+P))^k := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _≤|D| * (2*Real.log P)^k := by gcongr
      _=|D*2^k| * (Real.log P)^k := by rw [mul_pow,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤2^k)]; ring
      _≤_ := hbo
  filter_upwards [ht 1 (3/10) (by norm_num) 1,ht 2 (6/25) (by norm_num) (4*C),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/5)).eventually_ge_atTop 16,
    (Real.tendsto_log_atTop.comp (tendsto_const_nhds.add_atTop tendsto_id)).eventually_ge_atTop 1,
    eventually_ge_atTop (1:ℝ)] with P hroot hcharge h16 hL hP
  refine ⟨hP,hL,?_⟩
  intro w δ hw hδ
  have hp0 := zero_lt_one.trans_le hP
  have hw16 := h16.trans hw
  have hw1 : 1≤w := by linarith
  have hw0 := zero_lt_one.trans_le hw1
  have hsq : P≤w^2 := by
    calc
      P = P^(1:ℝ) := (Real.rpow_one P).symm
      _≤P^(6/5:ℝ) := Real.rpow_le_rpow_of_exponent_le hP (by norm_num)
      _=(P^(3/5:ℝ))^2 := by rw [←Real.rpow_natCast,←Real.rpow_mul hp0.le]; norm_num
      _≤w^2 := pow_le_pow_left₀ (Real.rpow_nonneg hp0.le _) hw _
  have hs : Real.log (2+P)≤Real.sqrt w := by
    simp only [pow_one,one_mul] at hroot
    apply hroot.trans
    rw [Real.sqrt_eq_rpow]
    calc
      P^(3/10:ℝ) = (P^(3/5:ℝ))^(1/2:ℝ) := by rw [←Real.rpow_mul hp0.le]; norm_num
      _≤w^(1/2:ℝ) := Real.rpow_le_rpow (Real.rpow_nonneg hp0.le _) hw (by norm_num)
  refine ⟨hw1,hw16,hsq,hs,?_⟩
  calc
    4*C*(Real.log (2+P))^2≤P^(6/25:ℝ) := hcharge
    _=(P^(3/5:ℝ))^(2/5:ℝ) := by rw [←Real.rpow_mul hp0.le]; norm_num
    _≤w^(2/5:ℝ) := Real.rpow_le_rpow (Real.rpow_nonneg hp0.le _) hw (by norm_num)
    _=w^(1+(-3/5:ℝ)) := by norm_num
    _=w*w^(-3/5:ℝ) := by rw [Real.rpow_add hw0,Real.rpow_one]
    _≤w*δ := mul_le_mul_of_nonneg_left hδ hw0.le

lemma direction_count_cost_scalar_bound {N : ℕ} {U F r Ci Ck Cw Cb T H I w L : ℝ}
    (hU : 0≤U) (hF : 0≤F) (hr : 0≤r) (hCi : 0≤Ci) (hCk : 0≤Ck)
    (hCw : 0≤Cw) (hCb : 0≤Cb) (hT : 0≤T) (hH : max 1 T≤H)
    (hI : 0≤I) (hI1 : I≤1) (hw : 1≤w) (hL : 1≤L) (hLs : L≤Real.sqrt w) :
    ENNReal.ofReal r*(ENNReal.ofReal (U*w*L^5)+ENNReal.ofReal (Ci*T*I)+
      (N:ℝ≥0∞)*ENNReal.ofReal (2*Cw*Real.sqrt (max 1 T)*L^2)+
      ENNReal.ofReal (F*w*Real.sqrt w*L^5)*ENNReal.ofReal (Ck*Real.sqrt (max 1 T)*L^2/w))+
      ENNReal.ofReal (Cb*I)≤
    ENNReal.ofReal (((r*(U+Ci*H+F*Ck*Real.sqrt H)+Cb)*w*L^6)+
      (N:ℝ)*(r*2*Cw*Real.sqrt H)*L^2) := by
  have hTH : T≤H := (le_max_right _ _).trans hH
  have hh : 0≤H := hT.trans hTH
  have hw0 := zero_lt_one.trans_le hw
  have hL0 := zero_le_one.trans hL
  have hWL : 1≤w*L^6 := one_le_mul_of_one_le_of_one_le hw (one_le_pow₀ hL)
  have hc := direction_receiver_charge_scalar_bound hF hCk (by positivity : (0:ℝ)≤ max 1 T) hw0 hL0 hLs
  have hc' : ENNReal.ofReal (F*w*Real.sqrt w*L^5)*ENNReal.ofReal (Ck*Real.sqrt (max 1 T)*L^2/w)≤
      ENNReal.ofReal (F*Ck*Real.sqrt H*w*L^6) := hc.trans (by gcongr)
  have hu : U*w*L^5≤U*w*L^6 := mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hL (by norm_num : 5≤6)) (mul_nonneg hU hw0.le)
  have hi : Ci*T*I≤Ci*H*w*L^6 := by
    calc
      _≤Ci*H*1 := by gcongr
      _≤Ci*H*(w*L^6) := mul_le_mul_of_nonneg_left hWL (by positivity)
      _=_ := by ring
  have hb : Cb*I≤Cb*w*L^6 := by
    calc
      _≤Cb*1 := mul_le_mul_of_nonneg_left hI1 hCb
      _≤Cb*(w*L^6) := mul_le_mul_of_nonneg_left hWL hCb
      _=_ := by ring
  have he : (N:ℝ≥0∞)*ENNReal.ofReal (2*Cw*Real.sqrt (max 1 T)*L^2)≤
      (N:ℝ≥0∞)*ENNReal.ofReal (2*Cw*Real.sqrt H*L^2) := by gcongr
  apply (add_le_add (mul_le_mul' le_rfl (add_le_add (add_le_add (add_le_add
    (ENNReal.ofReal_le_ofReal hu) (ENNReal.ofReal_le_ofReal hi)) he) hc'))
    (ENNReal.ofReal_le_ofReal hb)).trans_eq
  rw [←ENNReal.ofReal_natCast N,←ENNReal.ofReal_mul (by positivity),
    ←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_add (by positivity) (by positivity),
    ←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_mul hr,
    ←ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

lemma direction_count_absorb {N : ℕ} {w δ L B C : ℝ}
    (hw : 0<w) (hδ : 0<δ) (hL : 1≤L) (hB : 0≤B)
    (hcost : (N:ℝ)*w*δ/2≤B*w*L^6+(N:ℝ)*C*L^2)
    (habs : 4*C*L^2≤w*δ) (hδ1 : δ≤1) :
    (N:ℝ)+1≤(4*B+1)*L^6/δ := by
  have hn := (Nat.cast_nonneg N : (0:ℝ)≤N)
  have hnc : (N:ℝ)*C*L^2≤(N:ℝ)*w*δ/4 := by nlinarith [mul_le_mul_of_nonneg_left habs hn]
  have hN : (N:ℝ)*δ≤4*B*L^6 := by
    apply (mul_le_mul_iff_right₀ hw).mp
    nlinarith
  apply (le_div_iff₀ hδ).mpr
  have hLp : 1≤L^6 := one_le_pow₀ hL
  rcases hB.eq_or_lt with hB | hB <;> nlinarith



open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


def datumEnergyNumber (d : Datum) : ℝ :=
  ∫x : Vec,(‖d.E₀ x‖^2+‖d.B₀ x‖^2)/2+∫v : Vec,q v*d.f₀ (x,v)

lemma Admissible.datumEnergyNumber_nonneg {d : Datum} (hd : Admissible d) :
    0≤datumEnergyNumber d := by
  apply integral_nonneg
  intro x
  apply add_nonneg (by positivity)
  exact integral_nonneg (fun v=>mul_nonneg (q_pos v).le (hd.2.2.1 _))

lemma SmoothClassicalPrefix.initial_energy_eq {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) :
    (∫x : Vec,totalEnergy s (0,x))=datumEnergyNumber d := by
  unfold totalEnergy particleEnergy datumEnergyNumber
  simp only [hs.initial_E,hs.initial_B,hs.initial_f]

lemma Admissible.direction_complete_count_real_bound {d : Datum} (hd : Admissible d)
    (T₀ M A : ℝ) (hM : 0<M) (hA : 0≤A) :
    ∃ B C : ℝ,0≤B ∧ 0≤C ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (S : Set Phase) (a b w P δ : ℝ) (_ : 0<w),
      zX∈tsupport d.f₀ → IsCompact S → tsupport d.f₀⊆S →
      0≤a → b≤T → a≤b → b-a≤(w/P)^2 →
      1≤P → 1≤Real.log (2+P) → 1≤w → w≤P → P≤w^2 →
      Real.log (2+P)≤Real.sqrt w →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ D : WeightedDirectionPartition (fun t=>(F.flow zX t).2)
        (fun t=>s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))) a b w δ,
      ((D.count-1:ℕ):ℝ)*w*δ/2≤B*w*(Real.log (2+P))^6+
        ((D.count-1:ℕ):ℝ)*C*(Real.log (2+P))^2 := by
  classical
  obtain ⟨Ct,Cr,Cf,Cl,Cg,Ci,Ck,Cw,Cb,hCt,hCr,hCf,hCl,hCg,hCi,hCk,hCw,hCb,hcost⟩ :=
    hd.direction_complete_count_cost_bound T₀
  obtain ⟨Fb,Ft,Fs,hFb,hFt,hFs,hforce⟩ := hd.direction_lorentz_uniform_log_bound T₀
  let E := datumEnergyNumber d
  let H := max 1 T₀
  let r := (4*Real.pi)⁻¹
  let U := directionUnionConstant E H M A Ct Cr Cf Cl Cg
  let R := Fb+r*(Ft*(1+E)*(1+16384*(M+Real.sqrt A))*H+Fs*(1+E)*(1+M+Real.sqrt A))
  let B := r*(U+Ci*H+R*Ck*Real.sqrt H)+Cb
  let C := r*2*Cw*Real.sqrt H
  have hE : 0≤E := hd.datumEnergyNumber_nonneg
  have hH : 0≤H := by dsimp [H]; positivity
  have hr : 0≤r := by dsimp [r]; positivity
  have hU : 0≤U := directionUnionConstant_nonneg hE hH hM.le hCt hCr hCf hCl hCg
  have hR : 0≤R := by dsimp [R]; positivity
  have hB : 0≤B := by dsimp [B]; positivity
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨B,C,hB,hC,?_⟩
  intro s T F hs hT hTT zX S a b w P δ hw hzX hS hS0 ha hb hab hJI hP hL hw1 hwP hPw hLs hsource hq hV HX HZ D
  have hTH : max 1 T≤H := max_le_max le_rfl hTT
  have hI : 0≤b-a := sub_nonneg.mpr hab
  have hI1 : b-a≤1 := by
    apply hJI.trans
    apply (sq_le_one_iff_abs_le_one _).mpr
    rw [abs_of_nonneg (div_nonneg hw.le (zero_le_one.trans hP))]
    exact (div_le_one (zero_lt_one.trans_le hP)).mpr hwP
  have hc := hcost s T F hs hT hTT zX S a b w M A P δ hw hzX hS hS0 ha hb hab hJI hM hA hP hL hw1 hwP hPw hsource hq hV HX HZ D
  rw [hs.initial_energy_eq] at hc
  have hf := hforce s T F hT hTT hs zX S a b w M A P hzX hS hS0 ha hb hab hJI hM hA hP hL hw1 hwP hsource hq HX HZ
  dsimp only at hf
  rw [hs.initial_energy_eq] at hf
  have hf' : (∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)≤
      ENNReal.ofReal (R*w*Real.sqrt w*(Real.log (2+P))^5) := by
    have he : (∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)=
        ∫⁻t in Icc a b,ENNReal.ofReal ‖s.E (t,(F.flow zX t).1)+
          cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))‖ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simp only [prefixMomentumForce,prefixFlow,prefixClamp_eq (Icc_subset_Icc ha hb ht),lorentzField,lorentzPhase]
    rw [he]
    exact hf.trans (direction_force_budget_scalar_bound hE hTH hM.le hw1 hL hFb hFt hFs hI1)
  have hu := directionUnionBudget_scalar_bound (A:=A) hE hTH hM.le hw1 hL hCt hCr hCf hCl hCg
  have hnum := direction_count_cost_scalar_bound (N:=D.count-1) hU hR hr hCi hCk hCw hCb hT hTH hI hI1 hw1 hL hLs
  have ht : ENNReal.ofReal (((D.count-1:ℕ):ℝ)*w*δ/2)≤
      ENNReal.ofReal (B*w*(Real.log (2+P))^6+((D.count-1:ℕ):ℝ)*C*(Real.log (2+P))^2) := by
    apply hc.trans
    apply le_trans _ hnum
    apply add_le_add _ le_rfl
    apply mul_le_mul' le_rfl
    exact add_le_add (add_le_add (add_le_add hu le_rfl) le_rfl) (mul_le_mul' hf' le_rfl)
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp ht

lemma Admissible.direction_count_bound {d : Datum} (hd : Admissible d)
    (T₀ M A : ℝ) (hM : 0<M) (hA : 0≤A) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (S : Set Phase) (a b w δ : ℝ),
      zX∈tsupport d.f₀ → IsCompact S → tsupport d.f₀⊆S →
      0≤a → b≤T → a≤b → b-a≤(w/P)^2 →
      P^(3/5:ℝ)≤w → w≤P → w^(-3/5:ℝ)≤δ → δ≤1 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ D : WeightedDirectionPartition (fun t=>(F.flow zX t).2)
        (fun t=>s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))) a b w δ,
      (D.count:ℝ)≤C*(Real.log (2+P))^6/δ := by
  obtain ⟨B,C,hB,hC,hbound⟩ := hd.direction_complete_count_real_bound T₀ M A hM hA
  refine ⟨4*B+1,by positivity,?_⟩
  filter_upwards [eventually_direction_absorption C] with P hP
  intro s T F hs hT hTT zX S a b w δ hzX hS hS0 ha hb hab hJI hw hwP hδ hδ1 hsource hq hV HX HZ D
  obtain ⟨hw1,hw16,hPw,hLs,habs⟩ := hP.2.2 w δ hw hδ
  have hw0 := zero_lt_one.trans_le hw1
  have hδ0 := (Real.rpow_pos_of_pos hw0 (-3/5)).trans_le hδ
  have hc := hbound s T F hs hT hTT zX S a b w P δ hw0 hzX hS hS0 ha hb hab hJI hP.1 hP.2.1 hw1 hwP hPw hLs hsource hq hV HX HZ D
  have hn := direction_count_absorb hw0 hδ0 hP.2.1 hB hc habs hδ1
  apply le_trans _ hn
  exact_mod_cast (show D.count≤D.count-1+1 by omega)

end RVM

end

end OAI
