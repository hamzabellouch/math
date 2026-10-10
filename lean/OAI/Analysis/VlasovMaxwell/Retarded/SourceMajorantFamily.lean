import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.MajorantRelativeDensityTimeFar

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma measurable_sourceMajorantFamily {α : Type*} [MeasurableSpace α]
    {r : α→ℝ} {n W v E B : α→Vec} (hr : Measurable r) (hn : Measurable n)
    (hW : Measurable W) (hv : Measurable v) (hE : Measurable E) (hB : Measurable B) :
    Measurable (fun x=>sourceMajorantKernel (r x) (n x) (W x) (v x) (E x) (B x)) := by
  have hu := (contDiff_velocity (k:=0)).continuous.measurable.comp hv
  have ha := (contDiff_velocity (k:=0)).continuous.measurable.comp hW
  have hq := (contDiff_q (k:=0)).continuous.measurable.comp hv
  have hd : Measurable (fun x=>1-dot (n x) (velocity (v x))) :=
    measurable_const.sub (continuous_dot.measurable.comp (hn.prodMk hu))
  have hD : Measurable (fun x=>1-dot (n x) (velocity (W x))) :=
    measurable_const.sub (continuous_dot.measurable.comp (hn.prodMk ha))
  have hG : Measurable (fun x=>goodField (E x) (B x) (n x)) := by
    unfold goodField
    exact ((hE.add ((contDiff_cross (k:=0)).continuous.measurable.comp (hn.prodMk hB))).norm.add
      (continuous_dot.measurable.comp (hn.prodMk hB)).abs)
  unfold sourceMajorantKernel
  exact ((measurable_const.mul (Real.continuous_sqrt.measurable.comp
    (measurable_const.mul hD))).div (hr.mul hq)).mul ((hG.div hd).add hB.norm)

lemma measurable_coneBin_scalarDensity {g : Particle} (hg : Measurable g)
    {X V : ℝ→Vec} (hX : Measurable X) (hV : Measurable V) (B : ClosedConeBin)
    {K : ConeCoordinate×Vec→ℝ} (hK : Measurable K) :
    Measurable (fun z : ConeCoordinate=>∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal (g (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))*K (z,v))) := by
  let H : Set (ConeCoordinate×Vec) := {p | p.2∈coneBinMomentumSet B p.1.2.2.1 (velocity (V p.1.1))}
  have hn : Measurable (fun p : ConeCoordinate×Vec=>p.1.2.2.1) :=
    measurable_subtype_coe.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hv : Measurable (fun p : ConeCoordinate×Vec=>velocity p.2) :=
    (contDiff_velocity (k:=0)).continuous.measurable.comp measurable_snd
  have ha : Measurable (fun p : ConeCoordinate×Vec=>velocity (V p.1.1)) :=
    (contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp (measurable_fst.comp measurable_fst))
  have hH : MeasurableSet H := by
    exact (measurableSet_Icc.preimage ((contDiff_q (k:=0)).continuous.measurable.comp measurable_snd)).inter
      ((measurableSet_Icc.preimage (measurable_const.sub (continuous_dot.measurable.comp (hn.prodMk hv)))).inter
        (measurableSet_Icc.preimage (measurable_const.sub (continuous_dot.measurable.comp (ha.prodMk hv)))))
  have hf : Measurable (fun p : ConeCoordinate×Vec=>
      g (p.1.2.1,(X p.1.1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2))) := by
    exact hg.comp ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
      (((hX.comp (measurable_fst.comp measurable_fst)).sub
        (((measurable_fst.comp measurable_fst).sub (measurable_fst.comp (measurable_snd.comp measurable_fst))).smul hn)).prodMk measurable_snd))
  have hm : Measurable (fun z : ConeCoordinate=>∫⁻v : Vec,H.indicator
      (fun p=>ENNReal.ofReal (g (p.1.2.1,(X p.1.1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2))*K p)) (z,v)) :=
    (((hf.mul hK).ennreal_ofReal).indicator hH).lintegral_prod_right'
  convert hm using 1
  ext z
  rw [←lintegral_indicator (measurableSet_coneBinMomentumSet B _ _)]
  apply lintegral_congr
  intro v
  rfl

lemma physicalSourceMajorantDensity_aemeasurable {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) {X V : ℝ→Vec} (hX : Measurable X) (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) :
    AEMeasurable (physicalSourceMajorantDensity s X V B) (physicalBinMeasure V B J) := by
  have ht : Measurable (fun p : ConeCoordinate×Vec=>p.1.1) := measurable_fst.comp measurable_fst
  have hσ : Measurable (fun p : ConeCoordinate×Vec=>p.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hn : Measurable (fun p : ConeCoordinate×Vec=>p.1.2.2.1) :=
    measurable_subtype_coe.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hy := hσ.prodMk ((hX.comp ht).sub ((ht.sub hσ).smul hn))
  have hK := measurable_sourceMajorantFamily (ht.sub hσ) hn (hV.comp ht) measurable_snd
    ((continuous_prefixField hs.E_smooth.continuousOn hT).measurable.comp hy)
    ((continuous_prefixField hs.B_smooth.continuousOn hT).measurable.comp hy)
  have hm := measurable_coneBin_scalarDensity (hs.continuous_prefixParticle hT).measurable hX hV B hK
  have hR : Measurable (fun z : ConeCoordinate=>ENNReal.ofReal ((z.1-z.2.1)^2)) :=
    ((measurable_fst.sub (measurable_fst.comp measurable_snd)).pow_const 2).ennreal_ofReal
  apply (hR.mul hm).aemeasurable.congr
  apply ae_restrict_of_forall_mem (measurableSet_physicalBinBase hV B hJ)
  intro z hz
  unfold physicalSourceMajorantDensity
  dsimp only [Pi.mul_apply]
  congr 1
  apply lintegral_congr
  intro v
  dsimp only [Pi.sub_apply,Pi.smul_apply',Function.comp_apply]
  simp only [prefixParticle,prefixField,prefixClamp_eq
    (show z.2.1∈Icc 0 T from ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩)]

lemma physicalSourceMajorantDensity_relative_cover {s : Solution} {X V : ℝ→Vec}
    (B : ClosedConeBin) (z : ConeCoordinate) {N : ℕ} (hN : 1024*B.qmax≤(2:ℝ)^N)
    (hf : Measurable (fun v : Vec=>s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v)))) :
    physicalSourceMajorantDensity s X V B z≤
      ∑j∈Finset.range N,physicalSourceMajorantDensity s X V (relativeBinRefinement B j) z := by
  let y := X z.1-(z.1-z.2.1) • z.2.2.1
  let g := fun v : Vec=>ENNReal.ofReal (s.f (z.2.1,(y,v))*
    sourceMajorantKernel (z.1-z.2.1) z.2.2.1 (V z.1) v (s.E (z.2.1,y)) (s.B (z.2.1,y)))
  have hg : Measurable g := (hf.mul (measurable_sourceMajorantFamily measurable_const measurable_const
    measurable_const measurable_id measurable_const measurable_const)).ennreal_ofReal
  have hc := lintegral_coneBin_relative_cover B z.2.2.1 (V z.1) hN hg
  unfold physicalSourceMajorantDensity
  dsimp only
  change ENNReal.ofReal ((z.1-z.2.1)^2)*(∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),g v)≤_
  apply (mul_le_mul' le_rfl hc).trans_eq
  exact Finset.mul_sum _ _ _

lemma physicalSourceMajorant_integral_relative_cover {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) {X V : ℝ→Vec} (hX : Measurable X) (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    {N : ℕ} (hN : 1024*B.qmax≤(2:ℝ)^N) :
    (∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V B z ∂physicalBinMeasure V B J)≤
      ∑j∈Finset.range N,∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V (relativeBinRefinement B j) z
        ∂physicalBinMeasure V (relativeBinRefinement B j) J := by
  have hp : (∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V B z ∂physicalBinMeasure V B J)≤
      ∫⁻z : ConeCoordinate,∑j∈Finset.range N,physicalSourceMajorantDensity s X V (relativeBinRefinement B j) z
        ∂physicalBinMeasure V B J := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV B hJ)] with z hz
    exact physicalSourceMajorantDensity_relative_cover B z hN
      (hs.measurable_velocity_slice ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩ _)
  apply hp.trans_eq
  exact lintegral_finsetSum' _ (fun j _=>
    physicalSourceMajorantDensity_aemeasurable hs hT hX hV (relativeBinRefinement B j) hJ hJT)

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma closed_deficit_index_lt {n v : Vec} {k N : ℕ} (hn : ‖n‖=1)
    (hd : 1-dot n (velocity v)≤8*(cappedRepresentative k)^2)
    (hP : 1024*q v≤(2:ℝ)^N) : k<N := by
  have hq := q_pos v
  have hθ := cappedRepresentative_pos k
  have heq := cappedRepresentative_mul_pow k
  have he := source_angle_coordinate_lower v n hn
  have hroot : Real.sqrt ((1-dot n (velocity v))/2)≤2*cappedRepresentative k := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity,by nlinarith only [hd]⟩
  have hqθ : 1/2≤2*q v*cappedRepresentative k :=
    he.trans (by nlinarith only [mul_le_mul_of_nonneg_left hroot hq.le])
  by_contra hc
  have hp : (2:ℝ)^N≤(2:ℝ)^k := pow_le_pow_right₀ (by norm_num) (Nat.le_of_not_gt hc)
  have hh := mul_le_mul_of_nonneg_right (hP.trans hp) hθ.le
  nlinarith only [hh,heq,hqθ]

lemma PhaseFlowOn.physicalSourceMajorant_integral_truncate {s : Solution} {T P w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hP0 : 0≤P) (hwP : w≤P)
    (hP : ∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P)
    (N : ℕ) (hN : 8192*P≤(2:ℝ)^N) (X V : ℝ→Vec) (hV : Measurable V)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) (k : Fin 4→ℕ)
    (hk : ¬(k 0<N ∧ k 1<N ∧ k 2<N ∧ sourceRepresentative (k 0)≤128*P)) :
    (∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V (representativeClosedBin T w k) z
      ∂physicalBinMeasure V (representativeClosedBin T w k) J)=0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV _ hJ)] with z hz
  have hnφ : k 2<N := closed_deficit_index_lt (sphere_norm z.2.2) hz.2.2.2.2.2 (by
    have hb : q (V z.1)≤8*w := hz.2.2.2.1.2
    linarith only [hb,hwP,hN])
  unfold physicalSourceMajorantDensity
  have hfzero : (∫⁻v in coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1 (velocity (V z.1)),
      let r := z.1-z.2.1
      let n := z.2.2.1
      let W := V z.1
      let y := X z.1-r • n
      ENNReal.ofReal (s.f (z.2.1,(y,v))*sourceMajorantKernel r n W v (s.E (z.2.1,y)) (s.B (z.2.1,y))))=0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_mem (measurableSet_coneBinMomentumSet _ _ _)] with v hv
    have hf : s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))=0 := by
      by_contra hc
      have hq := F.eulerian_supported_momentum hs hP
        ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩ _ v hc
      have hidx := representativeClosedBin_source_indices (sphere_norm z.2.2) hv
        (show 1024*q v≤(2:ℝ)^N by linarith only [hq,hP0,hN])
      have hp : sourceRepresentative (k 0)≤128*P := by
        have hh : sourceRepresentative (k 0)/128≤q v := hv.1.1
        linarith only [hh,hq]
      exact hk ⟨hidx.1,hidx.2,hnφ,hp⟩
    dsimp only
    simp only [hf,zero_mul,ENNReal.ofReal_zero,Pi.zero_apply]
  simp only [hfzero,mul_zero,Pi.zero_apply]

lemma tsum_quad_of_finite_radial_bound (f : (Fin 4→ℕ)→ℝ≥0∞) (N : ℕ) (c : ℝ≥0∞)
    (h : ∀np nt nf, (∑'nr,f ![np,nt,nf,nr]) ≤ (if np<N ∧ nt<N ∧ nf<N then c else 0)) :
    (∑'k,f k)≤(N:ℝ≥0∞)^3*c := by
  classical
  rw [tsum_quad_index]
  calc
    _ ≤ ∑'np,∑'nt,∑'nf,if np<N ∧ nt<N ∧ nf<N then c else 0 := by
      apply ENNReal.tsum_le_tsum
      intro np
      apply ENNReal.tsum_le_tsum
      intro nt
      exact ENNReal.tsum_le_tsum (h np nt)
    _ = ∑'np,if np<N then ∑'nt,if nt<N then ∑'nf,if nf<N then c else 0 else 0 else 0 := by
      apply tsum_congr
      intro np
      by_cases hp : np<N
      · simp only [hp,true_and,ite_true]
        apply tsum_congr
        intro nt
        by_cases ht : nt<N <;> simp [ht]
      · simp [hp]
    _ = _ := by simp only [ennreal_tsum_indicator_lt]; ring

lemma Admissible.source_majorant_remaining_radial_cover {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤C ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ : ℕ) (a b w M A P : ℝ) (N : ℕ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → a≤b → b-a≤(w/P)^2 →
      0<M → 0≤A → 1≤P → 1≤Real.log (2+P) → 0<w → w≤P →
      sourceRepresentative np≤128*P → 8192*P≤(2:ℝ)^N →
      cappedRepresentative nφ≤16384*cappedRepresentative nθ →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>representativeClosedBin T w ![np,nθ,nφ,nr]
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V (B nr) z
        ∂physicalBinMeasure V (B nr) (Icc a b))≤
      (N:ℝ≥0∞)*ENNReal.ofReal (C*(1+E)*(1+M+Real.sqrt A)*w*Real.log (2+P)) := by
  classical
  obtain ⟨C,hC,hbnd⟩ := hd₀.source_majorant_remaining_all_radii
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ a b w M A P N hS hS0 ha hb hab hJI
    hM hA hP hL hw hwP hpP hN hsector HX HZ
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := fun nr=>representativeClosedBin T w ![np,nθ,nφ,nr]
  let U := C*(1+∫x : Vec,totalEnergy s (0,x))*(1+M+Real.sqrt A)*w*Real.log (2+P)
  have hα := (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const : Continuous (fun t : ℝ=>(t,zX)))
  have hj : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  calc
    _ ≤ ∑'nr : ℕ,∑j∈Finset.range N,∫⁻z : ConeCoordinate,
        physicalSourceMajorantDensity s X V (relativeBinRefinement (B nr) j) z
          ∂physicalBinMeasure V (relativeBinRefinement (B nr) j) (Icc a b) := by
      apply ENNReal.tsum_le_tsum
      intro nr
      have hq : 1024*(B nr).qmax≤(2:ℝ)^N := by
        change 1024*(sourceRepresentative np/32)≤(2:ℝ)^N
        nlinarith only [hpP,hN,zero_lt_one.trans_le hP]
      exact physicalSourceMajorant_integral_relative_cover hs hT hα.fst.measurable hα.snd.measurable
          (B nr) measurableSet_Icc hj hq
    _ = ∑j∈Finset.range N,∑'nr : ℕ,∫⁻z : ConeCoordinate,
        physicalSourceMajorantDensity s X V (relativeBinRefinement (B nr) j) z
          ∂physicalBinMeasure V (relativeBinRefinement (B nr) j) (Icc a b) := by
      exact Summable.tsum_finsetSum (fun j hj=>ENNReal.summable)
    _ ≤ ∑j∈Finset.range N,ENNReal.ofReal U := by
      apply Finset.sum_le_sum
      intro j _
      exact hbnd s T F hs hT h0 zX S np nθ nφ j a b w M A P hS hS0 ha hb hab hJI
        hM hA hP hL hw hwP hpP hsector HX HZ
    _ = _ := by simp [U,nsmul_eq_mul]

end RVM

end

end OAI
