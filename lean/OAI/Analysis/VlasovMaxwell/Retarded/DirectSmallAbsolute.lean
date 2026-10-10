import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.SpatialEstimates
import OAI.Analysis.VlasovMaxwell.Population.GoodSharedEstimates
import OAI.Analysis.VlasovMaxwell.Population.MagneticEstimates

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.small_source_absolute_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A P : ℝ,1≤M → 0≤A →
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I → 1≤w → w≤P → I≤(w/P)^2 →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let R := representativeSmallSector P
      (∑'k : Fin 4→ℕ,R.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalDirectSourceDensity s X V (representativeClosedBin T w k) z
          ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k)≤
      ENNReal.ofReal (C*Real.sqrt w*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cg,hCg,hgood⟩ := hd.small_good_uniform T₀
  obtain ⟨Cm,hCm,hmag⟩ := hd.magnetic_small_uniform T₀
  refine ⟨10240*(Cg+Cm),by positivity,?_⟩
  intro M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP HZ
  dsimp only
  let R := representativeSmallSector P
  let G := fun k=>representativeGoodCost s F zX w k a b
  let H := fun k=>representativeMagneticCost s F zX w k a b
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  have hB : 0≤B := by dsimp [B]; positivity
  have hPB : P*Real.sqrt I≤B := le_add_of_nonneg_right (by positivity)
  have hsum : (∑'k : Fin 4→ℕ,R.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalDirectSourceDensity s (fun t=>(prefixFlow F.flow T zX t).1)
          (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) z
          ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) (Icc a b)) k)≤
      ENNReal.ofReal 10240*((∑'k,R.indicator G k)+(∑'k,R.indicator H k)) := by
    rw [←ENNReal.tsum_add,←ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro k
    by_cases hk : k∈R
    · simp only [indicator_of_mem hk]
      have hc := (F.continuous_prefixFlow hs.energyPrefix hT).comp
        (continuous_id.prodMk continuous_const : Continuous (fun time : ℝ=>(time,zX)))
      have hp : 0<sourceRepresentative (k 0) := by unfold sourceRepresentative; positivity
      have ht := cappedRepresentative_pos (k 1)
      have hf := cappedRepresentative_pos (k 2)
      have hh := physicalDirectSource_integral_bound hs.energyPrefix hT hc.fst.measurable hc.snd.measurable
        (representativeClosedBin T w k) measurableSet_Icc (Icc_subset_Icc ha hb)
        (show 0<sourceRepresentative (k 0)/128 by positivity) ht hf
        (representativeClosedBin_radius_pos T w k) le_rfl le_rfl le_rfl
      apply hh.trans_eq
      dsimp only [G,H]
      unfold representativeGoodCost representativeMagneticCost
      dsimp only
      rw [mul_add,←mul_assoc,←mul_assoc,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10240),
        ←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10240)]
      congr 1
      · congr 1
        congr 1
        ring
      · rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_congr
        intro point
        have he : 10240*(cappedRepresentative (k 2)/sourceRepresentative (k 0))=
            (80/(sourceRepresentative (k 0)/128))*cappedRepresentative (k 2) := by ring
        rw [he,ENNReal.ofReal_mul (by positivity : 0≤80/(sourceRepresentative (k 0)/128))]
        dsimp only [Function.comp_apply,id_eq]
        ac_rfl
    · simp only [indicator_of_notMem hk,zero_add,mul_zero,le_refl]
  have hg' : (∑'k,R.indicator G k)≤ENNReal.ofReal (Cg*Real.sqrt w*B) :=
    hgood M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hI1 hJI
      (zero_lt_one.trans_le hw) hwP hIP HZ
  have hm : (∑'k,R.indicator H k)≤ENNReal.ofReal (Cm*Real.sqrt w*B) := by
    calc
      _≤∑'k,(centralIndexSector P).indicator H k := by
        apply ENNReal.tsum_le_tsum
        intro k
        by_cases hk : k∈R
        · rw [indicator_of_mem hk,indicator_of_mem (representativeSmallSector_subset_centralIndexSector P hk)]
        · rw [indicator_of_notMem hk]; exact bot_le
      _≤_ := by
        rw [tsum_centralIndexSector]
        apply (hmag M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hI1 hJI hw hwP HZ).trans
        apply ENNReal.ofReal_le_ofReal
        have hsw : 1≤Real.sqrt w := by simpa using Real.sqrt_le_sqrt hw
        have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsw hCm) hB
        simpa only [mul_one] using hh
  apply hsum.trans
  apply (mul_le_mul' le_rfl (add_le_add hg' hm)).trans_eq
  rw [←ENNReal.ofReal_add (by positivity : 0≤Cg*Real.sqrt w*B) (by positivity : 0≤Cm*Real.sqrt w*B),
    ←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10240)]
  congr 1
  ring

end RVM

end

end OAI
