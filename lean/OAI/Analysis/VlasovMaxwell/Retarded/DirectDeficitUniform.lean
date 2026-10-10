import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.DirectionCounts
import OAI.Analysis.VlasovMaxwell.Population.DirectionOverlap

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma log_four_le_linear {P : ℝ} (hP : 1≤P) : (Real.log (2+P))^4≤768*P := by
  have hpos : 0<2+P := by linarith
  have hr := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hpos (1/4:ℝ))
  rw [Real.log_rpow hpos] at hr
  have hlog : 0≤Real.log (2+P) := Real.log_nonneg (by linarith)
  have hb : Real.log (2+P)≤4*(2+P)^(1/4:ℝ) := by linarith
  have hp := pow_le_pow_left₀ hlog hb 4
  have he : ((2+P)^(1/4:ℝ))^4=2+P := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hpos.le]
    norm_num
  rw [mul_pow,he] at hp
  nlinarith

lemma Admissible.direct_remaining_source_deficit_short_uniform {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T →
    ∀ (zX : Phase) (S : Set Phase) (a b I w P K : ℝ) (N : ℕ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → b-a≤I → 0<I → I≤1 → 0<w → 1≤P →
      I≤(w/P)^2 → 0≤K → (N:ℝ)≤K*Real.log (2+P) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun np nt nf j nr=>relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j
      (∑np∈Finset.range N,∑nf∈Finset.range N,∑nt∈Finset.range N,∑j∈Finset.range N,
        if sourceRepresentative np≤128*P ∧ cappedRepresentative nf≤16*cappedRepresentative nt ∧
          (cappedRepresentative j*sourceRepresentative np≤512 ∨ cappedRepresentative j*w≤32) then
        ∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤I then
          ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B np nt nf j nr) z
            ∂physicalBinMeasure V (B np nt nf j nr) (Icc a b) else 0 else 0)≤
      ENNReal.ofReal (C*K^4*(P*Real.sqrt I)) := by
  obtain ⟨Cg,Cb,hCg,hCb,hbin⟩ := hd.direct_source_deficit_short_sum
  let E := datumEnergyNumber d
  let D := (256*relativeCauchyConstant Cg E (20*E)+relativeCauchyConstant Cb E (120*E))*16777216*
    (1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹
  have hD : 0≤D := mul_nonneg (mul_nonneg (add_nonneg
    (mul_nonneg (by norm_num) (relativeCauchyConstant_nonneg hCg))
    (relativeCauchyConstant_nonneg hCb)) (by norm_num)) shortSqrtConstant_pos.le
  refine ⟨768*D,by positivity,?_⟩
  intro s T F hs hT zX S a b I w P K N hS hS0 ha hb hJI hI hI1 hw hP hIP hK hN
  dsimp only
  have hlog : 0≤Real.log (2+P) := Real.log_nonneg (by linarith)
  calc
    _≤∑np∈Finset.range N,∑nf∈Finset.range N,∑nt∈Finset.range N,∑j∈Finset.range N,
        ENNReal.ofReal (D*Real.sqrt I) := by
      apply Finset.sum_le_sum
      intro np hnp
      apply Finset.sum_le_sum
      intro nf hnf
      apply Finset.sum_le_sum
      intro nt hnt
      apply Finset.sum_le_sum
      intro j hj
      split_ifs with hsector
      · have hh := hbin s T F hs.energyPrefix hT hs.initial_f zX S np nt nf j a b I w P
          hS hS0 ha hb hJI hI hI1 hw (zero_lt_one.trans_le hP) hsector.1 hIP hsector.2.1 hsector.2.2
        dsimp only at hh
        rw [hs.initial_energy_eq] at hh
        exact hh
      · exact bot_le
    _=(N:ℝ≥0∞)^4*ENNReal.ofReal (D*Real.sqrt I) := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring
    _≤ENNReal.ofReal (K^4*(Real.log (2+P))^4*(D*Real.sqrt I)) :=
      ennreal_count_four_bound hK hlog hN (D*Real.sqrt I)
    _≤_ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _≤K^4*(768*P)*(D*Real.sqrt I) := by gcongr; exact log_four_le_linear hP
        _=_ := by ring

end RVM

end

end OAI
