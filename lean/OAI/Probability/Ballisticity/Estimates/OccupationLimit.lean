import Mathlib
import OAI.Probability.Ballisticity.Crossings.OccupationCutoffs
import OAI.Probability.Ballisticity.Crossings.PhysicalExit
import OAI.Probability.Ballisticity.Estimates.AllLayerOccupation

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

noncomputable def firstHitOccupationMean {d : ℕ} (ν : Measure (Row d)) (e f : Direction d)
    (x y : Lattice d) (s : ℝ) (H : ℕ) : ℝ :=
  ∑ j ∈ Finset.range H, (sharedConditionedPairLaw ν (realPosition (step e)) x y).real
    {P | |physicalFirstHitGap (realPosition (step e)) f x y j P| ≤ s}

lemma firstHitOccupationMean_nonneg {d : ℕ} (ν : Measure (Row d)) (e f : Direction d)
    (x y : Lattice d) (s : ℝ) (H : ℕ) : 0 ≤ firstHitOccupationMean ν e f x y s H :=
  Finset.sum_nonneg fun _ _ => measureReal_nonneg

theorem occupation_fixed_parameters {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (x : ℕ → Lattice d) {T A t ρ : ℝ} (hT : 0 < T) (hA : 1 ≤ A)
    (ht : 0 < t) (htmax : t ≤ 1/1000000) (hρ : 0 < ρ)
    {c : ℝ≥0∞} (hc : 0 < c) (hcu : ∀ u v, c ≤ sharedNoDropMass ν (realPosition (step e)) u v)
    {η : ℝ} (hη : 0 < η) :
    let ℓ := realPosition (step e)
    let m := commonMeanWidth ν ℓ
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    ∀ᶠ i in atTop, firstHitOccupationMean ν e f (x i) (x i) (ρ*r i) (⌊T*n i⌋₊+1)/n i ≤
      (occupationMacroConstant A*((128*m)*(2*ρ)^((1:ℝ)/4)+
        (128*m)*A^((1:ℝ)/4)*(8*Real.exp (-m/(16*t))))+
        T*(8*Real.exp (-m*A^2/(4*T))))/c.toReal+η := by
  dsimp only
  let ℓ := realPosition (step e)
  let m := commonMeanWidth ν ℓ
  let M := 128*m
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let H := fun i => ⌊T*n i⌋₊+1
  let δ := 8*Real.exp (-m/(16*t))
  let a := 8*Real.exp (-m*A^2/(4*T))
  let μ := fun i => sharedConditionedPairLaw ν ℓ (x i) (x i)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => sharedConditionedPairLaw_probability ν ℓ (x i) (x i)
    (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans (x i) (x i)))
  have hcfin : c ≠ ⊤ := ne_top_of_le_ne_top
    (show sharedNoDropMass ν ℓ 0 0 ≠ ⊤ from ne_top_of_le_ne_top (by simp)
      (show sharedNoDropMass ν ℓ 0 0 ≤ 1 from sharedNoDropMass_le_one ν ℓ 0 0)) (hcu 0 0)
  have hcr : 0 < c.toReal := ENNReal.toReal_pos hc.ne' hcfin
  obtain ⟨D⟩ := exists_occupationData ν hue e f hef htrans ht htmax
  obtain ⟨b,K,hb,hb0,hgood,hK⟩ := occupation_cutoff_escape ν hue e f hef htrans D A r hr
  have hm : 0 < m := zero_lt_one.trans_le (commonMeanWidth_ge_one ν ℓ htrans (signedHeight e)
    (signedHeight_projection e) (signedHeight_step_le e))
  have hM : 0 < M := by dsimp [M]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  let C := D.C/(D.q*((2:ℝ)^((3:ℝ)/2)-1))
  let L := occupationMacroConstant A*(M*(2*ρ)^((1:ℝ)/4)+M*A^((1:ℝ)/4)*δ)+T*a
  let B := fun i => 1/n i + (occupationMacroConstant A*(C*(b i/r i)^((1:ℝ)/4)+
    M*(2*ρ)^((1:ℝ)/4)+M*A^((1:ℝ)/4)*δ)+(T+1/n i)*a)/c.toReal
  have hnInf := recordFluctuationScale_tendsto ν hue e f hef htrans r hr.1
  have hinv : Tendsto (fun i => 1/n i) atTop (𝓝 0) := by
    convert tendsto_inv_atTop_zero.comp hnInf using 1
    simp only [Function.comp_def,n,ℓ,one_div]
  have hpow : Tendsto (fun i => (b i/r i)^((1:ℝ)/4)) atTop (𝓝 0) := by
    simpa only [Real.zero_rpow (by norm_num : (1:ℝ)/4 ≠ 0)] using
      hb0.rpow_const (Or.inr (by norm_num : (0:ℝ) ≤ 1/4))
  have hB : Tendsto B atTop (𝓝 (L/c.toReal)) := by
    have hh : Tendsto B atTop (𝓝 (0+(occupationMacroConstant A*(C*0+M*(2*ρ)^((1:ℝ)/4)+
        M*A^((1:ℝ)/4)*δ)+(T+0)*a)/c.toReal)) := hinv.add (((tendsto_const_nhds.mul (((tendsto_const_nhds.mul hpow).add tendsto_const_nhds).add
      tendsto_const_nhds)).add (((tendsto_const_nhds.add hinv).mul tendsto_const_nhds))).div_const c.toReal)
    simpa only [mul_zero,zero_add,add_zero] using hh
  have hless := hB.eventually_lt_const (show L/c.toReal < L/c.toReal+η by linarith)
  have hexit := shared_physical_exit_gaussian ν hue e f hef htrans r hr x hT hA0
  filter_upwards [hless,hexit,hr.1.eventually_gt_atTop 0,
    hb0.eventually_lt_const (by norm_num : (0:ℝ)<1),
    hb0.eventually_lt_const (mul_pos (by norm_num : (0:ℝ)<2) hρ)] with i hBi hei hri hbri hbs
  have hni : 0 < n i := recordFluctuationScale_pos ν hue e f hef htrans hri
  have hbpos : 0 < b i := D.u₀_pos.trans_le (hb i)
  have hbr : b i ≤ r i := by exact (div_lt_one hri).mp hbri |>.le
  have hbs' : b i ≤ 2*(ρ*r i) := by
    have hh := (div_lt_iff₀ hri).mp hbs
    nlinarith
  let J := max ((2:ℝ)^((7:ℝ)/4)) (A^2)*n i/(r i)^((3:ℝ)/2)
  let V := occupationCoefficient J D.C D.q M (b i) (r i) ρ A δ*(2*(A*r i))^((3:ℝ)/2)
  have hJ : 0 ≤ J := div_nonneg (mul_nonneg ((sq_nonneg A).trans (le_max_right _ _)) hni.le)
    (Real.rpow_nonneg hri.le _)
  have hV : 0 ≤ V := mul_nonneg
    (occupationCoefficient_nonneg hJ D.C_pos.le D.q_pos hM.le hbpos.le hri.le hρ.le hA0.le hδ)
    (Real.rpow_nonneg (by positivity) _)
  have hfinite := occupation_finite_bound ν hue e f hef htrans ht D (hb i) hbr hρ.le hA
    hbs' (hgood i) (K i) (hK i).1 (hK i).2.1 (hK i).2.2 (H i) (x i,x i) rfl
  dsimp only at hfinite
  rw [smallCommonCount_lintegral ν e f htrans (x i) (x i) (ρ*r i) (H i)] at hfinite
  have hreal := real_sum_le_of_ennreal_count (μ := μ i)
    (fun j => SmallCommonLayer e f (ρ*r i) (signedHeight e (x i)+j)) (H i) V
    (PhysicalGapExit e f (A*r i) (H i) (x i,x i)) hV hfinite
  have hall := all_layers_occupation_le ν hue e f htrans (x i) (x i) rfl (ρ*r i) (H i) c hcu
  rw [smallCommonCount_lintegral ν e f htrans (x i) (x i) (ρ*r i) (H i)] at hall
  have hallr := real_all_layer_bound (μ := μ i) _ _ (H i) hcfin hall
  have htotal : c.toReal*firstHitOccupationMean ν e f (x i) (x i) (ρ*r i) (H i) ≤
      c.toReal+V+(H i:ℝ)*a := by
    have hh := mul_le_mul_of_nonneg_left hei (Nat.cast_nonneg (H i))
    dsimp only [firstHitOccupationMean]
    linarith
  have hH : (H i:ℝ)/n i ≤ T+1/n i := by
    have hh := Nat.floor_le (mul_nonneg hT.le hni.le)
    dsimp only [H]
    rw [Nat.cast_add,Nat.cast_one]
    apply (div_le_iff₀ hni).mpr
    field_simp
    nlinarith
  have hnorm := occupation_coefficient_normalization hri hni hA0.le D.C D.q M (b i) ρ δ
  have hbound : firstHitOccupationMean ν e f (x i) (x i) (ρ*r i) (H i)/n i ≤ B i := by
    have hh := (div_le_div_iff_of_pos_right hni).mpr htotal
    have he : (c.toReal+V+(H i:ℝ)*a)/n i=c.toReal/n i+V/n i+((H i:ℝ)/n i)*a := by ring
    rw [he] at hh
    have hu := mul_le_mul_of_nonneg_right hH ha.le
    have hVN : V/n i=occupationMacroConstant A*(C*(b i/r i)^((1:ℝ)/4)+
        M*(2*ρ)^((1:ℝ)/4)+M*A^((1:ℝ)/4)*δ) := by
      simpa only [V,J,C,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hnorm
    rw [hVN] at hh
    dsimp only [B]
    have hh' := hh.trans (add_le_add_right hu _)
    have heq : c.toReal * (firstHitOccupationMean ν e f (x i) (x i) (ρ*r i) (H i)/n i) =
      c.toReal * firstHitOccupationMean ν e f (x i) (x i) (ρ*r i) (H i)/n i := by ring
    have hdiv : c.toReal * ((occupationMacroConstant A *
      (C*(b i/r i)^((1:ℝ)/4)+M*(2*ρ)^((1:ℝ)/4)+M*A^((1:ℝ)/4)*δ)+(T+1/n i)*a)/c.toReal) =
      occupationMacroConstant A *
      (C*(b i/r i)^((1:ℝ)/4)+M*(2*ρ)^((1:ℝ)/4)+M*A^((1:ℝ)/4)*δ)+(T+1/n i)*a :=
      mul_div_cancel₀ _ hcr.ne'
    have hcdiv : c.toReal/n i = c.toReal*(1/n i) := by ring
    nlinarith only [hh',heq,hdiv,hcdiv,hcr]
  exact hbound.trans hBi.le

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

lemma occupation_parameter_choice {m T c ε : ℝ} (hm : 0 < m) (hT : 0 < T)
    (hc : 0 < c) (hε : 0 < ε) :
    ∃ A t ρ : ℝ, 1 ≤ A ∧ 0 < t ∧ t ≤ 1/1000000 ∧ 0 < ρ ∧
      (occupationMacroConstant A*((128*m)*(2*ρ)^((1:ℝ)/4)+
        (128*m)*A^((1:ℝ)/4)*(8*Real.exp (-m/(16*t))))+
        T*(8*Real.exp (-m*A^2/(4*T))))/c < ε := by
  have hcoef : 0 < m/(4*T) := by positivity
  have hexp : Tendsto (fun A : ℝ => Real.exp (-m*A^2/(4*T))) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp ((tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).const_mul_atTop hcoef))
    convert hh using 1
    funext A
    simp only [Function.comp_apply]
    congr 1
    ring
  have hex : ∀ᶠ A : ℝ in atTop, T*(8*Real.exp (-m*A^2/(4*T))) < ε*c/3 := by
    have hh : Tendsto (fun A : ℝ => T*(8*Real.exp (-m*A^2/(4*T)))) atTop (𝓝 0) := by
      simpa only [mul_zero] using hexp.const_mul 8 |>.const_mul T
    exact hh.eventually_lt_const (by positivity)
  obtain ⟨A,hA,ha⟩ := ((eventually_ge_atTop (1:ℝ)).and hex).exists
  let K := occupationMacroConstant A
  let M := 128*m
  have htlim : Tendsto (fun z : ℝ => K*(M*A^((1:ℝ)/4)*(8*Real.exp (-m*z/16)))) atTop (𝓝 0) := by
    have he : Tendsto (fun z : ℝ => Real.exp (-m*z/16)) atTop (𝓝 0) := by
      have hh := Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (by positivity : 0 < m/16)))
      convert hh using 1
      funext z
      simp only [Function.comp_apply,id_eq]
      congr 1
      ring
    simpa only [mul_zero] using (he.const_mul 8).const_mul (M*A^((1:ℝ)/4)) |>.const_mul K
  obtain ⟨z,hz,hzsmall⟩ := ((eventually_ge_atTop (1000000:ℝ)).and
    (htlim.eventually_lt_const (show 0 < ε*c/3 by positivity))).exists
  have hzpos : 0 < z := lt_of_lt_of_le (by norm_num) hz
  let t := 1/z
  have ht : 0 < t := one_div_pos.mpr hzpos
  have htmax : t ≤ 1/1000000 := one_div_le_one_div_of_le (by norm_num) hz
  have htterm : K*(M*A^((1:ℝ)/4)*(8*Real.exp (-m/(16*t)))) < ε*c/3 := by
    have heq : -m/(16*t) = -m*z/16 := by
      dsimp [t]
      field_simp
    rw [heq]
    exact hzsmall
  have hrpow : Tendsto (fun z : ℝ => (2*(1/z))^((1:ℝ)/4)) atTop (𝓝 0) := by
    have hi : Tendsto (fun z : ℝ => 2*(1/z)) atTop (𝓝 0) := by
      simpa only [one_div,mul_zero] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul 2
    simpa only [Real.zero_rpow (by norm_num : (1:ℝ)/4 ≠ 0)] using
      hi.rpow_const (Or.inr (by norm_num : (0:ℝ) ≤ 1/4))
  have hrholim : Tendsto (fun z : ℝ => K*(M*(2*(1/z))^((1:ℝ)/4))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (hrpow.const_mul M).const_mul K
  obtain ⟨w,hw,hwsmall⟩ := ((eventually_gt_atTop (0:ℝ)).and
    (hrholim.eventually_lt_const (show 0 < ε*c/3 by positivity))).exists
  refine ⟨A,t,1/w,hA,ht,htmax,one_div_pos.mpr hw,?_⟩
  apply (div_lt_iff₀ hc).mpr
  dsimp only [K,M] at htterm hwsmall
  linarith

theorem shared_first_hit_occupation_vanishes {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (x : ℕ → Lattice d) {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧
      let n := fun i => fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) (r i)
      ∀ᶠ i in atTop, firstHitOccupationMean ν e f (x i) (x i) (ρ*r i) (⌊T*n i⌋₊+1)/n i ≤ ε := by
  let ℓ := realPosition (step e)
  let m := commonMeanWidth ν ℓ
  have hm : 0 < m := zero_lt_one.trans_le (commonMeanWidth_ge_one ν ℓ htrans (signedHeight e)
    (signedHeight_projection e) (signedHeight_step_le e))
  obtain ⟨c,hc,hcu⟩ := sharedNoDropMass_uniform_positive ν hue ℓ (signed_direction_unit e) htrans
  have hcfin : c ≠ ⊤ := ne_top_of_le_ne_top
    (show sharedNoDropMass ν ℓ 0 0 ≠ ⊤ from ne_top_of_le_ne_top (by simp)
      (show sharedNoDropMass ν ℓ 0 0 ≤ 1 from sharedNoDropMass_le_one ν ℓ 0 0)) (hcu 0 0)
  have hcr : 0 < c.toReal := ENNReal.toReal_pos hc.ne' hcfin
  obtain ⟨A,t,ρ,hA,ht,htmax,hρ,hsmall⟩ := occupation_parameter_choice hm hT hcr
    (show 0 < ε/2 by positivity)
  refine ⟨ρ,hρ,?_⟩
  have hb := occupation_fixed_parameters ν hue e f hef htrans r hr x hT hA ht htmax hρ
    hc hcu (show 0 < ε/2 by positivity)
  filter_upwards [hb] with i hi
  exact hi.trans (by linarith)

end DirectionalTransience

end

end

end OAI
