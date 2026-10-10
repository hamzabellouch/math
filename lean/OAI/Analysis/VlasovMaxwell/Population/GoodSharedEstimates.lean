import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.GoodCrossings
import OAI.Analysis.VlasovMaxwell.Population.TransportRemainder

namespace OAI

noncomputable section

namespace RVM

section
open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


lemma Admissible.representative_regular_good_shared {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let h := cappedRepresentative (k 3)
      let R := representativeSharedRadius s F zX P M A w a b I (k 0,k 2)
      representativeRegularGoodCost s F zX P M A I w k a b≤
        ENNReal.ofReal (C*min (I*Real.sqrt h*p^2*φ^2) (Real.sqrt I*R/(θ*Real.sqrt h))) := by
  simpa only [mul_comm] using hd.representative_regular_good T₀

def goodInverseHalfConstant : ℝ := (1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹
lemma goodInverseHalfConstant_pos : 0<goodInverseHalfConstant := by
  apply inv_pos.mpr
  exact sub_pos.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num))

lemma capped_inverse_half_floor_sum {p : ℝ} (hp : 0<p) (S : Finset ℕ)
    (hS : ∀nt∈S,1/p≤cappedRepresentative nt) :
    (∑nt∈S,1/Real.sqrt (cappedRepresentative nt))≤goodInverseHalfConstant*Real.sqrt p := by
  have hh := capped_inverse_power_sum (one_div_pos.mpr hp) (by norm_num : (0:ℝ)<1/2) S hS
  have he (nt : ℕ) : 1/Real.sqrt (cappedRepresentative nt)=
      Real.sqrt p*((1/p)/cappedRepresentative nt)^(1/2:ℝ) := by
    rw [←Real.sqrt_eq_rpow,←Real.sqrt_mul hp.le]
    rw [show p*((1/p)/cappedRepresentative nt)=1/cappedRepresentative nt by field_simp]
    rw [Real.sqrt_div (by norm_num : (0:ℝ)≤1),Real.sqrt_one]
  simp_rw [he]
  rw [←Finset.mul_sum,mul_comm goodInverseHalfConstant]
  exact mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg p)

lemma capped_inverse_half_floor_tsum {p : ℝ} (hp : 0<p) :
    (∑'nt : ℕ,ENNReal.ofReal (if 1/p≤cappedRepresentative nt then
      1/Real.sqrt (cappedRepresentative nt) else 0))≤ENNReal.ofReal (goodInverseHalfConstant*Real.sqrt p) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun nt=>1/p≤cappedRepresentative nt)
  have he : (∑nt∈S,ENNReal.ofReal (if 1/p≤cappedRepresentative nt then
      1/Real.sqrt (cappedRepresentative nt) else 0))=
      ∑nt∈U,ENNReal.ofReal (1/Real.sqrt (cappedRepresentative nt)) := by
    simp only [U,Finset.sum_filter,apply_ite,ENNReal.ofReal_zero]
  rw [he,←ENNReal.ofReal_sum_of_nonneg (fun nt _=>by positivity)]
  exact ENNReal.ofReal_le_ofReal (capped_inverse_half_floor_sum hp U
    (fun nt hnt=>(Finset.mem_filter.mp hnt).2))

lemma good_shared_sqrt_balance {I p φ R θ : ℝ} (hI : 0≤I) (hp : 0≤p)
    (hφ : 0≤φ) (hR : 0≤R) (_ : 0<θ) :
    Real.sqrt ((I*p^2*φ^2)*(Real.sqrt I*R/θ))=
      Real.sqrt (I*Real.sqrt I)*Real.sqrt R*p*φ/Real.sqrt θ := by
  rw [show (I*p^2*φ^2)*(Real.sqrt I*R/θ)=((I*Real.sqrt I)*R*(p*φ)^2)/θ by ring]
  rw [Real.sqrt_div (by positivity),Real.sqrt_mul (by positivity : 0≤(I*Real.sqrt I)*R),
    Real.sqrt_sq (mul_nonneg hp hφ),Real.sqrt_mul (by positivity : 0≤I*Real.sqrt I)]
  ring

lemma good_shared_time_comparison {I p P w R : ℝ} (hI : 0≤I) (_ : 0≤p)
    (hpP : p≤P) (hP : 0<P) (hw : 0≤w) (hIP : I≤(w/P)^2) (hR : 1≤R) :
    Real.sqrt (I*Real.sqrt I)*Real.sqrt R*Real.sqrt p≤Real.sqrt w*Real.sqrt I*R := by
  have hsi : Real.sqrt I≤w/P := (Real.sqrt_le_iff).mpr ⟨div_nonneg hw hP.le,hIP⟩
  have hsiP : Real.sqrt I*P≤w := (le_div_iff₀ hP).mp hsi
  have hsip : Real.sqrt I*p≤w := (mul_le_mul_of_nonneg_left hpP (Real.sqrt_nonneg I)).trans hsiP
  have hR0 : 0≤R := zero_le_one.trans hR
  have hsR : Real.sqrt R≤R := by nlinarith [Real.sq_sqrt hR0,Real.sqrt_nonneg R]
  have hh : Real.sqrt (I*Real.sqrt I)*Real.sqrt p≤Real.sqrt w*Real.sqrt I := by
    rw [←Real.sqrt_mul (by positivity),←Real.sqrt_mul hw]
    apply Real.sqrt_le_sqrt
    nlinarith [mul_le_mul_of_nonneg_left hsip hI]
  calc
    _=(Real.sqrt (I*Real.sqrt I)*Real.sqrt p)*Real.sqrt R := by ring
    _≤(Real.sqrt w*Real.sqrt I)*R := mul_le_mul hh hsR (Real.sqrt_nonneg _) (by positivity)
    _=_ := by ring

lemma capped_half_tail_sum {x : ℝ} (hx : 0<x) :
    (∑'n : ℕ,ENNReal.ofReal (if cappedRepresentative n≤x then Real.sqrt (cappedRepresentative n) else 0))≤
      ENNReal.ofReal (goodInverseHalfConstant*Real.sqrt x) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun n=>cappedRepresentative n≤x)
  have he : (∑n∈S,ENNReal.ofReal (if cappedRepresentative n≤x then Real.sqrt (cappedRepresentative n) else 0))=
      ∑n∈U,ENNReal.ofReal (Real.sqrt (cappedRepresentative n)) := by simp [U,Finset.sum_filter,apply_ite]
  rw [he,←ENNReal.ofReal_sum_of_nonneg (fun n _=>Real.sqrt_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hh := capped_positive_power_sum_unscaled hx (by norm_num : (0:ℝ)<1/2) U
    (fun n hn=>(Finset.mem_filter.mp hn).2)
  simpa only [goodInverseHalfConstant,←Real.sqrt_eq_rpow] using hh

lemma capped_floor_count_half {p : ℝ} (hp : 0<p) :
    (∑'nt : ℕ,if 1/p≤cappedRepresentative nt then (1:ℝ≥0∞) else 0)≤
      ENNReal.ofReal (goodInverseHalfConstant*Real.sqrt p) := by
  apply le_trans _ (capped_inverse_half_floor_tsum hp)
  apply ENNReal.tsum_le_tsum
  intro nt
  split_ifs with ht
  · rw [←ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    apply (le_div_iff₀ (Real.sqrt_pos.mpr (cappedRepresentative_pos nt))).mpr
    simpa using Real.sqrt_le_one.mpr (cappedRepresentative_le_one nt)
  · simp

lemma good_exception_model_sum {P I p : ℝ} (hP : 0<P) (hI : 0≤I) (hp : 0<p) :
    (∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
      if 1/p≤cappedRepresentative nt then if cappedRepresentative nr≤1/P^2 then
        ENNReal.ofReal (I*Real.sqrt (cappedRepresentative nr)*p^2*(cappedRepresentative nf)^2)
      else 0 else 0)≤
      ENNReal.ofReal (2*goodInverseHalfConstant^2*I*p^2*Real.sqrt p/P) := by
  have hD := goodInverseHalfConstant_pos.le
  have hr (nf nt : ℕ) : (∑'nr : ℕ,if cappedRepresentative nr≤1/P^2 then
      ENNReal.ofReal (I*Real.sqrt (cappedRepresentative nr)*p^2*(cappedRepresentative nf)^2) else 0)≤
        ENNReal.ofReal (I*p^2*(cappedRepresentative nf)^2)*ENNReal.ofReal (goodInverseHalfConstant/P) := by
    have hc : 0≤I*p^2*(cappedRepresentative nf)^2 := by positivity
    have he (nr : ℕ) : (if cappedRepresentative nr≤1/P^2 then
        ENNReal.ofReal (I*Real.sqrt (cappedRepresentative nr)*p^2*(cappedRepresentative nf)^2) else 0)=
      ENNReal.ofReal (I*p^2*(cappedRepresentative nf)^2)*
        ENNReal.ofReal (if cappedRepresentative nr≤1/P^2 then Real.sqrt (cappedRepresentative nr) else 0) := by
      split_ifs with h
      · rw [←ENNReal.ofReal_mul hc]; congr 1; ring
      · simp
    simp_rw [he,ENNReal.tsum_mul_left]
    apply mul_le_mul' le_rfl
    have hh := capped_half_tail_sum (by positivity : 0<(1:ℝ)/P^2)
    simpa only [Real.sqrt_div (by norm_num : (0:ℝ)≤1),Real.sqrt_one,Real.sqrt_sq hP.le,mul_one_div] using hh
  have ht (nf : ℕ) : (∑'nt : ℕ,∑'nr : ℕ,
      if 1/p≤cappedRepresentative nt then if cappedRepresentative nr≤1/P^2 then
        ENNReal.ofReal (I*Real.sqrt (cappedRepresentative nr)*p^2*(cappedRepresentative nf)^2) else 0 else 0)≤
      ENNReal.ofReal (goodInverseHalfConstant^2*I*p^2*Real.sqrt p/P*(cappedRepresentative nf)^2) := by
    have hc : 0≤I*p^2*(cappedRepresentative nf)^2 := by positivity
    calc
      _≤(ENNReal.ofReal (I*p^2*(cappedRepresentative nf)^2)*ENNReal.ofReal (goodInverseHalfConstant/P))*
          (∑'nt : ℕ,if 1/p≤cappedRepresentative nt then (1:ℝ≥0∞) else 0) := by
        rw [←ENNReal.tsum_mul_left]
        apply ENNReal.tsum_le_tsum
        intro nt
        split_ifs with hnt
        · simpa only [mul_one] using hr nf nt
        · simp
      _≤(ENNReal.ofReal (I*p^2*(cappedRepresentative nf)^2)*ENNReal.ofReal (goodInverseHalfConstant/P))*
          ENNReal.ofReal (goodInverseHalfConstant*Real.sqrt p) := mul_le_mul' le_rfl (capped_floor_count_half hp)
      _=_ := by
        rw [←ENNReal.ofReal_mul hc,←ENNReal.ofReal_mul (mul_nonneg hc (div_nonneg hD hP.le))]
        congr 1; ring
  have hsq : (∑'nf : ℕ,ENNReal.ofReal ((cappedRepresentative nf)^2))≤2 := by
    have hh := capped_square_tail_sum (by norm_num : (0:ℝ)<1)
    simpa only [ite_eq_left (cappedRepresentative_le_one _),one_pow,ENNReal.ofReal_ofNat,mul_one] using hh
  have hc : 0≤goodInverseHalfConstant^2*I*p^2*Real.sqrt p/P := by positivity
  calc
    _≤∑'nf : ℕ,ENNReal.ofReal (goodInverseHalfConstant^2*I*p^2*Real.sqrt p/P*(cappedRepresentative nf)^2) := ENNReal.tsum_le_tsum ht
    _=ENNReal.ofReal (goodInverseHalfConstant^2*I*p^2*Real.sqrt p/P)*(∑'nf : ℕ,ENNReal.ofReal ((cappedRepresentative nf)^2)) := by
      simp_rw [ENNReal.ofReal_mul hc,ENNReal.tsum_mul_left]
    _≤ENNReal.ofReal (goodInverseHalfConstant^2*I*p^2*Real.sqrt p/P)*2 := mul_le_mul' le_rfl hsq
    _=_ := by rw [←ENNReal.ofReal_ofNat 2,←ENNReal.ofReal_mul hc]; congr 1; ring

noncomputable def representativeExceptionGoodCost {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (P M A I w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ :=
  if regularCentralIndex P M A I w k then 0 else representativeGoodCost s F zX w k a b

lemma good_cost_eq_regular_add_exception {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (P M A I w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) :
    representativeGoodCost s F zX w k a b=
      representativeRegularGoodCost s F zX P M A I w k a b+
      representativeExceptionGoodCost s F zX P M A I w k a b := by
  simp only [representativeRegularGoodCost,representativeExceptionGoodCost]
  split_ifs <;> simp

lemma Admissible.good_exception_triple_sum {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A P : ℝ,1≤M → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (np : ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I → 0<w →
      (∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
        if 1/sourceRepresentative np≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative nf/16 then
          representativeExceptionGoodCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤
        ENNReal.ofReal (C*I*(sourceRepresentative np)^2*Real.sqrt (sourceRepresentative np)/P) := by
  obtain ⟨Cn,hCn,hnear⟩ := hd.representative_good_near T₀
  refine ⟨2*goodInverseHalfConstant^2*Cn,by positivity,?_⟩
  intro M A P hM hP s T F hs hT hTT zX np a b I w ha hb hI hJI hw
  let p := sourceRepresentative np
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hpoint (nf nt nr : ℕ) :
      (if 1/p≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative nf/16 then
        representativeExceptionGoodCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤
      ENNReal.ofReal Cn*(if 1/p≤cappedRepresentative nt then if cappedRepresentative nr≤1/P^2 then
        ENNReal.ofReal (I*Real.sqrt (cappedRepresentative nr)*p^2*(cappedRepresentative nf)^2) else 0 else 0) := by
    by_cases ht : 1/p≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative nf/16
    · rw [ite_eq_left ht,ite_eq_left ht.1]
      by_cases hr : regularCentralIndex P M A I w ![np,nt,nf,nr]
      · simp only [representativeExceptionGoodCost,ite_eq_left hr]
        exact bot_le
      · have hreg : ¬(512/min p w<cappedRepresentative nf ∨
            min I (stabilityLength P 16384 M A p w (cappedRepresentative nf))<cappedRepresentative nr) := by
          simpa [regularCentralIndex,p] using hr
        have hf : cappedRepresentative nf≤512/min p w := le_of_not_gt (not_or.mp hreg).1
        have hnr : cappedRepresentative nr≤1/P^2 :=
          ((le_of_not_gt (not_or.mp hreg).2).trans (min_le_right _ _)).trans
            (small_deficit_stabilityLength hP hM hp hw (cappedRepresentative_pos _) hf)
        rw [ite_eq_left hnr,representativeExceptionGoodCost,ite_eq_right hr]
        apply (hnear s T F hs hT hTT zX ![np,nt,nf,nr] a b I w ha hb hI hJI).trans_eq
        rw [←ENNReal.ofReal_mul hCn]
        congr 1
    · rw [ite_eq_right ht]
      exact bot_le
  calc
    _≤∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
        ENNReal.ofReal Cn*(if 1/p≤cappedRepresentative nt then if cappedRepresentative nr≤1/P^2 then
          ENNReal.ofReal (I*Real.sqrt (cappedRepresentative nr)*p^2*(cappedRepresentative nf)^2) else 0 else 0) :=
      ENNReal.tsum_le_tsum (fun nf=>ENNReal.tsum_le_tsum (fun nt=>ENNReal.tsum_le_tsum (hpoint nf nt)))
    _=ENNReal.ofReal Cn*(∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
        if 1/p≤cappedRepresentative nt then if cappedRepresentative nr≤1/P^2 then
          ENNReal.ofReal (I*Real.sqrt (cappedRepresentative nr)*p^2*(cappedRepresentative nf)^2) else 0 else 0) := by
      simp only [ENNReal.tsum_mul_left]
    _≤ENNReal.ofReal Cn*ENNReal.ofReal (2*goodInverseHalfConstant^2*I*p^2*Real.sqrt p/P) :=
      mul_le_mul' le_rfl (good_exception_model_sum hP hI.le hp)
    _=_ := by rw [←ENNReal.ofReal_mul hCn]; congr 1; dsimp only [p]; ring

lemma Admissible.good_regular_radial {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (np nt nf : ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      cappedRepresentative nt≤cappedRepresentative nf/16 →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      (∑'nr : ℕ,representativeRegularGoodCost s F zX P M A I w ![np,nt,nf,nr] a b)≤
        ENNReal.ofReal (C*Real.sqrt (I*Real.sqrt I)*
          Real.sqrt (representativeSharedRadius s F zX P M A w a b I (np,nf))*
          sourceRepresentative np*cappedRepresentative nf/Real.sqrt (cappedRepresentative nt)) := by
  obtain ⟨C,hC,hbound⟩ := hd.representative_regular_good_shared T₀
  have hD : 0≤dyadicBalanceConstant (1/2) (1/2) := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  refine ⟨C*dyadicBalanceConstant (1/2) (1/2),mul_nonneg hC hD,?_⟩
  intro M A P hM hA hP s T F hs hT hTT zX np nt nf a b I w hzX ha hb hI hJI hw hsmall HZ
  let p := sourceRepresentative np
  let θ := cappedRepresentative nt
  let φ := cappedRepresentative nf
  let R := representativeSharedRadius s F zX P M A w a b I (np,nf)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have ht : 0<θ := cappedRepresentative_pos nt
  have hf : 0<φ := cappedRepresentative_pos nf
  have hR : 0≤R := zero_le_one.trans (representativeSharedRadius_one_le ..)
  have he (nr : ℕ) : min (I*Real.sqrt (cappedRepresentative nr)*p^2*φ^2)
        (Real.sqrt I*R/(θ*Real.sqrt (cappedRepresentative nr)))=
      min ((I*p^2*φ^2)*Real.sqrt (1*cappedRepresentative nr))
        ((Real.sqrt I*R/θ)/Real.sqrt (1*cappedRepresentative nr)) := by
    simp only [one_mul]
    congr 1 <;> ring
  calc
    _≤∑'nr : ℕ,ENNReal.ofReal (C*min (I*Real.sqrt (cappedRepresentative nr)*p^2*φ^2)
        (Real.sqrt I*R/(θ*Real.sqrt (cappedRepresentative nr)))) := by
      apply ENNReal.tsum_le_tsum
      intro nr
      exact hbound M A P hM hA hP s T F hs hT hTT zX ![np,nt,nf,nr] a b I w
        hzX ha hb hI hJI hw hsmall HZ
    _≤ENNReal.ofReal (C*dyadicBalanceConstant (1/2) (1/2)*
        Real.sqrt ((I*p^2*φ^2)*(Real.sqrt I*R/θ))) := by
      simp_rw [he]
      exact capped_sqrt_radius_ennreal_sum (by positivity) (by positivity) (by norm_num) hC
    _=_ := by
      rw [good_shared_sqrt_balance hI.le hp.le hf.le hR ht]
      congr 1
      ring

lemma Admissible.good_regular_double_sum {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (np nf : ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      sourceRepresentative np≤P → I≤(w/P)^2 →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      (∑'nt : ℕ,∑'nr : ℕ,if 1/sourceRepresentative np≤cappedRepresentative nt ∧
        cappedRepresentative nt≤cappedRepresentative nf/16 then
          representativeRegularGoodCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤
        ENNReal.ofReal (C*Real.sqrt w*Real.sqrt I*representativeSharedRadius s F zX P M A w a b I (np,nf)*
          sourceRepresentative np*cappedRepresentative nf) := by
  obtain ⟨C,hC,hbound⟩ := hd.good_regular_radial T₀
  have hD := goodInverseHalfConstant_pos.le
  refine ⟨C*goodInverseHalfConstant,mul_nonneg hC hD,?_⟩
  intro M A P hM hA hP s T F hs hT hTT zX np nf a b I w hzX ha hb hI hJI hw hpP hIP HZ
  let p := sourceRepresentative np
  let φ := cappedRepresentative nf
  let R := representativeSharedRadius s F zX P M A w a b I (np,nf)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hφ : 0<φ := cappedRepresentative_pos _
  have hR := representativeSharedRadius_one_le s F zX P M A w a b I (np,nf)
  have hc : 0≤C*Real.sqrt (I*Real.sqrt I)*Real.sqrt R*p*φ := by positivity
  have hsum : (∑'nt : ℕ,∑'nr : ℕ,if 1/p≤cappedRepresentative nt ∧ cappedRepresentative nt≤φ/16 then
      representativeRegularGoodCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤
      ENNReal.ofReal (C*Real.sqrt (I*Real.sqrt I)*Real.sqrt R*p*φ)*
        (∑'nt : ℕ,ENNReal.ofReal (if 1/p≤cappedRepresentative nt then 1/Real.sqrt (cappedRepresentative nt) else 0)) := by
    rw [←ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro nt
    by_cases ht : 1/p≤cappedRepresentative nt ∧ cappedRepresentative nt≤φ/16
    · simp only [ite_eq_left ht,ite_eq_left ht.1]
      apply (hbound M A P hM hA hP s T F hs hT hTT zX np nt nf a b I w
        hzX ha hb hI hJI hw ht.2 HZ).trans_eq
      rw [←ENNReal.ofReal_mul hc]
      congr 1
      ring
    · simp only [ite_eq_right ht,tsum_zero]
      exact bot_le
  apply hsum.trans
  calc
    _≤ENNReal.ofReal (C*Real.sqrt (I*Real.sqrt I)*Real.sqrt R*p*φ)*
        ENNReal.ofReal (goodInverseHalfConstant*Real.sqrt p) :=
      mul_le_mul' le_rfl (capped_inverse_half_floor_tsum hp)
    _≤_ := by
      rw [←ENNReal.ofReal_mul hc]
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_left
        (good_shared_time_comparison hI.le hp.le hpP hP hw.le hIP hR)
        (show 0≤C*goodInverseHalfConstant*p*φ by positivity)
      simpa only [p, φ, R, mul_assoc, mul_left_comm, mul_comm] using hh


end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma Admissible.good_regular_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w → w≤P → I≤(w/P)^2 →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if 1/sourceRepresentative n.1≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative n.2/16 then
          representativeRegularGoodCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*Real.sqrt w*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  classical
  obtain ⟨Cc,hCc,hcentral⟩ := hd.good_regular_double_sum T₀
  let E := 3468*datumEnergyNumber d
  let D := pairCountConstant+4*Real.sqrt pairCountConstant+2
  let K := 4+16384*Real.sqrt E*D
  have hE : 0≤E := mul_nonneg (by norm_num) hd.datumEnergyNumber_nonneg
  have hD : 0≤D := by dsimp [D]; exact add_nonneg (add_nonneg pairCountConstant_pos.le (by positivity)) (by norm_num)
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨Cc*K,mul_nonneg hCc hK,?_⟩
  intro M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hJI hw hwP hIP HZ
  dsimp only
  let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
    1/sourceRepresentative n.1≤cappedRepresentative n.2}
  let J := representativeJointEnergy s F zX a b I
  let R := representativeSharedRadius s F zX P M A w a b I
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hR (n : ℕ×ℕ) : 0<R n := zero_lt_one.trans_le (representativeSharedRadius_one_le ..)
  have hp (n : ℕ) : 0<sourceRepresentative n := by dsimp [sourceRepresentative]; positivity
  have hpair (n : ℕ×ℕ) (hn : n∈Q) : sourceRepresentative n.1≤P ∧
      1/sourceRepresentative n.1≤cappedRepresentative n.2 := hn
  obtain ⟨hJs,hJsum,hJeq⟩ := hs.representativeJointEnergy_sum hd F zX hI hJI
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun n=>n∈Q)
  have hU (n) (hn : n∈U) : n∈Q := (Finset.mem_filter.mp hn).2
  have he : (∑n∈S,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
      if 1/sourceRepresentative n.1≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative n.2/16 then
        representativeRegularGoodCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)=
      ∑n∈U,(∑'nt : ℕ,∑'nr : ℕ,if 1/sourceRepresentative n.1≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative n.2/16 then
        representativeRegularGoodCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) := by
    simp [U,Finset.sum_filter,indicator_apply]
  rw [he]
  have hJn (n : ℕ×ℕ) : 0≤J n := representativeJointEnergy_nonneg ..
  have hbudget : ∑n∈U,J n≤E := (hJs.sum_le_tsum U (fun n _=>hJn n)).trans hJsum
  have hn := shared_radius_pair_sum hP hL hM.le hA hI.le hw hwP hE U J
    (fun n _=>hJn n) hbudget (fun n hn=>hpair n (hU n hn))
  change (∑n∈U,Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2)≤
    K*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w) at hn
  calc
    _≤∑n∈U,ENNReal.ofReal (Cc*Real.sqrt w*Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hcentral M A P hM hA hP0 s T F hs hT hTT zX n.1 n.2 a b I w
        hzX ha hb hI hJI hw (hU n hn).1 hIP HZ
    _=ENNReal.ofReal ((Cc*Real.sqrt w)*(∑n∈U,Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2)) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun n _=>by
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCc (Real.sqrt_nonneg w)) (Real.sqrt_nonneg I)) (hR n).le) (hp _).le) (cappedRepresentative_pos _).le)]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _≤_ := ENNReal.ofReal_le_ofReal (by
      have hh := mul_le_mul_of_nonneg_left hn (mul_nonneg hCc (Real.sqrt_nonneg w))
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hh)



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


lemma sourceRepresentative_twohalf_sum {P : ℝ} (hP : 0≤P) (S : Finset ℕ)
    (hS : ∀np∈S,sourceRepresentative np≤P) :
    (∑np∈S,(sourceRepresentative np)^2*Real.sqrt (sourceRepresentative np))≤2*P^2*Real.sqrt P := by
  have hp (np : ℕ) : 0 ≤ sourceRepresentative np := by unfold sourceRepresentative; positivity
  calc
    _≤∑np∈S,(P*Real.sqrt P)*sourceRepresentative np := by
      apply Finset.sum_le_sum
      intro np hn
      have hh := mul_le_mul (hS np hn) (Real.sqrt_le_sqrt (hS np hn)) (Real.sqrt_nonneg _) hP
      have hh' := mul_le_mul_of_nonneg_right hh (hp np)
      nlinarith only [hh']
    _=(P*Real.sqrt P)*(∑np∈S,sourceRepresentative np) := (Finset.mul_sum ..).symm
    _≤(P*Real.sqrt P)*(2*P) := mul_le_mul_of_nonneg_left (sourceRepresentative_sum_bound hP S hS) (by positivity)
    _=2*P^2*Real.sqrt P := by ring

lemma Admissible.good_exception_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A P : ℝ,1≤M → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I → 0<w →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if 1/sourceRepresentative n.1≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative n.2/16 then
          representativeExceptionGoodCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*I*P*Real.sqrt P) := by
  obtain ⟨Cn,hCn,hnear⟩ := hd.good_exception_triple_sum T₀
  refine ⟨2*Cn,by positivity,?_⟩
  intro M A P hM hP s T F hs hT hTT zX a b I w ha hb hI hJI hw
  dsimp only
  let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
    1/sourceRepresentative n.1≤cappedRepresentative n.2}
  let g := fun np=>∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
    if 1/sourceRepresentative np≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative nf/16 then
      representativeExceptionGoodCost s F zX P M A I w ![np,nt,nf,nr] a b else 0
  have hc : 0≤Cn*I/P := by positivity
  have hdom : (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
      if 1/sourceRepresentative n.1≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative n.2/16 then
        representativeExceptionGoodCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ∑'np : ℕ,if sourceRepresentative np≤P then g np else 0 := by
    rw [ENNReal.tsum_prod']
    apply ENNReal.tsum_le_tsum
    intro np
    split_ifs with hn
    · apply ENNReal.tsum_le_tsum
      intro nf
      exact (indicator_le_self _ _) (np,nf)
    · have hz (nf : ℕ) : (np,nf)∉Q := fun hh=>hn hh.1
      simp only [indicator_of_notMem (hz _),tsum_zero,le_refl]
  apply hdom.trans
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun np=>sourceRepresentative np≤P)
  have hU (np) (hn : np∈U) : sourceRepresentative np≤P := (Finset.mem_filter.mp hn).2
  have he : (∑np∈S,if sourceRepresentative np≤P then g np else 0)=∑np∈U,g np := by
    simp [U,Finset.sum_filter]
  rw [he]
  calc
    _≤∑np∈U,ENNReal.ofReal (Cn*I*((sourceRepresentative np)^2*Real.sqrt (sourceRepresentative np))/P) := by
      apply Finset.sum_le_sum
      intro np hn
      simpa only [g,mul_assoc] using hnear M A P hM hP s T F hs hT hTT zX np a b I w ha hb hI hJI hw
    _=ENNReal.ofReal ((Cn*I/P)*(∑np∈U,(sourceRepresentative np)^2*Real.sqrt (sourceRepresentative np))) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun np _=>by unfold sourceRepresentative; positivity)]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro np hn
      ring
    _≤ENNReal.ofReal ((Cn*I/P)*(2*P^2*Real.sqrt P)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (sourceRepresentative_twohalf_sum hP.le U hU) hc)
    _=_ := by congr 1; field_simp



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


lemma good_exception_time_comparison {P I w : ℝ} (hP : 0<P) (hI : 0≤I)
    (hI1 : I≤1) (hw : 0≤w) (hIP : I≤(w/P)^2) :
    I*Real.sqrt P≤Real.sqrt w*Real.sqrt I := by
  have hs := (Real.sqrt_le_iff).mpr ⟨div_nonneg hw hP.le,hIP⟩
  have hsiP := (le_div_iff₀ hP).mp hs
  have hIs : I≤Real.sqrt I := by nlinarith [Real.sq_sqrt hI,Real.sqrt_nonneg I]
  have hIP' : I*P≤w := (mul_le_mul_of_nonneg_right hIs hP.le).trans hsiP
  have ht : Real.sqrt I*Real.sqrt P≤Real.sqrt w := by
    rw [←Real.sqrt_mul hI]
    exact Real.sqrt_le_sqrt hIP'
  have ht' := mul_le_mul_of_nonneg_right ht (Real.sqrt_nonneg I)
  calc
    _=(Real.sqrt I*Real.sqrt P)*Real.sqrt I := by
      rw [mul_right_comm,Real.mul_self_sqrt hI]
    _≤_ := ht'

lemma Admissible.small_good_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A P : ℝ,1≤M → 0≤A → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → I≤1 → b-a≤I → 0<w → w≤P → I≤(w/P)^2 →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      (∑'k : Fin 4→ℕ,(representativeSmallSector P).indicator
        (fun k=>representativeGoodCost s F zX w k a b) k)≤
        ENNReal.ofReal (C*Real.sqrt w*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cr,hCr,hregular⟩ := hd.good_regular_uniform T₀
  obtain ⟨Ce,hCe,hexception⟩ := hd.good_exception_uniform T₀
  refine ⟨Cr+Ce,add_nonneg hCr hCe,?_⟩
  intro M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hI1 hJI hw hwP hIP HZ
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  have hB : 0≤B := by dsimp [B]; positivity
  let R := representativeSmallSector P
  let g := fun k=>representativeRegularGoodCost s F zX P M A I w k a b
  let e := fun k=>representativeExceptionGoodCost s F zX P M A I w k a b
  have hsplit : (∑'k : Fin 4→ℕ,R.indicator (fun k=>representativeGoodCost s F zX w k a b) k)=
      (∑'k,R.indicator g k)+(∑'k,R.indicator e k) := by
    rw [←ENNReal.tsum_add]
    apply tsum_congr
    intro k
    by_cases hk : k∈R
    · simp only [indicator_of_mem hk]
      exact good_cost_eq_regular_add_exception s F zX P M A I w k a b
    · simp only [indicator_of_notMem hk,add_zero]
  have hr : (∑'k,R.indicator g k)≤ENNReal.ofReal (Cr*Real.sqrt w*B) := by
    rw [show R=representativeSmallSector P from rfl,tsum_representativeSmallSector]
    exact hregular M A P (zero_lt_one.trans_le hM) hA hP hL s T F hs hT hTT zX a b I w
      hzX ha hb hI hJI hw hwP hIP HZ
  have he : (∑'k,R.indicator e k)≤ENNReal.ofReal (Ce*Real.sqrt w*B) := by
    rw [show R=representativeSmallSector P from rfl,tsum_representativeSmallSector]
    apply (hexception M A P hM (zero_lt_one.trans_le hP) s T F hs hT hTT zX a b I w ha hb hI hJI hw).trans
    apply ENNReal.ofReal_le_ofReal
    have hi := good_exception_time_comparison (zero_lt_one.trans_le hP) hI.le hI1 hw.le hIP
    have hib : I*P*Real.sqrt P≤Real.sqrt w*B := by
      calc
        _=P*(I*Real.sqrt P) := by ring
        _≤P*(Real.sqrt w*Real.sqrt I) := mul_le_mul_of_nonneg_left hi (zero_le_one.trans hP)
        _≤Real.sqrt w*B := by
          have hh := mul_le_mul_of_nonneg_left (show P*Real.sqrt I≤B from le_add_of_nonneg_right (by positivity)) (Real.sqrt_nonneg w)
          simpa only [mul_assoc,mul_left_comm,mul_comm] using hh
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hib hCe
  rw [hsplit]
  apply (add_le_add hr he).trans_eq
  rw [←ENNReal.ofReal_add (by positivity : 0≤Cr*Real.sqrt w*B) (by positivity : 0≤Ce*Real.sqrt w*B)]
  congr 1
  ring

end RVM

end

end OAI
