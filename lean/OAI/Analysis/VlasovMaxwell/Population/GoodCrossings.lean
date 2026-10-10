import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.CentralOccupation

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.representative_good_central {d : Datum} (hd : Admissible d) :
    ∃ C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → ∀(zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let E := datumEnergyNumber d
      representativeGoodCost s F zX w k a b ≤
        ENNReal.ofReal (cappedRepresentative (k 2)/(p*θ^2))*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
          (ENNReal.ofReal (128*C*p^3*θ^2)*representativeCentralCost s F zX w k a b)^(1/2:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := hd.uniform_physicalBinDensity_constant
  refine ⟨C,hC,?_⟩
  intro s T F hs hT zX k a b I w ha hb hI hab
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let r := max 1 T*cappedRepresentative (k 3)
  let B := representativeClosedBin T w k
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let N : ConeCoordinate→ℝ≥0∞ := fun z=>physicalBinDensity s X V B z.1 z.2.1 z.2.2
  let μ := physicalBinMeasure V B (Icc a b)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hr : 0<r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hBmax : B.rmax=2*r := by dsimp [B,representativeClosedBin,r]; ring
  have hBmin : B.rmin=r/2 := rfl
  have hE := hd.datumEnergyNumber_nonneg
  have hgood : ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I (k 2)≤
      ENNReal.ofReal (20*I*datumEnergyNumber d) := by
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.energyPrefix.goodFieldBudget_uniform X (fun t=>velocity (V t)) 1 hJ hI hab)
    rw [hs.initial_energy_eq] at hh
    calc
      _ ≤ ENNReal.ofReal I*((4*1+1:ℕ)*ENNReal.ofReal (4*datumEnergyNumber d)) := mul_le_mul' le_rfl hh
      _ = _ := by
        norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat]
        rw [←ENNReal.ofReal_ofNat (n:=5),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤5),
          ←ENNReal.ofReal_mul hI.le]
        congr 1
        ring
  have hangle (D : ℝ) (hD : D∈Icc B.Dmin B.Dmax) : DyadicWindow 1 (k 2) (Real.sqrt (D/2)) :=
    dyadicWindow_one_sqrt (k 2)
      (by simpa only [B,representativeClosedBin,cappedRepresentative,inv_pow] using hD.1)
      (by simpa only [B,representativeClosedBin,cappedRepresentative,inv_pow] using hD.2)
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs.energyPrefix hT).comp (continuous_id.prodMk continuous_const)
  have hX : Measurable X := hα.fst.measurable
  have hV : Measurable V := hα.snd.measurable
  have hN : AEMeasurable N μ :=
    physicalBinDensity_aemeasurable hs.energyPrefix hT hX hV B measurableSet_Icc hJ
  have hG := hs.energyPrefix.measurable_prefixConeGood hT hX
  let W : ConeCoordinate→ℝ≥0∞ := fun z=>ENNReal.ofReal (z.1-z.2.1)*
      ENNReal.ofReal (prefixConeGood s T X z)
  have hW : AEMeasurable W μ :=
    ((measurable_fst.sub (measurable_fst.comp measurable_snd)).ennreal_ofReal.mul hG.ennreal_ofReal).aemeasurable
  have hfield : (∫⁻z, W z^2 ∂μ)≤ENNReal.ofReal (20*I*datumEnergyNumber d) := by
    apply le_trans _ ((hs.energyPrefix.physicalBin_goodField hT hX hV B 1 (k 2) hJ hI hangle).trans hgood)
    apply le_of_eq
    apply lintegral_congr_ae
    apply ae_restrict_of_forall_mem (measurableSet_physicalBinBase hV B measurableSet_Icc)
    intro z hz
    have hr : 0≤z.1-z.2.1 := sub_nonneg.mpr hz.2.1.2
    have hg : 0≤prefixConeGood s T X z := add_nonneg (norm_nonneg _) (abs_nonneg _)
    dsimp [W]
    rw [mul_pow,←ENNReal.ofReal_pow hr,←ENNReal.ofReal_pow hg,←ENNReal.ofReal_mul (sq_nonneg _)]
  have hD : ∀ᵐz ∂μ,N z≤ENNReal.ofReal (128*C*p^3*θ^2) := by
    apply ae_restrict_of_forall_mem (measurableSet_physicalBinBase hV B measurableSet_Icc)
    intro z hz
    have hh := hbound s T F hs.energyPrefix hs.initial_f X V B z.1 z.2.1 z.2.2 p θ 1
      ⟨hz.2.1.1,hz.2.1.2.trans (hJ hz.1).2⟩ hp.le hθ.le (by norm_num)
      (by change p/32≤p; linarith) le_rfl (by norm_num [B,representativeClosedBin])
    have hθ1 : θ≤1 := cappedRepresentative_le_one (k 1)
    simpa only [min_eq_left hθ1] using hh
  change ENNReal.ofReal (φ/(p*θ^2))*(∫⁻z,W z*N z ∂μ)≤_
  apply mul_le_mul' le_rfl
  have hh := lintegral_product_bound_two μ hW hN hfield hD
    (le_rfl : (∫⁻z,N z ∂μ)≤∫⁻z,N z ∂μ) (le_rfl : μ univ≤μ univ)
  apply hh.trans
  apply mul_le_mul' le_rfl
  exact ENNReal.rpow_le_rpow (min_le_right _ _) (by norm_num)

lemma capped_sqrt_min_sum {a b q : ℝ} (ha : 0<a) (hb : 0<b) (hq : 0≤q)
    (hab : a*b≤q^2) :
    (∑'n : ℕ,ENNReal.ofReal (min (a*Real.sqrt (cappedRepresentative n))
      (b/Real.sqrt (cappedRepresentative n)))) ≤
      ENNReal.ofReal (dyadicBalanceConstant (1/2) (1/2)*q) := by
  let r := b/a
  have hr : 0<r := div_pos hb ha
  let g : ℤ→ℝ := fun k=>min (a*((2:ℝ)^k)^((1:ℝ)/2)) (b*((2:ℝ)^k)^(-((1:ℝ)/2)))
  have hg := dyadic_power_min_summable ha.le hb.le (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1/2)
  have ht := dyadic_balance_at ha.le hb.le (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1/2) hr
  have hn : a*Real.sqrt r≤q := by
    have hs := Real.sq_sqrt hr.le
    have he : a^2*r=a*b := by dsimp [r]; field_simp
    nlinarith [mul_nonneg ha.le (Real.sqrt_nonneg r)]
  have hf : b/Real.sqrt r≤q := by
    have he : b/Real.sqrt r=a*Real.sqrt r := by
      apply (div_eq_iff (Real.sqrt_pos.mpr hr).ne').mpr
      have hs := Real.sq_sqrt hr.le
      have he : a*r=b := by dsimp [r]; field_simp
      nlinarith
    rwa [he]
  have hd : 0<1-((2:ℝ)^((1:ℝ)/2))⁻¹ := sub_pos.mpr
    (inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) (by norm_num : (0:ℝ)<1/2)))
  have ht' : (∑'k : ℤ,g k)≤dyadicBalanceConstant (1/2) (1/2)*q := by
    apply ht.trans
    rw [Real.rpow_neg hr.le,←Real.sqrt_eq_rpow]
    have hn' := div_le_div_of_nonneg_right hn hd.le
    have hf' := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hf hd.le)
      (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) ((1:ℝ)/2))
    dsimp [dyadicBalanceConstant]
    simp only [div_eq_mul_inv] at hn' hf' ⊢
    nlinarith only [hn',hf']
  have he (n : ℕ) : cappedRepresentative n=(2:ℝ)^(-(n:ℤ)) := by
    simp only [cappedRepresentative,zpow_neg,zpow_natCast,inv_pow]
  have he' (n : ℕ) : min (a*Real.sqrt (cappedRepresentative n))
      (b/Real.sqrt (cappedRepresentative n))=g (-(n:ℤ)) := by
    dsimp [g]
    rw [Real.rpow_neg (zpow_pos (by norm_num : (0:ℝ)<2) _).le,←Real.sqrt_eq_rpow,he]
    rfl
  have hinj : Function.Injective (fun n : ℕ=>-(n:ℤ)) := by
    intro x y hxy
    exact_mod_cast neg_injective hxy
  simp_rw [he']
  apply (ENNReal.tsum_comp_le_tsum_of_injective hinj (fun k=>ENNReal.ofReal (g k))).trans
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun k=>by positivity) hg]
  exact ENNReal.ofReal_le_ofReal ht'

lemma magnetic_shared_radial_sum {I R p θ φ : ℝ}
    (hI : 0<I) (hI1 : I≤1) (hR : 1≤R) (hp : 0<p) (hθ : 0<θ) (hθ1 : θ≤1) (hφ : 0<φ) :
    (∑'n : ℕ, ENNReal.ofReal (min
      (I*Real.sqrt (cappedRepresentative n)*p^2*θ^2*φ)
      (Real.sqrt I*R*θ/(Real.sqrt (cappedRepresentative n)*φ))))≤
      ENNReal.ofReal (dyadicBalanceConstant (1/2) (1/2)*Real.sqrt I*R*p*θ) := by
  have hR0 : 0<R := zero_lt_one.trans_le hR
  have hSI : Real.sqrt I≤1 := by simpa using Real.sqrt_le_sqrt hI1
  have hin : Real.sqrt I*θ≤R := ((mul_le_of_le_one_left hθ.le hSI).trans hθ1).trans hR
  have hab : (I*p^2*θ^2*φ)*(Real.sqrt I*R*θ/φ)≤(Real.sqrt I*R*p*θ)^2 := by
    have hh := mul_le_mul_of_nonneg_left hin (by positivity : 0≤I*R*p^2*θ^2)
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hI.le]
    calc
      _ = I*R*p^2*θ^2*(Real.sqrt I*θ) := by field_simp
      _ ≤ I*R*p^2*θ^2*R := hh
      _ = _ := by ring
  have hh := capped_sqrt_min_sum (by positivity : 0<I*p^2*θ^2*φ)
    (by positivity : 0<Real.sqrt I*R*θ/φ) (by positivity : 0≤Real.sqrt I*R*p*θ) hab
  convert hh using 1
  · congr 1
    ext n
    congr 1
    congr 1 <;> ring
  · congr 1
    ring

lemma good_central_near_scalar {C E D I h p θ φ : ℝ}
    (hC : 0≤C) (hE : 0≤E) (hD : 0≤D) (hI : 0≤I) (hh : 0≤h)
    (hp : 0<p) (hθ : 0<θ) (hφ : 0≤φ) :
    (φ/(p*θ^2))*(Real.sqrt (20*I*E)*Real.sqrt ((128*C*p^3*θ^2)*(D*(I*h*p^3*θ^2*φ^2))))=
    Real.sqrt (2560*C*E*D)*(I*Real.sqrt h*p^2*φ^2) := by
  rw [←Real.sqrt_mul (by positivity : 0≤20*I*E)]
  have he : Real.sqrt ((20*I*E)*((128*C*p^3*θ^2)*(D*(I*h*p^3*θ^2*φ^2))))=
      Real.sqrt (2560*C*E*D)*(I*Real.sqrt h*p^3*θ^2*φ) := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    simp only [mul_pow,Real.sq_sqrt (by positivity : 0≤2560*C*E*D),Real.sq_sqrt hh]
    ring
  rw [he]
  field_simp

lemma good_central_far_scalar {C E D I R h p θ φ : ℝ}
    (hC : 0≤C) (hE : 0≤E) (hD : 0≤D) (hI : 0≤I) (hR : 0≤R)
    (hh : 0<h) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ) :
    (φ/(p*θ^2))*(Real.sqrt (20*I*E)*Real.sqrt ((128*C*p^3*θ^2)*(D*(R^2/(p*h*φ^2)))))=
    Real.sqrt (2560*C*E*D)*(Real.sqrt I*R/(Real.sqrt h*θ)) := by
  rw [←Real.sqrt_mul (by positivity : 0≤20*I*E)]
  have he : Real.sqrt ((20*I*E)*((128*C*p^3*θ^2)*(D*(R^2/(p*h*φ^2)))))=
      Real.sqrt (2560*C*E*D)*(Real.sqrt I*R*p*θ/(Real.sqrt h*φ)) := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    simp only [div_pow,mul_pow,Real.sq_sqrt (by positivity : 0≤2560*C*E*D),
      Real.sq_sqrt hh.le,Real.sq_sqrt hI]
    field_simp
    ring
  rw [he]
  field_simp

lemma good_central_near_ennreal {C E D I h p θ φ : ℝ}
    (hC : 0≤C) (hE : 0≤E) (hD : 0≤D) (hI : 0≤I) (hh : 0≤h)
    (hp : 0<p) (hθ : 0<θ) (hφ : 0≤φ) :
    ENNReal.ofReal (φ/(p*θ^2))*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
      (ENNReal.ofReal (128*C*p^3*θ^2)*ENNReal.ofReal (D*(I*h*p^3*θ^2*φ^2)))^(1/2:ℝ))=
    ENNReal.ofReal (Real.sqrt (2560*C*E*D)*(I*Real.sqrt h*p^2*φ^2)) := by
  rw [←ENNReal.ofReal_mul (by positivity : 0≤128*C*p^3*θ^2),
    ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
    ←ENNReal.ofReal_mul (Real.sqrt_nonneg _),←ENNReal.ofReal_mul (by positivity),
    good_central_near_scalar hC hE hD hI hh hp hθ hφ]

lemma good_central_far_ennreal {C E D I R h p θ φ : ℝ}
    (hC : 0≤C) (hE : 0≤E) (hD : 0≤D) (hI : 0≤I) (hR : 0≤R)
    (hh : 0<h) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ) :
    ENNReal.ofReal (φ/(p*θ^2))*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
      (ENNReal.ofReal (128*C*p^3*θ^2)*ENNReal.ofReal (D*(R^2/(p*h*φ^2))))^(1/2:ℝ))=
    ENNReal.ofReal (Real.sqrt (2560*C*E*D)*(Real.sqrt I*R/(Real.sqrt h*θ))) := by
  rw [←ENNReal.ofReal_mul (by positivity : 0≤128*C*p^3*θ^2),
    ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
    ←ENNReal.ofReal_mul (Real.sqrt_nonneg _),←ENNReal.ofReal_mul (by positivity),
    good_central_far_scalar hC hE hD hI hR hh hp hθ hφ]

noncomputable def representativeRegularGoodCost {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (P M A I w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ := by
  classical
  exact if regularCentralIndex P M A I w k then
    representativeGoodCost s F zX w k a b else 0

lemma Admissible.representative_regular_good {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
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
        ENNReal.ofReal (C*min (I*Real.sqrt h*p^2*φ^2) (Real.sqrt I*R/(Real.sqrt h*θ))) := by
  classical
  obtain ⟨Cd,hCd,hmag⟩ := hd.representative_good_central
  obtain ⟨Cc,hCc,hcentral⟩ := hd.representative_regular_central_shared T₀
  let E := datumEnergyNumber d
  have hE : 0≤E := hd.datumEnergyNumber_nonneg
  let C := Real.sqrt (2560*Cd*E*Cc)
  refine ⟨C,Real.sqrt_nonneg _,?_⟩
  intro M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha hb hI hab hw hsmall HZ
  dsimp only
  unfold representativeRegularGoodCost
  split_ifs with hk
  · have hcen := hcentral M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha hb hI hab hw hsmall HZ
    unfold representativeRegularCentralCost at hcen
    rw [ite_eq_left hk] at hcen
    let p := sourceRepresentative (k 0)
    let θ := cappedRepresentative (k 1)
    let φ := cappedRepresentative (k 2)
    let h := cappedRepresentative (k 3)
    let R := representativeSharedRadius s F zX P M A w a b I (k 0,k 2)
    have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
    have hθ : 0<θ := cappedRepresentative_pos _
    have hφ : 0<φ := cappedRepresentative_pos _
    have hh : 0<h := cappedRepresentative_pos _
    have hR : 0≤R := zero_le_one.trans (representativeSharedRadius_one_le ..)
    have hmb := hmag s T F hs hT zX k a b I w ha hb hI hab
    dsimp only at hcen hmb
    have hnear : representativeGoodCost s F zX w k a b≤
        ENNReal.ofReal (C*(I*Real.sqrt h*p^2*φ^2)) := by
      apply hmb.trans
      apply le_trans _ (le_of_eq (good_central_near_ennreal hCd hE hCc hI.le hh.le hp hθ hφ.le))
      apply mul_le_mul' le_rfl
      apply mul_le_mul' le_rfl
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      apply mul_le_mul' le_rfl
      apply hcen.trans
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (min_le_left _ _) hCc)
    have hfar : representativeGoodCost s F zX w k a b≤
        ENNReal.ofReal (C*(Real.sqrt I*R/(Real.sqrt h*θ))) := by
      apply hmb.trans
      apply le_trans _ (le_of_eq (good_central_far_ennreal hCd hE hCc hI.le hR hh hp hθ hφ))
      apply mul_le_mul' le_rfl
      apply mul_le_mul' le_rfl
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      apply mul_le_mul' le_rfl
      apply hcen.trans
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (min_le_right _ _) hCc)
    rw [mul_min_of_nonneg _ _ (Real.sqrt_nonneg _),ENNReal.ofReal_min]
    exact le_min hnear hfar
  · exact bot_le

lemma capped_negative_power_sum {x α : ℝ} (hx : 0<x) (hα : 0<α)
    (S : Finset ℕ) (hS : ∀j∈S,x≤cappedRepresentative j) :
    ∑j∈S,(x/cappedRepresentative j)^α≤(1-((2:ℝ)⁻¹)^α)⁻¹ := by
  classical
  have hbase : 0<((2:ℝ)⁻¹)^α := Real.rpow_pos_of_pos (by norm_num) _
  have hbase1 : ((2:ℝ)⁻¹)^α<1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hnorm : ‖((2:ℝ)⁻¹)^α‖<1 := by rw [Real.norm_eq_abs,abs_of_pos hbase]; exact hbase1
  by_cases hne : S.Nonempty
  · let j₀ := S.max' hne
    have hj₀ : j₀∈S := S.max'_mem hne
    have hjmax (j : ℕ) (hj : j∈S) : j≤j₀ := S.le_max' j hj
    have hp (j : ℕ) (hj : j∈S) : x/cappedRepresentative j≤((2:ℝ)⁻¹)^(j₀-j) := by
      have he : cappedRepresentative j₀=cappedRepresentative j*((2:ℝ)⁻¹)^(j₀-j) := by
        dsimp only [cappedRepresentative]
        rw [←pow_add,Nat.add_sub_of_le (hjmax j hj)]
      apply (div_le_iff₀ (cappedRepresentative_pos j)).mpr
      exact (hS j₀ hj₀).trans_eq (by rw [he,mul_comm])
    have hpoint (j : ℕ) (hj : j∈S) : (x/cappedRepresentative j)^α≤(((2:ℝ)⁻¹)^α)^(j₀-j) := by
      rw [Real.rpow_pow_comm (by norm_num : (0:ℝ)≤2⁻¹)]
      exact Real.rpow_le_rpow (div_nonneg hx.le (cappedRepresentative_pos j).le) (hp j hj) hα.le
    have hinj : Set.InjOn (fun j : ℕ=>j₀-j) S := by
      intro i hi j hj hij
      have hi' := hjmax i hi
      have hj' := hjmax j hj
      change j₀-i=j₀-j at hij
      omega
    calc
      _≤∑j∈S,(((2:ℝ)⁻¹)^α)^(j₀-j) := Finset.sum_le_sum hpoint
      _=∑m∈S.image (fun j=>j₀-j),(((2:ℝ)⁻¹)^α)^m := (Finset.sum_image hinj).symm
      _≤∑'m : ℕ,(((2:ℝ)⁻¹)^α)^m :=
        (summable_geometric_of_norm_lt_one hnorm).sum_le_tsum _ (fun _ _=>by positivity)
      _=_ := tsum_geometric_of_norm_lt_one hnorm
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty]
    exact inv_nonneg.mpr (sub_nonneg.mpr hbase1.le)

lemma capped_inverse_head_sum {x : ℝ} (hx : 0<x) :
    (∑'j : ℕ,if x≤cappedRepresentative j then ENNReal.ofReal (x/cappedRepresentative j) else 0)≤2 := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun j=>x≤cappedRepresentative j)
  have he : (∑j∈S,if x≤cappedRepresentative j then ENNReal.ofReal (x/cappedRepresentative j) else 0)=
      ∑j∈U,ENNReal.ofReal (x/cappedRepresentative j) := by simp [U,Finset.sum_filter]
  rw [he,←ENNReal.ofReal_sum_of_nonneg (fun j _=>div_nonneg hx.le (cappedRepresentative_pos j).le)]
  have hb := capped_negative_power_sum hx (by norm_num : (0:ℝ)<1) U
    (fun j hj=>(Finset.mem_filter.mp hj).2)
  norm_num at hb
  exact (ENNReal.ofReal_le_ofReal hb).trans_eq (by norm_num)

lemma capped_balance_sum {a b α β : ℝ} (ha : 0<a) (hb : 0<b)
    (hα : 0<α) (hβ : 0<β) :
    (∑'j : ℕ,ENNReal.ofReal (min (a*(cappedRepresentative j)^α)
      (b*(cappedRepresentative j)^(-β))))≤
      ENNReal.ofReal (dyadicBalanceConstant α β*(a^(β/(α+β))*b^(α/(α+β)))) := by
  let g : ℤ→ℝ := fun k=>min (a*((2:ℝ)^k)^α) (b*((2:ℝ)^k)^(-β))
  have hg : Summable g := dyadic_power_min_summable ha.le hb.le hα hβ
  have hg0 (k : ℤ) : 0≤g k := by dsimp [g]; positivity
  have he (j : ℕ) : cappedRepresentative j=(2:ℝ)^(-(j:ℤ)) := by
    simp only [cappedRepresentative,zpow_neg,zpow_natCast,inv_pow]
  have hi : Function.Injective (fun j : ℕ=>-(j:ℤ)) := by
    intro a b hab
    exact_mod_cast neg_injective hab
  simp_rw [he]
  calc
    _≤∑'k : ℤ,ENNReal.ofReal (g k) := ENNReal.tsum_comp_le_tsum_of_injective hi _
    _=ENNReal.ofReal (∑'k : ℤ,g k) := (ENNReal.ofReal_tsum_of_nonneg hg0 hg).symm
    _≤_ := ENNReal.ofReal_le_ofReal (dyadic_balance ha hb hα hβ)

lemma scaled_capped_crossing_sum {n f x α : ℝ} (hn : 0<n) (hf : 0<f)
    (hx : 0<x) (hα : 0<α) :
    (∑'j : ℕ,if x≤cappedRepresentative j then
      ENNReal.ofReal (min (n*(cappedRepresentative j/x)^α)
        (f*(cappedRepresentative j/x)^(-1:ℝ))) else 0)≤
      ENNReal.ofReal (min (2*f)
        (dyadicBalanceConstant α 1*(n^(1/(α+1))*f^(α/(α+1))))) := by
  classical
  rw [ENNReal.ofReal_min]
  apply le_min
  · calc
      _≤∑'j : ℕ,if x≤cappedRepresentative j then
          ENNReal.ofReal f*ENNReal.ofReal (x/cappedRepresentative j) else 0 := by
        apply ENNReal.tsum_le_tsum
        intro j
        split_ifs
        · rw [←ENNReal.ofReal_mul hf.le,Real.rpow_neg_one,inv_div]
          exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
        · rfl
      _=ENNReal.ofReal f*(∑'j : ℕ,if x≤cappedRepresentative j then
          ENNReal.ofReal (x/cappedRepresentative j) else 0) := by
        rw [←ENNReal.tsum_mul_left]
        apply tsum_congr
        intro j
        split_ifs <;> simp
      _≤ENNReal.ofReal f*2 := mul_le_mul' le_rfl (capped_inverse_head_sum hx)
      _=ENNReal.ofReal (2*f) := by rw [mul_comm,ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]; norm_num
  · have hnorm : (n/x^α)^(1/(α+1))*(f*x)^(α/(α+1))=
        n^(1/(α+1))*f^(α/(α+1)) := by
      rw [Real.div_rpow hn.le (Real.rpow_nonneg hx.le _),Real.mul_rpow hf.le hx.le,
        ←Real.rpow_mul hx.le]
      have he : α*(1/(α+1))=α/(α+1) := by ring
      rw [he]
      have hz := (Real.rpow_pos_of_pos hx (α/(α+1))).ne'
      field_simp
    have he (j : ℕ) : min (n*(cappedRepresentative j/x)^α)
        (f*(cappedRepresentative j/x)^(-1:ℝ))=
        min ((n/x^α)*(cappedRepresentative j)^α) ((f*x)*(cappedRepresentative j)^(-1:ℝ)) := by
      rw [Real.div_rpow (cappedRepresentative_pos j).le hx.le,Real.rpow_neg_one,
        Real.rpow_neg_one,inv_div]
      congr 1 <;> ring
    calc
      _≤∑'j : ℕ,ENNReal.ofReal (min ((n/x^α)*(cappedRepresentative j)^α)
          ((f*x)*(cappedRepresentative j)^(-1:ℝ))) := by
        apply ENNReal.tsum_le_tsum
        intro j
        split_ifs
        · exact le_of_eq (congrArg ENNReal.ofReal (he j))
        · exact bot_le
      _≤ENNReal.ofReal (dyadicBalanceConstant α 1*
          ((n/x^α)^(1/(α+1))*(f*x)^(α/(α+1)))) :=
        capped_balance_sum (div_pos hn (Real.rpow_pos_of_pos hx _)) (mul_pos hf hx) hα (by norm_num)
      _=_ := by rw [hnorm]

lemma good_structural_radial_sum {I R p θ φ : ℝ}
    (hI : 0<I) (hR : 0<R) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ)
    (hband : φ/16384≤θ) :
    (∑'n : ℕ, ENNReal.ofReal (min
      (I*Real.sqrt (cappedRepresentative n)*p^2*φ^2)
      (Real.sqrt I*R/(Real.sqrt (cappedRepresentative n)*θ))))≤
      ENNReal.ofReal (dyadicBalanceConstant (1/2) (1/2)*128*
        (Real.sqrt I*R*p*φ+I*p)) := by
  let X := Real.sqrt I*R*p*φ
  let Y := I*p
  have hX : 0≤X := by dsimp [X]; positivity
  have hY : 0≤Y := by dsimp [Y]; positivity
  have hratio : φ/θ≤16384 := (div_le_iff₀ hθ).mpr (by linarith)
  have hab : (I*p^2*φ^2)*(Real.sqrt I*R/θ)≤(128*(X+Y))^2 := by
    calc
      _=(X*Y)*(φ/θ) := by dsimp [X,Y]; ring
      _≤(X*Y)*16384 := mul_le_mul_of_nonneg_left hratio (mul_nonneg hX hY)
      _≤(128*(X+Y))^2 := by nlinarith [sq_nonneg X,sq_nonneg Y,mul_nonneg hX hY]
  have hh := capped_sqrt_min_sum (by positivity : 0<I*p^2*φ^2)
    (by positivity : 0<Real.sqrt I*R/θ) (by positivity : 0≤128*(X+Y)) hab
  convert hh using 1
  · congr 1
    ext n
    congr 1
    congr 1 <;> ring
  · congr 1
    dsimp [X,Y]
    ring

lemma structural_angle_tsum_le {φ B : ℝ} (hφ : 0<φ) (hB : 0≤B)
    (f : ℕ→ℝ≥0∞)
    (hf : ∀n,φ/16384≤cappedRepresentative n → cappedRepresentative n≤φ/16 →
      f n≤ENNReal.ofReal B) :
    (∑'n : ℕ,if φ/16384≤cappedRepresentative n ∧ cappedRepresentative n≤φ/16 then f n else 0)≤
      ENNReal.ofReal (32768*B) := by
  classical
  have hpoint (n : ℕ) :
      (if φ/16384≤cappedRepresentative n ∧ cappedRepresentative n≤φ/16 then f n else 0)≤
      ENNReal.ofReal (16384*B)*(if φ/16384≤cappedRepresentative n then
        ENNReal.ofReal ((φ/16384)/cappedRepresentative n) else 0) := by
    by_cases hn : φ/16384≤cappedRepresentative n ∧ cappedRepresentative n≤φ/16
    · rw [ite_eq_left hn,ite_eq_left hn.1,←ENNReal.ofReal_mul (by positivity : 0≤16384*B)]
      apply (hf n hn.1 hn.2).trans
      apply ENNReal.ofReal_le_ofReal
      have hθ : cappedRepresentative n≤φ := hn.2.trans (by linarith)
      have hh := mul_le_mul_of_nonneg_left ((one_le_div (cappedRepresentative_pos n)).mpr hθ) hB
      calc
        B=B*1 := (mul_one _).symm
        _≤B*(φ/cappedRepresentative n) := hh
        _=_ := by ring
    · rw [ite_eq_right hn]
      exact bot_le
  apply (ENNReal.tsum_le_tsum hpoint).trans
  rw [ENNReal.tsum_mul_left]
  apply (mul_le_mul' le_rfl (capped_inverse_head_sum (by positivity : 0<φ/16384))).trans_eq
  rw [←ENNReal.ofReal_ofNat (n:=2),←ENNReal.ofReal_mul (by positivity : 0≤16384*B)]
  congr 1
  ring

lemma Admissible.representative_regular_good_structural_double_sum {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (np nf : ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let p := sourceRepresentative np
      let φ := cappedRepresentative nf
      let R := representativeSharedRadius s F zX P M A w a b I (np,nf)
      (∑'nt : ℕ,∑'nr : ℕ,if φ/16384≤cappedRepresentative nt ∧ cappedRepresentative nt≤φ/16 then
        representativeRegularGoodCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤
        ENNReal.ofReal (C*(Real.sqrt I*R*p*φ+I*p)) := by
  classical
  obtain ⟨C,hC,hbound⟩ := hd.representative_regular_good T₀
  let K := dyadicBalanceConstant (1/2) (1/2)
  have hK : 0<K := dyadicBalanceConstant_pos (by norm_num) (by norm_num)
  refine ⟨32768*C*K*128,by positivity,?_⟩
  intro M A P hM hA hP s T F hs hT hTT zX np nf a b I w hzX ha hb hI hJI hw HZ
  dsimp only
  let p := sourceRepresentative np
  let φ := cappedRepresentative nf
  let R := representativeSharedRadius s F zX P M A w a b I (np,nf)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hφ : 0<φ := cappedRepresentative_pos _
  have hR : 0<R := zero_lt_one.trans_le (representativeSharedRadius_one_le ..)
  have hr (nt : ℕ) (hl : φ/16384≤cappedRepresentative nt) (hnt : cappedRepresentative nt≤φ/16) :
      (∑'nr : ℕ,representativeRegularGoodCost s F zX P M A I w ![np,nt,nf,nr] a b)≤
      ENNReal.ofReal (C*(K*128*(Real.sqrt I*R*p*φ+I*p))) := by
    calc
      _≤∑'nr : ℕ,ENNReal.ofReal (C*min
          (I*Real.sqrt (cappedRepresentative nr)*p^2*φ^2)
          (Real.sqrt I*R/(Real.sqrt (cappedRepresentative nr)*cappedRepresentative nt))) := by
        apply ENNReal.tsum_le_tsum
        intro nr
        exact hbound M A P hM hA hP s T F hs hT hTT zX ![np,nt,nf,nr] a b I w
          hzX ha hb hI hJI hw hnt HZ
      _=ENNReal.ofReal C*(∑'nr : ℕ,ENNReal.ofReal (min
          (I*Real.sqrt (cappedRepresentative nr)*p^2*φ^2)
          (Real.sqrt I*R/(Real.sqrt (cappedRepresentative nr)*cappedRepresentative nt)))) := by
        simp_rw [ENNReal.ofReal_mul hC,ENNReal.tsum_mul_left]
      _≤ENNReal.ofReal C*ENNReal.ofReal (K*128*(Real.sqrt I*R*p*φ+I*p)) :=
        mul_le_mul' le_rfl (good_structural_radial_sum hI hR hp (cappedRepresentative_pos _) hφ hl)
      _=_ := (ENNReal.ofReal_mul hC).symm
  have he (nt : ℕ) : (∑'nr : ℕ,if φ/16384≤cappedRepresentative nt ∧ cappedRepresentative nt≤φ/16 then
      representativeRegularGoodCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)=
      if φ/16384≤cappedRepresentative nt ∧ cappedRepresentative nt≤φ/16 then
        (∑'nr : ℕ,representativeRegularGoodCost s F zX P M A I w ![np,nt,nf,nr] a b) else 0 := by
    split_ifs <;> simp
  change (∑'nt : ℕ,∑'nr : ℕ,if φ/16384≤cappedRepresentative nt ∧ cappedRepresentative nt≤φ/16 then
      representativeRegularGoodCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤_
  simp_rw [he]
  apply (structural_angle_tsum_le hφ (by positivity) _ hr).trans_eq
  congr 1
  ring

lemma small_pair_source_sum {P : ℝ} (hP : 1≤P) (hL : 1≤Real.log (2+P))
    (S : Finset (ℕ×ℕ)) (hS : ∀n∈S,sourceRepresentative n.1≤P ∧
      1/sourceRepresentative n.1≤cappedRepresentative n.2) :
    (∑n∈S,sourceRepresentative n.1)≤2*pairCountConstant*P*Real.log (2+P) := by
  classical
  let U := S.image Prod.fst
  let V := S.image Prod.snd
  have hU (n) (hn : n∈U) : sourceRepresentative n≤P := by
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hn
    exact (hS k hk).1
  have hsub : S⊆U.product V := by
    intro n hn
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨n,hn,rfl⟩,Finset.mem_image.mpr ⟨n,hn,rfl⟩⟩
  have hc := (small_pair_cardinals hP hL S hS).2
  have hp : 0≤P := zero_le_one.trans hP
  calc
    _≤∑n∈U.product V,sourceRepresentative n.1 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _=>by dsimp [sourceRepresentative]; positivity)
    _=(∑n∈U,sourceRepresentative n)*(V.card:ℝ) := by
      simp only [Finset.product_eq_sprod,Finset.sum_product,Finset.sum_const,nsmul_eq_mul]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _≤(2*P)*(pairCountConstant*Real.log (2+P)) :=
      mul_le_mul (sourceRepresentative_sum_bound hp U hU) hc (Nat.cast_nonneg _) (by positivity)
    _=_ := by ring

lemma small_pair_I_source_sum {P M A I w : ℝ} (hP : 1≤P) (hL : 1≤Real.log (2+P))
    (hM : 1≤M) (hI : 0≤I) (hw : 0<w) (hwP : w≤P)
    (S : Finset (ℕ×ℕ)) (hS : ∀n∈S,sourceRepresentative n.1≤P ∧
      1/sourceRepresentative n.1≤cappedRepresentative n.2) :
    (∑n∈S,I*sourceRepresentative n.1)≤2*pairCountConstant*
      (P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w) := by
  have hpc := pairCountConstant_pos
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hL0 : 0≤Real.log (2+P) := zero_le_one.trans hL
  have hstep : I*P*Real.log (2+P)≤(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w := by
    have hm : 1≤M+Real.sqrt A := hM.trans (le_add_of_nonneg_right (Real.sqrt_nonneg A))
    have hratio : 1≤P/w := (one_le_div hw).mpr hwP
    have hh := mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hm hratio)
      (by positivity : 0≤I*P*Real.log (2+P))
    calc
      _=(I*P*Real.log (2+P))*1 := (mul_one _).symm
      _≤(I*P*Real.log (2+P))*((M+Real.sqrt A)*(P/w)) := hh
      _=_ := by ring
  rw [←Finset.mul_sum]
  calc
    _≤I*(2*pairCountConstant*P*Real.log (2+P)) := mul_le_mul_of_nonneg_left (small_pair_source_sum hP hL S hS) hI
    _=2*pairCountConstant*(I*P*Real.log (2+P)) := by ring
    _≤2*pairCountConstant*((M+Real.sqrt A)*I*P^2*Real.log (2+P)/w) :=
      mul_le_mul_of_nonneg_left hstep (by positivity : 0≤2*pairCountConstant)
    _≤_ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity : 0≤2*pairCountConstant)

lemma Admissible.good_regular_structural_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,1≤M → 0≤A → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w → w≤P →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative n.2/16384≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative n.2/16 then
          representativeRegularGoodCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  classical
  obtain ⟨Cc,hCc,hcentral⟩ := hd.representative_regular_good_structural_double_sum T₀
  let E := 3468*datumEnergyNumber d
  let D := pairCountConstant+4*Real.sqrt pairCountConstant+2
  let K := 4+16384*Real.sqrt E*D
  have hE : 0≤E := mul_nonneg (by norm_num) hd.datumEnergyNumber_nonneg
  have hD : 0≤D := by dsimp [D]; exact add_nonneg (add_nonneg pairCountConstant_pos.le (by positivity)) (by norm_num)
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨Cc*(K+2*pairCountConstant),mul_nonneg hCc (add_nonneg hK (mul_nonneg (by norm_num) pairCountConstant_pos.le)),?_⟩
  intro M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hJI hw hwP HZ
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
      if cappedRepresentative n.2/16384≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative n.2/16 then
        representativeRegularGoodCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)=
      ∑n∈U,(∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative n.2/16384≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative n.2/16 then
        representativeRegularGoodCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) := by
    simp [U,Finset.sum_filter,indicator_apply]
  rw [he]
  have hJn (n : ℕ×ℕ) : 0≤J n := representativeJointEnergy_nonneg ..
  have hbudget : ∑n∈U,J n≤E := (hJs.sum_le_tsum U (fun n _=>hJn n)).trans hJsum
  have hn := shared_radius_pair_sum hP hL (zero_le_one.trans hM) hA hI.le hw hwP hE U J
    (fun n _=>hJn n) hbudget (fun n hn=>hpair n (hU n hn))
  change (∑n∈U,Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2)≤
    K*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w) at hn
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  have hn2 := small_pair_I_source_sum (A:=A) hP hL hM hI.le hw hwP U
    (fun n hn=>hpair n (hU n hn))
  have hsum : (∑n∈U,(Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2+
      I*sourceRepresentative n.1))≤(K+2*pairCountConstant)*B := by
    rw [Finset.sum_add_distrib]
    calc
      _≤K*B+(2*pairCountConstant)*B := add_le_add hn hn2
      _=_ := by ring
  calc
    _≤∑n∈U,ENNReal.ofReal (Cc*(Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2+
        I*sourceRepresentative n.1)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hcentral M A P (zero_lt_one.trans_le hM) hA hP0 s T F hs hT hTT zX n.1 n.2 a b I w
        hzX ha hb hI hJI hw HZ
    _=ENNReal.ofReal (Cc*(∑n∈U,(Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2+
        I*sourceRepresentative n.1))) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun n _=>by
        exact mul_nonneg hCc (add_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg I) (hR n).le) (hp _).le) (cappedRepresentative_pos _).le)
          (mul_nonneg hI.le (hp _).le)))]
      congr 1
      exact (Finset.mul_sum ..).symm
    _≤_ := ENNReal.ofReal_le_ofReal (by
      have hh := mul_le_mul_of_nonneg_left hsum hCc
      simpa only [B, mul_assoc] using hh)

lemma Admissible.representative_good_near {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ → ∀(zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I →
      representativeGoodCost s F zX w k a b ≤
        ENNReal.ofReal (C*(I*Real.sqrt (cappedRepresentative (k 3))*(sourceRepresentative (k 0))^2*
          (cappedRepresentative (k 2))^2)) := by
  obtain ⟨Cd,hCd,hmag⟩ := hd.representative_good_Cauchy
  let E := datumEnergyNumber d
  have hE : 0≤E := hd.datumEnergyNumber_nonneg
  refine ⟨128*Cd*Real.sqrt 15360*Real.sqrt E*Real.sqrt (max 1 T₀),by positivity,?_⟩
  intro s T F hs hT hTT zX k a b I w ha hb hI hab
  have hm := hmag s T F hs hT zX k a b I w ha hb hI hab
  dsimp only at hm
  have hp : 0<sourceRepresentative (k 0) := by dsimp [sourceRepresentative]; positivity
  have hθ := cappedRepresentative_pos (k 1)
  have hφ := cappedRepresentative_pos (k 2)
  have hh := cappedRepresentative_pos (k 3)
  have hH : 0 ≤ max 1 T := zero_le_one.trans (le_max_left _ _)
  apply hm.trans
  apply le_trans _ (le_of_eq (direct_good_near_ennreal hCd hI.le hE hH hh.le hφ.le hp hθ)) |>.trans
  · apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (max_le_max le_rfl hTT)) (by positivity)
  · apply mul_le_mul' le_rfl
    apply mul_le_mul' le_rfl
    exact ENNReal.rpow_le_rpow (min_le_left _ _) (by norm_num)

noncomputable def representativeLowShortGoodCost {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (I w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ := by
  classical
  exact if cappedRepresentative (k 2)≤512/min (sourceRepresentative (k 0)) w ∧
    cappedRepresentative (k 3)≤I then representativeGoodCost s F zX w k a b else 0

lemma good_low_coefficient {P p w : ℝ} (hP : 1≤P) (hp : 1≤p)
    (hpP : p≤P) (hw : 1≤w) (hwP : w≤P) :
    p^2*(512/min p w)^2≤512^2*P^2/w := by
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hp0 : 0<p := zero_lt_one.trans_le hp
  have hw0 : 0<w := zero_lt_one.trans_le hw
  have hP2 : P≤P^2 := by nlinarith only [hP,sq_nonneg (P-1)]
  rcases le_total p w with hpw|hwp
  · rw [min_eq_left hpw]
    have he : p^2*(512/p)^2=512^2 := by field_simp
    rw [he]
    apply (le_div_iff₀ hw0).mpr
    exact mul_le_mul_of_nonneg_left (hwP.trans hP2) (by norm_num)
  · rw [min_eq_right hwp]
    have hww : w≤w^2 := by nlinarith only [hw,sq_nonneg (w-1)]
    calc
      _≤P^2*(512/w)^2 := mul_le_mul_of_nonneg_right (sq_le_sq₀ hp0.le hP0.le |>.mpr hpP) (by positivity)
      _=512^2*(P^2/w^2) := by ring
      _≤512^2*(P^2/w) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (sq_nonneg _) hw0 hww) (by norm_num)
      _=_ := by ring

lemma Admissible.representative_low_good_structural_triple_sum {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (np : ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I → 0<w →
      (∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative nf/16384≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative nf/16 then
          representativeLowShortGoodCost s F zX I w ![np,nt,nf,nr] a b else 0)≤
        ENNReal.ofReal (C*I*Real.sqrt I*(sourceRepresentative np)^2*(512/min (sourceRepresentative np) w)^2) := by
  classical
  obtain ⟨Cn,hCn,hnear⟩ := hd.representative_good_near T₀
  let K := (1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹
  have hK : 0<K := majorant_shortSqrtConstant_pos
  refine ⟨65536*Cn*K,by positivity,?_⟩
  intro s T F hs hT hTT zX np a b I w ha hb hI hJI hw
  let p := sourceRepresentative np
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  let G := fun nf nt=>∑'nr : ℕ,representativeLowShortGoodCost s F zX I w ![np,nt,nf,nr] a b
  have hr (nf nt : ℕ) : G nf nt≤ENNReal.ofReal
      (Cn*(I*p^2*(cappedRepresentative nf)^2)*K*Real.sqrt I) := by
    have he (nr : ℕ) : representativeLowShortGoodCost s F zX I w ![np,nt,nf,nr] a b≤
        if cappedRepresentative nr≤I then
          ENNReal.ofReal ((Cn*I*p^2*(cappedRepresentative nf)^2)*Real.sqrt (cappedRepresentative nr)) else 0 := by
      unfold representativeLowShortGoodCost
      change (if cappedRepresentative nf≤512/min p w ∧ cappedRepresentative nr≤I then _ else 0)≤_
      by_cases hh : cappedRepresentative nr≤I
      · rw [ite_eq_left hh]
        split_ifs with hl
        · apply (hnear s T F hs hT hTT zX ![np,nt,nf,nr] a b I w ha hb hI hJI).trans_eq
          congr 1
          dsimp only [Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons]
          dsimp [p]
          ring
        · exact bot_le
      · rw [ite_eq_right hh,ite_eq_right (fun hc=>hh hc.2)]
    apply (ENNReal.tsum_le_tsum he).trans
    have hh := majorant_capped_short_sqrt_radius_sum (by norm_num : (0:ℝ)<1) hI
      (K:=Cn*I*p^2*(cappedRepresentative nf)^2) (by positivity)
    simp only [one_mul] at hh
    apply hh.trans_eq
    congr 1
    dsimp [K]
    ring
  have hf (nf : ℕ) :
      (∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative nf/16384≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative nf/16 then
        representativeLowShortGoodCost s F zX I w ![np,nt,nf,nr] a b else 0)≤
      if cappedRepresentative nf≤512/min p w then
        ENNReal.ofReal (32768*Cn*K*I*Real.sqrt I*p^2*(cappedRepresentative nf)^2) else 0 := by
    by_cases hl : cappedRepresentative nf≤512/min p w
    · rw [ite_eq_left hl]
      have he (nt : ℕ) : (∑'nr : ℕ,if cappedRepresentative nf/16384≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative nf/16 then
          representativeLowShortGoodCost s F zX I w ![np,nt,nf,nr] a b else 0)=
          if cappedRepresentative nf/16384≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative nf/16 then G nf nt else 0 := by
        split_ifs <;> simp [G]
      simp_rw [he]
      apply (structural_angle_tsum_le (cappedRepresentative_pos nf) (by positivity) (G nf) (fun nt _ _=>hr nf nt)).trans_eq
      congr 1
      ring
    · rw [ite_eq_right hl]
      have hz (nt nr : ℕ) : representativeLowShortGoodCost s F zX I w ![np,nt,nf,nr] a b=0 := by
        change (if cappedRepresentative nf≤512/min p w ∧ cappedRepresentative nr≤I then _ else 0)=0
        exact ite_eq_right (fun hh=>hl hh.1)
      simp only [hz,ite_self,tsum_zero,le_refl]
  apply (ENNReal.tsum_le_tsum hf).trans
  have hC : 0≤32768*Cn*K*I*Real.sqrt I*p^2 := by positivity
  calc
    _=ENNReal.ofReal (32768*Cn*K*I*Real.sqrt I*p^2)*
      (∑'nf : ℕ,ENNReal.ofReal (if cappedRepresentative nf≤512/min p w then (cappedRepresentative nf)^2 else 0)) := by
      rw [←ENNReal.tsum_mul_left]
      apply tsum_congr
      intro nf
      split_ifs <;> simp [←ENNReal.ofReal_mul hC]
    _≤ENNReal.ofReal (32768*Cn*K*I*Real.sqrt I*p^2)*ENNReal.ofReal (2*(512/min p w)^2) :=
      mul_le_mul' le_rfl (capped_square_tail_sum (by positivity))
    _=_ := by rw [←ENNReal.ofReal_mul hC]; congr 1; ring

lemma Admissible.good_low_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ P : ℝ,1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      0≤a → b≤T → 0<I → I≤1 → b-a≤I → 1≤w → w≤P →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative n.2/16384≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative n.2/16 then
          representativeLowShortGoodCost s F zX I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*(I*P^2*Real.log (2+P)/w)) := by
  classical
  obtain ⟨Cn,hCn,hnear⟩ := hd.representative_low_good_structural_triple_sum T₀
  have hpc := pairCountConstant_pos
  refine ⟨512^2*Cn*pairCountConstant,by positivity,?_⟩
  intro P hP hL s T F hs hT hTT zX a b I w ha hb hI hI1 hJI hw hwP
  dsimp only
  let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
    1/sourceRepresentative n.1≤cappedRepresentative n.2}
  let g := fun np=>∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
    if cappedRepresentative nf/16384≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative nf/16 then
      representativeLowShortGoodCost s F zX I w ![np,nt,nf,nr] a b else 0
  let D := 512^2*Cn*I*P^2/w
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hw0 : 0<w := zero_lt_one.trans_le hw
  have hD : 0≤D := by dsimp [D]; positivity
  have hgb (np : ℕ) (hn : sourceRepresentative np≤P) : g np≤ENNReal.ofReal D := by
    apply (hnear s T F hs hT hTT zX np a b I w ha hb hI hJI hw0).trans
    apply ENNReal.ofReal_le_ofReal
    have hh := mul_le_mul_of_nonneg_left
      (good_low_coefficient hP (sourceRepresentative_one_le _) hn hw hwP)
      (by positivity : 0≤Cn*I*Real.sqrt I)
    have hsqrt : Real.sqrt I≤1 := (Real.sqrt_le_one).mpr hI1
    calc
      _=(Cn*I*Real.sqrt I)*((sourceRepresentative np)^2*(512/min (sourceRepresentative np) w)^2) := by ring
      _≤(Cn*I*Real.sqrt I)*(512^2*P^2/w) := hh
      _≤(Cn*I*1)*(512^2*P^2/w) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsqrt (by positivity)) (by positivity)
      _=D := by dsimp [D]; ring
  have hdom : (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
      if cappedRepresentative n.2/16384≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative n.2/16 then
        representativeLowShortGoodCost s F zX I w ![n.1,nt,n.2,nr] a b else 0) n)≤
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
  obtain ⟨N,hN,hidx⟩ := exists_small_pair_count hP hL
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun np=>sourceRepresentative np≤P)
  have hU (np) (hn : np∈U) : sourceRepresentative np≤P := (Finset.mem_filter.mp hn).2
  have hsub : U⊆Finset.range N := by
    intro np hn
    have hpn : 1/sourceRepresentative np≤cappedRepresentative 0 := by
      rw [show cappedRepresentative 0=1 by rfl]
      exact (div_le_one (zero_lt_one.trans_le (sourceRepresentative_one_le _))).mpr (sourceRepresentative_one_le _)
    exact Finset.mem_range.mpr (hidx np 0 (hU np hn) hpn).1
  have hcard : (U.card:ℝ)≤pairCountConstant*Real.log (2+P) := by
    have hh : (U.card:ℝ)≤N := by exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range N)
    exact hh.trans hN
  have he : (∑np∈S,if sourceRepresentative np≤P then g np else 0)=∑np∈U,g np := by
    simp [U,Finset.sum_filter]
  rw [he]
  calc
    _≤∑np∈U,ENNReal.ofReal D := Finset.sum_le_sum (fun np hn=>hgb np (hU np hn))
    _=ENNReal.ofReal ((U.card:ℝ)*D) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _=>hD)]
      simp
    _≤ENNReal.ofReal ((pairCountConstant*Real.log (2+P))*D) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hD)
    _=_ := by congr 1; dsimp [D]; ring

lemma Admissible.good_structural_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,1≤M → 0≤A → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → I≤1 → b-a≤I → 1≤w → w≤P →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative n.2/16384≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative n.2/16 then
          representativeGoodCost s F zX w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  classical
  obtain ⟨Cr,hCr,hregular⟩ := hd.good_regular_structural_uniform T₀
  obtain ⟨Ce,hCe,hexception⟩ := hd.good_low_uniform T₀
  refine ⟨Cr+Ce,add_nonneg hCr hCe,?_⟩
  intro M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hI1 hJI hw hwP HZ
  dsimp only
  let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
    1/sourceRepresentative n.1≤cappedRepresentative n.2}
  let Gr := fun n : ℕ×ℕ=>∑'nt : ℕ,∑'nr : ℕ,
    if cappedRepresentative n.2/16384≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative n.2/16 then
      representativeRegularGoodCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0
  let Ge := fun n : ℕ×ℕ=>∑'nt : ℕ,∑'nr : ℕ,
    if cappedRepresentative n.2/16384≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative n.2/16 then
      representativeLowShortGoodCost s F zX I w ![n.1,nt,n.2,nr] a b else 0
  have he (n : ℕ×ℕ) : Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
      if cappedRepresentative n.2/16384≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative n.2/16 then
        representativeGoodCost s F zX w ![n.1,nt,n.2,nr] a b else 0) n≤
      Q.indicator Gr n+Q.indicator Ge n := by
    by_cases hn : n∈Q
    · simp only [indicator_of_mem hn,Gr,Ge]
      rw [←ENNReal.tsum_add]
      apply ENNReal.tsum_le_tsum
      intro nt
      rw [←ENNReal.tsum_add]
      apply ENNReal.tsum_le_tsum
      intro nr
      by_cases ht : cappedRepresentative n.2/16384≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative n.2/16
      · simp only [ite_eq_left ht]
        by_cases hreg : regularCentralIndex P M A I w ![n.1,nt,n.2,nr]
        · have he : representativeRegularGoodCost s F zX P M A I w ![n.1,nt,n.2,nr] a b=
              representativeGoodCost s F zX w ![n.1,nt,n.2,nr] a b := ite_eq_left hreg
          rw [he]
          exact le_add_right le_rfl
        · have hh : ¬(512/min (sourceRepresentative n.1) w<cappedRepresentative n.2 ∨
              min I (stabilityLength P 16384 M A (sourceRepresentative n.1) w (cappedRepresentative n.2))<cappedRepresentative nr) := hreg
          have hlow : cappedRepresentative n.2≤512/min (sourceRepresentative n.1) w :=
            le_of_not_gt (not_or.mp hh).1
          have hr : cappedRepresentative nr≤I := (le_of_not_gt (not_or.mp hh).2).trans (min_le_left ..)
          have he : representativeLowShortGoodCost s F zX I w ![n.1,nt,n.2,nr] a b=
              representativeGoodCost s F zX w ![n.1,nt,n.2,nr] a b := ite_eq_left ⟨hlow,hr⟩
          rw [he]
          exact le_add_left le_rfl
      · simp only [ite_eq_right ht,zero_add,le_refl]
    · simp only [indicator_of_notMem hn,zero_add,le_refl]
  change (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
    if cappedRepresentative n.2/16384≤cappedRepresentative nt ∧ cappedRepresentative nt≤cappedRepresentative n.2/16 then
      representativeGoodCost s F zX w ![n.1,nt,n.2,nr] a b else 0) n)≤_
  apply (ENNReal.tsum_le_tsum he).trans
  rw [ENNReal.tsum_add]
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  let V := I*P^2*Real.log (2+P)/w
  have hV : 0≤V := by dsimp [V]; positivity
  have hB : 0≤B := by dsimp [B]; positivity
  have hVB : V≤B := by
    have hroot := Real.sqrt_nonneg A
    have hfirst : 0≤P*Real.sqrt I := by positivity
    have ht : V≤(M+Real.sqrt A)*V := le_mul_of_one_le_left hV (by linarith)
    calc
      V≤(M+Real.sqrt A)*V := ht
      _≤P*Real.sqrt I+(M+Real.sqrt A)*V := le_add_of_nonneg_left hfirst
      _=B := by dsimp [B,V]; ring
  have hr := hregular M A P hM hA hP hL s T F hs hT hTT
    zX a b I w hzX ha hb hI hJI (zero_lt_one.trans_le hw) hwP HZ
  have he' := hexception P hP hL s T F hs hT hTT zX a b I w ha hb hI hI1 hJI hw hwP
  calc
    _≤ENNReal.ofReal (Cr*B)+ENNReal.ofReal (Ce*V) := add_le_add hr he'
    _≤ENNReal.ofReal (Cr*B)+ENNReal.ofReal (Ce*B) :=
      add_le_add le_rfl (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hVB hCe))
    _=ENNReal.ofReal ((Cr+Ce)*B) := by rw [←ENNReal.ofReal_add (mul_nonneg hCr hB) (mul_nonneg hCe hB)]; congr 1; ring

lemma crossing_bound_normalised {n D α : ℝ} (hn : 0<n) (hD : 0<D)
    (hα : 0<α) :
    min (2*(D^2/n))
      (dyadicBalanceConstant α 1*(n^(1/(α+1))*(D^2/n)^(α/(α+1))))≤
      (2+dyadicBalanceConstant α 1)*D*
        min ((n/D)^((1-α)/(1+α))) ((n/D)^(-1:ℝ)) := by
  have hC := dyadicBalanceConstant_pos hα (by norm_num : (0:ℝ)<1)
  have he : D^2/n=D*(n/D)^(-1:ℝ) := by rw [Real.rpow_neg_one,inv_div]; ring
  rw [crossing_normalisation hn hD hα,
    mul_min_of_nonneg _ _ (by positivity : 0≤(2+dyadicBalanceConstant α 1)*D)]
  apply le_min
  · apply (min_le_right _ _).trans
    have hn0 : 0≤D*(n/D)^((1-α)/(1+α)) := by positivity
    nlinarith only [mul_nonneg (by norm_num : (0:ℝ)≤2) hn0]
  · apply (min_le_left _ _).trans
    rw [he]
    have hn0 : 0≤D*(n/D)^(-1:ℝ) := by positivity
    nlinarith only [mul_nonneg hC.le hn0]

lemma scaled_capped_crossing_normalised {n D x α : ℝ} (hn : 0<n) (hD : 0<D)
    (hx : 0<x) (hα : 0<α) :
    (∑'j : ℕ,if x≤cappedRepresentative j then
      ENNReal.ofReal (min (n*(cappedRepresentative j/x)^α)
        ((D^2/n)*(cappedRepresentative j/x)^(-1:ℝ))) else 0)≤
      ENNReal.ofReal ((2+dyadicBalanceConstant α 1)*D*
        min ((n/D)^((1-α)/(1+α))) ((n/D)^(-1:ℝ))) :=
  (scaled_capped_crossing_sum hn (div_pos (sq_pos_of_pos hD) hn) hx hα).trans
    (ENNReal.ofReal_le_ofReal (crossing_bound_normalised hn hD hα))

lemma scaled_two_level_crossing_sum {N D α γ : ℝ} (hN : 0<N) (hD : 0<D)
    (hα : 0<α) (hα1 : α<1) (hγ : 0<γ) (x : ℕ→ℝ) (hx : ∀j,0<x j) :
    (∑'nt : ℕ,∑'nr : ℕ,if x nt≤cappedRepresentative nr then
      ENNReal.ofReal (min ((N*(cappedRepresentative nt)^γ)*(cappedRepresentative nr/x nt)^α)
        ((D^2/(N*(cappedRepresentative nt)^γ))*(cappedRepresentative nr/x nt)^(-1:ℝ)))
      else 0)≤
      ENNReal.ofReal ((2+dyadicBalanceConstant α 1)*D*
        dyadicBalanceConstant (γ*((1-α)/(1+α))) γ) := by
  let q : ℝ := (1-α)/(1+α)
  let K : ℝ := (2+dyadicBalanceConstant α 1)*D
  have hq : 0<q := div_pos (sub_pos.mpr hα1) (by linarith)
  have hK : 0≤K := by dsimp [K]; positivity [dyadicBalanceConstant_pos hα (by norm_num : (0:ℝ)<1)]
  let g : ℤ→ℝ := fun k=>min (((N/D)*((2:ℝ)^k)^γ)^q) (((N/D)*((2:ℝ)^k)^γ)^(-1:ℝ))
  have hg := angular_crossing_sum (div_pos hN hD) hγ hq
  have hg0 (k : ℤ) : 0≤g k := by dsimp [g]; positivity
  have he (j : ℕ) : cappedRepresentative j=(2:ℝ)^(-(j:ℤ)) := by
    simp only [cappedRepresentative,zpow_neg,zpow_natCast,inv_pow]
  have hi : Function.Injective (fun j : ℕ=>-(j:ℤ)) := by
    intro a b hab
    exact_mod_cast neg_injective hab
  calc
    _≤∑'nt : ℕ,ENNReal.ofReal K*ENNReal.ofReal (g (-(nt:ℤ))) := by
      apply ENNReal.tsum_le_tsum
      intro nt
      have hb := scaled_capped_crossing_normalised
        (mul_pos hN (Real.rpow_pos_of_pos (cappedRepresentative_pos nt) γ)) hD (hx nt) hα
      apply hb.trans_eq
      rw [←ENNReal.ofReal_mul hK]
      congr 1
      dsimp [K,g,q]
      rw [he]
      congr 2 <;> congr 1 <;> ring
    _=ENNReal.ofReal K*(∑'nt : ℕ,ENNReal.ofReal (g (-(nt:ℤ)))) := ENNReal.tsum_mul_left
    _≤ENNReal.ofReal K*(∑'k : ℤ,ENNReal.ofReal (g k)) :=
      mul_le_mul' le_rfl (ENNReal.tsum_comp_le_tsum_of_injective hi (fun index => ENNReal.ofReal (g index)))
    _=ENNReal.ofReal K*ENNReal.ofReal (∑'k : ℤ,g k) := by
      rw [ENNReal.ofReal_tsum_of_nonneg hg0 hg.1]
    _≤ENNReal.ofReal K*ENNReal.ofReal (dyadicBalanceConstant (γ*q) γ) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hg.2)
    _=_ := by rw [←ENNReal.ofReal_mul hK]

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma spatial_crossing_scale {b α θ : ℝ} (hb : 0<b) (hα : α<1) (hθ : 0<θ) :
    (b^(1/(1-α))*θ^(-α/(1-α)))^(1-α)=b*θ^(-α) := by
  rw [Real.mul_rpow (Real.rpow_pos_of_pos hb _).le (Real.rpow_pos_of_pos hθ _).le,
    ←Real.rpow_mul hb.le,←Real.rpow_mul hθ.le]
  have hne : (1-α)≠0 := by linarith
  rw [show (1/(1-α))*(1-α)=1 by field_simp,
    show (-α/(1-α))*(1-α) = -α by field_simp,Real.rpow_one]

lemma spatial_crossing_normalisation {a b c α θ h : ℝ}
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hα : α<1) (hθ : 0<θ) (hh : 0<h) :
    let H := b^(1/(1-α))
    let x := H*θ^(-α/(1-α))
    let N := a*H/b
    let γ := (1-2*α)/(1-α)
    let D := Real.sqrt (a*c/b)
    (N*θ^γ)*(h/x)^α=a*θ^(1-α)*h^α ∧
    (D^2/(N*θ^γ))*(h/x)^(-1:ℝ)=c/(θ*h) := by
  dsimp only
  let H := b^(1/(1-α))
  let δ := -α/(1-α)
  let x := H*θ^δ
  let γ := (1-2*α)/(1-α)
  have hH : 0<H := Real.rpow_pos_of_pos hb _
  have hx : 0<x := mul_pos hH (Real.rpow_pos_of_pos hθ _)
  have hne : (1-α)≠0 := by linarith
  have hγ : γ=1+δ := by dsimp [γ,δ]; field_simp; ring
  have hn : (a*H/b)*θ^γ=(a/b)*θ*x := by
    rw [hγ,Real.rpow_add hθ,Real.rpow_one]
    dsimp [x]
    ring
  have hs : x^(1-α)=b*θ^(-α) := spatial_crossing_scale hb hα hθ
  have hxa : x=x^α*(b*θ^(-α)) := by
    rw [←hs,←Real.rpow_add hx,show α+(1-α)=1 by ring,Real.rpow_one]
  have hθa : θ*θ^(-α)=θ^(1-α) := by
    calc
      _=θ^(1:ℝ)*θ^(-α) := by rw [Real.rpow_one]
      _=θ^(1-α) := by rw [←Real.rpow_add hθ]; congr 1
  change ((a*H/b)*θ^γ)*(h/x)^α=_ ∧ _
  rw [hn]
  constructor
  · rw [Real.div_rpow hh.le hx.le]
    calc
      _=(a/b)*θ*(x^α*(b*θ^(-α)))*(h^α/x^α) := by rw [←hxa]
      _=a*(θ*θ^(-α))*h^α := by field_simp
      _=_ := by rw [hθa]
  · rw [Real.sq_sqrt (by positivity : 0≤a*c/b),Real.rpow_neg_one]
    change ((a*c/b)/((a/b)*θ*x))*(h/x)⁻¹=c/(θ*h)
    field_simp

lemma spatial_transition_double_sum {a b c α : ℝ}
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hα : 0<α) (hα2 : α<1/2) :
    let γ := (1-2*α)/(1-α)
    (∑'nt : ℕ,∑'nr : ℕ,
      if b*(cappedRepresentative nt)^(-α)≤(cappedRepresentative nr)^(1-α) then
        ENNReal.ofReal (min (a*(cappedRepresentative nt)^(1-α)*(cappedRepresentative nr)^α)
          (c/(cappedRepresentative nt*cappedRepresentative nr))) else 0)≤
      ENNReal.ofReal ((2+dyadicBalanceConstant α 1)*Real.sqrt (a*c/b)*
        dyadicBalanceConstant (γ*((1-α)/(1+α))) γ) := by
  dsimp only
  have hα1 : α<1 := by linarith
  have hβ : 0<1-α := by linarith
  let H := b^(1/(1-α))
  let x := fun nt=>H*(cappedRepresentative nt)^(-α/(1-α))
  let N := a*H/b
  let D := Real.sqrt (a*c/b)
  let γ := (1-2*α)/(1-α)
  have hH : 0<H := Real.rpow_pos_of_pos hb _
  have hx (j : ℕ) : 0<x j := mul_pos hH (Real.rpow_pos_of_pos (cappedRepresentative_pos j) _)
  have hN : 0<N := div_pos (mul_pos ha hH) hb
  have hD : 0<D := Real.sqrt_pos.mpr (by positivity)
  have hγ : 0<γ := div_pos (by linarith) hβ
  have hbound := scaled_two_level_crossing_sum hN hD hα hα1 hγ x hx
  apply le_of_eq_of_le _ hbound
  apply tsum_congr
  intro nt
  apply tsum_congr
  intro nr
  have hs := spatial_crossing_scale hb hα1 (cappedRepresentative_pos nt)
  change (x nt)^(1-α)=b*(cappedRepresentative nt)^(-α) at hs
  have he : (b*(cappedRepresentative nt)^(-α)≤(cappedRepresentative nr)^(1-α)) ↔
      x nt≤cappedRepresentative nr := by
    rw [←hs,Real.rpow_le_rpow_iff (hx nt).le (cappedRepresentative_pos nr).le hβ]
  simp only [he]
  split_ifs
  · have hn := spatial_crossing_normalisation ha hb hc hα1
      (cappedRepresentative_pos nt) (cappedRepresentative_pos nr)
    rw [hn.1,hn.2]
  · rfl

end RVM

end

end OAI
