import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.ConformalRestartMap

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEKernel

lemma target_cap_cancellation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ℝ) (hα : 0≤α) (cap target : ι→ℝ)
    (hc : ∀i,0<cap i) (ht : ∀i,0<target i) :
    (∏i,target i^(-α))*(∏i∈Finset.univ.filter (fun i => target i≤cap i),
      (target i/cap i)^α) ≤ ∏i,cap i^(-α) := by
  rw [Finset.prod_filter,←Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro i _
    apply mul_nonneg (Real.rpow_nonneg (ht i).le _)
    split_ifs
    · exact Real.rpow_nonneg (div_nonneg (ht i).le (hc i).le) _
    · norm_num
  · intro i _
    by_cases hi : target i≤cap i
    · rw [ite_eq_left hi,Real.div_rpow (ht i).le (hc i).le,
        Real.rpow_neg (ht i).le,Real.rpow_neg (hc i).le]
      have hp := Real.rpow_pos_of_pos (ht i) α
      field_simp
      rfl
    · rw [ite_eq_right hi,mul_one]
      exact Real.rpow_le_rpow_of_nonpos (hc i) (le_of_not_ge hi) (neg_nonpos.mpr hα)

 

theorem actual_hit_density_product_bound (a : ℝ) (ha : 1/4<a) (m : ℕ) :
    ∃C : ℝ, 0<C ∧ ∀(W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W],
      IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W →
      ∀z : Fin (m+1)→ℂ, Function.Injective z → (∀i,0<(z i).im) →
      ∀cap target : Fin (m+1)→ℝ,
        (∀i,0<cap i ∧ cap i≤2*(z i).im) →
        (∀i j,i≠j → cap i≤‖z i-z j‖) →
        (∀i,0<target i ∧ target i≤2*(z i).im) →
        (∫⁻b in {b | radialTime a b.1 (z 0) (target 0/2)<∞},
          ∏i : Fin m, ENNReal.ofReal (fullRadialDensity a b.1 (z i.succ) (target i.succ))∂W) ≤
          ENNReal.ofReal (C*(target 0)^(alpha a)*(∏i,cap i^(-alpha a))) := by
  obtain ⟨C,hC,hCb⟩ := selective_hit_bound a ha (m+1)
  refine ⟨C,hC,?_⟩
  intro W hprob hW z hinj hz cap target hc hsep ht
  let I := Finset.univ.filter (fun i => target i≤cap i)
  let E := {b : ExactSLEGenerator.Driver | ∀i∈I,radialTime a b.1 (z i) (target i/2)<∞}
  let E₀ := {b : ExactSLEGenerator.Driver | radialTime a b.1 (z 0) (target 0/2)<∞}
  let A := ∏i : Fin m, (target i.succ)^(-alpha a)
  have hA : 0≤A := Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (ht _).1.le _)
  have hhit : W E≤ENNReal.ofReal (C*∏i∈I,(target i/cap i)^(alpha a)) :=
    hCb W hW z hinj hz cap target hc hsep I
      (fun i hi => ⟨(ht i).1,(Finset.mem_filter.mp hi).2⟩)
  have hS := radialTime_stopping a (lt_trans (by norm_num) ha) (z 0) (hz 0)
      (target 0/2) (by have := (ht 0).1; positivity) (by have := (ht 0).2; linarith)
  have hE₀ : MeasurableSet E₀ := hS.measurableSpace_le _ (hS.measurable measurableSet_Iio)
  have hpoint (b : ExactSLEGenerator.Driver) :
      E₀.indicator (fun b => ∏i : Fin m,
        ENNReal.ofReal (fullRadialDensity a b.1 (z i.succ) (target i.succ))) b ≤
      E.indicator (fun _ => ENNReal.ofReal A) b := by
    by_cases h0 : b∈E₀
    · rw [Set.indicator_of_mem h0]
      by_cases hb : b∈E
      · rw [Set.indicator_of_mem hb,ENNReal.ofReal_prod_of_nonneg
          (fun i _ => Real.rpow_nonneg (ht i.succ).1.le _)]
        exact Finset.prod_le_prod₀ (fun _ _ => bot_le) (fun i _ => ENNReal.ofReal_le_ofReal
          (fullRadialDensity_bound a ha (z i.succ) (hz _) (target i.succ)
            (ht _).1 (ht _).2 b).2)
      · rw [Set.indicator_of_notMem hb]
        have he : ∃i∈I,radialTime a b.1 (z i) (target i/2)=∞ := by
          by_contra hn
          apply hb
          intro i hi
          exact lt_top_iff_ne_top.mpr (fun he => hn ⟨i,hi,he⟩)
        obtain ⟨i,hi,he⟩ := he
        have hi0 : i≠0 := by
          intro h
          subst i
          exact (ne_of_lt (show radialTime a b.1 (z 0) (target 0/2)<∞ from h0)) he
        obtain ⟨j,rfl⟩ := Fin.exists_succ_eq.mpr hi0
        have hj : ENNReal.ofReal (fullRadialDensity a b.1 (z j.succ) (target j.succ))=0 := by
          simp [fullRadialDensity,radialWeight,he]
        exact le_of_eq (Finset.prod_eq_zero (Finset.mem_univ j) hj)
    · rw [Set.indicator_of_notMem h0]
      exact bot_le
  have halg : A*(∏i∈I,(target i/cap i)^(alpha a)) ≤
      (target 0)^(alpha a)*∏i,cap i^(-alpha a) := by
    have he : A=(target 0)^(alpha a)*(∏i,target i^(-alpha a)) := by
      rw [Fin.prod_univ_succ,←mul_assoc,←Real.rpow_add (ht 0).1]
      simp only [add_neg_cancel,Real.rpow_zero,one_mul,A]
    rw [he,mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (target_cap_cancellation (alpha a) (alpha_pos ha).le cap target
        (fun i => (hc i).1) (fun i => (ht i).1))
      (Real.rpow_nonneg (ht 0).1.le _)
  calc
    _ = ∫⁻b,E₀.indicator (fun b => ∏i : Fin m,
        ENNReal.ofReal (fullRadialDensity a b.1 (z i.succ) (target i.succ))) b∂W :=
      (lintegral_indicator hE₀ _).symm
    _ ≤ ∫⁻b,E.indicator (fun _ => ENNReal.ofReal A) b∂W := lintegral_mono hpoint
    _ ≤ ENNReal.ofReal A*W E := lintegral_indicator_const_le E _
    _ ≤ ENNReal.ofReal A*ENNReal.ofReal (C*∏i∈I,(target i/cap i)^(alpha a)) :=
      mul_le_mul' le_rfl hhit
    _ = ENNReal.ofReal (C*(A*∏i∈I,(target i/cap i)^(alpha a))) := by
      rw [←ENNReal.ofReal_mul hA]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [mul_le_mul_of_nonneg_left halg hC.le])

end ExactSLEGreen
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEKernel

 

theorem actual_hit_mass_moment_bound (a : ℝ) (ha : 1/4<a) (m : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀(W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W],
      IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W →
      ∀K : Set ℂ, MeasurableSet K → Bornology.IsBounded K →
      ∀c : ℝ, 0<c → (∀x∈K,c≤2*x.im) →
      ∀z : ℂ, c≤2*z.im →
      ∀f : ℂ→ℝ, Measurable f → (∀x∈K,0≤f x) →
      (∃B : ℝ,0≤B ∧ ∀x∈K,f x≤B) →
      let A := ∫⁻x : Fin m→ℂ, (∏i,ENNReal.ofReal (f (x i)))*
        kernel (alpha a) c (Fin.cons z x)∂Measure.pi (fun _ => volume.restrict K)
      A<∞ ∧ ∀ρ : ℝ, 0<ρ → ρ≤z.im → ∀q : ℝ,0<q → q≤1 →
        (∫⁻b in {b | radialTime a b.1 z ρ<∞},
          (∫⁻x in K, ENNReal.ofReal (f x)*massDensity a q b x)^m∂W) ≤
          ENNReal.ofReal (C*(2*ρ)^(alpha a))*A := by
  obtain ⟨C,hC,hCb⟩ := actual_hit_density_product_bound a ha m
  refine ⟨C,hC,?_⟩
  intro W hprob hW K hK hKb c hc hcK z hzc f hf hf0 hfB
  obtain ⟨B,hB,hBf⟩ := hfB
  let μ := volume.restrict K
  let ν := Measure.pi (fun _ : Fin m => μ)
  have hKae : ∀ᵐ x∂ν,∀i,x i∈K := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ:=fun _ : Fin m=>μ) (i:=i)).eventually
      (ae_restrict_mem hK)
  have halpha : alpha a<1 := by
    have ha0 : 0<a := by linarith
    have hp : 0<1/(4*a) := by positivity
    dsimp [alpha]; linarith
  obtain ⟨D,hD,hDb⟩ := capped_distance_fixed_center (alpha a) c (alpha_pos ha)
    halpha hc m K {z} hK hKb (isCompact_singleton.isBounded)
  have hkfin : (∫⁻x : Fin m→ℂ,kernel (alpha a) c (Fin.cons z x)∂ν)<∞ :=
    lt_of_le_of_lt (hDb z (mem_singleton z)) hD
  have hkm : Measurable (fun x : Fin m→ℂ => kernel (alpha a) c (Fin.cons z x)) :=
    (measurable_kernel (alpha_pos ha).le c).comp (by fun_prop)
  have hAfin : (∫⁻x,(∏i,ENNReal.ofReal (f (x i)))*kernel (alpha a) c
      (Fin.cons z x)∂ν)<∞ := by
    calc
      _ ≤ ∫⁻x,(ENNReal.ofReal B)^m*kernel (alpha a) c (Fin.cons z x)∂ν := by
        apply lintegral_mono_ae
        filter_upwards [hKae] with x hx
        apply mul_le_mul' _ le_rfl
        have hp := Finset.prod_le_prod₀ (fun _ _ => (bot_le : (0:ℝ≥0∞)≤_))
          (fun i (_ : i∈Finset.univ) => ENNReal.ofReal_le_ofReal (hBf (x i) (hx i)))
        simpa using hp
      _ = (ENNReal.ofReal B)^m*∫⁻x,kernel (alpha a) c (Fin.cons z x)∂ν :=
        lintegral_const_mul _ hkm
      _ < ∞ := ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hkfin
  refine ⟨hAfin,?_⟩
  intro ρ hρ hρz q hq hq1
  have hz : 0<z.im := by linarith
  let E := {b : ExactSLEGenerator.Driver | radialTime a b.1 z ρ<∞}
  have hd := massDensity_measurable a ha q hq hq1
  have hdz (b : ExactSLEGenerator.Driver) : Measurable (massDensity a q b) :=
    hd.comp (measurable_const.prodMk measurable_id)
  have hdm (x : Fin m→ℂ) : Measurable (fun b => ∏i,massDensity a q b (x i)) := by
    apply Finset.measurable_prod
    intro i hi
    exact hd.comp (measurable_id.prodMk measurable_const)
  have hprod (x : Fin m→ℂ) (hx : ∀i,x i∈K) :
      (∫⁻b in E,∏i,massDensity a q b (x i)∂W) ≤
        ENNReal.ofReal (C*(2*ρ)^(alpha a))*kernel (alpha a) c (Fin.cons z x) := by
    let Z : Fin (m+1)→ℂ := Fin.cons z x
    have hZ (i : Fin (m+1)) : 0<(Z i).im := by
      refine Fin.cases hz (fun j => ?_) i
      have := hcK (x j) (hx j)
      simp only [Z, Fin.cons_succ]
      linarith
    have hcz (i : Fin (m+1)) : c≤2*(Z i).im := by
      exact Fin.cases hzc (fun j => hcK (x j) (hx j)) i
    by_cases hinj : Function.Injective Z
    · let cap := fun i => cappedDistance c Z i
      let target : Fin (m+1)→ℝ := Fin.cons (2*ρ) (fun i => 2*(x i).im*q)
      have hcap (i) : 0<cap i := cappedDistance_pos hc Z hinj i
      have ht (i) : 0<target i ∧ target i≤2*(Z i).im := by
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [target, Z, Fin.cons_zero]
          constructor <;> linarith
        · simp only [target, Z, Fin.cons_succ]
          have hxi := hZ j.succ
          simp only [Z,Fin.cons_succ] at hxi
          constructor
          · positivity
          · nlinarith
      have hh := hCb W hW Z hinj hZ cap target
        (fun i => ⟨hcap i,(cappedDistance_le c Z i).trans (hcz i)⟩)
        (fun i j hij => by simpa [dist_eq_norm] using
          cappedDistance_le_dist c Z i j hij.symm) ht
      have he (b : ExactSLEGenerator.Driver) (i) : massDensity a q b (x i)=
          ENNReal.ofReal (fullRadialDensity a b.1 (Z i.succ) (target i.succ)) := by
        have hxi : 0 < (x i).im := by simpa [Z] using hZ i.succ
        simp [massDensity, hxi, Z, target]
      simp_rw [he]
      have hk : ENNReal.ofReal (C*(target 0)^(alpha a)*∏i,cap i^(-alpha a))=
          ENNReal.ofReal (C*(2*ρ)^(alpha a))*kernel (alpha a) c (Fin.cons z x) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hC.le (Real.rpow_nonneg (ht 0).1.le _)),
          ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (hcap i).le _)]
        congr 1
        unfold kernel
        apply Finset.prod_congr rfl
        intro i hi
        exact (ENNReal.ofReal_rpow_of_pos (hcap i)).symm
      simpa only [Z,target,Fin.cons_zero,mul_div_cancel_left₀ _ (two_ne_zero : (2:ℝ)≠0)]
        using hh.trans_eq hk
    · rw [kernel_top_of_not_injective (alpha a) c (alpha_pos ha) hc Z hinj,
        ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr
          (mul_pos hC (Real.rpow_pos_of_pos (by positivity) _))))]
      exact le_top
  have hjoint : Measurable (fun p : ExactSLEGenerator.Driver × (Fin m→ℂ) =>
      ∏i,ENNReal.ofReal (f (p.2 i))*massDensity a q p.1 (p.2 i)) := by
    apply Finset.measurable_prod
    intro i hi
    exact ((hf.comp ((measurable_pi_apply i).comp measurable_snd)).ennreal_ofReal).mul
      (hd.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  calc
    _ = ∫⁻b in E,∫⁻x : Fin m→ℂ,∏i,ENNReal.ofReal (f (x i))*massDensity a q b (x i)∂ν∂W := by
      apply lintegral_congr
      intro b
      exact lintegral_power_pi μ _ (hf.ennreal_ofReal.mul (hdz b)) m
    _ = ∫⁻x : Fin m→ℂ,∫⁻b in E,∏i,ENNReal.ofReal (f (x i))*massDensity a q b (x i)∂W∂ν :=
      lintegral_lintegral_swap hjoint.aemeasurable
    _ ≤ ∫⁻x,ENNReal.ofReal (C*(2*ρ)^(alpha a))*
        ((∏i,ENNReal.ofReal (f (x i)))*kernel (alpha a) c (Fin.cons z x))∂ν := by
      apply lintegral_mono_ae
      filter_upwards [hKae] with x hx
      simp_rw [Finset.prod_mul_distrib]
      rw [lintegral_const_mul _ (hdm x)]
      calc
        _ ≤ (∏i,ENNReal.ofReal (f (x i)))*
            (ENNReal.ofReal (C*(2*ρ)^(alpha a))*kernel (alpha a) c (Fin.cons z x)) :=
          mul_le_mul' le_rfl (hprod x hx)
        _ = _ := by ring
    _ = _ := by
      have hfm : Measurable (fun x : Fin m→ℂ => ∏i,ENNReal.ofReal (f (x i))) := by fun_prop
      exact lintegral_const_mul _ (hfm.mul hkm)

end ExactSLEGreen
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEKernel

lemma convex_limit_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (m : ℕ) (hm : 1 ≤ m) (A : ℝ≥0∞)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ)
    (hc : ∀k j,j∈s k→0≤c k j) (hsum : ∀k,∑j∈s k,c k j=1)
    (F : ℕ→Ω→ℝ) (hF : ∀j,AEStronglyMeasurable (F j) P)
    (hbound : ∀j,(∫⁻b,‖F j b‖ₑ^m∂P)≤A)
    (G : Ω→ℝ)
    (hlim : ∀ᵐ b∂P,Tendsto (fun k=>∑j∈s k,c k j*F j b) atTop (𝓝 (G b))) :
    (∫⁻b,‖G b‖ₑ^m∂P)≤A := by
  have hm0 : (m:ℝ)≠0 := by exact_mod_cast Nat.ne_zero_of_lt hm
  let D := A^(1/(m:ℝ))
  have hn (j) : eLpNorm (F j) (m:ℝ≥0∞) P≤D := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by exact_mod_cast Nat.ne_zero_of_lt hm) (by simp) (hF j),
      ENNReal.toReal_natCast]
    simpa only [ENNReal.rpow_natCast] using
      ENNReal.rpow_le_rpow (hbound j) (show (0:ℝ)≤1/(m:ℝ) by positivity)
  have hFn (k) : AEStronglyMeasurable (fun b=>∑j∈s k,c k j*F j b) P := by
    have h := Finset.aestronglyMeasurable_sum (μ:=P) (s k)
      (fun j hj => (hF j).const_mul (c k j))
    convert h using 1
    funext b
    simp only [Finset.sum_apply]
  have hnb (k) : eLpNorm (fun b=>∑j∈s k,c k j*F j b) (m:ℝ≥0∞) P≤D :=
    convex_eLpNorm_bound P _ D (by exact_mod_cast hm) (s k) (c k) (hc k) (hsum k)
      F (fun j _ => hF j) (fun j _ => hn j)
  have hGm := aestronglyMeasurable_of_tendsto_ae atTop hFn hlim
  have hg : eLpNorm G (m:ℝ≥0∞) P≤D :=
    Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall hnb) hFn hGm hlim
  have hid : (eLpNorm G (m:ℝ≥0∞) P)^m=∫⁻b,‖G b‖ₑ^m∂P := by
    simpa using (eLpNorm_nnreal_pow_eq_lintegral (f:=G) (μ:=P) (p:=(m:ℝ≥0))
      (by exact_mod_cast Nat.ne_zero_of_lt hm) hGm)
  rw [←hid]
  calc
    _ ≤ D^m := pow_le_pow_left' hg m
    _ = A := by
      dsimp [D]
      rw [←ENNReal.rpow_natCast,←ENNReal.rpow_mul,one_div_mul_cancel hm0,ENNReal.rpow_one]

 

theorem actual_hit_radon_moment_bound (a : ℝ) (ha : 1/4<a) (m : ℕ) (hm : 1 ≤ m) :
    ∃C : ℝ,0<C ∧ ∀(W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W],
      IsBrownianReal (fun t (b : ExactSLEGenerator.Driver)=>b.1 t) W →
      ∀f : C_c(UpperPlane,ℝ), ∀c : ℝ,0<c →
      (∀x∈tsupport f,c≤2*x.1.im) → ∀z : ℂ,c≤2*z.im →
      let A := ∫⁻x : Fin m→ℂ,(∏i,ENNReal.ofReal ‖upperExtension f (x i)‖)*
        kernel (alpha a) c (Fin.cons z x)∂Measure.pi
          (fun _ => volume.restrict (Subtype.val '' tsupport f))
      A<∞ ∧ ∀(s : ℕ→Finset ℕ) (coeff : ℕ→ℕ→ℝ),
      (∀k j,j∈s k→0≤coeff k j) → (∀k,∑j∈s k,coeff k j=1) →
      ∀(t : ℝ≥0∞) (μ : ExactSLEGenerator.Driver→Measure UpperPlane),
      (∀ᵐ b∂W,Tendsto (fun k=>∑j∈s k,coeff k j*
        ∫x,f x∂actualUpperMass a (Real.exp (-2*a*(j+1))) t b)
          atTop (𝓝 (∫x,f x∂μ b))) →
      ∀ρ : ℝ,0<ρ → ρ≤z.im →
        (∫⁻b in {b | radialTime a b.1 z ρ<∞},‖∫x,f x∂μ b‖ₑ^m∂W)≤
          ENNReal.ofReal (C*(2*ρ)^(alpha a))*A := by
  obtain ⟨C,hC,hCb⟩ := actual_hit_mass_moment_bound a ha m
  refine ⟨C,hC,?_⟩
  intro W hprob hW f c hc hcf z hzc
  let K := Subtype.val '' tsupport f
  have hK : IsCompact K := f.hasCompactSupport.image continuous_subtype_val
  have hcK (x : ℂ) (hx : x∈K) : c≤2*x.im := by
    obtain ⟨y,hy,rfl⟩ := hx
    exact hcf y hy
  obtain ⟨hAfin,hB⟩ := hCb W hW K hK.measurableSet hK.isBounded c hc hcK z hzc
    (fun x=>‖upperExtension f x‖) (upperExtension_measurable f).norm
    (fun _ _ => norm_nonneg _) (upperExtension_bounded f)
  refine ⟨hAfin,?_⟩
  intro s coeff hcoeff hsum t μ hlim ρ hρ hρz
  let E := {b : ExactSLEGenerator.Driver | radialTime a b.1 z ρ<∞}
  let q (j : ℕ) := Real.exp (-2*a*(j+1))
  have hq (j : ℕ) : 0<q j := Real.exp_pos _
  have hq1 (j : ℕ) : q j≤1 := by
    apply Real.exp_le_one_iff.mpr
    have ha0 : 0<a := by linarith
    have hj0 : (0:ℝ)≤j := Nat.cast_nonneg _
    nlinarith
  apply convex_limit_moment_bound (W.restrict E) m hm _ s coeff hcoeff hsum
    (fun j b=>∫x,f x∂actualUpperMass a (q j) t b)
    (fun j=>(actualUpperMass_eval_measurable a ha (q j) (hq j) (hq1 j) t f).aestronglyMeasurable.restrict)
    _ _ (ae_restrict_of_ae hlim)
  intro j
  calc
    _ ≤ ∫⁻b in E,(∫⁻x in K,ENNReal.ofReal ‖upperExtension f x‖*massDensity a (q j) b x)^m∂W := by
      apply lintegral_mono
      intro b
      dsimp only
      rw [actualUpperMass_eval a ha (q j) (hq j) (hq1 j)]
      exact pow_le_pow_left' (actualMassEval_enorm_bound a (q j) t K (upperExtension f) b) m
    _ ≤ _ := hB ρ hρ hρz (q j) (hq j) (hq1 j)

end ExactSLEGreen
end
end
 

 
section
 

noncomputable section
open MeasureTheory Set Filter Topology
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.KernelSimilarity
open ExactSLEKernel

 
def affine (x : ℂ) (y : ℝ) (hy : 0<y) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ (y:ℂ) (Complex.ofReal_ne_zero.mpr hy.ne')).trans
    (Homeomorph.addLeft x)

@[simp] lemma affine_apply (x : ℂ) {y : ℝ} (hy : 0<y) (z : ℂ) :
    affine x y hy z=x+(y:ℂ)*z := rfl

lemma dist_affine (x : ℂ) {y : ℝ} (hy : 0<y) (u v : ℂ) :
    dist (affine x y hy u) (affine x y hy v)=y*dist u v := by
  simp only [affine_apply,dist_eq_norm,add_sub_add_left_eq_sub,←mul_sub,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy]

lemma cappedDistance_affine {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ℂ) {y : ℝ} (hy : 0<y) (c : ℝ) (z : ι→ℂ) (i : ι) :
    cappedDistance (y*c) (affine x y hy ∘ z) i=y*cappedDistance c z i := by
  apply le_antisymm
  · rw [mul_comm y (cappedDistance c z i)]
    apply (div_le_iff₀ hy).mp
    rw [le_cappedDistance_iff]
    refine ⟨(div_le_iff₀ hy).mpr ?_,fun j hji=>(div_le_iff₀ hy).mpr ?_⟩
    · simpa [mul_comm] using cappedDistance_le (y*c) (affine x y hy ∘ z) i
    · simpa only [Function.comp_apply,dist_affine,mul_comm] using
        cappedDistance_le_dist (y*c) (affine x y hy ∘ z) i j hji
  · rw [le_cappedDistance_iff]
    refine ⟨mul_le_mul_of_nonneg_left (cappedDistance_le c z i) hy.le,?_⟩
    intro j hji
    simp only [Function.comp_apply,dist_affine]
    exact mul_le_mul_of_nonneg_left (cappedDistance_le_dist c z i j hji) hy.le

lemma kernel_affine {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α c : ℝ) (x : ℂ) {y : ℝ} (hy : 0<y) (z : ι→ℂ) :
    kernel α (y*c) (affine x y hy ∘ z)=
      (ENNReal.ofReal y)^(-α*(Fintype.card ι:ℝ))*kernel α c z := by
  unfold kernel
  simp_rw [cappedDistance_affine x hy c z,ENNReal.ofReal_mul hy.le,
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  rw [←ENNReal.rpow_natCast,←ENNReal.rpow_mul]

lemma pi_const_smul {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (r : ℝ≥0) (m : ℕ) :
    Measure.pi (fun _ : Fin m=>r • μ)=(r:ℝ≥0∞)^m • Measure.pi (fun _ : Fin m=>μ) := by
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.smul_apply,smul_eq_mul,Measure.pi_pi,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,ENNReal.smul_def]

lemma affine_area (x : ℂ) {y : ℝ} (hy : 0<y) {K : Set ℂ} (hK : MeasurableSet K) :
    volume.restrict (affine x y hy '' K)=
      (NNReal.mk (y^2) (sq_nonneg y)) • (volume.restrict K).map (affine x y hy) := by
  let T := affine x y hy
  have hder (z : ℂ) : HasDerivAt T (y:ℂ) z := by
    change HasDerivAt (fun w : ℂ=>x+(y:ℂ)*w) (y:ℂ) z
    simpa only [mul_one,id_eq] using ((hasDerivAt_id z).const_mul (y:ℂ)).const_add x
  ext A hA
  have h := Conformal.lintegral_image_complex hK
    (fun z _ => (hder z).differentiableAt) T.injective.injOn (A.indicator (fun _=>1))
  change (∫⁻z in T '' K,A.indicator (fun _=>(1:ℝ≥0∞)) z)=_ at h
  simp_rw [fun z=> (hder z).deriv,Complex.norm_real,Real.norm_eq_abs,sq_abs] at h
  have hAcomp : Measurable (fun z=>A.indicator (fun _=>(1:ℝ≥0∞)) (T z)) :=
    (measurable_const.indicator hA).comp T.measurable
  rw [lintegral_const_mul _ hAcomp] at h
  rw [←lintegral_map (measurable_const.indicator hA) T.measurable] at h
  rw [lintegral_indicator hA,lintegral_indicator hA,setLIntegral_one,setLIntegral_one] at h
  rw [Measure.smul_apply,ENNReal.smul_def]
  exact h.trans (by congr 1; simp only [ENNReal.ofReal,Real.toNNReal_of_nonneg (sq_nonneg y)])

lemma affine_pi_integral (x : ℂ) {y : ℝ} (hy : 0<y) {K : Set ℂ} (hK : MeasurableSet K)
    (m : ℕ) (F : (Fin m→ℂ)→ℝ≥0∞) (hF : Measurable F) :
    (∫⁻z,F z∂Measure.pi (fun _=>volume.restrict (affine x y hy '' K)))=
      (ENNReal.ofReal y)^(2*m)*
        ∫⁻z,F (affine x y hy ∘ z)∂Measure.pi (fun _=>volume.restrict K) := by
  let T := affine x y hy
  have : SigmaFinite ((volume.restrict K).map T) := T.toMeasurableEquiv.sigmaFinite_map
  rw [affine_area x hy hK,pi_const_smul,lintegral_smul_measure,
    ←Measure.pi_map_pi (fun _ : Fin m=>T.measurable.aemeasurable)]
  rw [lintegral_map hF (by fun_prop)]
  change ((NNReal.mk (y^2) (sq_nonneg y)):ℝ≥0∞)^m*_= _
  rw [show ((NNReal.mk (y^2) (sq_nonneg y)):ℝ≥0∞)=(ENNReal.ofReal y)^2 by
    rw [←ENNReal.ofReal_pow hy.le]; simp only [ENNReal.ofReal,Real.toNNReal_of_nonneg (sq_nonneg y)],
    ←pow_mul]
  rfl

 

theorem fixed_center_integral_affine (α c : ℝ) (hα : 0≤α)
    (x z₀ : ℂ) {y : ℝ} (hy : 0<y) {K : Set ℂ} (hK : MeasurableSet K) (m : ℕ) :
    (∫⁻z : Fin m→ℂ,kernel α (y*c) (Fin.cons (affine x y hy z₀) z)
      ∂Measure.pi (fun _=>volume.restrict (affine x y hy '' K)))=
      (ENNReal.ofReal y)^(2*(m:ℝ)-α*((m:ℝ)+1))*
        ∫⁻z : Fin m→ℂ,kernel α c (Fin.cons z₀ z)
          ∂Measure.pi (fun _=>volume.restrict K) := by
  have hm : Measurable (fun z : Fin m→ℂ=>kernel α (y*c) (Fin.cons (affine x y hy z₀) z)) :=
    (measurable_kernel hα _).comp (by fun_prop)
  rw [affine_pi_integral x hy hK m _ hm]
  have he (z : Fin m→ℂ) : Fin.cons (affine x y hy z₀) (affine x y hy ∘ z)=
      affine x y hy ∘ Fin.cons z₀ z := by
    funext i
    refine Fin.cases ?_ (fun j=>?_) i <;> simp
  simp_rw [he,kernel_affine,Fintype.card_fin]
  have hf : Measurable (fun z : Fin m→ℂ=>kernel α c (Fin.cons z₀ z)) :=
    (measurable_kernel hα c).comp (by fun_prop)
  rw [lintegral_const_mul _ hf,←mul_assoc,
    ←ENNReal.rpow_natCast,←ENNReal.rpow_add _ _ (ne_of_gt (ENNReal.ofReal_pos.mpr hy)) ENNReal.ofReal_ne_top]
  congr 2
  push_cast
  ring

end SLEExactGauge.KernelSimilarity
end
end

end OAI
