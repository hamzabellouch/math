import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.KernelMeasurability

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open scoped Topology
open Set
open MeasureTheory Filter
open scoped NNReal Topology
open MeasureTheory Filter Set Metric Function ODE
open MeasureTheory ProbabilityTheory Filter Set
open Filter
open Filter Set
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open MeasureTheory
open scoped Classical
open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped NNReal ENNReal Topology
open scoped ENNReal
namespace ExactSLEKernel
lemma kernel_cons_bound {m : ℕ} {α b : ℝ} (ha : 0 ≤ α) (hb : 0 < b)
    (z : ℂ) (x : Fin m → ℂ) :
    kernel α b (Fin.cons z x) ≤
      ipow α (1/2)^m * kernel α b x *
        (ipow α b + ∑ i, ipow α (dist z (x i)) +
          ENNReal.ofReal b ^ α * ∑ i, ipow (2*α) (dist z (x i))) := by
  classical
  have hD : 1 ≤ ipow α (1/2) := by
    have := ipow_anti ha (show (1:ℝ)/2 ≤ 1 by norm_num)
    simpa [ipow] using this
  by_cases hn : ∃ i, dist z (x i) < cappedDistance b x i / 2
  · obtain ⟨i,hi⟩ := hn
    have hp : (∏ j : Fin m, ipow α (cappedDistance b (Fin.cons z x) j.succ)) ≤
        ipow α (1/2)^m * kernel α b x * (ENNReal.ofReal b ^ α * ipow α (dist z (x i))) := by
      calc
        _ ≤ ∏ j : Fin m, (ipow α (1/2) * ipow α (cappedDistance b x j)) *
            (if j=i then ENNReal.ofReal b ^ α * ipow α (dist z (x i)) else 1) := by
          apply Finset.prod_le_prod
          intro j hj
          by_cases hji : j=i
          · subst j
            rw [ite_eq_left rfl,cappedDistance_cons_succ,min_eq_right (by have := dist_nonneg (x:=z) (y:=x i); linarith)]
            calc
              _ = 1 * ipow α (dist z (x i)) := by simp
              _ ≤ (ipow α (1/2) * (ipow α (cappedDistance b x i) * ENNReal.ofReal b ^ α)) * ipow α (dist z (x i)) := by
                exact mul_le_mul' (one_le_mul_of_one_le_of_one_le hD (cap_compensated ha hb x i)) le_rfl
              _ = _ := by ac_rfl
          · rw [ite_eq_right hji,mul_one]
            apply far_cap_factor ha hb.le
            by_contra h
            exact hji (half_cap_unique b z x j i (lt_of_not_ge h) hi)
        _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]; simp [Finset.prod_ite_eq',kernel,ipow]
    rw [kernel,Fin.prod_univ_succ]
    change ipow α (cappedDistance b (Fin.cons z x) 0) * _ ≤ _
    rw [near_cap_nearest b z x i hi]
    calc
      _ ≤ ipow α (dist z (x i)) *
          (ipow α (1/2)^m * kernel α b x * (ENNReal.ofReal b ^ α * ipow α (dist z (x i)))) := mul_le_mul' le_rfl hp
      _ = ipow α (1/2)^m * kernel α b x * (ENNReal.ofReal b ^ α * ipow (2*α) (dist z (x i))) := by rw [ipow_twice]; ac_rfl
      _ ≤ _ := by
        apply mul_le_mul' le_rfl
        exact (mul_le_mul' le_rfl (Finset.single_le_sum (fun k _ => (by positivity : (0:ℝ≥0∞) ≤ ipow (2*α) (dist z (x k)))) (Finset.mem_univ i))).trans le_add_self
  · push Not at hn
    have hp : (∏ j : Fin m, ipow α (cappedDistance b (Fin.cons z x) j.succ)) ≤
        ipow α (1/2)^m * kernel α b x := by
      calc
        _ ≤ ∏ j : Fin m, ipow α (1/2) * ipow α (cappedDistance b x j) :=
          Finset.prod_le_prod (fun j _ => far_cap_factor ha hb.le z x j (hn j))
        _ = _ := by simp [Finset.prod_mul_distrib,kernel,ipow]
    rw [kernel,Fin.prod_univ_succ]
    change ipow α (cappedDistance b (Fin.cons z x) 0) * _ ≤ _
    calc
      _ ≤ (ipow α b + ∑ i, ipow α (dist z (x i))) *
          (ipow α (1/2)^m * kernel α b x) := mul_le_mul' (cap_cons_factor_sum ha b z x) hp
      _ ≤ _ := by rw [mul_comm]; exact mul_le_mul' le_rfl le_self_add

open Metric

lemma singular_ball_finite {p : ℝ} (_hp : 0 < p) (hp2 : p < 2) (R : ℝ) :
    (∫⁻ x : ℂ in ball 0 R, edist x 0 ^ (-p)) < ∞ := by
  have hi : IntegrableOn (fun x : ℂ => ‖x‖ ^ (-p)) (ball 0 R) := by
    refine integrableOn_ball_of_norm_le_rpow (C:=1) (α:=p) (by simp) (by simpa using hp2) ?_ ?_
    · filter_upwards [] with x
      simp [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    · exact (measurable_norm.pow_const _).aestronglyMeasurable
  have hn : ∀ᵐ x : ℂ ∂volume.restrict (ball 0 R), x ≠ 0 :=
    ae_restrict_of_ae (by simp [ae_iff])
  have he : (fun x : ℂ => edist x 0 ^ (-p)) =ᵐ[volume.restrict (ball 0 R)]
      fun x => ENNReal.ofReal (‖x‖ ^ (-p)) := by
    filter_upwards [hn] with x hx
    rw [edist_dist,dist_zero_right,ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr hx)]
  rw [lintegral_congr_ae he]
  exact hi.lintegral_lt_top
lemma singular_ball_translate (p : ℝ) (z : ℂ) (R : ℝ) :
    (∫⁻ x : ℂ in ball z R, edist x z ^ (-p)) = ∫⁻ x : ℂ in ball 0 R, edist x 0 ^ (-p) := by
  rw [← lintegral_indicator measurableSet_ball,← lintegral_indicator measurableSet_ball]
  convert lintegral_sub_right_eq_self (μ:=volume) ((ball (0:ℂ) R).indicator (fun x => edist x 0 ^ (-p))) z using 1
  congr 1
  funext x
  simp [Set.indicator,mem_ball,dist_eq_norm,sub_zero,edist_dist]
lemma singular_uniform {p : ℝ} (hp : 0 < p) (hp2 : p < 2) (K : Set ℂ)
    (hKb : Bornology.IsBounded K) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ z : ℂ, (∫⁻ x in K, edist x z ^ (-p)) ≤ C := by
  let C := volume K + ∫⁻ x : ℂ in ball 0 1, edist x 0 ^ (-p)
  refine ⟨C,ENNReal.add_lt_top.mpr ⟨hKb.measure_lt_top,(singular_ball_finite hp hp2 1)⟩,?_⟩
  intro z
  calc
    _ ≤ ∫⁻ x in K, 1 + (ball z 1).indicator (fun x => edist x z ^ (-p)) x := by
      apply lintegral_mono
      intro x
      dsimp only
      by_cases hx : x ∈ ball z 1
      · simp [indicator_of_mem hx]
      · rw [indicator_of_notMem hx,add_zero]
        have hd : (1:ℝ≥0∞) ≤ edist x z := by
          rw [edist_dist,ENNReal.one_le_ofReal]
          simpa [mem_ball,dist_comm] using hx
        calc
          _ ≤ edist x z ^ (0:ℝ) := ENNReal.rpow_le_rpow_of_exponent_le hd (by linarith)
          _ = 1 := by simp
    _ = volume K + ∫⁻ x in K, (ball z 1).indicator (fun x => edist x z ^ (-p)) x := by
      rw [lintegral_add_left measurable_const,lintegral_const,Measure.restrict_apply_univ,one_mul]
    _ ≤ volume K + ∫⁻ x, (ball z 1).indicator (fun x => edist x z ^ (-p)) x :=
      add_le_add le_rfl (lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl))
    _ = C := by rw [lintegral_indicator measurableSet_ball,singular_ball_translate]
lemma conditional_kernel_bound {α b : ℝ} (ha : 0 < α) (ha1 : α < 1) (hb : 0 < b)
    (m : ℕ) (K : Set ℂ) (hKb : Bornology.IsBounded K) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ x : Fin m → ℂ,
      (∫⁻ z in K, kernel α b (Fin.cons z x)) ≤ C * kernel α b x := by
  obtain ⟨A,hA,hAb⟩ := singular_uniform ha (by linarith) K hKb
  obtain ⟨B,hB,hBb⟩ := singular_uniform (show 0 < 2*α by linarith) (by linarith) K hKb
  let Q := ipow α b * volume K + (m:ℝ≥0∞)*A + ENNReal.ofReal b ^ α * ((m:ℝ≥0∞)*B)
  let C := ipow α (1/2)^m * Q
  have hQ : Q < ∞ := by
    apply ENNReal.add_lt_top.mpr
    refine ⟨ENNReal.add_lt_top.mpr ⟨?_,?_⟩,?_⟩
    · exact ENNReal.mul_lt_top (ipow_finite hb) hKb.measure_lt_top
    · exact ENNReal.mul_lt_top (by simp) hA
    · exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg ha.le ENNReal.ofReal_ne_top)) (ENNReal.mul_lt_top (by simp) hB)
  refine ⟨C,ENNReal.mul_lt_top (ENNReal.pow_lt_top (ipow_finite (by norm_num))) hQ,?_⟩
  intro x
  have hm (p : ℝ) (i : Fin m) : Measurable (fun z : ℂ => ipow p (dist z (x i))) := by unfold ipow; fun_prop
  have hsum (p : ℝ) : Measurable (fun z : ℂ => ∑ i, ipow p (dist z (x i))) := Finset.measurable_sum _ (fun _ _ => hm _ _)
  have hs : (∫⁻ z in K, ipow α b + ∑ i, ipow α (dist z (x i)) +
        ENNReal.ofReal b ^ α * ∑ i, ipow (2*α) (dist z (x i))) ≤ Q := by
    rw [lintegral_add_left (f:=fun z : ℂ => ipow α b + ∑ i, ipow α (dist z (x i))) (by fun_prop),lintegral_add_left (f:=fun _ : ℂ => ipow α b) measurable_const,
        lintegral_const,Measure.restrict_apply_univ,
        lintegral_finsetSum _ (fun _ _ => hm _ _),lintegral_const_mul _ (hsum _),
        lintegral_finsetSum _ (fun _ _ => hm _ _)]
    apply add_le_add
    · apply add_le_add le_rfl
      calc
        _ ≤ ∑ i : Fin m, A := Finset.sum_le_sum (fun i _ => by simpa [ipow,edist_dist] using hAb (x i))
        _ = _ := by simp
    · apply mul_le_mul' le_rfl
      calc
        _ ≤ ∑ i : Fin m, B := Finset.sum_le_sum (fun i _ => by simpa [ipow,edist_dist] using hBb (x i))
        _ = _ := by simp
  calc
    _ ≤ ∫⁻ z in K, ipow α (1/2)^m * kernel α b x *
        (ipow α b + ∑ i, ipow α (dist z (x i)) +
          ENNReal.ofReal b ^ α * ∑ i, ipow (2*α) (dist z (x i))) := lintegral_mono (fun z => kernel_cons_bound ha.le hb z x)
    _ = _ := lintegral_const_mul _ ((measurable_const.add (hsum α)).add (measurable_const.mul (hsum _)))
    _ ≤ (ipow α (1/2)^m * kernel α b x) * Q := mul_le_mul' le_rfl hs
    _ = C * kernel α b x := by dsimp [C]; ac_rfl
lemma cap_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (b : ℝ) (x : κ → ℂ) (i : ι) :
    cappedDistance b (x ∘ e) i = cappedDistance b x (e i) := by
  apply le_antisymm
  · apply (le_cappedDistance_iff _ _ _ _).mpr
    refine ⟨cappedDistance_le _ _ _,?_⟩
    intro j hj
    have := cappedDistance_le_dist b (x ∘ e) i (e.symm j) (fun h => hj (by rw [←e.apply_symm_apply j,h]))
    simpa using this
  · apply (le_cappedDistance_iff _ _ _ _).mpr
    exact ⟨cappedDistance_le _ _ _,fun j hj => cappedDistance_le_dist b x (e i) (e j) (fun h => hj (e.injective h))⟩
lemma kernel_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (α b : ℝ) (x : κ → ℂ) : kernel α b (x ∘ e) = kernel α b x := by
  unfold kernel
  simp_rw [cap_equiv]
  exact e.prod_comp (fun i => ENNReal.ofReal (cappedDistance b x i) ^ (-α))
lemma kernel_swap_cons {m : ℕ} (α b : ℝ) (z y : ℂ) (x : Fin m → ℂ) :
    kernel α b (Fin.cons z (Fin.cons y x)) = kernel α b (Fin.cons y (Fin.cons z x)) := by
  classical
  have he : Fin.cons z (Fin.cons y x) =
      (Fin.cons y (Fin.cons z x)) ∘ Equiv.swap 0 (1 : Fin (m+2)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp
      · simp [Equiv.swap_apply_of_ne_of_ne,Fin.succ_succ_ne_one]
  rw [he,kernel_equiv]
lemma lintegral_cons {m : ℕ} (μ : Measure ℂ) [SigmaFinite μ]
    (f : (Fin (m+1) → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂Measure.pi (fun _ => μ)) =
      ∫⁻ x : Fin m → ℂ, ∫⁻ z : ℂ, f (Fin.cons z x) ∂μ ∂Measure.pi (fun _ => μ) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℂ) 0
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => μ) 0).symm
  have hi := he.lintegral_comp hf
  rw [←hi]
  change (∫⁻ a : ℂ × (Fin m → ℂ), (f ∘ e.symm) a ∂μ.prod (Measure.pi fun _ => μ)) = _
  rw [lintegral_prod_symm _ (hf.comp e.symm.measurable).aemeasurable]
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro z
  simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]

theorem capped_distance_kernel_integral (α b : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hb : 0 < b) (m : ℕ) (K : Set ℂ) (_hK : MeasurableSet K) (hKb : Bornology.IsBounded K) :
    (∫⁻ x : Fin m → ℂ, kernel α b x ∂Measure.pi (fun _ => volume.restrict K)) < ∞ := by
  induction m with
  | zero => simp [kernel]
  | succ m ih =>
    obtain ⟨C,hC,hCb⟩ := conditional_kernel_bound hα hα1 hb m K hKb
    rw [lintegral_cons _ _ (measurable_kernel hα.le b)]
    calc
      _ ≤ ∫⁻ x : Fin m → ℂ, C * kernel α b x ∂Measure.pi (fun _ => volume.restrict K) := lintegral_mono hCb
      _ = C * ∫⁻ x : Fin m → ℂ, kernel α b x ∂Measure.pi (fun _ => volume.restrict K) := lintegral_const_mul _ (measurable_kernel hα.le b)
      _ < ∞ := ENNReal.mul_lt_top hC ih

theorem capped_distance_fixed_center (α b : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hb : 0 < b) (m : ℕ) (K K₀ : Set ℂ) (_hK : MeasurableSet K)
    (hKb : Bornology.IsBounded K) (_hK₀b : Bornology.IsBounded K₀) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ z ∈ K₀,
      (∫⁻ x : Fin m → ℂ, kernel α b (Fin.cons z x) ∂Measure.pi (fun _ => volume.restrict K)) ≤ C := by
  have hmain : ∀ m : ℕ, ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ z : ℂ,
      (∫⁻ x : Fin m → ℂ, kernel α b (Fin.cons z x) ∂Measure.pi (fun _ => volume.restrict K)) ≤ C := by
    intro m
    induction m with
    | zero =>
      refine ⟨ipow α b,ipow_finite hb,fun z => ?_⟩
      simp [kernel,cappedDistance,ipow]
    | succ m ih =>
      obtain ⟨A,hA,hAb⟩ := ih
      obtain ⟨C,hC,hCb⟩ := conditional_kernel_bound hα hα1 hb (m+1) K hKb
      refine ⟨C*A,ENNReal.mul_lt_top hC hA,fun z => ?_⟩
      have hm : Measurable (fun x : Fin (m+1) → ℂ => kernel α b (Fin.cons z x)) :=
        (measurable_kernel hα.le b).comp (by fun_prop)
      rw [lintegral_cons _ _ hm]
      simp_rw [kernel_swap_cons α b z]
      calc
        _ ≤ ∫⁻ x : Fin m → ℂ, C * kernel α b (Fin.cons z x) ∂Measure.pi (fun _ => volume.restrict K) := lintegral_mono (fun x => hCb (Fin.cons z x))
        _ = C * ∫⁻ x : Fin m → ℂ, kernel α b (Fin.cons z x) ∂Measure.pi (fun _ => volume.restrict K) := lintegral_const_mul _ ((measurable_kernel hα.le b).comp (by fun_prop))
        _ ≤ _ := mul_le_mul' le_rfl (hAb z)
  obtain ⟨C,hC,hCb⟩ := hmain m
  exact ⟨C,hC,fun z _ => hCb z⟩
end ExactSLEKernel

namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory Set ExactSLEGenerator ExactSLEMain
open scoped Classical NNReal ENNReal
noncomputable def fullRadialDensity (a : ℝ) (b : ℝ≥0 → ℝ) (z : ℂ) (target : ℝ) : ℝ :=
  Real.exp (-alpha a * Real.log 2) * radialWeight a b z (target/2)
lemma fullRadialDensity_bound (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im)
    (target : ℝ) (ht : 0<target) (htz : target≤2*z.im) (b : ExactSLEGenerator.Driver) :
    0≤fullRadialDensity a b.1 z target ∧ fullRadialDensity a b.1 z target≤target^(-alpha a) := by
  have h := radialWeight_bound a ha z hz (target/2) (by positivity) (by linarith) b
  refine ⟨mul_nonneg (Real.exp_pos _).le h.1,?_⟩
  calc
    _ ≤ Real.exp (-alpha a*Real.log 2)*Real.exp (-alpha a*Real.log (target/2)) :=
      mul_le_mul_of_nonneg_left h.2 (Real.exp_pos _).le
    _ = target^(-alpha a) := by
      rw [←Real.exp_add,Real.log_div ht.ne' (by norm_num : (2:ℝ)≠0),Real.rpow_def_of_pos ht]
      congr 1; ring

lemma selective_hit_bound (a : ℝ) (ha : 1/4<a) (m : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W],
    IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W →
    ∀ z : Fin m → ℂ, Function.Injective z → (∀ i, 0<(z i).im) →
    ∀ cap target : Fin m → ℝ,
      (∀ i, 0<cap i ∧ cap i≤2*(z i).im) →
      (∀ i j, i≠j → cap i≤‖z i-z j‖) →
      ∀ I : Finset (Fin m), (∀ i∈I, 0<target i ∧ target i≤cap i) →
      W {b : ExactSLEGenerator.Driver | ∀ i∈I, radialTime a b.1 (z i) (target i/2)<∞} ≤
        ENNReal.ofReal (C*∏ i∈I, (target i/cap i)^(alpha a)) := by
  choose D hD hDb using fun k => actual_multipoint_hit_bound a ha k
  let C := 1+∑ k∈Finset.range (m+1), D k
  have hCle (k : ℕ) (hk : k ≤ m) : D k ≤ C := by
    have hs : D k≤∑ j∈Finset.range (m+1), D j :=
      Finset.single_le_sum (fun j _ => (hD j).le) (Finset.mem_range.mpr (by omega))
    dsimp [C]; linarith
  have hCp : 0<C := (hD 0).trans_le (hCle 0 (Nat.zero_le m))
  refine ⟨C,hCp,?_⟩
  intro W hprob hW z hinj hz cap target hc hsep I ht
  let e := (Fintype.equivFin I).symm
  have h : Fintype.card I ≤ m := by simpa using I.card_le_univ
  have hb := hDb (Fintype.card I) W hW (fun i => z (e i))
    (hinj.comp (Subtype.val_injective.comp e.injective)) (fun i => hz (e i))
    (fun i => cap (e i)) (fun i => target (e i)) (fun i => hc (e i))
    (fun i j hij => hsep (e i) (e j) (fun he => hij (e.injective (Subtype.ext he))))
    (fun i => ht (e i) (e i).2)
  have he : {b : ExactSLEGenerator.Driver | ∀ i : Fin (Fintype.card I), radialTime a b.1 (z (e i)) (target (e i)/2)<∞} =
      {b : ExactSLEGenerator.Driver | ∀ i∈I, radialTime a b.1 (z i) (target i/2)<∞} := by
    ext b; simp only [mem_ofPred_eq]
    constructor
    · intro H i hi; obtain ⟨j,hj⟩ := e.surjective ⟨i,hi⟩; simpa [hj] using H j
    · intro H i; exact H (e i) (e i).2
  have hp : (∏ i : Fin (Fintype.card I), (target (e i)/cap (e i))^(alpha a)) =
      ∏ i∈I, (target i/cap i)^(alpha a) := by
    rw [e.prod_comp (fun i : I => (target i/cap i)^(alpha a))]
    exact Finset.prod_coe_sort I (fun i => (target i/cap i)^(alpha a))
  rw [he,hp] at hb
  refine hb.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hCle _ h) ?_))
  exact Finset.prod_nonneg fun i hi => Real.rpow_nonneg (le_of_lt (div_pos (ht i hi).1 (hc i).1)) _

theorem actual_density_product_bound (a : ℝ) (ha : 1/4 < a) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W],
    IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W →
    ∀ z : Fin m → ℂ, Function.Injective z → (∀ i, 0 < (z i).im) →
    ∀ cap target : Fin m → ℝ,
      (∀ i, 0<cap i ∧ cap i≤2*(z i).im) →
      (∀ i j, i≠j → cap i≤‖z i-z j‖) →
      (∀ i, 0<target i ∧ target i≤2*(z i).im) →
      (∫⁻ b, ∏ i, ENNReal.ofReal (fullRadialDensity a b.1 (z i) (target i)) ∂W) ≤
        ENNReal.ofReal (C*∏ i, (cap i)^(-alpha a)) := by
  obtain ⟨C,hC,hCb⟩ := selective_hit_bound a ha m
  refine ⟨C,hC,?_⟩
  intro W hprob hW z hinj hz cap target hc hsep ht
  let I := Finset.univ.filter (fun i => target i≤cap i)
  let E := {b : ExactSLEGenerator.Driver | ∀ i∈I, radialTime a b.1 (z i) (target i/2)<∞}
  let A := ∏ i, (target i)^(-alpha a)
  have hA : 0≤A := Finset.prod_nonneg fun i _ => Real.rpow_nonneg (ht i).1.le _
  have hhit : W E≤ENNReal.ofReal (C*∏ i∈I, (target i/cap i)^(alpha a)) :=
    hCb W hW z hinj hz cap target hc hsep I (fun i hi => ⟨(ht i).1,(Finset.mem_filter.mp hi).2⟩)
  have hpoint (b : ExactSLEGenerator.Driver) :
      (∏ i, ENNReal.ofReal (fullRadialDensity a b.1 (z i) (target i))) ≤ E.indicator (fun _ => ENNReal.ofReal A) b := by
    by_cases hb : b∈E
    · rw [Set.indicator_of_mem hb,ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (ht i).1.le _)]
      exact Finset.prod_le_prod₀ (fun _ _ => bot_le) (fun i _ => ENNReal.ofReal_le_ofReal
        (fullRadialDensity_bound a ha (z i) (hz i) (target i) (ht i).1 (ht i).2 b).2)
    · rw [Set.indicator_of_notMem hb]
      have he : ∃ i∈I, radialTime a b.1 (z i) (target i/2)=∞ := by
        by_contra hn
        apply hb
        intro i hi
        exact lt_top_iff_ne_top.mpr (fun he => hn ⟨i,hi,he⟩)
      obtain ⟨i,hi,he⟩ := he
      have hz0 : ENNReal.ofReal (fullRadialDensity a b.1 (z i) (target i))=0 := by
        simp [fullRadialDensity,radialWeight,he]
      exact le_of_eq (Finset.prod_eq_zero (Finset.mem_univ i) hz0)
  have halg : A*(∏ i∈I, (target i/cap i)^(alpha a)) ≤ ∏ i, (cap i)^(-alpha a) := by
    unfold A I
    rw [Finset.prod_filter,←Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro i _
      apply mul_nonneg (Real.rpow_nonneg (ht i).1.le _)
      split_ifs
      · exact Real.rpow_nonneg (div_nonneg (ht i).1.le (hc i).1.le) _
      · norm_num
    · intro i _
      by_cases hi : target i≤cap i
      · rw [ite_eq_left hi,Real.div_rpow (ht i).1.le (hc i).1.le,
          Real.rpow_neg (ht i).1.le,Real.rpow_neg (hc i).1.le]
        have hp := Real.rpow_pos_of_pos (ht i).1 (alpha a)
        field_simp
        rfl
      · rw [ite_eq_right hi,mul_one]
        exact Real.rpow_le_rpow_of_nonpos (hc i).1 (le_of_not_ge hi) (neg_nonpos.mpr (alpha_pos ha).le)
  calc
    _ ≤ ∫⁻ b, E.indicator (fun _ => ENNReal.ofReal A) b ∂W := lintegral_mono hpoint
    _ ≤ ENNReal.ofReal A*W E := lintegral_indicator_const_le E _
    _ ≤ ENNReal.ofReal A*ENNReal.ofReal (C*∏ i∈I, (target i/cap i)^(alpha a)) := mul_le_mul' le_rfl hhit
    _ = ENNReal.ofReal (C*(A*∏ i∈I, (target i/cap i)^(alpha a))) := by rw [←ENNReal.ofReal_mul hA]; congr 1; ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left halg hC.le)
end ExactSLEGreen

namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory Set ExactSLEGenerator ExactSLEMain ExactSLEKernel
open scoped Classical NNReal ENNReal
noncomputable def massDensity (a q : ℝ) (b : ExactSLEGenerator.Driver) (z : ℂ) : ℝ≥0∞ :=
  if 0<z.im then ENNReal.ofReal (fullRadialDensity a b.1 z (2*z.im*q)) else 0
lemma massDensity_measurable (a : ℝ) (ha : 1/4<a) (q : ℝ) (hq : 0<q) (hq1 : q≤1) :
    Measurable (fun p : ExactSLEGenerator.Driver × ℂ => massDensity a q p.1 p.2) := by
  let U : Set (ExactSLEGenerator.Driver × ℂ) := {p | 0<p.2.im}
  have hU : MeasurableSet U := measurableSet_lt measurable_const (Complex.measurable_im.comp measurable_snd)
  have hm : Measurable (fun p : U => ENNReal.ofReal
      (Real.exp (-alpha a*Real.log 2)*radialWeight a p.1.1.1 p.1.2 (p.1.2.im*q))) := by
    have hp : Measurable (fun p : U => (p.1.1, (⟨p.1.2,p.2⟩ : {z : ℂ // 0<z.im}))) := by fun_prop
    exact ((measurable_const.mul ((joint_radialWeight_measurable a ha q hq hq1).comp hp)).ennreal_ofReal)
  have h := hm.dite (g:=fun _ => 0) measurable_const hU
  convert h using 1
  funext p
  simp only [massDensity,fullRadialDensity]
  have he : 2*p.2.im*q/2=p.2.im*q := by ring
  simp only [he]
  rfl

lemma lintegral_power_pi (μ : Measure ℂ) [SigmaFinite μ] (f : ℂ → ℝ≥0∞)
    (hf : Measurable f) (m : ℕ) :
    (∫⁻ z, f z ∂μ)^m = ∫⁻ x : Fin m → ℂ, ∏ i, f (x i) ∂Measure.pi (fun _ => μ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [lintegral_cons _ _ (by fun_prop)]
    simp_rw [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,lintegral_mul_const _ hf]
    rw [lintegral_const_mul _ (by fun_prop),←ih,pow_succ']

lemma kernel_top_of_not_injective (α c : ℝ) (ha : 0<α) (hc : 0<c)
    {m : ℕ} (x : Fin m → ℂ) (hx : ¬Function.Injective x) : kernel α c x=∞ := by
  classical
  have hh : ∃ i j, x i=x j ∧ i≠j := by
    by_contra hn
    apply hx
    intro i j hij
    by_contra hne
    exact hn ⟨i,j,hij,hne⟩
  obtain ⟨i,j,hij,hne⟩ := hh
  have hz : cappedDistance c x i=0 := by
    apply le_antisymm _ (cappedDistance_nonneg hc.le x i)
    have h := cappedDistance_le_dist c x i j hne.symm
    simpa [hij] using h
  have hp : ∀ k, ENNReal.ofReal (cappedDistance c x k)^(-α) ≠ 0 := fun k =>
    ne_of_gt (ipow_pos ha.le)
  unfold kernel
  rw [←Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),hz,ENNReal.ofReal_zero,
    ENNReal.zero_rpow_def]
  simp only [neg_pos,not_lt.mpr ha.le,ite_false,neg_eq_zero,ha.ne']
  exact ENNReal.top_mul (Finset.prod_ne_zero_iff.mpr (fun k _ => hp k))

end ExactSLEGreen
end

end OAI
