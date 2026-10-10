import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.TwoPointGrowth

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
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEFiniteTilt
lemma actual_radius_eq_full {a : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {z : ℂ} {t : ℝ≥0} (ht : alive a b t z) :
    2*physicalRadius (actualState a b t z)=fullLoewnerRadius a b z t := by
  have hd := norm_pos_iff.mpr (deriv_loewnerMap_ne_zero hb ht)
  simp only [physicalRadius,actualState,Y_apply,J_apply,Complex.sub_im,Complex.ofReal_im,sub_zero,
    Real.exp_neg,Real.exp_log hd,fullLoewnerRadius,div_eq_mul_inv]
  ring
lemma physicalClock_radius (a cap : ℝ) (hcap : 0<cap) (v : State) (hv : 0<Y v) :
    physicalClock a cap v=Real.log (cap/(2*physicalRadius v))/(2*a) := by
  rw [physicalClock,physicalRadius,Real.log_div hcap.ne' (by norm_num : (2:ℝ)≠0),
    Real.log_div hcap.ne' (show 2*(Y v*Real.exp (-J v))≠0 by positivity),
    Real.log_mul (by norm_num : (2:ℝ)≠0) (by positivity),
    Real.log_mul hv.ne' (Real.exp_ne_zero _),Real.log_exp]
  ring
lemma actual_clock_eq {a cap : ℝ} (ha : a≠0) (hcap : 0<cap)
    {b : ℝ≥0 → ℝ} (hb : Continuous b) {z : ℂ} {T σ t : ℝ≥0} {f : ℝ → ℂ}
    (hf : odeUntil a b z T f) (hσ : σ≤T) (ht : t≤T)
    (hR : fullLoewnerRadius a b z σ=cap) :
    physicalClock a cap (actualState a b t z)=activeODEClock b T σ f t := by
  have hy : 0<Y (actualState a b t z) := by
    simpa only [actualState,Y_apply,Complex.sub_im,Complex.ofReal_im,sub_zero,loewnerMap_eq (odeUntil_mono hf ht)]
      using (hf.2 t ⟨t.coe_nonneg,by exact_mod_cast ht⟩).1
  rw [physicalClock_radius a cap hcap _ hy,actual_radius_eq_full hb ⟨f,odeUntil_mono hf ht⟩,
    fullRadius_active_clock hb hf hσ ht,hR]
  have he : cap/(cap*Real.exp (-2*a*activeODEClock b T σ f t))=
      Real.exp (2*a*activeODEClock b T σ f t) := by
    rw [show -2*a*activeODEClock b T σ f t = -(2*a*activeODEClock b T σ f t) by ring,
      Real.exp_neg,div_mul_eq_div_div,div_self hcap.ne',one_div,inv_inv]
  rw [he,Real.log_exp]
  field_simp
lemma actual_speed_eq {a : ℝ} {b : ℝ≥0 → ℝ} {z : ℂ} {T t : ℝ≥0} {f : ℝ → ℂ}
    (hf : odeUntil a b z T f) (ht : t≤T) :
    physicalV (actualState a b t z)=odeSpeed b T f t := by
  rw [odeSpeed_eq f ⟨t.coe_nonneg,by exact_mod_cast ht⟩]
  simp only [physicalV,actualState,Y_apply,Q_eq,loewnerMap_eq (odeUntil_mono hf ht),
    Complex.sub_im,Complex.ofReal_im,sub_zero,Real.toNNReal_coe]
end ExactSLEGreen
namespace ExactSLEMain
lemma exp_clock_integral {a σ off : ℝ} (hσ : σ≠0)
    {b : ℝ≥0 → ℝ} (hb : Continuous b) {z : ℂ} {T A S : ℝ≥0} {f : ℝ → ℂ}
    (hf : odeUntil a b z T f) :
    (∫ t in (S:ℝ)..(T:ℝ), Real.exp (off+σ*activeODEClock b T A f t)*odeSpeed b T f t^2)=
      (Real.exp (off+σ*activeODEClock b T A f T)-
        Real.exp (off+σ*activeODEClock b T A f S))/σ := by
  let u := activeODEClock b T A f
  let v := odeSpeed b T f
  have hc : Continuous u := continuous_iff_continuousAt.mpr fun t => (activeODEClock_deriv hb hf A t).continuousAt
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f:=fun t => Real.exp (off+σ*u t)/σ)
    (f':=fun t => Real.exp (off+σ*u t)*v t^2)
    (a:=(S:ℝ)) (b:=(T:ℝ))
    (fun t _ => by
      exact (((((activeODEClock_deriv hb hf A t).const_mul σ).const_add off).exp).div_const σ).congr_deriv (by
        dsimp only [u,v]; field_simp [hσ]))
    (((Real.continuous_exp.comp (continuous_const.add (continuous_const.mul hc))).mul
      ((odeSpeed_continuous hb hf).pow 2)).intervalIntegrable _ _)
  simpa only [sub_div] using he
end ExactSLEMain
namespace ExactSLEMain
lemma activeODEClock_monotone {a : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {z : ℂ} {T A : ℝ≥0} {f : ℝ → ℂ} (hf : odeUntil a b z T f) :
    Monotone (activeODEClock b T A f) := by
  exact monotone_of_hasDerivAt_nonneg (fun t => activeODEClock_deriv hb hf A t) (fun t => sq_nonneg _)
end ExactSLEMain
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEFiniteTilt
 

theorem actual_regularized_pair_discount {a : ℝ} (ha : 1/4<a)
    {b : ℝ≥0 → ℝ} (hb : Continuous b) {z w : ℂ} {f g : ℝ → ℂ}
    {T S A B : ℝ≥0} (hST : S≤T) (hA : A≤S) (hB : B≤S)
    (hf : odeUntil a b z T f) (hg : odeUntil a b w T g) (hzw : z≠w)
    {cap₁ cap₂ U₁ U₂ σ₁ σ₂ off₁ off₂ : ℝ}
    (hcap₁ : 0<cap₁) (hcap₂ : 0<cap₂)
    (hR₁ : fullLoewnerRadius a b z A=cap₁) (hR₂ : fullLoewnerRadius a b w B=cap₂)
    (hsep₁ : cap₁≤‖z-w‖) (hsep₂ : cap₂≤‖z-w‖)
    (hp₁ : (σ₁=-regBeta a ∧ off₁=0) ∨
      (σ₁=regBeta a ∧ off₁=-regBeta a*U₁ ∧ U₁/2≤activeODEClock b T A f S))
    (hp₂ : (σ₂=-regBeta a ∧ off₂=0) ∨
      (σ₂=regBeta a ∧ off₂=-regBeta a*U₂ ∧ U₂/2≤activeODEClock b T B g S)) :
    (∫ t in (S:ℝ)..(T:ℝ),
      (physicalDelta a cap₁ σ₁ off₁ (actualState a b t.toNNReal z)*
       physicalDelta a cap₂ σ₂ off₂ (actualState a b t.toNNReal w))^(-regM a)*
       physicalV (actualState a b t.toNNReal z)*physicalV (actualState a b t.toNNReal w)) ≤
      Real.exp (2*(regM a*regBeta a))/(2*a*(1-Real.exp (2*(regM a*regBeta a)-a))) := by
  have ha0 : 0<a := by linarith
  have hM := regM_pos ha
  have hβ := regBeta_pos ha
  let u := activeODEClock b T A f
  let v := activeODEClock b T B g
  let V := odeSpeed b T f
  let W := odeSpeed b T g
  have huc : Continuous u := continuous_iff_continuousAt.mpr fun t => (activeODEClock_deriv hb hf A t).continuousAt
  have hvc : Continuous v := continuous_iff_continuousAt.mpr fun t => (activeODEClock_deriv hb hg B t).continuousAt
  let F := fun t => Real.exp ((off₁+σ₁*u t+off₂+σ₂*v t)*(-regM a))*V t*W t
  let G := fun t => Real.exp ((regM a*regBeta a)*(u t+v t))*V t*W t
  have hFc : Continuous F := (((Real.continuous_exp.comp
    (((continuous_const.add (continuous_const.mul huc)).add continuous_const).add
      (continuous_const.mul hvc) |>.mul continuous_const)).mul (odeSpeed_continuous hb hf)).mul
        (odeSpeed_continuous hb hg))
  have hGc : Continuous G := ((Real.continuous_exp.comp
    (continuous_const.mul (huc.add hvc))).mul (odeSpeed_continuous hb hf)).mul (odeSpeed_continuous hb hg)
  have hST' : (S:ℝ)≤T := by exact_mod_cast hST
  have he : (∫ t in (S:ℝ)..(T:ℝ),
      (physicalDelta a cap₁ σ₁ off₁ (actualState a b t.toNNReal z)*
       physicalDelta a cap₂ σ₂ off₂ (actualState a b t.toNNReal w))^(-regM a)*
       physicalV (actualState a b t.toNNReal z)*physicalV (actualState a b t.toNNReal w))=
      ∫ t in (S:ℝ)..(T:ℝ), F t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t∈Icc (S:ℝ) T := by simpa only [uIcc_of_le hST'] using ht
    have ht0 := S.coe_nonneg.trans ht'.1
    have htT : t.toNNReal≤T := by exact_mod_cast (show (t.toNNReal:ℝ)≤T by simpa only [Real.coe_toNNReal _ ht0] using ht'.2)
    simp only [physicalDelta]
    rw [actual_clock_eq ha0.ne' hcap₁ hb hf (hA.trans hST) htT hR₁,
      actual_clock_eq ha0.ne' hcap₂ hb hg (hB.trans hST) htT hR₂,
      actual_speed_eq hf htT,actual_speed_eq hg htT,Real.coe_toNNReal _ ht0,←Real.exp_add,
      Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
    dsimp only [F,u,v,V,W]
    congr 3
    ring
  rw [he]
  calc
    _ ≤ ∫ t in (S:ℝ)..(T:ℝ), G t := by
      apply intervalIntegral.integral_mono_on hST' (hFc.intervalIntegrable _ _) (hGc.intervalIntegrable _ _)
      intro t ht
      have ht0 : 0≤t := S.coe_nonneg.trans ht.1
      have hV : 0≤V t := by
        change 0≤odeSpeed b T f t
        rw [odeSpeed_eq f ⟨ht0,ht.2⟩]
        exact div_nonneg ((hf.2 t ⟨ht0,ht.2⟩).1.le) (Complex.normSq_nonneg _)
      have hW : 0≤W t := by
        change 0≤odeSpeed b T g t
        rw [odeSpeed_eq g ⟨ht0,ht.2⟩]
        exact div_nonneg ((hg.2 t ⟨ht0,ht.2⟩).1.le) (Complex.normSq_nonneg _)
      have h1 : -(off₁+σ₁*u t)≤regBeta a*u t := by
        rcases hp₁ with ⟨rfl,rfl⟩|⟨rfl,rfl,hmid⟩
        · simp
        · have hu : U₁/2≤u t := hmid.trans (activeODEClock_monotone hb hf ht.1)
          nlinarith [mul_le_mul_of_nonneg_left hu hβ.le]
      have h2 : -(off₂+σ₂*v t)≤regBeta a*v t := by
        rcases hp₂ with ⟨rfl,rfl⟩|⟨rfl,rfl,hmid⟩
        · simp
        · have hv : U₂/2≤v t := hmid.trans (activeODEClock_monotone hb hg ht.1)
          nlinarith [mul_le_mul_of_nonneg_left hv hβ.le]
      apply mul_le_mul_of_nonneg_right _ hW
      apply mul_le_mul_of_nonneg_right _ hV
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hM.le
      nlinarith only [hh]
    _ ≤ _ := actual_pair_interaction ha0 (mul_pos hM hβ).le
      (by nlinarith [regBeta_discount ha]) hb hST hA hB hf hg hzw
      (hR₁.le.trans hsep₁) (hR₂.le.trans hsep₂)
end ExactSLEGreen
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEFiniteTilt
lemma actual_regularized_single_discount {a : ℝ} (ha : 1/4<a)
    {b : ℝ≥0 → ℝ} (hb : Continuous b) {z : ℂ} {f : ℝ → ℂ}
    {T S A : ℝ≥0} (hST : S≤T) (hA : A≤S) (hf : odeUntil a b z T f)
    {cap U σ off : ℝ} (hcap : 0<cap) (hR : fullLoewnerRadius a b z A=cap)
    (hp : (σ=-regBeta a ∧ off=0) ∨
      (σ=regBeta a ∧ off=-regBeta a*U ∧ activeODEClock b T A f T≤U)) :
    (∫ t in (S:ℝ)..(T:ℝ), physicalDelta a cap σ off (actualState a b t.toNNReal z)*
      physicalV (actualState a b t.toNNReal z)^2) ≤ 1/regBeta a := by
  have ha0 : 0<a := by linarith
  have hβ := regBeta_pos ha
  have hST' : (S:ℝ)≤T := by exact_mod_cast hST
  let u := activeODEClock b T A f
  have he : (∫ t in (S:ℝ)..(T:ℝ), physicalDelta a cap σ off (actualState a b t.toNNReal z)*
      physicalV (actualState a b t.toNNReal z)^2)=
      ∫ t in (S:ℝ)..(T:ℝ), Real.exp (off+σ*u t)*odeSpeed b T f t^2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t∈Icc (S:ℝ) T := by simpa only [uIcc_of_le hST'] using ht
    have ht0 := S.coe_nonneg.trans ht'.1
    have htT : t.toNNReal≤T := by exact_mod_cast (show (t.toNNReal:ℝ)≤T by simpa only [Real.coe_toNNReal _ ht0] using ht'.2)
    simp only [physicalDelta]
    rw [actual_clock_eq ha0.ne' hcap hb hf (hA.trans hST) htT hR,
      actual_speed_eq hf htT,Real.coe_toNNReal _ ht0]
  rw [he]
  rcases hp with ⟨rfl,rfl⟩|⟨rfl,rfl,hU⟩
  · rw [exp_clock_integral (neg_ne_zero.mpr hβ.ne') hb hf]
    have hu : 0≤u S := activeODEClock_nonneg (by exact_mod_cast hA)
    have hex : Real.exp (0+-regBeta a*u S)≤1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hnon := (Real.exp_pos (0+-regBeta a*u T)).le
    rw [div_neg,←neg_div,neg_sub]
    exact (div_le_div_iff_of_pos_right hβ).mpr (by linarith)
  · rw [exp_clock_integral hβ.ne' hb hf]
    have hex : Real.exp (-regBeta a*U+regBeta a*u T)≤1 := Real.exp_le_one_iff.mpr (by
      have h := mul_le_mul_of_nonneg_left hU hβ.le
      dsimp only [u] at *
      linarith)
    have hnon := (Real.exp_pos (-regBeta a*U+regBeta a*u S)).le
    exact (div_le_div_iff_of_pos_right hβ).mpr (by linarith)
end ExactSLEGreen

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain
open scoped Classical
 

noncomputable def unfinishedCutoffTop {m : ℕ} (a : ℝ) (ha : 0<a)
    (z : Fin m → ℂ) (hz : ∀ i, 0<(z i).im)
    (ρ : Fin m → ℝ) (hρ : ∀ i, 0<ρ i) (hr : ∀ i, ρ i≤(z i).im)
    (n : ℕ) (b : ExactSLEGenerator.Driver) : ℝ≥0∞ :=
  min (n:ℝ≥0∞) (Finset.univ.inf fun i =>
    if (radialStop a ha (z i) (hz i) (ρ i) (hρ i) (hr i) n b : ℝ≥0∞)=radialTime a b.1 (z i) (ρ i)
    then ∞ else (radialStop a ha (z i) (hz i) (ρ i) (hρ i) (hr i) n b : ℝ≥0∞))
noncomputable def unfinishedCutoff {m : ℕ} (a : ℝ) (ha : 0<a)
    (z : Fin m → ℂ) (hz : ∀ i, 0<(z i).im)
    (ρ : Fin m → ℝ) (hρ : ∀ i, 0<ρ i) (hr : ∀ i, ρ i≤(z i).im)
    (n : ℕ) (b : ExactSLEGenerator.Driver) : ℝ≥0 := (unfinishedCutoffTop a ha z hz ρ hρ hr n b).toNNReal
end ExactSLEGreen

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace ExactSLEStops
variable {Ω : Type*} [MeasurableSpace Ω]
 
def insert (τ : Ω → ℝ≥0) : List (Ω → ℝ≥0) → List (Ω → ℝ≥0)
  | [] => [τ]
  | σ::l => (fun ω => min (τ ω) (σ ω)) :: insert (fun ω => max (τ ω) (σ ω)) l
def sort : List (Ω → ℝ≥0) → List (Ω → ℝ≥0)
  | [] => []
  | τ::l => insert τ (sort l)
omit [MeasurableSpace Ω] in
lemma insert_length (τ : Ω → ℝ≥0) (l : List (Ω → ℝ≥0)) :
    (insert τ l).length=l.length+1 := by
  induction l generalizing τ with
  | nil => rfl
  | cons σ l ih => simp only [insert,List.length_cons,ih]
omit [MeasurableSpace Ω] in
lemma sort_length (l : List (Ω → ℝ≥0)) : (sort l).length=l.length := by
  induction l with
  | nil => rfl
  | cons τ l ih => simp only [sort,insert_length,List.length_cons,ih]
lemma insert_stopping (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (τ : Ω → ℝ≥0) (l : List (Ω → ℝ≥0))
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (hl : ∀ σ ∈ l, IsStoppingTime F (fun ω => (σ ω : WithTop ℝ≥0))) :
    ∀ σ ∈ insert τ l, IsStoppingTime F (fun ω => (σ ω : WithTop ℝ≥0)) := by
  induction l generalizing τ with
  | nil => simpa only [insert,List.mem_singleton] using fun σ (h : σ=τ) => h ▸ hτ
  | cons π l ih =>
    intro σ hσ
    have hπ := hl π (by simp)
    rcases List.mem_cons.mp hσ with h|h
    · subst σ
      simpa only [WithTop.coe_min] using hτ.min hπ
    · apply ih (fun ω => max (τ ω) (π ω)) ?_ (fun σ h => hl σ (by simp [h])) σ h
      simpa only [WithTop.coe_max] using hτ.max hπ
lemma sort_stopping (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (l : List (Ω → ℝ≥0))
    (hl : ∀ σ ∈ l, IsStoppingTime F (fun ω => (σ ω : WithTop ℝ≥0))) :
    ∀ σ ∈ sort l, IsStoppingTime F (fun ω => (σ ω : WithTop ℝ≥0)) := by
  induction l with
  | nil => simp [sort]
  | cons τ l ih =>
    exact insert_stopping F τ (sort l) (hl τ (by simp)) (ih (fun σ h => hl σ (by simp [h])))
omit [MeasurableSpace Ω] in
lemma insert_perm (τ : Ω → ℝ≥0) (l : List (Ω → ℝ≥0)) (ω : Ω) :
    ((insert τ l).map (fun σ => σ ω)).Perm ((τ::l).map (fun σ => σ ω)) := by
  induction l generalizing τ with
  | nil => exact List.Perm.refl _
  | cons σ l ih =>
    simp only [insert,List.map_cons]
    have h := (ih (fun ω => max (τ ω) (σ ω))).cons (min (τ ω) (σ ω))
    rcases le_total (τ ω) (σ ω) with ht|ht
    · simpa only [List.map_cons,min_eq_left ht,max_eq_right ht] using h
    · simpa only [List.map_cons,min_eq_right ht,max_eq_left ht] using h.trans (List.Perm.swap _ _ _)
omit [MeasurableSpace Ω] in
lemma sort_perm (l : List (Ω → ℝ≥0)) (ω : Ω) :
    ((sort l).map (fun σ => σ ω)).Perm (l.map (fun σ => σ ω)) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons τ l ih => exact (insert_perm τ (sort l) ω).trans (ih.cons (τ ω))
omit [MeasurableSpace Ω] in
lemma insert_sorted (τ : Ω → ℝ≥0) (l : List (Ω → ℝ≥0)) (ω : Ω)
    (hl : ((l.map (fun σ => σ ω))).Pairwise (· ≤ ·)) :
    ((insert τ l).map (fun σ => σ ω)).Pairwise (· ≤ ·) := by
  induction l generalizing τ with
  | nil => simp [insert]
  | cons σ l ih =>
    simp only [List.map_cons,List.pairwise_cons] at hl
    simp only [insert,List.map_cons,List.pairwise_cons]
    refine ⟨?_,ih _ hl.2⟩
    intro x hx
    have hx' := (insert_perm (fun ω => max (τ ω) (σ ω)) l ω).mem_iff.mp hx
    simp only [List.map_cons,List.mem_cons] at hx'
    rcases hx' with rfl|hx'
    · exact (min_le_left _ _).trans (le_max_left _ _)
    · exact (min_le_right _ _).trans (hl.1 x hx')
omit [MeasurableSpace Ω] in
lemma sort_sorted (l : List (Ω → ℝ≥0)) (ω : Ω) :
    ((sort l).map (fun σ => σ ω)).Pairwise (· ≤ ·) := by
  induction l with
  | nil => simp [sort]
  | cons τ l ih => exact insert_sorted τ (sort l) ω ih
 
omit [MeasurableSpace Ω] in
lemma no_change_between (l : List (Ω → ℝ≥0)) (ω : Ω) (k : ℕ)
    (hk : k+1<(sort l).length) (τ : Ω → ℝ≥0) (hτ : τ∈l) :
    τ ω ≤ (sort l)[k] ω ∨ (sort l)[k+1] ω ≤ τ ω := by
  let v := (sort l).map (fun σ => σ ω)
  have hv : v.Pairwise (· ≤ ·) := sort_sorted l ω
  have ht : τ ω∈v := (sort_perm l ω).mem_iff.mpr (List.mem_map_of_mem hτ)
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem ht
  have hm := List.pairwise_iff_getElem.mp hv
  by_cases hik : i≤k
  · left
    rcases hik.eq_or_lt with rfl|hi'
    · simpa [v] using he.symm.le
    · have h := hm i k hi (by simpa [v] using (Nat.lt_of_succ_lt hk)) hi'
      rw [he] at h
      simpa only [v,List.getElem_map] using h
  · right
    have hki : k+1 ≤ i := Nat.succ_le_of_lt (lt_of_not_ge hik)
    rcases hki.eq_or_lt with heq|hlt
    · subst i
      simpa [v] using he.le
    · have h := hm (k+1) i (by simpa [v] using hk) hi hlt
      rw [he] at h
      simpa only [v,List.getElem_map] using h
end ExactSLEStops
namespace ExactSLEStops
open Set Filter
open scoped Classical
variable {Ω : Type*} [MeasurableSpace Ω]
lemma deferred_stopping (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime F τ) (A : Set Ω)
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    IsStoppingTime F (fun ω => if ω∈A then ∞ else τ ω) := by
  intro t
  change MeasurableSet[F t] {ω | (if ω∈A then ∞ else τ ω)≤(t:ℝ≥0∞)}
  have he : {ω | (if ω∈A then ∞ else τ ω)≤(t:ℝ≥0∞)}=Aᶜ∩{ω | τ ω≤(t:ℝ≥0∞)} := by
    ext ω
    by_cases h : ω∈A <;> simp [h]
  rw [he]
  exact (hτ.measurableSet Aᶜ).mp hA.compl |>.2 t
lemma finset_inf_stopping {ι : Type*} (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (s : Finset ι) (τ : ι → Ω → ℝ≥0∞)
    (hτ : ∀ i∈s, IsStoppingTime F (τ i)) :
    IsStoppingTime F (fun ω => s.inf fun i => τ i ω) := by
  induction s using Finset.induction_on with
  | empty =>
    intro t
    change MeasurableSet[F t] {ω | ((∅ : Finset ι).inf fun i => τ i ω)≤(t:ℝ≥0∞)}
    simp
  | @insert i s hi ih =>
    have h := (hτ i (Finset.mem_insert_self _ _)).min (ih fun j hj => hτ j (Finset.mem_insert_of_mem hj))
    intro t
    change MeasurableSet[F t] {ω | ((Insert.insert i s).inf fun i => τ i ω)≤(t:ℝ≥0∞)}
    have hh := h t
    change MeasurableSet[F t] {ω | min (τ i ω) (s.inf fun i => τ i ω)≤(t:ℝ≥0∞)} at hh
    simpa only [Finset.inf_insert] using hh
omit [MeasurableSpace Ω] in
lemma sort_bounded (l : List (Ω → ℝ≥0)) (B : Ω → ℝ≥0)
    (hl : ∀ τ∈l, ∀ ω, τ ω≤B ω) : ∀ τ∈sort l, ∀ ω, τ ω≤B ω := by
  intro τ hτ ω
  have h : τ ω∈l.map (fun σ => σ ω) :=
    (sort_perm l ω).mem_iff.mp (List.mem_map_of_mem hτ)
  obtain ⟨σ,hσ,he⟩ := List.mem_map.mp h
  exact he ▸ hl σ hσ ω
end ExactSLEStops

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain ExactSLEStops
open scoped Classical
lemma unfinishedCutoffTop_le {m : ℕ} (a : ℝ) (ha : 0<a)
    (z : Fin m → ℂ) (hz : ∀ i, 0<(z i).im)
    (ρ : Fin m → ℝ) (hρ : ∀ i, 0<ρ i) (hr : ∀ i, ρ i≤(z i).im)
    (n : ℕ) (b : ExactSLEGenerator.Driver) : unfinishedCutoffTop a ha z hz ρ hρ hr n b≤n := min_le_left _ _
lemma unfinishedCutoff_coe {m : ℕ} (a : ℝ) (ha : 0<a)
    (z : Fin m → ℂ) (hz : ∀ i, 0<(z i).im)
    (ρ : Fin m → ℝ) (hρ : ∀ i, 0<ρ i) (hr : ∀ i, ρ i≤(z i).im)
    (n : ℕ) (b : ExactSLEGenerator.Driver) :
    (unfinishedCutoff a ha z hz ρ hρ hr n b : ℝ≥0∞)=unfinishedCutoffTop a ha z hz ρ hρ hr n b := by
  exact ENNReal.coe_toNNReal (ne_top_of_le_ne_top (by simp) (unfinishedCutoffTop_le a ha z hz ρ hρ hr n b))
lemma unfinishedCutoff_stopping {m : ℕ} (a : ℝ) (ha : 0<a)
    (z : Fin m → ℂ) (hz : ∀ i, 0<(z i).im)
    (ρ : Fin m → ℝ) (hρ : ∀ i, 0<ρ i) (hr : ∀ i, ρ i≤(z i).im) (n : ℕ) :
    IsStoppingTime rawFiltration (fun b => (unfinishedCutoff a ha z hz ρ hρ hr n b : WithTop ℝ≥0)) := by
  have htop : IsStoppingTime rawFiltration (unfinishedCutoffTop a ha z hz ρ hρ hr n) := by
    apply (isStoppingTime_const rawFiltration (n:ℝ≥0)).min
    apply finset_inf_stopping
    intro i hi
    let A := {b | (radialStop a ha (z i) (hz i) (ρ i) (hρ i) (hr i) n b : ℝ≥0∞)=radialTime a b.1 (z i) (ρ i)}
    have htau := radialStop_stopping a ha (z i) (hz i) (ρ i) (hρ i) (hr i) n
    have hA : MeasurableSet[htau.measurableSpace] A := htau.measurableSet_eq_stopping_time
      (radialTime_stopping a ha (z i) (hz i) (ρ i) (hρ i) (hr i))
    intro t
    change MeasurableSet[rawFiltration t] {b | (if (radialStop a ha (z i) (hz i) (ρ i) (hρ i) (hr i) n b : ℝ≥0∞)=radialTime a b.1 (z i) (ρ i) then ∞ else (radialStop a ha (z i) (hz i) (ρ i) (hρ i) (hr i) n b : ℝ≥0∞))≤(t:ℝ≥0∞)}
    have hd := ((htau.measurableSet Aᶜ).mp hA.compl).2 t
    convert hd using 1
    ext b
    by_cases he : b∈A
    · simp only [A,Set.mem_ofPred_eq] at he
      simp [he,A]
      try exact WithTop.coe_le_coe.symm
    · simp only [A,Set.mem_ofPred_eq] at he
      simp [he,A]
      try exact WithTop.coe_le_coe.symm

  intro t
  have h := htop t
  change MeasurableSet[rawFiltration t] {b | unfinishedCutoffTop a ha z hz ρ hρ hr n b≤(t:ℝ≥0∞)} at h
  change MeasurableSet[rawFiltration t] {b | (unfinishedCutoff a ha z hz ρ hρ hr n b : ℝ≥0∞)≤(t:ℝ≥0∞)}
  simpa only [unfinishedCutoff_coe] using h
lemma unfinishedCutoff_before_individual {m : ℕ} (a : ℝ) (ha : 0<a)
    (z : Fin m → ℂ) (hz : ∀ i, 0<(z i).im)
    (ρ : Fin m → ℝ) (hρ : ∀ i, 0<ρ i) (hr : ∀ i, ρ i≤(z i).im)
    (n : ℕ) (b : ExactSLEGenerator.Driver) (t : ℝ≥0) (i : Fin m)
    (ht : t≤unfinishedCutoff a ha z hz ρ hρ hr n b)
    (hti : (t:ℝ≥0∞)≤radialTime a b.1 (z i) (ρ i)) :
    t≤radialStop a ha (z i) (hz i) (ρ i) (hρ i) (hr i) n b := by
  by_cases he : (radialStop a ha (z i) (hz i) (ρ i) (hρ i) (hr i) n b : ℝ≥0∞)=radialTime a b.1 (z i) (ρ i)
  · exact ENNReal.coe_le_coe.mp (by rw [he]; exact hti)
  · have hb : unfinishedCutoffTop a ha z hz ρ hρ hr n b≤
        (radialStop a ha (z i) (hz i) (ρ i) (hρ i) (hr i) n b : ℝ≥0∞) := by
      apply (min_le_right _ _).trans
      have h := Finset.inf_le (s:=Finset.univ) (f:=fun j =>
        if (radialStop a ha (z j) (hz j) (ρ j) (hρ j) (hr j) n b : ℝ≥0∞)=radialTime a b.1 (z j) (ρ j)
        then ∞ else (radialStop a ha (z j) (hz j) (ρ j) (hρ j) (hr j) n b : ℝ≥0∞)) (Finset.mem_univ i)
      simpa only [ite_eq_right he] using h
    exact ENNReal.coe_le_coe.mp ((ENNReal.coe_le_coe.mpr ht).trans (by rw [unfinishedCutoff_coe]; exact hb))
end ExactSLEGreen
end

end OAI
