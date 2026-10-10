import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.ActualCutoffCoordinates

namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma dyadicFactor_curve_log_bound {C : ℝ}
    (hC : ∀ n : ℕ, ∀ x : ℝ, |x*deriv (dyadicFactor n) x|≤C)
    {g : ℝ → ℝ} {t : ℝ} (hg : DifferentiableAt ℝ g t) (hx : 0<g t) (n : ℕ) :
    |deriv (fun r => dyadicFactor n (g r)) t|≤C*|deriv g t/g t| := by
  change |deriv (dyadicFactor n ∘ g) t| ≤ _
  rw [deriv_comp t ((contDiff_dyadicFactor n).differentiable (by simp) (g t)) hg]
  calc
    _ = |(g t*deriv (dyadicFactor n) (g t))*(deriv g t/g t)| := by
      congr 1
      field_simp [hx.ne']
    _ = |g t*deriv (dyadicFactor n) (g t)| * |deriv g t/g t| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (hC n (g t)) (abs_nonneg _)

lemma dyadicMultiFactor_curve_zero_derivative {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} (n : ι→ℕ)
    (hz : dyadicMultiFactor n (fun i => g i t)=0) :
    deriv (fun r => dyadicMultiFactor n (fun i => g i r)) t=0 := by
  apply IsLocalMin.deriv_eq_zero
  exact Filter.Eventually.of_forall (fun r => by
    dsimp only
    rw [hz]
    exact dyadicMultiFactor_nonneg _ _)

lemma dyadicMultiFactor_curve_log_bound {C : ℝ}
    (hC : ∀ n : ℕ, ∀ x : ℝ, |x*deriv (dyadicFactor n) x|≤C)
    {ι : Type*} [Fintype ι] {g : ι → ℝ → ℝ} {t : ℝ}
    (hg : ∀ i, DifferentiableAt ℝ (g i) t) (hx : ∀ i, 0<g i t) (n : ι→ℕ) :
    |deriv (fun r => dyadicMultiFactor n (fun i => g i r)) t| ≤
      C * ∑ i, |deriv (g i) t/g i t| := by
  classical
  have hd (i : ι) : DifferentiableAt ℝ (fun r => dyadicFactor (n i) (g i r)) t :=
    ((contDiff_dyadicFactor (n i)).differentiable (by simp) (g i t)).comp t (hg i)
  unfold dyadicMultiFactor
  dsimp only
  rw [deriv_fun_finsetProd (u:=Finset.univ) (fun i _ => hd i)]
  simp only [smul_eq_mul]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hp0 : 0≤∏ j∈Finset.univ.erase i,dyadicFactor (n j) (g j t) :=
    Finset.prod_nonneg (fun j _ => dyadicFactor_nonneg _ _)
  have hp1 : (∏ j∈Finset.univ.erase i,dyadicFactor (n j) (g j t))≤1 :=
    Finset.prod_le_one₀ (fun j _ => dyadicFactor_nonneg _ _) (fun j _ => dyadicFactor_le_one _ _)
  rw [abs_mul,abs_of_nonneg hp0]
  exact (mul_le_of_le_one_left (abs_nonneg _) hp1).trans
    (dyadicFactor_curve_log_bound hC (hg i) (hx i) (n i))

lemma dyadicMultiFactor_curve_indicator_bound {C : ℝ}
    (hC : ∀ n : ℕ, ∀ x : ℝ, |x*deriv (dyadicFactor n) x|≤C)
    {ι : Type*} [Fintype ι] {g : ι → ℝ → ℝ} {t : ℝ}
    (hg : ∀ i, DifferentiableAt ℝ (g i) t) (hx : ∀ i, 0<g i t) (n : ι→ℕ) :
    |deriv (fun r => dyadicMultiFactor n (fun i => g i r)) t| ≤
      {r | ∀ i,DyadicBand (n i) (g i r)}.indicator
        (fun _ => C * ∑ i, |deriv (g i) t/g i t|) t := by
  classical
  by_cases hb : ∀ i,DyadicBand (n i) (g i t)
  · change t∈{r | ∀ i,DyadicBand (n i) (g i r)} at hb
    rw [indicator_of_mem hb]
    exact dyadicMultiFactor_curve_log_bound hC hg hx n
  · change t∉{r | ∀ i,DyadicBand (n i) (g i r)} at hb
    rw [indicator_of_notMem hb]
    have hz : dyadicMultiFactor n (fun i => g i t)=0 := by
      by_contra hn
      exact hb (dyadicMultiFactor_positive_bands (lt_of_le_of_ne (dyadicMultiFactor_nonneg _ _) (Ne.symm hn)))
    rw [dyadicMultiFactor_curve_zero_derivative n hz,abs_zero]

lemma selected_dyadic_derivative_indicator_bound {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} (hg : ∀ i,DifferentiableAt ℝ (g i) t)
    (hx : ∀ i,0<g i t) (N : ℕ) (h1 : ∀ i,g i t≤1) (hN : ∀ i,2≤(2:ℝ)^N*g i t)
    (S : Finset (ι→ℕ)) (hS : S⊆dyadicBox ι N) :
    ∃ C : ℝ, 0≤C ∧
      |deriv (fun r => ∑ n∈S,dyadicMultiFactor n (fun i => g i r)) t| ≤
      ∑ n∈dyadicBox ι N \ S,{r | ∀ i,DyadicBand (n i) (g i r)}.indicator
        (fun _ => C * ∑ i,|deriv (g i) t/g i t|) t := by
  classical
  obtain ⟨C,hC,hbound⟩ := dyadicFactor_log_derivative_bound
  refine ⟨C,hC,?_⟩
  rw [selected_dyadic_derivative_cancel hg N h1 hN S hS,abs_neg]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun n _ => dyadicMultiFactor_curve_indicator_bound hbound hg hx n))

def momentumDirection (v : Vec) : Vec := ‖v‖⁻¹ • v

lemma momentumDirection_norm {v : Vec} (hv : v ≠ 0) : ‖momentumDirection v‖=1 := by
  simp [momentumDirection,norm_smul,norm_ne_zero_iff.mpr hv]

lemma hasDerivAt_momentumDirection {V : ℝ → Vec} {K : Vec} {t : ℝ}
    (hV : HasDerivAt V K t) (hv : V t ≠ 0) :
    HasDerivAt (momentumDirection ∘ V)
      (‖V t‖⁻¹ • transverseProjection (V t) K) t := by
  have hn := hasDerivAt_norm_nonzero hV hv
  have hh := (hn.inv (norm_ne_zero_iff.mpr hv)).smul hV
  convert hh using 1 <;> try rfl
  ext i
  simp only [Pi.inv_apply,transverseProjection,velocityProjection,dot_smul_left,
      PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,smul_eq_mul]
  field_simp
  ring

def angularMultiplier (w : ℝ) (v h : Vec) : Vec :=
  (w/‖v‖) • transverseProjection v h

lemma hasDerivAt_angularMultiplier {V : ℝ → Vec} {K : Vec} {t : ℝ}
    (hV : HasDerivAt V K t) (hv : V t ≠ 0) (w : ℝ) (h : Vec) :
    HasDerivAt (fun r => angularMultiplier w (V r) h)
      ((-w/‖V t‖^2) •
        (dot (momentumDirection (V t)) K • transverseProjection (V t) h +
         dot (momentumDirection (V t)) h • transverseProjection (V t) K +
         dot (transverseProjection (V t) K) h • momentumDirection (V t))) t := by
  have hn := hasDerivAt_norm_nonzero hV hv
  have hξ := hasDerivAt_momentumDirection hV hv
  have hP := (hasDerivAt_const t h).sub
    ((hasDerivAt_dot hξ (hasDerivAt_const t h)).smul hξ)
  have hh := ((hasDerivAt_const t w).div hn (norm_ne_zero_iff.mpr hv)).smul hP
  convert hh using 1 <;> try rfl
  ext i
  simp only [Pi.div_apply,Pi.sub_apply,Pi.smul_apply',momentumDirection,transverseProjection,velocityProjection,dot_smul_left,
      dot_sub_left,dot_zero_right_rvm,Function.comp_apply,zero_add,zero_sub,
      PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,PiLp.neg_apply,smul_eq_mul,
      zero_mul]
  field_simp
  ring

lemma angularMultiplier_derivative_bound (w : ℝ) (v K h : Vec) (hv : v ≠ 0) :
    ‖(-w/‖v‖^2) •
        (dot (momentumDirection v) K • transverseProjection v h +
         dot (momentumDirection v) h • transverseProjection v K +
         dot (transverseProjection v K) h • momentumDirection v)‖ ≤
      3*|w|/‖v‖^2*‖K‖*‖h‖ := by
  have hξ := momentumDirection_norm hv
  have ha : |dot (momentumDirection v) K| ≤ ‖K‖ := by simpa only [hξ,one_mul] using abs_dot_le (momentumDirection v) K
  have hb : |dot (momentumDirection v) h| ≤ ‖h‖ := by simpa only [hξ,one_mul] using abs_dot_le (momentumDirection v) h
  have hc : |dot (transverseProjection v K) h| ≤ ‖K‖*‖h‖ :=
    (abs_dot_le _ _).trans (mul_le_mul_of_nonneg_right (transverseProjection_norm _ _) (norm_nonneg _))
  have hsum : ‖dot (momentumDirection v) K • transverseProjection v h +
         dot (momentumDirection v) h • transverseProjection v K +
         dot (transverseProjection v K) h • momentumDirection v‖ ≤ 3*‖K‖*‖h‖ := by
    calc
      _ ≤ ‖dot (momentumDirection v) K • transverseProjection v h‖ +
          ‖dot (momentumDirection v) h • transverseProjection v K‖ +
          ‖dot (transverseProjection v K) h • momentumDirection v‖ := norm_add₃_le
      _ ≤ ‖K‖*‖h‖+‖h‖*‖K‖+‖K‖*‖h‖ := by
        simp only [norm_smul,Real.norm_eq_abs,hξ,mul_one]
        exact add_le_add (add_le_add (mul_le_mul ha (transverseProjection_norm _ _) (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul hb (transverseProjection_norm _ _) (norm_nonneg _) (norm_nonneg _))) hc
      _ = _ := by ring
  rw [norm_smul,Real.norm_eq_abs,abs_div,abs_neg,abs_sq]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by ring)

lemma dyadicBand_multi_card_le {ι : Type*} [Fintype ι] (S : Finset (ι→ℕ)) {x : ι→ℝ}
    (hS : ∀ n∈S,∀ i,DyadicBand (n i) (x i)) : S.card≤5^Fintype.card ι := by
  classical
  let A : ι→Finset ℕ := fun i=>S.image (fun n=>n i)
  have hA : ∀ i,(A i).card≤5 := by
    intro i
    apply dyadicBand_card_le
    intro n hn
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    exact hS m hm i
  calc
    S.card ≤ (Fintype.piFinset A).card := Finset.card_le_card (by
      intro n hn
      exact Fintype.mem_piFinset.mpr (fun i=>Finset.mem_image.mpr ⟨n,hn,rfl⟩))
    _ = ∏ i,(A i).card := Fintype.card_piFinset A
    _ ≤ ∏ _i : ι,5 := Finset.prod_le_prod (fun i _=>hA i)
    _ = _ := by simp

lemma selectedDyadicCutoff_uniform_log_bound {C : ℝ}
    (hC0 : 0≤C) (hC : ∀ n : ℕ,∀ x : ℝ,|x*deriv (dyadicFactor n) x|≤C)
    {ι : Type*} [Fintype ι] {g : ι→ℝ→ℝ} {t : ℝ}
    (hg : ∀ i,DifferentiableAt ℝ (g i) t) (hp : ∀ i,0<g i t) (S : Set (ι→ℕ)) :
    |deriv (fun r=>selectedDyadicCutoff S (fun i=>g i r)) t| ≤
      (5:ℝ)^Fintype.card ι*C*∑ i,|deriv (g i) t/g i t| := by
  classical
  obtain ⟨N,_hN,he⟩ := selectedDyadicCutoff_curve_eventually (fun i=>(hg i).continuousAt) hp S
  rw [he.deriv_eq,deriv_fun_sum (fun n _=>differentiableAt_dyadicMultiFactor_curve hg n)]
  let A := (selectedDyadicBox N S).filter (fun n=>∀ i,DyadicBand (n i) (g i t))
  have hac : A.card≤5^Fintype.card ι := dyadicBand_multi_card_le A
    (fun n hn=>(Finset.mem_filter.mp hn).2)
  have hz (n : ι→ℕ) (hnb : ¬∀ i,DyadicBand (n i) (g i t)) :
      deriv (fun r=>dyadicMultiFactor n (fun i=>g i r)) t=0 := by
    apply dyadicMultiFactor_curve_zero_derivative
    by_contra h
    exact hnb (dyadicMultiFactor_positive_bands
      (lt_of_le_of_ne (dyadicMultiFactor_nonneg _ _) (Ne.symm h)))
  have heq : (∑ n∈selectedDyadicBox N S,deriv (fun r=>dyadicMultiFactor n (fun i=>g i r)) t)=
      ∑ n∈A,deriv (fun r=>dyadicMultiFactor n (fun i=>g i r)) t := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hna
    exact hz n (by simpa only [A,Finset.mem_filter,hn,true_and] using hna)
  rw [heq]
  calc
    _ ≤ ∑ n∈A,|deriv (fun r=>dyadicMultiFactor n (fun i=>g i r)) t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n∈A,C*∑ i,|deriv (g i) t/g i t| :=
      Finset.sum_le_sum (fun n _=>dyadicMultiFactor_curve_log_bound hC hg hp n)
    _ = (A.card:ℝ)*(C*∑ i,|deriv (g i) t/g i t|) := by simp
    _ ≤ (5:ℝ)^Fintype.card ι*(C*∑ i,|deriv (g i) t/g i t|) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hac
    _ = _ := by ring

lemma selectedDyadicCutoff_mem_unit {ι : Type*} [Fintype ι] {x : ι→ℝ}
    (hp : ∀ i,0<x i) (h1 : ∀ i,x i≤1) (S : Set (ι→ℕ)) :
    selectedDyadicCutoff S x∈Icc (0:ℝ) 1 := by
  classical
  obtain ⟨N,hN,he⟩ := selectedDyadicCutoff_curve_eventually
    (t:=0) (g:=fun i (_r : ℝ)=>x i) (fun _=>continuousAt_const) hp S
  have hh := he.eq_of_nhds
  change selectedDyadicCutoff S x = ∑ n∈selectedDyadicBox N S,dyadicMultiFactor n x at hh
  rw [hh]
  refine ⟨Finset.sum_nonneg (fun n _=>dyadicMultiFactor_nonneg n x),?_⟩
  calc
    _ ≤ ∑ n∈dyadicBox ι N,dyadicMultiFactor n x := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun n _ _=>dyadicMultiFactor_nonneg n x)
    _ = 1 := sum_dyadicMultiFactor_eq_one N x h1 hN

lemma physical_cutoff_logarithmic_rates {T t : ℝ} {V W N : ℝ→Vec} {R : ℝ→ℝ}
    {E B K : Vec} (hn : ‖N t‖=1) (hr : 0<R t)
    (hsmall : 1-dot (N t) (velocity (V t))≤1-dot (N t) (velocity (W t)))
    (hV : HasDerivAt V (E+cross (velocity (V t)) B) t)
    (hW : HasDerivAt W
      (((1-dot (N t) (velocity (V t)))/(1-dot (N t) (velocity (W t)))) • K) t)
    (hN : HasDerivAt N ((R t)⁻¹ • coneMotion (velocity (W t)) (velocity (V t)) (N t)) t)
    (hR : HasDerivAt R
      ((1-dot (N t) (velocity (V t)))/(1-dot (N t) (velocity (W t)))-1) t) :
    let θ := Real.sqrt ((1-dot (N t) (velocity (V t)))/2)
    let φ := Real.sqrt ((1-dot (N t) (velocity (W t)))/2)
    ∑ i : Fin 4,|deriv (fun s=>physicalCutoffCoordinates T (R s) (N s) (V s) (W s) i) t /
        physicalCutoffCoordinates T (R t) (N t) (V t) (W t) i| ≤
      (3/q (V t))*(goodField E B (N t)/θ+θ*‖B‖)+5/R t+θ^2*‖K‖/(q (W t)*φ^3) := by
  let d := 1-dot (N t) (velocity (V t))
  let D := 1-dot (N t) (velocity (W t))
  let U := fderiv ℝ velocity (V t) (E+cross (velocity (V t)) B)
  let A := fderiv ℝ velocity (W t) K
  let M := (R t)⁻¹ • coneMotion (velocity (W t)) (velocity (V t)) (N t)
  have hdpos : 0<d := cone_denom_pos _ _ hn
  have hDpos : 0<D := cone_denom_pos _ _ hn
  have hu : HasDerivAt (fun s=>velocity (V s)) U t :=
    ((contDiff_velocity (k:=1)).differentiable one_ne_zero (V t)).hasFDerivAt.comp_hasDerivAt t hV
  have ha : HasDerivAt (fun s=>velocity (W s)) ((d/D) • A) t := by
    convert ((contDiff_velocity (k:=1)).differentiable one_ne_zero (W t)).hasFDerivAt.comp_hasDerivAt t hW using 1 <;> try rfl
    simp only [map_smul]
    rfl
  have hd : HasDerivAt (fun s=>1-dot (N s) (velocity (V s)))
      (-(dot M (velocity (V t))+dot (N t) U)) t := by
    have hh := (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_dot hN hu)
    convert hh using 1
    try rfl
    simp only [zero_sub]
    exact congrArg Neg.neg (add_comm _ _)
  have hD : HasDerivAt (fun s=>1-dot (N s) (velocity (W s)))
      (-(dot M (velocity (W t))+(d/D)*dot (N t) A)) t := by
    have hh := (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_dot hN ha)
    convert hh using 1
    try rfl
    simp only [zero_sub,dot_smul_right]
    exact congrArg Neg.neg (add_comm _ _)
  have hdf : HasDerivAt (fun s=>1-dot (N t) (velocity (V s))) (-dot (N t) U) t := by
    have hh := (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_dot (hasDerivAt_const t (N t)) hu)
    convert hh using 1
    try rfl
    simp only [zero_sub,dot_zero_left_rvm,add_zero]
  have hed := angularCoordinate_log_deriv hd hdpos
  have heD := angularCoordinate_log_deriv hD hDpos
  have hef := angularCoordinate_log_deriv hdf hdpos
  have heq := inverseCoordinate_log_deriv (hasDerivAt_lorentz_energy hV) (q_pos (V t))
  have her : deriv (fun s=>R s/max 1 T) t/(R t/max 1 T)=(d/D-1)/R t := by
    rw [(hR.div_const (max 1 T)).deriv]
    have hm : max 1 T≠0 := (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)).ne'
    change ((d/D-1)/max 1 T)/(R t/max 1 T)=(d/D-1)/R t
    field_simp
  have hsrc := source_cutoff_logarithmic_rates hV hn
  dsimp only at hsrc
  rw [heq,hef] at hsrc
  have hgeo := geometric_cutoff_logarithmic_rates hn hr hsmall
  have hrec := receiver_cutoff_logarithmic_rate (V t) (W t) K (N t) hn
  have hsplitd : |-(dot M (velocity (V t))+dot (N t) U)/(2*d)| ≤
      |dot M (velocity (V t))/(2*d)|+|-dot (N t) U/(2*d)| := by
    have he : -(dot M (velocity (V t))+dot (N t) U)/(2*d)=
        -(dot M (velocity (V t))/(2*d))+(-dot (N t) U/(2*d)) := by ring
    rw [he]
    exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
  have hsplitD : |-(dot M (velocity (W t))+(d/D)*dot (N t) A)/(2*D)| ≤
      |dot M (velocity (W t))/(2*D)|+|dot (N t) A*(d/D)/(2*D)| := by
    rw [neg_div,abs_neg,add_div]
    exact (abs_add_le _ _).trans_eq (by rw [mul_comm (d/D)])
  dsimp only at hsrc hgeo hrec ⊢
  simp only [Fin.sum_univ_succ,Fin.isValue,physicalCutoffCoordinates,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero]
  rw [heq,hed,heD,her]
  change |-dot (velocity (V t)) E/q (V t)|+
    (|-(dot M (velocity (V t))+dot (N t) U)/(2*d)|+
      (|-(dot M (velocity (W t))+(d/D)*dot (N t) A)/(2*D)|+|(d/D-1)/R t|)) ≤ _
  dsimp only [d,D,U,A,M] at hsplitd hsplitD
  linarith

def sourceRepresentative (n : ℕ) : ℝ := 64*(2:ℝ)^n

def cappedRepresentative (n : ℕ) : ℝ := (2:ℝ)⁻¹^n

lemma dyadicBand_capped_range {n : ℕ} {x : ℝ} (h : DyadicBand n x) :
    cappedRepresentative n/2≤x ∧ x≤2*cappedRepresentative n := by
  have hp : 0<(2:ℝ)^n := by positivity
  have he : cappedRepresentative n = ((2:ℝ)^n)⁻¹ := by simp [cappedRepresentative,inv_pow]
  rw [he]
  constructor
  · rw [inv_eq_one_div,div_div]
    exact (div_le_iff₀ (mul_pos hp (by norm_num))).mpr (by nlinarith [h.1])
  · rw [inv_eq_one_div,mul_one_div]
    exact (le_div_iff₀ hp).mpr (by nlinarith [h.2])

lemma dyadicBand_source_range {n : ℕ} {v : Vec} (h : DyadicBand n (1/q v)) :
    sourceRepresentative n/128≤q v ∧ q v≤ sourceRepresentative n/32 := by
  have hlo := h.1
  have hhi := h.2
  rw [mul_one_div] at hlo hhi
  have ha := (le_div_iff₀ (q_pos v)).mp hlo
  have hb := (div_le_iff₀ (q_pos v)).mp hhi
  dsimp [sourceRepresentative]
  constructor <;> linarith

lemma sourceRepresentative_mem_range {n : ℕ} {v : Vec} {P : ℝ}
    (h : DyadicBand n (1/q v)) (hP : 1024*q v≤P) :
    sourceRepresentative n∈Icc (64:ℝ) P := by
  have hh := dyadicBand_source_range h
  have hp : (1:ℝ)≤(2:ℝ)^n := one_le_pow₀ (by norm_num)
  constructor
  · dsimp [sourceRepresentative]; linarith
  · nlinarith [q_pos v]

lemma dyadicBand_angular_range {n : ℕ} {d : ℝ} (hd : 0≤d)
    (h : DyadicBand n (Real.sqrt (d/2))) :
    (cappedRepresentative n)^2/2≤d ∧ d≤8*(cappedRepresentative n)^2 := by
  have hh := dyadicBand_capped_range h
  have hp : 0<cappedRepresentative n := by dsimp [cappedRepresentative]; positivity
  have hs := Real.sq_sqrt (by positivity : 0≤d/2)
  have hn := Real.sqrt_nonneg (d/2)
  have hlo := mul_self_le_mul_self (by positivity : 0≤cappedRepresentative n/2) hh.1
  have hhi := mul_self_le_mul_self hn hh.2
  constructor <;> nlinarith

lemma dyadicBand_radius_range {n : ℕ} {T r : ℝ}
    (h : DyadicBand n (r/max 1 T)) :
    max 1 T*cappedRepresentative n/2≤r ∧ r≤2*max 1 T*cappedRepresentative n := by
  have hm : 0 < max (1:ℝ) T := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hh := dyadicBand_capped_range h
  have ha := (le_div_iff₀ hm).mp hh.1
  have hb := (div_le_iff₀ hm).mp hh.2
  constructor <;> nlinarith

lemma PhaseFlowOn.retardedMomentum_hasDerivAt {E B : Field} {T σ : ℝ}
    (F : PhaseFlowOn E B T) (zX zY : Phase)
    (hσ : σ∈branchDomain F.flow zX zY T)
    (hne : (F.flow zX σ).1≠(F.flow zY σ).1) :
    let τ := branchTime F.flow zX zY T
    let n := branchDirection F.flow zX zY T σ
    let d := 1-dot n (velocity (F.flow zY σ).2)
    let D := 1-dot n (velocity (F.flow zX (τ σ)).2)
    HasDerivAt (fun r=>(F.flow zX (τ r)).2)
      ((d/D) • (lorentzField E B (τ σ,F.flow zX (τ σ))).2) σ := by
  have ht := F.branch_time_mem zX zY hσ hne
  have hti : branchTime F.flow zX zY T σ∈Ioo 0 T := ⟨hσ.1.1.trans ht.1,ht.2⟩
  have hW : HasDerivAt (fun r=>(F.flow zX r).2)
      (lorentzField E B (branchTime F.flow zX zY T σ,F.flow zX (branchTime F.flow zX zY T σ))).2
      (branchTime F.flow zX zY T σ) :=
    ((F.ode zX _ (Ioo_subset_Icc_self hti)).hasDerivAt (Icc_mem_nhds hti.1 hti.2)).snd
  exact hW.scomp σ (F.branch_differential zX zY hσ hne).2

lemma PhaseFlowOn.actual_cutoff_logarithmic_rates {s : Solution} {T σ : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX zY : Phase)
    (hσ : σ∈branchDomain F.flow zX zY T)
    (hne : (F.flow zX σ).1≠(F.flow zY σ).1)
    (hsmall : 1-dot (branchDirection F.flow zX zY T σ) (velocity (F.flow zY σ).2)≤
      1-dot (branchDirection F.flow zX zY T σ) (velocity (F.flow zX (branchTime F.flow zX zY T σ)).2)) :
    let τ := branchTime F.flow zX zY T σ
    let n := branchDirection F.flow zX zY T σ
    let θ := Real.sqrt ((1-dot n (velocity (F.flow zY σ).2))/2)
    let φ := Real.sqrt ((1-dot n (velocity (F.flow zX τ).2))/2)
    let E := s.E (σ,(F.flow zY σ).1)
    let B := s.B (σ,(F.flow zY σ).1)
    let K := (lorentzField s.E s.B (τ,F.flow zX τ)).2
    ∑ i : Fin 4,|deriv (fun r=>actualCutoffCoordinates F.flow T zX zY r i) σ /
        actualCutoffCoordinates F.flow T zX zY σ i| ≤
      (3/q (F.flow zY σ).2)*(goodField E B n/θ+θ*‖B‖)+5/(τ-σ)+
        θ^2*‖K‖/(q (F.flow zX τ).2*φ^3) := by
  have ht := F.branch_time_mem zX zY hσ hne
  have hV := ((F.ode zY σ (Ioo_subset_Icc_self hσ.1)).hasDerivAt (Icc_mem_nhds hσ.1.1 hσ.1.2)).snd
  exact physical_cutoff_logarithmic_rates (F.branchDirection_norm zX zY hσ hne)
    (sub_pos.mpr ht.1) hsmall hV (F.retardedMomentum_hasDerivAt zX zY hσ hne)
    (F.branchDirection_hasDerivAt zX zY hσ hne)
    ((F.branch_differential zX zY hσ hne).2.sub (hasDerivAt_id σ))

def transverseCLM (v : Vec) : Vec→L[ℝ]Vec :=
  ContinuousLinearMap.id ℝ Vec -
    ((InnerProductSpace.toDual ℝ Vec) (momentumDirection v)).smulRight (momentumDirection v)

lemma transverseCLM_apply (v h : Vec) : transverseCLM v h=transverseProjection v h := by
  simp only [transverseCLM,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,InnerProductSpace.toDual_apply_apply,← dot_eq_inner]
  rfl

def angularMultiplierCLM (w : ℝ) (v : Vec) : Vec→L[ℝ]Vec := (w/‖v‖) • transverseCLM v

lemma angularMultiplierCLM_apply (w : ℝ) (v h : Vec) :
    angularMultiplierCLM w v h=angularMultiplier w v h := by
  simp only [angularMultiplierCLM,smul_apply,transverseCLM_apply,angularMultiplier]

lemma contDiffAt_transverseCLM {v : Vec} (hv : v≠0) {k : ℕ∞ω}
    (hk : k≤((⊤ : ℕ∞) : ℕ∞ω)) : ContDiffAt ℝ k transverseCLM v := by
  have hξ : ContDiffAt ℝ k momentumDirection v :=
    ((contDiffAt_id.norm ℝ hv).inv (norm_ne_zero_iff.mpr hv)).smul contDiffAt_id
  exact contDiffAt_const.sub (((InnerProductSpace.toDual ℝ Vec).contDiff.of_le hk).contDiffAt.comp v hξ |>.smulRight hξ)

lemma contDiffAt_angularMultiplierCLM (w : ℝ) {v : Vec} (hv : v≠0) {k : ℕ∞ω}
    (hk : k≤((⊤ : ℕ∞) : ℕ∞ω)) : ContDiffAt ℝ k (angularMultiplierCLM w) v := by
  exact (contDiffAt_const.div (contDiffAt_id.norm ℝ hv) (norm_ne_zero_iff.mpr hv)).smul
    (contDiffAt_transverseCLM hv hk)

def angularDerivativeCLM (w : ℝ) (v K : Vec) : Vec→L[ℝ] Vec :=
  (-w/‖v‖^2) •
    (dot (momentumDirection v) K • transverseCLM v +
     ((InnerProductSpace.toDual ℝ Vec) (momentumDirection v)).smulRight (transverseProjection v K) +
     ((InnerProductSpace.toDual ℝ Vec) (transverseProjection v K)).smulRight (momentumDirection v))

lemma angularDerivativeCLM_apply (w : ℝ) (v K h : Vec) :
    angularDerivativeCLM w v K h = (-w/‖v‖^2) •
      (dot (momentumDirection v) K • transverseProjection v h +
       dot (momentumDirection v) h • transverseProjection v K +
       dot (transverseProjection v K) h • momentumDirection v) := by
  simp only [angularDerivativeCLM,smul_apply,add_apply,
    transverseCLM_apply,ContinuousLinearMap.smulRight_apply,InnerProductSpace.toDual_apply_apply,← dot_eq_inner]

lemma hasDerivAt_angularMultiplierCLM {V : ℝ→Vec} {K : Vec} {t : ℝ}
    (hV : HasDerivAt V K t) (hv : V t≠0) (w : ℝ) :
    HasDerivAt (fun r=>angularMultiplierCLM w (V r)) (angularDerivativeCLM w (V t) K) t := by
  have hd := ((contDiffAt_angularMultiplierCLM w hv (k:=1) (by simp)).differentiableAt one_ne_zero).comp t hV.differentiableAt
  have he : deriv (fun r=>angularMultiplierCLM w (V r)) t=angularDerivativeCLM w (V t) K := by
    apply ContinuousLinearMap.ext
    intro h
    have hh := hd.hasDerivAt.clm_apply (hasDerivAt_const t h)
    simp only [ContinuousLinearMap.map_zero,add_zero,Function.comp_apply,angularMultiplierCLM_apply] at hh
    exact hh.unique (by simpa only [angularDerivativeCLM_apply] using hasDerivAt_angularMultiplier hV hv w h)
  rw [←he]
  exact hd.hasDerivAt

lemma angularDerivativeCLM_norm_le (w : ℝ) (v K : Vec) (hv : v≠0) :
    ‖angularDerivativeCLM w v K‖≤3*|w|/‖v‖^2*‖K‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  rw [angularDerivativeCLM_apply]
  exact angularMultiplier_derivative_bound w v K h hv

lemma continuousOn_momentumDirection {S : Set ℝ} {V : ℝ→Vec}
    (hV : ContinuousOn V S) (hne : ∀ t∈S,V t≠0) :
    ContinuousOn (fun t=>momentumDirection (V t)) S :=
  (hV.norm.inv₀ (fun t ht=>norm_ne_zero_iff.mpr (hne t ht))).smul hV

lemma continuousOn_transverseCLM {S : Set ℝ} {V : ℝ→Vec}
    (hV : ContinuousOn V S) (hne : ∀ t∈S,V t≠0) :
    ContinuousOn (fun t=>transverseCLM (V t)) S := by
  intro t ht
  exact ((contDiffAt_transverseCLM (hne t ht) (k:=0) (by simp)).continuousAt).comp_continuousWithinAt (hV t ht)

lemma continuousOn_transverseProjection {S : Set ℝ} {V K : ℝ→Vec}
    (hV : ContinuousOn V S) (hK : ContinuousOn K S) (hne : ∀ t∈S,V t≠0) :
    ContinuousOn (fun t=>transverseProjection (V t) (K t)) S := by
  simpa only [transverseCLM_apply] using (continuousOn_transverseCLM hV hne).clm_apply hK

lemma continuousOn_realTensor {S : Set ℝ} {V K : ℝ→Vec}
    (hV : ContinuousOn V S) (hK : ContinuousOn K S) :
    ContinuousOn (fun t=>((InnerProductSpace.toDual ℝ Vec) (V t)).smulRight (K t)) S := by
  have hd : ContinuousOn (fun t=>(InnerProductSpace.toDual ℝ Vec) (V t)) S :=
    (InnerProductSpace.toDual ℝ Vec).continuous.comp_continuousOn hV
  have hl : ContinuousOn (fun t=>ContinuousLinearMap.smulRightL ℝ Vec Vec ((InnerProductSpace.toDual ℝ Vec) (V t))) S :=
    (ContinuousLinearMap.smulRightL ℝ Vec Vec).continuous.comp_continuousOn hd
  exact hl.clm_apply hK

lemma continuousOn_angularDerivativeCLM {S : Set ℝ} {V K : ℝ→Vec}
    (hV : ContinuousOn V S) (hK : ContinuousOn K S) (hne : ∀ t∈S,V t≠0) (w : ℝ) :
    ContinuousOn (fun t=>angularDerivativeCLM w (V t) (K t)) S := by
  have hξ := continuousOn_momentumDirection hV hne
  have hP := continuousOn_transverseCLM hV hne
  have hPK := continuousOn_transverseProjection hV hK hne
  have hdot : ContinuousOn (fun t=>dot (momentumDirection (V t)) (K t)) S :=
    (contDiff_dot_pair (k:=0)).continuous.comp_continuousOn (hξ.prodMk hK)
  have ha := continuousOn_realTensor hξ hPK
  have hb := continuousOn_realTensor hPK hξ
  have hc : ContinuousOn (fun t=>(-w)/‖V t‖^2) S :=
    continuousOn_const.div (hV.norm.pow 2) (fun t ht=>pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne t ht)))
  exact hc.smul (((hdot.smul hP).add ha).add hb)



open MeasureTheory Set

open Filter Set
open scoped Topology

open scoped Topology Pointwise

open Set MeasureTheory Metric ODE
open scoped Topology NNReal

open scoped ContDiff

open Set MeasureTheory Metric

open Set MeasureTheory Metric Filter ODE

open Set MeasureTheory Filter Metric ODE

open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff

open Set MeasureTheory Filter

open scoped Topology ContDiff RealInnerProductSpace NNReal

open Set Filter MeasureTheory Metric

open scoped Topology ContDiff NNReal RealInnerProductSpace

open scoped Topology ContDiff NNReal ENNReal

open Set MeasureTheory
open scoped ENNReal

open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

open scoped Topology ContDiff ENNReal

open scoped Topology ContDiff NNReal

open scoped Topology ContDiff

open Set

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma sourceRepresentative_sum_bound {x : ℝ} (hx : 0≤x) (S : Finset ℕ)
    (hS : ∀n∈S,sourceRepresentative n≤x) : ∑n∈S,sourceRepresentative n≤2*x := by
  classical
  have hgeom (N : ℕ) : ∑n∈Finset.range (N+1),sourceRepresentative n≤2*sourceRepresentative N := by
    induction N with
    | zero => norm_num [sourceRepresentative]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have he : sourceRepresentative (N+1)=2*sourceRepresentative N := by
        dsimp only [sourceRepresentative]
        rw [pow_succ]
        ring
      rw [he]
      linarith
  by_cases hne : S.Nonempty
  · let N := S.max' hne
    have hsub : S⊆Finset.range (N+1) := by
      intro n hn
      apply Finset.mem_range.mpr
      have hh := S.le_max' n hn
      change n≤N at hh
      omega
    have hs : (∑n∈S,sourceRepresentative n)≤∑n∈Finset.range (N+1),sourceRepresentative n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>by dsimp only [sourceRepresentative]; positivity)
    exact hs.trans ((hgeom N).trans (mul_le_mul_of_nonneg_left (hS N (S.max'_mem hne)) (by norm_num)))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty]
    positivity

end RVM

end

end OAI
