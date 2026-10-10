import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Entropy.FineCharts

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma standardDerivativeProduct_quantitative (k : ℝ) (hk : 0≤k) :
    ∃ C : ℝ, 2≤C ∧ ∀ n : ℕ,
      (∀ z : ℂ, ‖standardDerivativeProduct k (complexProjection z) n‖≤C^n) ∧
      (∀ z w : ℂ, ‖standardDerivativeProduct k (complexProjection z) n-
        standardDerivativeProduct k (complexProjection w) n‖≤C^(3*n)*‖z-w‖) := by
  let D := 9*growthBase k
  let L := derivativeVariationBound k
  let C := 2+D+L
  have hD : 0≤D := by dsimp [D]; have := growthBase_ge_four k hk; positivity
  have hL : 0≤L := derivativeVariationBound_nonneg k
  have hC2 : 2≤C := by dsimp [C]; linarith
  have hC1 : 1≤C := by linarith
  have hC0 : 0≤C := by linarith
  have hDC : D≤C := by dsimp [C]; linarith
  refine ⟨C,hC2,?_⟩
  intro n
  induction n with
  | zero =>
    constructor
    · intro z; simp [standardDerivativeProduct]
    · intro z w; simp [standardDerivativeProduct]
  | succ n ih =>
    have hf : ∀ z w : ℂ, ‖(standardLift k)^[n] z-(standardLift k)^[n] w‖≤C^n*‖z-w‖ :=
      norm_sub_le_of_derivative_bound _ _ (hasFDerivAt_standardLift_iterate k n) ih.1
    constructor
    · intro z
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul ((standardDerivative_norm_bound k hk _).trans hDC) (ih.1 z)
          (norm_nonneg _) hC0).trans_eq (by rw [pow_succ]; ring))
    · intro z w
      let Az := standardDerivative k ((standardMap k)^[n] (complexProjection z))
      let Aw := standardDerivative k ((standardMap k)^[n] (complexProjection w))
      let Pz := standardDerivativeProduct k (complexProjection z) n
      let Pw := standardDerivativeProduct k (complexProjection w) n
      have he : Az.comp Pz-Aw.comp Pw=(Az-Aw).comp Pz+Aw.comp (Pz-Pw) := by
        ext v
        simp only [sub_apply,add_apply,ContinuousLinearMap.comp_apply,map_sub]
        abel
      have hdiff : ‖Az-Aw‖≤L*(C^n*‖z-w‖) := by
        have hh := standardDerivative_lift_sub_bound k ((standardLift k)^[n] z) ((standardLift k)^[n] w)
        rw [complexProjection_iterate,complexProjection_iterate] at hh
        exact hh.trans (mul_le_mul_of_nonneg_left (hf z w) hL)
      have hn : C^(2*n)≤C^(3*n) := pow_le_pow_right₀ hC1 (by omega)
      have hsum : L*C^(2*n)+D*C^(3*n)≤C^(3*(n+1)) := by
        calc
          _ ≤ (L+D)*C^(3*n) := by nlinarith [mul_le_mul_of_nonneg_left hn hL]
          _ ≤ C*C^(3*n) := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (pow_nonneg hC0 _)
          _ = C^(3*n+1) := by rw [pow_succ]; ring
          _ ≤ _ := pow_le_pow_right₀ hC1 (by omega)
      change ‖Az.comp Pz-Aw.comp Pw‖≤_
      rw [he]
      calc
        _ ≤ ‖(Az-Aw).comp Pz‖+‖Aw.comp (Pz-Pw)‖ := norm_add_le _ _
        _ ≤ ‖Az-Aw‖*‖Pz‖+‖Aw‖*‖Pz-Pw‖ :=
          add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
        _ ≤ (L*(C^n*‖z-w‖))*C^n+D*(C^(3*n)*‖z-w‖) := by
          apply add_le_add
          · exact mul_le_mul hdiff (ih.1 z) (norm_nonneg _) (by positivity)
          · exact mul_le_mul (standardDerivative_norm_bound k hk _) (ih.2 z w) (norm_nonneg _) hD
        _ = (L*C^(2*n)+D*C^(3*n))*‖z-w‖ := by rw [pow_mul]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hsum (norm_nonneg _)

lemma standardInverseDerivativeProduct_quantitative (k : ℝ) (hk : 0≤k) :
    ∃ C : ℝ, 2≤C ∧ ∀ n : ℕ, ∀ z w : ℂ,
      ‖standardInverseDerivativeProduct k (complexProjection z) n-
        standardInverseDerivativeProduct k (complexProjection w) n‖≤243*C^(3*n)*‖z-w‖ := by
  obtain ⟨C,hC,h⟩ := standardDerivativeProduct_quantitative k hk
  refine ⟨C,hC,?_⟩
  intro n z w
  have he : standardInverseDerivativeProduct k (complexProjection z) n-
      standardInverseDerivativeProduct k (complexProjection w) n = tangentReversal.comp
      ((standardDerivativeProduct k (complexProjection (tangentReversal z)) n-
        standardDerivativeProduct k (complexProjection (tangentReversal w)) n).comp tangentReversal) := by
    rw [standardInverseDerivativeProduct_conjugate,standardInverseDerivativeProduct_conjugate,
      complexProjection_tangentReversal,complexProjection_tangentReversal]
    ext v
    simp only [ContinuousLinearMap.comp_apply,sub_apply,map_sub]
  rw [he]
  have hc := tangentReversal_conjugate_norm_le
    (standardDerivativeProduct k (complexProjection (tangentReversal z)) n-
      standardDerivativeProduct k (complexProjection (tangentReversal w)) n)
  have hdist : ‖tangentReversal z-tangentReversal w‖≤3*‖z-w‖ := by
    rw [←map_sub]; exact tangentReversal_norm_le _
  calc
    _ ≤ 81*‖standardDerivativeProduct k (complexProjection (tangentReversal z)) n-
        standardDerivativeProduct k (complexProjection (tangentReversal w)) n‖ := hc
    _ ≤ 81*(C^(3*n)*‖tangentReversal z-tangentReversal w‖) :=
      mul_le_mul_of_nonneg_left ((h n).2 _ _) (by norm_num)
    _ ≤ 81*(C^(3*n)*(3*‖z-w‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdist (pow_nonneg (by linarith) _)) (by norm_num)
    _ = _ := by ring

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma contracting_line_comparison (A B : ℂ →L[ℝ] ℂ) (hA : PlaneAreaPreserving A)
    {u v : ℂ} (hv : ‖v‖=1) {a b : ℝ} (ha : ‖A u‖≤a) (hb : ‖B v‖≤b) :
    |wedge u v|≤a*b+a*‖A-B‖ := by
  have ha0 : 0≤a := (norm_nonneg _).trans ha
  have hb0 : 0≤b := (norm_nonneg _).trans hb
  have he : A v=B v+(A-B) v := by simp only [sub_apply]; abel
  calc
    _ = |wedge (A u) (A v)| := congrArg abs (hA u v).symm
    _ ≤ ‖A u‖*‖A v‖ := abs_wedge_le_norm_mul _ _
    _ ≤ a*(b+‖A-B‖) := by
      apply mul_le_mul ha _ (norm_nonneg _) ha0
      calc
        _ = ‖B v+(A-B) v‖ := congrArg norm he
        _ ≤ ‖B v‖+‖(A-B) v‖ := norm_add_le _ _
        _ ≤ b+‖A-B‖ := add_le_add hb (by simpa only [hv,mul_one] using (A-B).le_opNorm v)
    _ = _ := by ring

lemma PlaneLyapunov.norm_le_of_energy_le (A : ℕ → ℂ →L[ℝ] ℂ) {χ : ℝ} {v : ℂ}
    (hsum : Summable (fun n : ℕ => ‖A n v‖^2*Real.exp (2*χ*(n : ℝ))))
    {C : ℝ} (hC : 0≤C) (hE : PlaneLyapunov.energy A χ v≤C^2) (n : ℕ) :
    ‖A n v‖≤C*Real.exp (-χ*(n : ℝ)) := by
  have ht := (hsum.le_tsum n (fun m _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)).trans hE
  have he : Real.exp (2*χ*(n : ℝ))=(Real.exp (χ*(n : ℝ)))^2 := by
    rw [pow_two,←Real.exp_add]; congr 1; ring
  rw [he] at ht
  have hh : ‖A n v‖*Real.exp (χ*(n : ℝ))≤C :=
    (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) hC).mp (by nlinarith)
  have hh' := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-χ*(n : ℝ))).le
  have hc : Real.exp (χ*(n : ℝ))*Real.exp (-χ*(n : ℝ))=1 := by
    rw [←Real.exp_add]; convert Real.exp_zero using 1; ring_nf
  simpa only [mul_assoc,hc,mul_one] using hh'

lemma unit_projective_image_bound (A : ℂ →L[ℝ] ℂ) {u v : ℂ}
    (hu : ‖u‖=1) (hv : ‖v‖=1) :
    ‖A v‖≤‖A u‖+‖A‖*|wedge u v| := by
  have hd : |dot u v|≤1 := by simpa only [hu,hv,one_mul] using abs_dot_le_norm_mul u v
  have hj : ‖A (quarterTurn u)‖≤‖A‖ := by
    simpa only [norm_quarterTurn,hu,mul_one] using A.le_opNorm (quarterTurn u)
  calc
    _ = ‖dot u v • A u+wedge u v • A (quarterTurn u)‖ := by
      conv_lhs => rw [unit_expansion u v hu,map_add,map_smul,map_smul]
    _ ≤ |dot u v| *‖A u‖+|wedge u v| *‖A (quarterTurn u)‖ := by
      simpa only [norm_smul,Real.norm_eq_abs] using norm_add_le (dot u v • A u) (wedge u v • A (quarterTurn u))
    _ ≤ 1*‖A u‖+|wedge u v| *‖A‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hd (norm_nonneg _)) (mul_le_mul_of_nonneg_left hj (abs_nonneg _))
    _ = _ := by ring

lemma unit_image_norm_difference (A B : ℂ →L[ℝ] ℂ) {u v : ℂ}
    (hu : ‖u‖=1) (hv : ‖v‖=1) :
    |‖A u‖-‖B v‖|≤‖A‖*|wedge u v|+‖A-B‖ := by
  have h1 := unit_projective_image_bound A hu hv
  have h2 := unit_projective_image_bound A hv hu
  rw [wedge_swap v u,abs_neg] at h2
  have h3 : |‖A v‖-‖B v‖|≤‖A-B‖ :=
    (abs_norm_sub_norm_le _ _).trans (by simpa only [sub_apply,hv,mul_one] using (A-B).le_opNorm v)
  have h4 := abs_add_le (‖A u‖-‖A v‖) (‖A v‖-‖B v‖)
  have h5 : |‖A u‖-‖A v‖|≤‖A‖*|wedge u v| := abs_le.mpr ⟨by linarith,by linarith⟩
  have he : (‖A u‖-‖A v‖)+(‖A v‖-‖B v‖)=‖A u‖-‖B v‖ := by ring
  rw [he] at h4
  exact h4.trans (add_le_add h5 h3)

lemma log_difference_of_lower {a b D : ℝ} (hD : 0<D) (ha : 1≤D*a) (hb : 1≤D*b) :
    |Real.log a-Real.log b|≤D*|a-b| := by
  have ha0 : 0<a := by nlinarith
  have hb0 : 0<b := by nlinarith
  have hab := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
  have hba := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
  rw [Real.log_div ha0.ne' hb0.ne'] at hab
  rw [Real.log_div hb0.ne' ha0.ne'] at hba
  have hab' : a/b-1≤D*|a-b| := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hb0).mpr
    nlinarith [le_abs_self (a-b),mul_le_mul_of_nonneg_left hb (abs_nonneg (a-b))]
  have hba' : b/a-1≤D*|a-b| := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ ha0).mpr
    nlinarith [neg_le_abs (a-b),mul_le_mul_of_nonneg_left ha (abs_nonneg (a-b))]
  exact abs_le.mpr ⟨by linarith,hab.trans hab'⟩

lemma area_unit_log_image_difference (A B : ℂ →L[ℝ] ℂ)
    (hA : PlaneAreaPreserving A) (hB : PlaneAreaPreserving B) {u v : ℂ}
    (hu : ‖u‖=1) (hv : ‖v‖=1) {D : ℝ} (hD : 0<D) (hDA : ‖A‖≤D) (hDB : ‖B‖≤D) :
    |Real.log ‖A u‖-Real.log ‖B v‖|≤D^2*|wedge u v|+D*‖A-B‖ := by
  have ha : 1≤D*‖A u‖ := by
    calc
      _ = ‖u‖ := hu.symm
      _ ≤ ‖A‖*‖A u‖ := hA.norm_lower u
      _ ≤ _ := mul_le_mul_of_nonneg_right hDA (norm_nonneg _)
  have hb : 1≤D*‖B v‖ := by
    calc
      _ = ‖v‖ := hv.symm
      _ ≤ ‖B‖*‖B v‖ := hB.norm_lower v
      _ ≤ _ := mul_le_mul_of_nonneg_right hDB (norm_nonneg _)
  calc
    _ ≤ D*|‖A u‖-‖B v‖| := log_difference_of_lower hD ha hb
    _ ≤ D*(‖A‖*|wedge u v|+‖A-B‖) := mul_le_mul_of_nonneg_left (unit_image_norm_difference A B hu hv) hD.le
    _ ≤ D*(D*|wedge u v|+‖A-B‖) := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_right hDA (abs_nonneg _)) le_rfl) hD.le
    _ = _ := by ring

noncomputable def unstableLogJacobian (k : ℝ) (z : Torus) : ℝ :=
  Real.log ‖standardDerivative k z (unstableVector k z)‖
lemma measurable_unstableLogJacobian (k : ℝ) : Measurable (unstableLogJacobian k) :=
  (((continuous_fst.clm_apply continuous_snd :
    Continuous (fun p : (ℂ →L[ℝ] ℂ) × ℂ => p.1 p.2)).measurable.comp
    ((continuous_standardDerivative k).measurable.prodMk (measurable_unstableVector k))).norm).log

lemma unstableLogJacobian_difference (k : ℝ) (hk : 0≤k) (z w : ℂ) :
    |unstableLogJacobian k (complexProjection z)-unstableLogJacobian k (complexProjection w)|≤
      (9*growthBase k)^2*|wedge (unstableVector k (complexProjection z)) (unstableVector k (complexProjection w))|+
      (9*growthBase k)*derivativeVariationBound k*‖z-w‖ := by
  have hD : 0<9*growthBase k := by have := growthBase_ge_four k hk; positivity
  exact (area_unit_log_image_difference _ _ (standardDerivative_area k _) (standardDerivative_area k _)
    (norm_unstableVector k _) (norm_unstableVector k _) hD
    (standardDerivative_norm_bound k hk _) (standardDerivative_norm_bound k hk _)).trans
    (add_le_add le_rfl ((mul_le_mul_of_nonneg_left (standardDerivative_lift_sub_bound k z w) hD.le).trans_eq (by ring)))

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open Finset

lemma sum_of_backward_contraction (a : ℕ → ℝ) (ha : ∀ n,0≤a n) {q : ℝ}
    (hq0 : 0≤q) (hq1 : q<1) (N : ℕ) (hstep : ∀ j : ℕ,j<N → a j≤q*a (j+1)) :
    (∑ j ∈ Finset.range N,a j)≤a N/(1-q) := by
  have hh : (∑ j ∈ Finset.range N,a j)≤q*(∑ j ∈ Finset.range N,a (j+1)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj => hstep j (Finset.mem_range.mp hj)
  have he : (∑ j ∈ Finset.range N,a (j+1))+a 0=(∑ j ∈ Finset.range N,a j)+a N := by
    rw [←Finset.sum_range_succ',←Finset.sum_range_succ]
  apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
  have hlast := mul_le_mul_of_nonneg_right hq1.le (ha N)
  have hfirst := mul_nonneg hq0 (ha 0)
  nlinarith

namespace NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

@[simp] lemma Recurrence.step_zero (r : Recurrence ℓ δ) (n : ℕ) : r.step n 0=0 := by
  simp [Recurrence.step,r.zero]
@[simp] lemma Recurrence.orbit_zero (r : Recurrence ℓ δ) (n : ℕ) : r.orbit 0 n=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Recurrence.orbit,ih,r.step_zero]

lemma Recurrence.orbit_cone (r : Recurrence ℓ δ) (h : ℓ+δ<1) {v : Plane}
    (hv : |v.1|≤|v.2|) (n : ℕ) :
    |(r.orbit v n).1|≤|(r.orbit v n).2| ∧
    |(r.orbit v n).2|≤((ℓ+δ : ℝ≥0) : ℝ)*|(r.orbit v (n+1)).2| := by
  have hcone (m : ℕ) : |(r.orbit v m).1|≤|(r.orbit v m).2| := by
    induction m with
    | zero => exact hv
    | succ m ih =>
      simpa only [Recurrence.orbit,r.step_zero,Prod.fst_zero,Prod.snd_zero,sub_zero] using
        (r.unstable_cone_step h m (r.orbit v m) 0 (by simpa only [Prod.fst_zero,Prod.snd_zero,sub_zero] using ih)).1
  refine ⟨hcone n,?_⟩
  simpa only [Recurrence.orbit,r.step_zero,Prod.snd_zero,sub_zero] using
    (r.unstable_cone_step h n (r.orbit v n) 0 (by simpa only [Prod.fst_zero,Prod.snd_zero,sub_zero] using hcone n)).2
lemma Recurrence.orbit_norm_eq_snd (r : Recurrence ℓ δ) (h : ℓ+δ<1) {v : Plane}
    (hv : |v.1|≤|v.2|) (n : ℕ) : ‖r.orbit v n‖=|(r.orbit v n).2| :=
  max_eq_right (r.orbit_cone h hv n).1
lemma Recurrence.orbit_snd_ne_zero (r : Recurrence ℓ δ) (h : ℓ+δ<1) {v : Plane}
    (hv : |v.1|≤|v.2|) (hv0 : v.2≠0) (n : ℕ) : (r.orbit v n).2≠0 := by
  induction n with
  | zero => exact hv0
  | succ n ih =>
    intro he
    have hc := (r.orbit_cone h hv n).2
    rw [he,abs_zero,mul_zero] at hc
    exact (abs_pos.mpr ih).not_ge hc

lemma scalar_log_quadratic_error {b y e d : ℝ} (hb : 1≤|b|) (hy : y≠0)
    (hd0 : 0≤d) (hd1 : d≤1/2) (hysize : |y|≤1) (he : |e|≤d*|y|^2) :
    abs (Real.log |b*y+e|-Real.log |b|-Real.log |y|) ≤2*d*|y| := by
  have hyp : 0 < |y| := abs_pos.mpr hy
  have hbp : 0 < |b| := lt_of_lt_of_le zero_lt_one hb
  have hsmall : |e|≤|y|/2 := by
    have hsq : |y|^2≤|y| := by nlinarith [abs_nonneg y]
    have hle := mul_le_mul_of_nonneg_left hsq hd0
    have hle' := mul_le_mul_of_nonneg_right hd1 (abs_nonneg y)
    nlinarith
  have hlower : |y|/2≤|b*y+e| := by
    have hh : |b*y|≤|b*y+e|+|e| := by
      have hh := abs_sub (b*y+e) e
      simpa only [add_sub_cancel_right] using hh
    rw [abs_mul] at hh
    have hb' := mul_le_mul_of_nonneg_right hb (abs_nonneg y)
    nlinarith
  have hD : 0<2/|y| := div_pos (by norm_num) hyp
  have hx : 1≤(2/|y|)*|b*y+e| := by
    have hc := mul_le_mul_of_nonneg_left hlower hD.le
    have heq : (2/|y|)*(|y|/2)=1 := by field_simp
    rwa [heq] at hc
  have hb' : 1≤(2/|y|)*|b*y| := by
    rw [abs_mul]
    have heq : (2/|y|)*(|b| *|y|)=2*|b| := by field_simp
    rw [heq]; linarith
  have hl := log_difference_of_lower hD hx hb'
  have hnorm : abs (|b*y+e|-|b*y|)≤|e| := by
    simpa only [add_sub_cancel_left] using abs_abs_sub_abs_le_abs_sub (b*y+e) (b*y)
  have hh := hl.trans (mul_le_mul_of_nonneg_left (hnorm.trans he) hD.le)
  rw [abs_mul,Real.log_mul hbp.ne' hyp.ne'] at hh
  have hright : (2/|y|)*(d*|y|^2)=2*d*|y| := by field_simp
  rw [hright] at hh
  convert hh using 1; congr 1; ring

theorem Recurrence.finite_cone_log_distortion (r : Recurrence ℓ δ) (h : ℓ+δ<1)
    (hδ : (δ : ℝ)≤1/2)
    (hquad : ∀ n : ℕ,∀ v : Plane,‖v‖≤1 → ‖r.remainder n v‖≤(δ : ℝ)*‖v‖^2)
    {v : Plane} (hv : |v.1|≤|v.2|) (hv0 : v.2≠0) (N : ℕ) (htrap : v∈r.trappedBox N) :
    abs (Real.log |(r.orbit v N).2|-Real.log |v.2|-
      ∑ j ∈ Finset.range N,Real.log |r.b j|) ≤2*(δ : ℝ)/(1-((ℓ+δ : ℝ≥0) : ℝ)) := by
  let y := fun j : ℕ => |(r.orbit v j).2|
  have hstep (j : ℕ) (hj : j<N) :
      abs ((Real.log (y (j+1))-Real.log (y j))-Real.log |r.b j|) ≤2*(δ : ℝ)*y j := by
    have hy := r.orbit_snd_ne_zero h hv hv0 j
    have hysize : |(r.orbit v j).2|≤1 := by
      rw [←r.orbit_norm_eq_snd h hv j]
      exact htrap j hj.le
    have herr : |(r.remainder j (r.orbit v j)).2|≤(δ : ℝ)*|(r.orbit v j).2|^2 := by
      have hh := (norm_snd_le (r.remainder j (r.orbit v j))).trans (hquad j _ (htrap j hj.le))
      simpa only [Real.norm_eq_abs,r.orbit_norm_eq_snd h hv j] using hh
    have hh := scalar_log_quadratic_error (r.unstable_size_ge_one h j) hy δ.coe_nonneg hδ hysize herr
    change abs (Real.log |r.b j*(r.orbit v j).2+(r.remainder j (r.orbit v j)).2|-
      Real.log |(r.orbit v j).2|-Real.log |r.b j|) ≤_
    convert hh using 1; congr 1; ring
  have hsum := sum_of_backward_contraction y (fun j => abs_nonneg _) (ℓ+δ).coe_nonneg
    (NNReal.coe_lt_coe.mpr h) N (fun j _ => (r.orbit_cone h hv j).2)
  have hlast : y N≤1 := by
    dsimp [y]; rw [←r.orbit_norm_eq_snd h hv N]; exact htrap N le_rfl
  have hsum' : (∑ j ∈ Finset.range N,y j)≤1/(1-((ℓ+δ : ℝ≥0) : ℝ)) :=
    hsum.trans (div_le_div_of_nonneg_right hlast (sub_nonneg.mpr (NNReal.coe_le_coe.mpr h.le)))
  have htel : (∑ j ∈ Finset.range N,((Real.log (y (j+1))-Real.log (y j))-Real.log |r.b j|))=
      Real.log (y N)-Real.log (y 0)-(∑ j ∈ Finset.range N,Real.log |r.b j|) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_range_sub (fun j => Real.log (y j)) N
  calc
    _ = |∑ j ∈ Finset.range N,((Real.log (y (j+1))-Real.log (y j))-Real.log |r.b j|)| := congrArg abs htel.symm
    _ ≤ ∑ j ∈ Finset.range N,abs ((Real.log (y (j+1))-Real.log (y j))-Real.log |r.b j|) := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N,2*(δ : ℝ)*y j := Finset.sum_le_sum fun j hj => hstep j (Finset.mem_range.mp hj)
    _ = (2*(δ : ℝ))*(∑ j ∈ Finset.range N,y j) := (Finset.mul_sum _ _ _).symm
    _ ≤ (2*(δ : ℝ))*(1/(1-((ℓ+δ : ℝ≥0) : ℝ))) := mul_le_mul_of_nonneg_left hsum' (by positivity)
    _ = _ := by ring

end NonlinearStable
end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

noncomputable def fineRemainderDerivative (k χ ε δ : ℝ) (z : ℂ) : RealPlane → RealPlane →L[ℝ] RealPlane :=
  flatRemainderDerivative k z (fineFrame k χ ε δ (complexProjection z))
    (fineInverse k χ ε δ (standardMap k (complexProjection z)))
lemma hasFDerivAt_fineRemainder (k χ ε δ : ℝ) (z : ℂ) (v : RealPlane) :
    HasFDerivAt (fineRemainder k χ ε δ z) (fineRemainderDerivative k χ ε δ z v) v :=
  hasFDerivAt_flatRemainder _ _ _ _ _
@[simp] lemma fineRemainderDerivative_zero (k χ ε δ : ℝ) (z : ℂ) : fineRemainderDerivative k χ ε δ z 0=0 :=
  flatRemainderDerivative_zero _ _ _ _
lemma fineRemainderDerivative_lipschitz (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : ℂ)
    (hz : FineRegular k χ ε (complexProjection z))
    (hn : FineRegular k χ ε (standardMap k (complexProjection z))) (v w : RealPlane) :
    ‖fineRemainderDerivative k χ ε δ z v-fineRemainderDerivative k χ ε δ z w‖≤δ*‖v-w‖ :=
  (flatRemainderDerivative_lipschitz k z _ _ v w).trans
    (mul_le_mul_of_nonneg_right (fine_nonlinearity_coefficient k χ ε hδ _ hz hn) (norm_nonneg _))
lemma fineRemainderDerivative_bound (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : ℂ)
    (hz : FineRegular k χ ε (complexProjection z))
    (hn : FineRegular k χ ε (standardMap k (complexProjection z)))
    {v : RealPlane} (hv : ‖v‖≤1) : ‖fineRemainderDerivative k χ ε δ z v‖≤δ := by
  have hh := fineRemainderDerivative_lipschitz k χ ε hδ z hz hn v 0
  simp only [fineRemainderDerivative_zero,sub_zero] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left hv hδ.le).trans_eq (mul_one _))
lemma fineRemainder_taylor (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : ℂ)
    (hz : FineRegular k χ ε (complexProjection z))
    (hn : FineRegular k χ ε (standardMap k (complexProjection z))) (v w : RealPlane) :
    ‖fineRemainder k χ ε δ z w-fineRemainder k χ ε δ z v-
      fineRemainderDerivative k χ ε δ z v (w-v)‖≤δ*‖w-v‖^2 :=
  quadratic_taylor_of_derivative_lipschitz _ _ (hasFDerivAt_fineRemainder k χ ε δ z)
    hδ.le (fineRemainderDerivative_lipschitz k χ ε hδ z hz hn) v w
lemma fineRemainder_quadratic (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : ℂ)
    (hz : FineRegular k χ ε (complexProjection z))
    (hn : FineRegular k χ ε (standardMap k (complexProjection z))) (v : RealPlane) :
    ‖fineRemainder k χ ε δ z v‖≤δ*‖v‖^2 := by
  simpa only [fineRemainder_zero,fineRemainderDerivative_zero,zero_apply,sub_zero] using
    fineRemainder_taylor k χ ε hδ z hz hn 0 v

lemma fineTrapped_orbit (k χ ε δ : ℝ) (hδ : 0<δ) (w : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {N : ℕ} {v : RealPlane} (hv : v∈fineTrapped k χ ε δ w N) {j : ℕ} (hj : j≤N) :
    (fineLocalRecurrence k χ ε δ hδ w hw).extend.orbit v j=
      fineCoordinate k χ ε δ w (w+fineFrame k χ ε δ (complexProjection w) v) j := by
  induction j with
  | zero => exact (fineCoordinate_initial k χ ε hδ w (hw 0) v).symm
  | succ j ih =>
    rw [Recurrence.orbit,ih (by omega),extend_step_eq _ j (hv j (by omega)),fineCoordinate_step]

theorem fineTrapped_log_distortion (k χ ε δ : ℝ) (hδ : 0<δ) (hδ' : δ≤1/2)
    (hq : Real.exp (-χ+ε)+δ<1) (w : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {v : RealPlane} (hv : |v.1|≤|v.2|) (hv0 : v.2≠0) (N : ℕ)
    (htrap : v∈fineTrapped k χ ε δ w N) :
    abs (Real.log |(fineCoordinate k χ ε δ w (w+fineFrame k χ ε δ (complexProjection w) v) N).2|-
      Real.log |v.2|-(∑ j ∈ Finset.range N,Real.log |fineUnstableMultiplier k χ ε δ
        (complexProjection ((standardLift k)^[j] w))|))≤2*δ/(1-(Real.exp (-χ+ε)+δ)) := by
  let r := fineLocalRecurrence k χ ε δ hδ w hw
  have hquad (n : ℕ) (u : RealPlane) (hu : ‖u‖≤1) : ‖r.extend.remainder n u‖≤δ*‖u‖^2 := by
    change ‖fineRemainder k χ ε δ ((standardLift k)^[n] w) (planeClip u)‖≤_
    rw [planeClip_eq hu]
    exact fineRemainder_quadratic k χ ε hδ _ (hw n) (fine_regular_lift_next k χ ε w hw n) u
  have hh := r.extend.finite_cone_log_distortion hq hδ' hquad hv hv0 N
    (fineTrapped_subset k χ ε δ hδ w hw N htrap)
  rw [fineTrapped_orbit k χ ε δ hδ w hw htrap le_rfl] at hh
  exact hh

end StandardMapEntropy

end
end

end OAI
