import OAI.Geometry.LatticeCovering.RadialBounds

namespace OAI

section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
noncomputable section

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter Isotropization
open scoped ENNReal RealInnerProductSpace Topology BigOperators

lemma compact_volume_E {d : ℕ} {A B C : Set (E d)}
    (hA : IsCompact A) (hB : IsCompact B) (hC : IsCompact C)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hadd : ∀ x ∈ A, ∀ y ∈ B, a•x+b•y ∈ C) :
    (volume A).toReal^a*(volume B).toReal^b ≤ (volume C).toReal := by
  let e := (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toContinuousLinearEquiv
  have hp : MeasurePreserving e volume volume := PiLp.volume_preserving_ofLp (Fin d)
  have hv (S : Set (E d)) : volume (e '' S)=volume S := by
    have H := congrArg (fun μ : Measure (RV d) => μ (e '' S)) hp.map_eq
    change (Measure.map e.toHomeomorph.toMeasurableEquiv volume) (e '' S)=volume (e '' S) at H
    rw [e.toHomeomorph.toMeasurableEquiv.map_apply] at H
    change volume (e ⁻¹' (e '' S))=volume (e '' S) at H
    rw [Set.preimage_image_eq _ e.injective] at H
    exact H.symm
  rw [←hv A,←hv B,←hv C]
  apply compact_volume (hA.image e.continuous) (hB.image e.continuous) (hC.image e.continuous) ha hb hab
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  exact ⟨a•x+b•y,hadd x hx y hy,by simp⟩

lemma scalarLogConcave_cap_volume_E {d : ℕ} {K : Set (E d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (L : E d →L[ℝ] ℝ) :
    ScalarLogConcave (fun t => (volume (K ∩ {x | t ≤ L x})).toReal) := by
  refine ⟨fun _ => ENNReal.toReal_nonneg,fun u v a b ha hb hab => ?_⟩
  apply compact_volume_E (hK.inter_right (isClosed_le continuous_const L.continuous))
    (hK.inter_right (isClosed_le continuous_const L.continuous))
    (hK.inter_right (isClosed_le continuous_const L.continuous)) ha hb hab
  intro x hx y hy
  refine ⟨hc hx.1 hy.1 ha.le hb.le hab,?_⟩
  change a*u+b*v ≤ L (a•x+b•y)
  simp only [map_add,map_smul,smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left hx.2 ha.le) (mul_le_mul_of_nonneg_left hy.2 hb.le)

lemma scalarLogConcave_uniform_cap {d : ℕ} {K : Set (E d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (L : E d →L[ℝ] ℝ) :
    ScalarLogConcave (fun t => (((volume K)⁻¹ • volume.restrict K) : Measure (E d)).real {x | t ≤ L x}) := by
  have he (t : ℝ) : (((volume K)⁻¹ • volume.restrict K) : Measure (E d)).real {x | t ≤ L x}=
      ((volume K)⁻¹).toReal*(volume (K ∩ {x | t ≤ L x})).toReal := by
    rw [measureReal_def,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply
      (measurableSet_le measurable_const L.measurable),ENNReal.toReal_mul,inter_comm]
  simp_rw [he]
  exact (scalarLogConcave_cap_volume_E hK hc L).const_mul ENNReal.toReal_nonneg

lemma norm_fourth_le_sum {d : ℕ} (x : E d) : ‖x‖^4 ≤ (d:ℝ)*(∑ i, (x i)^4) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin d => (1:ℝ)) (fun i => (x i)^2)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at h
  have he : ‖x‖^2=∑ i, (x i)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs,sq_abs]
  rw [show ‖x‖^4=(‖x‖^2)^2 by ring,he]
  simpa only [←pow_mul] using h

lemma fourth_norm_of_coordinates {d : ℕ} {μ : Measure (E d)} [IsFiniteMeasure μ]
    (hint : ∀ i : Fin d, Integrable (fun x : E d => (x i)^4) μ)
    (hb : ∀ i : Fin d, (∫ x, (x i)^4 ∂μ) ≤ fourthMomentConstant) :
    Integrable (fun x : E d => ‖x‖^4) μ ∧
      (∫ x : E d, ‖x‖^4 ∂μ) ≤ fourthMomentConstant*(d:ℝ)^2 := by
  have hi : Integrable (fun x : E d => (d:ℝ)*(∑ i, (x i)^4)) μ :=
    (integrable_finsetSum _ (fun i _ => hint i)).const_mul _
  have hn : Integrable (fun x : E d => ‖x‖^4) μ := hi.mono' (by fun_prop)
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ ‖x‖^4)] using norm_fourth_le_sum x))
  refine ⟨hn,?_⟩
  calc
    _ ≤ ∫ x : E d, (d:ℝ)*(∑ i, (x i)^4) ∂μ := integral_mono hn hi norm_fourth_le_sum
    _ = (d:ℝ)*(∑ i, ∫ x : E d, (x i)^4 ∂μ) := by rw [integral_const_mul,integral_finsetSum _ (fun i _ => hint i)]
    _ ≤ (d:ℝ)*(∑ _i : Fin d, fourthMomentConstant) := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hb i)) (Nat.cast_nonneg _)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

lemma paley_zygmund_quarter {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hm : Measurable Y)
    (hi : Integrable Y μ) (hy : ∀ x, 0 ≤ Y x) (hmean : ∫ x, Y x ∂μ=1)
    {C : ℝ} (hC : 0 < C) (h2i : Integrable (fun x => (Y x)^2) μ)
    (hsecond : (∫ x, (Y x)^2 ∂μ) ≤ C) : 1/(4*C) ≤ μ.real {x | 1/2 ≤ Y x} := by
  have _ := hy
  classical
  let A := {x | (1:ℝ)/2 ≤ Y x}
  have hA : MeasurableSet A := measurableSet_le measurable_const hm
  have hpoint (x : Ω) : Y x ≤ 1/2+(Y x)^2/(4*C)+A.indicator (fun _ => C) x := by
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx]
      have hsq := sq_nonneg (Y x-2*C)
      apply (mul_le_mul_iff_left₀ (show 0 < 4*C by positivity)).mp
      have he : (1/2+(Y x)^2/(4*C)+C)*(4*C)=2*C+(Y x)^2+4*C^2 := by field_simp; ring
      rw [he]
      nlinarith
    · rw [indicator_of_notMem hx]
      have hh : Y x < 1/2 := lt_of_not_ge hx
      have hh' : 0 ≤ (Y x)^2/(4*C) := by positivity
      linarith
  have hb := integral_mono hi (((integrable_const (1/2:ℝ)).add (h2i.div_const (4*C))).add
    ((integrable_const C).indicator hA)) hpoint
  change (∫ x, Y x ∂μ) ≤ ∫ x, 1/2+(Y x)^2/(4*C)+A.indicator (fun _ => C) x ∂μ at hb
  have hsum : Integrable (fun x => (1/2:ℝ)+(Y x)^2/(4*C)) μ := (integrable_const _).add (h2i.div_const _)
  rw [integral_add hsum ((integrable_const C).indicator hA),
    integral_add (integrable_const (1/2:ℝ)) (h2i.div_const (4*C)),integral_div (4*C),
    integral_indicator hA,integral_const,integral_const,hmean] at hb
  simp only [measureReal_def,Measure.restrict_apply_univ,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul] at hb
  change 1 ≤ 1/2+(∫ x, (Y x)^2 ∂μ)/(4*C)+μ.real A*C at hb
  have hdiv := (div_le_div_iff_of_pos_right (show 0 < 4*C by positivity)).mpr hsecond
  have hcan : C/(4*C)=(1:ℝ)/4 := by field_simp
  rw [hcan] at hdiv
  apply (div_le_iff₀ (show 0 < 4*C by positivity)).mpr
  change 1 ≤ μ.real A*(4*C)
  nlinarith



end SingleLatticeCovering.Prekopa
namespace SingleLatticeCovering.Prekopa
open MeasureTheory ProbabilityTheory Set Filter Isotropization
open scoped ENNReal RealInnerProductSpace Topology

lemma uniform_body_fourth {d : ℕ} {K : Set (E d)} (hK : IsCompact K)
    (hc : Convex ℝ K) (μ : Measure (E d)) [IsProbabilityMeasure μ]
    (hdef : μ=(volume K)⁻¹ • volume.restrict K)
    (hlp : MemLp id 2 μ) (hiso : IsIsotropic μ) :
    Integrable (fun x : E d => ‖x‖^4) μ ∧
      (∫ x : E d, ‖x‖^4 ∂μ) ≤ fourthMomentConstant*(d:ℝ)^2 := by
  have H (i : Fin d) : Integrable (fun x : E d => (x i)^4) μ ∧
      (∫ x : E d, (x i)^4 ∂μ) ≤ fourthMomentConstant := by
    have hp : ScalarLogConcave (fun t => μ.real {x | t ≤ x i}) := by
      rw [hdef]
      exact scalarLogConcave_uniform_cap hK hc (EuclideanSpace.proj i)
    have hn : ScalarLogConcave (fun t => μ.real {x | t ≤ -(x i)}) := by
      rw [hdef]
      exact scalarLogConcave_uniform_cap hK hc (-EuclideanSpace.proj i)
    exact fourth_moment_bound μ (by fun_prop) (coordinate_memLp hlp i).integrable_sq
      (isotropic_coordinate_second hiso i).le hp hn
  exact fourth_norm_of_coordinates (fun i => (H i).1) (fun i => (H i).2)

lemma fourthMomentConstant_pos : 0 < fourthMomentConstant := by
  unfold fourthMomentConstant
  positivity

lemma uniform_body_radius_lower {d : ℕ} (hd : 0 < d) {K : Set (E d)} (hK : IsCompact K)
    (hc : Convex ℝ K) (μ : Measure (E d)) [IsProbabilityMeasure μ]
    (hdef : μ=(volume K)⁻¹ • volume.restrict K)
    (hlp : MemLp id 2 μ) (hiso : IsIsotropic μ) :
    1/(4*fourthMomentConstant) ≤ μ.real {x | (d:ℝ)/2 ≤ ‖x‖^2} := by
  have hdp : (0:ℝ) < d := Nat.cast_pos.mpr hd
  obtain ⟨hi,h4⟩ := uniform_body_fourth hK hc μ hdef hlp hiso
  have ht : Integrable (fun x : E d => (‖x‖^2/(d:ℝ))^2) μ := by
    simpa only [div_pow,←pow_mul] using hi.div_const ((d:ℝ)^2)
  have hmean : (∫ x : E d, ‖x‖^2/(d:ℝ) ∂μ)=1 := by
    rw [integral_div,isotropic_norm_sq hlp hiso,div_self (ne_of_gt hdp)]
  have hsecond : (∫ x : E d, (‖x‖^2/(d:ℝ))^2 ∂μ) ≤ fourthMomentConstant := by
    simp only [div_pow,←pow_mul]
    rw [integral_div]
    exact (div_le_iff₀ (sq_pos_of_pos hdp)).mpr h4
  have H := paley_zygmund_quarter μ (by fun_prop : Measurable (fun x : E d => ‖x‖^2/(d:ℝ)))
    (hlp.norm.integrable_sq.div_const _) (fun x => by positivity) hmean fourthMomentConstant_pos ht hsecond
  have he : {x : E d | (1:ℝ)/2 ≤ ‖x‖^2/(d:ℝ)}={x | (d:ℝ)/2 ≤ ‖x‖^2} := by
    ext x
    simp only [mem_ofPred_eq,le_div_iff₀ hdp]
    ring_nf
  rwa [he] at H


end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology

lemma scaled_gaussian_law {k : ℕ} {v : ℝ} (hv : 0 < v) :
    (stdGaussian (E k)).map (fun z => Real.sqrt v • z)=law k (1/(2*v)) := by
  let := law_probability k (show 0 < 1/(2*v) by positivity)
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply,integral_map (by fun_prop) (by fun_prop)]
  have he (y : E k) : ⟪Real.sqrt v • y,t⟫=⟪y,Real.sqrt v • t⟫ := by
    simp only [inner_smul_left,inner_smul_right,conj_trivial]
  simp only [he,←charFun_apply,charFun_stdGaussian,charFun_law (show 0 < 1/(2*v) by positivity)]
  congr 1
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),←Complex.ofReal_pow,mul_pow,
    Real.sq_sqrt hv.le]
  have hvC : (v:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hv
  push_cast
  field_simp
  ring

lemma measurable_mixture_kernel {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    {v : Ω → ℝ} (hv : Measurable v) :
    Measurable (fun p : Ω × E k => density (1/(2*v p.1)) p.2) := by
  unfold density normalizer
  fun_prop

section Integrable
attribute [local irreducible] density normalizer

lemma integrable_mixture_kernel {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] {v : Ω → ℝ} (hm : Measurable v) (hv : ∀ x, 0 < v x) :
    Integrable (fun p : Ω × E k => density (1/(2*v p.1)) p.2) (μ.prod volume) := by
  apply (integrable_prod_iff (measurable_mixture_kernel hm).aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun x => integrable_density (div_pos zero_lt_one (mul_pos (by norm_num) (hv x)))),?_⟩
  have he (x : Ω) : (∫ y : E k, ‖density (1/(2*v x)) y‖)=1 := by
    have hvx : 0 < 1/(2*v x) := div_pos zero_lt_one (mul_pos (by norm_num) (hv x))
    simp only [Real.norm_eq_abs,abs_of_nonneg (density_pos hvx _).le]
    exact integral_density hvx
  simp only [he]
  exact integrable_const _

lemma mixture_integrable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] {v : Ω → ℝ} (hm : Measurable v) (hv : ∀ x, 0 < v x) :
    Integrable (fun y : E k => ∫ x, density (1/(2*v x)) y ∂μ) volume :=
  (integrable_mixture_kernel μ hm hv).integral_prod_right

lemma mixture_integral {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {v : Ω → ℝ} (hm : Measurable v) (hv : ∀ x, 0 < v x) :
    (∫ y : E k, ∫ x, density (1/(2*v x)) y ∂μ)=1 := by
  have hj : Integrable (fun p : E k × Ω => density (1/(2*v p.2)) p.1) (volume.prod μ) :=
    (integrable_mixture_kernel μ hm hv).swap
  rw [integral_integral_swap hj]
  have hs (x : Ω) : (∫ y : E k, density (1/(2*v x)) y)=1 := integral_density (div_pos zero_lt_one (mul_pos (by norm_num) (hv x)))
  simp only [hs]
  simp

lemma mixture_set_integral {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] [SFinite μ] {v : Ω → ℝ}
    (hm : Measurable v) (hv : ∀ x, 0 < v x) (A : Set (E k)) :
    (∫ y : E k in A, ∫ x, density (1/(2*v x)) y ∂μ)=
      ∫ x, (∫ y : E k in A, density (1/(2*v x)) y) ∂μ := by
  have hj : Integrable (fun p : E k × Ω => density (1/(2*v p.2)) p.1) ((volume.restrict A).prod μ) :=
    ((integrable_mixture_kernel μ hm hv).mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)).swap
  exact integral_integral_swap hj

end Integrable

lemma density_set_integral {k : ℕ} {v : ℝ} (hv : 0 < v) {A : Set (E k)} (hA : MeasurableSet A) :
    (∫ y : E k in A, density (1/(2*v)) y)=
      (stdGaussian (E k)).real {z | Real.sqrt v • z ∈ A} := by
  have hprob := law_probability k (show 0 < 1/(2*v) by positivity)
  have he : (law k (1/(2*v))).real A=∫ y : E k in A, density (1/(2*v)) y := by
    rw [measureReal_def,law,withDensity_apply _ hA,←ofReal_integral_eq_lintegral_ofReal
      (integrable_density (show 0 < 1/(2*v) by positivity)).integrableOn
      (Filter.Eventually.of_forall (fun y => (density_pos (by positivity) y).le)),
      ENNReal.toReal_ofReal (integral_nonneg (fun y => (density_pos (by positivity) y).le))]
  rw [←he,←scaled_gaussian_law hv,measureReal_def,Measure.map_apply (by fun_prop) hA]
  rfl



end SingleLatticeCovering.GaussianDensity

namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology

lemma integrable_translated_density {k : ℕ} {b : ℝ} (hb : 0 < b) (w : E k) :
    Integrable (fun y => density b (y-w)) volume := by
  exact ((measurePreserving_sub_right volume w).integrable_comp
    (continuous_density k b).aestronglyMeasurable).mpr (integrable_density hb)

lemma integral_translated_density {k : ℕ} {b : ℝ} (hb : 0 < b) (w : E k) :
    (∫ y, density b (y-w))=1 := by
  rw [integral_sub_right_eq_self,integral_density hb]

attribute [local irreducible] density normalizer

lemma integrable_convolution_kernel {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] {p : Ω → E k} (hp : Measurable p)
    {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : Ω × E k => density b (z.2-p z.1)) (μ.prod volume) := by
  have hmm : Measurable (fun z : Ω × E k => density b (z.2-p z.1)) :=
    (continuous_density k b).measurable.comp (measurable_snd.sub (hp.comp measurable_fst))
  apply (integrable_prod_iff hmm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun x => integrable_translated_density hb (p x)),?_⟩
  have he (x : Ω) : (∫ y : E k, ‖density b (y-p x)‖)=1 := by
    simp only [Real.norm_eq_abs,abs_of_nonneg (density_pos hb _).le]
    exact integral_translated_density hb _
  simp only [he]
  exact integrable_const _

lemma convolution_integrable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] {p : Ω → E k} (hp : Measurable p)
    {b : ℝ} (hb : 0 < b) :
    Integrable (fun y : E k => ∫ x, density b (y-p x) ∂μ) volume :=
  (integrable_convolution_kernel μ hp hb).integral_prod_right

lemma convolution_integral {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : Ω → E k} (hp : Measurable p)
    {b : ℝ} (hb : 0 < b) :
    (∫ y : E k, ∫ x, density b (y-p x) ∂μ)=1 := by
  have hj : Integrable (fun z : E k × Ω => density b (z.1-p z.2)) (volume.prod μ) :=
    (integrable_convolution_kernel μ hp hb).swap
  rw [integral_integral_swap hj]
  simp only [integral_translated_density hb]
  simp


end SingleLatticeCovering.GaussianDensity

namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

lemma neg_log_one_sub_le {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1/2) :
    -Real.log (1-u) ≤ u+2*u^2 := by
  have _ := hu
  have hp : 0 < 1-u := by linarith
  have H := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at H
  apply (mul_le_mul_iff_right₀ hp).mp
  have HH := mul_le_mul_of_nonneg_right H hp.le
  rw [sub_mul,inv_mul_cancel₀ (ne_of_gt hp),one_mul] at HH
  have hcube : 0 ≤ u^2*(1-2*u) := mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith

lemma log_one_add_ge {u : ℝ} (hu : 0 ≤ u) : u-u^2 ≤ Real.log (1+u) := by
  have hp : 0 < 1+u := by linarith
  have H := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at H
  apply (mul_le_mul_iff_right₀ hp).mp
  have HH := mul_le_mul_of_nonneg_right H hp.le
  rw [sub_mul,inv_mul_cancel₀ (ne_of_gt hp),one_mul] at HH
  nlinarith [pow_nonneg hu 3]

lemma gaussian_chernoff_upper {k : ℕ} {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (B : ℝ) :
    (stdGaussian (E k)).real {y | B ≤ ‖y‖^2} ≤
      Real.exp (-((k:ℝ)/2)*Real.log (1-a)-a*B/2) := by
  have H := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun y : E k => (Real.exp_pos (a*‖y‖^2/2)).le))
    (stdGaussian_integrable_exp_norm_sq (k := k) ha1) (Real.exp (a*B/2))
  have hs : {y : E k | Real.exp (a*B/2) ≤ Real.exp (a*‖y‖^2/2)}={y | B ≤ ‖y‖^2} := by
    ext y
    simp only [mem_ofPred_eq,Real.exp_le_exp]
    exact div_le_div_iff_of_pos_right (by norm_num) |>.trans (mul_le_mul_iff_right₀ ha)
  rw [hs,stdGaussian_laplace_norm_sq ha1] at H
  rw [Real.exp_sub]
  apply (le_div_iff₀ (Real.exp_pos _)).mpr
  simpa only [mul_comm] using H

lemma gaussian_chernoff_lower {k : ℕ} {a : ℝ} (ha : a < 0) (B : ℝ) :
    (stdGaussian (E k)).real {y | ‖y‖^2 ≤ B} ≤
      Real.exp (-((k:ℝ)/2)*Real.log (1-a)-a*B/2) := by
  have ha1 : a < 1 := by linarith
  have H := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun y : E k => (Real.exp_pos (a*‖y‖^2/2)).le))
    (stdGaussian_integrable_exp_norm_sq (k := k) ha1) (Real.exp (a*B/2))
  have hs : {y : E k | Real.exp (a*B/2) ≤ Real.exp (a*‖y‖^2/2)}={y | ‖y‖^2 ≤ B} := by
    ext y
    simp only [mem_ofPred_eq,Real.exp_le_exp]
    rw [div_le_div_iff_of_pos_right (by norm_num),mul_le_mul_left_of_neg ha]
  rw [hs,stdGaussian_laplace_norm_sq ha1] at H
  rw [Real.exp_sub]
  apply (le_div_iff₀ (Real.exp_pos _)).mpr
  simpa only [mul_comm] using H

lemma gaussian_norm_sq_upper {k : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (stdGaussian (E k)).real {y | (1+ε)*(k:ℝ) ≤ ‖y‖^2} ≤ Real.exp (-(k:ℝ)*ε^2/16) := by
  apply (gaussian_chernoff_upper (k := k) (a := ε/4) (by positivity) (by linarith) _).trans
  apply Real.exp_le_exp.mpr
  have H := neg_log_one_sub_le (show (0:ℝ) ≤ ε/4 by positivity) (show ε/4 ≤ 1/2 by linarith)
  have HH := mul_le_mul_of_nonneg_left H (show 0 ≤ (k:ℝ)/2 by positivity)
  nlinarith

lemma gaussian_norm_sq_lower {k : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (stdGaussian (E k)).real {y | ‖y‖^2 ≤ (1-ε)*(k:ℝ)} ≤ Real.exp (-(k:ℝ)*ε^2/16) := by
  have _ := hε1
  apply (gaussian_chernoff_lower (k := k) (a := -ε/4) (by linarith) _).trans
  apply Real.exp_le_exp.mpr
  have H := log_one_add_ge (show (0:ℝ) ≤ ε/4 by positivity)
  have HH := mul_le_mul_of_nonneg_left H (show 0 ≤ (k:ℝ)/2 by positivity)
  rw [show 1-(-ε/4)=1+ε/4 by ring]
  nlinarith [mul_nonneg (show (0:ℝ) ≤ k by positivity) (sq_nonneg ε)]



end SingleLatticeCovering.GaussianDensity

namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology

lemma norm_scaled_sq {k : ℕ} {v : ℝ} (hv : 0 ≤ v) (z : E k) :
    ‖Real.sqrt v • z‖^2=v*‖z‖^2 := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt hv]

lemma density_small_ball_lower {k : ℕ} {v a ε : ℝ} (hv : 0 < v) (ha : 0 ≤ a)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : v*(1+ε)*(k:ℝ) ≤ a^2) :
    1-Real.exp (-(k:ℝ)*ε^2/16) ≤ ∫ y : E k in {y | ‖y‖ ≤ a}, density (1/(2*v)) y := by
  rw [density_set_integral hv (measurableSet_le measurable_norm measurable_const)]
  let A := {z : E k | ‖Real.sqrt v • z‖ ≤ a}
  have hA : MeasurableSet A := measurableSet_le (by fun_prop) measurable_const
  have hs : Aᶜ ⊆ {z : E k | (1+ε)*(k:ℝ) ≤ ‖z‖^2} := by
    intro z hz
    have hz' : a < ‖Real.sqrt v • z‖ := lt_of_not_ge hz
    have hh : a^2 ≤ ‖Real.sqrt v • z‖^2 := pow_le_pow_left₀ ha hz'.le 2
    rw [norm_scaled_sq hv.le] at hh
    change (1+ε)*(k:ℝ) ≤ ‖z‖^2
    nlinarith
  have H := (measureReal_mono (μ := stdGaussian (E k)) hs).trans (gaussian_norm_sq_upper hε hε1)
  rw [probReal_compl_eq_one_sub hA] at H
  change 1-Real.exp (-(k:ℝ)*ε^2/16) ≤ (stdGaussian (E k)).real A
  linarith

lemma density_large_ball_lower {k : ℕ} {v b ε : ℝ} (hv : 0 < v) (hb : 0 ≤ b)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : b^2 ≤ v*(1-ε)*(k:ℝ)) :
    1-Real.exp (-(k:ℝ)*ε^2/16) ≤ ∫ y : E k in {y | b < ‖y‖}, density (1/(2*v)) y := by
  have _ := hb
  rw [density_set_integral hv (measurableSet_lt measurable_const measurable_norm)]
  let A := {z : E k | b < ‖Real.sqrt v • z‖}
  have hA : MeasurableSet A := measurableSet_lt measurable_const (by fun_prop)
  have hs : Aᶜ ⊆ {z : E k | ‖z‖^2 ≤ (1-ε)*(k:ℝ)} := by
    intro z hz
    have hz' : ‖Real.sqrt v • z‖ ≤ b := le_of_not_gt hz
    have hh : ‖Real.sqrt v • z‖^2 ≤ b^2 := pow_le_pow_left₀ (norm_nonneg _) hz' 2
    rw [norm_scaled_sq hv.le] at hh
    change ‖z‖^2 ≤ (1-ε)*(k:ℝ)
    nlinarith
  have H := (measureReal_mono (μ := stdGaussian (E k)) hs).trans (gaussian_norm_sq_lower hε hε1)
  rw [probReal_compl_eq_one_sub hA] at H
  change 1-Real.exp (-(k:ℝ)*ε^2/16) ≤ (stdGaussian (E k)).real A
  linarith

lemma mixture_scale_small {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {v : Ω → ℝ} (hm : Measurable v) (hv : ∀ x, 0 < v x)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) (hε1 : ε < 1) :
    (1-Real.exp (-(k:ℝ)*ε^2/16))*μ.real {x | v x*(1+ε)*(k:ℝ) ≤ a^2} ≤
      ∫ y : E k in {y | ‖y‖ ≤ a}, ∫ x, density (1/(2*v x)) y ∂μ := by
  classical
  let B := {x | v x*(1+ε)*(k:ℝ) ≤ a^2}
  have hB : MeasurableSet B := measurableSet_le (by fun_prop) measurable_const
  have hkernel : Integrable (fun x => ∫ y : E k in {y | ‖y‖ ≤ a}, density (1/(2*v x)) y) μ := by
    exact ((integrable_mixture_kernel μ hm hv).mono_measure
      (Measure.prod_mono le_rfl Measure.restrict_le_self)).integral_prod_left
  have hpoint (x : Ω) : B.indicator (fun _ => 1-Real.exp (-(k:ℝ)*ε^2/16)) x ≤
      ∫ y : E k in {y | ‖y‖ ≤ a}, density (1/(2*v x)) y := by
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx]
      exact density_small_ball_lower (hv x) ha hε hε1 hx
    · rw [indicator_of_notMem hx]
      exact integral_nonneg (fun y => (density_pos (by have := hv x; positivity) y).le)
  have H := integral_mono ((integrable_const _).indicator hB) hkernel hpoint
  rw [integral_indicator hB,integral_const,smul_eq_mul] at H
  simp only [measureReal_def,Measure.restrict_apply_univ] at H
  rw [mixture_set_integral μ hm hv]
  simpa only [B,measureReal_def,mul_comm] using H

lemma mixture_scale_large {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {v : Ω → ℝ} (hm : Measurable v) (hv : ∀ x, 0 < v x)
    {b ε : ℝ} (hb : 0 ≤ b) (hε : 0 < ε) (hε1 : ε < 1) :
    (1-Real.exp (-(k:ℝ)*ε^2/16))*μ.real {x | b^2 ≤ v x*(1-ε)*(k:ℝ)} ≤
      ∫ y : E k in {y | b < ‖y‖}, ∫ x, density (1/(2*v x)) y ∂μ := by
  classical
  let B := {x | b^2 ≤ v x*(1-ε)*(k:ℝ)}
  have hB : MeasurableSet B := measurableSet_le measurable_const (by fun_prop)
  have hkernel : Integrable (fun x => ∫ y : E k in {y | b < ‖y‖}, density (1/(2*v x)) y) μ := by
    exact ((integrable_mixture_kernel μ hm hv).mono_measure
      (Measure.prod_mono le_rfl Measure.restrict_le_self)).integral_prod_left
  have hpoint (x : Ω) : B.indicator (fun _ => 1-Real.exp (-(k:ℝ)*ε^2/16)) x ≤
      ∫ y : E k in {y | b < ‖y‖}, density (1/(2*v x)) y := by
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx]
      exact density_large_ball_lower (hv x) hb hε hε1 hx
    · rw [indicator_of_notMem hx]
      exact integral_nonneg (fun y => (density_pos (by have := hv x; positivity) y).le)
  have H := integral_mono ((integrable_const _).indicator hB) hkernel hpoint
  rw [integral_indicator hB,integral_const,smul_eq_mul] at H
  simp only [measureReal_def,Measure.restrict_apply_univ] at H
  rw [mixture_set_integral μ hm hv]
  simpa only [B,measureReal_def,mul_comm] using H



end SingleLatticeCovering.GaussianDensity

namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology BigOperators

lemma stdGaussian_norm_second (k : ℕ) :
    (∫ z : E k, ‖z‖^2 ∂stdGaussian (E k))=(k:ℝ) := by
  have hi (i : Fin k) : Integrable (fun x : E k => (x i)^2) (stdGaussian (E k)) := by
    have H := (IsGaussian.memLp_two_id (μ := stdGaussian (E k))).continuousLinearMap_comp (EuclideanSpace.proj i : E k →L[ℝ] ℝ)
    exact H.integrable_sq
  have hinner (u v : E k) : (∫ z : E k, ⟪u,z⟫*⟪v,z⟫ ∂stdGaussian (E k))=⟪u,v⟫ := by
    have H := covarianceBilin_apply (μ := stdGaussian (E k)) IsGaussian.memLp_two_id u v
    simp only [id_eq,integral_id_stdGaussian,sub_zero,covarianceBilin_stdGaussian
      ] at H
    exact H.symm
  have hh (i : Fin k) : (∫ z : E k, (z i)^2 ∂stdGaussian (E k))=1 := by
    have H := hinner (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
    simpa only [EuclideanSpace.inner_single_left,one_mul,EuclideanSpace.inner_single_right,
      PiLp.single_apply,mul_one,one_pow,←sq,map_one,ite_true] using H
  have he (z : E k) : ‖z‖^2=∑ i, (z i)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs,sq_abs]
  simp only [he]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp only [hh,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

lemma density_tail_markov {k : ℕ} {v T : ℝ} (hv : 0 < v) (hT : 0 < T) :
    (∫ y : E k in {y | T < ‖y‖}, density (1/(2*v)) y) ≤ (k:ℝ)*v/T^2 := by
  rw [density_set_integral hv (measurableSet_lt measurable_const measurable_norm)]
  have hm : Integrable (fun z : E k => ‖Real.sqrt v • z‖^2) (stdGaussian (E k)) := by
    simp only [norm_scaled_sq hv.le]
    exact ((IsGaussian.memLp_two_id (μ := stdGaussian (E k))).norm.integrable_sq).const_mul _
  have H := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun z : E k => sq_nonneg ‖Real.sqrt v • z‖)) hm (T^2)
  have hs : {z : E k | T < ‖Real.sqrt v • z‖} ⊆ {z | T^2 ≤ ‖Real.sqrt v • z‖^2} := by
    intro z hz
    exact pow_le_pow_left₀ hT.le hz.le 2
  have hb := measureReal_mono (μ := stdGaussian (E k)) hs
  simp only [norm_scaled_sq hv.le] at H hb
  change (stdGaussian (E k)).real {z | T < ‖Real.sqrt v • z‖} ≤ (k:ℝ)*v/T^2
  rw [integral_const_mul,stdGaussian_norm_second] at H
  apply (le_div_iff₀ (sq_pos_of_pos hT)).mpr
  nlinarith

lemma mixture_tail_markov {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {v : Ω → ℝ} (hm : Measurable v)
    (hv : ∀ x, 0 < v x) (hi : Integrable v μ) {T : ℝ} (hT : 0 < T) :
    (∫ y : E k in (Metric.closedBall (0:E k) T)ᶜ,
      ∫ x, density (1/(2*v x)) y ∂μ) ≤ (k:ℝ)*(∫ x, v x ∂μ)/T^2 := by
  have he : (Metric.closedBall (0:E k) T)ᶜ={y : E k | T < ‖y‖} := by
    ext y
    simp only [Set.mem_compl_iff,Metric.mem_closedBall,dist_zero_right,not_le,mem_ofPred_eq]
  rw [he,mixture_set_integral μ hm hv]
  have hi' : Integrable (fun x => ∫ y : E k in {y | T < ‖y‖}, density (1/(2*v x)) y) μ :=
    ((integrable_mixture_kernel μ hm hv).mono_measure
      (Measure.prod_mono le_rfl Measure.restrict_le_self)).integral_prod_left
  have H := integral_mono hi' ((hi.const_mul (k:ℝ)).div_const (T^2))
    (fun x => density_tail_markov (hv x) hT)
  simpa only [integral_div,integral_const_mul] using H


end SingleLatticeCovering.GaussianDensity

end
end
end
end
end

section

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter Sections Isotropization
open scoped ENNReal Topology RealInnerProductSpace

lemma logConcave_smoothed_volume_E {n D : ℕ} {K : Set (Isotropization.E n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (A : Isotropization.E n →ₗ[ℝ] Isotropization.E D)
    {c : ℝ} (hcn : 0 ≤ c) :
    LogConcave (fun y => ∫ x in K, Real.exp (-c*‖y-A x‖^2)) := by
  let e := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toContinuousLinearEquiv
  have hp : MeasurePreserving e volume volume := PiLp.volume_preserving_ofLp (Fin n)
  have hK' : IsCompact (e '' K) := hK.image e.continuous
  have he (y : Isotropization.E D) : (∫ x in K, Real.exp (-c*‖y-A x‖^2))=
      ∫ z in e '' K, smoothingKernel (A.comp e.symm.toLinearMap) c y z := by
    have H := (hp.restrict_preimage hK'.measurableSet).integral_comp
      e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
      (smoothingKernel (A.comp e.symm.toLinearMap) c y)
    rw [Set.preimage_image_eq _ e.injective] at H
    change (∫ x in K, Real.exp (-c*‖y-A (e.symm (e x))‖^2))=
      ∫ z in e '' K, smoothingKernel (A.comp e.symm.toLinearMap) c y z at H
    simpa only [e.symm_apply_apply] using H
  simp_rw [he]
  exact logConcave_smoothed_volume hK' (hc.linear_image e.toLinearMap) _ hcn

lemma logConcave_smoothed_uniform {n D : ℕ} {K : Set (Isotropization.E n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (A : Isotropization.E n →ₗ[ℝ] Isotropization.E D)
    (μ : Measure (Isotropization.E n)) (hdef : μ=(volume K)⁻¹ • volume.restrict K)
    {c : ℝ} (hcn : 0 ≤ c) :
    LogConcave (fun y => ∫ x, Real.exp (-c*‖y-A x‖^2) ∂μ) := by
  rw [hdef]
  simp only [integral_smul_measure,smul_eq_mul]
  exact LogConcave.const_mul (logConcave_smoothed_volume_E hK hc A hcn) ENNReal.toReal_nonneg
end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter Isotropization GaussianDensity Prekopa
open scoped ENNReal Topology RealInnerProductSpace BigOperators

noncomputable def colLinear {n k : ℕ} (g : MatrixSpace n k) : Isotropization.E n →ₗ[ℝ] Isotropization.E k where
  toFun := colApply g
  map_add' x z := by
    ext j
    simp only [colApply,PiLp.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' a x := by
    ext j
    simp only [colApply,PiLp.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp only [←Finset.mul_sum,mul_left_comm]

noncomputable def normalizedProjection {n k : ℕ} (μ : Measure (Isotropization.E n)) (s r : ℝ)
    (g : MatrixSpace n k) (y : Isotropization.E k) : ℝ :=
  (normalizer k (r^2/2))⁻¹*smoothedProjection μ s r g y

lemma normalizedProjection_kernel {n k : ℕ} (μ : Measure (Isotropization.E n)) (s r : ℝ)
    (g : MatrixSpace n k) (y : Isotropization.E k) :
    normalizedProjection μ s r g y=∫ x, density (r^2/2) (y-s•colApply g x) ∂μ := by
  rw [normalizedProjection,smoothedProjection,←integral_const_mul]
  congr 1
  funext x
  unfold density
  congr 2
  ring

lemma logConcave_normalizedProjection {n k : ℕ} {K : Set (Isotropization.E n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (μ : Measure (Isotropization.E n))
    (hdef : μ=(volume K)⁻¹ • volume.restrict K) (s r : ℝ) (g : MatrixSpace n k) :
    LogConcave (normalizedProjection μ s r g) := by
  have H := logConcave_smoothed_uniform hK hc (s • colLinear g) μ hdef (c := r^2/2) (by positivity)
  have he : (fun y => ∫ x, Real.exp (-(r^2/2)*‖y-(s • colLinear g) x‖^2) ∂μ)=
      smoothedProjection μ s r g := by
    funext y
    unfold smoothedProjection
    congr 1
    funext x
    change Real.exp (-(r^2/2)*‖y-s•colApply g x‖^2)=_
    congr 1
    ring
  rw [he] at H
  exact Prekopa.LogConcave.const_mul H (inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _))


end SingleLatticeCovering.GaussianProjection


end

end OAI
