import OAI.Analysis.HotSpots.Eigenfunction

namespace OAI

section ActualInteriorNodal

noncomputable section NodalVariationalInteriorLayer
open Set MeasureTheory Filter Metric
open scoped ContDiff InnerProductSpace Topology
namespace StrictHotSpots.InteriorNodal
open StrictHotSpots.Nodal

lemma minimizer_zero_of_open_zero {Ω : Set Plane} {u : Plane → ℝ} {g : Plane → Plane}
    (hΩ : IsOpen Ω) (hc : IsPreconnected Ω) (hb : Bornology.IsBounded Ω)
    (hv : 0 < (volume Ω).toReal) (hu : HasH1Gradient Ω u g)
    (hm : (∫ x in Ω, u x) = 0)
    (he : (∫ x in Ω, ‖g x‖^2) = firstPositiveNeumannValue Ω * (∫ x in Ω, (u x)^2))
    (hz : ∃ a ∈ Ω, ∃ ε > 0, ∀ᵐ x ∂volume, x ∈ ball a ε → u x = 0) :
    u =ᵐ[volume.restrict Ω] 0 := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  have hi : IntegrableOn u Ω := hu.1.integrable (by norm_num)
  have hp := planeWeakEquation_of_euler hΩ hu (fun v k hvk =>
    minimizer_euler hb hv hu hvk hm he)
  exact (ae_restrict_iff' hΩ.measurableSet).mpr (planeWeak_uniqueContinuation hΩ hc hi hp hz)

lemma integral_indicator_pos {Ω U : Set Plane} {u : Plane → ℝ}
    (_hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hU : IsOpen U)
    (hs : U ⊆ Ω) (hne : U.Nonempty) (hc : ContinuousOn u Ω)
    (hu : MemLp u 2 (volume.restrict Ω)) (hp : ∀ x ∈ U, 0 < u x) :
    0 < ∫ x in Ω, U.indicator u x := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  have hi := (hu.indicator hU.measurableSet).integrable (by norm_num : 1 ≤ (2:ENNReal))
  have hn (x : Plane) : 0 ≤ U.indicator u x := by
    by_cases hx : x ∈ U
    · simpa only [indicator_of_mem hx] using (hp x hx).le
    · simp only [indicator_of_notMem hx,le_refl]
  have hnn : 0 ≤ ∫ x in Ω, U.indicator u x := integral_nonneg hn
  by_contra hf
  have hz : (∫ x in Ω, U.indicator u x) = 0 := le_antisymm (le_of_not_gt hf) hnn
  have hae := (integral_eq_zero_iff_of_nonneg hn hi).mp hz
  have he : u =ᵐ[volume.restrict U] 0 := by
    have hh := ae_restrict_of_ae_restrict_of_subset hs hae
    filter_upwards [hh,ae_restrict_mem hU.measurableSet] with x hx hxm
    simpa only [indicator_of_mem hxm,Pi.zero_apply] using hx
  have hh := Measure.eqOn_open_of_ae_eq he hU (hc.mono hs) continuousOn_const
  obtain ⟨x,hx⟩ := hne
  have hp' := hp x hx
  simp only [hh hx,Pi.zero_apply,lt_self_iff_false] at hp'

lemma restriction_energy {Ω U : Set Plane} {u : Plane → ℝ}
    (hu : InInteriorNeumannEigenspace Ω u)
    (hH : HasH1Gradient Ω (U.indicator u) (U.indicator (gradient u))) :
    (∫ x in Ω, ‖U.indicator (gradient u) x‖^2) =
      firstPositiveNeumannValue Ω * (∫ x in Ω, (U.indicator u x)^2) := by
  have he := hu.2.2.2 _ _ hH
  convert he using 1
  · apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ U
      · simp only [indicator_of_mem hx,real_inner_self_eq_norm_sq]
      · simp only [indicator_of_notMem hx,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),inner_zero_right]
  · congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ U
      · simp only [indicator_of_mem hx,pow_two]
      · simp only [indicator_of_notMem hx,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero]

lemma disjoint_indicator_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U V : Set Plane} (hd : Disjoint U V) (g : Plane → E) (a b : ℝ) (x : Plane) :
    ‖a • U.indicator g x + b • V.indicator g x‖^2 =
      a^2 * ‖U.indicator g x‖^2 + b^2 * ‖V.indicator g x‖^2 := by
  by_cases hxU : x ∈ U
  · have hxV : x ∉ V := fun hxV => Set.disjoint_left.mp hd hxU hxV
    simp only [indicator_of_mem hxU,indicator_of_notMem hxV,smul_zero,add_zero,norm_zero,
      zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  · simp only [indicator_of_notMem hxU,smul_zero,zero_add,norm_zero,
      zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]

lemma disjoint_restriction_combination_energy {Ω U V : Set Plane} {u : Plane → ℝ}
    (hu : InInteriorNeumannEigenspace Ω u) (hd : Disjoint U V)
    (hU : HasH1Gradient Ω (U.indicator u) (U.indicator (gradient u)))
    (hV : HasH1Gradient Ω (V.indicator u) (V.indicator (gradient u))) (a b : ℝ) :
    (∫ x in Ω, ‖a • U.indicator (gradient u) x + b • V.indicator (gradient u) x‖^2) =
      firstPositiveNeumannValue Ω * (∫ x in Ω, (a * U.indicator u x + b * V.indicator u x)^2) := by
  have ha : (∫ x in Ω, ‖a • U.indicator (gradient u) x + b • V.indicator (gradient u) x‖^2) =
      a^2 * (∫ x in Ω, ‖U.indicator (gradient u) x‖^2) +
        b^2 * (∫ x in Ω, ‖V.indicator (gradient u) x‖^2) := by
    simp_rw [disjoint_indicator_norm_sq hd]
    rw [integral_add (hU.2.1.norm.integrable_sq.const_mul _) (hV.2.1.norm.integrable_sq.const_mul _),
      integral_const_mul,integral_const_mul]
  have hb : (∫ x in Ω, (a * U.indicator u x + b * V.indicator u x)^2) =
      a^2 * (∫ x in Ω, (U.indicator u x)^2) + b^2 * (∫ x in Ω, (V.indicator u x)^2) := by
    have he (x : Plane) := disjoint_indicator_norm_sq hd u a b x
    simp only [smul_eq_mul,Real.norm_eq_abs,sq_abs] at he
    simp_rw [he]
    rw [integral_add (hU.1.integrable_sq.const_mul _) (hV.1.integrable_sq.const_mul _),
      integral_const_mul,integral_const_mul]
  rw [ha,hb,restriction_energy hu hU,restriction_energy hu hV]
  ring

end StrictHotSpots.InteriorNodal

end NodalVariationalInteriorLayer


noncomputable section NodalConnectedInteriorLayer
open Set MeasureTheory Filter Metric
open scoped ContDiff InnerProductSpace Topology
namespace StrictHotSpots.InteriorNodal
open StrictHotSpots.Nodal

lemma gradient_neg_fun (u : Plane → ℝ) : gradient (-u) = -gradient u := by
  funext x
  simp only [gradient,Pi.neg_apply,fderiv_neg,map_neg]

lemma eigenfunction_neg {Ω : Set Plane} {u : Plane → ℝ}
    (hu : InInteriorNeumannEigenspace Ω u) : InInteriorNeumannEigenspace Ω (-u) := by
  refine ⟨hu.1.neg,?_,?_,?_⟩
  · simpa only [gradient_neg_fun,neg_one_smul] using hu.2.1.smul (-1)
  · simp only [Pi.neg_apply,integral_neg,hu.2.2.1,neg_zero]
  · intro v g hv
    simp only [gradient_neg_fun,Pi.neg_apply,inner_neg_left,neg_mul,integral_neg]
    rw [hu.2.2.2 v g hv]
    ring

lemma eigenfunction_has_negative {Ω : Set Plane} {u : Plane → ℝ}
    (hΩ : AdmissibleDomain Ω) (hu : InInteriorNeumannEigenspace Ω u)
    (hne : ∃ x ∈ Ω, u x ≠ 0) : ∃ x ∈ Ω, u x < 0 := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩ.2.2.1.measure_lt_top.ne
  by_contra hn
  push Not at hn
  have hae : 0 ≤ᵐ[volume.restrict Ω] u :=
    (ae_restrict_iff' hΩ.2.1.measurableSet).mpr (Eventually.of_forall hn)
  have hz := (integral_eq_zero_iff_of_nonneg_ae hae (hu.2.1.1.integrable (by norm_num))).mp hu.2.2.1
  have hall := Measure.eqOn_open_of_ae_eq hz hΩ.2.1 hu.1.continuousOn continuousOn_const
  obtain ⟨x,hx,hux⟩ := hne
  exact hux (hall hx)

lemma eigenfunction_has_positive {Ω : Set Plane} {u : Plane → ℝ}
    (hΩ : AdmissibleDomain Ω) (hu : InInteriorNeumannEigenspace Ω u)
    (hne : ∃ x ∈ Ω, u x ≠ 0) : ∃ x ∈ Ω, 0 < u x := by
  have hn : ∃ x ∈ Ω, (-u) x ≠ 0 := by
    obtain ⟨x,hx,hux⟩ := hne
    exact ⟨x,hx,by simpa only [Pi.neg_apply,neg_ne_zero] using hux⟩
  obtain ⟨x,hx,hux⟩ := eigenfunction_has_negative hΩ (eigenfunction_neg hu) hn
  exact ⟨x,hx,by simpa only [Pi.neg_apply,neg_lt_zero] using hux⟩

lemma no_two_positive_regions {Ω U V : Set Plane} {u : Plane → ℝ}
    (hΩ : AdmissibleDomain Ω) (hu : InInteriorNeumannEigenspace Ω u)
    (hU : IsOpen U) (hV : IsOpen V) (hsU : U ⊆ Ω) (hsV : V ⊆ Ω)
    (hnU : U.Nonempty) (hnV : V.Nonempty) (hd : Disjoint U V)
    (hpU : ∀ x ∈ U, 0 < u x) (hpV : ∀ x ∈ V, 0 < u x)
    (hhU : HasH1Gradient Ω (U.indicator u) (U.indicator (gradient u)))
    (hhV : HasH1Gradient Ω (V.indicator u) (V.indicator (gradient u)))
    (hneg : ∃ x ∈ Ω, u x < 0) : False := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩ.2.2.1.measure_lt_top.ne
  let A := ∫ x in Ω, U.indicator u x
  let B := ∫ x in Ω, V.indicator u x
  have hB : 0 < B := integral_indicator_pos hΩ.2.1 hΩ.2.2.1 hV hsV hnV
    hu.1.continuousOn hu.2.1.1 hpV
  let w := B • U.indicator u + (-A) • V.indicator u
  let g := B • U.indicator (gradient u) + (-A) • V.indicator (gradient u)
  have hw : HasH1Gradient Ω w g := (hhU.smul B).add (hhV.smul (-A))
  have hm : (∫ x in Ω, w x) = 0 := by
    change (∫ x in Ω, B * U.indicator u x + (-A) * V.indicator u x) = 0
    rw [integral_add ((hhU.1.integrable (by norm_num)).const_mul B)
      ((hhV.1.integrable (by norm_num)).const_mul (-A)),integral_const_mul,integral_const_mul]
    change B*A+(-A)*B=0
    ring
  have he : (∫ x in Ω, ‖g x‖^2) = firstPositiveNeumannValue Ω * (∫ x in Ω, (w x)^2) :=
    disjoint_restriction_combination_energy hu hd hhU hhV B (-A)
  have hz : ∃ a ∈ Ω, ∃ ε > 0, ∀ᵐ x ∂volume, x ∈ ball a ε → w x = 0 := by
    obtain ⟨a,ha,han⟩ := hneg
    have haU : {x | u x < 0} ∈ 𝓝 a :=
      (hu.1.continuousOn a ha).continuousAt (hΩ.2.1.mem_nhds ha) |>.eventually (gt_mem_nhds han)
    obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp haU
    refine ⟨a,ha,ε,hε,Eventually.of_forall fun x hx => ?_⟩
    have hn : u x < 0 := he hx
    have hxu : x ∉ U := fun hxu => (not_lt_of_ge (hpU x hxu).le) hn
    have hxv : x ∉ V := fun hxv => (not_lt_of_ge (hpV x hxv).le) hn
    simp only [w,Pi.add_apply,Pi.smul_apply,indicator_of_notMem hxu,indicator_of_notMem hxv,smul_zero,add_zero]
  have hv : 0 < (volume Ω).toReal := ENNReal.toReal_pos
    (ne_of_gt (hΩ.2.1.measure_pos volume hΩ.1)) hΩ.2.2.1.measure_lt_top.ne
  have hall := minimizer_zero_of_open_zero hΩ.2.1
    hΩ.2.2.2.1.isPathConnected.isConnected.isPreconnected hΩ.2.2.1 hv hw hm he hz
  have hvu : (fun x => B * u x) =ᵐ[volume.restrict U] 0 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsU hall,ae_restrict_mem hU.measurableSet] with x hx hxm
    have hxv : x ∉ V := fun hxv => Set.disjoint_left.mp hd hxm hxv
    simpa only [w,Pi.add_apply,Pi.smul_apply,indicator_of_mem hxm,indicator_of_notMem hxv,
      smul_zero,add_zero,smul_eq_mul,mul_zero] using hx
  have hcont : ContinuousOn (fun x => B*u x) U :=
    continuousOn_const.mul (hu.1.continuousOn.mono hsU)
  have hh := Measure.eqOn_open_of_ae_eq hvu hU hcont continuousOn_const
  obtain ⟨x,hx⟩ := hnU
  have hp := mul_pos hB (hpU x hx)
  have hzero : B*u x = 0 := hh hx
  linarith



lemma positive_set_connected {Ω : Set Plane} {u : Plane → ℝ}
    (hΩ : AdmissibleDomain Ω) (hu : InInteriorNeumannEigenspace Ω u)
    (hne : ∃ x ∈ Ω, u x ≠ 0) : IsConnected (Ω ∩ {x | 0 < u x}) := by
  let P := Ω ∩ {x | 0 < u x}
  have hopen : IsOpen P := positive_set_open hΩ.2.1 hu.1.continuousOn
  obtain ⟨a,ha,hua⟩ := eigenfunction_has_positive hΩ hu hne
  have hap : a ∈ P := ⟨ha,hua⟩
  have heq : P = connectedComponentIn P a := by
    apply subset_antisymm _ (connectedComponentIn_subset P a)
    intro b hb
    by_contra hba
    let U := connectedComponentIn P a
    let V := connectedComponentIn P b
    have hd : Disjoint U V := by
      apply Set.disjoint_left.mpr
      intro x hxU hxV
      have heq : U = V := (connectedComponentIn_eq hxU).trans (connectedComponentIn_eq hxV).symm
      have hbV : b ∈ V := mem_connectedComponentIn hb
      have hbU : b ∈ U := heq.symm ▸ hbV
      exact hba hbU
    exact no_two_positive_regions hΩ hu hopen.connectedComponentIn hopen.connectedComponentIn
      ((connectedComponentIn_subset P a).trans inter_subset_left)
      ((connectedComponentIn_subset P b).trans inter_subset_left)
      ⟨a,mem_connectedComponentIn hap⟩ ⟨b,mem_connectedComponentIn hb⟩ hd
      (fun x hx => (connectedComponentIn_subset P a hx).2)
      (fun x hx => (connectedComponentIn_subset P b hx).2)
      (positive_component_hasH1Gradient hΩ.2.1 hu.1 hu.2.1 a)
      (positive_component_hasH1Gradient hΩ.2.1 hu.1 hu.2.1 b)
      (eigenfunction_has_negative hΩ hu hne)
  rw [show Ω ∩ {x | 0 < u x} = P from rfl,heq]
  exact isConnected_connectedComponentIn_iff.mpr hap

lemma negative_set_connected {Ω : Set Plane} {u : Plane → ℝ}
    (hΩ : AdmissibleDomain Ω) (hu : InInteriorNeumannEigenspace Ω u)
    (hne : ∃ x ∈ Ω, u x ≠ 0) : IsConnected (Ω ∩ {x | u x < 0}) := by
  have hn : ∃ x ∈ Ω, (-u) x ≠ 0 := by
    obtain ⟨x,hx,hux⟩ := hne
    exact ⟨x,hx,by simpa only [Pi.neg_apply,neg_ne_zero] using hux⟩
  simpa only [Pi.neg_apply,neg_pos] using positive_set_connected hΩ (eigenfunction_neg hu) hn

end StrictHotSpots.InteriorNodal

end NodalConnectedInteriorLayer

end ActualInteriorNodal

section ActualInteriorBoundarySign

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace ENNReal
namespace StrictHotSpots.InteriorBoundarySign
open StrictHotSpots.BoundarySign
variable {Ω : Set Plane} {u : Plane → ℝ}
lemma gap_test (ho : IsOpen Ω) (hu : InInteriorNeumannEigenspace Ω u) (hc : ContinuousOn u (closure Ω))
    (hbound : Bornology.IsBounded Ω) (hb : ∀ x ∈ frontier Ω, u x ≤ 0)
    {lam : ℝ} (hg : ∀ v : H10 ho, lam * ‖H10.value ho v‖^2 ≤ ‖H10.grad ho v‖^2)
    (n : ℕ) :
    lam * (∫ x in Ω, (Nodal.cutoff n (u x))^2) ≤
      ∫ x in Ω, (deriv (Nodal.cutoff n) (u x))^2 * ‖gradient u x‖^2 := by
  let f := test_interior ho hu.1 hc hbound hb n
  have hh := hg (smoothTestToH10 ho f)
  change lam * ‖(HasH1Gradient.test ho f.property.1 f.property.2.1).1.toLp f.val‖^2 ≤
    ‖(HasH1Gradient.test ho f.property.1 f.property.2.1).2.1.toLp (gradient f.val)‖^2 at hh
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    L2Inner.toLp_pair,L2Inner.toLp_pair] at hh
  have hval : (∫ x in Ω, inner ℝ (f.val x) (f.val x)) = ∫ x in Ω, (Nodal.cutoff n (u x))^2 := by
    apply setIntegral_congr_fun ho.measurableSet
    intro x hx
    simp only [f,test_interior,cut,indicator_of_mem hx,RCLike.inner_apply,conj_trivial,pow_two]
  have hgrad : (∫ x in Ω, inner ℝ (gradient f.val x) (gradient f.val x)) =
      ∫ x in Ω, (deriv (Nodal.cutoff n) (u x))^2 * ‖gradient u x‖^2 := by
    apply setIntegral_congr_fun ho.measurableSet
    intro x hx
    dsimp only
    rw [real_inner_self_eq_norm_sq]
    change ‖gradient (cut Ω u n) x‖^2 = _
    rw [cut_gradient_interior ho hu.1 n hx,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  rwa [hval,hgrad] at hh

lemma equation_test (ho : IsOpen Ω) (hu : InInteriorNeumannEigenspace Ω u) (hc : ContinuousOn u (closure Ω))
    (hbound : Bornology.IsBounded Ω) (hb : ∀ x ∈ frontier Ω, u x ≤ 0) (n : ℕ) :
    (∫ x in Ω, deriv (Nodal.cutoff n) (u x) * ‖gradient u x‖^2) =
      firstPositiveNeumannValue Ω * (∫ x in Ω, u x * Nodal.cutoff n (u x)) := by
  let f := test_interior ho hu.1 hc hbound hb n
  have hh := hu.2.2.2 f.val (gradient f.val) (HasH1Gradient.test ho f.property.1 f.property.2.1)
  convert hh using 1
  · apply setIntegral_congr_fun ho.measurableSet
    intro x hx
    change _ = inner ℝ (gradient u x) (gradient (cut Ω u n) x)
    rw [cut_gradient_interior ho hu.1 n hx,inner_smul_right,real_inner_self_eq_norm_sq]
  · congr 1
    apply setIntegral_congr_fun ho.measurableSet
    intro x hx
    simp only [f,test_interior,cut,indicator_of_mem hx]
lemma positivePart_square (t : ℝ) : (if 0 < t then t^2 else 0) = (max t 0)^2 := by
  by_cases h : 0 < t
  · rw [ite_eq_left h,max_eq_left h.le]
  · rw [ite_eq_right h,max_eq_right (le_of_not_gt h),zero_pow (by decide : 2 ≠ 0)]
lemma positivePart_memLp (hu : MemLp u 2 (volume.restrict Ω)) :
    MemLp (fun x => max (u x) 0) 2 (volume.restrict Ω) := by
  apply hu.mono (((continuous_id.max continuous_const : Continuous (fun t : ℝ => max t 0))).comp_aestronglyMeasurable hu.aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    change ‖max (u x) 0‖ ≤ ‖u x‖
    by_cases h : 0 ≤ u x
    · rw [max_eq_left h]
    · rw [max_eq_right (le_of_not_ge h),norm_zero]
      exact norm_nonneg _




lemma nonpos_of_boundary_nonpos (ho : IsOpen Ω) (hne : Ω.Nonempty)
    (hbound : Bornology.IsBounded Ω) (hu : InInteriorNeumannEigenspace Ω u) (hc : ContinuousOn u (closure Ω))
    (hb : ∀ x ∈ frontier Ω, u x ≤ 0) : ∀ x ∈ Ω, u x ≤ 0 := by
  obtain ⟨lam,_hl,hgap,hDir⟩ := H10.subcritical ho hne hbound
  let M := ∫ x in Ω, if 0 < u x then (u x)^2 else 0
  let E := ∫ x in Ω, if 0 < u x then ‖gradient u x‖^2 else 0
  have hIg : Integrable (fun x => ‖gradient u x‖^2) (volume.restrict Ω) :=
    hu.2.1.2.1.integrable_norm_pow (by norm_num)
  have hM := Nodal.cutoff_square_integral hu.2.1.1
  have hE := Nodal.cutoff_deriv_square_integral hu.2.1.1.aestronglyMeasurable hIg (fun x => sq_nonneg _)
  have hi : lam * M ≤ E := le_of_tendsto_of_tendsto
    (hM.const_mul lam) hE (Eventually.of_forall (gap_test ho hu hc hbound hb hDir))
  have hD := Nodal.cutoff_deriv_integral hu.2.1.1.aestronglyMeasurable hIg (fun x => sq_nonneg _)
  have hP := Nodal.cutoff_product_integral hu.2.1.1
  have he : E = firstPositiveNeumannValue Ω * M := by
    apply tendsto_nhds_unique hD
    apply (hP.const_mul (firstPositiveNeumannValue Ω)).congr
    intro n
    exact (equation_test ho hu hc hbound hb n).symm
  have hMn : 0 ≤ M := integral_nonneg fun x => by split_ifs <;> positivity
  have hMz : M = 0 := by nlinarith
  have hMz' : (∫ x in Ω, (max (u x) 0)^2) = 0 := by
    simpa only [M,positivePart_square] using hMz
  have hz := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) (positivePart_memLp hu.2.1.1).integrable_sq).mp hMz'
  have hae : (fun x => max (u x) 0) =ᵐ[volume.restrict Ω] 0 := by
    filter_upwards [hz] with x hx
    exact eq_zero_of_pow_eq_zero hx
  have hall := Measure.eqOn_open_of_ae_eq hae ho
    ((continuous_id.max continuous_const : Continuous (fun t : ℝ => max t 0)).comp_continuousOn
      hu.1.continuousOn) continuousOn_const
  intro x hx
  exact (le_max_left (u x) 0).trans (le_of_eq (hall hx))

lemma zero_of_boundary_nonpos (ho : IsOpen Ω) (hne : Ω.Nonempty)
    (hbound : Bornology.IsBounded Ω) (hu : InInteriorNeumannEigenspace Ω u) (hc : ContinuousOn u (closure Ω))
    (hb : ∀ x ∈ frontier Ω, u x ≤ 0) : ∀ x ∈ Ω, u x = 0 := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hbound.measure_lt_top.ne
  have hnp := nonpos_of_boundary_nonpos ho hne hbound hu hc hb
  have hn : 0 ≤ᵐ[volume.restrict Ω] -u := by
    filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
    simpa only [Pi.neg_apply,Pi.zero_apply,neg_nonneg] using hnp x hx
  have hm : (∫ x in Ω, (-u) x) = 0 := by
    simp only [Pi.neg_apply,integral_neg,hu.2.2.1,neg_zero]
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn (hu.2.1.1.neg.integrable (by norm_num))).mp hm
  have hae : u =ᵐ[volume.restrict Ω] 0 := by
    filter_upwards [hz] with x hx
    simpa only [Pi.neg_apply,Pi.zero_apply,neg_eq_zero] using hx
  exact fun x hx => Measure.eqOn_open_of_ae_eq hae ho
    hu.1.continuousOn continuousOn_const hx

lemma exists_boundary_pos (ho : IsOpen Ω) (hbound : Bornology.IsBounded Ω)
    (hu : InInteriorNeumannEigenspace Ω u) (hc : ContinuousOn u (closure Ω)) (hne : ∃ x ∈ Ω, u x ≠ 0) :
    ∃ x ∈ frontier Ω, 0 < u x := by
  by_contra hn
  push Not at hn
  obtain ⟨x,hx,hux⟩ := hne
  exact hux (zero_of_boundary_nonpos ho ⟨x,hx⟩ hbound hu hc hn x hx)
lemma eigen_neg (hu : InInteriorNeumannEigenspace Ω u) : InInteriorNeumannEigenspace Ω (-u) := by
  have hg : gradient (-u) = -gradient u := by
    funext x
    simp only [gradient,Pi.neg_apply,fderiv_neg,map_neg]
  refine ⟨hu.1.neg,?_,?_,?_⟩
  · simpa only [hg,neg_one_smul] using hu.2.1.smul (-1)
  · simp only [Pi.neg_apply,integral_neg,hu.2.2.1,neg_zero]
  · intro v g hv
    simp only [hg,Pi.neg_apply,inner_neg_left,neg_mul,integral_neg]
    rw [hu.2.2.2 v g hv]
    ring
lemma exists_boundary_neg (ho : IsOpen Ω) (hbound : Bornology.IsBounded Ω)
    (hu : InInteriorNeumannEigenspace Ω u) (hc : ContinuousOn u (closure Ω)) (hne : ∃ x ∈ Ω, u x ≠ 0) :
    ∃ x ∈ frontier Ω, u x < 0 := by
  have hn : ∃ x ∈ Ω, (-u) x ≠ 0 := by
    obtain ⟨x,hx,hux⟩ := hne
    exact ⟨x,hx,by simpa only [Pi.neg_apply,neg_ne_zero] using hux⟩
  obtain ⟨x,hx,hux⟩ := exists_boundary_pos ho hbound (eigen_neg hu) hc.neg hn
  exact ⟨x,hx,by simpa only [Pi.neg_apply,neg_pos] using hux⟩

end StrictHotSpots.InteriorBoundarySign
end
end ActualInteriorBoundarySign

section MultiplicityComplete

noncomputable section

section PositiveWeightLayer
open Set Filter MeasureTheory Function
open scoped Topology InnerProductSpace
namespace StrictHotSpots.PositiveWeight
variable {X E : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (μ : Measure X) [IsFiniteMeasure μ]

omit [Nonempty X] in
lemma continuous_integrable {G : Type*} [NormedAddCommGroup G] (f : C(X,G)) : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [Nonempty X] [FiniteDimensional ℝ E] in
lemma product_integrable (F : C(X,E)) (f : C(X,ℝ)) : Integrable (fun s => f s • F s) μ :=
  (f.continuous.smul F.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def momentLinear (F : C(X,E)) : C(X,ℝ) →ₗ[ℝ] E where
  toFun f := ∫ s, f s • F s ∂μ
  map_add' f g := by
    simp only [ContinuousMap.add_apply,add_smul]
    exact integral_add (product_integrable μ F f) (product_integrable μ F g)
  map_smul' a f := by
    simp only [ContinuousMap.smul_apply,smul_eq_mul,mul_smul,integral_smul,RingHom.id_apply]

def moment (F : C(X,E)) : C(X,ℝ) →L[ℝ] E :=
  (momentLinear μ F).mkContinuous (‖F‖ * μ.real univ) (fun f => by
    have hh := norm_integral_le_of_norm_le_const (μ := μ)
      (Eventually.of_forall fun s => show ‖f s • F s‖ ≤ ‖f‖*‖F‖ by
        rw [norm_smul]
        exact mul_le_mul (f.norm_coe_le_norm s) (F.norm_coe_le_norm s) (norm_nonneg _) (norm_nonneg _))
    change ‖∫ s, f s • F s ∂μ‖ ≤ _
    nlinarith only [hh])
omit [Nonempty X] [FiniteDimensional ℝ E] in
lemma moment_apply (F : C(X,E)) (f : C(X,ℝ)) : moment μ F f = ∫ s, f s • F s ∂μ := rfl

def probe (F : C(X,E)) : E →ₗ[ℝ] C(X,ℝ) where
  toFun a := ⟨fun s => inner ℝ a (F s),continuous_const.inner F.continuous⟩
  map_add' a b := by
    ext s
    change inner ℝ (a+b) (F s) = inner ℝ a (F s) + inner ℝ b (F s)
    exact inner_add_left _ _ _
  map_smul' c a := by
    ext s
    change inner ℝ (c • a) (F s) = c * inner ℝ a (F s)
    simp only [inner_smul_left,conj_trivial]

omit [Nonempty X] in
lemma dual_moment (F : C(X,E)) (f : C(X,ℝ)) (l : E →L[ℝ] ℝ) :
    l (moment μ F f) = ∫ s, f s * l (F s) ∂μ := by
  rw [moment_apply,← l.integral_comp_comm (product_integrable μ F f)]
  congr 1
  funext s
  exact l.map_smul (f s) (F s)

omit [Nonempty X] in
lemma integral_sq_pos [μ.IsOpenPosMeasure] (f : C(X,ℝ)) (hf : ∃ x, f x ≠ 0) :
    0 < ∫ s, (f s)^2 ∂μ := by
  have hn : 0 ≤ ∫ s, (f s)^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  by_contra hp
  have hz : (∫ s, (f s)^2 ∂μ) = 0 := le_antisymm (le_of_not_gt hp) hn
  have hi : Integrable (fun s => (f s)^2) μ :=
    (f.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have ha := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).mp hz
  have hae : f =ᵐ[μ.restrict univ] (0 : X → ℝ) := by
    rw [Measure.restrict_univ]
    filter_upwards [ha] with x hx
    exact eq_zero_of_pow_eq_zero hx
  have he := Measure.eqOn_open_of_ae_eq hae isOpen_univ f.continuous.continuousOn continuousOn_const
  obtain ⟨x,hx⟩ := hf
  exact hx (he (mem_univ x))

omit [Nonempty X] in
lemma moment_surjective [μ.IsOpenPosMeasure] (F : C(X,E))
    (hF : ∀ a : E, a ≠ 0 → ∃ s, 0 < inner ℝ a (F s)) : Surjective (moment μ F) := by
  let G : E →ₗ[ℝ] E := (moment μ F).toLinearMap.comp (probe F)
  have hz (a : E) (ha : G a = 0) : a = 0 := by
    by_contra hn
    obtain ⟨s,hs⟩ := hF a hn
    have hp := integral_sq_pos μ (probe F a) ⟨s,ne_of_gt hs⟩
    have he := dual_moment μ F (probe F a) (innerSL ℝ a)
    have hv : (∫ s, (probe F a s)^2 ∂μ) = 0 := by
      change inner ℝ a (G a) = ∫ s, inner ℝ a (F s) * inner ℝ a (F s) ∂μ at he
      rw [ha,inner_zero_right] at he
      simpa only [probe,LinearMap.coe_mk,AddHom.coe_mk,ContinuousMap.coe_mk,pow_two] using he.symm
    linarith
  have hi : Injective G := by
    intro a b hab
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub,hab,sub_self]
  intro a
  obtain ⟨b,hb⟩ := G.surjective_of_injective hi a
  exact ⟨probe F b,hb⟩

def positive : Set C(X,ℝ) := {f | ∀ s, 0 < f s}
omit [CompactSpace X] [Nonempty X] [MeasurableSpace X] [OpensMeasurableSpace X] in
lemma positive_convex : Convex ℝ (positive (X := X)) := by
  intro f hf g hg a b ha hb hab s
  change 0 < a * f s + b * g s
  by_cases hza : a = 0
  · have hbo : b = 1 := by linarith
    simpa [hza,hbo] using hg s
  · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm hza)) (hf s))
      (mul_nonneg hb (hg s).le)
omit [MeasurableSpace X] [OpensMeasurableSpace X] in
lemma positive_open : IsOpen (positive (X := X)) := by
  rw [Metric.isOpen_iff]
  intro f hf
  obtain ⟨x,_,hx⟩ := isCompact_univ.exists_isMinOn (univ_nonempty : (univ : Set X).Nonempty) f.continuous.continuousOn
  refine ⟨f x,hf x,?_⟩
  intro g hg s
  have hd : |g s-f s| < f x := by
    rw [← Real.dist_eq]
    exact (ContinuousMap.dist_apply_le_dist s).trans_lt hg
  have hm : f x ≤ f s := hx (mem_univ s)
  have hl := (abs_lt.mp hd).1
  linarith




theorem exists_positive_annihilator [μ.IsOpenPosMeasure] (F : C(X,E))
    (hF : ∀ a : E, a ≠ 0 → ∃ s, 0 < inner ℝ a (F s)) :
    ∃ w : C(X,ℝ), (∀ s, 0 < w s) ∧ (∫ s, w s • F s ∂μ) = 0 := by
  let T := moment μ F
  have hT : Surjective T := moment_surjective μ F hF
  have ho : IsOpen (T '' positive) := T.isOpenMap hT _ positive_open
  have hc : Convex ℝ (T '' positive) := positive_convex.linear_image T.toLinearMap
  have hz : (0:E) ∈ T '' positive := by
    by_contra hn
    obtain ⟨l,hl⟩ := geometric_hahn_banach_open_point hc ho hn
    let one : C(X,ℝ) := ContinuousMap.const X 1
    have hone : one ∈ positive := fun _ => zero_lt_one
    have hnegative (f : C(X,ℝ)) (hf : f ∈ positive) : l (T f) < 0 := by
      simpa only [map_zero] using hl (T f) ⟨f,hf,rfl⟩
    have hl0 : l ≠ 0 := by
      intro he
      have h := hnegative one hone
      rw [he] at h
      exact (lt_irrefl (0:ℝ)) h
    let a : E := (InnerProductSpace.toDual ℝ E).symm l
    have ha : a ≠ 0 := by
      intro hz
      have he := congrArg (InnerProductSpace.toDual ℝ E) hz
      simp only [a,LinearIsometryEquiv.apply_symm_apply,map_zero] at he
      exact hl0 he
    obtain ⟨s,hs⟩ := hF a ha
    have hla : ∀ x, l (F x) = inner ℝ a (F x) := by
      intro x
      exact congrArg (fun k : E →L[ℝ] ℝ => k (F x))
        ((InnerProductSpace.toDual ℝ E).apply_symm_apply l).symm
    let q : C(X,ℝ) := ⟨fun x => max (l (F x)) 0,(l.continuous.comp F.continuous).max continuous_const⟩
    have hqnonneg (x : X) : 0 ≤ q x := le_max_right _ _
    have hqpos : 0 < q s := lt_of_lt_of_le (by rwa [hla s]) (le_max_left _ _)
    let A := ∫ x, (q x)^2 ∂μ
    have hA : 0 < A := integral_sq_pos μ q ⟨s,ne_of_gt hqpos⟩
    have he : l (T q) = A := by
      rw [show T q = moment μ F q from rfl,dual_moment]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change max (l (F x)) 0 * l (F x) = (max (l (F x)) 0)^2
        by_cases h : 0 ≤ l (F x)
        · rw [max_eq_left h,pow_two]
        · rw [max_eq_right (le_of_not_ge h),zero_mul,zero_pow (by decide : 2 ≠ 0)]
    let B := l (T one)
    let c := (|B|+1)/A
    have hcpos : 0 < c := div_pos (by positivity) hA
    let f := one + c • q
    have hf : f ∈ positive := by
      intro x
      change 0 < 1 + c * q x
      linarith [mul_nonneg hcpos.le (hqnonneg x)]
    have hbad := hnegative f hf
    have hval : l (T f) = B + (|B|+1) := by
      simp only [f,map_add,map_smul,smul_eq_mul,he]
      change B + c*A = B+(|B|+1)
      dsimp only [c]
      rw [div_mul_cancel₀ _ hA.ne']
    rw [hval] at hbad
    linarith [neg_abs_le B]
  obtain ⟨w,hw,he⟩ := hz
  exact ⟨w,hw,he⟩
end StrictHotSpots.PositiveWeight
end PositiveWeightLayer

section CirclePositiveWeightLayer
open Set MeasureTheory
open scoped Topology InnerProductSpace
namespace StrictHotSpots.PositiveWeight
local instance : Fact (0 < 2*Real.pi) := ⟨Real.two_pi_pos⟩
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]


theorem exists_circle_weight (F : C(Circle,E))
    (hF : ∀ a : E, a ≠ 0 → ∃ s, 0 < inner ℝ a (F s)) :
    ∃ w : ℝ → ℝ, Continuous w ∧ Function.Periodic w (2*Real.pi) ∧
      (∀ θ, 0 < w θ) ∧ ∀ a : E,
        (∫ θ in (0:ℝ)..2*Real.pi, w θ*inner ℝ a (F (Circle.exp θ))) = 0 := by
  let G : C(AddCircle (2*Real.pi),E) := F.comp ⟨AddCircle.homeomorphCircle',AddCircle.homeomorphCircle'.continuous⟩
  have hG (a : E) (ha : a ≠ 0) : ∃ s, 0 < inner ℝ a (G s) := by
    obtain ⟨s,hs⟩ := hF a ha
    refine ⟨AddCircle.homeomorphCircle'.symm s,?_⟩
    change 0 < inner ℝ a (F (AddCircle.homeomorphCircle' (AddCircle.homeomorphCircle'.symm s)))
    rwa [Homeomorph.apply_symm_apply]
  obtain ⟨w,hw,he⟩ := exists_positive_annihilator (volume : Measure (AddCircle (2*Real.pi))) G hG
  let W : ℝ → ℝ := fun θ => w (θ : AddCircle (2*Real.pi))
  refine ⟨W,w.continuous.comp (AddCircle.continuous_mk' (2*Real.pi)),?_,fun θ => hw _,?_⟩
  · intro θ
    exact congrArg w (AddCircle.coe_add_period (2*Real.pi) θ)
  · intro a
    have hh := dual_moment (volume : Measure (AddCircle (2*Real.pi))) G w (innerSL ℝ a)
    rw [moment_apply,he,map_zero] at hh
    have hI := AddCircle.intervalIntegral_preimage (2*Real.pi) 0
      (fun s : AddCircle (2*Real.pi) => w s*inner ℝ a (G s))
    simp only [zero_add] at hI
    simpa only [W,G,ContinuousMap.comp_apply,ContinuousMap.coe_mk,
      AddCircle.homeomorphCircle'_apply_mk] using hI.trans hh.symm
end StrictHotSpots.PositiveWeight
end CirclePositiveWeightLayer

section PlanarCrossingLayer


open Set Filter _root_.Complex _root_.OAI.Complex Metric
open scoped unitInterval Topology ComplexConjugate
namespace StrictHotSpots.PlanarTopology

private lemma boundary_halfPlane {x b : ℂ} (hx : ‖x‖ ≤ 1) (hb : ‖b‖ = 1)
    (hne : x ≠ b) : 0 < ((x-b)*(-conj b)).re := by
  have hx' : normSq x ≤ 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg x]
  have hb' : normSq b = 1 := by rw [normSq_eq_norm_sq,hb]; norm_num
  have hd : 0 < normSq (x-b) := normSq_pos.mpr (sub_ne_zero.mpr hne)
  simp only [normSq_apply,sub_re,sub_im] at hx' hb' hd
  simp only [mul_re,sub_re,sub_im,neg_re,neg_im,conj_re,conj_im]
  nlinarith

private lemma log_difference {P : C(unitInterval,ℂ)} {b : ℂ}
    (hP : ∀ s, ‖P s‖ ≤ 1) (hb : ‖b‖ = 1) (hne : ∀ s, P s ≠ b)
    {l : C(unitInterval,ℂ)} (hl : ∀ s, exp (l s) = P s-b) :
    l 1-l 0 = log ((P 1-b)*(-conj b))-log ((P 0-b)*(-conj b)) := by
  let w : unitInterval → ℂ := fun s => (P s-b)*(-conj b)
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hwpos (s) : 0 < (w s).re := boundary_halfPlane (hP s) hb (hne s)
  have hws (s) : w s ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (hwpos s))
  have hwn (s) : w s ≠ 0 := fun h => by simpa [h] using hwpos s
  have hc : Continuous (fun s => log (w s)-log (w 0)+l 0) :=
    ((hw.clog hws).sub continuous_const).add continuous_const
  have he (s) : exp (log (w s)-log (w 0)+l 0) = exp (l s) := by
    rw [exp_add,exp_sub,exp_log (hwn s),exp_log (hwn 0),hl s,hl 0]
    dsimp [w]
    have hb0 : -conj b ≠ 0 := neg_ne_zero.mpr ((map_ne_zero (starRingEnd ℂ)).mpr (by intro h; simp [h] at hb))
    field_simp [sub_ne_zero.mpr (hne 0),neg_ne_zero.mp hb0]
  have eqfun : (fun s => log (w s)-log (w 0)+l 0) = l := by
    exact isCoveringMap_exp.eq_of_comp_eq hc l.continuous
      (funext fun s => Subtype.ext (he s)) 0 (by simp)
  have heq := congrFun eqfun 1
  dsimp [w] at heq
  linear_combination -heq

private lemma square_log {P N : C(unitInterval,ℂ)} (hne : ∀ s t, P s ≠ N t) :
    ∃ L : C(unitInterval × unitInterval,ℂ), ∀ s t, exp (L (s,t)) = P s-N t := by
  let : ContractibleSpace unitInterval := (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,by simp⟩
  let : LocallyPathConnectedSpace unitInterval := (convex_Icc (0:ℝ) 1).locallyPathConnectedSpace
  let f : C(unitInterval × unitInterval,{z : ℂ // z ≠ 0}) :=
    ⟨fun st => ⟨P st.1-N st.2,sub_ne_zero.mpr (hne st.1 st.2)⟩,
      ((P.continuous.comp continuous_fst).sub (N.continuous.comp continuous_snd)).subtype_mk _⟩
  obtain ⟨L,hL,-⟩ := isCoveringMap_exp.existsUnique_continuousMap_lifts f (0,0)
    (log (f (0,0))) (Subtype.ext (exp_log (f (0,0)).property))
  exact ⟨L,fun s t => congrArg Subtype.val (congrFun hL.2 (s,t))⟩



theorem disk_paths_cross {P N : C(unitInterval,ℂ)}
    (hP : ∀ s, ‖P s‖ ≤ 1) (hN : ∀ t, ‖N t‖ ≤ 1)
    (hP0 : P 0 = -1) (hP1 : P 1 = 1)
    (hN0 : ‖N 0‖ = 1) (hN1 : ‖N 1‖ = 1)
    (hup : 0 < (N 0).im) (hdn : (N 1).im < 0) :
    ∃ s t, P s = N t := by
  by_contra h
  push Not at h
  obtain ⟨L,hL⟩ := square_log h
  let D : unitInterval → ℂ := fun t => L (1,t)-L (0,t)
  have hD : Continuous D := by dsimp [D]; fun_prop
  have hed (t : unitInterval) (ht : ‖N t‖ = 1) :
      D t = log ((1-N t)*(-conj (N t)))-log ((-1-N t)*(-conj (N t))) := by
    have hh := log_difference hP ht (fun s => h s t)
      (l := ⟨fun s => L (s,t),by fun_prop⟩) (fun s => hL s t)
    simpa only [ContinuousMap.coe_mk,hP0,hP1] using hh
  have him1 (z : ℂ) : ((1-z)*(-conj z)).im = z.im := by
    simp only [mul_im,sub_re,sub_im,one_re,one_im,neg_re,neg_im,conj_re,conj_im]
    ring
  have him0 (z : ℂ) : ((-1-z)*(-conj z)).im = -z.im := by
    simp only [mul_im,sub_re,sub_im,one_re,one_im,neg_re,neg_im,conj_re,conj_im]
    ring
  have hp : 0 < (D 0).im := by
    rw [hed 0 hN0,sub_im,log_im,log_im]
    have ha := arg_nonneg_iff.mpr (by rw [him1]; exact hup.le)
    have hb := arg_neg_iff.mpr (by rw [him0]; exact neg_neg_of_pos hup)
    linarith
  have hn : (D 1).im < 0 := by
    rw [hed 1 hN1,sub_im,log_im,log_im]
    have ha := arg_neg_iff.mpr (by rw [him1]; exact hdn)
    have hb := arg_nonneg_iff.mpr (by rw [him0]; exact neg_nonneg.mpr hdn.le)
    linarith
  obtain ⟨t,ht⟩ := intermediate_value_univ (1 : unitInterval) 0 (continuous_im.comp hD)
    ⟨hn.le,hp.le⟩
  have he : (1-N t) = exp (D t) * (-1-N t) := by
    have hd : exp (D t) = (1-N t)/(-1-N t) := by
      dsimp only [D]
      rw [exp_sub,hL,hL,hP1,hP0]
    exact ((div_eq_iff (sub_ne_zero.mpr (hP0 ▸ h 0 t))).mp hd.symm)
  have hex : exp (D t) = (Real.exp (D t).re : ℂ) := by
    apply Complex.ext <;> simp [exp_re,exp_im,show (D t).im = 0 from ht]
  rw [hex] at he
  have hv : 0 < normSq (-1-N t) := normSq_pos.mpr (sub_ne_zero.mpr (hP0 ▸ h 0 t))
  have hx : normSq (N t) ≤ 1 := by
    rw [normSq_eq_norm_sq]
    nlinarith [hN t,norm_nonneg (N t)]
  have hpv := mul_pos (Real.exp_pos (D t).re) hv
  have hr := congrArg re (congrArg (fun z : ℂ => z*conj (-1-N t)) he)
  simp only [mul_re,mul_im,sub_re,sub_im,one_re,one_im,neg_re,neg_im,conj_re,conj_im,
    ofReal_re,ofReal_im,zero_mul,add_zero,sub_zero] at hr
  simp only [normSq_apply,sub_re,sub_im,one_re,one_im,neg_re,neg_im] at hx hpv
  nlinarith

private lemma arg_product_rightHalfPlane {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    arg (u*conj v) = arg u-arg v := by
  have h₁ := neg_pi_div_two_lt_arg_iff.mpr (Or.inl hu)
  have h₂ := arg_lt_pi_div_two_iff.mpr (Or.inl hu)
  have h₃ := neg_pi_div_two_lt_arg_iff.mpr (Or.inl hv)
  have h₄ := arg_lt_pi_div_two_iff.mpr (Or.inl hv)
  have hvπ : arg v ≠ Real.pi := by linarith [Real.pi_pos]
  have hc : arg (conj v) = -arg v := by rw [arg_conj,ite_eq_right hvπ]
  rw [arg_mul (by intro h; simp [h] at hu)
    (by intro h; have := congrArg re h; simp only [conj_re,zero_re] at this; linarith)
    (by rw [hc]; constructor <;> linarith),hc,sub_eq_add_neg]

private lemma log_difference_im {P : C(unitInterval,ℂ)} {b : ℂ}
    (hP : ∀ s, ‖P s‖ ≤ 1) (hb : ‖b‖ = 1) (hne : ∀ s, P s ≠ b)
    {l : C(unitInterval,ℂ)} (hl : ∀ s, exp (l s) = P s-b) :
    (l 1-l 0).im = arg ((P 1-b)*conj (P 0-b)) := by
  rw [log_difference hP hb hne hl,sub_im,log_im,log_im,
    ← arg_product_rightHalfPlane (boundary_halfPlane (hP 1) hb (hne 1))
      (boundary_halfPlane (hP 0) hb (hne 0))]
  congr 1
  have hbc : (-conj b)*conj (-conj b) = 1 := by
    rw [mul_conj,normSq_eq_norm_sq,norm_neg,norm_conj,hb]
    norm_num
  rw [map_mul]
  calc
    (P 1-b)*(-conj b)*(conj (P 0-b)*conj (-conj b)) =
        ((P 1-b)*conj (P 0-b))*((-conj b)*conj (-conj b)) := by ring
    _ = _ := by rw [hbc,mul_one]

private lemma no_positive_chord_ratio {a c z : ℂ} {k : ℝ}
    (ha : ‖a‖ = 1) (hc : ‖c‖ = 1) (hz : ‖z‖ ≤ 1) (hac : a ≠ c) (haz : a ≠ z)
    (hk : 0 < k) (he : c-z = (k : ℂ)*(a-z)) : False := by
  have hna : normSq a = 1 := by rw [normSq_eq_norm_sq,ha]; norm_num
  have hnc : normSq c = 1 := by rw [normSq_eq_norm_sq,hc]; norm_num
  have hnz : normSq z ≤ 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have hnaz : 0 < normSq (a-z) := normSq_pos.mpr (sub_ne_zero.mpr haz)
  have hce : c = z+(k : ℂ)*(a-z) := by linear_combination he
  have hid : normSq c-normSq a =
      (k-1)*(normSq a-normSq z+k*normSq (a-z)) := by
    rw [hce]
    simp only [normSq_apply,add_re,add_im,mul_re,mul_im,sub_re,sub_im,ofReal_re,ofReal_im]
    ring
  rw [hna,hnc,sub_self] at hid
  have hp : 0 < 1-normSq z+k*normSq (a-z) :=
    add_pos_of_nonneg_of_pos (sub_nonneg.mpr hnz) (mul_pos hk hnaz)
  have he1 : k = 1 := by
    have hh := (mul_eq_zero.mp hid.symm).resolve_right hp.ne'
    linarith
  rw [he1,ofReal_one,one_mul] at he
  exact hac (sub_left_injective he).symm




theorem disk_paths_cross_chord {P N : C(unitInterval,ℂ)}
    (hP : ∀ s, ‖P s‖ ≤ 1) (hN : ∀ t, ‖N t‖ ≤ 1)
    (hP0 : ‖P 0‖ = 1) (hP1 : ‖P 1‖ = 1) (hneP : P 0 ≠ P 1)
    (hN0 : ‖N 0‖ = 1) (hN1 : ‖N 1‖ = 1)
    (hup : 0 < ((P 1-N 0)*conj (P 0-N 0)).im)
    (hdn : ((P 1-N 1)*conj (P 0-N 1)).im < 0) :
    ∃ s t, P s = N t := by
  by_contra h
  push Not at h
  obtain ⟨L,hL⟩ := square_log h
  let D : unitInterval → ℂ := fun t => L (1,t)-L (0,t)
  have hD : Continuous D := by dsimp [D]; fun_prop
  have hed (t : unitInterval) (ht : ‖N t‖ = 1) :
      (D t).im = arg ((P 1-N t)*conj (P 0-N t)) :=
    log_difference_im hP ht (fun s => h s t)
      (l := ⟨fun s => L (s,t),by fun_prop⟩) (fun s => hL s t)
  have hp : 0 < (D 0).im := by
    rw [hed 0 hN0]
    have hge := arg_nonneg_iff.mpr hup.le
    have hn : arg ((P 1-N 0)*conj (P 0-N 0)) ≠ 0 := by
      intro ht
      exact hup.ne' (arg_eq_zero_iff.mp ht).2
    exact hge.lt_of_ne' hn
  have hn : (D 1).im < 0 := by rw [hed 1 hN1]; exact arg_neg_iff.mpr hdn
  obtain ⟨t,ht⟩ := intermediate_value_univ (1 : unitInterval) 0 (continuous_im.comp hD) ⟨hn.le,hp.le⟩
  have he : (P 1-N t) = exp (D t)*(P 0-N t) := by
    have hd : exp (D t) = (P 1-N t)/(P 0-N t) := by dsimp only [D]; rw [exp_sub,hL,hL]
    exact (div_eq_iff (sub_ne_zero.mpr (h 0 t))).mp hd.symm
  have hex : exp (D t) = (Real.exp (D t).re : ℂ) := by
    apply Complex.ext <;> simp [exp_re,exp_im,show (D t).im = 0 from ht]
  rw [hex] at he
  exact no_positive_chord_ratio hP0 hP1 (hN t) hneP (h 0 t) (Real.exp_pos _) he

end StrictHotSpots.PlanarTopology
end PlanarCrossingLayer

section DiskSignTopologyLayer

open Set Filter Metric _root_.Complex _root_.OAI.Complex
open scoped unitInterval Topology ComplexConjugate
namespace StrictHotSpots.PlanarTopology

private lemma disk_positive_open {u : ℂ → ℝ}
    (hu : ContinuousOn u (closedBall 0 1)) : IsOpen (ball (0 : ℂ) 1 ∩ {z | 0 < u z}) := by
  exact (hu.mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball isOpen_Ioi



lemma join_positive_interior {u : ℂ → ℝ}
    (hu : ContinuousOn u (closedBall 0 1)) {a : ℂ}
    (ha : a ∈ closedBall (0 : ℂ) 1) (hua : 0 < u a) :
    ∃ a' ∈ ball (0 : ℂ) 1 ∩ {z | 0 < u z},
      JoinedIn (closedBall (0 : ℂ) 1 ∩ {z | 0 < u z}) a a' := by
  obtain ⟨ε,hε,hεu⟩ := (Metric.continuousWithinAt_iff.mp (hu a ha)) (u a) hua
  have hpos : closedBall (0 : ℂ) 1 ∩ ball a ε ⊆ {z | 0 < u z} := by
    intro z hz
    have hd := hεu hz.1 hz.2
    rw [Real.dist_eq] at hd
    have := (abs_lt.mp hd).1
    change 0 < u z
    linarith
  have hacl : a ∈ closure (ball (0 : ℂ) 1) := by rwa [closure_ball (0 : ℂ) one_ne_zero]
  obtain ⟨a',ha',hda'⟩ := Metric.mem_closure_iff.mp hacl ε hε
  have hsa : a ∈ closedBall (0 : ℂ) 1 ∩ ball a ε := ⟨ha,mem_ball_self hε⟩
  have hsa' : a' ∈ closedBall (0 : ℂ) 1 ∩ ball a ε :=
    ⟨ball_subset_closedBall ha',by simpa only [mem_ball,dist_comm] using hda'⟩
  refine ⟨a',⟨ha',hpos hsa'⟩,?_⟩
  exact (((convex_closedBall (0 : ℂ) 1).inter (convex_ball a ε)).isPathConnected
    ⟨a,hsa⟩ |>.joinedIn a hsa a' hsa').mono (fun z hz => ⟨hz.1,hpos hz⟩)

lemma join_positive_closedDisk {u : ℂ → ℝ}
    (hu : ContinuousOn u (closedBall 0 1))
    (hc : IsConnected (ball (0 : ℂ) 1 ∩ {z | 0 < u z}))
    {a c : ℂ} (ha : a ∈ closedBall (0 : ℂ) 1) (hc' : c ∈ closedBall (0 : ℂ) 1)
    (hua : 0 < u a) (huc : 0 < u c) :
    JoinedIn (closedBall (0 : ℂ) 1 ∩ {z | 0 < u z}) a c := by
  obtain ⟨a',ha',hja⟩ := join_positive_interior hu ha hua
  obtain ⟨c',hc'',hjc⟩ := join_positive_interior hu hc' huc
  have hpath := (disk_positive_open hu).isConnected_iff_isPathConnected.mp hc
  have hj := (hpath.joinedIn a' ha' c' hc'').mono
    (show ball (0 : ℂ) 1 ∩ {z | 0 < u z} ⊆ closedBall (0 : ℂ) 1 ∩ {z | 0 < u z} from
      fun z hz => ⟨ball_subset_closedBall hz.1,hz.2⟩)
  exact (hja.trans hj).trans hjc.symm



theorem no_alternating_boundary_signs {u : ℂ → ℝ}
    (hu : ContinuousOn u (closedBall 0 1))
    (hp : IsConnected (ball (0 : ℂ) 1 ∩ {z | 0 < u z}))
    (hn : IsConnected (ball (0 : ℂ) 1 ∩ {z | u z < 0}))
    {a b c d : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)
    (hac : a ≠ c) (hup : 0 < ((c-b)*conj (a-b)).im)
    (hdn : ((c-d)*conj (a-d)).im < 0)
    (hua : 0 < u a) (hub : u b < 0) (huc : 0 < u c) (hud : u d < 0) : False := by
  have hacl : a ∈ closedBall (0 : ℂ) 1 := by simp only [mem_closedBall,dist_zero_right,ha,le_refl]
  have hccl : c ∈ closedBall (0 : ℂ) 1 := by simp only [mem_closedBall,dist_zero_right,hc,le_refl]
  have hbcl : b ∈ closedBall (0 : ℂ) 1 := by simp only [mem_closedBall,dist_zero_right,hb,le_refl]
  have hdcl : d ∈ closedBall (0 : ℂ) 1 := by simp only [mem_closedBall,dist_zero_right,hd,le_refl]
  have hP := join_positive_closedDisk hu hp hacl hccl hua huc
  have hneg : IsConnected (ball (0 : ℂ) 1 ∩ {z | 0 < -u z}) := by
    simpa only [neg_pos] using hn
  have hN := join_positive_closedDisk hu.neg hneg hbcl hdcl (neg_pos.mpr hub) (neg_pos.mpr hud)
  let P : C(unitInterval,ℂ) := hP.somePath.toContinuousMap
  let N : C(unitInterval,ℂ) := hN.somePath.toContinuousMap
  have hPs (s) : ‖P s‖ ≤ 1 := by
    have hh := (hP.somePath_mem s).1
    simpa only [P,N,Path.coe_toContinuousMap,mem_closedBall,dist_zero_right] using hh
  have hNs (s) : ‖N s‖ ≤ 1 := by
    have hh := (hN.somePath_mem s).1
    simpa only [P,N,Path.coe_toContinuousMap,mem_closedBall,dist_zero_right] using hh
  have hP0 : P 0 = a := hP.somePath.source
  have hP1 : P 1 = c := hP.somePath.target
  have hN0 : N 0 = b := hN.somePath.source
  have hN1 : N 1 = d := hN.somePath.target
  obtain ⟨s,t,hst⟩ := disk_paths_cross_chord hPs hNs (hP0.symm ▸ ha) (hP1.symm ▸ hc)
    (by simpa only [hP0,hP1] using hac) (hN0.symm ▸ hb) (hN1.symm ▸ hd)
    (by simpa only [hP0,hP1,hN0] using hup) (by simpa only [hP0,hP1,hN1] using hdn)
  have hpos : 0 < u (P s) := (hP.somePath_mem s).2
  have hneg : 0 < -u (N t) := (hN.somePath_mem t).2
  rw [hst] at hpos
  linarith

end StrictHotSpots.PlanarTopology
end DiskSignTopologyLayer

section CircleSignMomentsLayer



open Set MeasureTheory
namespace StrictHotSpots.CircleSigns

lemma separating_cosine (a b x : ℝ) :
    Real.cos (x-(a+b)/2)-Real.cos ((b-a)/2) =
      2*Real.sin ((x-a)/2)*Real.sin ((b-x)/2) := by
  rw [Real.cos_sub_cos]
  have h₁ : ((x-(a+b)/2)+(b-a)/2)/2 = (x-a)/2 := by ring
  have h₂ : ((x-(a+b)/2)-(b-a)/2)/2 = -((b-x)/2) := by ring
  rw [h₁,h₂,Real.sin_neg]
  ring

lemma separating_cosine_pos {α a b x : ℝ} (ha : α < a) (hb : b < α+2*Real.pi)
    (hx : x ∈ Ioo a b) :
    0 < Real.cos (x-(a+b)/2)-Real.cos ((b-a)/2) := by
  rw [separating_cosine]
  have h₁ : 0 < Real.sin ((x-a)/2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])
  have h₂ : 0 < Real.sin ((b-x)/2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.2]) (by linarith [hx.1])
  positivity

lemma separating_cosine_nonpos {α a b x : ℝ} (ha : α < a) (hab : a < b)
    (hb : b < α+2*Real.pi) (hx : x ∈ Icc α (α+2*Real.pi))
    (hout : x ≤ a ∨ b ≤ x) :
    Real.cos (x-(a+b)/2)-Real.cos ((b-a)/2) ≤ 0 := by
  rw [separating_cosine]
  rcases hout with h | h
  · have h₁ : Real.sin ((x-a)/2) ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith [hx.1])
    have h₂ : 0 ≤ Real.sin ((b-x)/2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hx.1])
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num) h₁) h₂
  · have h₁ : 0 ≤ Real.sin ((x-a)/2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hx.2])
    have h₂ : Real.sin ((b-x)/2) ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith [hx.2])
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) h₁) h₂

lemma positive_points_sandwich {h : ℝ → ℝ} (hc : Continuous h) {α x : ℝ}
    (hα : h α < 0) (hβ : h (α+2*Real.pi) < 0)
    (hx : x ∈ Icc α (α+2*Real.pi)) (hh : 0 < h x) :
    ∃ y z, y ∈ Icc α (α+2*Real.pi) ∧ z ∈ Icc α (α+2*Real.pi) ∧
      0 < h y ∧ 0 < h z ∧ y < x ∧ x < z := by
  have hαx : α < x := lt_of_le_of_ne hx.1 (by rintro rfl; linarith)
  have hxβ : x < α+2*Real.pi := lt_of_le_of_ne hx.2 (by intro he; rw [he] at hh; linarith)
  have ho : IsOpen (Ioo α (α+2*Real.pi) ∩ h ⁻¹' Ioi 0) :=
    isOpen_Ioo.inter (isOpen_Ioi.preimage hc)
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp ho x ⟨⟨hαx,hxβ⟩,hh⟩
  have hy : x-ε/2 ∈ Ioo α (α+2*Real.pi) ∩ h ⁻¹' Ioi 0 := by
    apply hball
    rw [Metric.mem_ball,Real.dist_eq]
    have : x-ε/2-x = -(ε/2) := by ring
    rw [this,abs_neg,abs_of_pos (by positivity)]
    linarith
  have hz : x+ε/2 ∈ Ioo α (α+2*Real.pi) ∩ h ⁻¹' Ioi 0 := by
    apply hball
    rw [Metric.mem_ball,Real.dist_eq]
    have : x+ε/2-x = ε/2 := by ring
    rw [this,abs_of_pos (by positivity)]
    linarith
  exact ⟨_,_,⟨hy.1.1.le,hy.1.2.le⟩,⟨hz.1.1.le,hz.1.2.le⟩,hy.2,hz.2,by linarith,by linarith⟩



theorem moment_sign_changes {h w : ℝ → ℝ} (hc : Continuous h) (wc : Continuous w) (α : ℝ)
    (wp : ∀ x ∈ Icc α (α+2*Real.pi), 0 < w x)
    (hα : h α < 0) (hβ : h (α+2*Real.pi) < 0)
    (hp : ∃ x ∈ Icc α (α+2*Real.pi), 0 < h x)
    (h0 : (∫ x in α..α+2*Real.pi, w x*h x) = 0)
    (hcos : (∫ x in α..α+2*Real.pi, w x*h x*Real.cos x) = 0)
    (hsin : (∫ x in α..α+2*Real.pi, w x*h x*Real.sin x) = 0) :
    ∃ x y z, x ∈ Ioo α (α+2*Real.pi) ∧ z ∈ Ioo α (α+2*Real.pi) ∧
      x < y ∧ y < z ∧ 0 < h x ∧ h y < 0 ∧ 0 < h z := by
  by_contra! hn
  let P : Set ℝ := Icc α (α+2*Real.pi) ∩ h ⁻¹' Ioi 0
  have hP : P.Nonempty := hp
  have hb : BddBelow P := ⟨α,fun x hx => hx.1.1⟩
  have ht : BddAbove P := ⟨α+2*Real.pi,fun x hx => hx.1.2⟩
  let a := sInf P
  let b := sSup P
  have hcl : closure P ⊆ Icc α (α+2*Real.pi) ∩ h ⁻¹' Ici 0 := by
    apply closure_minimal
    · intro x hx
      refine ⟨hx.1,?_⟩
      change 0 ≤ h x
      exact le_of_lt hx.2
    · exact isClosed_Icc.inter (isClosed_Ici.preimage hc)
  have ham : a ∈ Icc α (α+2*Real.pi) ∩ h ⁻¹' Ici 0 := hcl (csInf_mem_closure hP hb)
  have hbm : b ∈ Icc α (α+2*Real.pi) ∩ h ⁻¹' Ici 0 := hcl (csSup_mem_closure hP ht)
  have ha : α < a := lt_of_le_of_ne ham.1.1 (by intro he; rw [← he] at ham; exact (not_lt_of_ge ham.2) hα)
  have hβb : b < α+2*Real.pi := lt_of_le_of_ne hbm.1.2 (by intro he; rw [he] at hbm; exact (not_lt_of_ge hbm.2) hβ)
  have hstrict (x : ℝ) (hx : x ∈ P) : a < x ∧ x < b := by
    obtain ⟨y,z,hy,hz,hpy,hpz,hyx,hxz⟩ := positive_points_sandwich hc hα hβ hx.1 hx.2
    exact ⟨lt_of_le_of_lt (csInf_le hb ⟨hy,hpy⟩) hyx,
      lt_of_lt_of_le hxz (le_csSup ht ⟨hz,hpz⟩)⟩
  let p := hP.some
  have hp : p ∈ P := hP.some_mem
  have hsp := hstrict p hp
  have hab : a < b := hsp.1.trans hsp.2
  have hmid (x : ℝ) (hx : x ∈ Ioo a b) : 0 ≤ h x := by
    by_contra! hh
    obtain ⟨y,hy,hyx⟩ := exists_lt_of_csInf_lt hP hx.1
    obtain ⟨z,hz,hxz⟩ := exists_lt_of_lt_csSup hP hx.2
    have hsy := hstrict y hy
    have hsz := hstrict z hz
    exact (not_lt_of_ge (hn y x z ⟨ha.trans hsy.1,hsy.2.trans hβb⟩
      ⟨ha.trans hsz.1,hsz.2.trans hβb⟩ hyx hxz hy.2 hh)) hz.2
  have hout (x : ℝ) (hx : x ∈ Icc α (α+2*Real.pi)) (hh : x ≤ a ∨ b ≤ x) : h x ≤ 0 := by
    by_contra! hp
    have hs := hstrict x ⟨hx,hp⟩
    rcases hh with h | h <;> linarith [hs.1,hs.2]
  let F : ℝ → ℝ := fun x => Real.cos (x-(a+b)/2)-Real.cos ((b-a)/2)
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hnon (x : ℝ) (hx : x ∈ Icc α (α+2*Real.pi)) : 0 ≤ w x*h x*F x := by
    by_cases hi : x ∈ Ioo a b
    · exact mul_nonneg (mul_nonneg (wp x hx).le (hmid x hi)) (separating_cosine_pos ha hβb hi).le
    · have he : x ≤ a ∨ b ≤ x := by simpa only [mem_Ioo,not_and_or,not_lt] using hi
      exact mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (wp x hx).le (hout x hx he))
        (separating_cosine_nonpos ha hab hβb hx he)
  have hpos : 0 < ∫ x in α..α+2*Real.pi, w x*h x*F x := by
    apply intervalIntegral.integral_pos (by linarith [Real.pi_pos]) ((wc.mul hc).mul hF).continuousOn
    · intro x hx
      exact hnon x ⟨hx.1.le,hx.2⟩
    · exact ⟨p,hp.1,mul_pos (mul_pos (wp p hp.1) hp.2) (separating_cosine_pos ha hβb hsp)⟩
  have heq (x : ℝ) : w x*h x*F x =
      Real.cos ((a+b)/2)*(w x*h x*Real.cos x) +
      Real.sin ((a+b)/2)*(w x*h x*Real.sin x) - Real.cos ((b-a)/2)*(w x*h x) := by
    dsimp [F]
    rw [Real.cos_sub]
    ring
  have he : (∫ x in α..α+2*Real.pi, w x*h x*F x) = 0 := by
    simp_rw [heq]
    rw [intervalIntegral.integral_sub,intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,hcos,hsin,h0]
    · ring
    all_goals apply Continuous.intervalIntegrable; fun_prop
  linarith

end StrictHotSpots.CircleSigns
end CircleSignMomentsLayer

section ChordAnglesLayer
open _root_.Complex _root_.OAI.Complex Set Metric
open scoped ComplexConjugate
namespace StrictHotSpots.PlanarTopology

lemma sine_triple_identity (a b c : ℝ) :
    Real.sin (c-a) - Real.sin (c-b) + Real.sin (a-b) =
      4*Real.sin ((c-b)/2)*Real.sin ((a-b)/2)*Real.sin ((c-a)/2) := by
  have h₂ : Real.sin (c-a) = 2*Real.sin ((c-a)/2)*Real.cos ((c-a)/2) := by
    simpa only [show 2*((c-a)/2) = c-a by ring] using Real.sin_two_mul ((c-a)/2)
  have h₃ := Real.sin_sub_sin (c-b) (a-b)
  have he : ((c-b)-(a-b))/2 = (c-a)/2 := by ring
  rw [he] at h₃
  have h₄ := Real.cos_sub_cos ((c-a)/2) (((c-b)+(a-b))/2)
  have he₁ : ((c-a)/2 + ((c-b)+(a-b))/2)/2 = (c-b)/2 := by ring
  have he₂ : ((c-a)/2 - ((c-b)+(a-b))/2)/2 = -((a-b)/2) := by ring
  rw [he₁,he₂,Real.sin_neg] at h₄
  calc
    _ = 2*Real.sin ((c-a)/2)*(Real.cos ((c-a)/2)-Real.cos (((c-b)+(a-b))/2)) := by
      linarith [h₃]
    _ = _ := by rw [h₄]; ring

lemma chord_exp_det (a b c : ℝ) :
    (((Circle.exp c : ℂ)-(Circle.exp b : ℂ))*
      conj ((Circle.exp a : ℂ)-(Circle.exp b : ℂ))).im =
      4*Real.sin ((c-b)/2)*Real.sin ((a-b)/2)*Real.sin ((c-a)/2) := by
  rw [← sine_triple_identity]
  simp only [Circle.coe_exp,exp_ofReal_mul_I_re,exp_ofReal_mul_I_im,
    mul_im,sub_re,sub_im,conj_re,conj_im,Real.sin_sub]
  ring

lemma angles_no_alternation {u : ℂ → ℝ}
    (hu : ContinuousOn u (closedBall 0 1))
    (hp : IsConnected (ball (0 : ℂ) 1 ∩ {z | 0 < u z}))
    (hn : IsConnected (ball (0 : ℂ) 1 ∩ {z | u z < 0}))
    {α x y z : ℝ} (hαx : α < x) (hxy : x < y) (hyz : y < z) (hzβ : z < α+2*Real.pi)
    (hα : u (Circle.exp α) < 0) (hx : 0 < u (Circle.exp x))
    (hy : u (Circle.exp y) < 0) (hz : 0 < u (Circle.exp z)) : False := by
  have hzx : (Circle.exp z : ℂ) ≠ (Circle.exp x : ℂ) := by
    intro he
    have hc : Circle.exp z = Circle.exp x := Subtype.ext he
    have := Circle.exp_injOn_Ico (a := α) (b := α+2*Real.pi) (by linarith)
      ⟨by linarith,hzβ⟩ ⟨hαx.le,by linarith⟩ hc
    linarith
  have hup : 0 < (((Circle.exp x : ℂ)-(Circle.exp y : ℂ))*
      conj ((Circle.exp z : ℂ)-(Circle.exp y : ℂ))).im := by
    rw [chord_exp_det]
    have hs₁ : Real.sin ((x-y)/2) < 0 := Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
    have hs₂ : 0 < Real.sin ((z-y)/2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hs₃ : Real.sin ((x-z)/2) < 0 := Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
    exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hs₁) hs₂) hs₃
  have hdn : (((Circle.exp x : ℂ)-(Circle.exp α : ℂ))*
      conj ((Circle.exp z : ℂ)-(Circle.exp α : ℂ))).im < 0 := by
    rw [chord_exp_det]
    have hs₁ : 0 < Real.sin ((x-α)/2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hs₂ : 0 < Real.sin ((z-α)/2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hs₃ : Real.sin ((x-z)/2) < 0 := Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
    exact mul_neg_of_pos_of_neg (mul_pos (mul_pos (by norm_num) hs₁) hs₂) hs₃
  exact no_alternating_boundary_signs hu hp hn (Circle.exp z).norm_coe (Circle.exp y).norm_coe
    (Circle.exp x).norm_coe (Circle.exp α).norm_coe hzx hup hdn hz hy hx hα

end StrictHotSpots.PlanarTopology
end ChordAnglesLayer

section DiskBoundaryMomentsLayer
open Set MeasureTheory Metric
namespace StrictHotSpots.CircleSigns

lemma periodic_weighted_signs {h w : ℝ → ℝ} (hc : Continuous h) (wc : Continuous w)
    (hp : Function.Periodic h (2*Real.pi)) (wp : Function.Periodic w (2*Real.pi))
    (hw : ∀ x, 0 < w x) (hne : ∃ x, h x ≠ 0)
    (hi : (∫ x in (0:ℝ)..2*Real.pi, w x*h x) = 0) :
    (∃ x, h x < 0) ∧ (∃ x, 0 < h x) := by
  have hneg {f : ℝ → ℝ} (fc : Continuous f) (fp : Function.Periodic f (2*Real.pi))
      (fn : ∃ x, f x ≠ 0) (fi : (∫ x in (0:ℝ)..2*Real.pi, w x*f x) = 0) : ∃ x, f x < 0 := by
    by_contra! hh
    obtain ⟨x,hx⟩ := fn
    have hxx : 0 < f x := lt_of_le_of_ne (hh x) hx.symm
    have hi' : 0 < ∫ y in x..x+2*Real.pi, w y*f y := by
      apply intervalIntegral.integral_pos (by linarith [Real.pi_pos]) (wc.mul fc).continuousOn
      · intro y _
        exact mul_nonneg (hw y).le (hh y)
      · exact ⟨x,⟨le_rfl,by linarith [Real.pi_pos]⟩,mul_pos (hw x) hxx⟩
    have he := (wp.mul fp).intervalIntegral_add_eq x 0
    simp only [zero_add,Pi.mul_apply] at he
    rw [fi] at he
    linarith
  constructor
  · exact hneg hc hp hne hi
  · obtain ⟨x,hx⟩ := hneg hc.neg (fun x => by simp only [Pi.neg_apply,hp x]) (by simpa using hne) (by
      simpa only [Pi.neg_apply,mul_neg,intervalIntegral.integral_neg,neg_zero] using congrArg Neg.neg hi)
    exact ⟨x,neg_lt_zero.mp hx⟩

lemma circle_trace_continuous {u : ℂ → ℝ} (hu : ContinuousOn u (closedBall 0 1)) :
    Continuous (fun θ : ℝ => u (Circle.exp θ : ℂ)) := by
  apply hu.comp_continuous
  · fun_prop
  · intro θ
    simp only [mem_closedBall,dist_zero_right,(Circle.exp θ).norm_coe,le_refl]



theorem disk_moments_nonzero {u : ℂ → ℝ} (hu : ContinuousOn u (closedBall 0 1))
    (hpos : IsConnected (ball (0 : ℂ) 1 ∩ {z | 0 < u z}))
    (hneg : IsConnected (ball (0 : ℂ) 1 ∩ {z | u z < 0}))
    {w : ℝ → ℝ} (wc : Continuous w) (wp : Function.Periodic w (2*Real.pi))
    (hw : ∀ θ, 0 < w θ) (hne : ∃ θ, u (Circle.exp θ : ℂ) ≠ 0)
    (hi : (∫ θ in (0:ℝ)..2*Real.pi, w θ*u (Circle.exp θ : ℂ)) = 0) :
    (∫ θ in (0:ℝ)..2*Real.pi, w θ*u (Circle.exp θ : ℂ)*Real.cos θ) ≠ 0 ∨
      (∫ θ in (0:ℝ)..2*Real.pi, w θ*u (Circle.exp θ : ℂ)*Real.sin θ) ≠ 0 := by
  by_contra! hm
  let h : ℝ → ℝ := fun θ => u (Circle.exp θ : ℂ)
  have hc : Continuous h := circle_trace_continuous hu
  have hp : Function.Periodic h (2*Real.pi) := by
    intro θ
    exact congrArg (fun z : Circle => u (z : ℂ)) (Circle.exp_add_two_pi θ)
  obtain ⟨⟨α,hα⟩,⟨p,hp'⟩⟩ := periodic_weighted_signs hc wc hp wp hw hne hi
  have hα' : h (α+2*Real.pi) < 0 := by rw [hp]; exact hα
  have hposI : ∃ x ∈ Icc α (α+2*Real.pi), 0 < h x := by
    have hr := hp.image_Icc Real.two_pi_pos α
    have hx : h p ∈ Set.range h := ⟨p,rfl⟩
    rw [← hr] at hx
    obtain ⟨x,hx,hex⟩ := hx
    exact ⟨x,hx,hex ▸ hp'⟩
  have hi' : (∫ x in α..α+2*Real.pi, w x*h x) = 0 := by
    have he := (wp.mul hp).intervalIntegral_add_eq α 0
    simp only [zero_add,Pi.mul_apply] at he
    exact he.trans hi
  have hcos : (∫ x in α..α+2*Real.pi, w x*h x*Real.cos x) = 0 := by
    have he := ((wp.mul hp).mul Real.cos_periodic).intervalIntegral_add_eq α 0
    simp only [zero_add,Pi.mul_apply] at he
    exact he.trans hm.1
  have hsin : (∫ x in α..α+2*Real.pi, w x*h x*Real.sin x) = 0 := by
    have he := ((wp.mul hp).mul Real.sin_periodic).intervalIntegral_add_eq α 0
    simp only [zero_add,Pi.mul_apply] at he
    exact he.trans hm.2
  obtain ⟨x,y,z,hx,hz,hxy,hyz,hpx,hny,hpz⟩ :=
    moment_sign_changes hc wc α (fun x _ => hw x) hα hα' hposI hi' hcos hsin
  exact PlanarTopology.angles_no_alternation hu hpos hneg hx.1 hxy hyz hz.2 hα hpx hny hpz

end StrictHotSpots.CircleSigns
end DiskBoundaryMomentsLayer

section DiskMultiplicityLayer
open Set MeasureTheory Metric Function Module
open scoped Topology InnerProductSpace
namespace StrictHotSpots.CircleSigns
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def weightedMoment (F : ℂ → E) (w q : ℝ → ℝ)
    (hc : Continuous (fun θ => w θ*q θ))
    (hF : ContinuousOn F (closedBall 0 1)) : E →ₗ[ℝ] ℝ where
  toFun a := ∫ θ in (0:ℝ)..2*Real.pi, w θ*q θ*inner ℝ a (F (Circle.exp θ : ℂ))
  map_add' a b := by
    simp only [inner_add_left,mul_add]
    have hcont : Continuous (fun θ : ℝ => F (Circle.exp θ : ℂ)) :=
      hF.comp_continuous (by fun_prop) (fun θ => by simp [mem_closedBall,dist_zero_right])
    exact intervalIntegral.integral_add
      ((hc.mul (continuous_const.inner hcont)).intervalIntegrable _ _)
      ((hc.mul (continuous_const.inner hcont)).intervalIntegrable _ _)
  map_smul' c a := by
    simp only [inner_smul_left,conj_trivial,RingHom.id_apply,smul_eq_mul]
    simp_rw [show ∀ θ, w θ * q θ * (c * inner ℝ a (F (Circle.exp θ : ℂ))) =
      c * (w θ*q θ*inner ℝ a (F (Circle.exp θ : ℂ))) from fun _ => by ring]
    exact intervalIntegral.integral_const_mul _ _




theorem disk_family_finrank_le_two (F : ℂ → E)
    (hc : ContinuousOn F (closedBall 0 1))
    (hb : ∀ a : E, a ≠ 0 → ∃ s : Circle, 0 < inner ℝ a (F s))
    (hp : ∀ a : E, a ≠ 0 → IsConnected
      (ball (0:ℂ) 1 ∩ {z | 0 < inner ℝ a (F z)}))
    (hn : ∀ a : E, a ≠ 0 → IsConnected
      (ball (0:ℂ) 1 ∩ {z | inner ℝ a (F z) < 0})) : finrank ℝ E ≤ 2 := by
  let G : C(Circle,E) := ⟨fun s => F s,
    hc.comp_continuous (by fun_prop) (fun s => by simpa only [mem_closedBall,dist_zero_right,Circle.norm_coe] using (le_refl (1:ℝ)))⟩
  obtain ⟨w,wc,wp,hw,hzero⟩ := PositiveWeight.exists_circle_weight G hb
  let T : E →ₗ[ℝ] ℝ×ℝ := (weightedMoment F w Real.cos (wc.mul Real.continuous_cos) hc).prod
    (weightedMoment F w Real.sin (wc.mul Real.continuous_sin) hc)
  have hker (a : E) (ha : T a = 0) : a = 0 := by
    by_contra haz
    obtain ⟨s,hs⟩ := hb a haz
    have hne : ∃ θ, inner ℝ a (F (Circle.exp θ : ℂ)) ≠ 0 := by
      exact ⟨(s:ℂ).arg,by simpa only [Circle.exp_arg] using ne_of_gt hs⟩
    have hcont : ContinuousOn (fun z => inner ℝ a (F z)) (closedBall 0 1) :=
      continuousOn_const.inner hc
    have hh := disk_moments_nonzero hcont (hp a haz) (hn a haz) wc wp hw hne (hzero a)
    have hreal := congrArg Prod.fst ha
    have himag := congrArg Prod.snd ha
    change (∫ θ in (0:ℝ)..2*Real.pi, w θ*Real.cos θ*inner ℝ a (F (Circle.exp θ : ℂ))) = 0 at hreal
    change (∫ θ in (0:ℝ)..2*Real.pi, w θ*Real.sin θ*inner ℝ a (F (Circle.exp θ : ℂ))) = 0 at himag
    have hre : (∫ θ in (0:ℝ)..2*Real.pi, w θ*inner ℝ a (F (Circle.exp θ : ℂ))*Real.cos θ) = 0 := by
      simpa only [mul_right_comm (w _) (Real.cos _) _] using hreal
    have him : (∫ θ in (0:ℝ)..2*Real.pi, w θ*inner ℝ a (F (Circle.exp θ : ℂ))*Real.sin θ) = 0 := by
      simpa only [mul_right_comm (w _) (Real.sin _) _] using himag
    exact hh.elim (fun h => h hre) (fun h => h him)
  have hi : Injective T := by
    intro a b he
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub,he,sub_self]
  simpa only [finrank_prod,finrank_self] using T.finrank_le_finrank_of_injective hi
end StrictHotSpots.CircleSigns
end DiskMultiplicityLayer
end
end MultiplicityComplete

section ClosedEigenMultiplicity

noncomputable section
open Set Metric Function Module
open scoped Topology InnerProductSpace
namespace StrictHotSpots
open PlaneGreen DiskH10


def closedScalarEval {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (x : closure Ω) : closedEigenSpace Ω ho hb →ₗ[ℝ] ℝ where
  toFun J := J.val.1 x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl




theorem closedEigenSpace_family_card {Ω : Set Plane} (c : Conformal.ClosedDiskChart Ω)
    (hΩ : AdmissibleDomain Ω) {n : ℕ}
    (f : Fin n → closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1) (hf : LinearIndependent ℝ f) : n ≤ 2 := by
  classical
  choose u Y hu huc hY he hjet using fun i => (f i).property
  let J (a : EuclideanSpace ℝ (Fin n)) : closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1 := ∑ i, a i • f i
  have hjnz (a : EuclideanSpace ℝ (Fin n)) (ha : a ≠ 0) : J a ≠ 0 := by
    intro hz
    have hh := Fintype.linearIndependent_iff.mp hf (fun i => a i) hz
    exact ha (by ext i; exact hh i)
  have hcombo (a : EuclideanSpace ℝ (Fin n)) (x : closure Ω) :
      (J a).val.1 x = ∑ i, a i * u i x := by
    change closedScalarEval hΩ.2.1 hΩ.2.2.1 x (∑ i, a i • f i) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    change a i * (f i).val.1 x = a i * u i x
    rw [← hjet i]
    rfl
  let F (z : ℂ) : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => u i (c.F (complexIso z)))
  have hc : ContinuousOn F (closedBall 0 1) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    exact (huc i).comp (c.lipschitz.continuous.comp complexIso.continuous).continuousOn (fun _ hz => c.complex_maps_closed hz)
  have hval (a : EuclideanSpace ℝ (Fin n)) {v : Plane → ℝ} {Z : Plane → Plane}
      (hv : closedEigenJet Ω v Z = (J a).val) (z : ℂ) (hz : z ∈ closedBall 0 1) :
      inner ℝ a (F z) = v (c.F (complexIso z)) := by
    let x : closure Ω := ⟨c.F (complexIso z),c.complex_maps_closed hz⟩
    calc
      inner ℝ a (F z) = ∑ i, a i * u i x := by
        simp only [F,PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _
      _ = (J a).val.1 x := (hcombo a x).symm
      _ = v (c.F (complexIso z)) := by rw [← hv]; rfl
  have hdim := CircleSigns.disk_family_finrank_le_two F hc ?_ ?_ ?_
  · simpa only [finrank_euclideanSpace, Fintype.card_fin] using hdim
  · intro a ha
    obtain ⟨v,Z,hv,hvc,hZ,hvZ,hvjet⟩ := (J a).property
    have hn : ∃ x ∈ Ω, v x ≠ 0 := closedEigenJet_nonzero_interior hΩ.2.1 hvc hZ hvZ
      (fun hz => hjnz a ha (Subtype.ext (hvjet.symm.trans hz)))
    obtain ⟨x,hx,hvx⟩ := InteriorBoundarySign.exists_boundary_pos hΩ.2.1 hΩ.2.2.1 hv hvc hn
    let s : Circle := c.circleBoundaryHomeomorph.symm ⟨x,hx⟩
    have hs : c.F (complexIso (s:ℂ)) = x := congrArg Subtype.val (c.circleBoundaryHomeomorph.apply_symm_apply ⟨x,hx⟩)
    refine ⟨s,?_⟩
    rw [hval a hvjet s (by simp only [mem_closedBall_zero_iff,Circle.norm_coe,le_refl]),hs]
    exact hvx
  · intro a ha
    obtain ⟨v,Z,hv,hvc,hZ,hvZ,hvjet⟩ := (J a).property
    have hn : ∃ x ∈ Ω, v x ≠ 0 := closedEigenJet_nonzero_interior hΩ.2.1 hvc hZ hvZ
      (fun hz => hjnz a ha (Subtype.ext (hvjet.symm.trans hz)))
    have hcon := c.connected_complex_pull (P := Ioi 0) (InteriorNodal.positive_set_connected hΩ hv hn)
    convert hcon using 1
    ext z
    constructor
    · rintro ⟨hz,hp⟩
      refine ⟨hz,?_⟩
      simpa only [mem_ofPred_eq,mem_preimage,mem_Ioi,mem_Iio,← hval a hvjet z (ball_subset_closedBall hz)] using hp
    · rintro ⟨hz,hp⟩
      refine ⟨hz,?_⟩
      change (0:ℝ) < inner ℝ a (F z)
      rw [hval a hvjet z (ball_subset_closedBall hz)]
      exact hp
  · intro a ha
    obtain ⟨v,Z,hv,hvc,hZ,hvZ,hvjet⟩ := (J a).property
    have hn : ∃ x ∈ Ω, v x ≠ 0 := closedEigenJet_nonzero_interior hΩ.2.1 hvc hZ hvZ
      (fun hz => hjnz a ha (Subtype.ext (hvjet.symm.trans hz)))
    have hcon := c.connected_complex_pull (P := Iio 0) (InteriorNodal.negative_set_connected hΩ hv hn)
    convert hcon using 1
    ext z
    constructor
    · rintro ⟨hz,hp⟩
      refine ⟨hz,?_⟩
      simpa only [mem_ofPred_eq,mem_preimage,mem_Ioi,mem_Iio,← hval a hvjet z (ball_subset_closedBall hz)] using hp
    · rintro ⟨hz,hp⟩
      refine ⟨hz,?_⟩
      change inner ℝ a (F z) < (0:ℝ)
      rw [hval a hvjet z (ball_subset_closedBall hz)]
      exact hp


theorem closedEigenSpace_finrank_le_two {Ω : Set Plane} (c : Conformal.ClosedDiskChart Ω)
    (hΩ : AdmissibleDomain Ω) : Module.Finite ℝ (closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1) ∧
      Module.finrank ℝ (closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1) ≤ 2 := by
  have hr : Module.rank ℝ (closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1) < 3 := by
    by_contra hn
    obtain ⟨f,hf⟩ := exists_linearIndependent_of_le_rank (n := 3) (le_of_not_gt hn)
    have hh := closedEigenSpace_family_card c hΩ f hf
    norm_num at hh
  have hfinite : Module.Finite ℝ (closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1) :=
    Module.rank_lt_aleph0_iff.mp (hr.trans (Cardinal.natCast_lt_aleph0 (n := 3)))
  let : Module.Finite ℝ (closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1) := hfinite
  refine ⟨hfinite,?_⟩
  have he := Module.finrank_eq_rank ℝ (closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1)
  rw [← he] at hr
  exact Nat.le_of_lt_succ (by exact_mod_cast hr)
end StrictHotSpots
end
end ClosedEigenMultiplicity

section ClosedBoundaryZeroJet

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
include c




theorem hasFDerivWithinAt_zero_of_closedGradient_zero {v : Plane → ℝ}
    (hv : ContDiffOn ℝ ∞ v Ω) (hvc : ContinuousOn v (closure Ω))
    {Y : Plane → Plane} (hY : ContinuousOn Y (closure Ω)) (he : EqOn (gradient v) Y Ω)
    {p : Plane} (hp : p ∈ closure Ω) (hz : Y p = 0) :
    HasFDerivWithinAt v (0 : Plane →L[ℝ] ℝ) (closure Ω) p := by
  have hGp := c.inverse_maps_closed hp
  have hYG : Tendsto (fun z => Y (c.F z)) (𝓝[disk] (c.G p)) (𝓝 (0 : Plane)) := by
    have hc := (hY.comp c.continuous_closed c.maps_closed (c.G p) hGp).mono subset_closure
    change Tendsto (Y ∘ c.F) (𝓝[disk] c.G p) (𝓝 (Y (c.F (c.G p)))) at hc
    rw [c.right_inverse p hp,hz] at hc
    exact hc
  have hlim : Tendsto (fun z => fderiv ℝ (c.pullDatum v) z)
      (𝓝[disk] (c.G p)) (𝓝 (0 : Plane →L[ℝ] ℝ)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (g := fun z => c.bound * ‖Y (c.F z)‖) (Eventually.of_forall fun _ => norm_nonneg _)
    · filter_upwards [self_mem_nhdsWithin] with z hzD
      have hn : ‖fderiv ℝ (c.pullDatum v) z‖ = ‖gradient (c.pullDatum v) z‖ := by
        simp only [gradient,LinearIsometryEquiv.norm_map]
      rw [hn,c.pullDatum_grad_norm (hv.differentiableOn (by simp)) hzD,
        he (c.diskMap.map_source hzD),c.diskMap_agrees hzD]
      exact mul_le_mul_of_nonneg_right (c.bounded_deriv z (c.source_eq.symm ▸ hzD)) (norm_nonneg _)
    · simpa only [norm_zero,mul_zero] using tendsto_const_nhds.mul hYG.norm
  have hD : HasFDerivWithinAt (c.pullDatum v) (0 : Plane →L[ℝ] ℝ)
      (closure disk) (c.G p) :=
    hasFDerivWithinAt_closure_of_tendsto_fderiv
      ((c.pullDatum_smooth hv).differentiableOn (by simp))
      (convex_ball (0:Plane) 1) diskOpen
      (fun z hzD => (c.pullDatum_continuous hvc z hzD).mono subset_closure) hlim
  have ht : Tendsto c.G (𝓝[closure Ω] p) (𝓝[closure disk] (c.G p)) :=
    c.inverse_lipschitz.continuous.continuousWithinAt.tendsto_nhdsWithin c.inverse_maps_closed
  have hsmall := (hasFDerivWithinAt_iff_isLittleO.mp hD).comp_tendsto ht
  have hbig : (fun x => c.G x-c.G p) =O[𝓝[closure Ω] p] (fun x => x-p) :=
    Asymptotics.IsBigO.of_bound c.InvLip (Eventually.of_forall (fun x => c.inverse_lipschitz.norm_sub_le x p))
  have hh := hsmall.trans_isBigO hbig
  apply hasFDerivWithinAt_iff_isLittleO.mpr
  apply hh.congr' _ (Filter.EventuallyEq.refl _ _)
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [Function.comp_apply,zero_apply,sub_zero,pullDatum,
    c.right_inverse x hx,c.right_inverse p hp]

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ClosedBoundaryZeroJet


end OAI
