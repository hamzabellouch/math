import OAI.Analysis.HotSpots.Basic

namespace OAI

section DouglasLipschitzBase

noncomputable section

section DouglasMonomialCombinedLayer
open Set MeasureTheory AddCircle
open scoped InnerProductSpace
namespace StrictHotSpots.Douglas
variable {T : ℝ} [hT : Fact (0 < T)]

instance haar_nullSingleton : NullSingletonClass (@haarAddCircle T hT) := by
  constructor
  intro t
  have hv : (volume : Measure (AddCircle T)) {t} = 0 := by
    simpa only [Metric.closedBall_zero,mul_zero,min_eq_right hT.out.le,ENNReal.ofReal_zero]
      using (AddCircle.volume_closedBall T (x := t) 0)
  rw [volume_eq_smul_haarAddCircle,Measure.smul_apply,smul_eq_mul] at hv
  exact (mul_eq_zero.mp hv).resolve_left (ENNReal.ofReal_pos.mpr hT.out).ne'


def polynomial (n : ℕ) (a : ℕ → ℂ) : C(AddCircle T, ℂ) :=
  ∑ k ∈ Finset.range n, a k • fourier (k : ℤ)

omit hT in
lemma polynomial_apply (n : ℕ) (a : ℕ → ℂ) (s : AddCircle T) :
    polynomial n a s = ∑ k ∈ Finset.range n, a k * fourier (k : ℤ) s := by
  simp [polynomial,ContinuousMap.sum_apply]

lemma integral_norm_sq_polynomial (n : ℕ) (a : ℕ → ℂ) :
    (∫ s : AddCircle T, ‖polynomial n a s‖^2 ∂haarAddCircle) =
      ∑ k ∈ Finset.range n, ‖a k‖^2 := by
  have ho := (orthonormal_fourier (T := T)).comp (fun n : ℕ => (n : ℤ))
    Int.ofNat_injective
  have he := ho.inner_sum a a (Finset.range n)
  have he' : inner ℂ ((ContinuousMap.toLp 2 (@haarAddCircle T hT) ℂ) (polynomial n a))
      ((ContinuousMap.toLp 2 (@haarAddCircle T hT) ℂ) (polynomial n a)) =
        ∑ k ∈ Finset.range n, star (a k) * a k := by
    simpa only [polynomial,map_sum,map_smul,Function.comp_apply,RCLike.star_def]
      using he
  rw [ContinuousMap.inner_toLp] at he'
  have hi : Integrable (fun s : AddCircle T =>
      polynomial n a s * star (polynomial n a s)) haarAddCircle := by
    exact ((polynomial (T:=T) n a).memLp haarAddCircle ℂ (p:=2)).integrable_mul
      ((polynomial (T:=T) n a).memLp haarAddCircle ℂ (p:=2)).star
  have hr := congrArg Complex.re he'
  have hir : (∫ s : AddCircle T, polynomial n a s *
      (starRingEnd ℂ) (polynomial n a s) ∂haarAddCircle).re =
      ∫ s : AddCircle T, (polynomial n a s *
        (starRingEnd ℂ) (polynomial n a s)).re ∂haarAddCircle := (integral_re hi).symm
  rw [hir] at hr
  simpa only [RCLike.star_def,Complex.re_sum,Complex.mul_re,Complex.conj_re,Complex.conj_im,
    mul_neg,neg_mul,sub_neg_eq_add,← Complex.normSq_eq_norm_sq,Complex.normSq_apply] using hr

omit hT in
lemma fourier_nat (n : ℕ) (s : AddCircle T) :
    fourier (n : ℤ) s = (s.toCircle : ℂ)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_add,Nat.cast_one,fourier_add,ih,fourier_one,pow_succ]

omit hT in
lemma polynomial_geom (n : ℕ) (s t : AddCircle T) :
    polynomial n (fun k => (t.toCircle : ℂ)^(n-1-k)) s =
      ∑ k ∈ Finset.range n, (s.toCircle : ℂ)^k * (t.toCircle : ℂ)^(n-1-k) := by
  rw [polynomial_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [fourier_nat,mul_comm]

lemma normalized_monomial_quotient (n : ℕ) (t : AddCircle T) :
    (∫ s : AddCircle T,
      ‖((s.toCircle : ℂ)^n-(t.toCircle : ℂ)^n) /
        ((s.toCircle : ℂ)-(t.toCircle : ℂ))‖^2 ∂haarAddCircle) = (n : ℝ) := by
  have hnull : ∀ᵐ s : AddCircle T ∂haarAddCircle, s ≠ t := by
    simp only [ae_iff, not_not, measure_singleton, Set.ofPred_eq_eq_singleton]
  have he : (fun s : AddCircle T =>
      ‖((s.toCircle : ℂ)^n-(t.toCircle : ℂ)^n) /
        ((s.toCircle : ℂ)-(t.toCircle : ℂ))‖^2) =ᵐ[haarAddCircle]
      (fun s => ‖polynomial n (fun k => (t.toCircle : ℂ)^(n-1-k)) s‖^2) := by
    filter_upwards [hnull] with s hs
    have hne : (s.toCircle : ℂ)-(t.toCircle : ℂ) ≠ 0 := by
      intro hz
      apply hs
      exact injective_toCircle hT.out.ne' (Subtype.ext (sub_eq_zero.mp hz))
    rw [polynomial_geom,← geom_sum₂_mul _ _ n,mul_div_cancel_right₀ _ hne]
  rw [integral_congr_ae he,integral_norm_sq_polynomial]
  simp [norm_pow,Circle.norm_coe]



theorem monomial_double_integral (n : ℕ) :
    (∫ t : AddCircle T, ∫ s : AddCircle T,
      ‖((s.toCircle : ℂ)^n-(t.toCircle : ℂ)^n) /
        ((s.toCircle : ℂ)-(t.toCircle : ℂ))‖^2) = T^2 * (n : ℝ) := by
  rw [volume_eq_smul_haarAddCircle]
  simp_rw [integral_smul_measure,ENNReal.toReal_ofReal hT.out.le,smul_eq_mul,
    normalized_monomial_quotient]
  simp [pow_two,mul_assoc]

end StrictHotSpots.Douglas
end DouglasMonomialCombinedLayer

section LipschitzBoundaryEnergyCombinedLayer
open Set Filter MeasureTheory AddCircle
open scoped Topology
namespace StrictHotSpots.Douglas
variable {T : ℝ} [hT : Fact (0 < T)]


def boundaryDifference (h : AddCircle T → ℂ) (p : AddCircle T × AddCircle T) : ℂ :=
  (h p.1-h p.2) / ((p.1.toCircle : ℂ)-(p.2.toCircle : ℂ))


def ChordLipschitz (K : ℝ) (h : AddCircle T → ℂ) : Prop :=
  ∀ s t, ‖h s-h t‖ ≤ K*‖(s.toCircle : ℂ)-(t.toCircle : ℂ)‖

omit hT in
lemma boundaryDifference_bound {K : ℝ} (hK : 0 ≤ K) {h : AddCircle T → ℂ}
    (hh : ChordLipschitz K h) (p : AddCircle T × AddCircle T) :
    ‖boundaryDifference h p‖ ≤ K := by
  rw [boundaryDifference,norm_div]
  by_cases hz : (p.1.toCircle : ℂ)-(p.2.toCircle : ℂ) = 0
  · simpa only [hz,norm_zero,div_zero] using hK
  · exact (div_le_iff₀ (norm_pos_iff.mpr hz)).mpr (hh p.1 p.2)

omit hT in
lemma measurable_boundaryDifference {h : AddCircle T → ℂ} (hh : Continuous h) :
    Measurable (boundaryDifference h) := by
  apply Measurable.div
  · exact (hh.measurable.comp measurable_fst).sub (hh.measurable.comp measurable_snd)
  · exact ((continuous_subtype_val.comp continuous_toCircle).measurable.comp measurable_fst).sub
      ((continuous_subtype_val.comp continuous_toCircle).measurable.comp measurable_snd)

lemma integrable_boundaryDifference_sq {K : ℝ} (hK : 0 ≤ K)
    {h : AddCircle T → ℂ} (hc : Continuous h) (hh : ChordLipschitz K h) :
    Integrable (fun p => ‖boundaryDifference h p‖^2) := by
  refine (integrable_const (K^2)).mono'
    ((measurable_boundaryDifference hc).norm.pow_const 2).aestronglyMeasurable ?_
  exact ae_of_all _ fun p => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (boundaryDifference_bound hK hh p) 2


def boundaryEnergy (h : AddCircle T → ℂ) : ℝ :=
  ∫ p : AddCircle T × AddCircle T, ‖boundaryDifference h p‖^2



theorem boundaryEnergy_tendsto {K : ℝ} (hK : 0 ≤ K)
    {h : AddCircle T → ℂ} {f : ℕ → AddCircle T → ℂ}
    (hc : ∀ n, Continuous (f n)) (hf : ∀ n, ChordLipschitz K (f n))
    (hl : ∀ s, Tendsto (fun n => f n s) atTop (𝓝 (h s))) :
    Tendsto (fun n => boundaryEnergy (f n)) atTop (𝓝 (boundaryEnergy h)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ : AddCircle T × AddCircle T => K^2)
  · exact fun n => ((measurable_boundaryDifference (hc n)).norm.pow_const 2).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (boundaryDifference_bound hK (hf n) p) 2
  · exact ae_of_all _ fun p => (((hl p.1).sub (hl p.2)).div_const _).norm.pow 2

end StrictHotSpots.Douglas
end LipschitzBoundaryEnergyCombinedLayer

section BoundaryFourierCrossCombinedLayer
open Set MeasureTheory AddCircle
open scoped ComplexConjugate
namespace StrictHotSpots.Douglas
variable {T : ℝ} [hT : Fact (0 < T)]

omit hT in
lemma fourier_shift (m : ℤ) (s r : AddCircle T) :
    fourier m (s+r) = fourier m s * fourier m r := by
  simp only [fourier_apply,smul_add,toCircle_add,Circle.coe_mul]


def boundaryModeCross (m n : ℤ) (p : AddCircle T × AddCircle T) : ℂ :=
  ((fourier m p.1-fourier m p.2)*conj (fourier n p.1-fourier n p.2)) /
    ((‖(p.1.toCircle : ℂ)-(p.2.toCircle : ℂ)‖^2 : ℝ) : ℂ)

omit hT in
lemma boundaryModeCross_shift (m n : ℤ) (p : AddCircle T × AddCircle T)
    (r : AddCircle T) :
    boundaryModeCross m n (p+(r,r)) = boundaryModeCross m n p * fourier (m-n) r := by
  rw [show m-n = m+(-n) by rfl,fourier_add,fourier_neg]
  simp only [boundaryModeCross,Prod.fst_add,Prod.snd_add,fourier_shift,toCircle_add,
    Circle.coe_mul]
  rw [← sub_mul,← sub_mul,← sub_mul]
  simp only [norm_mul,Circle.norm_coe,mul_one,map_mul]
  ring


theorem boundaryModeCross_integral_zero {m n : ℤ} (hmn : m ≠ n) :
    (∫ p : AddCircle T × AddCircle T, boundaryModeCross m n p) = 0 := by
  let r : AddCircle T := (T/2/(m-n) : ℝ)
  have hf : fourier (m-n) r = -1 := by
    simpa only [zero_add,fourier_eval_zero,Int.cast_sub,r] using
      fourier_add_half_inv_index (sub_ne_zero.mpr hmn) hT.out (0 : AddCircle T)
  let : (volume : Measure (AddCircle T × AddCircle T)).IsAddRightInvariant := ⟨fun g =>
    ((measurePreserving_add_right (volume : Measure (AddCircle T)) g.1).prod
      (measurePreserving_add_right (volume : Measure (AddCircle T)) g.2)).map_eq⟩
  apply integral_eq_zero_of_add_right_eq_neg (g := (r,r))
  intro p
  rw [boundaryModeCross_shift,hf,mul_neg_one]

end StrictHotSpots.Douglas
end BoundaryFourierCrossCombinedLayer

section DouglasBulkModeCombinedLayer
open Set MeasureTheory Metric
open scoped Topology
namespace StrictHotSpots.Douglas

lemma integral_disk_norm_pow (n : ℕ) :
    (∫ z : ℂ in ball 0 1, ‖z‖^n) = (2*Real.pi)/(n+2) := by
  classical
  let f : ℂ → ℝ := (ball 0 1).indicator (fun z => ‖z‖^n)
  have h1 : (∫ z : ℂ in ball 0 1, ‖z‖^n) =
      ∫ p in polarCoord.target, p.1 * f (Complex.polarCoord.symm p) := by
    rw [← integral_indicator measurableSet_ball]
    exact (Complex.integral_comp_polarCoord_symm f).symm
  rw [h1]
  have he : polarCoord.target.indicator
      (fun p : ℝ × ℝ => p.1 * f (Complex.polarCoord.symm p)) =
      ((Ioo (0:ℝ) 1) ×ˢ (Ioo (-Real.pi) Real.pi)).indicator
        (fun p => p.1^(n+1)) := by
    funext p
    have hf : f (Complex.polarCoord.symm p) =
        if |p.1| < 1 then |p.1|^n else 0 := by
      change (if Complex.polarCoord.symm p ∈ ball (0:ℂ) 1 then
        ‖Complex.polarCoord.symm p‖^n else 0) = _
      rw [mem_ball_zero_iff,Complex.norm_polarCoord_symm]
    by_cases hr : 0 < p.1
    · by_cases ht : -Real.pi < p.2 ∧ p.2 < Real.pi
      · by_cases hR : p.1 < 1 <;>
          simp only [Set.indicator_apply,polarCoord_target,mem_prod,mem_Ioi,mem_Ioo,
            hr,ht,hR,and_self,ite_true,ite_false,hf,abs_of_pos hr,mul_zero,
            pow_succ,mul_comm,false_and,and_false]
      · simp only [Set.indicator_apply,polarCoord_target,mem_prod,mem_Ioi,mem_Ioo,
          hr,ht,and_false,ite_false]
    · simp [polarCoord_target,hr]
  rw [← integral_indicator polarCoord.open_target.measurableSet,he,
    integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
  have hi : (∫ r : ℝ in Ioo 0 1, r^(n+1)) = 1/(n+2) := by
    rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      integral_pow]
    simp [add_assoc]
    norm_num
  have hp := setIntegral_prod_mul (fun r : ℝ => r^(n+1)) (fun _ : ℝ => (1:ℝ))
    (Ioo 0 1) (Ioo (-Real.pi) Real.pi) (μ:=volume) (ν:=volume)
  simp only [mul_one] at hp
  rw [Measure.volume_eq_prod ℝ ℝ,hp,hi]
  have hpos : 0 ≤ Real.pi - -Real.pi := by linarith [Real.pi_pos]
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Ioo,ENNReal.toReal_ofReal hpos,
    smul_eq_mul,mul_one]
  ring



lemma holomorphic_mode_energy (n : ℕ) :
    (∫ z : ℂ in ball 0 1, 2 * ‖((n+1 : ℕ) : ℂ) * z^n‖^2) =
      2*Real.pi*(n+1) := by
  simp_rw [norm_mul,Complex.norm_natCast,norm_pow,mul_pow,← pow_mul]
  rw [integral_const_mul,integral_const_mul,integral_disk_norm_pow]
  push_cast
  field_simp

end StrictHotSpots.Douglas
end DouglasBulkModeCombinedLayer

section DouglasModesCombinedLayer
open Set MeasureTheory Metric AddCircle InnerProductSpace
open scoped ComplexConjugate
namespace StrictHotSpots.Douglas

local instance twoPiPos : Fact (0 < 2*Real.pi) := ⟨by positivity⟩


def harmonicMode : ℤ → ℂ → ℂ
  | .ofNat n, z => z^n
  | .negSucc n, z => conj (z^(n+1))

lemma harmonicMode_boundary {T : ℝ} (m : ℤ) (s : AddCircle T) :
    harmonicMode m s.toCircle = fourier m s := by
  cases m with
  | ofNat n => exact (fourier_nat n s).symm
  | negSucc n =>
    change conj ((s.toCircle : ℂ)^(n+1)) = fourier (-(↑(n+1) : ℤ)) s
    rw [fourier_neg,fourier_nat]

lemma harmonicMode_harmonic (m : ℤ) (z : ℂ) : HarmonicAt (harmonicMode m) z := by
  cases m with
  | ofNat n => exact (analyticAt_id.pow n).harmonicAt
  | negSucc n => exact (analyticAt_id.pow (n+1)).harmonicAt_conj

lemma harmonicMode_continuous (m : ℤ) : Continuous (harmonicMode m) := by
  cases m with
  | ofNat n =>
    change Continuous (fun z : ℂ => z^n)
    fun_prop
  | negSucc n =>
    change Continuous (fun z : ℂ => conj (z^(n+1)))
    fun_prop

lemma harmonicMode_poisson (m : ℤ) {z : ℂ} (hz : z ∈ ball 0 1) :
    Real.circleAverage (poissonKernel 0 z • harmonicMode m) 0 1 =
      harmonicMode m z := by
  have hk : ContinuousOn (poissonKernel 0 z) (sphere 0 1) := by
    unfold poissonKernel
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro w hw
    simp only [sub_zero]
    apply pow_ne_zero
    apply norm_ne_zero_iff.mpr
    apply sub_ne_zero.mpr
    intro he
    have hw' : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hw
    have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    rw [he] at hw'
    linarith
  have hci : CircleIntegrable (poissonKernel 0 z • harmonicMode m) 0 1 :=
    (hk.smul (harmonicMode_continuous m).continuousOn).circleIntegrable (by norm_num)
  have hr : HarmonicOnNhd (Complex.reCLM ∘ harmonicMode m) (closedBall 0 1) :=
    fun w _ => (harmonicMode_harmonic m w).comp_CLM Complex.reCLM
  have hi : HarmonicOnNhd (Complex.imCLM ∘ harmonicMode m) (closedBall 0 1) :=
    fun w _ => (harmonicMode_harmonic m w).comp_CLM Complex.imCLM
  apply Complex.ext
  · have h := hr.circleAverage_poissonKernel_smul hz
    change Complex.reCLM (Real.circleAverage _ _ _) = _
    rw [← Complex.reCLM.circleAverage_comp_comm hci]
    have he : Complex.reCLM ∘ (poissonKernel 0 z • harmonicMode m) =
        poissonKernel 0 z • (Complex.reCLM ∘ harmonicMode m) := by
      funext w
      exact map_smul Complex.reCLM (poissonKernel 0 z w) (harmonicMode m w)
    rw [he]
    exact h
  · have h := hi.circleAverage_poissonKernel_smul hz
    change Complex.imCLM (Real.circleAverage _ _ _) = _
    rw [← Complex.imCLM.circleAverage_comp_comm hci]
    have he : Complex.imCLM ∘ (poissonKernel 0 z • harmonicMode m) =
        poissonKernel 0 z • (Complex.imCLM ∘ harmonicMode m) := by
      funext w
      exact map_smul Complex.imCLM (poissonKernel 0 z w) (harmonicMode m w)
    rw [he]
    exact h

lemma fderiv_pow_mode (n : ℕ) (z e : ℂ) :
    fderiv ℝ (fun w : ℂ => w^(n+1)) z e = e * ((n+1 : ℕ) * z^n) := by
  have h := (hasDerivAt_pow (n+1) z).hasFDerivAt.restrictScalars ℝ
  simpa using congrArg (fun L : ℂ →L[ℝ] ℂ => L e) h.fderiv

lemma fderiv_conj_mode (n : ℕ) (z e : ℂ) :
    fderiv ℝ (fun w : ℂ => conj (w^(n+1))) z e =
      conj (e * ((n+1 : ℕ) * z^n)) := by
  have h := (hasDerivAt_pow (n+1) z).hasFDerivAt.restrictScalars ℝ
  have hc := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z h
  have he := congrArg (fun L : ℂ →L[ℝ] ℂ => L e) hc.fderiv
  change fderiv ℝ (fun w : ℂ => conj (w^(n+1))) z e =
    conj (e * ((n+1 : ℕ) * z^(n+1-1))) at he
  simpa only [Nat.add_sub_cancel] using he



theorem harmonicMode_energy (m : ℤ) :
    (∫ z : ℂ in ball 0 1,
      ‖fderiv ℝ (harmonicMode m) z 1‖^2 + ‖fderiv ℝ (harmonicMode m) z Complex.I‖^2) =
      2*Real.pi*(m.natAbs : ℝ) := by
  cases m with
  | ofNat n =>
    cases n with
    | zero =>
      change (∫ z : ℂ in ball 0 1,
        ‖fderiv ℝ (fun _ : ℂ => (1:ℂ)) z 1‖^2 +
        ‖fderiv ℝ (fun _ : ℂ => (1:ℂ)) z Complex.I‖^2) = _
      simp
    | succ n =>
      change (∫ z : ℂ in ball 0 1,
        ‖fderiv ℝ (fun w : ℂ => w^(n+1)) z 1‖^2 +
        ‖fderiv ℝ (fun w : ℂ => w^(n+1)) z Complex.I‖^2) = _
      simp_rw [fderiv_pow_mode,one_mul,norm_mul,Complex.norm_I,one_mul,← two_mul]
      change _ = 2*Real.pi*((n+1 : ℕ) : ℝ)
      simpa only [norm_mul,Nat.cast_add,Nat.cast_one] using holomorphic_mode_energy n
  | negSucc n =>
    change (∫ z : ℂ in ball 0 1,
      ‖fderiv ℝ (fun w : ℂ => conj (w^(n+1))) z 1‖^2 +
      ‖fderiv ℝ (fun w : ℂ => conj (w^(n+1))) z Complex.I‖^2) = _
    simp_rw [fderiv_conj_mode,Complex.norm_conj,one_mul,norm_mul,Complex.norm_I,
      one_mul,← two_mul]
    simpa only [norm_mul,Int.natAbs_negSucc,Nat.cast_add,Nat.cast_one,Nat.succ_eq_add_one]
      using holomorphic_mode_energy n


theorem fourier_double_integral {T : ℝ} [Fact (0 < T)] (m : ℤ) :
    (∫ t : AddCircle T, ∫ s : AddCircle T,
      ‖(fourier m s-fourier m t) / ((s.toCircle : ℂ)-(t.toCircle : ℂ))‖^2) =
        T^2 * (m.natAbs : ℝ) := by
  cases m with
  | ofNat n =>
    have h := monomial_double_integral (T:=T) n
    simp_rw [← fourier_nat] at h
    exact h
  | negSucc n =>
    change (∫ t : AddCircle T, ∫ s : AddCircle T,
      ‖(fourier (-(↑(n+1) : ℤ)) s-fourier (-(↑(n+1) : ℤ)) t) /
        ((s.toCircle : ℂ)-(t.toCircle : ℂ))‖^2) = _
    simp_rw [fourier_neg,← map_sub,norm_div,Complex.norm_conj,← norm_div,fourier_nat]
    exact monomial_double_integral (n+1)


theorem douglas_for_mode (m : ℤ) :
    (∫ z : ℂ in ball 0 1,
      ‖fderiv ℝ (harmonicMode m) z 1‖^2 + ‖fderiv ℝ (harmonicMode m) z Complex.I‖^2) =
    (1/(2*Real.pi)) *
      (∫ t : AddCircle (2*Real.pi), ∫ s : AddCircle (2*Real.pi),
        ‖(fourier m s-fourier m t) / ((s.toCircle : ℂ)-(t.toCircle : ℂ))‖^2) := by
  rw [harmonicMode_energy,fourier_double_integral]
  field_simp

end StrictHotSpots.Douglas
end DouglasModesCombinedLayer

section BoundaryFourierIntegrableCombinedLayer
open Set Filter MeasureTheory AddCircle
open scoped ComplexConjugate
namespace StrictHotSpots.Douglas
variable {T : ℝ} [hT : Fact (0 < T)]

lemma norm_pow_sub_pow_of_unit {a b : ℂ} (ha : ‖a‖=1) (hb : ‖b‖=1) (n : ℕ) :
    ‖a^n-b^n‖ ≤ (n:ℝ)*‖a-b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : a^(n+1)-b^(n+1)=a^n*(a-b)+(a^n-b^n)*b := by ring
    rw [he]
    calc
      _ ≤ ‖a^n*(a-b)‖+‖(a^n-b^n)*b‖ := norm_add_le _ _
      _ = ‖a-b‖+‖a^n-b^n‖ := by rw [norm_mul,norm_mul,norm_pow,ha,hb]; simp
      _ ≤ ‖a-b‖+(n:ℝ)*‖a-b‖ := add_le_add_right ih _
      _ = ((n+1:ℕ):ℝ)*‖a-b‖ := by push_cast; ring

omit hT in
lemma chordLipschitz_fourier (m : ℤ) : ChordLipschitz (m.natAbs:ℝ) (@fourier T m) := by
  intro s t
  cases m with
  | ofNat n =>
    change ‖fourier (n:ℤ) s-fourier (n:ℤ) t‖ ≤ (n:ℝ)*_
    rw [fourier_nat,fourier_nat]
    exact norm_pow_sub_pow_of_unit (Circle.norm_coe _) (Circle.norm_coe _) n
  | negSucc n =>
    change ‖fourier (-(↑(n+1) : ℤ)) s-fourier (-(↑(n+1) : ℤ)) t‖ ≤ _
    rw [fourier_neg,fourier_neg,← map_sub,Complex.norm_conj,fourier_nat,fourier_nat]
    exact norm_pow_sub_pow_of_unit (Circle.norm_coe _) (Circle.norm_coe _) (n+1)

omit hT in
lemma boundaryModeCross_eq (m n : ℤ) (p : AddCircle T × AddCircle T) :
    boundaryModeCross m n p =
      boundaryDifference (fourier m) p * conj (boundaryDifference (fourier n) p) := by
  simp only [boundaryModeCross,boundaryDifference,map_div₀,div_mul_div_comm,
    Complex.mul_conj,Complex.normSq_eq_norm_sq]

lemma integrable_boundaryModeCross (m n : ℤ) :
    Integrable (boundaryModeCross (T:=T) m n) := by
  have he : boundaryModeCross (T:=T) m n = fun p =>
      boundaryDifference (fourier m) p * conj (boundaryDifference (fourier n) p) := by
    funext p; exact boundaryModeCross_eq m n p
  rw [he]
  refine (integrable_const ((m.natAbs:ℝ)*(n.natAbs:ℝ))).mono' ?_ ?_
  · exact ((measurable_boundaryDifference (fourier m).continuous).mul
      ((Complex.continuous_conj.measurable).comp
        (measurable_boundaryDifference (fourier n).continuous))).aestronglyMeasurable
  · exact ae_of_all _ fun p => by
      rw [norm_mul,Complex.norm_conj]
      exact mul_le_mul (boundaryDifference_bound (by positivity) (chordLipschitz_fourier m) p)
        (boundaryDifference_bound (by positivity) (chordLipschitz_fourier n) p)
        (norm_nonneg _) (by positivity)

lemma boundaryDifference_sq_integral (m : ℤ) :
    (∫ p : AddCircle T × AddCircle T, ‖boundaryDifference (fourier m) p‖^2) =
      T^2*(m.natAbs:ℝ) := by
  have hi := integrable_boundaryDifference_sq (by positivity : 0 ≤ (m.natAbs:ℝ))
    (fourier (T:=T) m).continuous (chordLipschitz_fourier m)
  rw [Measure.volume_eq_prod (AddCircle T) (AddCircle T),integral_prod _ hi]
  have he : (∫ x : AddCircle T, ∫ y : AddCircle T,
      ‖boundaryDifference (fourier m) (x,y)‖^2) =
    (∫ x : AddCircle T, ∫ y : AddCircle T,
      ‖(fourier m y-fourier m x)/((y.toCircle:ℂ)-(x.toCircle:ℂ))‖^2) := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => integral_congr_ae (ae_of_all _ fun y => by
      simp only [boundaryDifference,norm_div]
      rw [norm_sub_rev (fourier m x),norm_sub_rev (x.toCircle:ℂ)])
  exact he.trans (fourier_double_integral m)


theorem boundaryModeCross_integral (m n : ℤ) :
    (∫ p : AddCircle T × AddCircle T, boundaryModeCross m n p) =
      if m=n then ((T^2*(m.natAbs:ℝ):ℝ):ℂ) else 0 := by
  classical
  split_ifs with h
  · subst n
    have he : boundaryModeCross (T:=T) m m = fun p =>
        ((‖boundaryDifference (fourier m) p‖^2:ℝ):ℂ) := by
      funext p
      rw [boundaryModeCross_eq,Complex.mul_conj,Complex.normSq_eq_norm_sq]
    rw [he,integral_complex_ofReal,boundaryDifference_sq_integral]
  · exact boundaryModeCross_integral_zero h

end StrictHotSpots.Douglas
end BoundaryFourierIntegrableCombinedLayer

section BoundaryFourierPolynomialCombinedLayer
open Set MeasureTheory AddCircle
open scoped ComplexConjugate
namespace StrictHotSpots.Douglas
variable {T : ℝ} [hT : Fact (0 < T)]

def boundaryPolynomial (S : Finset ℤ) (a : ℤ → ℂ) (x : AddCircle T) : ℂ :=
  ∑ m ∈ S, a m * fourier m x

omit hT in
lemma boundaryDifference_polynomial (S : Finset ℤ) (a : ℤ → ℂ)
    (p : AddCircle T × AddCircle T) :
    boundaryDifference (boundaryPolynomial S a) p =
      ∑ m ∈ S, a m * boundaryDifference (fourier m) p := by
  simp only [boundaryDifference,boundaryPolynomial,← Finset.sum_sub_distrib,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m _
  ring

omit hT in
lemma boundaryPolynomial_sq (S : Finset ℤ) (a : ℤ → ℂ)
    (p : AddCircle T × AddCircle T) :
    ((‖boundaryDifference (boundaryPolynomial S a) p‖^2 : ℝ) : ℂ) =
      ∑ m ∈ S, ∑ n ∈ S, (a m*conj (a n))*boundaryModeCross m n p := by
  rw [← Complex.normSq_eq_norm_sq,← Complex.mul_conj,boundaryDifference_polynomial]
  simp only [map_sum,Finset.sum_mul,Finset.mul_sum,map_mul,boundaryModeCross_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  ring

lemma boundaryPolynomial_energy (S : Finset ℤ) (a : ℤ → ℂ) :
    boundaryEnergy (boundaryPolynomial (T:=T) S a) =
      T^2 * ∑ m ∈ S, (m.natAbs:ℝ)*‖a m‖^2 := by
  classical
  have hi (m n : ℤ) : Integrable (fun p : AddCircle T × AddCircle T =>
      (a m*conj (a n))*boundaryModeCross m n p) :=
    (integrable_boundaryModeCross m n).const_mul _
  have he : (fun p : AddCircle T × AddCircle T =>
      ((‖boundaryDifference (boundaryPolynomial S a) p‖^2 : ℝ) : ℂ)) =
      fun p => ∑ m ∈ S, ∑ n ∈ S, (a m*conj (a n))*boundaryModeCross m n p := by
    funext p; exact boundaryPolynomial_sq S a p
  apply Complex.ofReal_injective
  change ((∫ p : AddCircle T × AddCircle T,
      ‖boundaryDifference (boundaryPolynomial S a) p‖^2 : ℝ) : ℂ) = _
  rw [← integral_complex_ofReal,he]
  rw [integral_finsetSum S (fun m _ => integrable_finsetSum S (fun n _ => hi m n))]
  simp_rw [integral_finsetSum S (fun n _ => hi _ n),integral_const_mul,
    boundaryModeCross_integral]
  have hs : (∑ m ∈ S, ∑ n ∈ S,
      (a m*conj (a n))*(if m=n then ((T^2*(m.natAbs:ℝ):ℝ):ℂ) else 0)) =
      ∑ m ∈ S, (a m*conj (a m))*((T^2*(m.natAbs:ℝ):ℝ):ℂ) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.sum_eq_single m]
    · simp
    · intro n _ hnm
      simp [Ne.symm hnm]
    · exact fun h => (h hm).elim
  rw [hs]
  simp only [Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.ofReal_mul,
    Complex.ofReal_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

end StrictHotSpots.Douglas
end BoundaryFourierPolynomialCombinedLayer

section DiskRotationCombinedLayer
open Set MeasureTheory Metric
namespace StrictHotSpots.Douglas

def circleRotation (u : Circle) : ℂ ≃ₗᵢ[ℝ] ℂ where
  toFun z := u • z
  invFun z := u⁻¹ • z
  left_inv z := inv_smul_smul u z
  right_inv z := smul_inv_smul u z
  map_add' z w := smul_add u z w
  map_smul' r z := smul_comm u r z
  norm_map' z := Circle.norm_smul u z

lemma circleRotation_apply (u : Circle) (z : ℂ) : circleRotation u z = (u:ℂ)*z := rfl

lemma integral_disk_rotation (u : Circle) (f : ℂ → ℂ) :
    (∫ z : ℂ in ball 0 1, f ((u:ℂ)*z)) = ∫ z : ℂ in ball 0 1, f z := by
  have h := (circleRotation u).measurePreserving.integral_comp
    (circleRotation u).toHomeomorph.measurableEmbedding ((ball (0:ℂ) 1).indicator f)
  have he : (fun z => (ball (0:ℂ) 1).indicator f (circleRotation u z)) =
      (ball (0:ℂ) 1).indicator (fun z => f ((u:ℂ)*z)) := by
    funext z
    have hm : circleRotation u z ∈ ball (0:ℂ) 1 ↔ z ∈ ball 0 1 := by
      simp only [mem_ball_zero_iff,(circleRotation u).norm_map]
    by_cases hz : z ∈ ball (0:ℂ) 1
    · rw [Set.indicator_of_mem (hm.mpr hz),Set.indicator_of_mem hz,circleRotation_apply]
    · rw [Set.indicator_of_notMem (mt hm.mp hz),Set.indicator_of_notMem hz]
  rw [he,integral_indicator measurableSet_ball,integral_indicator measurableSet_ball] at h
  exact h
end StrictHotSpots.Douglas
end DiskRotationCombinedLayer

section DiskMonomialCrossCombinedLayer
open Set MeasureTheory Metric AddCircle
open scoped ComplexConjugate
namespace StrictHotSpots.Douglas
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

lemma monomialCross_rotation (k l : ℕ) (s : AddCircle (2*Real.pi)) (z : ℂ) :
    ((s.toCircle:ℂ)*z)^k * conj (((s.toCircle:ℂ)*z)^l) =
      (z^k * conj (z^l)) * fourier ((k:ℤ)-(l:ℤ)) s := by
  rw [sub_eq_add_neg,fourier_add,fourier_neg,fourier_nat,fourier_nat]
  simp only [mul_pow,map_mul]
  ring

lemma integral_disk_monomial_cross_zero {k l : ℕ} (hkl : k ≠ l) :
    (∫ z : ℂ in ball 0 1, z^k * conj (z^l)) = 0 := by
  let r : AddCircle (2*Real.pi) := ((2*Real.pi)/2/((k:ℤ)-(l:ℤ)) : ℝ)
  have hne : (k:ℤ)-(l:ℤ) ≠ 0 := sub_ne_zero.mpr (Int.ofNat_inj.not.mpr hkl)
  have hf : fourier ((k:ℤ)-(l:ℤ)) r = -1 := by
    simpa only [zero_add,fourier_eval_zero,r,Int.cast_sub] using
      fourier_add_half_inv_index hne (by positivity : 0 < 2*Real.pi)
        (0 : AddCircle (2*Real.pi))
  have h := integral_disk_rotation r.toCircle (fun z => z^k*conj (z^l))
  simp_rw [monomialCross_rotation,hf,mul_neg_one] at h
  rw [integral_neg] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  apply Complex.ext <;> simp only [Complex.neg_re,Complex.neg_im,Complex.zero_re,
    Complex.zero_im] at * <;> linarith

lemma integrableOn_monomial_cross (k l : ℕ) :
    IntegrableOn (fun z : ℂ => z^k*conj (z^l)) (ball 0 1) := by
  have hc : Continuous (fun z : ℂ => z^k*conj (z^l)) := by fun_prop
  exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall

lemma integral_disk_monomial_cross (k l : ℕ) :
    (∫ z : ℂ in ball 0 1, z^k * conj (z^l)) =
      if k=l then (((2*Real.pi)/((2*k:ℕ)+2):ℝ):ℂ) else 0 := by
  classical
  split_ifs with h
  · subst l
    have he : (fun z : ℂ => z^k*conj (z^k)) = fun z => ((‖z‖^(2*k):ℝ):ℂ) := by
      funext z
      rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,norm_pow,← pow_mul,mul_comm k 2]
    rw [he,integral_complex_ofReal,integral_disk_norm_pow]
  · exact integral_disk_monomial_cross_zero h
end StrictHotSpots.Douglas
end DiskMonomialCrossCombinedLayer

section DiskModeCrossCombinedLayer
open Set MeasureTheory Metric
open scoped ComplexConjugate
namespace StrictHotSpots.Douglas

def bulkModeCross (m n : ℤ) (z : ℂ) : ℂ :=
  fderiv ℝ (harmonicMode m) z 1 * conj (fderiv ℝ (harmonicMode n) z 1) +
  fderiv ℝ (harmonicMode m) z Complex.I * conj (fderiv ℝ (harmonicMode n) z Complex.I)

lemma bulkModeCross_zero_left (n : ℤ) (z : ℂ) : bulkModeCross 0 n z = 0 := by
  have he : harmonicMode 0 = fun _ : ℂ => (1:ℂ) := by funext w; change w^0=1; exact pow_zero w
  simp [bulkModeCross,he]

lemma bulkModeCross_symm (m n : ℤ) (z : ℂ) :
    bulkModeCross m n z = conj (bulkModeCross n m z) := by
  simp only [bulkModeCross,map_add,map_mul,Complex.conj_conj]
  ring

lemma bulkModeCross_pos (k l : ℕ) (z : ℂ) :
    bulkModeCross (k+1:ℕ) (l+1:ℕ) z =
      (2*((k+1:ℕ):ℂ)*((l+1:ℕ):ℂ))*(z^k * conj (z^l)) := by
  change (fderiv ℝ (fun w : ℂ => w^(k+1)) z 1 *
      conj (fderiv ℝ (fun w : ℂ => w^(l+1)) z 1) +
    fderiv ℝ (fun w : ℂ => w^(k+1)) z Complex.I *
      conj (fderiv ℝ (fun w : ℂ => w^(l+1)) z Complex.I)) = _
  simp only [fderiv_pow_mode,one_mul,map_mul,map_natCast,Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma bulkModeCross_neg (k l : ℕ) (z : ℂ) :
    bulkModeCross (Int.negSucc k) (Int.negSucc l) z =
      conj (bulkModeCross (k+1:ℕ) (l+1:ℕ) z) := by
  change (fderiv ℝ (fun w : ℂ => conj (w^(k+1))) z 1 *
      conj (fderiv ℝ (fun w : ℂ => conj (w^(l+1))) z 1) +
    fderiv ℝ (fun w : ℂ => conj (w^(k+1))) z Complex.I *
      conj (fderiv ℝ (fun w : ℂ => conj (w^(l+1))) z Complex.I)) = _
  rw [bulkModeCross_pos]
  simp only [fderiv_conj_mode,one_mul,map_mul,map_natCast,Complex.conj_I,
    Complex.conj_conj,map_ofNat]
  ring_nf
  simp only [map_neg,Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma bulkModeCross_mixed (k l : ℕ) (z : ℂ) :
    bulkModeCross (k+1:ℕ) (Int.negSucc l) z = 0 := by
  change (fderiv ℝ (fun w : ℂ => w^(k+1)) z 1 *
      conj (fderiv ℝ (fun w : ℂ => conj (w^(l+1))) z 1) +
    fderiv ℝ (fun w : ℂ => w^(k+1)) z Complex.I *
      conj (fderiv ℝ (fun w : ℂ => conj (w^(l+1))) z Complex.I)) = _
  simp only [fderiv_pow_mode,fderiv_conj_mode,one_mul,Complex.conj_conj]
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma bulkModeCross_continuous (m n : ℤ) : Continuous (bulkModeCross m n) := by
  have hp (k l : ℕ) : Continuous (bulkModeCross (k+1:ℕ) (l+1:ℕ)) := by
    simp_rw [funext (bulkModeCross_pos k l)]
    fun_prop
  have hn (k l : ℕ) : Continuous (bulkModeCross (Int.negSucc k) (Int.negSucc l)) := by
    simp_rw [funext (bulkModeCross_neg k l)]
    exact Complex.continuous_conj.comp (hp k l)
  cases m with
  | ofNat k =>
    cases k with
    | zero =>
      change Continuous (bulkModeCross 0 n)
      rw [funext (bulkModeCross_zero_left n)]; exact continuous_const
    | succ k =>
      cases n with
      | ofNat l =>
        cases l with
        | zero =>
          have he : bulkModeCross (k+1:ℕ) 0 = fun _ => (0:ℂ) := by
            funext z; rw [bulkModeCross_symm,bulkModeCross_zero_left,map_zero]
          change Continuous (bulkModeCross (k+1:ℕ) 0)
          rw [he]; exact continuous_const
        | succ l => exact hp k l
      | negSucc l =>
        change Continuous (bulkModeCross (k+1:ℕ) (Int.negSucc l))
        rw [funext (bulkModeCross_mixed k l)]; exact continuous_const
  | negSucc k =>
    cases n with
    | ofNat l =>
      cases l with
      | zero =>
        have he : bulkModeCross (Int.negSucc k) 0 = fun _ => (0:ℂ) := by
          funext z; rw [bulkModeCross_symm,bulkModeCross_zero_left,map_zero]
        change Continuous (bulkModeCross (Int.negSucc k) 0)
        rw [he]; exact continuous_const
      | succ l =>
        have he : bulkModeCross (Int.negSucc k) (l+1:ℕ) = fun _ => (0:ℂ) := by
          funext z; rw [bulkModeCross_symm,bulkModeCross_mixed,map_zero]
        change Continuous (bulkModeCross (Int.negSucc k) (l+1:ℕ))
        rw [he]; exact continuous_const
    | negSucc l => exact hn k l

lemma bulkModeCross_integrable (m n : ℤ) :
    IntegrableOn (bulkModeCross m n) (ball 0 1) :=
  ((bulkModeCross_continuous m n).continuousOn.integrableOn_compact (isCompact_closedBall 0 1)).mono_set
    ball_subset_closedBall

end StrictHotSpots.Douglas
end DiskModeCrossCombinedLayer

section DiskModeGramCombinedLayer
open Set MeasureTheory Metric
open scoped ComplexConjugate
namespace StrictHotSpots.Douglas

lemma bulkModeCross_self_integral (m : ℤ) :
    (∫ z : ℂ in ball 0 1, bulkModeCross m m z) =
      ((2*Real.pi*(m.natAbs:ℝ):ℝ):ℂ) := by
  have he : bulkModeCross m m = fun z =>
      ((‖fderiv ℝ (harmonicMode m) z 1‖^2 +
        ‖fderiv ℝ (harmonicMode m) z Complex.I‖^2 : ℝ):ℂ) := by
    funext z
    simp only [bulkModeCross,Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.ofReal_add]
  rw [he,integral_complex_ofReal,harmonicMode_energy]

lemma bulkModeCross_pos_integral_zero {k l : ℕ} (hkl : k ≠ l) :
    (∫ z : ℂ in ball 0 1, bulkModeCross (k+1:ℕ) (l+1:ℕ) z) = 0 := by
  simp_rw [bulkModeCross_pos]
  rw [integral_const_mul,integral_disk_monomial_cross_zero hkl,mul_zero]

lemma bulkModeCross_zero_right (m : ℤ) (z : ℂ) : bulkModeCross m 0 z = 0 := by
  rw [bulkModeCross_symm,bulkModeCross_zero_left,map_zero]

lemma bulkModeCross_opposite (k l : ℕ) (z : ℂ) :
    bulkModeCross (Int.negSucc k) (l+1:ℕ) z = 0 := by
  rw [bulkModeCross_symm,bulkModeCross_mixed,map_zero]

lemma bulkModeCross_integral_zero {m n : ℤ} (hmn : m ≠ n) :
    (∫ z : ℂ in ball 0 1, bulkModeCross m n z) = 0 := by
  cases m with
  | ofNat k =>
    cases k with
    | zero =>
      change (∫ z : ℂ in ball 0 1, bulkModeCross 0 n z) = 0
      simp_rw [bulkModeCross_zero_left]; exact integral_zero _ _
    | succ k =>
      cases n with
      | ofNat l =>
        cases l with
        | zero =>
          change (∫ z : ℂ in ball 0 1, bulkModeCross (k+1:ℕ) 0 z) = 0
          simp_rw [bulkModeCross_zero_right]; exact integral_zero _ _
        | succ l =>
          exact bulkModeCross_pos_integral_zero (fun h => hmn (by subst l; rfl))
      | negSucc l =>
        change (∫ z : ℂ in ball 0 1, bulkModeCross (k+1:ℕ) (Int.negSucc l) z) = 0
        simp_rw [bulkModeCross_mixed]; exact integral_zero _ _
  | negSucc k =>
    cases n with
    | ofNat l =>
      cases l with
      | zero =>
        change (∫ z : ℂ in ball 0 1, bulkModeCross (Int.negSucc k) 0 z) = 0
        simp_rw [bulkModeCross_zero_right]; exact integral_zero _ _
      | succ l =>
        change (∫ z : ℂ in ball 0 1, bulkModeCross (Int.negSucc k) (l+1:ℕ) z) = 0
        simp_rw [bulkModeCross_opposite]; exact integral_zero _ _
    | negSucc l =>
      simp_rw [bulkModeCross_neg]
      rw [integral_conj,bulkModeCross_pos_integral_zero (fun h => hmn (by subst l; rfl)),map_zero]


theorem bulkModeCross_integral (m n : ℤ) :
    (∫ z : ℂ in ball 0 1, bulkModeCross m n z) =
      if m=n then ((2*Real.pi*(m.natAbs:ℝ):ℝ):ℂ) else 0 := by
  classical
  split_ifs with h
  · subst n; exact bulkModeCross_self_integral m
  · exact bulkModeCross_integral_zero h
end StrictHotSpots.Douglas
end DiskModeGramCombinedLayer

section DouglasPolynomialCombinedLayer
open Set MeasureTheory Metric AddCircle
open scoped ComplexConjugate
namespace StrictHotSpots.Douglas

def harmonicPolynomial (S : Finset ℤ) (a : ℤ → ℂ) (z : ℂ) : ℂ :=
  ∑ m ∈ S, a m * harmonicMode m z

lemma harmonicMode_differentiable (m : ℤ) : Differentiable ℝ (harmonicMode m) := by
  cases m with
  | ofNat n => exact differentiable_pow n
  | negSucc n =>
    exact Complex.conjCLE.toContinuousLinearMap.differentiable.comp (differentiable_pow (n+1))

lemma harmonicPolynomial_deriv (S : Finset ℤ) (a : ℤ → ℂ) (z e : ℂ) :
    fderiv ℝ (harmonicPolynomial S a) z e =
      ∑ m ∈ S, a m * fderiv ℝ (harmonicMode m) z e := by
  have h := HasFDerivAt.fun_sum (u:=S) (fun m _ =>
    ((harmonicMode_differentiable m z).hasFDerivAt.const_mul (a m)))
  have he := congrArg (fun L : ℂ →L[ℝ] ℂ => L e) h.fderiv
  change fderiv ℝ (fun y => ∑ i ∈ S, a i * harmonicMode i y) z e = _
  simpa using he

lemma harmonicPolynomial_boundary {T : ℝ} (S : Finset ℤ) (a : ℤ → ℂ) (x : AddCircle T) :
    harmonicPolynomial S a x.toCircle = boundaryPolynomial S a x := by
  simp only [harmonicPolynomial,boundaryPolynomial,harmonicMode_boundary]

lemma harmonicPolynomial_sq (S : Finset ℤ) (a : ℤ → ℂ) (z : ℂ) :
    ((‖fderiv ℝ (harmonicPolynomial S a) z 1‖^2 +
       ‖fderiv ℝ (harmonicPolynomial S a) z Complex.I‖^2 : ℝ):ℂ) =
      ∑ m ∈ S, ∑ n ∈ S, (a m*conj (a n))*bulkModeCross m n z := by
  simp only [Complex.ofReal_add,← Complex.normSq_eq_norm_sq,← Complex.mul_conj,
    harmonicPolynomial_deriv,map_sum,Finset.sum_mul,Finset.mul_sum,map_mul]
  rw [← Finset.sum_add_distrib,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [bulkModeCross]
  ring

lemma harmonicPolynomial_energy (S : Finset ℤ) (a : ℤ → ℂ) :
    (∫ z : ℂ in ball 0 1, ‖fderiv ℝ (harmonicPolynomial S a) z 1‖^2 +
        ‖fderiv ℝ (harmonicPolynomial S a) z Complex.I‖^2) =
      2*Real.pi * ∑ m ∈ S, (m.natAbs:ℝ)*‖a m‖^2 := by
  classical
  have hi (m n : ℤ) : IntegrableOn (fun z : ℂ =>
      (a m*conj (a n))*bulkModeCross m n z) (ball 0 1) :=
    (bulkModeCross_integrable m n).const_mul _
  have he := funext (harmonicPolynomial_sq S a)
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal,he]
  rw [integral_finsetSum S (fun m _ => integrable_finsetSum S (fun n _ => hi m n))]
  simp_rw [integral_finsetSum S (fun n _ => hi _ n),integral_const_mul,
    bulkModeCross_integral]
  have hs : (∑ m ∈ S, ∑ n ∈ S,
      (a m*conj (a n))*(if m=n then ((2*Real.pi*(m.natAbs:ℝ):ℝ):ℂ) else 0)) =
      ∑ m ∈ S, (a m*conj (a m))*((2*Real.pi*(m.natAbs:ℝ):ℝ):ℂ) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.sum_eq_single m]
    · simp
    · intro n _ hnm
      simp [Ne.symm hnm]
    · exact fun h => (h hm).elim
  rw [hs]
  simp only [Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.ofReal_mul,
    Complex.ofReal_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩


theorem douglas_polynomial (S : Finset ℤ) (a : ℤ → ℂ) :
    (∫ z : ℂ in ball 0 1, ‖fderiv ℝ (harmonicPolynomial S a) z 1‖^2 +
        ‖fderiv ℝ (harmonicPolynomial S a) z Complex.I‖^2) =
    (1/(2*Real.pi))*boundaryEnergy (boundaryPolynomial (T:=2*Real.pi) S a) := by
  rw [harmonicPolynomial_energy,boundaryPolynomial_energy]
  field_simp

end StrictHotSpots.Douglas
end DouglasPolynomialCombinedLayer

section DouglasSeriesBoundsCombinedLayer
open Set MeasureTheory Metric Filter
open scoped ComplexConjugate
namespace StrictHotSpots.Douglas

lemma harmonicMode_norm_le_one (m : ℤ) {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖harmonicMode m z‖ ≤ 1 := by
  cases m with
  | ofNat n =>
    change ‖z^n‖ ≤ 1
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg z) hz
  | negSucc n =>
    change ‖conj (z^(n+1))‖ ≤ 1
    rw [Complex.norm_conj,norm_pow]
    exact pow_le_one₀ (norm_nonneg z) hz

lemma harmonicMode_deriv_apply_bound (m : ℤ) {z : ℂ} (hz : ‖z‖ ≤ 1) (e : ℂ) :
    ‖fderiv ℝ (harmonicMode m) z e‖ ≤ (m.natAbs:ℝ)*‖e‖ := by
  have hp (n : ℕ) : ‖e*((n+1:ℕ)*z^n)‖ ≤ ((n+1:ℕ):ℝ)*‖e‖ := by
    rw [norm_mul,norm_mul,Complex.norm_natCast,norm_pow]
    have h := mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg z) hz (n:=n))
      (mul_nonneg (norm_nonneg e) (Nat.cast_nonneg (n+1) : (0:ℝ) ≤ (n+1:ℕ)))
    calc
      ‖e‖ * (((n+1:ℕ):ℝ) * ‖z‖^n) = (‖e‖ * ((n+1:ℕ):ℝ)) * ‖z‖^n := by ring
      _ ≤ (‖e‖ * ((n+1:ℕ):ℝ)) * 1 := h
      _ = ((n+1:ℕ):ℝ)*‖e‖ := by ring
  cases m with
  | ofNat n =>
    cases n with
    | zero =>
      change ‖fderiv ℝ (fun _ : ℂ => (1:ℂ)) z e‖ ≤ _
      simp
    | succ n =>
      change ‖fderiv ℝ (fun w : ℂ => w^(n+1)) z e‖ ≤ ((n+1:ℕ):ℝ)*‖e‖
      rw [fderiv_pow_mode]
      exact hp n
  | negSucc n =>
    change ‖fderiv ℝ (fun w : ℂ => conj (w^(n+1))) z e‖ ≤ ((n+1:ℕ):ℝ)*‖e‖
    rw [fderiv_conj_mode,Complex.norm_conj]
    exact hp n

lemma harmonicMode_deriv_bound (m : ℤ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖fderiv ℝ (harmonicMode m) z‖ ≤ (m.natAbs:ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact harmonicMode_deriv_apply_bound m hz



def harmonicSeries (a : ℤ → ℂ) (z : ℂ) : ℂ := ∑' m : ℤ, a m*harmonicMode m z

lemma harmonicSeries_summable {a : ℤ → ℂ} (ha : Summable (fun m => ‖a m‖))
    {z : ℂ} (hz : ‖z‖ ≤ 1) : Summable (fun m => a m*harmonicMode m z) := by
  apply Summable.of_norm_bounded ha
  intro m
  rw [norm_mul]
  simpa using mul_le_mul_of_nonneg_left (harmonicMode_norm_le_one m hz) (norm_nonneg (a m))

lemma harmonicSeries_deriv_summable {a : ℤ → ℂ}
    (ha : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable (fun m => a m • fderiv ℝ (harmonicMode m) z) := by
  apply Summable.of_norm_bounded ha
  intro m
  rw [norm_smul]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (harmonicMode_deriv_bound m hz) (norm_nonneg (a m))

end StrictHotSpots.Douglas
end DouglasSeriesBoundsCombinedLayer

section DouglasSeriesDerivCombinedLayer
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ComplexConjugate
namespace StrictHotSpots.Douglas

def firstMoment (a : ℤ → ℂ) : ℝ := ∑' m : ℤ, (m.natAbs:ℝ)*‖a m‖
lemma firstMoment_nonneg (a : ℤ → ℂ) : 0 ≤ firstMoment a :=
  tsum_nonneg (fun _m => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))

lemma harmonicSeries_hasFDerivAt {a : ℤ → ℂ}
    (h0 : Summable (fun m => ‖a m‖))
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖))
    {z : ℂ} (hz : z ∈ ball 0 1) :
    HasFDerivAt (harmonicSeries a) (∑' m : ℤ, a m • fderiv ℝ (harmonicMode m) z) z := by
  apply hasFDerivAt_tsum_of_isPreconnected (s:=ball (0:ℂ) 1) h1 isOpen_ball
    (convex_ball (0:ℂ) 1).isPreconnected
    (fun m w _ => (harmonicMode_differentiable m w).hasFDerivAt.const_mul (a m))
  · intro m w hw
    rw [norm_smul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (harmonicMode_deriv_bound m (mem_ball_zero_iff.mp hw).le) (norm_nonneg (a m))
  · exact mem_ball_self (by norm_num)
  · exact harmonicSeries_summable h0 (z:=0) (by simp)
  · exact hz

lemma harmonicPolynomial_deriv_bound {a : ℤ → ℂ}
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖))
    (S : Finset ℤ) {z : ℂ} (hz : ‖z‖ ≤ 1) (e : ℂ) :
    ‖fderiv ℝ (harmonicPolynomial S a) z e‖ ≤ firstMoment a * ‖e‖ := by
  rw [harmonicPolynomial_deriv]
  calc
    _ ≤ ∑ m ∈ S, ‖a m * fderiv ℝ (harmonicMode m) z e‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ S, ((m.natAbs:ℝ)*‖a m‖)*‖e‖ := by
      apply Finset.sum_le_sum
      intro m _
      rw [norm_mul]
      convert mul_le_mul_of_nonneg_left (harmonicMode_deriv_apply_bound m hz e)
        (norm_nonneg (a m)) using 1; ring
    _ = (∑ m ∈ S, (m.natAbs:ℝ)*‖a m‖)*‖e‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ firstMoment a * ‖e‖ := mul_le_mul_of_nonneg_right
      (h1.sum_le_tsum S (fun m _ => by positivity)) (norm_nonneg _)

lemma harmonicMode_deriv_continuous (m : ℤ) (e : ℂ) :
    Continuous (fun z => fderiv ℝ (harmonicMode m) z e) := by
  cases m with
  | ofNat n =>
    cases n with
    | zero =>
      change Continuous (fun z : ℂ => fderiv ℝ (fun _ : ℂ => (1:ℂ)) z e)
      simpa using (continuous_const : Continuous (fun _ : ℂ => (0:ℂ)))
    | succ n =>
      change Continuous (fun z : ℂ => fderiv ℝ (fun w : ℂ => w^(n+1)) z e)
      simp_rw [fderiv_pow_mode]
      fun_prop
  | negSucc n =>
    change Continuous (fun z : ℂ => fderiv ℝ (fun w : ℂ => conj (w^(n+1))) z e)
    simp_rw [fderiv_conj_mode]
    fun_prop

lemma harmonicPolynomial_deriv_continuous (S : Finset ℤ) (a : ℤ → ℂ) (e : ℂ) :
    Continuous (fun z => fderiv ℝ (harmonicPolynomial S a) z e) := by
  simp_rw [harmonicPolynomial_deriv]
  exact continuous_finsetSum _ (fun m _ => continuous_const.mul (harmonicMode_deriv_continuous m e))

lemma harmonicPolynomial_deriv_tendsto {a : ℤ → ℂ}
    (h0 : Summable (fun m => ‖a m‖))
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖))
    {z : ℂ} (hz : z ∈ ball 0 1) (e : ℂ) :
    Tendsto (fun S : Finset ℤ => fderiv ℝ (harmonicPolynomial S a) z e)
      atTop (𝓝 (fderiv ℝ (harmonicSeries a) z e)) := by
  rw [(harmonicSeries_hasFDerivAt h0 h1 hz).fderiv]
  have ht := (harmonicSeries_deriv_summable h1 (mem_ball_zero_iff.mp hz).le).hasSum
  have he := ((ContinuousLinearMap.apply ℝ ℂ e).continuous.tendsto _).comp ht
  change Tendsto (fun S : Finset ℤ => (∑ m ∈ S, a m • fderiv ℝ (harmonicMode m) z) e)
    atTop (𝓝 ((∑' m : ℤ, a m • fderiv ℝ (harmonicMode m) z) e)) at he
  simpa only [sum_apply,smul_apply,smul_eq_mul,harmonicPolynomial_deriv] using he

end StrictHotSpots.Douglas
end DouglasSeriesDerivCombinedLayer

section DouglasSeriesBoundaryCombinedLayer
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ComplexConjugate
namespace StrictHotSpots.Douglas
variable {T : ℝ}

lemma harmonicSeries_boundary_tendsto {a : ℤ → ℂ}
    (h0 : Summable (fun m => ‖a m‖)) (x : AddCircle T) :
    Tendsto (fun S : Finset ℤ => boundaryPolynomial S a x)
      atTop (𝓝 (harmonicSeries a x.toCircle)) := by
  have h := harmonicSeries_summable h0 (z:=(x.toCircle : ℂ)) (Circle.norm_coe x.toCircle).le
  have ht := h.hasSum
  change Tendsto (fun S : Finset ℤ => ∑ m ∈ S, a m * harmonicMode m x.toCircle)
    atTop (𝓝 (harmonicSeries a x.toCircle)) at ht
  simpa only [harmonicMode_boundary,boundaryPolynomial] using ht

lemma boundaryPolynomial_chordLipschitz {a : ℤ → ℂ}
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) (S : Finset ℤ) :
    ChordLipschitz (firstMoment a) (boundaryPolynomial (T:=T) S a) := by
  intro s t
  simp only [boundaryPolynomial,← Finset.sum_sub_distrib,← mul_sub]
  calc
    _ ≤ ∑ m ∈ S, ‖a m*(fourier m s-fourier m t)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ S, ((m.natAbs:ℝ)*‖a m‖)*‖(s.toCircle:ℂ)-(t.toCircle:ℂ)‖ := by
      apply Finset.sum_le_sum
      intro m _
      rw [norm_mul]
      convert mul_le_mul_of_nonneg_left (chordLipschitz_fourier m s t)
        (norm_nonneg (a m)) using 1; ring
    _ = (∑ m ∈ S, (m.natAbs:ℝ)*‖a m‖)*‖(s.toCircle:ℂ)-(t.toCircle:ℂ)‖ :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ firstMoment a * ‖(s.toCircle:ℂ)-(t.toCircle:ℂ)‖ :=
      mul_le_mul_of_nonneg_right (h1.sum_le_tsum S (fun m _ => by positivity)) (norm_nonneg _)

lemma boundaryPolynomial_continuous (S : Finset ℤ) (a : ℤ → ℂ) :
    Continuous (boundaryPolynomial (T:=T) S a) :=
  continuous_finsetSum _ (fun m _ => continuous_const.mul (fourier m).continuous)

variable [hT : Fact (0 < T)]
theorem boundaryEnergy_tendsto_filter {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {K : ℝ} (hK : 0 ≤ K) {h : AddCircle T → ℂ} {f : ι → AddCircle T → ℂ}
    (hc : ∀ i, Continuous (f i)) (hf : ∀ i, ChordLipschitz K (f i))
    (hl : ∀ s, Tendsto (fun i => f i s) l (𝓝 (h s))) :
    Tendsto (fun i => boundaryEnergy (f i)) l (𝓝 (boundaryEnergy h)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : AddCircle T × AddCircle T => K^2)
  · exact Eventually.of_forall fun i =>
      ((measurable_boundaryDifference (hc i)).norm.pow_const 2).aestronglyMeasurable
  · exact Eventually.of_forall fun i => ae_of_all _ fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (boundaryDifference_bound hK (hf i) p) 2
  · exact integrable_const _
  · exact ae_of_all _ fun p => (((hl p.1).sub (hl p.2)).div_const _).norm.pow 2

lemma harmonicSeries_boundaryEnergy_tendsto {a : ℤ → ℂ}
    (h0 : Summable (fun m => ‖a m‖))
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) :
    Tendsto (fun S : Finset ℤ => boundaryEnergy (boundaryPolynomial (T:=T) S a)) atTop
      (𝓝 (boundaryEnergy (fun x : AddCircle T => harmonicSeries a x.toCircle))) :=
  boundaryEnergy_tendsto_filter (firstMoment_nonneg a)
    (fun S => boundaryPolynomial_continuous S a) (boundaryPolynomial_chordLipschitz h1)
    (harmonicSeries_boundary_tendsto h0)

end StrictHotSpots.Douglas
end DouglasSeriesBoundaryCombinedLayer

section DouglasSeriesEnergyCombinedLayer
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ComplexConjugate
namespace StrictHotSpots.Douglas

def diskEnergy (f : ℂ → ℂ) : ℝ :=
  ∫ z : ℂ in ball 0 1, ‖fderiv ℝ f z 1‖^2 + ‖fderiv ℝ f z Complex.I‖^2

lemma harmonicSeries_diskEnergy_tendsto {a : ℤ → ℂ}
    (h0 : Summable (fun m => ‖a m‖))
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) :
    Tendsto (fun S : Finset ℤ => diskEnergy (harmonicPolynomial S a)) atTop
      (𝓝 (diskEnergy (harmonicSeries a))) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℂ => 2*(firstMoment a)^2)
  · exact Eventually.of_forall fun S =>
      (((harmonicPolynomial_deriv_continuous S a 1).norm.pow 2).add
        ((harmonicPolynomial_deriv_continuous S a Complex.I).norm.pow 2)).aestronglyMeasurable
  · exact Eventually.of_forall fun S =>
      (ae_restrict_mem measurableSet_ball).mono fun z hz => by
        have ha := harmonicPolynomial_deriv_bound h1 S (mem_ball_zero_iff.mp hz).le 1
        have hb := harmonicPolynomial_deriv_bound h1 S (mem_ball_zero_iff.mp hz).le Complex.I
        rw [norm_one,mul_one] at ha
        rw [Complex.norm_I,mul_one] at hb
        rw [Real.norm_eq_abs,abs_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))]
        have hA := pow_le_pow_left₀ (norm_nonneg _) ha 2
        have hB := pow_le_pow_left₀ (norm_nonneg _) hb 2
        linarith
  · exact integrableOn_const
  · exact (ae_restrict_mem measurableSet_ball).mono fun z hz =>
      ((harmonicPolynomial_deriv_tendsto h0 h1 hz 1).norm.pow 2).add
        ((harmonicPolynomial_deriv_tendsto h0 h1 hz Complex.I).norm.pow 2)

local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩



theorem douglas_series {a : ℤ → ℂ}
    (h0 : Summable (fun m => ‖a m‖))
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) :
    diskEnergy (harmonicSeries a) = (1/(2*Real.pi))*
      boundaryEnergy (fun x : AddCircle (2*Real.pi) => harmonicSeries a x.toCircle) := by
  have hb := (harmonicSeries_boundaryEnergy_tendsto (T:=2*Real.pi) h0 h1).const_mul
    (1/(2*Real.pi))
  have he : (fun S : Finset ℤ => (1/(2*Real.pi))*
      boundaryEnergy (boundaryPolynomial (T:=2*Real.pi) S a)) =
      fun S => diskEnergy (harmonicPolynomial S a) := by
    funext S
    exact (douglas_polynomial S a).symm
  rw [he] at hb
  exact tendsto_nhds_unique (harmonicSeries_diskEnergy_tendsto h0 h1) hb

end StrictHotSpots.Douglas
end DouglasSeriesEnergyCombinedLayer

section DouglasSeriesPoissonCombinedLayer
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ComplexConjugate
namespace StrictHotSpots.Douglas

lemma poissonKernel_continuousOn_sphere {z : ℂ} (hz : z ∈ ball 0 1) :
    ContinuousOn (poissonKernel 0 z) (sphere 0 1) := by
  unfold poissonKernel
  refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
  intro w hw
  simp only [sub_zero]
  apply pow_ne_zero
  apply norm_ne_zero_iff.mpr
  apply sub_ne_zero.mpr
  intro he
  have hw' : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hw
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  rw [he] at hw'
  linarith

lemma harmonicPolynomial_continuous (S : Finset ℤ) (a : ℤ → ℂ) :
    Continuous (harmonicPolynomial S a) :=
  continuous_finsetSum _ (fun m _ => continuous_const.mul (harmonicMode_continuous m))

lemma harmonicPolynomial_poisson (S : Finset ℤ) (a : ℤ → ℂ)
    {z : ℂ} (hz : z ∈ ball 0 1) :
    Real.circleAverage (poissonKernel 0 z • harmonicPolynomial S a) 0 1 =
      harmonicPolynomial S a z := by
  have hk := poissonKernel_continuousOn_sphere hz
  have he : poissonKernel 0 z • harmonicPolynomial S a =
      fun w => ∑ m ∈ S, a m • (poissonKernel 0 z w • harmonicMode m w) := by
    funext w
    change poissonKernel 0 z w • (∑ m ∈ S, a m * harmonicMode m w) = _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro m _
    change poissonKernel 0 z w • (a m • harmonicMode m w) = _
    exact smul_comm (poissonKernel 0 z w) (a m) (harmonicMode m w)
  rw [he,Real.circleAverage_fun_sum]
  · change (∑ m ∈ S, Real.circleAverage (fun w => a m • (poissonKernel 0 z w • harmonicMode m w)) 0 1) = _
    simp only [Real.circleAverage_fun_smul]
    change (∑ m ∈ S, a m • Real.circleAverage (poissonKernel 0 z • harmonicMode m) 0 1) = _
    simp only [harmonicMode_poisson _ hz,smul_eq_mul,harmonicPolynomial]
  · intro m _
    exact ((hk.smul (harmonicMode_continuous m).continuousOn).circleIntegrable
      (by norm_num)).smul (a m)

lemma harmonicPolynomial_bound {a : ℤ → ℂ} (h0 : Summable (fun m => ‖a m‖))
    (S : Finset ℤ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖harmonicPolynomial S a z‖ ≤ ∑' m : ℤ, ‖a m‖ := by
  calc
    _ ≤ ∑ m ∈ S, ‖a m*harmonicMode m z‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ S, ‖a m‖ := by
      apply Finset.sum_le_sum
      intro m _
      rw [norm_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (harmonicMode_norm_le_one m hz) (norm_nonneg (a m))
    _ ≤ _ := h0.sum_le_tsum S (fun m _ => norm_nonneg (a m))

lemma harmonicSeries_poisson_tendsto {a : ℤ → ℂ} (h0 : Summable (fun m => ‖a m‖))
    {z : ℂ} (hz : z ∈ ball 0 1) :
    Tendsto (fun S : Finset ℤ => Real.circleAverage
      (poissonKernel 0 z • harmonicPolynomial S a) 0 1) atTop
      (𝓝 (Real.circleAverage (poissonKernel 0 z • harmonicSeries a) 0 1)) := by
  have hk := poissonKernel_continuousOn_sphere hz
  obtain ⟨C,hC⟩ := (isCompact_sphere (0:ℂ) 1).exists_bound_of_continuousOn hk
  have hmap (t : ℝ) : circleMap (0:ℂ) 1 t ∈ sphere 0 1 := by
    exact circleMap_mem_sphere (0:ℂ) (by norm_num) t
  have hkc : Continuous (fun t : ℝ => poissonKernel 0 z (circleMap 0 1 t)) :=
    hk.comp_continuous (continuous_circleMap 0 1) hmap
  apply Filter.Tendsto.smul tendsto_const_nhds
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => C*(∑' m : ℤ, ‖a m‖))
  · exact Eventually.of_forall fun S =>
      (hkc.smul ((harmonicPolynomial_continuous S a).comp (continuous_circleMap 0 1))).aestronglyMeasurable
  · exact Eventually.of_forall fun S => ae_of_all _ fun t _ => by
      rw [Pi.smul_apply',norm_smul]
      exact mul_le_mul (hC _ (hmap t))
        (harmonicPolynomial_bound h0 S (mem_sphere_zero_iff_norm.mp (hmap t)).le)
        (norm_nonneg _) (le_trans (norm_nonneg _) (hC _ (hmap t)))
  · exact intervalIntegrable_const
  · refine ae_of_all _ fun t _ => ?_
    change Tendsto (fun S : Finset ℤ => poissonKernel 0 z (circleMap 0 1 t) •
      (∑ m ∈ S, a m*harmonicMode m (circleMap 0 1 t))) atTop
      (𝓝 (poissonKernel 0 z (circleMap 0 1 t) • ∑' m : ℤ, a m*harmonicMode m (circleMap 0 1 t)))
    exact tendsto_const_nhds.smul
      (harmonicSeries_summable h0 (mem_sphere_zero_iff_norm.mp (hmap t)).le).hasSum



theorem harmonicSeries_poisson {a : ℤ → ℂ} (h0 : Summable (fun m => ‖a m‖))
    {z : ℂ} (hz : z ∈ ball 0 1) :
    Real.circleAverage (poissonKernel 0 z • harmonicSeries a) 0 1 = harmonicSeries a z := by
  have ht := harmonicSeries_poisson_tendsto h0 hz
  simp only [harmonicPolynomial_poisson _ _ hz] at ht
  exact tendsto_nhds_unique ht (harmonicSeries_summable h0 (mem_ball_zero_iff.mp hz).le).hasSum

end StrictHotSpots.Douglas
end DouglasSeriesPoissonCombinedLayer

section FourierSmoothMomentCombinedLayer
open Set MeasureTheory AddCircle
open scoped ComplexConjugate
namespace StrictHotSpots.Douglas
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma norm_fourierCoeff_le (f : C(AddCircle τ, ℂ)) (m : ℤ) :
    ‖fourierCoeff f m‖ ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const (μ:=haarAddCircle) (C:=‖f‖)
    (f:=fun x : AddCircle τ => fourier (-m) x • f x) (ae_of_all _ fun x => by
    rw [norm_smul]
    have hf : ‖fourier (T:=τ) (-m) x‖ = 1 := by
      rw [fourier_apply,Circle.norm_coe]
    rw [hf,one_mul]
    exact ContinuousMap.norm_coe_le_norm f x)
  simpa only [fourierCoeff,probReal_univ,mul_one] using h

lemma fourierCoeffOn_coe (f : C(AddCircle τ, ℂ)) (m : ℤ) :
    fourierCoeffOn (a:=0) (b:=τ) (by positivity) (fun t : ℝ => f t) m =
      fourierCoeff f m := by
  rw [fourierCoeffOn_eq_integral,fourierCoeff_eq_intervalIntegral _ _ 0]
  simp_rw [fourier_coe_apply]
  simp only [sub_zero,zero_add]

lemma fourierCoeff_derivative (f g : C(AddCircle τ, ℂ))
    (hfg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f t) (g t) t)
    {m : ℤ} (hm : m ≠ 0) :
    ((m:ℂ)*Complex.I)*fourierCoeff f m = fourierCoeff g m := by
  have h := fourierCoeffOn_of_hasDerivAt (a:=0) (b:=τ) (by positivity) hm
    (fun t _ => hfg t) ((g.continuous.comp (AddCircle.continuous_mk' τ)).intervalIntegrable _ _)
  rw [fourierCoeffOn_coe f m,fourierCoeffOn_coe g m] at h
  have he : f ((τ:ℝ):AddCircle τ) = f (0:AddCircle τ) := by rw [AddCircle.coe_period]
  simp only [he] at h
  rw [h]
  have hm' : (m:ℂ) ≠ 0 := Int.cast_ne_zero.mpr hm
  push_cast
  field_simp [hm',Real.pi_ne_zero]
  ring

lemma norm_fourierCoeff_derivative (f g : C(AddCircle τ, ℂ))
    (hfg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f t) (g t) t)
    {m : ℤ} (hm : m ≠ 0) :
    (m.natAbs:ℝ)*‖fourierCoeff f m‖ = ‖fourierCoeff g m‖ := by
  have h := congrArg norm (fourierCoeff_derivative f g hfg hm)
  have ha : (m.natAbs:ℝ) = |(m:ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
  simpa only [norm_mul,Complex.norm_intCast,Complex.norm_I,mul_one,ha] using h


lemma firstMoment_fourierCoeff_bound (f0 f1 f2 f3 : C(AddCircle τ, ℂ))
    (h01 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f0 t) (f1 t) t)
    (h12 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f1 t) (f2 t) t)
    (h23 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f2 t) (f3 t) t) (m : ℤ) :
    (m.natAbs:ℝ)*‖fourierCoeff f0 m‖ ≤ ‖f3‖*(1/(m:ℝ)^2) := by
  by_cases hm : m=0
  · subst m; simp
  have h0 := norm_fourierCoeff_derivative f0 f1 h01 hm
  have h1 := norm_fourierCoeff_derivative f1 f2 h12 hm
  have h2 := norm_fourierCoeff_derivative f2 f3 h23 hm
  have hm' : (m:ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  rw [mul_one_div]
  apply (le_div_iff₀ (sq_pos_of_ne_zero hm')).2
  calc
    _ = (m.natAbs:ℝ)*((m.natAbs:ℝ)*((m.natAbs:ℝ)*‖fourierCoeff f0 m‖)) := by
      have ha : (m.natAbs:ℝ) = |(m:ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
      rw [ha]
      calc
        _ = |(m:ℝ)| * ‖fourierCoeff f0 m‖ * |(m:ℝ)|^2 := by rw [sq_abs]
        _ = _ := by ring
    _ = ‖fourierCoeff f3 m‖ := by rw [h0,h1,h2]
    _ ≤ ‖f3‖ := norm_fourierCoeff_le f3 m

lemma summable_firstMoment_fourierCoeff (f0 f1 f2 f3 : C(AddCircle τ, ℂ))
    (h01 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f0 t) (f1 t) t)
    (h12 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f1 t) (f2 t) t)
    (h23 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f2 t) (f3 t) t) :
    Summable (fun m : ℤ => (m.natAbs:ℝ)*‖fourierCoeff f0 m‖) := by
  have hp : Summable (fun m : ℤ => (1:ℝ)/(m:ℝ)^2) := Real.summable_one_div_int_pow.mpr (by norm_num)
  exact Summable.of_nonneg_of_le (fun m => by positivity)
    (firstMoment_fourierCoeff_bound f0 f1 f2 f3 h01 h12 h23) (hp.mul_left ‖f3‖)

end StrictHotSpots.Douglas
end FourierSmoothMomentCombinedLayer

section DouglasSmoothDataCombinedLayer
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ComplexConjugate
namespace StrictHotSpots.Douglas
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma summable_norm_of_firstMoment {a : ℤ → ℂ}
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) : Summable (fun m => ‖a m‖) := by
  apply h1.of_norm_bounded_eventually
  filter_upwards [eventually_cofinite_ne (0:ℤ)] with m hm
  rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  have hm' : 1 ≤ (m.natAbs:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hm)
  exact le_mul_of_one_le_left (norm_nonneg _) hm'

lemma harmonicSeries_fourier_boundary (f : C(AddCircle τ, ℂ))
    (h : Summable (fun m => ‖fourierCoeff f m‖)) (s : AddCircle τ) :
    harmonicSeries (fourierCoeff f) s.toCircle = f s := by
  have hf := has_pointwise_sum_fourier_series_of_summable h.of_norm s
  simpa only [harmonicSeries,harmonicMode_boundary,smul_eq_mul] using hf.tsum_eq

lemma circleMap_eq_toCircle (t : ℝ) :
    circleMap (0:ℂ) 1 t = (AddCircle.toCircle (t:AddCircle τ) : ℂ) := by
  rw [toCircle_apply_mk,Circle.coe_exp]
  simp only [circleMap,Complex.ofReal_one,one_mul,zero_add]
  congr 1
  push_cast
  field_simp


def poissonExtension (f : AddCircle τ → ℂ) (z : ℂ) : ℂ :=
  τ⁻¹ • ∫ t in 0..τ, poissonKernel 0 z (circleMap 0 1 t) • f t

lemma poissonExtension_eq_harmonicSeries (f : C(AddCircle τ, ℂ))
    (h : Summable (fun m => ‖fourierCoeff f m‖)) {z : ℂ} (hz : z ∈ ball 0 1) :
    poissonExtension f z = harmonicSeries (fourierCoeff f) z := by
  rw [← harmonicSeries_poisson h hz]
  unfold poissonExtension Real.circleAverage
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [Pi.smul_apply',circleMap_eq_toCircle,harmonicSeries_fourier_boundary f h]



theorem douglas_C3 (f0 f1 f2 f3 : C(AddCircle τ, ℂ))
    (h01 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f0 t) (f1 t) t)
    (h12 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f1 t) (f2 t) t)
    (h23 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f2 t) (f3 t) t) :
    diskEnergy (poissonExtension f0) = (1/τ)*boundaryEnergy f0 := by
  have h1 := summable_firstMoment_fourierCoeff f0 f1 f2 f3 h01 h12 h23
  have h0 := summable_norm_of_firstMoment h1
  have he : EqOn (poissonExtension f0) (harmonicSeries (fourierCoeff f0)) (ball 0 1) :=
    fun z hz => poissonExtension_eq_harmonicSeries f0 h0 hz
  have hd (z : ℂ) (hz : z ∈ ball 0 1) :
      fderiv ℝ (poissonExtension f0) z = fderiv ℝ (harmonicSeries (fourierCoeff f0)) z :=
    (he.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz)).fderiv_eq
  have hE : diskEnergy (poissonExtension f0) = diskEnergy (harmonicSeries (fourierCoeff f0)) := by
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    dsimp only
    rw [hd z hz]
  rw [hE,douglas_series h0 h1]
  have hb : (fun s : AddCircle τ => harmonicSeries (fourierCoeff f0) s.toCircle) = f0 :=
    funext (harmonicSeries_fourier_boundary f0 h0)
  rw [hb]

end StrictHotSpots.Douglas
end DouglasSmoothDataCombinedLayer

section DouglasClosureCombinedLayer
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ComplexConjugate ContDiff
namespace StrictHotSpots.Douglas

lemma harmonicMode_contDiff (m : ℤ) : ContDiff ℝ ∞ (harmonicMode m) := by
  cases m with
  | ofNat n => exact contDiff_id.pow n
  | negSucc n => exact Complex.conjCLE.contDiff.comp (contDiff_id.pow (n+1))

lemma harmonicSeries_continuousOn {a : ℤ → ℂ} (ha : Summable (fun m => ‖a m‖)) :
    ContinuousOn (harmonicSeries a) (closedBall 0 1) := by
  apply continuousOn_tsum (fun m =>
    (continuous_const.mul (harmonicMode_continuous m)).continuousOn) ha
  intro m z hz
  dsimp only [Pi.mul_apply]
  rw [norm_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (harmonicMode_norm_le_one m (mem_closedBall_zero_iff.mp hz)) (norm_nonneg (a m))

def harmonicD (a : ℤ → ℂ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  ∑' m : ℤ, a m • fderiv ℝ (harmonicMode m) z

lemma harmonicD_continuousOn {a : ℤ → ℂ}
    (ha : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) :
    ContinuousOn (harmonicD a) (closedBall 0 1) := by
  unfold harmonicD
  apply continuousOn_tsum (f := fun m z => a m • fderiv ℝ (harmonicMode m) z)
    (fun m => (Continuous.const_smul ((harmonicMode_contDiff m).continuous_fderiv (by simp))
      (a m)).continuousOn) ha
  intro m z hz
  rw [norm_smul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (harmonicMode_deriv_bound m (mem_closedBall_zero_iff.mp hz)) (norm_nonneg (a m))

lemma harmonicD_bound {a : ℤ → ℂ}
    (ha : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖harmonicD a z‖ ≤ firstMoment a := by
  apply (norm_tsum_le_tsum_norm (harmonicSeries_deriv_summable ha hz).norm).trans
  exact Summable.tsum_le_tsum (fun m => by
    rw [norm_smul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (harmonicMode_deriv_bound m hz) (norm_nonneg (a m)))
    (harmonicSeries_deriv_summable ha hz).norm ha

end StrictHotSpots.Douglas
end DouglasClosureCombinedLayer


end

end DouglasLipschitzBase

end OAI
