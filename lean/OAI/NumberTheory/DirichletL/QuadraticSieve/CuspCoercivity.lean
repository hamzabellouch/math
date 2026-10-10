import OAI.NumberTheory.DirichletL.CubicSieve.PrincipalDensity

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum

theorem unrestrictedPrincipalDensity_twisted_squarefree {n : Type} [Fintype n] [DecidableEq n]
    (cols : n → Ideal O) (a : n → ℂ) (q : Ideal O) (M K : ℝ) (hM : 0 ≤ M)
    (hcols : ∀ j, Admissible (cols j)) :
    unrestrictedPrincipalDensity (fun I : squarefreeIdealRange K => I.val) cols cols
      (fun j => a j*quadraticRow (cols j) (idealGenerator q))
      (fun j => a j*quadraticRow (cols j) (idealGenerator q)) (M/(Ideal.absNorm q:ℝ)) =
      (Real.sqrt M : ℂ)*densityPairSum cols a
        (fun I J => normalizedPairPartial I J K*normalizedIdealPair I J q) := by
  rw [unrestrictedPrincipalDensity_squarefree _ _ _ _ (by positivity),Real.sqrt_div hM]
  simp only [densityPairSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : IsCoprime (cols j) (cols k)
  · simp only [hc,ite_true,star_mul,canonical_quadraticRow_star _ (hcols j),
      normalizedIdealPair,unrestrictedPairCharacter,Complex.ofReal_div]
    ring
  · simp only [hc,ite_false,mul_zero]

theorem densityPairSum_weighted_sum {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (P : Ideal O → Ideal O → ℂ) (Q : ι → Ideal O → Ideal O → ℂ) :
    (∑ q ∈ S, c q*densityPairSum cols a (fun I J => P I J*Q q I J)) =
      densityPairSum cols a (fun I J => P I J*∑ q ∈ S, c q*Q q I J) := by
  simp only [densityPairSum,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : IsCoprime (cols j) (cols k)
  · simp only [hc,ite_true]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  · simp only [hc,ite_false,mul_zero,Finset.sum_const_zero]

theorem summed_dual_density {n : Type} [Fintype n] [DecidableEq n]
    (cols : n → Ideal O) (a : n → ℂ) (G : Ideal O) (M K : ℝ) (hM : 0 ≤ M)
    (hcols : ∀ j, Admissible (cols j)) :
    (∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
      unrestrictedPrincipalDensity (fun I : squarefreeIdealRange K => I.val) cols cols
        (fun j => a j*quadraticRow (cols j) (idealGenerator q))
        (fun j => a j*quadraticRow (cols j) (idealGenerator q)) (M/(Ideal.absNorm q:ℝ))) =
      (Real.sqrt M : ℂ)*densityPairSum cols a
        (fun I J => normalizedPairPartial I J K*normalizedPairDivisors I J G) := by
  simp_rw [unrestrictedPrincipalDensity_twisted_squarefree cols a _ M K hM hcols]
  calc
    _ = (Real.sqrt M : ℂ)*∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
        densityPairSum cols a (fun I J => normalizedPairPartial I J K*normalizedIdealPair I J q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = _ := by
      rw [densityPairSum_weighted_sum]
      rfl

theorem actual_source_dual_density_cancellation {n : Type} [Fintype n] [DecidableEq n]
    (cols : n → Ideal O) (a : n → ℂ) (G : Ideal O) (hG : G ≠ 0)
    (M K : ℝ) (hM : 0 ≤ M) (hcols : ∀ j, Admissible (cols j))
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (hGc : ∀ j, IsCoprime G (cols j)) (hbad : ∀ P ∈ fixedBadPrimes, P ∣ G) :
    (∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
      unrestrictedPrincipalDensity (fun I : squarefreeIdealRange K => I.val) cols cols
        (fun j => a j*quadraticRow (cols j) (idealGenerator q))
        (fun j => a j*quadraticRow (cols j) (idealGenerator q)) (M/(Ideal.absNorm q:ℝ))) -
      maskedSourceDensity G (fun I : coprimeSquarefreeRange G K => I.val) cols a M =
      (Real.sqrt M : ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K := by
  rw [summed_dual_density cols a G M K hM hcols,
    maskedSourceDensity_coprime_squarefree G hG K M hM cols a hcols hray hGc hbad,
    actualPrincipalDifference_densityColumn cols a G K
      (fun j => (hcols j).1) (fun j => (hGc j).symm)]
  change _ = (Real.sqrt M:ℂ)*(densityPairSum cols a
    (fun I J => normalizedPairPartial I J K*normalizedPairDivisors I J G) -
    primePoolDensity G*densityPairSum cols a (fun I J => normalizedPairCoprimePartial I J G K))
  ring

end CanonicalQuadraticSieve

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

namespace CubicEisenstein

section

lemma cusp_hardy_square_identity (u du : ℂ) (v : ℝ) (hv : v≠0) :
    ‖du‖^2/v-‖u‖^2/v^3=
      ‖du-v⁻¹ • u‖^2/v+
        (2*⟪u,du⟫_ℝ/v^2-2*‖u‖^2/v^3) := by
  rw [norm_sub_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,
    mul_pow,sq_abs,real_inner_comm du u]
  field_simp
  ; ring

lemma cusp_hardy_boundary_hasDerivAt (f : ℝ → ℂ) (v : ℝ)
    (hf : DifferentiableAt ℝ f v) (hv : v≠0) :
    HasDerivAt (fun t => ‖f t‖^2/t^2)
      (2*⟪f v,deriv f v⟫_ℝ/v^2-2*‖f v‖^2/v^3) v := by
  convert hf.hasDerivAt.norm_sq.div ((hasDerivAt_id v).pow 2) (pow_ne_zero 2 hv) using 1
  · rfl
  · dsimp
    field_simp

theorem cusp_hardy_interval_identity (f : ℝ → ℂ) (a b : ℝ)
    (ha : 0<a) (hab : a≤b)
    (hf : ∀t∈Set.Icc a b,DifferentiableAt ℝ f t)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b)) :
    (∫t in a..b,‖deriv f t‖^2/t)-(∫t in a..b,‖f t‖^2/t^3)=
      (∫t in a..b,‖deriv f t-t⁻¹ • f t‖^2/t)+
        (‖f b‖^2/b^2-‖f a‖^2/a^2) := by
  have hfC : ContinuousOn f (Set.Icc a b) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hn : ∀t∈Set.Icc a b,t≠0 := fun t ht => (ha.trans_le ht.1).ne'
  have hiE : IntervalIntegrable (fun t => ‖deriv f t‖^2/t) volume a b :=
    ((hdf.norm.pow 2).div continuousOn_id hn).intervalIntegrable_of_Icc hab
  have hiM : IntervalIntegrable (fun t => ‖f t‖^2/t^3) volume a b :=
    ((hfC.norm.pow 2).div (continuousOn_id.pow 3) (fun t ht => pow_ne_zero 3 (hn t ht))).intervalIntegrable_of_Icc hab
  have hiS : IntervalIntegrable (fun t => ‖deriv f t-t⁻¹ • f t‖^2/t) volume a b :=
    (((hdf.sub ((continuousOn_id.inv₀ hn).smul hfC)).norm.pow 2).div continuousOn_id hn).intervalIntegrable_of_Icc hab
  have hiB : IntervalIntegrable
      (fun t => 2*⟪f t,deriv f t⟫_ℝ/t^2-2*‖f t‖^2/t^3) volume a b :=
    ((((hfC.inner hdf).const_mul 2).div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (hn t ht))).sub
        (((hfC.norm.pow 2).const_mul 2).div (continuousOn_id.pow 3)
          (fun t ht => pow_ne_zero 3 (hn t ht)))).intervalIntegrable_of_Icc hab
  have hB := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (ht : t∈Set.uIcc a b) => cusp_hardy_boundary_hasDerivAt f t
      (hf t (by simpa only [Set.uIcc_of_le hab] using ht))
      (hn t (by simpa only [Set.uIcc_of_le hab] using ht))) hiB
  rw [←intervalIntegral.integral_sub hiE hiM]
  calc
    _ = ∫t in a..b, ‖deriv f t-t⁻¹ • f t‖^2/t+
          (2*⟪f t,deriv f t⟫_ℝ/t^2-2*‖f t‖^2/t^3) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact cusp_hardy_square_identity (f t) (deriv f t) t
        (hn t (by simpa only [Set.uIcc_of_le hab] using ht))
    _ = _ := by rw [intervalIntegral.integral_add hiS hiB,hB]

theorem cusp_hardy_interval (f : ℝ → ℂ) (a b : ℝ)
    (ha : 0<a) (hab : a≤b) (hfa : f a=0)
    (hf : ∀t∈Set.Icc a b,DifferentiableAt ℝ f t)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b)) :
    (∫t in a..b,‖f t‖^2/t^3)≤∫t in a..b,‖deriv f t‖^2/t := by
  have hid := cusp_hardy_interval_identity f a b ha hab hf hdf
  have hsq : 0≤∫t in a..b,‖deriv f t-t⁻¹ • f t‖^2/t := by
    apply intervalIntegral.integral_nonneg hab
    intro t ht
    exact div_nonneg (sq_nonneg _) (ha.trans_le ht.1).le
  have hb : 0≤‖f b‖^2/b^2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  simp only [hfa,norm_zero,zero_pow (by decide : 2≠0),zero_div,sub_zero] at hid
  linarith

theorem cusp_hardy_halfline (f : ℝ → ℂ) (a : ℝ) (ha : 0<a) (hfa : f a=0)
    (hf : ∀t∈Set.Ici a,DifferentiableAt ℝ f t)
    (hdf : ContinuousOn (deriv f) (Set.Ici a))
    (hM : IntegrableOn (fun t => ‖f t‖^2/t^3) (Set.Ioi a) volume)
    (hE : IntegrableOn (fun t => ‖deriv f t‖^2/t) (Set.Ioi a) volume) :
    (∫t in Set.Ioi a,‖f t‖^2/t^3)≤∫t in Set.Ioi a,‖deriv f t‖^2/t := by
  apply le_of_tendsto_of_tendsto
    (intervalIntegral_tendsto_integral_Ioi a hM tendsto_id)
    (intervalIntegral_tendsto_integral_Ioi a hE tendsto_id)
  filter_upwards [eventually_ge_atTop a] with b hab
  exact cusp_hardy_interval f a b ha hab hfa
    (fun t ht => hf t ht.1) (hdf.mono (fun t ht => ht.1))

theorem cusp_hardy_interval_lintegral (f : ℝ → ℂ) (a b : ℝ)
    (ha : 0<a) (hab : a≤b) (hfa : f a=0)
    (hf : ∀t∈Set.Icc a b,DifferentiableAt ℝ f t)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b)) :
    (∫⁻t in Set.Ioc a b,ENNReal.ofReal (‖f t‖^2/t^3))≤
      ∫⁻t in Set.Ioc a b,ENNReal.ofReal (‖deriv f t‖^2/t) := by
  have hfC : ContinuousOn f (Set.Icc a b) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hn : ∀t∈Set.Icc a b,t≠0 := fun t ht => (ha.trans_le ht.1).ne'
  have hiE : IntervalIntegrable (fun t => ‖deriv f t‖^2/t) volume a b :=
    ((hdf.norm.pow 2).div continuousOn_id hn).intervalIntegrable_of_Icc hab
  have hiM : IntervalIntegrable (fun t => ‖f t‖^2/t^3) volume a b :=
    ((hfC.norm.pow 2).div (continuousOn_id.pow 3)
      (fun t ht => pow_ne_zero 3 (hn t ht))).intervalIntegrable_of_Icc hab
  have hEnn : 0≤ᵐ[volume.restrict (Set.Ioc a b)] (fun t => ‖deriv f t‖^2/t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact div_nonneg (sq_nonneg _) (ha.trans ht.1).le
  have hMnn : 0≤ᵐ[volume.restrict (Set.Ioc a b)] (fun t => ‖f t‖^2/t^3) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact div_nonneg (sq_nonneg _) (pow_nonneg (ha.trans ht.1).le 3)
  rw [←ofReal_integral_eq_lintegral_ofReal hiM.1 hMnn,
    ←ofReal_integral_eq_lintegral_ofReal hiE.1 hEnn]
  apply ENNReal.ofReal_le_ofReal
  simpa only [intervalIntegral.integral_of_le hab] using
    cusp_hardy_interval f a b ha hab hfa hf hdf

theorem cusp_hardy_halfline_lintegral (f : ℝ → ℂ) (a : ℝ) (ha : 0<a) (hfa : f a=0)
    (hf : ∀t∈Set.Ici a,DifferentiableAt ℝ f t)
    (hdf : ContinuousOn (deriv f) (Set.Ici a)) :
    (∫⁻t in Set.Ioi a,ENNReal.ofReal (‖f t‖^2/t^3))≤
      ∫⁻t in Set.Ioi a,ENNReal.ofReal (‖deriv f t‖^2/t) := by
  have hcover : (⋃n : ℕ,Set.Ioc a (a+n))=Set.Ioi a := by
    ext t
    constructor
    · rintro ⟨_,⟨n,rfl⟩,ht⟩
      exact ht.1
    · intro ht
      obtain ⟨n,hn⟩ := exists_nat_ge (t-a)
      exact Set.mem_iUnion.mpr ⟨n,ht,by linarith⟩
  have hdir : Directed (· ⊆ ·) (fun n : ℕ => Set.Ioc a (a+n)) := by
    intro m n
    refine ⟨max m n,Set.Ioc_subset_Ioc_right ?_,Set.Ioc_subset_Ioc_right ?_⟩
    · change a+(m:ℝ)≤a+((max m n:ℕ):ℝ)
      have hh : (m:ℝ)≤((max m n:ℕ):ℝ) := by exact_mod_cast le_max_left m n
      linarith
    · change a+(n:ℝ)≤a+((max m n:ℕ):ℝ)
      have hh : (n:ℝ)≤((max m n:ℕ):ℝ) := by exact_mod_cast le_max_right m n
      linarith
  calc
    _ = ⨆n : ℕ,∫⁻t in Set.Ioc a (a+n),ENNReal.ofReal (‖f t‖^2/t^3) := by
      rw [←hcover]
      exact setLIntegral_iUnion_of_directed _ hdir
    _ ≤ _ := by
      apply iSup_le
      intro n
      exact (cusp_hardy_interval_lintegral f a (a+n) ha (le_add_of_nonneg_right (Nat.cast_nonneg n)) hfa
        (fun t ht => hf t ht.1) (hdf.mono (fun t ht => ht.1))).trans
          (lintegral_mono_set Set.Ioc_subset_Ioi_self)

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ENNReal

abbrev CuspChartCoordinates := (ℝ×ℝ)×ℝ

def cuspBaseArea : Measure (ℝ×ℝ) := volume.restrict cuspRectangle
instance cuspBaseArea_sFinite : SFinite cuspBaseArea := by unfold cuspBaseArea; infer_instance

def cuspChartVolume (a : ℝ) : Measure CuspChartCoordinates :=
  (cuspBaseArea.prod (volume.restrict (Set.Ioi a))).withDensity
    (fun q => ENNReal.ofReal ((q.2^3)⁻¹))

abbrev CuspChartL2 (a : ℝ) := Lp ℂ 2 (cuspChartVolume a)

example (a : ℝ) : InnerProductSpace ℂ (CuspChartL2 a) := inferInstance
example (a : ℝ) : CompleteSpace (CuspChartL2 a) := inferInstance

def cuspVerticalDerivative (F : CuspChartCoordinates → ℂ) (q : CuspChartCoordinates) : ℂ :=
  deriv (fun v => F (q.1,v)) q.2

def cuspVerticalVelocity (F : CuspChartCoordinates → ℂ) (q : CuspChartCoordinates) : ℂ :=
  (q.2:ℂ)*cuspVerticalDerivative F q

lemma cusp_weight_mass_identity (u : ℂ) (v : ℝ) (hv : 0<v) :
    ENNReal.ofReal ((v^3)⁻¹) * ENNReal.ofReal (‖u‖^2)=
      ENNReal.ofReal (‖u‖^2/v^3) := by
  rw [←ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

lemma cusp_weight_velocity_identity (u : ℂ) (v : ℝ) (hv : 0<v) :
    ENNReal.ofReal ((v^3)⁻¹) * ENNReal.ofReal (‖(v:ℂ)*u‖^2)=
      ENNReal.ofReal (‖u‖^2/v) := by
  rw [cusp_weight_mass_identity _ _ hv,norm_mul,mul_pow,Complex.norm_real,
    Real.norm_of_nonneg hv.le]
  congr 1
  field_simp

theorem cusp_chart_vertical_coercivity (F : CuspChartCoordinates → ℂ) (a : ℝ)
    (ha : 0<a) (hF : Continuous F) (hD : Continuous (cuspVerticalDerivative F))
    (hFa : ∀z : ℝ×ℝ,F (z,a)=0)
    (hDiff : ∀z : ℝ×ℝ,∀v∈Set.Ici a,DifferentiableAt ℝ (fun t => F (z,t)) v) :
    (∫⁻q,ENNReal.ofReal (‖F q‖^2) ∂cuspChartVolume a)≤
      ∫⁻q,ENNReal.ofReal (‖cuspVerticalVelocity F q‖^2) ∂cuspChartVolume a := by
  have hw : Measurable (fun q : CuspChartCoordinates => ENNReal.ofReal ((q.2^3)⁻¹)) := by
    fun_prop
  have hFm : Measurable (fun q : CuspChartCoordinates => ENNReal.ofReal (‖F q‖^2)) := by fun_prop
  have hVm : Measurable (fun q : CuspChartCoordinates => ENNReal.ofReal (‖cuspVerticalVelocity F q‖^2)) := by
    unfold cuspVerticalVelocity
    fun_prop
  unfold cuspChartVolume
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hFm,
    lintegral_withDensity_eq_lintegral_mul _ hw hVm,
    lintegral_prod _ ((hw.mul hFm).aemeasurable),
    lintegral_prod _ ((hw.mul hVm).aemeasurable)]
  apply lintegral_mono
  intro z
  calc
    _ = ∫⁻v in Set.Ioi a,ENNReal.ofReal (‖F (z,v)‖^2/v^3) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact cusp_weight_mass_identity _ _ (ha.trans hv)
    _ ≤ ∫⁻v in Set.Ioi a,ENNReal.ofReal (‖deriv (fun t => F (z,t)) v‖^2/v) := by
      apply cusp_hardy_halfline_lintegral _ a ha (hFa z) (hDiff z)
      exact (hD.comp (continuous_const.prodMk continuous_id)).continuousOn
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact (cusp_weight_velocity_identity _ _ (ha.trans hv)).symm

theorem cusp_chart_normalized_vertical_coercivity (F : CuspChartCoordinates → ℂ) (a : ℝ)
    (ha : 0<a) (hF : Continuous F) (hD : Continuous (cuspVerticalDerivative F))
    (hFa : ∀z : ℝ×ℝ,F (z,a)=0)
    (hDiff : ∀z : ℝ×ℝ,∀v∈Set.Ici a,DifferentiableAt ℝ (fun t => F (z,t)) v) :
    (1/2:ℝ≥0∞)*(∫⁻q,ENNReal.ofReal (‖F q‖^2) ∂cuspChartVolume a)≤
      (1/2:ℝ≥0∞)*(∫⁻q,ENNReal.ofReal (‖cuspVerticalVelocity F q‖^2) ∂cuspChartVolume a) :=
by
  exact mul_le_mul_of_nonneg_left
    (cusp_chart_vertical_coercivity F a ha hF hD hFa hDiff) (by positivity)

theorem cusp_chart_memLp_of_vertical (F : CuspChartCoordinates → ℂ) (a : ℝ)
    (ha : 0<a) (hF : Continuous F) (hD : Continuous (cuspVerticalDerivative F))
    (hFa : ∀z : ℝ×ℝ,F (z,a)=0)
    (hDiff : ∀z : ℝ×ℝ,∀v∈Set.Ici a,DifferentiableAt ℝ (fun t => F (z,t)) v)
    (hEnergy : MemLp (cuspVerticalVelocity F) 2 (cuspChartVolume a)) :
    MemLp F 2 (cuspChartVolume a) := by
  have hV : Continuous (cuspVerticalVelocity F) := by
    unfold cuspVerticalVelocity
    fun_prop
  have hEi := (memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).mp hEnergy
  have hEfin := (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (fun q => sq_nonneg ‖cuspVerticalVelocity F q‖))).mp hEi.2
  apply (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mpr
  refine ⟨(hF.norm.pow 2).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun q => sq_nonneg ‖F q‖))).mpr
  exact (cusp_chart_vertical_coercivity F a ha hF hD hFa hDiff).trans_lt hEfin

def cuspCoordinateVelocity (F : CuspChartCoordinates → ℂ)
    (q : CuspChartCoordinates) : Fin 3 → ℂ :=
  ![(q.2:ℂ)*deriv (fun x => F ((x,q.1.2),q.2)) q.1.1,
    (q.2:ℂ)*deriv (fun y => F ((q.1.1,y),q.2)) q.1.2,
    cuspVerticalVelocity F q]

def cuspDirichletEnergy (F : CuspChartCoordinates → ℂ) (a : ℝ) : ℝ≥0∞ :=
  ∫⁻q,∑j : Fin 3,ENNReal.ofReal (‖cuspCoordinateVelocity F q j‖^2) ∂cuspChartVolume a

lemma cusp_vertical_energy_le (F : CuspChartCoordinates → ℂ) (a : ℝ) :
    (∫⁻q,ENNReal.ofReal (‖cuspVerticalVelocity F q‖^2) ∂cuspChartVolume a)≤
      cuspDirichletEnergy F a := by
  apply lintegral_mono
  intro q
  change ENNReal.ofReal (‖cuspCoordinateVelocity F q 2‖^2)≤_
  exact Finset.single_le_sum (fun j hj => (zero_le : (0:ℝ≥0∞)≤ENNReal.ofReal (‖cuspCoordinateVelocity F q j‖^2))) (Finset.mem_univ (2:Fin 3))

theorem cusp_chart_dirichlet_coercivity (F : CuspChartCoordinates → ℂ) (a : ℝ)
    (ha : 0<a) (hF : Continuous F) (hD : Continuous (cuspVerticalDerivative F))
    (hFa : ∀z : ℝ×ℝ,F (z,a)=0)
    (hDiff : ∀z : ℝ×ℝ,∀v∈Set.Ici a,DifferentiableAt ℝ (fun t => F (z,t)) v) :
    (∫⁻q,ENNReal.ofReal (‖F q‖^2) ∂cuspChartVolume a)≤cuspDirichletEnergy F a :=
  (cusp_chart_vertical_coercivity F a ha hF hD hFa hDiff).trans (cusp_vertical_energy_le F a)

theorem cusp_chart_memLp_of_energy (F : CuspChartCoordinates → ℂ) (a : ℝ)
    (ha : 0<a) (hF : Continuous F) (hD : Continuous (cuspVerticalDerivative F))
    (hFa : ∀z : ℝ×ℝ,F (z,a)=0)
    (hDiff : ∀z : ℝ×ℝ,∀v∈Set.Ici a,DifferentiableAt ℝ (fun t => F (z,t)) v)
    (hEnergy : cuspDirichletEnergy F a<(∞ : ℝ≥0∞)) : MemLp F 2 (cuspChartVolume a) := by
  apply (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mpr
  refine ⟨(hF.norm.pow 2).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun q => sq_nonneg ‖F q‖))).mpr
  exact (cusp_chart_dirichlet_coercivity F a ha hF hD hFa hDiff).trans_lt hEnergy

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal

lemma cusp_height_volume (a : ℝ) (ha : 0<a) :
    (∫⁻v in Set.Ioi a,ENNReal.ofReal ((v^3)⁻¹))=ENNReal.ofReal (1/(2*a^2)) := by
  have hi : IntegrableOn (fun v : ℝ => (v^3)⁻¹) (Set.Ioi a) volume := by
    simpa only [show (-3:ℝ)=-(3:ℕ) by norm_num,Real.rpow_neg_natCast,zpow_neg,
      zpow_natCast] using (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) ha)
  have hn : 0≤ᵐ[volume.restrict (Set.Ioi a)] (fun v : ℝ => (v^3)⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact inv_nonneg.mpr (pow_nonneg (ha.trans hv).le 3)
  rw [←ofReal_integral_eq_lintegral_ofReal hi hn]
  congr 1
  have he := integral_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) ha
  norm_num only at he
  simp only [show (-3:ℝ)=-(3:ℕ) by norm_num,Real.rpow_neg_natCast,zpow_neg,
    zpow_natCast] at he
  rw [he]
  norm_num [show (-3:ℝ)+1=-2 by norm_num]
  ring

theorem cuspChartVolume_univ (a : ℝ) (ha : 0<a) :
    cuspChartVolume a Set.univ=ENNReal.ofReal (9*Real.sqrt 3/(2*a^2)) := by
  unfold cuspChartVolume
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [lintegral_prod _ (by fun_prop)]
  simp only [cusp_height_volume a ha,lintegral_const]
  rw [cuspBaseArea,Measure.restrict_apply MeasurableSet.univ]
  simp only [Set.univ_inter,cuspRectangle_volume]
  rw [←ENNReal.ofReal_mul (by positivity : (0:ℝ)≤1/(2*a^2))]
  congr 1
  ring

lemma cuspChartVolume_finite (a : ℝ) (ha : 0<a) : IsFiniteMeasure (cuspChartVolume a) :=
  ⟨by rw [cuspChartVolume_univ a ha]; exact ENNReal.ofReal_lt_top⟩

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ENNReal ContDiff

def cuspCoordinateVector : Fin 3 → CuspChartCoordinates := ![((1,0),0),((0,1),0),((0,0),1)]

lemma cuspCoordinateVelocity_eq_fderiv (F : CuspChartCoordinates → ℂ)
    (hF : Differentiable ℝ F) (q : CuspChartCoordinates) (j : Fin 3) :
    cuspCoordinateVelocity F q j=(q.2:ℂ)*fderiv ℝ F q (cuspCoordinateVector j) := by
  fin_cases j
  · have hd := (hF q).hasFDerivAt.comp_hasDerivAt q.1.1
      (((hasDerivAt_id q.1.1).prodMk (hasDerivAt_const q.1.1 q.1.2)).prodMk (hasDerivAt_const q.1.1 q.2))
    exact congrArg (fun u : ℂ => (q.2:ℂ)*u) hd.deriv
  · have hd := (hF q).hasFDerivAt.comp_hasDerivAt q.1.2
      (((hasDerivAt_const q.1.2 q.1.1).prodMk (hasDerivAt_id q.1.2)).prodMk (hasDerivAt_const q.1.2 q.2))
    exact congrArg (fun u : ℂ => (q.2:ℂ)*u) hd.deriv
  · have hd := (hF q).hasFDerivAt.comp_hasDerivAt q.2
      ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))
    exact congrArg (fun u : ℂ => (q.2:ℂ)*u) hd.deriv

lemma cuspCoordinateVelocity_continuous_compact (F : CuspChartCoordinates → ℂ)
    (hF : ContDiff ℝ ∞ F) (hC : HasCompactSupport F) (j : Fin 3) :
    Continuous (fun q => cuspCoordinateVelocity F q j) ∧
      HasCompactSupport (fun q => cuspCoordinateVelocity F q j) := by
  simp_rw [cuspCoordinateVelocity_eq_fderiv F (hF.differentiable (by simp))]
  have hc := hC.fderiv_apply ℝ (cuspCoordinateVector j)
  constructor
  · exact (Complex.continuous_ofReal.comp continuous_snd).mul
      ((hF.continuous_fderiv (by simp)).clm_apply continuous_const)
  · exact HasCompactSupport.mul_left hc

lemma cusp_compact_smooth_memLp (F : CuspChartCoordinates → ℂ)
    (hF : ContDiff ℝ ∞ F) (hC : HasCompactSupport F) (a : ℝ) (ha : 0<a) :
    MemLp F 2 (cuspChartVolume a) ∧
      ∀j : Fin 3,MemLp (fun q => cuspCoordinateVelocity F q j) 2 (cuspChartVolume a) := by
  let : IsFiniteMeasure (cuspChartVolume a) := cuspChartVolume_finite a ha
  refine ⟨hF.continuous.memLp_of_hasCompactSupport hC,fun j => ?_⟩
  obtain ⟨hc,hs⟩ := cuspCoordinateVelocity_continuous_compact F hF hC j
  exact hc.memLp_of_hasCompactSupport hs

theorem cuspChartL2_dense_smooth_energy (a : ℝ) (ha : 0<a) :
    Dense {f : CuspChartL2 a | ∃g : CuspChartCoordinates → ℂ,
      f=ᵐ[cuspChartVolume a] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      ∀j : Fin 3,MemLp (fun q => cuspCoordinateVelocity g q j) 2 (cuspChartVolume a)} := by
  let : IsFiniteMeasure (cuspChartVolume a) := cuspChartVolume_finite a ha
  apply (Lp.dense_hasCompactSupport_contDiff («μ» := cuspChartVolume a)
    (F := ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)).mono
  rintro f ⟨g,hg,hC,hgD⟩
  exact ⟨g,hg,hC,hgD,(cusp_compact_smooth_memLp g hgD hC a ha).2⟩

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport UnrestrictedIdealReindex IdealMobiusDivisorSum

theorem commonMaskIdeal_primeSupport (D : Ideal O) :
    IdealMobiusDivisorSum.primeSupport (commonMaskIdeal D) = gcdMaskPrimes D := by
  have hp : ∀ P ∈ (gcdMaskPrimes D).val, Prime P := by
    intro P hP
    let : P.IsMaximal := gcdMaskPrimes_maximal D ⟨P,hP⟩
    exact Ideal.prime_of_isPrime (NeZero.ne P) inferInstance
  have hf : UniqueFactorizationMonoid.normalizedFactors (commonMaskIdeal D) = (gcdMaskPrimes D).val := by
    simpa [commonMaskIdeal] using UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hp
  rw [IdealMobiusDivisorSum.primeSupport,hf,Finset.val_toFinset]

theorem commonMask_subset_sum_eq_divisors (D : Ideal O) (f : Ideal O → ℂ) :
    (∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset,
      f (∏ P ∈ E, P.val)) = ∑ q ∈ idealDivisors (commonMaskIdeal D), f q := by
  rw [sum_subtype_powerset_products,← commonMaskIdeal_primeSupport D]
  exact (squarefree_divisor_sum_eq_support _ (commonMaskIdeal_squarefree D) f).symm

theorem primaryProduct_norm (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) :
    ‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖ =
      Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
  have hs : ‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2 =
      (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ) := by
    rw [map_mul,norm_mul,mul_pow,
      primaryGenerator_norm_sq I (supported_primaryGenerator_ne_zero I (admissible_supported hI)),
      primaryGenerator_norm_sq J (supported_primaryGenerator_ne_zero J (admissible_supported hJ))]
  rw [← hs,Real.sqrt_sq (norm_nonneg _)]

def maskedPairIdealDualKernel (G I J : Ideal O) (W : ℝ → ℂ) (M : ℝ) : ℂ :=
  ((M:ℂ)/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)):ℂ))*
    ∑ q ∈ idealDivisors G,
      ((UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ))*
      ∑' B : NonzeroIdeal, unrestrictedPairCharacter I J B.val*paperRadialFourier W
        ((M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))*(Ideal.absNorm B.val:ℝ))

theorem originalPairIdealDualKernel_eq_divisors
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (W : ℝ → ℂ) (M : ℝ) :
    originalPairIdealDualKernel D I J W M =
      maskedPairIdealDualKernel (commonMaskIdeal D) (idealQuotient D I) (idealQuotient D J) W M := by
  let Q := idealQuotient D I
  let T := idealQuotient D J
  have hQ : Admissible Q := admissible_idealQuotient hI hDI
  have hT : Admissible T := admissible_idealQuotient hJ hDJ
  have hn := primaryProduct_norm Q T hQ hT
  have hnonneg : 0 ≤ (Ideal.absNorm Q:ℝ)*(Ideal.absNorm T:ℝ) := by positivity
  unfold originalPairIdealDualKernel maskedPairIdealDualKernel
  change ((M:ℂ)/(‖eisEmbedding (primaryGenerator Q*primaryGenerator T)‖:ℂ))*_ =
    ((M:ℂ)/(Real.sqrt ((Ideal.absNorm Q:ℝ)*(Ideal.absNorm T:ℝ)):ℂ))*_
  rw [hn]
  congr 1
  rw [← commonMask_subset_sum_eq_divisors D]
  apply Finset.sum_congr rfl
  intro E hE
  simp only [Real.sq_sqrt hnonneg,primeSubsetGenerator,unrestrictedPairCharacter,
    idealGenerator_norm_sq,Complex.ofReal_natCast]
  congr 1
  apply tsum_congr
  intro B
  congr 2
  ring

theorem originalPairDualKernel_eq_divisors
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (hIJ : I ≠ J) (hray : columnRay I=columnRay J)
    (W : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0<M) :
    originalPairDualKernel D I J W M =
      maskedPairIdealDualKernel (commonMaskIdeal D) (idealQuotient D I) (idealQuotient D J) W M := by
  rw [originalPairDualKernel_eq_ideal D I J hI hJ hDI hDJ hIJ hray W M hM]
  exact originalPairIdealDualKernel_eq_divisors D I J hI hJ hDI hDJ W M

end CanonicalQuadraticSieve

end

end OAI
