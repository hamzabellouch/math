import OAI.NumberTheory.PrimeGaps.FourierDerivatives

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

theorem integrable_schwartz_contourKernel {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) :
    Integrable (fun u => Φ u*contourKernel B u) := by
  have hm := (schwartz_integrable_polynomial_majorant Φ B.card).const_mul
    (((max (Fintype.card ι) 1:ℕ):ℝ)^B.card*2^(B.card-1))
  apply hm.mono' ((Φ.continuous.mul (continuous_contourKernel B hB)).aestronglyMeasurable)
  filter_upwards [] with u
  simp only [Pi.mul_apply]
  rw [norm_mul]
  calc
    _ ≤ ‖Φ u‖*(((max (Fintype.card ι) 1:ℕ):ℝ)^B.card*2^(B.card-1)*(1+‖u‖^B.card)) :=
      mul_le_mul_of_nonneg_left (contourKernel_norm_polynomial B hB u) (norm_nonneg _)
    _ = _ := by ring

noncomputable def kernelConstant {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (B : Finset (Finset ι)) : ℂ :=
  ∫ u, Φ u*contourKernel B u

noncomputable def kernelAbsoluteConstant {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (B : Finset (Finset ι)) : ℝ :=
  ∫ u, ‖Φ u*contourKernel B u‖

theorem kernelAbsoluteConstant_nonneg {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (B : Finset (Finset ι)) :
    0≤kernelAbsoluteConstant Φ B := integral_nonneg fun _ => norm_nonneg _

theorem kernel_integral_on_error {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty)
    (S : Set (EuclideanSpace ℝ ι)) (hS : MeasurableSet S)
    (f : EuclideanSpace ℝ ι → ℂ) (hf : IntegrableOn (fun u => Φ u*f u) S)
    (H : ℂ) {E : ℝ} (hE : 0≤E)
    (he : ∀ u∈S, ‖f u-H*contourKernel B u‖≤‖contourKernel B u‖*E) :
    ‖(∫ u in S, Φ u*f u)-H*(∫ u in S, Φ u*contourKernel B u)‖ ≤
      kernelAbsoluteConstant Φ B*E := by
  have hi := integrable_schwartz_contourKernel Φ B hB
  have hH : IntegrableOn (fun u => Φ u*(H*contourKernel B u)) S := by
    simpa only [mul_left_comm] using (hi.const_mul H).integrableOn (s:=S)
  have hiH : H*(∫ u in S, Φ u*contourKernel B u) =
      ∫ u in S, Φ u*(H*contourKernel B u) := by
    rw [← integral_const_mul]
    congr 1; ext u; ring
  rw [hiH,← integral_sub hf hH]
  calc
    _ ≤ ∫ u in S, ‖Φ u*f u-Φ u*(H*contourKernel B u)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in S, ‖Φ u*contourKernel B u‖*E := by
      apply integral_mono_ae (hf.sub hH).norm (hi.norm.mul_const E).integrableOn
      filter_upwards [ae_restrict_mem hS] with u hu
      simp only [Pi.sub_apply]
      rw [← mul_sub,norm_mul,norm_mul]
      nlinarith [mul_le_mul_of_nonneg_left (he u hu) (norm_nonneg (Φ u))]
    _ ≤ ∫ u, ‖Φ u*contourKernel B u‖*E :=
      setIntegral_le_integral (hi.norm.mul_const E) (by filter_upwards [] with u; positivity)
    _ = kernelAbsoluteConstant Φ B*E := by rw [integral_mul_const]; rfl

theorem eulerGlobalMajorant_div_rpow_tendsto (R : ℕ) {s : ℝ} (hs : 0<s) :
    Tendsto (fun y : ℕ => eulerGlobalMajorant R y/(y:ℝ)^s) atTop (𝓝 0) := by
  let c : ℝ := Real.exp 1
  let a : ℝ := 4*R*c
  let M : ℝ := Real.exp (a+genericEulerConstant R)
  have hlim := (tendsto_log_rpow_div_nat_rpow a hs).const_mul M
  apply squeeze_zero' _ _ (by simpa only [mul_zero] using hlim)
  · filter_upwards [] with y
    unfold eulerGlobalMajorant
    positivity
  · have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
    filter_upwards [eventually_prime_reciprocal_bound,
      ht.eventually_ge_atTop 1,
      (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop 1] with y hr hl hy
    change 1≤Real.log (y:ℝ) at hl
    have hly : 0<Real.log (y:ℝ) := by linarith
    have hr' : primeReciprocalPrefix y ≤ c*(1+Real.log (Real.log y)) := by
      simpa only [primeReciprocalPrefix_eq,c] using hr
    have hK : genericEulerConstant R/(y:ℝ)≤genericEulerConstant R :=
      div_le_self (genericEulerConstant_nonneg R) hy
    have hb : eulerGlobalMajorant R y ≤ M*(Real.log (y:ℝ))^a := by
      calc
        _ ≤ Real.exp (4*R*(c*(1+Real.log (Real.log y)))+genericEulerConstant R) := by
          unfold eulerGlobalMajorant
          gcongr
        _ = _ := by
          rw [Real.rpow_def_of_pos hly]
          dsimp only [M,a]
          rw [← Real.exp_add]
          congr 1
          ring
    calc
      _ ≤ (M*(Real.log (y:ℝ))^a)/(y:ℝ)^s :=
        div_le_div_of_nonneg_right hb (Real.rpow_nonneg (by positivity) _)
      _ = M*((Real.log (y:ℝ))^a/(y:ℝ)^s) := by ring

noncomputable def uniformCoreError (R : ℕ) (c s : ℝ) (y : ℕ) : ℝ :=
  uniformEulerError R s y*(1+(2^R*(R*(2*c)))*(y:ℝ)^(-s))+
    eulerGlobalMajorant R y*(2^R*(R*(2*c)))*(y:ℝ)^(-s)

theorem uniformCoreError_tendsto (R : ℕ) (c : ℝ) {s : ℝ} (hs : 0<s) :
    Tendsto (uniformCoreError R c s) atTop (𝓝 0) := by
  have hy : Tendsto (fun y : ℕ => (y:ℝ)^(-s)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hs).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have h₁ := (uniformEulerError_tendsto R hs).mul
    ((tendsto_const_nhds (x:=(1:ℝ))).add (hy.const_mul (2^R*(R*(2*c)))))
  have h₂ := (eulerGlobalMajorant_div_rpow_tendsto R hs).mul_const (2^R*(R*(2*c)))
  have he : (fun y : ℕ => eulerGlobalMajorant R y/(y:ℝ)^s*(2^R*(R*(2*c)))) =
      (fun y : ℕ => eulerGlobalMajorant R y*(2^R*(R*(2*c)))*(y:ℝ)^(-s)) := by
    ext y
    rw [Real.rpow_neg (by positivity : (0:ℝ)≤y)]
    ring
  rw [he] at h₂
  unfold uniformCoreError
  simpa only [zero_mul,mul_zero,add_zero,zero_add] using h₁.add h₂

theorem integrable_pow_mul_schwartz_contourKernel {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (k : ℕ) :
    Integrable (fun u => ‖u‖^k*‖Φ u*contourKernel B u‖) := by
  have hi := ((SchwartzMap.integrable_pow_mul volume Φ k).add
    (SchwartzMap.integrable_pow_mul volume Φ (k+B.card))).const_mul
    (((max (Fintype.card ι) 1:ℕ):ℝ)^B.card*2^(B.card-1))
  apply hi.mono' ((continuous_norm.pow k).mul
    ((Φ.continuous.mul (continuous_contourKernel B hB)).norm)).aestronglyMeasurable
  filter_upwards [] with u
  simp only [Pi.mul_apply,Pi.pow_apply,Pi.add_apply]
  rw [Real.norm_of_nonneg (by positivity),norm_mul]
  calc
    _ ≤ ‖u‖^k*(‖Φ u‖*((((max (Fintype.card ι) 1:ℕ):ℝ)^B.card*
      2^(B.card-1))*(1+‖u‖^B.card))) := by
      gcongr; exact contourKernel_norm_polynomial B hB u
    _ = _ := by rw [pow_add]; ring

theorem norm_integral_norm_tail_le {V : Type*} [NormedAddCommGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (f : V → ℂ)
    (hf : Integrable f μ) (k : ℕ) (hk : Integrable (fun u => ‖u‖^k*‖f u‖) μ)
    {U : ℝ} (hU : 0<U) :
    ‖∫ u in {u | U<‖u‖}, f u ∂μ‖ ≤ (∫ u, ‖u‖^k*‖f u‖ ∂μ)/U^k := by
  let S : Set V := {u | U<‖u‖}
  have hS : MeasurableSet S := measurableSet_lt measurable_const continuous_norm.measurable
  have hbound : ∀ᵐ u ∂μ.restrict S, ‖f u‖≤(U^k)⁻¹*(‖u‖^k*‖f u‖) := by
    filter_upwards [ae_restrict_mem hS] with u hu
    have hp : U^k≤‖u‖^k := pow_le_pow_left₀ hU.le hu.le k
    have hdiv : 1≤(U^k)⁻¹*‖u‖^k := by
      rw [← div_eq_inv_mul]
      exact (one_le_div (pow_pos hU k)).mpr hp
    calc
      _ ≤ ((U^k)⁻¹*‖u‖^k)*‖f u‖ := by nlinarith [norm_nonneg (f u)]
      _ = _ := by ring
  calc
    _ ≤ ∫ u in S, ‖f u‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in S, (U^k)⁻¹*(‖u‖^k*‖f u‖) ∂μ :=
      integral_mono_ae hf.integrableOn.norm ((hk.const_mul _).integrableOn) hbound
    _ ≤ ∫ u, (U^k)⁻¹*(‖u‖^k*‖f u‖) ∂μ :=
      setIntegral_le_integral (hk.const_mul _) (by filter_upwards [] with u; positivity)
    _ = _ := by rw [integral_const_mul]; ring

theorem kernel_integral_tail_bound {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (k : ℕ)
    {U : ℝ} (hU : 0<U) :
    ‖∫ u in {u | U<‖u‖}, Φ u*contourKernel B u‖ ≤
      (∫ u, ‖u‖^k*‖Φ u*contourKernel B u‖)/U^k :=
  norm_integral_norm_tail_le volume _ (integrable_schwartz_contourKernel Φ B hB) k
    (integrable_pow_mul_schwartz_contourKernel Φ B hB k) hU

theorem BombieriVinogradov_quantitative_PNT (hBV : BombieriVinogradov) :
    ∀ A : ℝ, 0<A → ∃ M>0, ∀ᶠ X : ℕ in atTop,
      |(∑ n∈Finset.Ioc 0 X, ArithmeticFunction.vonMangoldt n)-(X:ℝ)| ≤
        M*(X:ℝ)*(Real.log X)^(-A) := by
  intro A hA
  obtain ⟨b,hb,M,hM,x₀,hx₀,hbound⟩ := hBV A hA
  refine ⟨M,hM,?_⟩
  have hx := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop x₀
  have hQ := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (eventually_rpow_le_BV_range (rho:=0) (by norm_num) b)
  filter_upwards [hx,hQ] with X hX hXQ
  have hQ1 : 1≤⌊(X:ℝ)^(1/2:ℝ)*(Real.log X)^(-b)⌋₊ := by
    apply Nat.le_floor
    simpa only [Real.rpow_zero,Nat.cast_one] using hXQ
  have hle : (endpointError X 1:ℝ) ≤
      ∑ q ∈ Finset.Icc 1 ⌊(X:ℝ)^(1/2:ℝ)*(Real.log X)^(-b)⌋₊, (endpointError X q:ℝ) := by
    exact Finset.single_le_sum (fun q _ => NNReal.coe_nonneg _)
      (Finset.mem_Icc.mpr ⟨le_rfl,hQ1⟩)
  have hclass := endpointClassError_le X (q:=1) (c:=0) (by norm_num) (by norm_num)
  have heq : residuePrefix ArithmeticFunction.vonMangoldt X 1 0 =
      ∑ n∈Finset.Ioc 0 X, ArithmeticFunction.vonMangoldt n := by
    simp [residuePrefix,residueSlice,Nat.mod_one]
  rw [heq,Nat.totient_one,Nat.cast_one,div_one] at hclass
  exact hclass.trans (hle.trans (hbound X hX))

theorem uniformEulerError_nonneg (R : ℕ) (s : ℝ) {y : ℕ} (hy : 1≤y) :
    0≤uniformEulerError R s y := by
  have hl : 0≤Real.log (y:ℝ) := Real.log_nonneg (by exact_mod_cast hy)
  have hp := primeReciprocalPrefix_nonneg y
  have he : 0≤Real.exp (genericEulerConstant R/(y:ℝ))-1 :=
    sub_nonneg.mpr (Real.one_le_exp (by
      exact div_nonneg (genericEulerConstant_nonneg R) (by positivity)))
  unfold uniformEulerError
  positivity

theorem uniformCoreError_nonneg (R : ℕ) {c : ℝ} (hc : 0≤c) (s : ℝ)
    {y : ℕ} (hy : 1≤y) : 0≤uniformCoreError R c s y := by
  have he := uniformEulerError_nonneg R s hy
  have hm : 0≤eulerGlobalMajorant R y := (Real.exp_pos _).le
  unfold uniformCoreError
  positivity

theorem frequencyW_div_norm_sum_le {ι : Type*} [Fintype ι] (u : ι → ℝ)
    {L U : ℝ} (hL : 0<L) (hu : ∀ i, |u i|≤U) :
    (∑ i, ‖frequencyW (u i)/(L:ℂ)‖) ≤ (Fintype.card ι:ℝ)*(1+U)/L := by
  calc
    _ ≤ ∑ _i : ι, (1+U)/L := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
      apply div_le_div_of_nonneg_right _ hL.le
      exact (frequencyW_norm (u i)).trans (by linarith [hu i])
    _ = _ := by simp; ring

theorem tupleFourier_scaled_uniform_core_error :
    ∃ c>0, ∃ ε>0, ∀ {ι : Type*} [Fintype ι] {δ R : ℕ}, δ≤1 →
      ∀ (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι)),
      (∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty) →
      (∀ p : Nat.Primes, (A p).card≤R) →
      (∀ S∈B, S.Nonempty) → B.card≤R → ∀ {y : ℕ}, 2≤y →
      (∀ p : Nat.Primes, y<(p:ℕ) → A p=B) →
      ∀ (u : ι → ℝ) {t : ℕ}, (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ) →
      ∀ {L U s : ℝ}, 0<L → 0≤U → (∀ i, |u i|≤U) →
      (Fintype.card ι:ℝ)*(1+U)/L<ε →
      (Fintype.card ι:ℝ)*(1+U)/L≤(y:ℝ)^(-s) →
      ‖(L:ℂ)^t*(∑' d : AllowedDivisorTuple A,
        tupleFourierCoefficient δ d.val (fun i => frequencyW (u i)/(L:ℂ))) -
        eulerGlobal δ A B (fun _ => 0)*familyKernel B (fun i => frequencyW (u i))‖ ≤
      ‖familyKernel B (fun i => frequencyW (u i))‖*uniformCoreError R c s y := by
  obtain ⟨c,hc,ε,hε,hcore⟩ := tupleFourier_scaled_core_error
  refine ⟨c,hc,ε,hε,?_⟩
  intro ι _ δ R hδ A B hA hR hB hBR y hy hgen u t ht L U s hL hU hu hsmall hzsmall
  apply (hcore hδ A B hA hR hB hBR hy hgen u ht hL hU hu hsmall
    ((frequencyW_div_norm_sum_le u hL hu).trans hzsmall)).trans
  have hE := uniformEulerError_nonneg R s (show 1≤y by omega)
  have hCB : (B.card:ℝ)≤R := by exact_mod_cast hBR
  have h2 : (2:ℝ)^B.card≤2^R := pow_le_pow_right₀ (by norm_num) hBR
  have hζ : 2^B.card*(B.card*(2*c*((Fintype.card ι:ℝ)*(1+U)/L))) ≤
      (2^R*(R*(2*c)))*(y:ℝ)^(-s) := by
    calc
      _ ≤ 2^R*(R*(2*c*(y:ℝ)^(-s))) := by gcongr
      _ = _ := by ring
  unfold uniformCoreError
  have hM : 0≤eulerGlobalMajorant R y := (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_left hζ hM
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (add_le_add_right hζ 1) hE
  · calc
      _ ≤ eulerGlobalMajorant R y*((2^R*(R*(2*c)))*(y:ℝ)^(-s)) := hmul
      _ = _ := by ring

theorem integrable_schwartz_tupleFourier {ι : Type*} [Fintype ι] {δ R : ℕ}
    (hδ : δ≤1) (A : ℕ → Finset (Finset ι)) {L : ℝ} (hL : 0<L)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R)
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    Integrable (fun u => Φ u * (∑' d : AllowedDivisorTuple A,
      tupleFourierCoefficient δ d.val (fourierContour L u))) := by
  exact Φ.integrable.mul_bdd
    (continuous_tupleFourier_tsum hδ A hL hA hR).aestronglyMeasurable
    (Filter.Eventually.of_forall (tupleFourier_tsum_norm_bound hδ A hL hA hR))

theorem integral_core_tail_error {V : Type*} [MeasurableSpace V]
    (μ : Measure V) (f g : V → ℂ) (hf : Integrable f μ) (hg : Integrable g μ)
    (S : Set V) (hS : MeasurableSet S) (H : ℂ) {E : ℝ}
    (he : ‖(∫ u in S, f u ∂μ)-H*(∫ u in S, g u ∂μ)‖≤E) :
    ‖(∫ u, f u ∂μ)-H*(∫ u, g u ∂μ)‖ ≤
      E + ‖∫ u in Sᶜ, f u ∂μ‖ + ‖H‖*‖∫ u in Sᶜ, g u ∂μ‖ := by
  rw [← integral_add_compl hS hf,← integral_add_compl hS hg]
  calc
    _ = ‖((∫ u in S, f u ∂μ)-H*(∫ u in S, g u ∂μ)) +
      ((∫ u in Sᶜ, f u ∂μ)-H*(∫ u in Sᶜ, g u ∂μ))‖ := by congr 1; ring
    _ ≤ ‖(∫ u in S, f u ∂μ)-H*(∫ u in S, g u ∂μ)‖ +
      ‖(∫ u in Sᶜ, f u ∂μ)-H*(∫ u in Sᶜ, g u ∂μ)‖ := norm_add_le _ _
    _ ≤ E + (‖∫ u in Sᶜ, f u ∂μ‖ + ‖H‖*‖∫ u in Sᶜ, g u ∂μ‖) := by
      apply add_le_add he
      simpa only [norm_mul] using norm_sub_le (∫ u in Sᶜ, f u ∂μ)
        (H*(∫ u in Sᶜ, g u ∂μ))
    _ = _ := by ring

theorem tupleFourier_integral_uniform_error :
    ∃ c>0, ∃ ε>0, ∀ {ι : Type*} [Fintype ι] {δ R : ℕ}, δ≤1 →
      ∀ (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι)),
      (∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty) →
      (∀ p : Nat.Primes, (A p).card≤R) →
      (∀ S∈B, S.Nonempty) → B.card≤R → ∀ {y : ℕ}, 2≤y →
      (∀ p : Nat.Primes, y<(p:ℕ) → A p=B) →
      ∀ (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) {t : ℕ},
      (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ) →
      ∀ {L U s : ℝ}, 0<L → 0<U →
      (Fintype.card ι:ℝ)*(1+U)/L<ε →
      (Fintype.card ι:ℝ)*(1+U)/L≤(y:ℝ)^(-s) → ∀ k₁ k₂ : ℕ,
      ‖(L:ℂ)^t*(∫ u, Φ u*(∑' d : AllowedDivisorTuple A,
        tupleFourierCoefficient δ d.val (fourierContour L u))) -
        eulerGlobal δ A B (fun _ => 0)*kernelConstant Φ B‖ ≤
      kernelAbsoluteConstant Φ B*uniformCoreError R c s y +
      L^t*(Real.exp ((2*R)*Real.log (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re)/U^k₁)*
        (∫ u, ‖u‖^k₁*‖Φ u‖) +
      eulerGlobalMajorant R y*(∫ u, ‖u‖^k₂*‖Φ u*contourKernel B u‖)/U^k₂ := by
  obtain ⟨c,hc,ε,hε,hcore⟩ := tupleFourier_scaled_uniform_core_error
  refine ⟨c,hc,ε,hε,?_⟩
  intro ι _ δ R hδ A B hA hR hB hBR y hy hgen Φ t ht L U s hL hU hsmall hysmall k₁ k₂
  let T := fun u : EuclideanSpace ℝ ι => ∑' d : AllowedDivisorTuple A,
    tupleFourierCoefficient δ d.val (fourierContour L u)
  let S : Set (EuclideanSpace ℝ ι) := {u | ‖u‖≤U}
  have hS : MeasurableSet S := measurableSet_le continuous_norm.measurable measurable_const
  have hSc : Sᶜ={u | U<‖u‖} := by ext u; simp [S]
  have hT : Integrable (fun u => Φ u*T u) := integrable_schwartz_tupleFourier hδ A hL hA hR Φ
  have hcT : Integrable (fun u => Φ u*((L:ℂ)^t*T u)) := by
    simpa only [mul_left_comm] using hT.const_mul ((L:ℂ)^t)
  have hK := integrable_schwartz_contourKernel Φ B hB
  have hpoint : ∀ u∈S, ‖(L:ℂ)^t*T u-eulerGlobal δ A B (fun _ => 0)*
      contourKernel B u‖≤‖contourKernel B u‖*uniformCoreError R c s y := by
    intro u hu
    have hui : ∀ i, |u i|≤U := by
      intro i
      have hh : |u i|≤‖u‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i
      exact hh.trans hu
    exact hcore hδ A B hA hR hB hBR hy hgen (fun i => u i) ht hL hU.le hui hsmall hysmall
  have he := kernel_integral_on_error Φ B hB S hS (fun u => (L:ℂ)^t*T u)
    hcT.integrableOn (eulerGlobal δ A B (fun _ => 0))
    (uniformCoreError_nonneg R hc.le s (y:=y) (by omega)) hpoint
  have hall := integral_core_tail_error volume (fun u => Φ u*((L:ℂ)^t*T u))
    (fun u => Φ u*contourKernel B u) hcT hK S hS
    (eulerGlobal δ A B (fun _ => 0)) he
  have hid : ∀ D : Set (EuclideanSpace ℝ ι),
      (∫ u in D, Φ u*((L:ℂ)^t*T u)) = (L:ℂ)^t*∫ u in D, Φ u*T u := by
    intro D
    rw [← integral_const_mul]
    congr 1; ext u; ring
  have hidall : (∫ u, Φ u*((L:ℂ)^t*T u))=(L:ℂ)^t*∫ u, Φ u*T u := by
    rw [← integral_const_mul]
    congr 1; ext u; ring
  rw [hidall,hid,hSc] at hall
  apply hall.trans
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  apply add_le_add
  · apply add_le_add_right
    have hb := tupleFourier_schwartz_tail hδ A hL hU hA hR Φ k₁
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (pow_nonneg hL.le t)
  · have hH := norm_eulerGlobal_le hδ A B (fun _ => (0:ℂ)) (by intro i; simp)
      (y:=y) (by omega) hR hBR hgen
    have hb := kernel_integral_tail_bound Φ B hB k₂ hU
    calc
      _ ≤ eulerGlobalMajorant R y*((∫ u, ‖u‖^k₂*‖Φ u*contourKernel B u‖)/U^k₂) :=
        mul_le_mul hH hb (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by ring

noncomputable def densityCutoff (b : ℕ) (L : ℝ) : ℕ := ⌊L^b⌋₊

noncomputable def densityCoreExponent (b : ℕ) : ℝ := (4*(b:ℝ))⁻¹

theorem densityCoreExponent_pos {b : ℕ} (hb : 0<b) : 0<densityCoreExponent b := by
  unfold densityCoreExponent
  positivity

theorem densityCutoff_tendsto {b : ℕ} (hb : 0<b) :
    Tendsto (densityCutoff b) atTop atTop :=
  tendsto_nat_floor_atTop.comp (tendsto_pow_atTop (by omega : b≠0))

theorem sqrt_core_rate (C : ℝ) {L : ℝ} (hL : 0<L) :
    C*(1+Real.sqrt L)/L = C*(L^(-1:ℝ)+L^(-(1/2):ℝ)) := by
  have hp : L^(1/2:ℝ)/L = L^(-(1/2):ℝ) := by
    calc
      _ = L^(1/2:ℝ)/L^(1:ℝ) := by rw [Real.rpow_one]
      _ = L^((1/2:ℝ)-1) := (Real.rpow_sub hL _ _).symm
      _ = _ := by norm_num
  rw [Real.sqrt_eq_rpow,Real.rpow_neg_one,← hp]
  ring

theorem sqrt_core_rate_tendsto (C : ℝ) :
    Tendsto (fun L : ℝ => C*(1+Real.sqrt L)/L) atTop (𝓝 0) := by
  have h₁ := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)
  have h₂ := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)
  have hh := (h₁.add h₂).const_mul C
  simp only [add_zero,mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  exact (sqrt_core_rate C hL).symm

theorem sqrt_core_quarter_rate (C : ℝ) {L : ℝ} (hL : 0<L) :
    (C*(1+Real.sqrt L)/L)/(L^(-(1/4):ℝ)) =
      C*(L^(-(3/4):ℝ)+L^(-(1/4):ℝ)) := by
  rw [sqrt_core_rate C hL,mul_div_assoc,add_div,← Real.rpow_sub hL,← Real.rpow_sub hL]
  norm_num

theorem eventually_sqrt_core_le_quarter (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, C*(1+Real.sqrt L)/L≤L^(-(1/4):ℝ) := by
  have h₁ := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<3/4)
  have h₂ := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)
  have hh := (h₁.add h₂).const_mul C
  simp only [add_zero,mul_zero] at hh
  filter_upwards [hh.eventually_lt_const zero_lt_one,eventually_gt_atTop (0:ℝ)] with L h hL
  apply (div_le_one (Real.rpow_pos_of_pos hL _)).mp
  rw [sqrt_core_quarter_rate C hL]
  exact h.le

theorem densityCutoff_neg_rpow {b : ℕ} (hb : 0<b) {L : ℝ} (hL : 1≤L) :
    L^(-(1/4):ℝ) ≤ (densityCutoff b L:ℝ)^(-densityCoreExponent b) := by
  have hLb : 1≤L^b := one_le_pow₀ hL
  have hy : 0<(densityCutoff b L:ℝ) := by
    have : 1≤densityCutoff b L := (Nat.one_le_floor_iff _).mpr hLb
    exact_mod_cast (show 0<densityCutoff b L by omega)
  have hyle : (densityCutoff b L:ℝ)≤L^b := Nat.floor_le (by positivity)
  have hb0 : (b:ℝ)≠0 := by exact_mod_cast hb.ne'
  have hexp : (b:ℝ)*(-densityCoreExponent b)=-(1/4:ℝ) := by
    unfold densityCoreExponent
    field_simp
  calc
    _ = L^((b:ℝ)*(-densityCoreExponent b)) := by rw [hexp]
    _ = (L^b)^(-densityCoreExponent b) := by
      rw [Real.rpow_mul (by linarith),Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos hy hyle (by
      have := densityCoreExponent_pos hb; linarith)

theorem eventually_density_core_scale {b : ℕ} (hb : 0<b) (C : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, 0<L ∧ 2≤densityCutoff b L ∧
      C*(1+Real.sqrt L)/L<ε ∧
      C*(1+Real.sqrt L)/L≤(densityCutoff b L:ℝ)^(-densityCoreExponent b) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (densityCutoff_tendsto hb).eventually (eventually_ge_atTop 2),
    (sqrt_core_rate_tendsto C).eventually_lt_const hε,
    eventually_sqrt_core_le_quarter C] with L hL hy hεL hbound
  exact ⟨by linarith,hy,hεL,hbound.trans (densityCutoff_neg_rpow hb hL)⟩

theorem eventually_nat_rate_le_index (a : ℕ → ℝ)
    (ha : Tendsto (fun y : ℕ => a y/(y:ℝ)) atTop (𝓝 0)) :
    ∀ᶠ y : ℕ in atTop, a y≤y := by
  filter_upwards [ha.eventually_lt_const zero_lt_one,eventually_ge_atTop 1] with y h hy
  exact ((div_le_one (by exact_mod_cast hy : 0<(y:ℝ))).mp h.le)

theorem eventually_rate_densityCutoff_le_pow (a : ℕ → ℝ)
    (ha : Tendsto (fun y : ℕ => a y/(y:ℝ)) atTop (𝓝 0))
    {b : ℕ} (hb : 0<b) :
    ∀ᶠ L : ℝ in atTop, a (densityCutoff b L)≤L^b := by
  filter_upwards [(densityCutoff_tendsto hb).eventually (eventually_nat_rate_le_index a ha),
    eventually_ge_atTop (0:ℝ)] with L h hL
  exact h.trans (Nat.floor_le (pow_nonneg hL b))

theorem sqrt_pow_even {L : ℝ} (hL : 0≤L) (n : ℕ) :
    (Real.sqrt L)^(2*n) = L^n := by rw [pow_mul,Real.sq_sqrt hL]

theorem scaled_polynomial_tail {L Z I : ℝ} (hL : 0<L) (hI : 0≤I) (R t : ℕ)
    (hZ : Z≤((3/2:ℝ)*L)^(2*R)) :
    L^t*(Z/(Real.sqrt L)^(2*(2*R+t+1)))*I≤((3/2:ℝ)^(2*R)*I)/L := by
  rw [sqrt_pow_even hL.le]
  calc
    _ ≤ L^t*((((3/2:ℝ)*L)^(2*R))/L^(2*R+t+1))*I := by gcongr
    _ = _ := by rw [mul_pow,pow_add,pow_add,pow_one]; field_simp

theorem kernel_polynomial_tail {L Z I : ℝ} (hL : 0<L) (hI : 0≤I) (b : ℕ)
    (hZ : Z≤L^b) :
    Z*I/(Real.sqrt L)^(2*(b+1))≤I/L := by
  rw [sqrt_pow_even hL.le]
  calc
    _ ≤ L^b*I/L^(b+1) := by gcongr
    _ = _ := by rw [pow_succ]; field_simp

theorem tupleFourier_integral_uniform_asymptotic {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (B : Finset (Finset ι))
    (hB : ∀ S∈B, S.Nonempty) (R t b : ℕ) (hBR : B.card≤R) (hb : 0<b)
    (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) :
    ∃ E : ℝ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ L : ℝ in atTop, ∀ δ : ℕ, δ≤1 → ∀ A : ℕ → Finset (Finset ι),
      (∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty) →
      (∀ p : Nat.Primes, (A p).card≤R) →
      (∀ p : Nat.Primes, densityCutoff b L<(p:ℕ) → A p=B) →
      ‖(L:ℂ)^t*(∫ u, Φ u*(∑' d : AllowedDivisorTuple A,
        tupleFourierCoefficient δ d.val (fourierContour L u))) -
        eulerGlobal δ A B (fun _ => 0)*kernelConstant Φ B‖ ≤ E L := by
  obtain ⟨c,hc,ε,hε,hformula⟩ := tupleFourier_integral_uniform_error
  obtain ⟨L₀,hL₀,hz⟩ := zeta_contour_majorant_polynomial
  let I₁ : ℝ := (3/2:ℝ)^(2*R)*(∫ u, ‖u‖^(2*(2*R+t+1))*‖Φ u‖)
  let I₂ : ℝ := ∫ u, ‖u‖^(2*(b+1))*‖Φ u*contourKernel B u‖
  let E : ℝ → ℝ := fun L => kernelAbsoluteConstant Φ B*
    uniformCoreError R c (densityCoreExponent b) (densityCutoff b L) + I₁/L + I₂/L
  refine ⟨E,?_,?_⟩
  · have hcore := ((uniformCoreError_tendsto R c (densityCoreExponent_pos hb)).comp
      (densityCutoff_tendsto hb)).const_mul (kernelAbsoluteConstant Φ B)
    have h₁ : Tendsto (fun L : ℝ => I₁/L) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have h₂ : Tendsto (fun L : ℝ => I₂/L) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    simpa only [mul_zero,add_zero,Function.comp_def,E] using (hcore.add h₁).add h₂
  · have hM : Tendsto (fun y : ℕ => eulerGlobalMajorant R y/(y:ℝ)) atTop (𝓝 0) := by
      simpa only [Real.rpow_one] using eulerGlobalMajorant_div_rpow_tendsto R zero_lt_one
    filter_upwards [eventually_density_core_scale hb (Fintype.card ι:ℝ) hε,
      eventually_rate_densityCutoff_le_pow (eulerGlobalMajorant R) hM hb,
      eventually_ge_atTop L₀] with L hscale hmajor hLL₀
    intro δ hδ A hA hR hgen
    obtain ⟨hL,hy,hsmall,hysmall⟩ := hscale
    have hbound := hformula hδ A B hA hR hB hBR hy hgen Φ ht hL
      (Real.sqrt_pos.mpr hL) hsmall hysmall (2*(2*R+t+1)) (2*(b+1))
    apply hbound.trans
    apply add_le_add
    · apply add_le_add_right
      exact scaled_polynomial_tail hL (integral_nonneg (fun _ => by positivity)) R t (hz L hLL₀ R)
    · exact kernel_polynomial_tail hL (integral_nonneg (fun _ => by positivity)) b hmajor

end LargePrimeGaps

end OAI
