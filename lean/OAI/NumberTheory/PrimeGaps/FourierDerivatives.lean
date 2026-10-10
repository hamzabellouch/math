import OAI.NumberTheory.PrimeGaps.ContourSums

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

theorem tendsto_log_rpow_div_nat_rpow (a : ℝ) {s : ℝ} (hs : 0<s) :
    Tendsto (fun y : ℕ => (Real.log (y:ℝ))^a/(y:ℝ)^s) atTop (𝓝 0) :=
  (isLittleO_log_rpow_rpow_atTop a hs).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))

theorem uniformEulerError_tendsto (R : ℕ) {s : ℝ} (hs : 0<s) :
    Tendsto (uniformEulerError R s) atTop (𝓝 0) := by
  let c : ℝ := Real.exp 1
  let a : ℝ := 4*R*c
  let M : ℝ := Real.exp a
  let K : ℝ := genericEulerConstant R
  let E₁ : ℕ → ℝ := fun y => (M*Real.exp (2*R)*6*R*c)*
    ((Real.log (y:ℝ))^(a+2)/(y:ℝ)^s)
  let E₂ : ℕ → ℝ := fun y => (4*M*K)*((Real.log (y:ℝ))^a/(y:ℝ))
  have h₁ : Tendsto E₁ atTop (𝓝 0) := by
    simpa only [mul_zero,E₁] using (tendsto_log_rpow_div_nat_rpow (a+2) hs).const_mul _
  have h₂ : Tendsto E₂ atTop (𝓝 0) := by
    simpa only [mul_zero,Real.rpow_one,E₂] using
      (tendsto_log_rpow_div_nat_rpow a (s:=1) zero_lt_one).const_mul (4*M*K)
  have he : ∀ᶠ y : ℕ in atTop, 0≤uniformEulerError R s y ∧
      uniformEulerError R s y ≤ E₁ y+E₂ y := by
    have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
    filter_upwards [eventually_prime_reciprocal_bound, ht.eventually_ge_atTop 1,
      (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (max K 1)] with y hr hl hy
    change 1 ≤ Real.log (y:ℝ) at hl
    have hy0 : (0:ℝ)<y := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hy)
    have hK0 : 0≤K := genericEulerConstant_nonneg R
    have hKy : K/(y:ℝ)≤1 := (div_le_one hy0).mpr ((le_max_left _ _).trans hy)
    have hp0 := primeReciprocalPrefix_nonneg y
    have hr' : primeReciprocalPrefix y ≤ c*(1+Real.log (Real.log y)) := by
      simpa only [primeReciprocalPrefix_eq,c] using hr
    have hr'' : primeReciprocalPrefix y ≤ c*Real.log y := by
      apply hr'.trans
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      linarith [Real.log_le_sub_one_of_pos (show 0<Real.log (y:ℝ) by linarith)]
    have hp : Real.exp (4*R*primeReciprocalPrefix y) ≤ M*(Real.log (y:ℝ))^a := by
      calc
        _ ≤ Real.exp (4*R*(c*(1+Real.log (Real.log y)))) := by gcongr
        _ = _ := by
          rw [Real.rpow_def_of_pos (show 0<Real.log (y:ℝ) by linarith)]
          dsimp only [M,a]
          rw [← Real.exp_add]
          congr 1
          ring
    have hex : Real.exp (K/(y:ℝ))-1 ≤ 2*(K/(y:ℝ)) :=
      exp_sub_one_le_two_mul (by positivity) hKy
    have hnonneg : 0≤Real.exp (K/(y:ℝ))-1 := sub_nonneg.mpr (Real.one_le_exp (by positivity))
    constructor
    · unfold uniformEulerError
      exact mul_nonneg (Real.exp_pos _).le (add_nonneg (by positivity) (mul_nonneg (by norm_num) hnonneg))
    · calc
        _ ≤ (M*(Real.log (y:ℝ))^a)*
              (Real.exp (2*R)*6*R*Real.log y*(y:ℝ)^(-s)*(c*Real.log y)+4*K/(y:ℝ)) := by
            unfold uniformEulerError
            apply mul_le_mul hp ?_ (add_nonneg (by positivity) (mul_nonneg (by norm_num) hnonneg))
              (by positivity)
            gcongr
            calc
              _ ≤ 2*(2*(K/(y:ℝ))) := mul_le_mul_of_nonneg_left hex (by norm_num)
              _ = _ := by ring
        _ = E₁ y+E₂ y := by
          dsimp only [E₁,E₂]
          rw [Real.rpow_neg hy0.le,Real.rpow_add (show 0<Real.log (y:ℝ) by linarith),Real.rpow_two]
          ring
  apply squeeze_zero'
  · exact he.mono (fun _ => And.left)
  · exact he.mono (fun _ => And.right)
  · simpa only [add_zero] using h₁.add h₂

section FourierDerivative

open scoped FourierTransform SchwartzMap ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

open LineDeriv

theorem radianFourier_lineDeriv (G : SchwartzMap V ℂ) (m u : V) :
    radianFourier (∂_{m} G) u = -Complex.I*(inner ℝ u m:ℂ)*radianFourier G u := by
  have hg : (inner ℝ · m).HasTemperateGrowth := by fun_prop
  simp only [radianFourier,SchwartzMap.fourierInv_lineDerivOp_eq,
    smul_apply,SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,
    frequencyDilation_apply,SchwartzMap.smulLeftCLM_apply hg,real_inner_smul_left,
    smul_eq_mul,Complex.real_smul]
  push_cast
  field_simp

theorem radianFourier_add (G H : SchwartzMap V ℂ) (u : V) :
    radianFourier (G+H) u = radianFourier G u+radianFourier H u := by
  simp only [radianFourier, FourierTransform.fourierInv_add, map_add, smul_add, add_apply]

theorem radianFourier_const_mul (c : ℂ) (G : SchwartzMap V ℂ) (u : V) :
    radianFourier (c • G) u = c*radianFourier G u := by
  simp only [radianFourier, FourierTransform.fourierInv_smul, map_smul, smul_apply,Complex.real_smul,smul_eq_mul]
  ring

noncomputable def laplaceLineDeriv (ℓ : V →L[ℝ] ℝ) (m : V) (G : SchwartzMap V ℂ) :
    SchwartzMap V ℂ := (ℓ m : ℂ) • G + (-1:ℂ) • (∂_{m} G)

theorem radianFourier_laplaceLineDeriv (ℓ : V →L[ℝ] ℝ) (m : V)
    (G : SchwartzMap V ℂ) (u : V) :
    radianFourier (laplaceLineDeriv ℓ m G) u =
      ((ℓ m : ℂ)+Complex.I*(inner ℝ u m:ℂ))*radianFourier G u := by
  rw [laplaceLineDeriv, radianFourier_add, radianFourier_const_mul,
    radianFourier_const_mul, radianFourier_lineDeriv]
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem laplaceLineDeriv_apply (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (m v : V) :
    laplaceLineDeriv ℓ m (laplaceSchwartz ℓ F hF hFs) v =
      Complex.exp (ℓ v : ℂ)*(-fderiv ℝ F v m) := by
  have hlin := Complex.ofRealCLM.hasFDerivAt.comp v ℓ.hasFDerivAt
  have he := hlin.cexp
  have hf := he.mul ((hFs.differentiable (by simp)).differentiableAt.hasFDerivAt (x := v))
  simp only [laplaceLineDeriv, add_apply, smul_apply, smul_eq_mul,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, laplaceSchwartz_apply]
  change (ℓ m:ℂ)*(Complex.exp (ℓ v:ℂ)*F v) +
    -1*(fderiv ℝ (fun v => Complex.exp (ℓ v:ℂ)*F v) v m) = _
  have hd := congrArg (fun A : V →L[ℝ] ℂ => A m) hf.fderiv
  simp only [Function.comp_apply, add_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, smul_eq_mul] at hd
  change (fderiv ℝ (fun x => Complex.exp (ℓ x:ℂ)*F x) v) m =
    Complex.exp (ℓ v:ℂ)*fderiv ℝ F v m + F v*(Complex.exp (ℓ v:ℂ)*(ℓ m:ℂ)) at hd
  rw [hd]
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem contDiff_signedLineDeriv (F : V → ℂ) (hFs : ContDiff ℝ ∞ F) (m : V) :
    ContDiff ℝ ∞ (fun v => -fderiv ℝ F v m) := by
  exact (hFs.fderiv_right (by simp)).clm_apply contDiff_const |>.neg

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem laplaceLineDeriv_laplaceSchwartz (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (m : V) :
    laplaceLineDeriv ℓ m (laplaceSchwartz ℓ F hF hFs) =
      laplaceSchwartz ℓ (fun v => -fderiv ℝ F v m) (hF.fderiv_apply ℝ m |>.neg)
        (contDiff_signedLineDeriv F hFs m) := by
  ext v
  exact laplaceLineDeriv_apply ℓ F hF hFs m v

theorem sourceFourier_signedLineDeriv (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (m u : V) :
    sourceFourier ℓ (fun v => -fderiv ℝ F v m) (hF.fderiv_apply ℝ m |>.neg)
        (contDiff_signedLineDeriv F hFs m) u =
      ((ℓ m:ℂ)+Complex.I*(inner ℝ u m:ℂ))*sourceFourier ℓ F hF hFs u := by
  unfold sourceFourier
  rw [← laplaceLineDeriv_laplaceSchwartz, radianFourier_laplaceLineDeriv]

noncomputable def signedDirections (ms : List V) (F : V → ℂ) : V → ℂ :=
  ms.foldr (fun m H v => -fderiv ℝ H v m) F

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem signedDirections_compact (ms : List V) (F : V → ℂ) (hF : HasCompactSupport F) :
    HasCompactSupport (signedDirections ms F) := by
  induction ms with
  | nil => exact hF
  | cons m ms ih => exact (ih.fderiv_apply ℝ m).neg

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem signedDirections_smooth (ms : List V) (F : V → ℂ) (hFs : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (signedDirections ms F) := by
  induction ms with
  | nil => exact hFs
  | cons m ms ih => exact contDiff_signedLineDeriv _ ih m

theorem sourceFourier_signedDirections (ℓ : V →L[ℝ] ℝ) (ms : List V) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (u : V) :
    sourceFourier ℓ (signedDirections ms F) (signedDirections_compact ms F hF)
        (signedDirections_smooth ms F hFs) u =
      (ms.map (fun m => ((ℓ m:ℂ)+Complex.I*(inner ℝ u m:ℂ)))).prod *
        sourceFourier ℓ F hF hFs u := by
  induction ms with
  | nil => simp [signedDirections]
  | cons m ms ih =>
    change sourceFourier ℓ (fun v => -fderiv ℝ (signedDirections ms F) v m) _ _ u = _
    rw [sourceFourier_signedLineDeriv ℓ (signedDirections ms F)
      (signedDirections_compact ms F hF) (signedDirections_smooth ms F hFs),ih]
    simp only [List.map_cons,List.prod_cons,mul_assoc]

theorem sourceFourier_derivative_inversion (ℓ : V →L[ℝ] ℝ) (ms : List V) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : V) :
    (∫ u : V, sourceFourier ℓ F hF hFs u *
      (ms.map (fun m => ((ℓ m:ℂ)+Complex.I*(inner ℝ u m:ℂ)))).prod *
      Complex.exp (-(ℓ v:ℂ)-Complex.I*(inner ℝ u v:ℂ))) = signedDirections ms F v := by
  rw [← sourceFourier_inversion ℓ (signedDirections ms F)
    (signedDirections_compact ms F hF) (signedDirections_smooth ms F hFs) v]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [sourceFourier_signedDirections,mul_comm (sourceFourier ℓ F hF hFs u)]

end FourierDerivative

noncomputable def familyKernel {ι : Type*} (B : Finset (Finset ι)) (w : ι → ℂ) : ℂ :=
  ∏ S∈B, (∑ i∈S, w i)^(-((-1:ℤ)^S.card))

noncomputable def normalizedZetaProduct {ι : Type*} (B : Finset (Finset ι)) (z : ι → ℂ) : ℂ :=
  ∏ S∈B, ((∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i))^((-1:ℤ)^S.card)

theorem familyKernel_fibers {ι α : Type*} [Fintype ι] (b : ι → α)
    (R : Finset α) (w : ι → ℂ) :
    familyKernel (fiberSubsetFamily b R) w =
      ∏ r∈R, fiberKernel (Finset.univ.filter fun i => b i=r) w := by
  classical
  unfold familyKernel fiberSubsetFamily fiberKernel
  rw [Finset.prod_biUnion]
  intro r _ s _ hrs
  exact disjoint_nonemptySubsets_fibers b hrs

theorem familyKernel_homogeneous {ι : Type*} (B : Finset (Finset ι))
    (w : ι → ℂ) {c : ℂ} (hc : c≠0) {t : ℕ}
    (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) :
    familyKernel B (fun i => c*w i) = c^t*familyKernel B w := by
  classical
  unfold familyKernel
  simp_rw [← Finset.mul_sum,mul_zpow]
  rw [Finset.prod_mul_distrib,prod_const_zpow _ _ hc,Finset.sum_neg_distrib,ht,
    neg_neg,zpow_natCast]

theorem eulerZetaProduct_factorization {ι : Type*} (B : Finset (Finset ι)) (z : ι → ℂ)
    (hz : ∀ S∈B, ∑ i∈S, z i≠0) :
    eulerZetaProduct B z=familyKernel B z*normalizedZetaProduct B z := by
  classical
  unfold eulerZetaProduct familyKernel normalizedZetaProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro S hS
  rw [mul_zpow,← mul_assoc,← zpow_add₀ (hz S hS),neg_add_cancel,zpow_zero,one_mul]

theorem familyKernel_norm_polynomial {ι : Type*} [Fintype ι]
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (u : ι → ℝ)
    {U : ℝ} (hU : 0≤U) (hu : ∀ i, |u i|≤U) :
    ‖familyKernel B (fun i => frequencyW (u i))‖ ≤
      ((max (Fintype.card ι) 1:ℕ)*(1+U):ℝ)^B.card := by
  have hbase : (1:ℝ)≤(max (Fintype.card ι) 1:ℕ)*(1+U) := by
    have h : (1:ℝ)≤(max (Fintype.card ι) 1:ℕ) := by exact_mod_cast le_max_right _ _
    nlinarith
  rw [familyKernel,norm_prod]
  calc
    _ ≤ ∏ _S∈B, ((max (Fintype.card ι) 1:ℕ)*(1+U):ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro S hS
      rcases neg_one_pow_eq_or ℤ S.card with h | h
      · rw [h,zpow_neg_one,norm_inv]
        exact (inv_le_one_of_one_le₀ (frequencySum_norm_lower (hB S hS) u)).trans hbase
      · rw [h,neg_neg,zpow_one]
        apply (frequencySum_norm_upper S u (fun i _ => hu i)).trans
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (Finset.card_le_univ S).trans (le_max_left _ _)
    _ = _ := by simp

theorem normalizedZetaProduct_error {ι : Type*} (B : Finset (Finset ι)) (z : ι → ℂ)
    {c ε : ℝ} (hc : 0<c) (hε : 0≤ε)
    (hz : ∀ S∈B,
      ‖(∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i)-1‖≤c*ε ∧
      1/2≤‖(∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i)‖ ∧
      ‖(∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i)‖≤3/2) :
    ‖normalizedZetaProduct B z-1‖ ≤ 2^B.card*(B.card*(2*c*ε)) := by
  apply norm_prod_sub_one_le _ _ (by norm_num : (1:ℝ)≤2)
  · intro S hS
    rcases neg_one_pow_eq_or ℤ S.card with h | h
    · rw [h,zpow_one]
      linarith [(hz S hS).2.2]
    · rw [h,zpow_neg_one,norm_inv]
      exact (inv_le_comm₀ (by linarith [(hz S hS).2.1] :
        0<‖(∑ i∈S, z i)*riemannZeta (1+∑ i∈S, z i)‖) (by norm_num)).mpr
        (by simpa only [one_div] using (hz S hS).2.1)
  · intro S hS
    rcases neg_one_pow_eq_or ℤ S.card with h | h
    · rw [h,zpow_one]
      nlinarith [(hz S hS).1]
    · rw [h,zpow_neg_one]
      exact (norm_inv_sub_one_le (hz S hS).2.1).trans (by nlinarith [(hz S hS).1])

theorem eulerZeta_norm_contour_error :
    ∃ c>0, ∃ ε>0, ∀ {ι : Type*} [Fintype ι] (B : Finset (Finset ι)),
      (∀ S∈B, S.Nonempty) → ∀ u : ι → ℝ, ∀ {L U : ℝ}, 0<L → 0≤U →
      (∀ i, |u i|≤U) → (Fintype.card ι:ℝ)*(1+U)/L<ε →
      ‖normalizedZetaProduct B (fun i => frequencyW (u i)/(L:ℂ))-1‖ ≤
        2^B.card*(B.card*(2*c*((Fintype.card ι:ℝ)*(1+U)/L))) := by
  obtain ⟨c,hc,ε,hε,hpole⟩ := zeta_pole_two_sided
  refine ⟨c,hc,ε,hε,?_⟩
  intro ι _ B hB u L U hL hU hu hsmall
  apply normalizedZetaProduct_error B _ hc (by positivity)
  intro S hS
  have hsum : (∑ i∈S, frequencyW (u i)/(L:ℂ)) =
      (∑ i∈S, frequencyW (u i))/(L:ℂ) := (Finset.sum_div _ _ _).symm
  have hnz : (∑ i∈S, frequencyW (u i)/(L:ℂ))≠0 := by
    rw [hsum]
    exact div_ne_zero (frequencySum_ne_zero (hB S hS) u) (by exact_mod_cast hL.ne')
  have hn : ‖∑ i∈S, frequencyW (u i)/(L:ℂ)‖ ≤ (Fintype.card ι:ℝ)*(1+U)/L := by
    rw [hsum,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
    apply div_le_div_of_nonneg_right _ hL.le
    apply (frequencySum_norm_upper S u (fun i _ => hu i)).trans
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ S) (by positivity)
  have hp := hpole _ hnz (hn.trans_lt hsmall)
  exact ⟨hp.1.trans (mul_le_mul_of_nonneg_left hn hc.le), hp.2⟩

theorem eulerZetaProduct_scaled_factorization {ι : Type*}
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (u : ι → ℝ)
    {t : ℕ} (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) {L : ℝ} (hL : 0<L) :
    (L:ℂ)^t*eulerZetaProduct B (fun i => frequencyW (u i)/(L:ℂ)) =
      familyKernel B (fun i => frequencyW (u i))*
        normalizedZetaProduct B (fun i => frequencyW (u i)/(L:ℂ)) := by
  have hLc : (L:ℂ)≠0 := by exact_mod_cast hL.ne'
  have hnz : ∀ S∈B, ∑ i∈S, frequencyW (u i)/(L:ℂ)≠0 := by
    intro S hS
    rw [← Finset.sum_div]
    exact div_ne_zero (frequencySum_ne_zero (hB S hS) u) hLc
  have hk : familyKernel B (fun i => frequencyW (u i)/(L:ℂ)) =
      (L:ℂ)⁻¹^t*familyKernel B (fun i => frequencyW (u i)) := by
    simpa only [div_eq_mul_inv,mul_comm] using
      familyKernel_homogeneous B (fun i => frequencyW (u i)) (inv_ne_zero hLc) ht
  rw [eulerZetaProduct_factorization _ _ hnz,hk,inv_pow,← mul_assoc,← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero t hLc),one_mul]

theorem eulerZetaProduct_scaled_error {ι : Type*} (B : Finset (Finset ι))
    (hB : ∀ S∈B, S.Nonempty) (u : ι → ℝ) {t : ℕ}
    (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ)) {L : ℝ} (hL : 0<L) {E : ℝ}
    (hE : ‖normalizedZetaProduct B (fun i => frequencyW (u i)/(L:ℂ))-1‖≤E) :
    ‖(L:ℂ)^t*eulerZetaProduct B (fun i => frequencyW (u i)/(L:ℂ))-
      familyKernel B (fun i => frequencyW (u i))‖ ≤
        ‖familyKernel B (fun i => frequencyW (u i))‖*E := by
  rw [eulerZetaProduct_scaled_factorization B hB u ht hL,← mul_sub_one,norm_mul]
  exact mul_le_mul_of_nonneg_left hE (norm_nonneg _)

noncomputable def eulerGlobalMajorant (R y : ℕ) : ℝ :=
  Real.exp (4*R*primeReciprocalPrefix y+genericEulerConstant R/(y:ℝ))

theorem norm_eulerGlobal_le {ι : Type*} {δ : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι))
    (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) {y R : ℕ} (hy : 0<y)
    (hA : ∀ p : Nat.Primes, (A p).card≤R) (hB : B.card≤R)
    (hgen : ∀ p : Nat.Primes, y<(p:ℕ) → A p=B) :
    ‖eulerGlobal δ A B z‖ ≤ eulerGlobalMajorant R y := by
  have hf := eulerH_summable_error hδ A B z hz hy hgen
  have ht := norm_tprod_sub_one_le_exp (hf.subtype (fun p => p∉primePrefix y))
  have htail := eulerH_tail_sum hδ A B z hz hy hgen
  have hpref : ‖∏ p∈primePrefix y, eulerH p δ (A p) B z‖ ≤
      Real.exp (4*R*primeReciprocalPrefix y) := by
    rw [norm_prod]
    calc
      _ ≤ ∏ p∈primePrefix y, Real.exp (4*R*(p:ℝ)⁻¹) := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro p _
        apply (norm_eulerH_le p.property.two_le hδ (A p) B z hz).trans
        apply Real.exp_le_exp.mpr
        have haR : ((A p).card:ℝ)≤R := by exact_mod_cast hA p
        have hbR : (B.card:ℝ)≤R := by exact_mod_cast hB
        have hp0 : 0≤(p:ℝ)⁻¹ := by positivity
        nlinarith
      _ = _ := by rw [← Real.exp_sum]; congr 1; simp [primeReciprocalPrefix,Finset.mul_sum]
  have hn : ‖∏' p : {p : Nat.Primes // p∉primePrefix y}, eulerH p.val δ (A p.val) B z‖ ≤
      Real.exp (genericEulerConstant R/(y:ℝ)) := by
    have hh := norm_le_norm_sub_add (∏' p : {p : Nat.Primes // p∉primePrefix y},
      eulerH p.val δ (A p.val) B z) 1
    rw [norm_one] at hh
    have he : Real.exp (∑' p : {p : Nat.Primes // p∉primePrefix y},
      ‖eulerH p.val δ (A p.val) B z-1‖) ≤ Real.exp (genericEulerConstant R/(y:ℝ)) := by
      apply Real.exp_le_exp.mpr
      apply htail.trans
      exact div_le_div_of_nonneg_right (genericEulerConstant_mono hB) (by positivity)
    linarith
  unfold eulerGlobal
  rw [tprod_eq_prod_mul_tail (primePrefix y) hf,norm_mul]
  apply (mul_le_mul hpref hn (norm_nonneg _) (Real.exp_pos _).le).trans_eq
  exact (Real.exp_add _ _).symm

theorem tupleFourier_scaled_factorization {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι))
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R)
    (hB : ∀ S∈B, S.Nonempty) {y : ℕ} (hy : 0<y)
    (hgen : ∀ p : Nat.Primes, y<(p:ℕ) → A p=B)
    (u : ι → ℝ) {t : ℕ} (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ))
    {L : ℝ} (hL : 0<L) :
    (L:ℂ)^t*(∑' d : AllowedDivisorTuple A,
      tupleFourierCoefficient δ d.val (fun i => frequencyW (u i)/(L:ℂ))) =
      eulerGlobal δ A B (fun i => frequencyW (u i)/(L:ℂ))*
      familyKernel B (fun i => frequencyW (u i))*
      normalizedZetaProduct B (fun i => frequencyW (u i)/(L:ℂ)) := by
  have hz (i : ι) : (frequencyW (u i)/(L:ℂ)).re = 1/L := by
    simp [frequencyW,Complex.div_re]
  have hn (i : ι) : 0≤(frequencyW (u i)/(L:ℂ)).re := by rw [hz]; positivity
  have hH := multipliable_of_summable_norm_sub_one
    (eulerH_summable_error hδ A B _ hn hy hgen)
  rw [tupleFourier_eq_H_zeta hδ A B _ (by positivity : 0<1/L) hA hR
    (fun i => (hz i).ge) hB hH.hasProd]
  have he := eulerZetaProduct_scaled_factorization B hB u ht hL
  change (L:ℂ)^t*(eulerGlobal δ A B _*_) = _
  calc
    _ = eulerGlobal δ A B _*((L:ℂ)^t*eulerZetaProduct B _) := by ring
    _ = _ := by rw [he]; ring

theorem norm_mul_mul_sub_le {H H₀ K N : ℂ} {E M Z : ℝ}
    (hE : ‖H-H₀‖≤E) (hM : ‖H₀‖≤M) (hZ : ‖N-1‖≤Z) :
    ‖H*K*N-H₀*K‖ ≤ ‖K‖*(E*(1+Z)+M*Z) := by
  have he0 : 0≤E := (norm_nonneg _).trans hE
  have hM0 : 0≤M := (norm_nonneg _).trans hM
  have hN : ‖N‖≤1+Z := by
    have := norm_le_norm_sub_add N 1
    rw [norm_one] at this
    linarith
  calc
    _ = ‖K*((H-H₀)*N+H₀*(N-1))‖ := by congr 1; ring
    _ ≤ ‖K‖*(‖H-H₀‖*‖N‖+‖H₀‖*‖N-1‖) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (by
        simpa only [norm_mul] using (norm_add_le ((H-H₀)*N) (H₀*(N-1)))) (norm_nonneg _)
    _ ≤ _ := by gcongr

theorem tupleFourier_scaled_core_error :
    ∃ c>0, ∃ ε>0, ∀ {ι : Type*} [Fintype ι] {δ R : ℕ}, δ≤1 →
      ∀ (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι)),
      (∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty) →
      (∀ p : Nat.Primes, (A p).card≤R) →
      (∀ S∈B, S.Nonempty) → B.card≤R → ∀ {y : ℕ}, 2≤y →
      (∀ p : Nat.Primes, y<(p:ℕ) → A p=B) →
      ∀ (u : ι → ℝ) {t : ℕ}, (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ) →
      ∀ {L U s : ℝ}, 0<L → 0≤U → (∀ i, |u i|≤U) →
      (Fintype.card ι:ℝ)*(1+U)/L<ε →
      (∑ i, ‖frequencyW (u i)/(L:ℂ)‖)≤(y:ℝ)^(-s) →
      ‖(L:ℂ)^t*(∑' d : AllowedDivisorTuple A,
        tupleFourierCoefficient δ d.val (fun i => frequencyW (u i)/(L:ℂ))) -
        eulerGlobal δ A B (fun _ => 0)*familyKernel B (fun i => frequencyW (u i))‖ ≤
      ‖familyKernel B (fun i => frequencyW (u i))‖*
        (uniformEulerError R s y*(1+2^B.card*(B.card*(2*c*((Fintype.card ι:ℝ)*(1+U)/L))))+
         eulerGlobalMajorant R y*(2^B.card*(B.card*(2*c*((Fintype.card ι:ℝ)*(1+U)/L))))) := by
  obtain ⟨c,hc,ε,hε,hpole⟩ := eulerZeta_norm_contour_error
  refine ⟨c,hc,ε,hε,?_⟩
  intro ι _ δ R hδ A B hA hR hB hBR y hy hgen u t ht L U s hL hU hu hsmall hzsmall
  rw [tupleFourier_scaled_factorization hδ A B hA hR hB (by omega) hgen u ht hL]
  apply norm_mul_mul_sub_le
  · exact eulerGlobal_uniform_error hδ A B _
      (fun i => by simp [frequencyW,Complex.div_re]; positivity) hy hR hBR hgen hzsmall
  · exact norm_eulerGlobal_le hδ A B _ (by simp) (by omega) hR hBR hgen
  · exact hpole B hB u hL hU hu hsmall

noncomputable def contourKernel {ι : Type*} (B : Finset (Finset ι))
    (u : EuclideanSpace ℝ ι) : ℂ := familyKernel B (fun i => frequencyW (u i))

theorem continuous_contourKernel {ι : Type*} [Fintype ι]
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) : Continuous (contourKernel B) := by
  unfold contourKernel familyKernel
  apply continuous_finsetProd
  intro S hS
  apply Continuous.zpow₀
  · apply continuous_finsetSum
    intro i _
    unfold frequencyW
    fun_prop
  · intro u
    exact Or.inl (frequencySum_ne_zero (hB S hS) (fun i => u i))

theorem contourKernel_norm_polynomial {ι : Type*} [Fintype ι]
    (B : Finset (Finset ι)) (hB : ∀ S∈B, S.Nonempty) (u : EuclideanSpace ℝ ι) :
    ‖contourKernel B u‖ ≤ ((max (Fintype.card ι) 1:ℕ):ℝ)^B.card*
      2^(B.card-1)*(1+‖u‖^B.card) := by
  apply (familyKernel_norm_polynomial B hB (fun i => u i) (norm_nonneg _)
    (fun i => by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i)).trans
  rw [mul_pow,mul_assoc]
  gcongr
  simpa only [one_pow] using add_pow_le (by norm_num : (0:ℝ)≤1) (norm_nonneg u) B.card

theorem schwartz_integrable_polynomial_majorant {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (k : ℕ) :
    Integrable (fun u => ‖Φ u‖*(1+‖u‖^k)) := by
  have hi := Φ.integrable.norm.add (SchwartzMap.integrable_pow_mul volume Φ k)
  apply hi.congr
  filter_upwards [] with u
  dsimp; ring

end LargePrimeGaps

end OAI
