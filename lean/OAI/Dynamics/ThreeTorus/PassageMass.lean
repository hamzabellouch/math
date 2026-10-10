import OAI.Dynamics.ThreeTorus.StationaryPhase
import OAI.Dynamics.ThreeTorus.Twists

namespace OAI

/-! Actual Fourier passage coefficients, branch Jacobians, rounding removal, and integrated stationary mass. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology

namespace ThreeTorus

lemma continuous_fourierCoeff_param {Ω : Type*} [TopologicalSpace Ω]
    [FirstCountableTopology Ω] [LocallyCompactSpace Ω]
    {f : Ω → UnitAddCircle → ℂ} (hf : Continuous f.uncurry) (j : ℤ) :
    Continuous (fun a => fourierCoeff (f a) j) := by
  have hh : Continuous (fun p : Ω × UnitAddCircle => fourier (-j) p.2*f p.1 p.2) :=
    ((fourier (-j)).continuous.comp continuous_snd).mul hf
  simpa only [fourierCoeff,smul_eq_mul,setIntegral_univ] using
    (continuous_parametric_integral_of_continuous (μ := AddCircle.haarAddCircle)
      (f := fun a θ => fourier (-j) θ*f a θ) hh isCompact_univ)

/-- The precise old-amplitude Fourier coefficients in the passage chart. -/
def passageFourierInput (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (a θ : UnitAddCircle) : ℂ :=
  A (θ,a)*fourier m (H θ)

def exactPassageCoeff (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (j : ℤ) (a : UnitAddCircle) : ℂ :=
  fourierCoeff (passageFourierInput m H A a) j

def retainedPassage (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (S : Finset ℤ)
    (χ : ℤ → UnitAddCircle → ℝ) (ψ : UnitAddCircle → ℝ) (x : TripleTorus) : ℂ :=
  ∑ j ∈ S, (ψ x.2.1:ℂ)*(χ j x.2.1:ℂ)*exactPassageCoeff m H A j x.2.1*
    fourier m x.2.2*fourier j x.1

lemma continuous_passageFourierInput {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hH : Continuous H) (hA : Continuous A) :
    Continuous (passageFourierInput m H A).uncurry := by
  exact (hA.comp continuous_swap).mul ((fourier m).continuous.comp (hH.comp continuous_snd))

lemma continuous_exactPassageCoeff {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hH : Continuous H) (hA : Continuous A) (j : ℤ) :
    Continuous (exactPassageCoeff m H A j) :=
  continuous_fourierCoeff_param (continuous_passageFourierInput hH hA) j

lemma packet_in_passage_chart (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (x : TripleTorus) :
    packet m A ((passageChart H).symm x) =
      passageFourierInput m H A x.2.1 x.1*fourier m x.2.2 := by
  change A (x.1,x.2.1)*fourier m (x.2.2-(-H x.1)) =
    (A (x.1,x.2.1)*fourier m (H x.1))*fourier m x.2.2
  simp only [sub_neg_eq_add,fourier_apply,smul_add,AddCircle.toCircle_add,Circle.coe_mul]
  ring

lemma retainedPassage_error_norm (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (S : Finset ℤ)
    (χ : ℤ → UnitAddCircle → ℝ) (ψ : UnitAddCircle → ℝ) (x : TripleTorus) :
    ‖(ψ x.2.1:ℂ)*packet m A ((passageChart H).symm x)-
      retainedPassage m H A S χ ψ x‖^2 =
    ψ x.2.1^2*‖passageFourierInput m H A x.2.1 x.1-
      ∑ j ∈ S, (χ j x.2.1:ℂ)*exactPassageCoeff m H A j x.2.1*fourier j x.1‖^2 := by
  rw [packet_in_passage_chart]
  have he : (ψ x.2.1:ℂ)*
      (passageFourierInput m H A x.2.1 x.1*fourier m x.2.2)-
      retainedPassage m H A S χ ψ x =
      (ψ x.2.1:ℂ)*fourier m x.2.2*(passageFourierInput m H A x.2.1 x.1-
        ∑ j ∈ S, (χ j x.2.1:ℂ)*exactPassageCoeff m H A j x.2.1*fourier j x.1) := by
    unfold retainedPassage
    rw [mul_sub,Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j _; ring
  rw [he,norm_mul,norm_mul,show ‖fourier m x.2.2‖ = 1 from Circle.norm_coe _,mul_one,
    mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma integrated_retainedPassage_error {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hH : Continuous H) (hA : Continuous A)
    (S : Finset ℤ) (χ : ℤ → UnitAddCircle → ℝ) (hχ : ∀ j, Continuous (χ j))
    (ψ : UnitAddCircle → ℝ) (hψ : Continuous ψ) :
    (∫ x : TripleTorus,
      ‖(ψ x.2.1:ℂ)*packet m A ((passageChart H).symm x)-
        retainedPassage m H A S χ ψ x‖^2 ∂tripleVolume) =
    ∫ a : UnitAddCircle, ψ a^2*(∫ θ : UnitAddCircle,
      ‖passageFourierInput m H A a θ-
        ∑ j ∈ S, (χ j a:ℂ)*exactPassageCoeff m H A j a*fourier j θ‖^2
          ∂AddCircle.haarAddCircle) ∂AddCircle.haarAddCircle := by
  let E : UnitAddCircle → UnitAddCircle → ℝ := fun a θ => ψ a^2*
    ‖passageFourierInput m H A a θ-
      ∑ j ∈ S, (χ j a:ℂ)*exactPassageCoeff m H A j a*fourier j θ‖^2
  have hE : Continuous E.uncurry := by
    apply ((hψ.comp continuous_fst).pow 2).mul
    apply Continuous.pow
    apply Continuous.norm
    apply (continuous_passageFourierInput hH hA).sub
    apply continuous_finsetSum
    intro j _hj
    exact (((Complex.continuous_ofReal.comp (hχ j)).comp continuous_fst).mul
      ((continuous_exactPassageCoeff hH hA j).comp continuous_fst)).mul
      ((fourier j).continuous.comp continuous_snd)
  simp_rw [retainedPassage_error_norm]
  change (∫ x : TripleTorus, E x.2.1 x.1 ∂tripleVolume) = _
  have hit : Integrable (fun x : TripleTorus => E x.2.1 x.1) tripleVolume :=
    (hE.comp (continuous_snd.fst.prodMk continuous_fst)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_prod _ hit]
  have hinner (θ : UnitAddCircle) :
      (∫ p : UnitAddCircle × UnitAddCircle, E p.1 θ ∂slowVolume) =
        ∫ a : UnitAddCircle, E a θ ∂AddCircle.haarAddCircle := by
    rw [integral_prod]
    · simp
    · exact (hE.comp (continuous_fst.prodMk continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  simp_rw [hinner]
  rw [integral_integral_swap]
  · congr 1; funext a
    exact integral_const_mul _ _
  · exact (hE.comp continuous_swap).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end ThreeTorus

namespace ThreeTorus

/-- The exact torus coefficient as a compactly supported real oscillatory integral.
The support hypothesis is the lifted good-arc support, not a Fourier approximation. -/
lemma exactPassageCoeff_real_integral {m j : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} {a : UnitAddCircle} {o : ℝ}
    {H₀ : ℝ → ℝ} {A₀ : ℝ → ℂ}
    (hH : ∀ x : ℝ, H (x : UnitAddCircle) = (H₀ x : UnitAddCircle))
    (hA : ∀ x ∈ Ioc o (o+1), A ((x : UnitAddCircle),a) = A₀ x)
    (hAs : Function.support A₀ ⊆ Ioc o (o+1)) :
    exactPassageCoeff m H A j a =
      ∫ x : ℝ, A₀ x*Complex.exp (Complex.I*((2*Real.pi*((m:ℝ)*H₀ x-j*x)):ℝ)) := by
  unfold exactPassageCoeff
  rw [fourierCoeff_eq_intervalIntegral _ _ o]
  simp only [one_div,inv_one,one_smul]
  have he (x : ℝ) (hx : x ∈ Ioc o (o+1)) :
      fourier (-j) (x : UnitAddCircle) • passageFourierInput m H A a (x : UnitAddCircle) =
        A₀ x*Complex.exp (Complex.I*((2*Real.pi*((m:ℝ)*H₀ x-j*x)):ℝ)) := by
    simp only [passageFourierInput,hA x hx,hH x,smul_eq_mul,fourier_coe_apply]
    simp only [Complex.ofReal_one,div_one,Int.cast_neg]
    rw [show Complex.exp (2*Real.pi*Complex.I*(-(j:ℂ))*(x:ℂ))*
        (A₀ x*Complex.exp (2*Real.pi*Complex.I*(m:ℂ)*(H₀ x:ℂ))) =
        A₀ x*(Complex.exp (2*Real.pi*Complex.I*(-(j:ℂ))*(x:ℂ))*
          Complex.exp (2*Real.pi*Complex.I*(m:ℂ)*(H₀ x:ℂ))) by ring,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring
  calc
    _ = ∫ x in o..o+1, A₀ x*Complex.exp (Complex.I*((2*Real.pi*((m:ℝ)*H₀ x-j*x)):ℝ)) := by
      rw [intervalIntegral.integral_of_le (by linarith : o ≤ o+1),
        intervalIntegral.integral_of_le (by linarith : o ≤ o+1)]
      exact setIntegral_congr_fun measurableSet_Ioc he
    _ = _ := intervalIntegral.integral_eq_integral_of_support_subset (by
      intro x hx
      exact hAs (mul_ne_zero_iff.mp hx).1)

/-- No approximation occurs when the rounded primitive is inserted in the phase.
This is the normalization needed by the compact-support stationary-phase proof. -/
lemma rounded_phase_normalization (m j : ℤ) {n : ℕ} (hn : n ≠ 0)
    (P : ℝ → ℝ) (δ : ℕ → ℝ) (x : ℝ) :
    2*Real.pi*((m:ℝ)*((n:ℝ)*(P x+δ n*x))-(j:ℝ)*x) =
      (n:ℝ)*((2*Real.pi*(m:ℝ)*P x)-
        ((2*Real.pi)*(j:ℝ)/(n:ℝ)-(2*Real.pi*(m:ℝ)*δ n))*x) := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp
  ring

end ThreeTorus

namespace ThreeTorus

lemma continuous_compact_phase_integral {Ω : Type*} [TopologicalSpace Ω]
    [FirstCountableTopology Ω] [LocallyCompactSpace Ω]
    {A : Ω → ℝ → ℂ} {Φ : ℝ → ℝ} {l u : ℝ}
    (hA : Continuous A.uncurry) (hΦ : Continuous Φ) (hlu : l ≤ u)
    (hs : ∀ a, Function.support (A a) ⊆ Ioc l u) (t : ℝ) :
    Continuous (fun a => ∫ x, A a x*Complex.exp (Complex.I*((t*Φ x):ℝ))) := by
  have hf : Continuous (fun p : Ω × ℝ => A p.1 p.2*Complex.exp (Complex.I*((t*Φ p.2):ℝ))) := by
    fun_prop
  have hh := continuous_parametric_integral_of_continuous
    (μ := (volume : Measure ℝ)) (f := fun a x => A a x*Complex.exp (Complex.I*((t*Φ x):ℝ)))
    hf (isCompact_Icc (a := l) (b := u))
  have he (a : Ω) : (∫ x in Icc l u, A a x*Complex.exp (Complex.I*((t*Φ x):ℝ))) =
      ∫ x, A a x*Complex.exp (Complex.I*((t*Φ x):ℝ)) := by
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hlu]
    exact intervalIntegral_phase_of_support (hs a) Φ t
  simpa only [he] using hh

lemma continuous_passageCoefficient {A : UnitAddCircle → ℝ → ℂ} {Φ : ℝ → ℝ}
    {l u : ℝ} (hA : Continuous A.uncurry) (hΦ : Continuous Φ) (hlu : l ≤ u)
    (hs : ∀ a, Function.support (A a) ⊆ Ioc l u)
    (κ : ℝ) (α : ℕ → ℝ) (n : ℕ) (j : ℤ) :
    Continuous (passageCoefficient Φ A κ α n j) :=
  continuous_compact_phase_integral hA (hΦ.sub (continuous_const.mul continuous_id)) hlu hs n

lemma continuous_passageLeading {A : UnitAddCircle → ℝ → ℂ} {Φ : ℝ → ℝ}
    (hA : Continuous A.uncurry) (l u R κ : ℝ) (α : ℕ → ℝ) (n : ℕ) (j : ℤ) :
    Continuous (passageLeading Φ A l u R κ α n j) := by
  unfold passageLeading stationaryLeading
  split_ifs
  · fun_prop
  · exact continuous_const

/-- Strong summed stationary mass for the actual torus passage coefficients.
All integrability in the slow parameter is derived from compact smooth data. -/
lemma exactPassageCoeff_summed_mass
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {P : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R d D C₀ C₁ M M₁ C : ℝ}
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(P x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hsupp : ∀ a, Function.support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u)
    (hΦ : ContDiff ℝ 3 (fun x => 2*Real.pi*(m:ℝ)*P x))
    (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M) (hM₁ : 0 ≤ M₁) (hC : 0 ≤ C)
    (hδ : ∀ n, |2*Real.pi*(m:ℝ)*δ n| ≤ C)
    (hfirst : ∀ x ∈ Icc (l-2*R) (u+2*R), |deriv (fun x => 2*Real.pi*(m:ℝ)*P x) x| ≤ M₁)
    (hsecond : ∀ x ∈ Icc (l-2*R) (u+2*R), d ≤ iteratedDeriv 2 (fun x => 2*Real.pi*(m:ℝ)*P x) x)
    (hupper : ∀ x ∈ Icc (l-2*R) (u+2*R), iteratedDeriv 2 (fun x => 2*Real.pi*(m:ℝ)*P x) x ≤ D)
    (hM : ∀ x ∈ Icc (l-2*R) (u+2*R), |iteratedDeriv 3 (fun x => 2*Real.pi*(m:ℝ)*P x) x| ≤ M)
    (hAb : ∀ a x, x ∈ Icc (l-2*R) (u+2*R) → ‖A₀ a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (l-2*R) (u+2*R) → ‖deriv (A₀ a) x‖ ≤ C₁) :
    Tendsto (fun n : ℕ => ∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖exactPassageCoeff m (H n) A j a‖^2-
        (n:ℝ)⁻¹*‖passageLeading (fun x => 2*Real.pi*(m:ℝ)*P x) A₀ l u R (2*Real.pi)
          (fun n => 2*Real.pi*(m:ℝ)*δ n) n j a‖^2| ∂AddCircle.haarAddCircle)
      atTop (𝓝 0) := by
  let Φ : ℝ → ℝ := fun x => 2*Real.pi*(m:ℝ)*P x
  let α : ℕ → ℝ := fun n => 2*Real.pi*(m:ℝ)*δ n
  have hi (n : ℕ) (j : ℤ) : Integrable (fun a =>
      |‖passageCoefficient Φ A₀ (2*Real.pi) α n j a‖^2-
        (n:ℝ)⁻¹*‖passageLeading Φ A₀ l u R (2*Real.pi) α n j a‖^2|)
      AddCircle.haarAddCircle := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (((continuous_passageCoefficient hAc hΦ.continuous hlu hsupp _ _ n j).norm.pow 2).sub
      ((continuous_const.mul ((continuous_passageLeading hAc l u R _ α n j).norm.pow 2)))).abs
  have ht := passage_summed_mass (μ := AddCircle.haarAddCircle) hΦ hA₀ hlu hR hd hdD
    hC₀ hC₁ hM₀ hM₁ hC (by positivity : 0 < 2*Real.pi) hδ
    hfirst hsecond hupper hM hAb hA'b hsupp hi
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  congr 1; funext j
  apply integral_congr_ae
  filter_upwards [] with a
  have hs : Function.support (A₀ a) ⊆ Ioc o (o+1) :=
    (hsupp a).trans (Ioc_subset_Ioc hlo huo)
  have he := exactPassageCoeff_real_integral (m := m) (j := j) (H := H n) (A := A)
    (a := a) (hH n) (hA a) hs
  rw [he]
  congr 3
  unfold passageCoefficient passageSlope
  apply congrArg norm
  apply integral_congr_ae
  filter_upwards [] with x
  rw [rounded_phase_normalization m j (by omega : n ≠ 0) P δ x]

open Function
/-- Zero-extended Jacobian density on a single injective good arc. -/
def branchDensity (I : Set ℝ) (J g D q : ℝ → ℝ) (y : ℝ) : ℝ :=
  (J '' I).indicator (fun y => q (g y)/|D (g y)|) y

lemma branchDensity_on {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hg : ∀ x ∈ I, g (J x) = x) {x : ℝ} (hx : x ∈ I) :
    branchDensity I J g D q (J x) = q x/|D x| := by
  simp only [branchDensity,indicator_of_mem (mem_image_of_mem J hx),hg x hx]

/-- The normalized physical-frequency mass used in (W-definition). -/
def stationaryWeight (I : Set ℝ) (J : ℝ → ℝ) (A : ℝ → ℂ) : ℝ → ℝ :=
  branchDensity I J (invFunOn J I) (deriv J) (fun u => ‖A u‖^2)

lemma stationaryLeading_norm_sq_weight {Φ J : ℝ → ℝ} {A : ℝ → ℂ} {l u : ℝ}
    (hΦ : ContDiff ℝ 2 Φ) (hJ : Continuous J) (hlu : l ≤ u)
    (hfirst : ∀ x, deriv Φ x = 2*Real.pi*J x)
    (hsecond : ∀ x, iteratedDeriv 2 Φ x = 2*Real.pi*deriv J x)
    (hpos : ∀ x ∈ Icc l u, 0 < deriv J x) (s t : ℝ) :
    ‖stationaryLeading Φ A l u (2*Real.pi*s) t‖^2 = stationaryWeight (Icc l u) J A s := by
  have hk : 0 < 2*Real.pi := by positivity
  have hmono : StrictMonoOn J (Icc l u) := strictMonoOn_of_deriv_pos (convex_Icc _ _)
    hJ.continuousOn (fun x hx => hpos x (interior_subset hx))
  have himage : J '' Icc l u = Icc (J l) (J u) :=
    hJ.continuousOn.image_Icc_of_monotoneOn hlu hmono.monotoneOn
  have hsiff : 2*Real.pi*s ∈ Icc (deriv Φ l) (deriv Φ u) ↔ s ∈ J '' Icc l u := by
    rw [hfirst l,hfirst u,himage]
    simp only [mem_Icc,mul_le_mul_iff_right₀ hk]
  by_cases hs : s ∈ J '' Icc l u
  · have hsΦ := hsiff.mpr hs
    let v := invFunOn J (Icc l u) s
    have hv : v ∈ Icc l u := (invFunOn_pos hs).1
    have hvJ : J v = s := (invFunOn_pos hs).2
    have hw := stationary_branch_center hΦ hlu hsΦ
    have hinv : invFunOn (deriv Φ) (Icc l u) (2*Real.pi*s) = v := by
      apply hmono.injOn hw.1 hv
      rw [hfirst] at hw
      exact (mul_left_cancel₀ hk.ne' hw.2).trans hvJ.symm
    have hp := hpos v hv
    have hb : iteratedDeriv 2 Φ v/(2*Real.pi) = deriv J v := by
      rw [hsecond]
      field_simp
    rw [norm_stationaryLeading hsΦ,hinv,hb,mul_pow,inv_pow,Real.sq_sqrt hp.le]
    simp only [stationaryWeight,branchDensity,indicator_of_mem hs,abs_of_pos hp,v]
    ring
  · have hsΦ := mt hsiff.mp hs
    simp only [stationaryLeading,ite_eq_right hsΦ,norm_zero,zero_pow (by norm_num : 2 ≠ 0),
      stationaryWeight,branchDensity,indicator_of_notMem hs]

/-- Normalization of the phase derivative agrees exactly with the old speed.
This computes the manuscript's W under the ordinary derivative identity P'=V. -/
lemma phase_speed_derivatives {P V : ℝ → ℝ} {m : ℝ}
    (hP : Differentiable ℝ P) (hV : Differentiable ℝ V) (hPV : deriv P = V) :
    (∀ x, deriv (fun x => 2*Real.pi*m*P x) x = 2*Real.pi*(m*V x)) ∧
    (∀ x, iteratedDeriv 2 (fun x => 2*Real.pi*m*P x) x =
      2*Real.pi*deriv (fun x => m*V x) x) := by
  have hd : deriv (fun x => 2*Real.pi*m*P x) = fun x => 2*Real.pi*m*V x := by
    funext x
    rw [deriv_const_mul (2*Real.pi*m) (hP x),hPV]
  refine ⟨fun x => by rw [hd]; ring,?_⟩
  intro x
  simp only [iteratedDeriv_succ,iteratedDeriv_zero,hd]
  rw [deriv_const_mul (2*Real.pi*m) (hV x),deriv_const_mul m (hV x)]
  ring

/-- Summed stationary mass in the manuscript's actual normalization W, without
an auxiliary complex leading array remaining in the conclusion. -/
lemma exactPassageCoeff_summed_weight
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {P V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R d D C₀ C₁ M M₁ C : ℝ}
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(P x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hsupp : ∀ a, Function.support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u)
    (hΦ : ContDiff ℝ 3 (fun x => 2*Real.pi*(m:ℝ)*P x))
    (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M) (hM₁ : 0 ≤ M₁) (hC : 0 ≤ C)
    (hδ : ∀ n, |2*Real.pi*(m:ℝ)*δ n| ≤ C)
    (hfirst : ∀ x ∈ Icc (l-2*R) (u+2*R), |deriv (fun x => 2*Real.pi*(m:ℝ)*P x) x| ≤ M₁)
    (hsecond : ∀ x ∈ Icc (l-2*R) (u+2*R), d ≤ iteratedDeriv 2 (fun x => 2*Real.pi*(m:ℝ)*P x) x)
    (hupper : ∀ x ∈ Icc (l-2*R) (u+2*R), iteratedDeriv 2 (fun x => 2*Real.pi*(m:ℝ)*P x) x ≤ D)
    (hM : ∀ x ∈ Icc (l-2*R) (u+2*R), |iteratedDeriv 3 (fun x => 2*Real.pi*(m:ℝ)*P x) x| ≤ M)
    (hAb : ∀ a x, x ∈ Icc (l-2*R) (u+2*R) → ‖A₀ a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (l-2*R) (u+2*R) → ‖deriv (A₀ a) x‖ ≤ C₁) 
    (hP : Differentiable ℝ P) (hV : Differentiable ℝ V) (hPV : deriv P = V) :

    Tendsto (fun n : ℕ => ∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖exactPassageCoeff m (H n) A j a‖^2-
        (n:ℝ)⁻¹*stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
          (A₀ a) ((j:ℝ)/n-(m:ℝ)*δ n)| ∂AddCircle.haarAddCircle)
      atTop (𝓝 0) := by
  have he := phase_speed_derivatives (m := (m:ℝ)) hP hV hPV
  have hi : Icc (l-R) (u+R) ⊆ Icc (l-2*R) (u+2*R) := by
    apply Icc_subset_Icc <;> linarith
  have hpos (x : ℝ) (hx : x ∈ Icc (l-R) (u+R)) :
      0 < deriv (fun x => (m:ℝ)*V x) x := by
    have hh := hsecond x (hi hx)
    rw [he.2 x] at hh
    have hk : 0 < 2*Real.pi := by positivity
    nlinarith
  have hweight (n : ℕ) (j : ℤ) (a : UnitAddCircle) :
      ‖passageLeading (fun x => 2*Real.pi*(m:ℝ)*P x) A₀ l u R (2*Real.pi)
        (fun n => 2*Real.pi*(m:ℝ)*δ n) n j a‖^2 =
      stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a)
        ((j:ℝ)/n-(m:ℝ)*δ n) := by
    unfold passageLeading passageSlope
    have hs : 2*Real.pi*(j:ℝ)/(n:ℝ)-2*Real.pi*(m:ℝ)*δ n =
        2*Real.pi*((j:ℝ)/n-(m:ℝ)*δ n) := by ring
    rw [hs]
    exact stationaryLeading_norm_sq_weight (hΦ.of_le (by norm_num))
      (continuous_const.mul hV.continuous) (by linarith) he.1 he.2 hpos _ _
  have hh := exactPassageCoeff_summed_mass hH hA hA₀ hAc hsupp hlo huo hlu
    hΦ hR hd hdD hC₀ hC₁ hM₀ hM₁ hC hδ hfirst hsecond hupper hM hAb hA'b
  simp_rw [hweight] at hh
  exact hh

lemma continuous_fourier_summable {f : UnitAddCircle → ℂ} (hf : Continuous f) :
    Summable (fun j : ℤ => ‖fourierCoeff f j‖^2) := by
  let F : C(UnitAddCircle,ℂ) := ⟨f,hf⟩
  have hh := (hasSum_sq_fourierCoeff (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ F)).summable
  simpa only [fourierCoeff_toLp, F, ContinuousMap.coe_mk] using hh

/-- The integrated Fourier masses really are summable, so no use of a default
zero value of a divergent tsum is possible in the passage estimates. -/
lemma continuous_family_fourier_summable {f : UnitAddCircle → UnitAddCircle → ℂ}
    (hf : Continuous f.uncurry) :
    Summable (fun j : ℤ => ∫ a : UnitAddCircle, ‖fourierCoeff (f a) j‖^2
      ∂AddCircle.haarAddCircle) := by
  have hfi (a : UnitAddCircle) : Continuous (f a) := hf.comp (continuous_const.prodMk continuous_id)
  have hj (j : ℤ) : Integrable (fun a => ‖fourierCoeff (f a) j‖^2) AddCircle.haarAddCircle :=
    ((continuous_fourierCoeff_param hf j).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hec : Continuous (fun a : UnitAddCircle => ∫ θ : UnitAddCircle, ‖f a θ‖^2
      ∂AddCircle.haarAddCircle) := by
    simpa only [setIntegral_univ] using
      (continuous_parametric_integral_of_continuous (μ := AddCircle.haarAddCircle)
        (f := fun a θ => ‖f a θ‖^2) (by exact hf.norm.pow 2) isCompact_univ)
  have hei := hec.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  apply summable_of_sum_le (c := ∫ a : UnitAddCircle,
    (∫ θ : UnitAddCircle, ‖f a θ‖^2 ∂AddCircle.haarAddCircle) ∂AddCircle.haarAddCircle)
  · intro j
    exact integral_nonneg (fun _ => sq_nonneg _)
  · intro S
    rw [← integral_finsetSum _ (fun j _ => hj j)]
    apply integral_mono (integrable_finsetSum S (fun j _ => hj j)) hei
    intro a
    dsimp only
    rw [← continuous_fourier_parseval (hfi a)]
    exact (continuous_fourier_summable (hfi a)).sum_le_tsum S (fun _ _ => sq_nonneg _)

lemma exactPassageCoeff_summable {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hH : Continuous H) (hA : Continuous A) :
    Summable (fun j : ℤ => ∫ a : UnitAddCircle, ‖exactPassageCoeff m H A j a‖^2
      ∂AddCircle.haarAddCircle) := by
  exact continuous_family_fourier_summable (continuous_passageFourierInput hH hA)

lemma contDiffAt_invFunOn_of_deriv_ne_zero {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hIo : IsOpen I) (hinj : InjOn J I) {x d : ℝ} (hx : x ∈ I)
    (hd : HasDerivAt J d x) (hd0 : d ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (invFunOn J I) (J x) := by
  let e := hJ.contDiffAt.toOpenPartialHomeomorph J (hd.hasFDerivAt_equiv hd0) (by simp)
  have he : (e : ℝ → ℝ) = J := rfl
  have hxs : x ∈ e.source := hJ.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hd.hasFDerivAt_equiv hd0) (by simp)
  have hyt : J x ∈ e.target := by simpa only [he] using e.map_source hxs
  have hix : e.symm (J x) = x := by simpa only [he] using e.left_inv hxs
  have hi : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) e.symm (J x) := by
    apply e.contDiffAt_symm_deriv hd0 hyt
    · simpa only [he,hix] using hd
    · simpa only [he,hix] using hJ.contDiffAt (x := x)
  have hnear : ∀ᶠ y in 𝓝 (J x), e.symm y ∈ I := by
    apply hi.continuousAt.eventually
    change I ∈ 𝓝 (e.symm (J x))
    rw [hix]
    exact hIo.mem_nhds hx
  apply hi.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hyt,hnear] with y hy hyI
  have hr : J (e.symm y) = y := by simpa only [he] using e.right_inv hy
  have hp := invFunOn_pos (show y ∈ J '' I from ⟨e.symm y,hyI,hr⟩)
  exact hinj hp.1 hyI (hp.2.trans hr.symm)

lemma isOpen_image_of_deriv_ne_zero {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hIo : IsOpen I) (hd : ∀ x ∈ I, deriv J x ≠ 0) : IsOpen (J '' I) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x,hx,rfl⟩
  have hdx := (hJ.differentiable (by simp) x).hasDerivAt
  let e := hJ.contDiffAt.toOpenPartialHomeomorph J (hdx.hasFDerivAt_equiv (hd x hx)) (by simp)
  have he : (e : ℝ → ℝ) = J := rfl
  have hxs : x ∈ e.source := hJ.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hdx.hasFDerivAt_equiv (hd x hx)) (by simp)
  have hyt : J x ∈ e.target := by simpa only [he] using e.map_source hxs
  have hix : e.symm (J x) = x := by simpa only [he] using e.left_inv hxs
  have hnear : ∀ᶠ y in 𝓝 (J x), e.symm y ∈ I := by
    apply (e.continuousAt_symm hyt).eventually
    change I ∈ 𝓝 (e.symm (J x))
    rw [hix]
    exact hIo.mem_nhds hx
  filter_upwards [e.open_target.mem_nhds hyt,hnear] with y hy hyI
  exact ⟨e.symm y,hyI,by simpa only [he] using e.right_inv hy⟩

/-- The branch Jacobian with an arbitrary compact slow parameter space. -/
def branchFamily {Ω : Type*} (I : Set ℝ) (J : ℝ → ℝ) (F : ℝ × Ω → ℝ)
    (p : ℝ × Ω) : ℝ := by
  classical
  exact if p.1 ∈ J '' I then F (invFunOn J I p.1,p.2)/|deriv J (invFunOn J I p.1)| else 0

lemma support_branchFamily_subset {Ω : Type*} [TopologicalSpace Ω]
    {I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × Ω → ℝ} :
    support (branchFamily I J F) ⊆ (fun p : ℝ × Ω => (J p.1,p.2)) '' tsupport F := by
  rintro ⟨s,a⟩ hh
  have hs : s ∈ J '' I := by
    by_contra hn
    exact hh (by simp [branchFamily,hn])
  have hp := invFunOn_pos hs
  refine ⟨(invFunOn J I s,a),subset_tsupport F ?_,?_⟩
  · intro hz
    exact hh (by simp [branchFamily,hs,hz])
  · simp only [hp.2]

lemma branchFamily_compact {Ω : Type*} [TopologicalSpace Ω] [T2Space Ω]
    {I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × Ω → ℝ}
    (hJ : Continuous J) (hc : HasCompactSupport F) : HasCompactSupport (branchFamily I J F) := by
  apply HasCompactSupport.intro (hc.image (by fun_prop : Continuous (fun p : ℝ × Ω => (J p.1,p.2))))
  intro p hp
  by_contra hn
  exact hp (support_branchFamily_subset hn)

lemma branchFamily_continuous {Ω : Type*} [TopologicalSpace Ω] [T2Space Ω]
    {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × Ω → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hF : Continuous F) (hc : HasCompactSupport F) (hs : tsupport F ⊆ I ×ˢ univ) :
    Continuous (branchFamily I J F) := by
  classical
  let g := invFunOn J I
  let M := (fun p : ℝ × Ω => (J p.1,p.2)) '' tsupport F
  have hM : IsCompact M := hc.image (by fun_prop)
  have hzero {p : ℝ × Ω} (hp : p ∉ M) : branchFamily I J F p = 0 :=
    notMem_support.mp (fun hn => hp (support_branchFamily_subset hn))
  have hD : Continuous (deriv J) := hJ.continuous_deriv (by simp)
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p ∈ M
  · rcases hp with ⟨⟨x,a⟩,hx,rfl⟩
    have hxI : x ∈ I := (hs hx).1
    have hy : J x ∈ J '' I := mem_image_of_mem J hxI
    have hgi := (contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hxI
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hxI)).continuousAt
    have hge : g (J x) = x := by
      exact hinj (invFunOn_pos hy).1 hxI (invFunOn_pos hy).2
    have hgi' : ContinuousAt (fun p : ℝ × Ω => g p.1) (J x,a) :=
      hgi.comp_of_eq continuousAt_fst rfl
    have hin : ContinuousAt (fun p : ℝ × Ω => (g p.1,p.2)) (J x,a) :=
      hgi'.prodMk continuousAt_snd
    have hDen : ContinuousAt (fun p : ℝ × Ω => |deriv J (g p.1)|) (J x,a) :=
      (hD.continuousAt.comp hgi').abs
    have hquot : ContinuousAt (fun p : ℝ × Ω => F (g p.1,p.2) / |deriv J (g p.1)|) (J x,a) := by
      apply (hF.continuousAt.comp hin).div hDen
      simpa only [hge] using abs_ne_zero.mpr (hd x hxI)
    apply hquot.congr_of_eventuallyEq
    have hnear : ∀ᶠ p : ℝ × Ω in 𝓝 (J x,a), p.1 ∈ J '' I :=
      continuous_fst.continuousAt.eventually ((isOpen_image_of_deriv_ne_zero hJ hIo hd).mem_nhds hy)
    filter_upwards [hnear] with p hp
    simp only [branchFamily,ite_eq_left hp,g]
  · apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hM.isClosed.isOpen_compl.mem_nhds hp] with q hq
    exact hzero hq

lemma branchFamily_congr_branch {Ω : Type*} {C I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × Ω → ℝ}
    (hIC : I ⊆ C) (hinj : InjOn J C) (hs : support F ⊆ I ×ˢ univ) :
    branchFamily C J F = branchFamily I J F := by
  classical
  funext p
  have him : J '' I ⊆ J '' C := image_mono hIC
  by_cases hp : p.1 ∈ J '' C
  · have hc := invFunOn_pos hp
    by_cases hpi : p.1 ∈ J '' I
    · have hi := invFunOn_pos hpi
      have hinv : invFunOn J C p.1 = invFunOn J I p.1 :=
        hinj hc.1 (hIC hi.1) (hc.2.trans hi.2.symm)
      simp [branchFamily,hp,hpi,hinv]
    · have hz : F (invFunOn J C p.1,p.2) = 0 := by
        by_contra hn
        exact hpi ⟨_, (hs hn).1, hc.2⟩
      simp [branchFamily,hp,hpi,hz]
  · have hpi : p.1 ∉ J '' I := fun h => hp (him h)
    simp [branchFamily,hp,hpi]

lemma branchFamily_bound_first {Ω : Type*} [TopologicalSpace Ω] [T2Space Ω]
    {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × Ω → ℝ}
    (hJ : Continuous J) (hc : HasCompactSupport F) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s a, A < |s| → branchFamily I J F (s,a) = 0 := by
  have hC := branchFamily_compact (I := I) hJ hc
  obtain ⟨R,hR⟩ := (hC.image continuous_fst).isBounded.subset_closedBall (0 : ℝ)
  refine ⟨max R 0,le_max_right _ _,?_⟩
  intro s a hs
  by_contra hn
  have hh := hR ⟨(s,a),subset_tsupport _ hn,rfl⟩
  rw [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs] at hh
  exact (not_lt_of_ge (hh.trans (le_max_left _ _))) hs

lemma stationaryWeight_family_eq (C : Set ℝ) (J : ℝ → ℝ)
    (A : UnitAddCircle → ℝ → ℂ) :
    (fun p : ℝ × UnitAddCircle => stationaryWeight C J (A p.2) p.1) =
      branchFamily C J (fun p : ℝ × UnitAddCircle => ‖A p.2 p.1‖^2) := by
  classical
  funext p
  by_cases hp : p.1 ∈ J '' C <;> simp [stationaryWeight,branchDensity,branchFamily,hp]

/-- Joint compact continuity of the exact density used in stationary phase.
The enlarged stationary branch creates no boundary discontinuity because the
original packet is supported in the strictly smaller closed interval. -/
lemma stationaryWeight_compact_continuous {J : ℝ → ℝ}
    {A : UnitAddCircle → ℝ → ℂ} {l u R : ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hA : Continuous A.uncurry) (hs : ∀ a, support (A a) ⊆ Icc l u)
    (hR : 0 < R) (hd : ∀ x ∈ Icc (l-R) (u+R), 0 < deriv J x) :
    Continuous (fun p : ℝ × UnitAddCircle => stationaryWeight (Icc (l-R) (u+R)) J (A p.2) p.1) ∧
    HasCompactSupport (fun p : ℝ × UnitAddCircle => stationaryWeight (Icc (l-R) (u+R)) J (A p.2) p.1) := by
  let F : ℝ × UnitAddCircle → ℝ := fun p => ‖A p.2 p.1‖^2
  have hF : Continuous F := (hA.comp (continuous_snd.prodMk continuous_fst)).norm.pow 2
  have hFs : support F ⊆ Icc l u ×ˢ (univ : Set UnitAddCircle) := by
    intro p hp
    refine ⟨hs p.2 ?_,mem_univ _⟩
    by_contra hn
    have hz : A p.2 p.1 = 0 := notMem_support.mp hn
    exact hp (by simp [F,hz])
  have hFt : tsupport F ⊆ Icc l u ×ˢ (univ : Set UnitAddCircle) :=
    closure_minimal hFs (isClosed_Icc.prod isClosed_univ)
  have hc : HasCompactSupport F :=
    (isCompact_Icc.prod isCompact_univ).of_isClosed_subset (isClosed_tsupport F) hFt
  let C := Icc (l-R) (u+R)
  let I := Ioo (l-R) (u+R)
  have hIC : I ⊆ C := Ioo_subset_Icc_self
  have hinj : InjOn J C := (strictMonoOn_of_deriv_pos (convex_Icc _ _)
    hJ.continuous.continuousOn (fun x hx => hd x (interior_subset hx))).injOn
  have hsub : Icc l u ⊆ I := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hFtI : tsupport F ⊆ I ×ˢ (univ : Set UnitAddCircle) :=
    fun p hp => ⟨hsub (hFt hp).1,mem_univ _⟩
  have he := branchFamily_congr_branch hIC hinj (subset_trans subset_closure hFtI)
  rw [stationaryWeight_family_eq]
  change Continuous (branchFamily C J F) ∧ HasCompactSupport (branchFamily C J F)
  refine ⟨?_,branchFamily_compact hJ.continuous hc⟩
  rw [he]
  exact branchFamily_continuous hJ isOpen_Ioo (hinj.mono hIC)
    (fun x hx => (hd x (hIC hx)).ne') hF hc hFtI

open scoped NNReal
def roundingMass (W : ℝ → UnitAddCircle → ℝ) (n : ℕ) (e : ℝ) : ℝ :=
  (n:ℝ)⁻¹ * ∑' j : ℤ, ∫ a : UnitAddCircle,
    |W ((j:ℝ)/n-e) a-W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle

lemma roundingMass_bound {W : ℝ → UnitAddCircle → ℝ} {A C e : ℝ} {L : ℝ≥0} {K n : ℕ}
    (hW : Continuous W.uncurry) (hLip : ∀ a, LipschitzWith L (fun s => W s a))
    (hs : ∀ s a, A < |s| → W s a = 0)
    (he : |e| ≤ C) (hK : A+C ≤ K) (hn : 0 < n) :
    roundingMass W n e ≤ (2*(K:ℝ)+1)*L*|e| := by
  classical
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hC : 0 ≤ C := (abs_nonneg e).trans he
  let S : Finset ℤ := Finset.Icc (-(K*n:ℤ)) (K*n)
  have hz (j : ℤ) (hj : j ∉ S) (a : UnitAddCircle) :
      |W ((j:ℝ)/n-e) a-W ((j:ℝ)/n) a| = 0 := by
    have hj' : (K:ℝ)*n < |(j:ℝ)| := by
      have hh : (K*n:ℤ) < |j| := by
        simpa only [S,Finset.mem_Icc,← abs_le,not_le] using hj
      exact_mod_cast hh
    have hjn : (K:ℝ) < |(j:ℝ)/n| := by
      rw [abs_div,abs_of_pos hn']
      exact (lt_div_iff₀ hn').mpr hj'
    have hje : A < |(j:ℝ)/n-e| := by
      have hb := abs_add_le ((j:ℝ)/n-e) e
      rw [sub_add_cancel] at hb
      linarith
    have hja : A < |(j:ℝ)/n| := by linarith
    rw [hs _ _ hje,hs _ _ hja,sub_self,abs_zero]
  have heq : (∑' j : ℤ, ∫ a : UnitAddCircle,
      |W ((j:ℝ)/n-e) a-W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) =
      ∑ j ∈ S, ∫ a : UnitAddCircle, |W ((j:ℝ)/n-e) a-W ((j:ℝ)/n) a|
        ∂AddCircle.haarAddCircle := by
    apply tsum_eq_sum
    intro j hj
    simp only [hz j hj,integral_zero]
  have hb (j : ℤ) : (∫ a : UnitAddCircle, |W ((j:ℝ)/n-e) a-W ((j:ℝ)/n) a|
      ∂AddCircle.haarAddCircle) ≤ (L:ℝ)*|e| := by
    have hc : Continuous (fun a : UnitAddCircle => |W ((j:ℝ)/n-e) a-W ((j:ℝ)/n) a|) := by
      fun_prop
    calc
      _ ≤ ∫ _ : UnitAddCircle, (L:ℝ)*|e| ∂AddCircle.haarAddCircle :=
        integral_mono (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          (integrable_const _) (fun a => by
            simpa only [Real.dist_eq,sub_sub_cancel_left,abs_neg] using
              (hLip a).dist_le_mul ((j:ℝ)/n-e) ((j:ℝ)/n))
      _ = _ := by simp
  have hcard : (S.card:ℝ) = 2*(K:ℝ)*n+1 := by
    have hc : S.card = 2*(K*n)+1 := by
      dsimp only [S]
      rw [Int.card_Icc]
      have hz : (K:ℤ)*n + 1 - -((K:ℤ)*n) = ((2*(K*n)+1:ℕ):ℤ) := by
        push_cast
        ring
      rw [hz, Int.toNat_natCast]
    rw [hc]
    push_cast
    ring
  unfold roundingMass
  rw [heq]
  calc
    _ ≤ (n:ℝ)⁻¹ * (S.card*((L:ℝ)*|e|)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hn'.le)
      simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum (fun j _ => hb j)
    _ = (2*(K:ℝ)+(n:ℝ)⁻¹)*L*|e| := by rw [hcard]; field_simp
    _ ≤ _ := by
      have hi : (n:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) L.coe_nonneg) (abs_nonneg e)

/-- The rounding correction is removed at the coefficient mass level, without
translating the actual lattice j/N or its fine phase. -/
lemma tendsto_roundingMass {W : ℝ → UnitAddCircle → ℝ} {A C : ℝ} {L : ℝ≥0} {e : ℕ → ℝ}
    (hW : Continuous W.uncurry) (hLip : ∀ a, LipschitzWith L (fun s => W s a))
    (hs : ∀ s a, A < |s| → W s a = 0)
    (he : ∀ n, |e n| ≤ C) (ht : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => roundingMass W n (e n)) atTop (𝓝 0) := by
  obtain ⟨K,hK⟩ := exists_nat_ge (A+C)
  apply squeeze_zero' (Eventually.of_forall (fun n => by
    unfold roundingMass
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (tsum_nonneg (fun _ => integral_nonneg (fun _ => abs_nonneg _)))))
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    exact roundingMass_bound hW hLip hs (he n) hK hn
  · simpa only [abs_zero,mul_zero] using (tendsto_const_nhds.mul ht.abs)

lemma roundingMass_uniform_bound {W : ℝ → UnitAddCircle → ℝ} {A C e η : ℝ} {K n : ℕ}
    (hW : Continuous W.uncurry) (hη : 0 ≤ η)
    (hclose : ∀ s a, |W (s-e) a-W s a| ≤ η)
    (hs : ∀ s a, A < |s| → W s a = 0)
    (he : |e| ≤ C) (hK : A+C ≤ K) (hn : 0 < n) :
    roundingMass W n e ≤ (2*(K:ℝ)+1)*η := by
  classical
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hC : 0 ≤ C := (abs_nonneg e).trans he
  let S : Finset ℤ := Finset.Icc (-(K*n:ℤ)) (K*n)
  have hz (j : ℤ) (hj : j ∉ S) (a : UnitAddCircle) :
      |W ((j:ℝ)/n-e) a-W ((j:ℝ)/n) a| = 0 := by
    have hj' : (K:ℝ)*n < |(j:ℝ)| := by
      have hh : (K*n:ℤ) < |j| := by
        simpa only [S,Finset.mem_Icc,← abs_le,not_le] using hj
      exact_mod_cast hh
    have hjn : (K:ℝ) < |(j:ℝ)/n| := by
      rw [abs_div,abs_of_pos hn']
      exact (lt_div_iff₀ hn').mpr hj'
    have hje : A < |(j:ℝ)/n-e| := by
      have hb := abs_add_le ((j:ℝ)/n-e) e
      rw [sub_add_cancel] at hb
      linarith
    have hja : A < |(j:ℝ)/n| := by linarith
    rw [hs _ _ hje,hs _ _ hja,sub_self,abs_zero]
  have heq : (∑' j : ℤ, ∫ a : UnitAddCircle,
      |W ((j:ℝ)/n-e) a-W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) =
      ∑ j ∈ S, ∫ a : UnitAddCircle, |W ((j:ℝ)/n-e) a-W ((j:ℝ)/n) a|
        ∂AddCircle.haarAddCircle := by
    apply tsum_eq_sum
    intro j hj
    simp only [hz j hj,integral_zero]
  have hb (j : ℤ) : (∫ a : UnitAddCircle, |W ((j:ℝ)/n-e) a-W ((j:ℝ)/n) a|
      ∂AddCircle.haarAddCircle) ≤ η := by
    have hc : Continuous (fun a : UnitAddCircle => |W ((j:ℝ)/n-e) a-W ((j:ℝ)/n) a|) := by
      fun_prop
    calc
      _ ≤ ∫ _ : UnitAddCircle, η ∂AddCircle.haarAddCircle :=
        integral_mono (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          (integrable_const _) (fun a => hclose _ a)
      _ = _ := by simp
  have hcard : (S.card:ℝ) = 2*(K:ℝ)*n+1 := by
    have hc : S.card = 2*(K*n)+1 := by
      dsimp only [S]
      rw [Int.card_Icc]
      have hz : (K:ℤ)*n + 1 - -((K:ℤ)*n) = ((2*(K*n)+1:ℕ):ℤ) := by
        push_cast
        ring
      rw [hz, Int.toNat_natCast]
    rw [hc]
    push_cast
    ring
  unfold roundingMass
  rw [heq]
  calc
    _ ≤ (n:ℝ)⁻¹ * (S.card*(η)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hn'.le)
      simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum (fun j _ => hb j)
    _ = (2*(K:ℝ)+(n:ℝ)⁻¹)*η := by rw [hcard]; field_simp
    _ ≤ _ := by
      have hi : (n:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
      exact mul_le_mul_of_nonneg_right (by linarith) hη

/-- Compact continuity is sufficient for removal of rounding; no quantitative
Lipschitz hypothesis has to be added to the old spectral density. -/
lemma tendsto_roundingMass_of_compact {W : ℝ → UnitAddCircle → ℝ} {e : ℕ → ℝ}
    (hW : Continuous W.uncurry) (hc : HasCompactSupport W.uncurry)
    (ht : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => roundingMass W n (e n)) atTop (𝓝 0) := by
  have hUC := hc.uniformContinuous_of_continuous hW
  obtain ⟨R,hR⟩ := (hc.image continuous_fst).isBounded.subset_closedBall (0 : ℝ)
  let A := max R 0
  have hs (s a) (hs : A < |s|) : W s a = 0 := by
    by_contra hn
    have hh := hR ⟨(s,a),subset_tsupport _ hn,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs] at hh
    exact (not_lt_of_ge (hh.trans (le_max_left _ _))) hs
  obtain ⟨K,hK⟩ := exists_nat_ge (A+1)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let C : ℝ := 2*(K:ℝ)+1
  have hC : 0 < C := by dsimp [C]; positivity
  let η : ℝ := ε/(2*C)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuous_iff.mp hUC η hη
  have he : ∀ᶠ n in atTop, |e n| < min δ 1 := by
    simpa only [Real.dist_eq,sub_zero] using Metric.tendsto_nhds.mp ht (min δ 1) (lt_min hδ zero_lt_one)
  filter_upwards [he,eventually_gt_atTop (0:ℕ)] with n hn hn0
  have hb := roundingMass_uniform_bound (K := K) hW hη.le
    (fun s a => le_of_lt (hclose (a := (s-e n,a)) (b := (s,a)) (by
      simpa only [Prod.dist_eq,dist_self,Real.dist_eq,sub_sub_cancel_left,abs_neg,max_eq_left (abs_nonneg (e n))] using
        (lt_of_lt_of_le hn (min_le_left _ _))))) hs
    (show |e n| ≤ 1 from le_of_lt (lt_of_lt_of_le hn (min_le_right _ _))) hK hn0
  have hnonneg : 0 ≤ roundingMass W n (e n) := by
    unfold roundingMass
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (tsum_nonneg (fun _ => integral_nonneg (fun _ => abs_nonneg _)))
  rw [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg hnonneg]
  have heq : (2*(K:ℝ)+1)*η = ε/2 := by dsimp [η,C]; field_simp
  exact (hb.trans_eq heq).trans_lt (by linarith)

lemma compact_lattice_support {W : ℝ → UnitAddCircle → ℝ} (hc : HasCompactSupport W.uncurry)
    {n : ℕ} (hn : 0 < n) (e : ℝ) :
    ∃ S : Finset ℤ, ∀ j ∉ S, ∀ a, W ((j:ℝ)/n-e) a = 0 := by
  obtain ⟨R,hR⟩ := (hc.image continuous_fst).isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨K,hK⟩ := exists_nat_ge (R+|e|)
  refine ⟨Finset.Icc (-(K*n:ℤ)) (K*n),?_⟩
  intro j hj a
  by_contra hz
  have hh := hR ⟨((j:ℝ)/n-e,a),subset_tsupport _ hz,rfl⟩
  rw [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs] at hh
  have hjn : (K:ℝ) < |(j:ℝ)/n| := by
    have hk : (K*n:ℤ) < |j| := by
      simpa only [Finset.mem_Icc,← abs_le,not_le] using hj
    have hk' : (K:ℝ)*n < |(j:ℝ)| := by exact_mod_cast hk
    rw [abs_div,abs_of_pos (show (0:ℝ) < n by exact_mod_cast hn)]
    exact (lt_div_iff₀ (by exact_mod_cast hn)).mpr hk'
  have ht := abs_add_le ((j:ℝ)/n-e) e
  rw [sub_add_cancel] at ht
  linarith

lemma compact_lattice_summable_integral {W : ℝ → UnitAddCircle → ℝ}
    (hc : HasCompactSupport W.uncurry) {n : ℕ} (hn : 0 < n) (e : ℝ) :
    Summable (fun j : ℤ => ∫ a : UnitAddCircle, |W ((j:ℝ)/n-e) a|
      ∂AddCircle.haarAddCircle) := by
  obtain ⟨S,hS⟩ := compact_lattice_support hc hn e
  apply summable_of_ne_finset_zero (s := S)
  intro j hj
  simp only [hS j hj,abs_zero,integral_zero]

lemma integrated_array_mass_error_summable {c : ℤ → UnitAddCircle → ℂ}
    {W : ℝ → UnitAddCircle → ℝ} (hW : Continuous W.uncurry)
    (hc : HasCompactSupport W.uncurry) (hcc : ∀ j, Continuous (c j))
    (hcs : Summable (fun j : ℤ => ∫ a : UnitAddCircle, ‖c j a‖^2 ∂AddCircle.haarAddCircle))
    {n : ℕ} (hn : 0 < n) (e : ℝ) :
    Summable (fun j : ℤ => ∫ a : UnitAddCircle,
      |‖c j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n-e) a| ∂AddCircle.haarAddCircle) := by
  have hp (j : ℤ) : Continuous (fun a => W ((j:ℝ)/n-e) a) :=
    hW.comp (continuous_const.prodMk continuous_id)
  have he (j : ℤ) : Integrable (fun a => |‖c j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n-e) a|)
      AddCircle.haarAddCircle :=
    (((hcc j).norm.pow 2).sub (continuous_const.mul (hp j))).abs.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi (j : ℤ) : Integrable (fun a => ‖c j a‖^2+(n:ℝ)⁻¹*|W ((j:ℝ)/n-e) a|)
      AddCircle.haarAddCircle :=
    (((hcc j).norm.pow 2).add (continuous_const.mul (hp j).abs)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply Summable.of_nonneg_of_le (fun j => integral_nonneg (fun a => abs_nonneg _))
    (f := fun j => (∫ a : UnitAddCircle, ‖c j a‖^2 ∂AddCircle.haarAddCircle)+
      (n:ℝ)⁻¹*(∫ a : UnitAddCircle, |W ((j:ℝ)/n-e) a| ∂AddCircle.haarAddCircle))
  · intro j
    rw [← integral_const_mul,← integral_add]
    · exact integral_mono (he j) (hi j) (fun a => by
        calc
          _ ≤ |‖c j a‖^2|+|(n:ℝ)⁻¹*W ((j:ℝ)/n-e) a| := abs_sub _ _
          _ = _ := by rw [abs_of_nonneg (sq_nonneg _),abs_mul,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))])
    · exact ((hcc j).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · exact (continuous_const.mul (hp j).abs).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact hcs.add ((compact_lattice_summable_integral hc hn e).mul_left _)

/-- Removal of rounding for actual coefficient masses, with all summability
proved from compact support and true squared Fourier mass. -/
lemma remove_array_rounding {c : ℕ → ℤ → UnitAddCircle → ℂ}
    {W : ℝ → UnitAddCircle → ℝ} {e : ℕ → ℝ}
    (hW : Continuous W.uncurry) (hc : HasCompactSupport W.uncurry)
    (hcc : ∀ n j, Continuous (c n j))
    (hcs : ∀ n, Summable (fun j : ℤ => ∫ a : UnitAddCircle, ‖c n j a‖^2 ∂AddCircle.haarAddCircle))
    (he : Tendsto e atTop (𝓝 0))
    (ht : Tendsto (fun n => ∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n-e n) a| ∂AddCircle.haarAddCircle) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) atTop (𝓝 0) := by
  have hr := tendsto_roundingMass_of_compact hW hc he
  have hbound : ∀ᶠ n in atTop,
      (∑' j : ℤ, ∫ a : UnitAddCircle, |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) ≤
      (∑' j : ℤ, ∫ a : UnitAddCircle, |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n-e n) a| ∂AddCircle.haarAddCircle)+
        roundingMass W n (e n) := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have hinv : 0 ≤ (n:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
    have hs₀ := integrated_array_mass_error_summable hW hc (hcc n) (hcs n) hn 0
    simp only [sub_zero] at hs₀
    have hs₁ := integrated_array_mass_error_summable hW hc (hcc n) (hcs n) hn (e n)
    have hs₂ : Summable (fun j : ℤ => ∫ a : UnitAddCircle,
        |W ((j:ℝ)/n-e n) a-W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) := by
      obtain ⟨S,hS⟩ := compact_lattice_support hc hn (e n)
      obtain ⟨T,hT⟩ := compact_lattice_support hc hn 0
      apply summable_of_ne_finset_zero (s := S ∪ T)
      intro j hj
      have hjS : j ∉ S := fun h => hj (Finset.mem_union_left T h)
      have hjT : j ∉ T := fun h => hj (Finset.mem_union_right S h)
      have hz (a) : W ((j:ℝ)/n) a = 0 := by simpa only [sub_zero] using hT j hjT a
      simp only [hS j hjS,hz,sub_self,abs_zero,integral_zero]
    have hi (j : ℤ) :
        (∫ a : UnitAddCircle, |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) ≤
        (∫ a : UnitAddCircle, |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n-e n) a| ∂AddCircle.haarAddCircle)+
          (n:ℝ)⁻¹*(∫ a : UnitAddCircle, |W ((j:ℝ)/n-e n) a-W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) := by
      have h₀ : Continuous (fun a => W ((j:ℝ)/n) a) := hW.comp (continuous_const.prodMk continuous_id)
      have h₁ : Continuous (fun a => W ((j:ℝ)/n-e n) a) := hW.comp (continuous_const.prodMk continuous_id)
      have hcj := ((hcc n j).norm.pow 2)
      rw [← integral_const_mul,← integral_add]
      · apply integral_mono
        · exact (hcj.sub (continuous_const.mul h₀)).abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        · exact ((hcj.sub (continuous_const.mul h₁)).abs.add
            (continuous_const.mul (h₁.sub h₀).abs)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        · intro a
          calc
            _ ≤ |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n-e n) a|+
                |(n:ℝ)⁻¹*(W ((j:ℝ)/n-e n) a-W ((j:ℝ)/n) a)| := by
              convert abs_add_le (‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n-e n) a)
                ((n:ℝ)⁻¹*(W ((j:ℝ)/n-e n) a-W ((j:ℝ)/n) a)) using 1
              ring_nf
            _ = _ := by rw [abs_mul,abs_of_nonneg hinv]
      · exact (hcj.sub (continuous_const.mul h₁)).abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · exact (continuous_const.mul (h₁.sub h₀).abs).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hh := Summable.tsum_le_tsum hi hs₀ (hs₁.add (hs₂.mul_left _))
    rw [hs₁.tsum_add (hs₂.mul_left _),tsum_mul_left] at hh
    exact hh
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => tsum_nonneg (fun j => integral_nonneg (fun a => abs_nonneg _)))) hbound
  simpa only [add_zero] using ht.add hr

lemma exactPassageCoeff_summed_unrounded
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {P V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R d D C₀ C₁ M M₁ C : ℝ}
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(P x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hsupp : ∀ a, Function.support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u)
    (hΦ : ContDiff ℝ 3 (fun x => 2*Real.pi*(m:ℝ)*P x))
    (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M) (hM₁ : 0 ≤ M₁) (hC : 0 ≤ C)
    (hδ : ∀ n, |2*Real.pi*(m:ℝ)*δ n| ≤ C)
    (hfirst : ∀ x ∈ Icc (l-2*R) (u+2*R), |deriv (fun x => 2*Real.pi*(m:ℝ)*P x) x| ≤ M₁)
    (hsecond : ∀ x ∈ Icc (l-2*R) (u+2*R), d ≤ iteratedDeriv 2 (fun x => 2*Real.pi*(m:ℝ)*P x) x)
    (hupper : ∀ x ∈ Icc (l-2*R) (u+2*R), iteratedDeriv 2 (fun x => 2*Real.pi*(m:ℝ)*P x) x ≤ D)
    (hM : ∀ x ∈ Icc (l-2*R) (u+2*R), |iteratedDeriv 3 (fun x => 2*Real.pi*(m:ℝ)*P x) x| ≤ M)
    (hAb : ∀ a x, x ∈ Icc (l-2*R) (u+2*R) → ‖A₀ a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (l-2*R) (u+2*R) → ‖deriv (A₀ a) x‖ ≤ C₁) 
    (hP : Differentiable ℝ P) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv P = V)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hδt : Tendsto δ atTop (𝓝 0)) :

    Tendsto (fun n : ℕ => ∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖exactPassageCoeff m (H n) A j a‖^2-
        (n:ℝ)⁻¹*stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
          (A₀ a) ((j:ℝ)/n)| ∂AddCircle.haarAddCircle)
      atTop (𝓝 0) := by
  have hVr := hV.differentiable (by simp)
  have ht := exactPassageCoeff_summed_weight hH hA hA₀ hAc hsupp hlo huo hlu
    hΦ hR hd hdD hC₀ hC₁ hM₀ hM₁ hC hδ hfirst hsecond hupper hM hAb hA'b hP hVr hPV
  let W : ℝ → UnitAddCircle → ℝ := fun s a =>
    stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s
  have he := phase_speed_derivatives (m := (m:ℝ)) hP hVr hPV
  have hi : Icc (l-R) (u+R) ⊆ Icc (l-2*R) (u+2*R) := by
    apply Icc_subset_Icc <;> linarith
  have hp (x : ℝ) (hx : x ∈ Icc (l-R) (u+R)) :
      0 < deriv (fun x => (m:ℝ)*V x) x := by
    have hh := hsecond x (hi hx)
    rw [he.2 x] at hh
    have hk : 0 < 2*Real.pi := by positivity
    nlinarith
  have hW := stationaryWeight_compact_continuous (contDiff_const.mul hV) hAc
    (fun a => (hsupp a).trans Ioc_subset_Icc_self) hR hp
  simpa only [W] using remove_array_rounding (c := fun n j => exactPassageCoeff m (H n) A j)
    (W := W) hW.1 hW.2 (fun n j => continuous_exactPassageCoeff (hHc n) hAcont j)
    (fun n => exactPassageCoeff_summable (hHc n) hAcont)
    (show Tendsto (fun n => (m:ℝ)*δ n) atTop (𝓝 0) from by simpa using hδt.const_mul (m:ℝ)) ht

end ThreeTorus

namespace ThreeTorus

/-- A compact positive second derivative supplies every numerical constant used
by the uniform stationary-phase estimate.  None of those constants are extra
hypotheses of the passage. -/
lemma exactPassageCoeff_summed_positive
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {P V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : 0 < m)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(P x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hsupp : ∀ a, Function.support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv P = V)
    (hd : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hδt : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖exactPassageCoeff m (H n) A j a‖^2-
        (n:ℝ)⁻¹*stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
          (A₀ a) ((j:ℝ)/n)| ∂AddCircle.haarAddCircle)
      atTop (𝓝 0) := by
  let Φ : ℝ → ℝ := fun x => 2*Real.pi*(m:ℝ)*P x
  let K : Set ℝ := Icc (l-2*R) (u+2*R)
  have hK : IsCompact K := isCompact_Icc
  have hKne : K.Nonempty := nonempty_Icc.mpr (by linarith)
  have hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ := contDiff_const.mul hP
  have he := phase_speed_derivatives (m := (m:ℝ)) (hP.differentiable (by simp))
    (hV.differentiable (by simp)) hPV
  have hpos (x : ℝ) (hx : x ∈ K) : 0 < iteratedDeriv 2 Φ x := by
    rw [he.2 x,deriv_const_mul _ (hV.differentiable (by simp) x)]
    exact mul_pos (by positivity) (mul_pos (by exact_mod_cast hm) (hd x hx))
  obtain ⟨x₀,hx₀,hmin⟩ := hK.exists_isMinOn hKne
    (hΦ.continuous_iteratedDeriv 2 (by exact WithTop.coe_le_coe.mpr le_top)).continuousOn
  let d := iteratedDeriv 2 Φ x₀
  have hd0 : 0 < d := hpos x₀ hx₀
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn
    (hΦ.continuous_iteratedDeriv 2 (by exact WithTop.coe_le_coe.mpr le_top)).continuousOn
  obtain ⟨M₁,hM₁⟩ := hK.exists_bound_of_continuousOn
    (hΦ.continuous_deriv (by simp)).continuousOn
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn
    (hΦ.continuous_iteratedDeriv 3 (by exact WithTop.coe_le_coe.mpr le_top)).continuousOn
  obtain ⟨C₀,hC₀⟩ := (isCompact_univ.prod hK).exists_bound_of_continuousOn hAc.continuousOn
  obtain ⟨C₁,hC₁⟩ := (isCompact_univ.prod hK).exists_bound_of_continuousOn hAd.continuousOn
  have hδb : BddAbove (range (fun n => |2*Real.pi*(m:ℝ)*δ n|)) :=
    ((hδt.const_mul (2*Real.pi*(m:ℝ))).abs).bddAbove_range
  obtain ⟨C,hC⟩ := hδb
  apply exactPassageCoeff_summed_unrounded hH hA hA₀ hAc hsupp hlo huo hlu
    (hΦ.of_le (by exact WithTop.coe_le_coe.mpr le_top)) hR hd0
    (d := d) (D := max 0 D) (C₀ := max 0 C₀) (C₁ := max 0 C₁)
    (M := max 0 M) (M₁ := max 0 M₁) (C := max 0 C)
  · exact (le_abs_self _).trans ((hD x₀ hx₀).trans (le_max_right _ _))
  · exact le_max_left _ _
  · exact le_max_left _ _
  · exact le_max_left _ _
  · exact le_max_left _ _
  · exact le_max_left _ _
  · intro n
    exact (hC (mem_range_self n)).trans (le_max_right _ _)
  · intro x hx
    exact (hM₁ x hx).trans (le_max_right _ _)
  · intro x hx
    exact hmin hx
  · intro x hx
    exact (le_abs_self _).trans ((hD x hx).trans (le_max_right _ _))
  · intro x hx
    exact (hM x hx).trans (le_max_right _ _)
  · intro a x hx
    exact (hC₀ (a,x) ⟨mem_univ _,hx⟩).trans (le_max_right _ _)
  · intro a x hx
    exact (hC₁ (a,x) ⟨mem_univ _,hx⟩).trans (le_max_right _ _)
  · exact hP.differentiable (by simp)
  · exact hV
  · exact hPV
  · exact hHc
  · exact hAcont
  · exact hδt

end ThreeTorus

namespace ThreeTorus
open Function
open scoped ComplexConjugate

lemma exactPassageCoeff_neg (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (j : ℤ) (a : UnitAddCircle) :
    exactPassageCoeff (-m) H (fun x => conj (A x)) j a =
      conj (exactPassageCoeff m H A (-j) a) := by
  unfold exactPassageCoeff fourierCoeff passageFourierInput
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with θ
  simp only [smul_eq_mul, neg_neg, map_mul, fourier_neg]

lemma exactPassageCoeff_neg_norm (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (j : ℤ) (a : UnitAddCircle) :
    ‖exactPassageCoeff (-m) H (fun x => conj (A x)) j a‖ =
      ‖exactPassageCoeff m H A (-j) a‖ := by
  rw [exactPassageCoeff_neg,Complex.norm_conj]

lemma summed_mass_reflect (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (W : ℝ → UnitAddCircle → ℝ) (n : ℕ) :
    (∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖exactPassageCoeff (-m) H (fun x => conj (A x)) j a‖^2-
        (n:ℝ)⁻¹*W (-(j:ℝ)/n) a| ∂AddCircle.haarAddCircle) =
    (∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖exactPassageCoeff m H A j a‖^2-
        (n:ℝ)⁻¹*W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) := by
  simp_rw [exactPassageCoeff_neg_norm]
  simpa only [Int.cast_neg] using
    tsum_comp_neg (fun j : ℤ => ∫ a : UnitAddCircle,
      |‖exactPassageCoeff m H A j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a|
        ∂AddCircle.haarAddCircle)

lemma stationaryWeight_reflect {I : Set ℝ} {J : ℝ → ℝ}
    (hinj : InjOn J I) (A : ℝ → ℂ) (s : ℝ) :
    stationaryWeight I (fun x => -J x) (fun x => conj (A x)) s =
      stationaryWeight I J A (-s) := by
  classical
  have hi : InjOn (fun x => -J x) I := fun x hx y hy he => hinj hx hy (neg_injective he)
  by_cases hs : -s ∈ J '' I
  · obtain ⟨x,hx,hxs⟩ := hs
    have hneg : -J x = s := by linarith
    have hm : s ∈ (fun x => -J x) '' I := ⟨x,hx,hneg⟩
    have h₁ : invFunOn (fun x => -J x) I s = x := by
      rw [← hneg]; exact hi.leftInvOn_invFunOn hx
    have h₂ : invFunOn J I (-s) = x := by
      rw [← hxs]; exact hinj.leftInvOn_invFunOn hx
    simp only [stationaryWeight,branchDensity,indicator_of_mem hm,
      indicator_of_mem (show -s ∈ J '' I from ⟨x,hx,hxs⟩),h₁,h₂,
      Complex.norm_conj]
    change ‖A x‖^2/|deriv (-J) x| = ‖A x‖^2/|deriv J x|
    rw [deriv.neg,abs_neg]
  · have hm : s ∉ (fun x => -J x) '' I := by
      rintro ⟨x,hx,he⟩
      exact hs ⟨x,hx,by linarith⟩
    simp only [stationaryWeight,branchDensity,indicator_of_notMem hm,indicator_of_notMem hs]

/-- The source passage mass theorem at every nonzero angular index. -/
lemma exactPassageCoeff_summed
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {P V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : m ≠ 0)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(P x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hsupp : ∀ a, Function.support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv P = V)
    (hd : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hδt : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖exactPassageCoeff m (H n) A j a‖^2-
        (n:ℝ)⁻¹*stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
          (A₀ a) ((j:ℝ)/n)| ∂AddCircle.haarAddCircle)
      atTop (𝓝 0) := by
  rcases lt_or_gt_of_ne hm with hm | hm
  · have hm' : 0 < -m := neg_pos.mpr hm
    have hconjA₀ (a : UnitAddCircle) : ContDiff ℝ 2 (fun x => conj (A₀ a x)) :=
      Complex.conjCLE.contDiff.comp (hA₀ a)
    have hconjAc : Continuous (fun p : UnitAddCircle × ℝ => conj (A₀ p.1 p.2)) :=
      Complex.continuous_conj.comp hAc
    have hconjAd : Continuous (fun p : UnitAddCircle × ℝ =>
        deriv (fun x => conj (A₀ p.1 x)) p.2) := by
      simpa only [show ∀ z : ℂ, conj z = star z from fun _ => rfl, deriv.star]
        using hAd.star
    have hs := exactPassageCoeff_summed_positive (A := fun x => conj (A x))
      (A₀ := fun a x => conj (A₀ a x)) hm' hH
      (fun a x hx => congrArg (conj : ℂ → ℂ) (hA a x hx))
      hconjA₀ hconjAc hconjAd
      (fun a x hx => hsupp a (by simpa using hx))
      hlo huo hlu hR hP hV hPV hd hHc (Complex.continuous_conj.comp hAcont) hδt
    have hJ : InjOn (fun x => (-m:ℝ)*V x) (Icc (l-R) (u+R)) := by
      apply StrictMonoOn.injOn
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
        ((contDiff_const.mul hV).continuous.continuousOn)
      intro x hx
      rw [deriv_const_mul _ (hV.differentiable (by simp) x)]
      exact mul_pos (by exact_mod_cast hm') (hd x (by
        have hx' := interior_subset hx
        constructor <;> linarith [hx'.1,hx'.2]))
    have href (a : UnitAddCircle) (s : ℝ) :
        stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s =
        stationaryWeight (Icc (l-R) (u+R)) (fun x => (-m:ℝ)*V x)
          (fun x => conj (A₀ a x)) (-s) := by
      simpa only [neg_mul, neg_neg, starRingEnd_self_apply] using
        stationaryWeight_reflect hJ (fun x => conj (A₀ a x)) s
    have he (n : ℕ) :
        (∑' j : ℤ, ∫ a : UnitAddCircle,
          |‖exactPassageCoeff m (H n) A j a‖^2-
            (n:ℝ)⁻¹*stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
              (A₀ a) ((j:ℝ)/n)| ∂AddCircle.haarAddCircle) =
        (∑' j : ℤ, ∫ a : UnitAddCircle,
          |‖exactPassageCoeff (-m) (H n) (fun x => conj (A x)) j a‖^2-
            (n:ℝ)⁻¹*stationaryWeight (Icc (l-R) (u+R)) (fun x => (-m:ℝ)*V x)
              (fun x => conj (A₀ a x)) ((j:ℝ)/n)| ∂AddCircle.haarAddCircle) := by
      simp_rw [href]
      simpa only [neg_neg,starRingEnd_self_apply, Int.cast_neg, neg_div] using
        summed_mass_reflect (-m) (H n) (fun x => conj (A x))
          (fun s a => stationaryWeight (Icc (l-R) (u+R)) (fun x => (-m:ℝ)*V x)
            (fun x => conj (A₀ a x)) s) n
    simpa only [he,Int.cast_neg] using hs
  · exact exactPassageCoeff_summed_positive hm hH hA hA₀ hAc hAd hsupp hlo huo hlu hR
      hP hV hPV hd hHc hAcont hδt

end ThreeTorus

end

end OAI
