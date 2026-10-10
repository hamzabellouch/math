import OAI.MathematicalPhysics.Boltzmann.Branching.ComplexWeakL2Diagonal
import OAI.MathematicalPhysics.Boltzmann.Branching.InverseFourierL2
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityAverageDifference
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrableCoordinates

namespace OAI

section

/-! # Finite-measure cutoffs of L2 Fourier data -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ENNReal
namespace BoltzmannNonuniqueness.Published

def complexL2Cutoff (S : Set FourierSpace) (hS : MeasurableSet S)
    (a : Lp ℂ 2 (volume : Measure FourierSpace)) : Lp ℂ 2 (volume : Measure FourierSpace) :=
  ((Lp.memLp a).indicator hS).toLp (S.indicator a)

theorem complexL2Cutoff_ae (S : Set FourierSpace) (hS : MeasurableSet S)
    (a : Lp ℂ 2 (volume : Measure FourierSpace)) :
    (complexL2Cutoff S hS a : FourierSpace → ℂ) =ᵐ[volume] S.indicator a :=
  MemLp.coeFn_toLp _

theorem complexL2Cutoff_norm_le (S : Set FourierSpace) (hS : MeasurableSet S)
    (a : Lp ℂ 2 (volume : Measure FourierSpace)) : ‖complexL2Cutoff S hS a‖ ≤ ‖a‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [complexL2Cutoff_ae S hS a] with x hx
  rw [hx]
  by_cases hxS : x ∈ S <;> simp [hxS]

theorem complexL2Cutoff_integrable (S : Set FourierSpace) (hS : MeasurableSet S)
    (hfinite : volume S < ⊤) (a : Lp ℂ 2 (volume : Measure FourierSpace)) :
    Integrable (S.indicator a) := by
  have : Fact (volume S < ⊤) := ⟨hfinite⟩
  apply (integrable_indicator_iff hS).mpr
  exact ((Lp.memLp a).restrict S).integrable (by norm_num)

def fourierBandApprox (S : Set FourierSpace)
    (a : Lp ℂ 2 (volume : Measure FourierSpace)) : FourierSpace → ℂ :=
  𝓕⁻ (S.indicator a)

theorem fourierBandApprox_ae (S : Set FourierSpace) (hS : MeasurableSet S)
    (hfinite : volume S < ⊤) (a : Lp ℂ 2 (volume : Measure FourierSpace)) :
    (fun x => (𝓕⁻ (complexL2Cutoff S hS a) : Lp ℂ 2 (volume : Measure FourierSpace)) x) =ᵐ[volume]
      fourierBandApprox S a :=
  inverseFourier_L2_ae_eq_integral (complexL2Cutoff_integrable S hS hfinite a)
    ((Lp.memLp a).indicator hS)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # A finite Fourier window evaluates by an L2 pairing -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ComplexConjugate RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

def fourierBandTest (S : Set FourierSpace) (x : FourierSpace) : FourierSpace → ℂ :=
  S.indicator (fun k => (𝐞 (-inner ℝ k x) : ℂ))

theorem fourierBandTest_memLp (S : Set FourierSpace) (hS : MeasurableSet S)
    (hfinite : volume S < ⊤) (x : FourierSpace) : MemLp (fourierBandTest S x) 2 volume := by
  have hb : MemLp (S.indicator (fun _ : FourierSpace => (1 : ℂ))) 2 volume :=
    memLp_indicator_const _ hS _ (Or.inr hfinite.ne)
  have hm : Measurable (fourierBandTest S x) := by
    apply Measurable.indicator _ hS
    fun_prop
  apply hb.of_le hm.aestronglyMeasurable
  exact ae_of_all _ (fun k => by
    by_cases hk : k ∈ S <;> simp [fourierBandTest,hk])

theorem fourierBandApprox_pairing (S : Set FourierSpace) (hS : MeasurableSet S)
    (hfinite : volume S < ⊤) (a : Lp ℂ 2 (volume : Measure FourierSpace)) (x : FourierSpace) :
    fourierBandApprox S a x = inner ℂ ((fourierBandTest_memLp S hS hfinite x).toLp
      (fourierBandTest S x)) a := by
  rw [fourierBandApprox,Real.fourierInv_eq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(fourierBandTest_memLp S hS hfinite x).coeFn_toLp] with k hk
  rw [hk]
  by_cases hks : k ∈ S
  · simp only [fourierBandTest,indicator_of_mem hks,RCLike.inner_apply]
    change (𝐞 (inner ℝ k x) : ℂ)*a k = a k*conj (𝐞 (-inner ℝ k x) : ℂ)
    rw [Circle.starRingEnd_addChar,neg_neg,mul_comm]
  · simp [fourierBandTest,hks,RCLike.inner_apply]

theorem fourierBandApprox_tendsto {u : ℕ → Lp ℂ 2 (volume : Measure FourierSpace)}
    {g : Lp ℂ 2 (volume : Measure FourierSpace)}
    (hu : ∀ h : Lp ℂ 2 volume,
      Filter.Tendsto (fun n => inner ℂ (u n) h) Filter.atTop (nhds (inner ℂ g h)))
    (S : Set FourierSpace) (hS : MeasurableSet S) (hfinite : volume S < ⊤) (x : FourierSpace) :
    Filter.Tendsto (fun n => fourierBandApprox S (u n) x) Filter.atTop
      (nhds (fourierBandApprox S g x)) := by
  simp_rw [fourierBandApprox_pairing S hS hfinite]
  have h := (Complex.continuous_conj.tendsto _).comp
    (hu ((fourierBandTest_memLp S hS hfinite x).toLp (fourierBandTest S x)))
  simpa only [Function.comp_def,inner_conj_symm] using h

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Uniform pointwise bounds on finite-frequency reconstructions -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ComplexConjugate RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

theorem fourierBandTest_norm_sq (S : Set FourierSpace) (hS : MeasurableSet S)
    (hfinite : volume S < ⊤) (x : FourierSpace) :
    ‖(fourierBandTest_memLp S hS hfinite x).toLp (fourierBandTest S x)‖^2 = volume.real S := by
  rw [L2_norm_sq_integral]
  calc
    _ = ∫ k, S.indicator (fun _ => (1 : ℝ)) k := by
      apply integral_congr_ae
      filter_upwards [(fourierBandTest_memLp S hS hfinite x).coeFn_toLp] with k hk
      rw [hk]
      by_cases hks : k ∈ S <;> simp [fourierBandTest,hks]
    _ = volume.real S := by rw [integral_indicator hS]; simp

theorem fourierBandApprox_norm_le (S : Set FourierSpace) (hS : MeasurableSet S)
    (hfinite : volume S < ⊤) (a : Lp ℂ 2 (volume : Measure FourierSpace)) (x : FourierSpace) :
    ‖fourierBandApprox S a x‖ ≤ (volume.real S+1)*‖a‖ := by
  let q := (fourierBandTest_memLp S hS hfinite x).toLp (fourierBandTest S x)
  have hq : ‖q‖ ≤ volume.real S+1 := by
    have he := fourierBandTest_norm_sq S hS hfinite x
    change ‖q‖^2 = volume.real S at he
    nlinarith [sq_nonneg (‖q‖-1),norm_nonneg q]
  rw [fourierBandApprox_pairing S hS hfinite]
  exact (norm_inner_le_norm q a).trans
    (mul_le_mul_of_nonneg_right hq (norm_nonneg a))

theorem fourierBandApprox_continuous (S : Set FourierSpace) (hS : MeasurableSet S)
    (hfinite : volume S < ⊤) (a : Lp ℂ 2 (volume : Measure FourierSpace)) :
    Continuous (fourierBandApprox S a) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner.neg
    (complexL2Cutoff_integrable S hS hfinite a)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Weak L2 convergence becomes strong locally after a finite-frequency cutoff -/
noncomputable section
open MeasureTheory Filter Set
open scoped FourierTransform Topology
namespace BoltzmannNonuniqueness.Published

theorem fourierBandApprox_local_convergence
    {u : ℕ → Lp ℂ 2 (volume : Measure FourierSpace)} {g : Lp ℂ 2 volume}
    {C : ℝ} (hC : 0 ≤ C) (hu : ∀ n, ‖u n‖ ≤ C) (hg : ‖g‖ ≤ C)
    (hw : ∀ h : Lp ℂ 2 volume,
      Tendsto (fun n => inner ℂ (u n) h) atTop (𝓝 (inner ℂ g h)))
    (S : Set FourierSpace) (hS : MeasurableSet S) (hfinite : volume S < ⊤)
    (K : Set FourierSpace) (hK : volume K < ⊤) :
    Tendsto (fun n => ∫ x in K, ‖fourierBandApprox S (u n) x-fourierBandApprox S g x‖^2)
      atTop (𝓝 0) := by
  have : IsFiniteMeasure ((volume : Measure FourierSpace).restrict K) :=
    isFiniteMeasure_restrict.mpr hK.ne
  let B := 2*(volume.real S+1)*C
  have hb n x : ‖fourierBandApprox S (u n) x-fourierBandApprox S g x‖ ≤ B := by
    have h₁ := fourierBandApprox_norm_le S hS hfinite (u n) x
    have h₂ := fourierBandApprox_norm_le S hS hfinite g x
    have hpos : 0 ≤ volume.real S+1 := by positivity
    have h₃ := mul_le_mul_of_nonneg_left (hu n) hpos
    have h₄ := mul_le_mul_of_nonneg_left hg hpos
    have ht := norm_sub_le (fourierBandApprox S (u n) x) (fourierBandApprox S g x)
    dsimp [B]
    linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have ht := tendsto_integral_of_dominated_convergence (μ := volume.restrict K)
    (fun _ : FourierSpace => B^2)
    (fun n => (((fourierBandApprox_continuous S hS hfinite (u n)).sub
      (fourierBandApprox_continuous S hS hfinite g)).norm.pow 2).aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb n x) 2))
    (ae_of_all _ (fun x => by
      have hx := ((fourierBandApprox_tendsto hw S hS hfinite x).sub_const
        (fourierBandApprox S g x)).norm.pow 2
      simpa only [Pi.pow_apply,Pi.sub_apply,sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)] using hx))
  simpa only [Pi.pow_apply,Pi.sub_apply,integral_zero] using ht

end BoltzmannNonuniqueness.Published

end

end

section

/-! # The error of finite-frequency reconstruction is exactly its Fourier tail -/
noncomputable section
open MeasureTheory Set FourierTransform
open scoped FourierTransform
namespace BoltzmannNonuniqueness.Published

theorem complexL2Cutoff_error (S : Set FourierSpace) (hS : MeasurableSet S)
    (a : Lp ℂ 2 (volume : Measure FourierSpace)) :
    ‖a-complexL2Cutoff S hS a‖^2 = ∫ k in Sᶜ, ‖a k‖^2 := by
  rw [L2_norm_sq_integral,← integral_indicator hS.compl]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub a (complexL2Cutoff S hS a),complexL2Cutoff_ae S hS a] with k hk hc
  simp only [Pi.sub_apply] at hk
  rw [hk,hc]
  by_cases hks : k ∈ S <;> simp [hks]

theorem fourierBand_error (S : Set FourierSpace) (hS : MeasurableSet S)
    (f : Lp ℂ 2 (volume : Measure FourierSpace)) :
    ‖f-(𝓕⁻ (complexL2Cutoff S hS (𝓕 f)) : Lp ℂ 2 volume)‖^2 =
      ∫ k in Sᶜ, ‖(𝓕 f : Lp ℂ 2 volume) k‖^2 := by
  have he : f-(𝓕⁻ (complexL2Cutoff S hS (𝓕 f)) : Lp ℂ 2 volume) =
      𝓕⁻ (𝓕 f-complexL2Cutoff S hS (𝓕 f)) := by
    let L := Lp.fourierTransformₗᵢ FourierSpace ℂ
    change f-L.symm (complexL2Cutoff S hS (L f)) =
      L.symm (L f-complexL2Cutoff S hS (L f))
    rw [map_sub,L.symm_apply_apply]

  have hn (a : Lp ℂ 2 (volume : Measure FourierSpace)) : ‖𝓕⁻ a‖ = ‖a‖ := by
    simpa only [fourier_fourierInv_eq] using (Lp.norm_fourier_eq (𝓕⁻ a)).symm
  rw [he,hn,complexL2Cutoff_error]

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Local norms of finite-frequency reconstruction errors -/
noncomputable section
open MeasureTheory Filter Set FourierTransform
open scoped FourierTransform Topology
namespace BoltzmannNonuniqueness.Published

theorem inverseFourier_norm (a : Lp ℂ 2 (volume : Measure FourierSpace)) : ‖𝓕⁻ a‖ = ‖a‖ := by
  simpa only [fourier_fourierInv_eq] using (Lp.norm_fourier_eq (𝓕⁻ a)).symm

theorem inverseFourier_sub (a b : Lp ℂ 2 (volume : Measure FourierSpace)) :
    (𝓕⁻ (a-b) : Lp ℂ 2 volume) = 𝓕⁻ a-𝓕⁻ b :=
  (Lp.fourierTransformₗᵢ FourierSpace ℂ).symm.map_sub a b

theorem fourierReconstruction_error (S : Set FourierSpace) (hS : MeasurableSet S)
    (a : Lp ℂ 2 (volume : Measure FourierSpace)) :
    ‖(𝓕⁻ a : Lp ℂ 2 volume)-𝓕⁻ (complexL2Cutoff S hS a)‖ =
      ‖a-complexL2Cutoff S hS a‖ := by
  rw [← inverseFourier_sub,inverseFourier_norm]

theorem fourierReconstruction_local_band_sq (S : Set FourierSpace) (hS : MeasurableSet S)
    (hfinite : volume S < ⊤) (K : Set FourierSpace)
    (a b : Lp ℂ 2 (volume : Measure FourierSpace)) :
    ‖complexL2Restriction K ((𝓕⁻ (complexL2Cutoff S hS a) : Lp ℂ 2 volume)-
      𝓕⁻ (complexL2Cutoff S hS b))‖^2 =
      ∫ x in K, ‖fourierBandApprox S a x-fourierBandApprox S b x‖^2 := by
  rw [complexL2Restriction_norm_sq]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub (𝓕⁻ (complexL2Cutoff S hS a))
    (𝓕⁻ (complexL2Cutoff S hS b))),ae_restrict_of_ae (fourierBandApprox_ae S hS hfinite a),
    ae_restrict_of_ae (fourierBandApprox_ae S hS hfinite b)] with x hx ha hb
  simp only [Pi.sub_apply] at hx
  rw [hx,ha,hb]

theorem fourierReconstruction_local_band_tendsto
    {u : ℕ → Lp ℂ 2 (volume : Measure FourierSpace)} {g : Lp ℂ 2 volume}
    {C : ℝ} (hC : 0 ≤ C) (hu : ∀ n, ‖u n‖ ≤ C) (hg : ‖g‖ ≤ C)
    (hw : ∀ h : Lp ℂ 2 volume,
      Tendsto (fun n => inner ℂ (u n) h) atTop (𝓝 (inner ℂ g h)))
    (S : Set FourierSpace) (hS : MeasurableSet S) (hfinite : volume S < ⊤)
    (K : Set FourierSpace) (hK : volume K < ⊤) :
    Tendsto (fun n => ‖complexL2Restriction K
      ((𝓕⁻ (complexL2Cutoff S hS (u n)) : Lp ℂ 2 volume)-𝓕⁻ (complexL2Cutoff S hS g))‖)
      atTop (𝓝 0) := by
  have h := (fourierBandApprox_local_convergence hC hu hg hw S hS hfinite K hK).sqrt
  simp_rw [← fourierReconstruction_local_band_sq S hS hfinite K,Real.sqrt_sq_eq_abs,
    abs_norm] at h
  simpa only [Real.sqrt_zero] using h

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Fourier-window projections preserve weak convergence and closed norm bounds -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BoltzmannNonuniqueness.Published

theorem complexL2Cutoff_inner (S : Set FourierSpace) (hS : MeasurableSet S)
    (a b : Lp ℂ 2 (volume : Measure FourierSpace)) :
    inner ℂ (complexL2Cutoff S hS a) b = inner ℂ a (complexL2Cutoff S hS b) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [complexL2Cutoff_ae S hS a,complexL2Cutoff_ae S hS b] with x ha hb
  rw [ha,hb]
  by_cases hx : x ∈ S <;> simp [hx]

theorem complexL2Cutoff_weak_tendsto
    {u : ℕ → Lp ℂ 2 (volume : Measure FourierSpace)} {g : Lp ℂ 2 volume}
    (hw : ∀ h : Lp ℂ 2 volume,
      Tendsto (fun n => inner ℂ (u n) h) atTop (𝓝 (inner ℂ g h)))
    (S : Set FourierSpace) (hS : MeasurableSet S) (h : Lp ℂ 2 volume) :
    Tendsto (fun n => inner ℂ (complexL2Cutoff S hS (u n)) h) atTop
      (𝓝 (inner ℂ (complexL2Cutoff S hS g) h)) := by
  simpa only [complexL2Cutoff_inner] using hw (complexL2Cutoff S hS h)

theorem complexL2Cutoff_limit_bound
    {u : ℕ → Lp ℂ 2 (volume : Measure FourierSpace)} {g : Lp ℂ 2 volume}
    (hw : ∀ h : Lp ℂ 2 volume,
      Tendsto (fun n => inner ℂ (u n) h) atTop (𝓝 (inner ℂ g h)))
    (S : Set FourierSpace) (hS : MeasurableSet S) {C : ℝ}
    (hu : ∀ n, ‖complexL2Cutoff S hS (u n)‖ ≤ C) : ‖complexL2Cutoff S hS g‖ ≤ C :=
  complex_weak_norm_le hu (complexL2Cutoff_weak_tendsto hw S hS)

theorem complexL2Cutoff_compl (S : Set FourierSpace) (hS : MeasurableSet S)
    (a : Lp ℂ 2 (volume : Measure FourierSpace)) :
    a-complexL2Cutoff S hS a = complexL2Cutoff Sᶜ hS.compl a := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub a (complexL2Cutoff S hS a),complexL2Cutoff_ae S hS a,
    complexL2Cutoff_ae Sᶜ hS.compl a] with x hx hc hd
  simp only [Pi.sub_apply] at hx
  rw [hx,hc,hd]
  by_cases hxs : x ∈ S <;> simp [hxs]

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Uniform Fourier tails upgrade weak L2 convergence to local strong convergence -/
noncomputable section
open MeasureTheory Filter Set FourierTransform
open scoped FourierTransform Topology
namespace BoltzmannNonuniqueness.Published

theorem inverseFourier_local_strong_of_weak_and_tails
    {u : ℕ → Lp ℂ 2 (volume : Measure FourierSpace)} {g : Lp ℂ 2 volume}
    {C : ℝ} (hC : 0 ≤ C) (hu : ∀ n, ‖u n‖ ≤ C) (hg : ‖g‖ ≤ C)
    (hw : ∀ h : Lp ℂ 2 volume,
      Tendsto (fun n => inner ℂ (u n) h) atTop (𝓝 (inner ℂ g h)))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ S : Set FourierSpace, ∃ hS : MeasurableSet S,
      volume S < ⊤ ∧ ∀ n, ‖u n-complexL2Cutoff S hS (u n)‖ ≤ ε)
    (K : Set FourierSpace) (hK : volume K < ⊤) :
    Tendsto (fun n => ‖complexL2Restriction K ((𝓕⁻ (u n) : Lp ℂ 2 volume)-𝓕⁻ g)‖)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨S,hS,hfinite,ht⟩ := htail (ε/4) (by positivity)
  have htg : ‖g-complexL2Cutoff S hS g‖ ≤ ε/4 := by
    rw [complexL2Cutoff_compl]
    apply complexL2Cutoff_limit_bound hw Sᶜ hS.compl
    intro n
    rw [← complexL2Cutoff_compl S hS (u n)]
    exact ht n
  have hb := fourierReconstruction_local_band_tendsto hC hu hg hw S hS hfinite K hK
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hb (ε/4) (by positivity)
  refine ⟨N,?_⟩
  intro n hn
  let A := complexL2Restriction K (𝓕⁻ (u n))
  let B := complexL2Restriction K (𝓕⁻ (complexL2Cutoff S hS (u n)))
  let D := complexL2Restriction K (𝓕⁻ (complexL2Cutoff S hS g))
  let G := complexL2Restriction K (𝓕⁻ g)
  have hAB : ‖A-B‖ ≤ ε/4 := by
    dsimp [A,B]
    rw [← complexL2Restriction_sub]
    exact (complexL2Restriction_norm_le K _).trans
      ((fourierReconstruction_error S hS (u n)).le.trans (ht n))
  have hDG : ‖D-G‖ ≤ ε/4 := by
    dsimp [D,G]
    rw [norm_sub_rev,← complexL2Restriction_sub]
    exact (complexL2Restriction_norm_le K _).trans
      ((fourierReconstruction_error S hS g).le.trans htg)
  have hBD : ‖B-D‖ < ε/4 := by
    have hh := hN n hn
    rw [Real.dist_eq,sub_zero,abs_norm] at hh
    simpa only [complexL2Restriction_sub] using hh
  have htriangle : ‖A-G‖ ≤ ‖A-B‖+‖B-D‖+‖D-G‖ := by
    calc
      _ ≤ ‖A-B‖+‖B-G‖ := norm_sub_le_norm_sub_add_norm_sub A B G
      _ ≤ _ := by
        have h := norm_sub_le_norm_sub_add_norm_sub B D G
        linarith
  rw [Real.dist_eq,sub_zero,abs_norm,complexL2Restriction_sub]
  change ‖A-G‖ < ε
  linarith

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Fourier transformation commutes with an integrable velocity integral -/
noncomputable section
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

theorem fourier_velocity_integral {F : Velocity × FourierSpace → ℂ} (hF : Integrable F)
    (k : FourierSpace) :
    𝓕 (fun x => ∫ v, F (v,x)) k = ∫ v, 𝓕 (fun x => F (v,x)) k := by
  have hi : Integrable (fun p : Velocity × FourierSpace =>
      𝐞 (-inner ℝ p.2 k) • F p) := by
    apply hF.norm.mono'
    · have hm : Measurable (fun p : Velocity × FourierSpace => 𝐞 (-inner ℝ p.2 k)) := by
        fun_prop
      exact hm.aestronglyMeasurable.smul hF.aestronglyMeasurable
    · exact ae_of_all _ (fun p => (Circle.norm_smul _ _).le)
  rw [Real.fourier_eq]
  calc
    _ = ∫ x : FourierSpace, ∫ v : Velocity, 𝐞 (-inner ℝ x k) • F (v,x) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        change (𝐞 (-inner ℝ x k) : ℂ) * (∫ v, F (v,x)) = _
        rw [← integral_const_mul]
        rfl)
    _ = ∫ v : Velocity, ∫ x : FourierSpace, 𝐞 (-inner ℝ x k) • F (v,x) :=
      (integral_integral_swap (f := fun v x => 𝐞 (-inner ℝ x k) • F (v,x)) hi).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun v => (Real.fourier_eq _ _).symm)

theorem fourier_velocityLineAverage {r : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) (k : FourierSpace) :
    𝓕 (velocityLineAverage r) k = ∫ v,
      (1+Complex.I*(2*Real.pi*inner ℝ (characteristicDirection v) k))⁻¹ *
        𝓕 (fun x => r (v,x)) k := by
  change 𝓕 (fun x => ∫ v, velocityLineResolvent r (v,x)) k = _
  rw [fourier_velocity_integral (velocityLineResolvent_integrable hr)]
  apply integral_congr_ae
  filter_upwards [hr.prod_right_ae] with v hv
  exact fourier_dampedLine hv (characteristicDirection v) k

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Bounded velocity tests preserve uniform integrability in Fourier coordinates -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace BoltzmannNonuniqueness.Published

theorem fourierSource_uniformIntegrable (r : ℕ → KineticPhase → ℝ)
    (hm : ∀ n, Measurable (r n)) (hui : UniformIntegrable r 1 volume)
    (ψ : Velocity → ℝ) (hψ : Continuous ψ) (hs : HasCompactSupport ψ) :
    UniformIntegrable (fun n => fourierSource (r n) ψ) 1 volume := by
  obtain ⟨C,hC⟩ := hψ.bounded_above_of_compact_support hs
  let D : ℝ≥0 := ⟨max C 0,le_max_right _ _⟩
  apply uniformIntegrable_norm_domination (fun n => r n ∘ kineticFourierEquiv.symm)
    (fun n => fourierSource (r n) ψ)
    (uniformIntegrable_comp_equiv kineticFourierEquiv.symm kineticFourier_symm_measurePreserving r hui)
    (fun n => fourierSource_measurable (hm n) hψ.measurable) D
  intro n p
  change ‖((ψ p.1*r n (p.2.ofLp,p.1) : ℝ) : ℂ)‖ ≤ (D : ℝ)*‖r n (p.2.ofLp,p.1)‖
  rw [Complex.norm_real,Real.norm_eq_abs,abs_mul]
  exact mul_le_mul_of_nonneg_right ((hC p.1).trans (le_max_left _ _)) (abs_nonneg _)

theorem fourierSource_congr_ae {r q : KineticPhase → ℝ} (ψ : Velocity → ℝ)
    (he : r =ᵐ[volume] q) : fourierSource r ψ =ᵐ[volume] fourierSource q ψ := by
  have h := kineticFourier_symm_measurePreserving.quasiMeasurePreserving.ae_eq_comp he
  filter_upwards [h] with p hp
  change r (p.2.ofLp,p.1) = q (p.2.ofLp,p.1) at hp
  simp only [fourierSource,hp]

end BoltzmannNonuniqueness.Published

end

end

end OAI
