import Mathlib

namespace OAI

/-! Product torus, exact angular packets, all integer twist iterates, and measure-preserving passage charts. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology

noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace ThreeTorus
abbrev TripleTorus := UnitAddCircle × UnitAddCircle × UnitAddCircle
abbrev slowVolume : Measure (UnitAddCircle × UnitAddCircle) :=
  AddCircle.haarAddCircle.prod AddCircle.haarAddCircle
abbrev tripleVolume : Measure TripleTorus := AddCircle.haarAddCircle.prod slowVolume

/-- The actual angular packet, in the volume preserving coordinates of section 2. -/
def packet (m : ℤ) (A : UnitAddCircle × UnitAddCircle → ℂ) (x : TripleTorus) : ℂ :=
  A x.2 * fourier m x.1

/-- All integer powers of an intermediate twist in its coordinates. -/
def twistIter (φ : UnitAddCircle → UnitAddCircle) (n : ℤ) (x : TripleTorus) : TripleTorus :=
  (x.1+n • φ x.2.1,x.2)

lemma twistIter_add (φ : UnitAddCircle → UnitAddCircle) (n k : ℤ) (x : TripleTorus) :
    twistIter φ (n+k) x = twistIter φ n (twistIter φ k x) := by
  dsimp [twistIter]
  simp only [add_zsmul]
  congr 1
  abel

lemma fourier_zsmul (m n : ℤ) (x : UnitAddCircle) :
    fourier m (n • x) = fourier n (m • x) := by
  simp only [fourier_apply,smul_smul,mul_comm]

lemma packet_twistIter (φ : UnitAddCircle → UnitAddCircle) (n m : ℤ)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (x : TripleTorus) :
    packet m A (twistIter φ n x) = fourier n (m • φ x.2.1) * packet m A x := by
  change A x.2 * fourier m (x.1+n • φ x.2.1) =
    fourier n (m • φ x.2.1)*(A x.2*fourier m x.1)
  simp only [fourier_apply,smul_add,AddCircle.toCircle_add,Circle.coe_mul,smul_smul]
  rw [mul_comm n m]
  ring

lemma continuous_packet {m : ℤ} {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : Continuous A) : Continuous (packet m A) :=
  (hA.comp continuous_snd).mul ((fourier m).continuous.comp continuous_fst)

lemma integral_fourier_pair (m k : ℤ) :
    (∫ θ : UnitAddCircle, starRingEnd ℂ (fourier m θ)*fourier k θ
      ∂AddCircle.haarAddCircle) = if m = k then 1 else 0 := by
  have hh := (orthonormal_iff_ite.mp (orthonormal_fourier (T := (1:ℝ)))) m k
  rw [ContinuousMap.inner_toLp] at hh
  simpa only [RCLike.inner_apply,mul_comm] using hh

/-- Exact packet orthogonality, before stationary phase or any passage limit. -/
lemma integral_packet_pair {A B : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : Continuous A) (hB : Continuous B) (m k : ℤ) :
    (∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*packet k B x ∂tripleVolume) =
      if m = k then ∫ ua, starRingEnd ℂ (A ua)*B ua ∂slowVolume else 0 := by
  have hi : Integrable (fun x : TripleTorus =>
      starRingEnd ℂ (packet m A x)*packet k B x) tripleVolume :=
    ((Complex.continuous_conj.comp (continuous_packet hA)).mul
      (continuous_packet hB)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [MeasureTheory.integral_prod_symm _ hi]
  have he (ua : UnitAddCircle × UnitAddCircle) :
      (∫ θ : UnitAddCircle, starRingEnd ℂ (packet m A (θ,ua))*packet k B (θ,ua)
        ∂AddCircle.haarAddCircle) =
      (starRingEnd ℂ (A ua)*B ua)*(if m = k then 1 else 0) := by
    simp only [packet,map_mul]
    have hr (θ : UnitAddCircle) :
        starRingEnd ℂ (A ua)*starRingEnd ℂ (fourier m θ)*(B ua*fourier k θ) =
        (starRingEnd ℂ (A ua)*B ua)*(starRingEnd ℂ (fourier m θ)*fourier k θ) := by ring
    simp_rw [hr]
    rw [integral_const_mul,integral_fourier_pair]
  simp_rw [he]
  split_ifs <;> simp

lemma normSq_complex (z : ℂ) : starRingEnd ℂ z*z = (‖z‖^2 : ℝ) := by
  simp only [Complex.conj_mul',Complex.ofReal_pow]

/-- Exact correlation formula for a packet under every positive or negative power. -/
lemma packet_correlation {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : Continuous A) {φ : UnitAddCircle → UnitAddCircle} (hφ : Continuous φ)
    (m n : ℤ) :
    (∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*
      packet m A (twistIter φ n x) ∂tripleVolume) =
    ∫ ua : UnitAddCircle × UnitAddCircle,
      fourier n (m • φ ua.1)*(‖A ua‖^2 : ℝ) ∂slowVolume := by
  let B : UnitAddCircle × UnitAddCircle → ℂ :=
    fun ua => fourier n (m • φ ua.1)*A ua
  have hB : Continuous B := ((fourier n).continuous.comp
    ((hφ.comp continuous_fst).const_smul m)).mul hA
  have he : ∀ x, packet m A (twistIter φ n x) = packet m B x := by
    intro x
    rw [packet_twistIter]
    dsimp [packet,B]
    ring
  simp_rw [he]
  rw [integral_packet_pair hA hB,ite_eq_left rfl]
  apply integral_congr_ae
  filter_upwards [] with ua
  dsimp only [B]
  rw [show starRingEnd ℂ (A ua)*(fourier n (m • φ ua.1)*A ua) =
    fourier n (m • φ ua.1)*(starRingEnd ℂ (A ua)*A ua) by ring,normSq_complex]

/-- Packet spectral measure is the precise pushforward stated in (2.3). -/
def packetSpectralMeasure (φ : UnitAddCircle → UnitAddCircle) (m : ℤ)
    (A : UnitAddCircle × UnitAddCircle → ℂ) : Measure UnitAddCircle :=
  Measure.map (fun ua : UnitAddCircle × UnitAddCircle => m • φ ua.1)
    (slowVolume.withDensity (fun ua => ENNReal.ofReal (‖A ua‖^2)))

lemma packet_spectral_moment {φ : UnitAddCircle → UnitAddCircle} (hφ : Continuous φ)
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hA : Continuous A) (m n : ℤ) :
    (∫ z, fourier n z ∂packetSpectralMeasure φ m A) =
      ∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*
        packet m A (twistIter φ n x) ∂tripleVolume := by
  rw [packet_correlation hA hφ]
  unfold packetSpectralMeasure
  erw [integral_map ((hφ.measurable.comp measurable_fst).const_smul m).aemeasurable
    (fourier n).continuous.aestronglyMeasurable]
  erw [integral_withDensity_eq_integral_toReal_smul
    (hA.norm.pow 2).measurable.ennreal_ofReal (by filter_upwards [] with ua; finiteness)]
  apply integral_congr_ae
  filter_upwards [] with ua
  simp only [Pi.pow_apply,Function.comp_apply,Pi.smul_apply]
  rw [ENNReal.toReal_ofReal (sq_nonneg _),Complex.real_smul,mul_comm]

lemma continuous_fourier_parseval {f : UnitAddCircle → ℂ} (hf : Continuous f) :
    ∑' j : ℤ, ‖fourierCoeff f j‖^2 =
      ∫ θ : UnitAddCircle, ‖f θ‖^2 ∂AddCircle.haarAddCircle := by
  let F : C(UnitAddCircle,ℂ) := ⟨f,hf⟩
  have hh := tsum_sq_fourierCoeff (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ F)
  simp_rw [fourierCoeff_toLp] at hh
  erw [hh]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) AddCircle.haarAddCircle F] with θ hθ
  rw [hθ]
  rfl

/-- Exact Parseval identity for arbitrary finite smooth coefficient cutoffs. -/
lemma Fourier_cutoff_error {f : UnitAddCircle → ℂ} (hf : Continuous f)
    (S : Finset ℤ) (χ : ℤ → ℂ) :
    (∫ θ : UnitAddCircle,
      ‖f θ-∑ j ∈ S, χ j*fourierCoeff f j*fourier j θ‖^2 ∂AddCircle.haarAddCircle) =
    ∑' j : ℤ, ‖(1-(if j ∈ S then χ j else 0))*fourierCoeff f j‖^2 := by
  classical
  let g : UnitAddCircle → ℂ := fun θ =>
    f θ-∑ j ∈ S, χ j*fourierCoeff f j*fourier j θ
  have hg : Continuous g := hf.sub (continuous_finsetSum _
    (fun j _hj => continuous_const.mul (fourier j).continuous))
  rw [← continuous_fourier_parseval hg]
  congr 1
  funext j
  congr 1
  have hcoeff : fourierCoeff g j =
      fourierCoeff f j - (if j ∈ S then χ j else 0)*fourierCoeff f j := by
    change (∫ θ : UnitAddCircle, fourier (-j) θ*(f θ-
      ∑ k ∈ S, χ k*fourierCoeff f k*fourier k θ) ∂AddCircle.haarAddCircle) =
      (∫ θ : UnitAddCircle, fourier (-j) θ*f θ ∂AddCircle.haarAddCircle) -
        (if j ∈ S then χ j else 0)*fourierCoeff f j
    simp only [mul_sub,Finset.mul_sum]
    have hif : Integrable (fun θ : UnitAddCircle => fourier (-j) θ*f θ)
        AddCircle.haarAddCircle :=
      ((fourier (-j)).continuous.mul hf).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have his : Integrable (fun θ : UnitAddCircle => ∑ k ∈ S,
        fourier (-j) θ*(χ k*fourierCoeff f k*fourier k θ)) AddCircle.haarAddCircle :=
      (continuous_finsetSum _ (fun k _ => (fourier (-j)).continuous.mul
        (continuous_const.mul (fourier k).continuous))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    rw [integral_sub hif his]
    rw [integral_finsetSum]
    · congr 1
      have he (k : ℤ) :
          (∫ θ : UnitAddCircle, fourier (-j) θ*(χ k*fourierCoeff f k*fourier k θ)
            ∂AddCircle.haarAddCircle) = (χ k*fourierCoeff f k)*(if j = k then 1 else 0) := by
        simp_rw [show ∀ θ : UnitAddCircle,
          fourier (-j) θ*(χ k*fourierCoeff f k*fourier k θ) =
          (χ k*fourierCoeff f k)*(starRingEnd ℂ (fourier j θ)*fourier k θ) by
            intro θ; rw [fourier_neg]; ring]
        rw [integral_const_mul,integral_fourier_pair]
      simp_rw [he]
      by_cases hj : j ∈ S
      · rw [ite_eq_left hj,Finset.sum_eq_single j]
        · simp
        · intro k _ hk; simp [Ne.symm hk]
        · exact fun hh => (hh hj).elim
      · rw [ite_eq_right hj,zero_mul]
        apply Finset.sum_eq_zero
        intro k hk
        have hh : j ≠ k := by intro he; subst k; exact hj hk
        simp [hh]
    · intro k _
      exact ((fourier (-j)).continuous.mul (continuous_const.mul
        (fourier k).continuous)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  rw [hcoeff]
  ring_nf

/-- The exact cutoff energy is bounded by coefficient-mass error; the model
mass need not be a Fourier coefficient of any function. -/
lemma cutoff_normSq_le_mass_error {c : ℂ} {χ w : ℝ}
    (hχ : 0 ≤ χ ∧ χ ≤ 1) (hw : w ≠ 0 → χ = 1) :
    ‖(1-(χ:ℂ))*c‖^2 ≤ |‖c‖^2-w| := by
  by_cases hc : χ = 1
  · simp only [hc,Complex.ofReal_one,sub_self,zero_mul,norm_zero,zero_pow (by decide : 2 ≠ 0)]
    exact abs_nonneg _
  have hw0 : w = 0 := by_contra fun hh => hc (hw hh)
  have hnorm : ‖(1-(χ:ℂ))‖ ≤ 1 := by
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith)]
    linarith [hχ.1,hχ.2]
  rw [hw0,sub_zero,abs_of_nonneg (sq_nonneg _),norm_mul,mul_pow]
  have hs : ‖(1-(χ:ℂ))‖^2 ≤ 1 := by nlinarith [norm_nonneg (1-(χ:ℂ))]
  nlinarith [sq_nonneg ‖c‖]

lemma Fourier_cutoff_le_mass_error {f : UnitAddCircle → ℂ} (hf : Continuous f)
    (S : Finset ℤ) (χ W : ℤ → ℝ) (hχ : ∀ j, 0 ≤ χ j ∧ χ j ≤ 1)
    (hW : ∀ j, W j ≠ 0 → j ∈ S ∧ χ j = 1)
    (hE : Summable (fun j => |‖fourierCoeff f j‖^2-W j|)) :
    (∫ θ : UnitAddCircle,
      ‖f θ-∑ j ∈ S, (χ j:ℂ)*fourierCoeff f j*fourier j θ‖^2
        ∂AddCircle.haarAddCircle) ≤ ∑' j : ℤ, |‖fourierCoeff f j‖^2-W j| := by
  classical
  rw [Fourier_cutoff_error hf]
  have hb (j : ℤ) :
      ‖(1-(if j ∈ S then (χ j:ℂ) else 0))*fourierCoeff f j‖^2 ≤
        |‖fourierCoeff f j‖^2-W j| := by
    by_cases hj : j ∈ S
    · rw [ite_eq_left hj]
      exact cutoff_normSq_le_mass_error (hχ j) (fun hw => (hW j hw).2)
    · rw [ite_eq_right hj]
      have hw : W j = 0 := by_contra fun hh => hj (hW j hh).1
      simp only [sub_zero,one_mul,hw]
      exact le_abs_self _
  exact Summable.tsum_le_tsum hb (Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hb hE) hE

/-- Tonelli in real form for a summable nonnegative array. -/
lemma integrable_nonneg_tsum {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {μ : Measure Ω} {E : ι → Ω → ℝ} (hE : ∀ j, Integrable (E j) μ)
    (h0 : ∀ j a, 0 ≤ E j a) (hp : ∀ᵐ a ∂μ, Summable (fun j => E j a))
    (hs : Summable (fun j => ∫ a, E j a ∂μ)) :
    Integrable (fun a => ∑' j, E j a) μ := by
  refine ⟨(AEMeasurable.tsum (fun j => (hE j).aemeasurable)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun a => tsum_nonneg (fun j => h0 j a)))]
  calc
    (∫⁻ a, ENNReal.ofReal (∑' j, E j a) ∂μ) =
        ∫⁻ a, ∑' j, ENNReal.ofReal (E j a) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hp] with a ha
      exact ENNReal.ofReal_tsum_of_nonneg (fun j => h0 j a) ha
    _ = ∑' j, ∫⁻ a, ENNReal.ofReal (E j a) ∂μ :=
      lintegral_tsum (fun j => (hE j).aemeasurable.ennreal_ofReal)
    _ = ∑' j, ENNReal.ofReal (∫ a, E j a ∂μ) := by
      congr 1; funext j
      exact (ofReal_integral_eq_lintegral_ofReal (hE j)
        (Filter.Eventually.of_forall (h0 j))).symm
    _ = ENNReal.ofReal (∑' j, ∫ a, E j a ∂μ) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg (h0 j)) hs).symm
    _ < ∞ := ENNReal.ofReal_lt_top

/-- Integrating the genuine Fourier reconstruction error preserves the summed
stationary mass bound from (2.14), with no assertion of an L² leading phase. -/
lemma integrated_Fourier_cutoff_le_mass_error {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → UnitAddCircle → ℂ} (hf : ∀ a, Continuous (f a))
    (S : Finset ℤ) (χ W : ℤ → Ω → ℝ)
    (hχ : ∀ j a, 0 ≤ χ j a ∧ χ j a ≤ 1)
    (hW : ∀ j a, W j a ≠ 0 → j ∈ S ∧ χ j a = 1)
    (hE : ∀ j, Integrable (fun a => |‖fourierCoeff (f a) j‖^2-W j a|) μ)
    (hp : ∀ᵐ a ∂μ, Summable (fun j => |‖fourierCoeff (f a) j‖^2-W j a|))
    (hs : Summable (fun j => ∫ a, |‖fourierCoeff (f a) j‖^2-W j a| ∂μ)) :
    (∫ a, ∫ θ : UnitAddCircle,
      ‖f a θ-∑ j ∈ S, (χ j a:ℂ)*fourierCoeff (f a) j*fourier j θ‖^2
        ∂AddCircle.haarAddCircle ∂μ) ≤
      ∑' j : ℤ, ∫ a, |‖fourierCoeff (f a) j‖^2-W j a| ∂μ := by
  have hsum := integrable_nonneg_tsum hE (fun _ _ => abs_nonneg _) hp hs
  have hs' : Summable (fun j => ∫ a, ‖|‖fourierCoeff (f a) j‖^2-W j a|‖ ∂μ) := by
    simpa only [Real.norm_eq_abs,abs_abs] using hs
  rw [integral_tsum_of_summable_integral_norm hE hs']
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => integral_nonneg (fun _ => sq_nonneg _))) hsum
  filter_upwards [hp] with a ha
  exact Fourier_cutoff_le_mass_error (hf a) S (fun j => χ j a) (fun j => W j a)
    (fun j => hχ j a) (fun j => hW j a) ha

end ThreeTorus

namespace ThreeTorus
def circleCycle : TripleTorus ≃ TripleTorus where
  toFun x := (x.2.1,x.2.2,x.1)
  invFun x := (x.2.2,x.1,x.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

def circleThetaShear (H : UnitAddCircle → UnitAddCircle) : TripleTorus ≃ TripleTorus where
  toFun x := (x.1+H x.2.1,x.2)
  invFun x := (x.1-H x.2.1,x.2)
  left_inv x := by simp
  right_inv x := by simp

def passageChart (H : UnitAddCircle → UnitAddCircle) : TripleTorus ≃ TripleTorus :=
  (circleThetaShear (fun u => -H u)).trans circleCycle

def passageTwist (σ : UnitAddCircle → UnitAddCircle) : TripleTorus ≃ TripleTorus :=
  circleThetaShear σ

def passageMap (H σ : UnitAddCircle → UnitAddCircle) : TripleTorus ≃ TripleTorus where
  toFun x := (x.1+H (x.2.1+σ x.2.2)-H x.2.1, x.2.1+σ x.2.2, x.2.2)
  invFun x := (x.1-H x.2.1+H (x.2.1-σ x.2.2), x.2.1-σ x.2.2, x.2.2)
  left_inv x := by
    simp only [add_sub_cancel_right]
    ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  right_inv x := by
    simp only [sub_add_cancel]
    ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma passage_conjugacy (H σ : UnitAddCircle → UnitAddCircle) (x : TripleTorus) :
    passageChart H (passageMap H σ ((passageChart H).symm x)) = passageTwist σ x := by
  simp only [passageChart, passageMap, passageTwist, circleThetaShear, circleCycle,
    Equiv.trans_apply, Equiv.symm_trans_apply]
  ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma measurePreserving_circleCycle :
    MeasurePreserving circleCycle tripleVolume tripleVolume := by
  exact (measurePreserving_prodAssoc AddCircle.haarAddCircle AddCircle.haarAddCircle
    AddCircle.haarAddCircle).comp Measure.measurePreserving_swap

lemma measurePreserving_fiberTranslate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {g : Ω → UnitAddCircle} (hg : Measurable g) :
    MeasurePreserving (fun p : Ω × UnitAddCircle => (p.1,p.2+g p.1))
      (μ.prod AddCircle.haarAddCircle) (μ.prod AddCircle.haarAddCircle) := by
  exact (MeasurePreserving.id μ).skew_product (measurable_snd.add (hg.comp measurable_fst))
    (Filter.Eventually.of_forall (fun x => (measurePreserving_add_right AddCircle.haarAddCircle (g x)).map_eq))

lemma measurePreserving_circleThetaShear {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H) :
    MeasurePreserving (circleThetaShear H) tripleVolume tripleVolume := by
  exact Measure.measurePreserving_swap.comp
    ((measurePreserving_fiberTranslate (AddCircle.haarAddCircle.prod AddCircle.haarAddCircle)
      (hH.comp measurable_fst)).comp Measure.measurePreserving_swap)

lemma measurePreserving_passageChart {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H) :
    MeasurePreserving (passageChart H) tripleVolume tripleVolume :=
  measurePreserving_circleCycle.comp (measurePreserving_circleThetaShear hH.neg)

lemma passageChart_inverse_measurable {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H) :
    Measurable (passageChart H).symm := by
  change Measurable (fun x : TripleTorus => (x.2.2-(-H x.1),x.1,x.2.1))
  exact (measurable_snd.snd.sub (hH.comp measurable_fst).neg).prodMk
    (measurable_fst.prodMk measurable_snd.fst)

lemma measurePreserving_passageChart_inverse {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H) :
    MeasurePreserving (passageChart H).symm tripleVolume tripleVolume := by
  let e : TripleTorus ≃ᵐ TripleTorus :=
    { toEquiv := passageChart H
      measurable_toFun := (measurePreserving_passageChart hH).measurable
      measurable_invFun := passageChart_inverse_measurable hH }
  exact MeasurePreserving.symm e (measurePreserving_passageChart hH)

lemma passage_as_conjugate (H σ : UnitAddCircle → UnitAddCircle) :
    (passageMap H σ : TripleTorus → TripleTorus) =
      (passageChart H).symm ∘ passageTwist σ ∘ passageChart H := by
  funext x
  have hh := passage_conjugacy H σ (passageChart H x)
  simpa only [Equiv.symm_apply_apply, Function.comp_apply] using
    congrArg (passageChart H).symm hh

lemma measurePreserving_passageMap {H σ : UnitAddCircle → UnitAddCircle}
    (hH : Measurable H) (hσ : Measurable σ) :
    MeasurePreserving (passageMap H σ) tripleVolume tripleVolume := by
  rw [passage_as_conjugate]
  exact (measurePreserving_passageChart_inverse hH).comp
    ((measurePreserving_circleThetaShear hσ).comp (measurePreserving_passageChart hH))

end ThreeTorus

end

end

end OAI
