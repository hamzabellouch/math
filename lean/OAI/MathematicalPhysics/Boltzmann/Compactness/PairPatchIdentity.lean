import OAI.MathematicalPhysics.Boltzmann.Admissibility
import OAI.MathematicalPhysics.Boltzmann.Branching.SmoothTestFamily
import OAI.MathematicalPhysics.Boltzmann.Branching.SupportedTensorConvergence
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedPairUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Model
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

section

/-! # Strong L1 continuity of translations on the outgoing velocity-pair space -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

local instance pairTranslationHaar : Measure.IsAddHaarMeasure (volume : Measure (Velocity × Velocity)) :=
  Measure.prod.instIsAddHaarMeasure _ _

local instance pairTranslationRegular : (volume : Measure (Velocity × Velocity)).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

private def pairTranslation (a : Velocity × Velocity) : C(Velocity × Velocity,Velocity × Velocity) :=
  ⟨fun p => p+a,continuous_id.add continuous_const⟩

private theorem pairTranslation_continuous : Continuous pairTranslation :=
  ContinuousMap.continuous_of_continuous_uncurry pairTranslation (continuous_snd.add continuous_fst)

private theorem pairTranslation_preserving (a : Velocity × Velocity) :
    MeasurePreserving (pairTranslation a) (volume : Measure (Velocity × Velocity)) volume :=
  measurePreserving_add_right volume a

theorem pair_translation_L1 {f : Velocity × Velocity → ℝ} (hf : Integrable f)
    (a : Velocity × Velocity) :
    Tendsto (fun b => eLpNorm (fun p => f (p+b)-f (p+a)) 1 volume) (𝓝 a) (𝓝 0) := by
  let hf₁ := memLp_one_iff_integrable.mpr hf
  let u : Lp ℝ 1 (volume : Measure (Velocity × Velocity)) := hf₁.toLp f
  have hu : u =ᵐ[volume] f := hf₁.coeFn_toLp
  have hc : Continuous (fun b => Lp.compMeasurePreserving (pairTranslation b)
      (pairTranslation_preserving b) u) :=
    continuous_const.compMeasurePreservingLp pairTranslation_continuous
      pairTranslation_preserving (by norm_num)
  have hrep b : Lp.compMeasurePreserving (pairTranslation b) (pairTranslation_preserving b) u =ᵐ[volume]
      (fun p => f (p+b)) := by
    filter_upwards [Lp.coeFn_compMeasurePreserving u (pairTranslation_preserving b),
      (pairTranslation_preserving b).quasiMeasurePreserving.ae hu] with p hp hpu
    exact hp.trans hpu
  have he b : edist (Lp.compMeasurePreserving (pairTranslation b) (pairTranslation_preserving b) u)
      (Lp.compMeasurePreserving (pairTranslation a) (pairTranslation_preserving a) u) =
      eLpNorm (fun p => f (p+b)-f (p+a)) 1 volume := by
    rw [Lp.edist_def]
    exact eLpNorm_congr_ae ((hrep b).sub (hrep a))
  simpa only [he] using tendsto_iff_edist_tendsto_0.mp (hc.tendsto a)

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Bounded tests of a velocity-pair density -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

def pairTestAverage (k : Velocity × Velocity → ℝ) (P : X × (Velocity × Velocity) → ℝ)
    (x : X) : ℝ := ∫ y : Velocity × Velocity, k y*P (x,y)

omit [SFinite μ] in
theorem pairTestAverage_integrable {P : X × (Velocity × Velocity) → ℝ}
    (hP : Integrable P (μ.prod volume)) {k : Velocity × Velocity → ℝ}
    (hk : Measurable k) (C : ℝ) (hC : ∀ y, |k y| ≤ C) :
    Integrable (pairTestAverage k P) μ :=
  (hP.bdd_mul (hk.comp measurable_snd).aestronglyMeasurable (ae_of_all _ (fun p => hC p.2))).integral_prod_left

theorem pairTestAverage_add {P : X × (Velocity × Velocity) → ℝ}
    (hP : Integrable P (μ.prod volume)) {k l : C(Velocity × Velocity,ℝ)}
    (hk : HasCompactSupport k) (hl : HasCompactSupport l) :
    pairTestAverage (k+l : C(Velocity × Velocity,ℝ)) P =ᵐ[μ] fun x => pairTestAverage k P x+pairTestAverage l P x := by
  obtain ⟨C,hC⟩ := k.continuous.bounded_above_of_compact_support hk
  obtain ⟨D,hD⟩ := l.continuous.bounded_above_of_compact_support hl
  filter_upwards [hP.prod_right_ae] with x hx
  change (∫ y : Velocity × Velocity, (k y+l y)*P (x,y)) = _
  simp_rw [add_mul]
  exact integral_add (hx.bdd_mul k.continuous.measurable.aestronglyMeasurable (ae_of_all _ hC))
    (hx.bdd_mul l.continuous.measurable.aestronglyMeasurable (ae_of_all _ hD))

omit [MeasurableSpace X] in
theorem pairTestAverage_smul (c : ℝ) (k : C(Velocity × Velocity,ℝ))
    (P : X × (Velocity × Velocity) → ℝ) (x : X) :
    pairTestAverage (c • k : C(Velocity × Velocity,ℝ)) P x = c*pairTestAverage k P x := by
  change (∫ y : Velocity × Velocity, (c*k y)*P (x,y)) = c*∫ y : Velocity × Velocity, k y*P (x,y)
  simp only [mul_assoc,integral_const_mul]

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Countable tensor tests determine an integrable velocity-pair density -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.Compactness

theorem pair_tests_determine {ψ : ℕ → Velocity → ℝ}
    (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i)) (hc : ∀ i, HasCompactSupport (ψ i))
    (hdet : ∀ u : Velocity → ℝ, Integrable u → (∀ i, ∫ v, ψ i v*u v = 0) → u =ᵐ[volume] 0)
    {F : Velocity × Velocity → ℝ} (hFm : Measurable F) (hFi : Integrable F)
    (hz : ∀ i j, ∫ z, (ψ i z.1*ψ j z.2)*F z = 0) : F =ᵐ[volume] 0 := by
  have hF : Integrable F ((volume : Measure Velocity).prod volume) := by
    simpa only [← Measure.volume_eq_prod] using hFi
  have hbound (i) : ∃ C : ℝ, ∀ v, |ψ i v| ≤ C :=
    (hψ i).continuous.bounded_above_of_compact_support (hc i)
  have hm (i) : Integrable (fun z : Velocity × Velocity => ψ i z.1*F z)
      ((volume : Measure Velocity).prod volume) := by
    obtain ⟨C,hC⟩ := hbound i
    exact hF.bdd_mul ((hψ i).continuous.measurable.comp measurable_fst).aestronglyMeasurable
      (ae_of_all _ (fun z => hC z.1))
  have hzero (i) : (fun w => ∫ v, ψ i v*F (v,w)) =ᵐ[volume] 0 := by
    apply hdet _ (hm i).integral_prod_right
    intro j
    obtain ⟨D,hD⟩ := hbound j
    have hmul := (hm i).bdd_mul
      ((hψ j).continuous.measurable.comp measurable_snd).aestronglyMeasurable
      (ae_of_all _ (fun z => hD z.2))
    change Integrable (fun z : Velocity × Velocity => ψ j z.2*(ψ i z.1*F z))
      ((volume : Measure Velocity).prod volume) at hmul
    calc
      _ = ∫ z : Velocity × Velocity, ψ j z.2*(ψ i z.1*F z)
          ∂((volume : Measure Velocity).prod volume) := by
        rw [integral_prod_symm _ hmul]
        simp_rw [integral_const_mul]
      _ = ∫ z : Velocity × Velocity, (ψ i z.1*ψ j z.2)*F z := by
        rw [Measure.volume_eq_prod]
        congr 1
        ext z
        ring
      _ = 0 := hz i j
  have hs : MeasurableSet {z : Velocity × Velocity | F z = 0} := hFm (isClosed_singleton.measurableSet)
  have hfib : ∀ᵐ w ∂(volume : Measure Velocity), ∀ᵐ v ∂(volume : Measure Velocity), F (v,w) = 0 := by
    filter_upwards [ae_all_iff.mpr hzero,hF.prod_left_ae] with w hw hfw
    exact hdet (fun v => F (v,w)) hfw hw
  have hall : ∀ᵐ z ∂((volume : Measure Velocity).prod volume), F z = 0 :=
    (Measure.ae_prod_iff_ae_ae hs).mpr ((Measure.ae_ae_comm hs).mpr hfib)
  rw [Measure.volume_eq_prod]
  exact hall

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Uniform velocity-pair test errors are bounded by the pair L1 mass -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem pairTestAverage_uniform_error {P : X × (Velocity × Velocity) → ℝ}
    (hPm : Measurable P) (hPi : Integrable P (μ.prod volume))
    {k l : C(Velocity × Velocity,ℝ)} (hk : HasCompactSupport k) (hl : HasCompactSupport l)
    {ε : ℝ} (hε : ∀ y, |k y-l y| ≤ ε) :
    eLpNorm (fun x => pairTestAverage k P x-pairTestAverage l P x) 1 μ ≤
      ENNReal.ofReal ε*eLpNorm P 1 (μ.prod volume) := by
  obtain ⟨C,hC⟩ := k.continuous.bounded_above_of_compact_support hk
  obtain ⟨D,hD⟩ := l.continuous.bounded_above_of_compact_support hl
  have he : (fun x => pairTestAverage k P x-pairTestAverage l P x) =ᵐ[μ]
      fun x => ∫ y : Velocity × Velocity, (k y-l y)*P (x,y) := by
    filter_upwards [hPi.prod_right_ae] with x hx
    have hi₁ := hx.bdd_mul k.continuous.measurable.aestronglyMeasurable (ae_of_all _ hC)
    have hi₂ := hx.bdd_mul l.continuous.measurable.aestronglyMeasurable (ae_of_all _ hD)
    rw [pairTestAverage,pairTestAverage,← integral_sub hi₁ hi₂]
    apply integral_congr_ae
    exact ae_of_all _ (fun y => (sub_mul _ _ _).symm)
  rw [eLpNorm_congr_ae he]
  have hm : Measurable (fun p : X × (Velocity × Velocity) => (k p.2-l p.2)*P p) :=
    ((k.continuous.measurable.sub l.continuous.measurable).comp measurable_snd).mul hPm
  apply (eLpNorm_integral_le hm).trans
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm.aestronglyMeasurable
  filter_upwards [] with p
  rw [norm_mul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hε p.2) (norm_nonneg _)

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Tensor moments identify the full velocity-pair product -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.Compactness

theorem pair_eq_product_of_moments {ψ : ℕ → Velocity → ℝ}
    (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i)) (hc : ∀ i, HasCompactSupport (ψ i))
    (hdet : ∀ u : Velocity → ℝ, Integrable u → (∀ i, ∫ v, ψ i v*u v = 0) → u =ᵐ[volume] 0)
    {W : Velocity × Velocity → ℝ} {g : Velocity → ℝ}
    (hWm : Measurable W) (hgm : Measurable g) (hWi : Integrable W) (hgi : Integrable g)
    (hmom : ∀ i j, (∫ z, (ψ i z.1*ψ j z.2)*W z) =
      (∫ v, ψ i v*g v)*(∫ w, ψ j w*g w)) :
    W =ᵐ[volume] (fun z => g z.1*g z.2) := by
  have hgmul : Integrable (fun z : Velocity × Velocity => g z.1*g z.2) := by
    rw [Measure.volume_eq_prod]
    exact hgi.mul_prod hgi
  have hprodMeas : Measurable (fun z : Velocity × Velocity => g z.1*g z.2) := by fun_prop
  have hd := hWi.sub hgmul
  have hdm := hWm.sub hprodMeas
  have htest (i j) {u : Velocity × Velocity → ℝ} (hi : Integrable u) :
      Integrable (fun z : Velocity × Velocity => (ψ i z.1*ψ j z.2)*u z) := by
    obtain ⟨C,hC⟩ := (hψ i).continuous.bounded_above_of_compact_support (hc i)
    obtain ⟨D,hD⟩ := (hψ j).continuous.bounded_above_of_compact_support (hc j)
    apply hi.bdd_mul (by fun_prop)
    exact ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul ((hC z.1).trans (le_abs_self C)) ((hD z.2).trans (le_abs_self D))
        (abs_nonneg _) (abs_nonneg _))
  have hz (i j) : (∫ z : Velocity × Velocity,
      (ψ i z.1*ψ j z.2)*(W z-g z.1*g z.2)) = 0 := by
    have hsplit : (fun z : Velocity × Velocity => (ψ i z.1*ψ j z.2)*(W z-g z.1*g z.2)) =
        fun z => (ψ i z.1*ψ j z.2)*W z-(ψ i z.1*ψ j z.2)*(g z.1*g z.2) := by
      funext z
      ring
    rw [hsplit,integral_sub (htest i j hWi) (htest i j hgmul),hmom i j]
    have he : (∫ z : Velocity × Velocity, (ψ i z.1*ψ j z.2)*(g z.1*g z.2)) =
        (∫ v, ψ i v*g v)*(∫ w, ψ j w*g w) := by
      calc
        _ = ∫ z : Velocity × Velocity, (ψ i z.1*g z.1)*(ψ j z.2*g z.2) := by
          congr 1
          ext z
          ring
        _ = _ := by
          rw [Measure.volume_eq_prod]
          exact integral_prod_mul (fun v => ψ i v*g v) (fun w => ψ j w*g w)
    rw [he,sub_self]
  have he := pair_tests_determine hψ hc hdet hdm hd hz
  filter_upwards [he] with z hz
  exact sub_eq_zero.mp hz

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Removing a nonzero spacetime cutoff from tensor moments -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.Compactness

theorem unscale_pair_moment {W : Velocity × Velocity → ℝ} {g p q : Velocity → ℝ}
    {c : ℝ} (hc : c ≠ 0)
    (h : (∫ y : Velocity × Velocity, ((c*p y.1)*(c*q y.2))*W y) =
      (∫ v, (c*p v)*g v)*(∫ w, (c*q w)*g w)) :
    (∫ y : Velocity × Velocity, (p y.1*q y.2)*W y) =
      (∫ v, p v*g v)*(∫ w, q w*g w) := by
  have hleft : (fun y : Velocity × Velocity => ((c*p y.1)*(c*q y.2))*W y) =
      fun y => (c*c)*((p y.1*q y.2)*W y) := by funext y; ring
  have hp : (∫ v, (c*p v)*g v) = c*(∫ v, p v*g v) := by
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  have hq : (∫ v, (c*q v)*g v) = c*(∫ v, q v*g v) := by
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  rw [hleft,integral_const_mul,hp,hq] at h
  apply mul_left_cancel₀ (mul_ne_zero hc hc)
  calc
    _ = (c*(∫ v, p v*g v))*(c*(∫ w, q w*g w)) := h
    _ = _ := by ring

theorem pair_identity_on_patch {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {ψ : ℕ → Velocity → ℝ}
    (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i)) (hc : ∀ i, HasCompactSupport (ψ i))
    (hdet : ∀ u : Velocity → ℝ, Integrable u → (∀ i, ∫ v, ψ i v*u v = 0) → u =ᵐ[volume] 0)
    {W : X × (Velocity × Velocity) → ℝ} {g : X × Velocity → ℝ}
    (hWm : Measurable W) (hgm : Measurable g)
    (hWi : Integrable W (μ.prod volume)) (hgi : Integrable g (μ.prod volume))
    (χ : X → ℝ)
    (hmom : ∀ i j, ∀ᵐ x ∂μ, χ x ≠ 0 →
      (∫ y : Velocity × Velocity, ((χ x*ψ i y.1)*(χ x*ψ j y.2))*W (x,y)) =
        (∫ v, (χ x*ψ i v)*g (x,v))*(∫ w, (χ x*ψ j w)*g (x,w))) :
    ∀ᵐ x ∂μ, χ x ≠ 0 → (fun y => W (x,y)) =ᵐ[volume]
      (fun y : Velocity × Velocity => g (x,y.1)*g (x,y.2)) := by
  have hm : ∀ᵐ x ∂μ, ∀ i j, χ x ≠ 0 →
      (∫ y : Velocity × Velocity, ((χ x*ψ i y.1)*(χ x*ψ j y.2))*W (x,y)) =
        (∫ v, (χ x*ψ i v)*g (x,v))*(∫ w, (χ x*ψ j w)*g (x,w)) :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (hmom i))
  filter_upwards [hm,hWi.prod_right_ae,hgi.prod_right_ae] with x hx hWx hgx hχ
  apply pair_eq_product_of_moments hψ hc hdet
    (hWm.comp measurable_prodMk_left) (hgm.comp measurable_prodMk_left) hWx hgx
  intro i j
  exact unscale_pair_moment hχ (hx i j hχ)

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
