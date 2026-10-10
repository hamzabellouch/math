import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.ZPow
import OAI.AlgebraicGeometry.PlaneCurves.CubicEvaluation
import OAI.AlgebraicGeometry.PlaneCurves.ThetaSections

namespace OAI

/-!
# Evaluation kernels and orbit jets of theta sections
-/

section

noncomputable section

namespace Nagata.W07

open Nagata.W08 Filter Topology

theorem section_zero_mul_iff {τ γ z : ℂ} {n : ℤ} (hγ : γ ≠ 0) (hz : z ≠ 0)
    (f : automorphicSections τ n γ) : f.val (τ * z) = 0 ↔ f.val z = 0 := by
  rw [f.property.2.2 z hz]
  simp only [mul_eq_zero, hγ, zpow_ne_zero _ hz, false_or]

/-- Differentiate the actual automorphy equation at a zero. -/
theorem section_deriv_mul_at_zero {τ γ z : ℂ} {n : ℤ}
    (hτ : τ ≠ 0) (hz : z ≠ 0) (f : automorphicSections τ n γ)
    (hfz : f.val z = 0) :
    deriv f.val (τ * z) * τ = (γ * z ^ (-n)) * deriv f.val z := by
  have hl := (f.property.2.1 (τ * z) (mul_ne_zero hτ hz)).hasDerivAt.comp z
    (hasDerivAt_const_mul τ (x := z))
  have hA : DifferentiableAt ℂ (fun w : ℂ => γ * w ^ (-n)) z :=
    ((hasDerivAt_zpow (-n) z (Or.inl hz)).const_mul γ).differentiableAt
  have hr := hA.hasDerivAt.mul (f.property.2.1 z hz).hasDerivAt
  have heq : (fun w : ℂ => f.val (τ * w)) =ᶠ[𝓝 z]
      (fun w => (γ * w ^ (-n)) * f.val w) :=
    (eventually_ne_nhds hz).mono fun w hw => f.property.2.2 w hw
  have he := (hl.congr_of_eventuallyEq heq.symm).unique hr
  simpa only [hfz, mul_zero, zero_add] using he

theorem section_firstJet_zero_mul_iff {τ γ z : ℂ} {n : ℤ}
    (hτ : τ ≠ 0) (hγ : γ ≠ 0) (hz : z ≠ 0) (f : automorphicSections τ n γ) :
    (f.val (τ * z) = 0 ∧ deriv f.val (τ * z) = 0) ↔
      f.val z = 0 ∧ deriv f.val z = 0 := by
  constructor
  · rintro ⟨hf, hd⟩
    have hfz := (section_zero_mul_iff hγ hz f).mp hf
    refine ⟨hfz, ?_⟩
    have he := section_deriv_mul_at_zero hτ hz f hfz
    rw [hd, zero_mul] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (mul_ne_zero hγ (zpow_ne_zero _ hz))
  · rintro ⟨hf, hd⟩
    refine ⟨(section_zero_mul_iff hγ hz f).mpr hf, ?_⟩
    have he := section_deriv_mul_at_zero hτ hz f hf
    rw [hd, mul_zero] at he
    exact (mul_eq_zero.mp he).resolve_right hτ

/-- Invariance under one invertible generator implies invariance under all integer powers. -/
theorem invariant_zpow {G α : Type*} [CommGroup G] (τ : G) (F : G → α)
    (hstep : ∀ z, F (τ * z) = F z) (z : G) (k : ℤ) : F (τ ^ k * z) = F z := by
  have he : (fun k : ℤ => F (τ ^ k * z)) = (fun _ : ℤ => F z) := by
    apply Nagata.W08.biInfinite_unique (fun _ x => x)
    · intro _ _ _ h
      exact h
    · intro j
      rw [zpow_add, zpow_one, mul_comm (τ ^ j) τ, mul_assoc]
      exact hstep (τ ^ j * z)
    · intro _
      rfl
    · simp
  exact congrFun he k

theorem section_zero_orbit_iff {τ γ a : ℂ} {n : ℤ}
    (hτ : τ ≠ 0) (hγ : γ ≠ 0) (ha : a ≠ 0)
    (f : automorphicSections τ n γ) (k : ℤ) :
    f.val (τ ^ k * a) = 0 ↔ f.val a = 0 := by
  let τu : ℂˣ := Units.mk0 τ hτ
  let au : ℂˣ := Units.mk0 a ha
  have h := invariant_zpow τu (fun z : ℂˣ => f.val (z : ℂ) = 0)
    (fun z => propext (section_zero_mul_iff hγ z.ne_zero f)) au k
  simpa [τu, au] using Iff.of_eq h

theorem section_firstJet_zero_orbit_iff {τ γ a : ℂ} {n : ℤ}
    (hτ : τ ≠ 0) (hγ : γ ≠ 0) (ha : a ≠ 0)
    (f : automorphicSections τ n γ) (k : ℤ) :
    (f.val (τ ^ k * a) = 0 ∧ deriv f.val (τ ^ k * a) = 0) ↔
      f.val a = 0 ∧ deriv f.val a = 0 := by
  let τu : ℂˣ := Units.mk0 τ hτ
  let au : ℂˣ := Units.mk0 a ha
  have h := invariant_zpow τu
    (fun z : ℂˣ => f.val (z : ℂ) = 0 ∧ deriv f.val (z : ℂ) = 0)
    (fun z => propext (section_firstJet_zero_mul_iff hτ hγ z.ne_zero f)) au k
  simpa [τu, au] using Iff.of_eq h

/-- Order at least one means the ordinary value vanishes, including the zero section. -/
theorem section_order_one_iff {τ γ z : ℂ} {n : ℤ}
    (f : automorphicSections τ n γ) (hz : z ≠ 0) :
    (1 : ℕ∞) ≤ analyticOrderAt f.val z ↔ f.val z = 0 := by
  have h := natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (n := 1) (automorphicSection_analyticAt f hz)
  simpa using h

/-- Order at least two means the actual value and first derivative both vanish. -/
theorem section_order_two_iff {τ γ z : ℂ} {n : ℤ}
    (f : automorphicSections τ n γ) (hz : z ≠ 0) :
    (2 : ℕ∞) ≤ analyticOrderAt f.val z ↔ f.val z = 0 ∧ deriv f.val z = 0 := by
  rw [show (2 : ℕ∞) = ((2 : ℕ) : ℕ∞) by rfl,
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (automorphicSection_analyticAt f hz)]
  constructor
  · intro h
    exact ⟨by simpa using h 0 (by omega), by simpa using h 1 (by omega)⟩
  · rintro ⟨hf, hd⟩ i hi
    have hcases : i = 0 ∨ i = 1 := by omega
    rcases hcases with rfl | rfl
    · simpa using hf
    · simpa using hd

end Nagata.W07

end
end

section

noncomputable section

namespace Nagata.W07

open Nagata.W08 Nagata.CoefficientSpaces

/-- Multiplication by the actual marked theta section to its `k`th power. -/
def pointThetaMultiply {τ a : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0)
    (n : ℤ) (γ : ℂ) (k : ℕ) :
    automorphicSections τ (n - (k : ℤ)) (γ / (-a) ^ k) →ₗ[ℂ]
      automorphicSections τ n γ :=
  LinearMap.codRestrict (automorphicSections τ n γ)
    (multiplySection τ (γ / (-a) ^ k) (n - (k : ℤ))
      (thetaProductSection hτ hτ0 ha).val k) (by
    intro G
    change multiplyPower (thetaProductSection hτ hτ0 ha).val k G.val ∈
      automorphicSections τ n γ
    have h := multiplyPower_mem_sections (thetaProductSection hτ hτ0 ha).property G.property k
    have hdeg : n - (k : ℤ) + (k : ℤ) * 1 = n := by ring
    have hgam : (γ / (-a) ^ k) * (-a) ^ k = γ :=
      div_mul_cancel₀ γ (pow_ne_zero k (neg_ne_zero.mpr ha))
    simpa only [hdeg, hgam] using h)

@[simp] theorem pointThetaMultiply_apply {τ a : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (n : ℤ) (γ : ℂ) (k : ℕ)
    (G : automorphicSections τ (n - (k : ℤ)) (γ / (-a) ^ k)) (z : ℂ) :
    (pointThetaMultiply hτ hτ0 ha n γ k G).val z =
      (thetaProductSection hτ hτ0 ha).val z ^ k * G.val z := rfl

/-- The actual theta multiplier has finite zero order at every genuine point. -/
theorem pointTheta_order_ne_top {τ a z : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0) :
    analyticOrderAt (thetaProductSection hτ hτ0 ha).val z ≠ ⊤ := by
  by_cases hP : (thetaProductSection hτ hτ0 ha).val z = 0
  · rw [(automorphicSection_analyticAt _ hz).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      hP (thetaProductSection_zero_has_nonzero_deriv hτ hτ0 ha hz hP)]
    simp
  · rw [(automorphicSection_analyticAt _ hz).analyticOrderAt_eq_zero.mpr hP]
    simp

theorem pointThetaMultiply_injective {τ a : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (n : ℤ) (γ : ℂ) (k : ℕ) :
    Function.Injective (pointThetaMultiply hτ hτ0 ha n γ k) := by
  have hinj := multiplySection_injective τ (γ / (-a) ^ k) (n - (k : ℤ))
    (thetaProductSection hτ hτ0 ha).val k
    (automorphicSection_analyticOnNhd _) (fun z hz => pointTheta_order_ne_top hτ hτ0 ha hz)
  intro f g hfg
  apply hinj
  exact congrArg Subtype.val hfg

/-- Dividing a section vanishing at the marked point by its genuine theta factor. -/
theorem pointThetaMultiply_range_eq_eval_kernel {τ a γ : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hγ : γ ≠ 0) (n : ℤ) :
    LinearMap.range (pointThetaMultiply hτ hτ0 ha n γ 1) =
      LinearMap.ker (sectionEval τ n γ a) := by
  ext f
  constructor
  · rintro ⟨G, rfl⟩
    change (thetaProductSection hτ hτ0 ha).val a ^ 1 * G.val a = 0
    simp
  · intro hf
    have hfa : f.val a = 0 := hf
    have hzero : ∀ z ≠ 0, (thetaProductSection hτ hτ0 ha).val z = 0 →
        deriv (thetaProductSection hτ hτ0 ha).val z ≠ 0 ∧
          (1 : ℕ∞) ≤ analyticOrderAt f.val z := by
      intro z hz hP
      refine ⟨thetaProductSection_zero_has_nonzero_deriv hτ hτ0 ha hz hP, ?_⟩
      apply (section_order_one_iff f hz).mpr
      obtain ⟨k, hk⟩ := (thetaProductSection_zero_iff hτ hτ0 ha hz).mp hP
      rw [hk, mul_comm a]
      exact (section_zero_orbit_iff hτ0 hγ ha f k).mpr hfa
    obtain ⟨G, hG⟩ : ∃ G : automorphicSections τ (n - (1 : ℤ)) (γ / (-a) ^ 1),
        ∀ z ≠ 0, f.val z = (thetaProductSection hτ hτ0 ha).val z ^ 1 * G.val z := by
      obtain ⟨G, hG⟩ := exists_holomorphic_quotient hτ0 (neg_ne_zero.mpr ha)
        f (thetaProductSection hτ hτ0 ha) 1 hzero
      refine ⟨⟨G.val, ?_⟩, hG⟩
      simpa only [Nat.cast_one, mul_one] using G.property
    refine ⟨G, automorphicSections_ext _ _ ?_⟩
    intro z hz
    exact (hG z hz).symm

/-- The square of the actual theta factor identifies the genuine double-point kernel. -/
theorem pointThetaMultiply_range_eq_firstJet_kernel {τ a γ : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hγ : γ ≠ 0) (n : ℤ) :
    LinearMap.range (pointThetaMultiply hτ hτ0 ha n γ 2) =
      LinearMap.ker (sectionFirstJet τ n γ ha) := by
  ext f
  constructor
  · rintro ⟨G, rfl⟩
    apply (mem_sectionFirstJet_ker τ n γ ha _).mpr
    constructor
    · change (thetaProductSection hτ hτ0 ha).val a ^ 2 * G.val a = 0
      simp
    · change deriv ((thetaProductSection hτ hτ0 ha).val ^ 2 * G.val) a = 0
      have hd := (((thetaProductSection hτ hτ0 ha).property.2.1 a ha).hasDerivAt.pow 2).mul
        (G.property.2.1 a ha).hasDerivAt
      simpa only [Pi.pow_apply, Pi.mul_apply, thetaProductSection_at_mark,
        zero_pow (by decide : 2 ≠ 0),
        zero_pow (by decide : 2 - 1 ≠ 0), mul_zero, zero_mul, add_zero, zero_add] using hd.deriv
  · intro hf
    have hfa := (mem_sectionFirstJet_ker τ n γ ha f).mp hf
    have hzero : ∀ z ≠ 0, (thetaProductSection hτ hτ0 ha).val z = 0 →
        deriv (thetaProductSection hτ hτ0 ha).val z ≠ 0 ∧
          (2 : ℕ∞) ≤ analyticOrderAt f.val z := by
      intro z hz hP
      refine ⟨thetaProductSection_zero_has_nonzero_deriv hτ hτ0 ha hz hP, ?_⟩
      apply (section_order_two_iff f hz).mpr
      obtain ⟨k, hk⟩ := (thetaProductSection_zero_iff hτ hτ0 ha hz).mp hP
      rw [hk, mul_comm a]
      exact (section_firstJet_zero_orbit_iff hτ0 hγ ha f k).mpr hfa
    obtain ⟨G, hG⟩ : ∃ G : automorphicSections τ (n - (2 : ℤ)) (γ / (-a) ^ 2),
        ∀ z ≠ 0, f.val z = (thetaProductSection hτ hτ0 ha).val z ^ 2 * G.val z := by
      obtain ⟨G, hG⟩ := exists_holomorphic_quotient hτ0 (neg_ne_zero.mpr ha)
        f (thetaProductSection hτ hτ0 ha) 2 hzero
      refine ⟨⟨G.val, ?_⟩, hG⟩
      simpa only [Nat.cast_ofNat, mul_one] using G.property
    refine ⟨G, automorphicSections_ext _ _ ?_⟩
    intro z hz
    exact (hG z hz).symm

/-- Exact kernel dimension transfer; the lower-degree section dimension remains explicit. -/
theorem sectionEval_kernel_finrank {τ a γ : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hγ : γ ≠ 0) (n : ℤ) :
    Module.finrank ℂ (LinearMap.ker (sectionEval τ n γ a)) =
      Module.finrank ℂ (automorphicSections τ (n - 1) (γ / (-a))) := by
  rw [← pointThetaMultiply_range_eq_eval_kernel hτ hτ0 ha hγ n,
    LinearMap.finrank_range_of_inj (pointThetaMultiply_injective hτ hτ0 ha n γ 1)]
  rw [pow_one]
  rfl

theorem sectionFirstJet_kernel_finrank {τ a γ : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hγ : γ ≠ 0) (n : ℤ) :
    Module.finrank ℂ (LinearMap.ker (sectionFirstJet τ n γ ha)) =
      Module.finrank ℂ (automorphicSections τ (n - 2) (γ / (-a) ^ 2)) := by
  rw [← pointThetaMultiply_range_eq_firstJet_kernel hτ hτ0 ha hγ n,
    LinearMap.finrank_range_of_inj (pointThetaMultiply_injective hτ hτ0 ha n γ 2)]
  rfl

end Nagata.W07

end
end

section

/-! Two distinct point conditions are handled by actual theta multiplication
followed by a second genuine evaluation kernel. The first theta factor is
nonzero at the second point by its proved exact orbit zero set. -/

noncomputable section

namespace Nagata.W07

open Nagata.W08

/-- Restrict multiplication by the first theta factor to sections vanishing at the second point. -/
def twoPointThetaMultiply {τ a : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0)
    (n : ℤ) (γ b : ℂ) :
    LinearMap.ker (sectionEval τ (n - (1 : ℤ)) (γ / (-a) ^ 1) b) →ₗ[ℂ]
      automorphicSections τ n γ :=
  (pointThetaMultiply hτ hτ0 ha n γ 1).comp
    (LinearMap.ker (sectionEval τ (n - (1 : ℤ)) (γ / (-a) ^ 1) b)).subtype

theorem twoPointThetaMultiply_injective {τ a : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (n : ℤ) (γ b : ℂ) :
    Function.Injective (twoPointThetaMultiply hτ hτ0 ha n γ b) :=
  (pointThetaMultiply_injective hτ hτ0 ha n γ 1).comp Subtype.val_injective

/-- Exact range identification for two inequivalent lifts on the actual torus. -/
theorem twoPointThetaMultiply_range_eq_twoEval_kernel {τ a b γ : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hγ : γ ≠ 0) (hab : ¬ ∃ k : ℤ, b = a * τ ^ k) (n : ℤ) :
    LinearMap.range (twoPointThetaMultiply hτ hτ0 ha n γ b) =
      LinearMap.ker (sectionTwoEval τ n γ a b) := by
  have hPb : (thetaProductSection hτ hτ0 ha).val b ≠ 0 := by
    intro hz
    exact hab ((thetaProductSection_zero_iff hτ hτ0 ha hb).mp hz)
  ext f
  constructor
  · rintro ⟨G, rfl⟩
    apply (mem_sectionTwoEval_ker τ n γ a b _).mpr
    constructor
    · change (thetaProductSection hτ hτ0 ha).val a ^ 1 * G.val.val a = 0
      simp
    · have hGb : G.val.val b = 0 := G.property
      change (thetaProductSection hτ hτ0 ha).val b ^ 1 * G.val.val b = 0
      rw [hGb, mul_zero]
  · intro hf
    obtain ⟨hfa, hfb⟩ := (mem_sectionTwoEval_ker τ n γ a b f).mp hf
    have hfrange : f ∈ LinearMap.range (pointThetaMultiply hτ hτ0 ha n γ 1) := by
      rw [pointThetaMultiply_range_eq_eval_kernel hτ hτ0 ha hγ n]
      exact hfa
    obtain ⟨G, hG⟩ := hfrange
    have hGb : G.val b = 0 := by
      have he := congrArg (fun F : automorphicSections τ n γ => F.val b) hG
      change (thetaProductSection hτ hτ0 ha).val b ^ 1 * G.val b = f.val b at he
      rw [pow_one, hfb] at he
      exact (mul_eq_zero.mp he).resolve_left hPb
    exact ⟨⟨G, hGb⟩, hG⟩

/-- Exact lower-degree dimension transfer for the two-point vanishing subspace. -/
theorem sectionTwoEval_kernel_finrank {τ a b γ : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hγ : γ ≠ 0) (hab : ¬ ∃ k : ℤ, b = a * τ ^ k) (n : ℤ) :
    Module.finrank ℂ (LinearMap.ker (sectionTwoEval τ n γ a b)) =
      Module.finrank ℂ (automorphicSections τ (n - 2) ((γ / (-a)) / (-b))) := by
  rw [← twoPointThetaMultiply_range_eq_twoEval_kernel hτ hτ0 ha hb hγ hab n,
    LinearMap.finrank_range_of_inj (twoPointThetaMultiply_injective hτ hτ0 ha n γ b)]
  rw [sectionEval_kernel_finrank hτ hτ0 hb
    (div_ne_zero hγ (pow_ne_zero 1 (neg_ne_zero.mpr ha))) (n - 1)]
  rw [pow_one, show n - (1 : ℤ) - 1 = n - 2 by ring]

end Nagata.W07

end
end

end OAI
