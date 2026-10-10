import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ThirdOrderPerturbation

namespace OAI

/-! Third-order comparison of actual finite-dimensional ground energies. -/

noncomputable section
namespace ContinuumCoulomb.Perturbation
open scoped InnerProductSpace
variable {L H : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem thirdOrderForm_smul (C : L →L[ℝ] L) (T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) (r : ℝ) (p : L) :
    thirdOrderForm C T D B (r • p) = r^2*thirdOrderForm C T D B p := by
  simp only [thirdOrderForm,effectiveForm_smul,map_smul,
    real_inner_smul_left,real_inner_smul_right]
  ring

def thirdOrderBottom (C : L →L[ℝ] L) (T D : H →L[ℝ] H) (B : L →L[ℝ] H) : ℝ :=
  sInf {e | ∃ p : L, ‖p‖ = 1 ∧ e = thirdOrderForm C T D B p}

theorem thirdOrderForm_minimizer [FiniteDimensional ℝ L]
    (C : L →L[ℝ] L) (T D : H →L[ℝ] H) (B : L →L[ℝ] H)
    (u : L) (hu : ‖u‖ = 1) :
    ∃ p : L, ‖p‖ = 1 ∧ ∀ x : L,
      thirdOrderForm C T D B p*‖x‖^2 ≤ thirdOrderForm C T D B x := by
  have := FiniteDimensional.proper_rclike ℝ L
  have hTB : Continuous (fun p => T (B p)) := T.continuous.comp B.continuous
  have hc : Continuous (thirdOrderForm C T D B) :=
    ((continuous_id.inner C.continuous).sub
      (B.continuous.inner hTB)).add (hTB.inner (D.continuous.comp hTB))
  have hn : (Metric.sphere (0 : L) 1).Nonempty := ⟨u,by simpa using hu⟩
  obtain ⟨p,hp,hmin⟩ := (isCompact_sphere (0 : L) 1).exists_isMinOn hn hc.continuousOn
  refine ⟨p,by simpa using hp,?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx,thirdOrderForm,effectiveForm,inverseForm]
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hunit : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := norm_smul_inv_norm hx
  have h := hmin (show (‖x‖⁻¹ : ℝ) • x ∈ Metric.sphere (0 : L) 1 by simpa using hunit)
  change thirdOrderForm C T D B p ≤ thirdOrderForm C T D B ((‖x‖⁻¹ : ℝ) • x) at h
  rw [thirdOrderForm_smul] at h
  calc
    _ ≤ (‖x‖⁻¹^2*thirdOrderForm C T D B x)*‖x‖^2 :=
      mul_le_mul_of_nonneg_right h (sq_nonneg _)
    _ = _ := by field_simp

theorem thirdOrderBottom_eq (C : L →L[ℝ] L) (T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) (p : L) (hp : ‖p‖ = 1)
    (hmin : ∀ x, thirdOrderForm C T D B p*‖x‖^2 ≤ thirdOrderForm C T D B x) :
    thirdOrderBottom C T D B = thirdOrderForm C T D B p := by
  have hl (e : ℝ) (he : ∃ x : L, ‖x‖ = 1 ∧ e = thirdOrderForm C T D B x) :
      thirdOrderForm C T D B p ≤ e := by
    obtain ⟨x,hx,rfl⟩ := he
    simpa only [hx,one_pow,mul_one] using hmin x
  exact le_antisymm (csInf_le ⟨_,hl⟩ ⟨p,hp,rfl⟩) (le_csInf ⟨_,p,hp,rfl⟩ hl)

theorem thirdOrder_bottom_error (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) {g d m η μ : ℝ} (hg : 0 < g)
    (hd : 0 ≤ d) (hm : 0 ≤ m) (hsmall : 2*d+4*m ≤ g)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x,A y⟫_ℝ = ⟪A x,y⟫_ℝ)
    (hDsymm : ∀ x y, ⟪x,D y⟫_ℝ = ⟪D x,y⟫_ℝ)
    (hgap : ∀ q, g*‖q‖^2 ≤ penaltyForm A q)
    (hTB : ∀ p, ‖T (B p)‖ ≤ η*‖p‖) (hD : ‖D‖ ≤ d)
    (hμ : |μ| ≤ m) (hmin : ∀ p, μ*‖p‖^2 ≤ thirdOrderForm C T D B p)
    (p₀ : L) (hp₀ : ‖p₀‖ = 1) (he : thirdOrderForm C T D B p₀ = μ) :
    |lowBlockBottom C A D B-μ| ≤ (2*d^2/g+2*m)*η^2 := by
  have hμb := abs_le.mp hμ
  have hnon : 0 < ‖p₀‖^2+‖-(T (B p₀))‖^2 := by rw [hp₀]; positivity
  have hn : {e | ∃ (p : L) (q : H), 0 < ‖p‖^2+‖q‖^2 ∧
      e = lowBlockRayleigh C A D B p q}.Nonempty := ⟨_,p₀,-(T (B p₀)),hnon,rfl⟩
  have hl (e : ℝ) (he : ∃ (p : L) (q : H), 0 < ‖p‖^2+‖q‖^2 ∧
      e = lowBlockRayleigh C A D B p q) : μ-(2*d^2/g+2*m)*η^2 ≤ e := by
    obtain ⟨p,q,hpq,rfl⟩ := he
    exact thirdOrder_rayleigh_lower C A T D B hg hd hm hsmall hAT hAsymm
      hDsymm hgap hTB hD hμb.2 hmin p q hpq
  have hb : BddBelow {e | ∃ (p : L) (q : H), 0 < ‖p‖^2+‖q‖^2 ∧
      e = lowBlockRayleigh C A D B p q} := ⟨_,hl⟩
  have hlow : μ-(2*d^2/g+2*m)*η^2 ≤ lowBlockBottom C A D B := le_csInf hn hl
  have hu : lowBlockBottom C A D B ≤ μ+m*η^2 :=
    (csInf_le hb ⟨p₀,-(T (B p₀)),hnon,rfl⟩).trans
      (thirdOrder_trial_upper C A T D B hm hAT hTB hμb.1 p₀ hp₀ he)
  have herr : m*η^2 ≤ (2*d^2/g+2*m)*η^2 := by
    have hz : 0 ≤ 2*d^2/g := by positivity
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg η)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem finite_thirdOrder_bottom_error [FiniteDimensional ℝ L]
    (C : L →L[ℝ] L) (A T D : H →L[ℝ] H) (B : L →L[ℝ] H)
    {g d m η : ℝ} (hg : 0 < g) (hd : 0 ≤ d) (hm : 0 ≤ m) (hsmall : 2*d+4*m ≤ g)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x,A y⟫_ℝ = ⟪A x,y⟫_ℝ)
    (hDsymm : ∀ x y, ⟪x,D y⟫_ℝ = ⟪D x,y⟫_ℝ)
    (hgap : ∀ q, g*‖q‖^2 ≤ penaltyForm A q)
    (hTB : ∀ p, ‖T (B p)‖ ≤ η*‖p‖) (hD : ‖D‖ ≤ d)
    (hbound : ∀ p, ‖p‖ = 1 → |thirdOrderForm C T D B p| ≤ m)
    (u : L) (hu : ‖u‖ = 1) :
    |lowBlockBottom C A D B-thirdOrderBottom C T D B| ≤ (2*d^2/g+2*m)*η^2 := by
  obtain ⟨p,hp,hmin⟩ := thirdOrderForm_minimizer C T D B u hu
  rw [thirdOrderBottom_eq C T D B p hp hmin]
  exact thirdOrder_bottom_error C A T D B hg hd hm hsmall hAT hAsymm hDsymm hgap
    hTB hD (hbound p hp) hmin p hp rfl

end ContinuumCoulomb.Perturbation

end

end OAI
