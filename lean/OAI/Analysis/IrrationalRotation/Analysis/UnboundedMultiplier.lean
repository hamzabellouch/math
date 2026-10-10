import OAI.Analysis.IrrationalRotation.Model.UnboundedMultiplier
import OAI.Analysis.IrrationalRotation.Rotation.WeightedShiftPowers
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

namespace OAI

noncomputable section
open Filter Topology
open scoped ENNReal
namespace Invariant233.WeightedShift

@[simp] theorem multiplier_apply (h : ℤ → ℂ) (ξ : multiplierDomain h) (k : ℤ) :
    multiplier h ξ k = h k * ξ.val k := rfl

theorem multiplier_injective {h : ℤ → ℂ} (hh : ∀ k, h k ≠ 0) :
    Function.Injective (multiplier h) := by
  intro ξ η heq
  apply Subtype.ext
  ext k
  exact mul_left_cancel₀ (hh k) (congrArg (fun v : Hilbert => v k) heq)

theorem operator_mem_multiplierDomain (h : ℤ → ℂ) (f g : Weight) (c : ℂ)
    (hfg : ∀ k : ℤ, h (k + 1) * f k = c * g k * h k)
    (ξ : multiplierDomain h) :
    operator f ξ.val ∈ multiplierDomain h := by
  change Memℓp (fun k => h k * (operator f ξ.val) k) 2
  have heq : (fun k => h k * (operator f ξ.val) k) =
      fun k => (c • operator g (multiplier h ξ)) k := by
    funext k
    have hk := hfg (k - 1)
    simp only [sub_add_cancel] at hk
    change h k * (f (k - 1) * ξ.val (k - 1)) =
      c * (g (k - 1) * (h (k - 1) * ξ.val (k - 1)))
    rw [← mul_assoc, hk]
    ring
  rw [heq]
  exact lp.memℓp (c • operator g (multiplier h ξ))

theorem multiplier_intertwines (h : ℤ → ℂ) (f g : Weight) (c : ℂ)
    (hfg : ∀ k : ℤ, h (k + 1) * f k = c * g k * h k)
    (ξ : multiplierDomain h) :
    multiplier h ⟨operator f ξ.val, operator_mem_multiplierDomain h f g c hfg ξ⟩ =
      c • operator g (multiplier h ξ) := by
  ext k
  have hk := hfg (k - 1)
  simp only [sub_add_cancel] at hk
  change h k * (f (k - 1) * ξ.val (k - 1)) =
    c * (g (k - 1) * (h (k - 1) * ξ.val (k - 1)))
  rw [← mul_assoc, hk]
  ring

theorem exp_coboundary_intertwining {b g gstar : ℤ → ℝ} {d : ℝ}
    (hcost : ∀ k, g k = gstar k + d + b (k + 1) - b k) (k : ℤ) :
    Real.exp (b (k + 1)) * Real.exp (-g k) =
      Real.exp (-d) * Real.exp (-gstar k) * Real.exp (b k) := by
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [hcost k]
  ring

theorem single_mem_multiplierDomain (h : ℤ → ℂ) (k : ℤ) (z : ℂ) :
    lp.single (E := fun _ : ℤ => ℂ) 2 k z ∈ multiplierDomain h := by
  change Memℓp (fun j => h j * lp.single (E := fun _ : ℤ => ℂ) 2 k z j) 2
  convert lp.memℓp (lp.single (E := fun _ : ℤ => ℂ) 2 k (h k * z)) using 1
  funext j
  by_cases hj : j = k
  · subst j; simp
  · simp [lp.single_apply, Pi.single_eq_of_ne hj]

theorem dense_multiplierDomain (h : ℤ → ℂ) :
    Dense (multiplierDomain h : Set Hilbert) := by
  intro ξ
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num) ξ)
  exact Filter.Eventually.of_forall fun s => subset_closure
    ((multiplierDomain h).sum_mem fun k _ => single_mem_multiplierDomain h k (ξ k))

theorem unboundedMultiplier_single (h : ℤ → ℂ) (k : ℤ) (z : ℂ) :
    unboundedMultiplier h ⟨lp.single (E := fun _ : ℤ => ℂ) 2 k z, single_mem_multiplierDomain h k z⟩ =
      lp.single (E := fun _ : ℤ => ℂ) 2 k (h k * z) := by
  ext j
  change h j * lp.single (E := fun _ : ℤ => ℂ) 2 k z j = lp.single (E := fun _ : ℤ => ℂ) 2 k (h k * z) j
  by_cases hj : j = k
  · subst j; simp
  · simp [lp.single_apply, Pi.single_eq_of_ne hj]

theorem unboundedMultiplier_formalAdjoint (h : ℤ → ℂ) :
    (unboundedMultiplier h).IsFormalAdjoint (unboundedMultiplier (fun k => star (h k))) := by
  intro ξ η
  change inner ℂ (multiplier h ξ) η.val =
    inner ℂ ξ.val (multiplier (fun k => star (h k)) η)
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  simp only [RCLike.inner_apply', starRingEnd_apply]
  change star (h k * ξ.val k) * η.val k = star (ξ.val k) * (star (h k) * η.val k)
  rw [star_mul]
  ring

theorem adjoint_unboundedMultiplier_apply (h : ℤ → ℂ)
    (ξ : (unboundedMultiplier h).adjoint.domain) (k : ℤ) :
    (unboundedMultiplier h).adjoint ξ k = star (h k) * ξ.val k := by
  have hformal := (LinearPMap.adjoint_isFormalAdjoint (T := unboundedMultiplier h) (dense_multiplierDomain h)).symm
  have heq := hformal
    ⟨lp.single (E := fun _ : ℤ => ℂ) 2 k 1, single_mem_multiplierDomain h k 1⟩ ξ
  rw [unboundedMultiplier_single, lp.inner_single_left, lp.inner_single_left] at heq
  simpa only [mul_one, RCLike.inner_apply', map_one, one_mul, starRingEnd_apply] using heq.symm

theorem adjoint_unboundedMultiplier (h : ℤ → ℂ) :
    (unboundedMultiplier h).adjoint = unboundedMultiplier (fun k => star (h k)) := by
  apply le_antisymm
  · constructor
    · intro ξ hξ
      change Memℓp (fun k => star (h k) * ξ k) 2
      have heq : (fun k => star (h k) * ξ k) =
          fun k => (unboundedMultiplier h).adjoint ⟨ξ, hξ⟩ k := by
        funext k
        exact (adjoint_unboundedMultiplier_apply h ⟨ξ, hξ⟩ k).symm
      rw [heq]
      exact lp.memℓp ((unboundedMultiplier h).adjoint ⟨ξ, hξ⟩)
    · intro ξ η hξη
      ext k
      rw [adjoint_unboundedMultiplier_apply]
      change star (h k) * ξ.val k = star (h k) * η.val k
      rw [hξη]
  · exact LinearPMap.IsFormalAdjoint.le_adjoint (dense_multiplierDomain h)
      (unboundedMultiplier_formalAdjoint h)

theorem isSelfAdjoint_unboundedMultiplier_real (h : ℤ → ℝ) :
    IsSelfAdjoint (unboundedMultiplier (fun k => (h k : ℂ))) := by
  rw [LinearPMap.isSelfAdjoint_def, adjoint_unboundedMultiplier]
  congr 1
  funext k
  simp

theorem isClosed_unboundedMultiplier_real (h : ℤ → ℝ) :
    (unboundedMultiplier (fun k => (h k : ℂ))).IsClosed :=
  (isSelfAdjoint_unboundedMultiplier_real h).isClosed

theorem unboundedMultiplier_nonnegative (h : ℤ → ℝ) (hh : ∀ k, 0 ≤ h k)
    (ξ : multiplierDomain (fun k => (h k : ℂ))) :
    0 ≤ (inner ℂ ξ.val (multiplier (fun k => (h k : ℂ)) ξ)).re := by
  rw [lp.inner_eq_tsum, Complex.re_tsum (lp.summable_inner _ _)]
  apply tsum_nonneg
  intro k
  change 0 ≤ (inner ℂ (ξ.val k) ((h k : ℂ) • ξ.val k)).re
  rw [inner_smul_right]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (hh k) (inner_self_nonneg (𝕜 := ℂ) (x := ξ.val k))

theorem exponential_multiplier_injective (b : ℤ → ℝ) :
    Function.Injective (multiplier (fun k => (Real.exp (b k) : ℂ))) := by
  apply multiplier_injective
  intro k
  exact_mod_cast Real.exp_ne_zero (b k)

theorem multiplier_mem_inverseDomain (h : ℤ → ℂ) (hh : ∀ k, h k ≠ 0)
    (ξ : multiplierDomain h) :
    multiplier h ξ ∈ multiplierDomain (fun k => (h k)⁻¹) := by
  change Memℓp (fun k => (h k)⁻¹ * (h k * ξ.val k)) 2
  simpa only [← mul_assoc, inv_mul_cancel₀ (hh _), one_mul] using lp.memℓp ξ.val

theorem inverse_multiplier_mul (h : ℤ → ℂ) (hh : ∀ k, h k ≠ 0)
    (ξ : multiplierDomain h) :
    multiplier (fun k => (h k)⁻¹)
      ⟨multiplier h ξ, multiplier_mem_inverseDomain h hh ξ⟩ = ξ.val := by
  ext k
  change (h k)⁻¹ * (h k * ξ.val k) = ξ.val k
  rw [← mul_assoc, inv_mul_cancel₀ (hh k), one_mul]

theorem inverseMultiplier_mem_domain (h : ℤ → ℂ) (hh : ∀ k, h k ≠ 0)
    (ξ : multiplierDomain (fun k => (h k)⁻¹)) :
    multiplier (fun k => (h k)⁻¹) ξ ∈ multiplierDomain h := by
  change Memℓp (fun k => h k * ((h k)⁻¹ * ξ.val k)) 2
  simpa only [← mul_assoc, mul_inv_cancel₀ (hh _), one_mul] using lp.memℓp ξ.val

theorem multiplier_mul_inverse (h : ℤ → ℂ) (hh : ∀ k, h k ≠ 0)
    (ξ : multiplierDomain (fun k => (h k)⁻¹)) :
    multiplier h
      ⟨multiplier (fun k => (h k)⁻¹) ξ, inverseMultiplier_mem_domain h hh ξ⟩ = ξ.val := by
  ext k
  change h k * ((h k)⁻¹ * ξ.val k) = ξ.val k
  rw [← mul_assoc, mul_inv_cancel₀ (hh k), one_mul]

theorem multiplier_range (h : ℤ → ℂ) (hh : ∀ k, h k ≠ 0) :
    LinearMap.range (multiplier h) = multiplierDomain (fun k => (h k)⁻¹) := by
  ext ξ
  constructor
  · rintro ⟨η, rfl⟩
    exact multiplier_mem_inverseDomain h hh η
  · intro hξ
    exact ⟨⟨multiplier (fun k => (h k)⁻¹) ⟨ξ, hξ⟩,
      inverseMultiplier_mem_domain h hh ⟨ξ, hξ⟩⟩,
      multiplier_mul_inverse h hh ⟨ξ, hξ⟩⟩

theorem multiplier_denseRange (h : ℤ → ℂ) (hh : ∀ k, h k ≠ 0) :
    DenseRange (multiplier h) := by
  change Dense (LinearMap.range (multiplier h) : Set Hilbert)
  rw [multiplier_range h hh]
  exact dense_multiplierDomain _

theorem unboundedMultiplier_real_formalAdjoint (h : ℤ → ℝ) :
    (unboundedMultiplier (fun k => (h k : ℂ))).IsFormalAdjoint
      (unboundedMultiplier (fun k => (h k : ℂ))) := by
  simpa using unboundedMultiplier_formalAdjoint (fun k => (h k : ℂ))

theorem inverse_multiplier_inner (h : ℤ → ℝ) (hh : ∀ k, h k ≠ 0)
    (η : multiplierDomain (fun k => (h k : ℂ)⁻¹))
    (ζ : multiplierDomain (fun k => (h k : ℂ))) :
    inner ℂ (multiplier (fun k => (h k : ℂ)⁻¹) η)
      (multiplier (fun k => (h k : ℂ)) ζ) = inner ℂ η.val ζ.val := by
  have hh' : ∀ k, (h k : ℂ) ≠ 0 := fun k => Complex.ofReal_ne_zero.mpr (hh k)
  have heq := unboundedMultiplier_real_formalAdjoint h
    ⟨multiplier (fun k => (h k : ℂ)⁻¹) η,
      inverseMultiplier_mem_domain (fun k => (h k : ℂ)) hh' η⟩ ζ
  change inner ℂ
    (multiplier (fun k => (h k : ℂ))
      ⟨multiplier (fun k => (h k : ℂ)⁻¹) η,
        inverseMultiplier_mem_domain (fun k => (h k : ℂ)) hh' η⟩)
    ζ.val = _ at heq
  rw [multiplier_mul_inverse _ hh'] at heq
  exact heq.symm

@[simp] theorem exponentialWeight_apply (g : ℤ → ℝ) (hg : ∀ k, 0 ≤ g k) (k : ℤ) :
    exponentialWeight g hg k = (Real.exp (-g k) : ℂ) := rfl

theorem operator_exponentialWeight_ne_zero (g : ℤ → ℝ) (hg : ∀ k, 0 ≤ g k) :
    operator (exponentialWeight g hg) ≠ 0 := by
  intro hzero
  have hw := (operator_eq_zero_iff (exponentialWeight g hg)).mp hzero
  have h := congrArg (fun w : Weight => w 0) hw
  simp only [exponentialWeight_apply, lp.coeFn_zero, Pi.zero_apply,
    Complex.ofReal_eq_zero, Real.exp_ne_zero] at h

theorem exponentialWeight_coboundary (b g gstar : ℤ → ℝ) (d : ℝ)
    (hg : ∀ k, 0 ≤ g k) (hgs : ∀ k, 0 ≤ gstar k)
    (hcost : ∀ k, g k = gstar k + d + b (k + 1) - b k) (k : ℤ) :
    (Real.exp (b (k + 1)) : ℂ) * exponentialWeight g hg k =
      (Real.exp (-d) : ℂ) * exponentialWeight gstar hgs k * (Real.exp (b k) : ℂ) := by
  simp only [exponentialWeight_apply]
  exact_mod_cast exp_coboundary_intertwining hcost k

theorem exponential_coboundary_domain (b g gstar : ℤ → ℝ) (d : ℝ)
    (hg : ∀ k, 0 ≤ g k) (hgs : ∀ k, 0 ≤ gstar k)
    (hcost : ∀ k, g k = gstar k + d + b (k + 1) - b k)
    (ξ : multiplierDomain (fun k => (Real.exp (b k) : ℂ))) :
    operator (exponentialWeight g hg) ξ.val ∈
      multiplierDomain (fun k => (Real.exp (b k) : ℂ)) :=
  operator_mem_multiplierDomain _ _ _ _
    (exponentialWeight_coboundary b g gstar d hg hgs hcost) ξ

theorem exponential_coboundary_intertwines (b g gstar : ℤ → ℝ) (d : ℝ)
    (hg : ∀ k, 0 ≤ g k) (hgs : ∀ k, 0 ≤ gstar k)
    (hcost : ∀ k, g k = gstar k + d + b (k + 1) - b k)
    (ξ : multiplierDomain (fun k => (Real.exp (b k) : ℂ))) :
    multiplier (fun k => (Real.exp (b k) : ℂ))
      ⟨operator (exponentialWeight g hg) ξ.val,
        exponential_coboundary_domain b g gstar d hg hgs hcost ξ⟩ =
      (Real.exp (-d) : ℂ) • operator (exponentialWeight gstar hgs)
        (multiplier (fun k => (Real.exp (b k) : ℂ)) ξ) :=
  multiplier_intertwines _ _ _ _
    (exponentialWeight_coboundary b g gstar d hg hgs hcost) ξ

end Invariant233.WeightedShift

end

end OAI
