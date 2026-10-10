import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTruncatedNonlinearity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialShootingBarrier
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMinimumPrinciple
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! Positive scalar inner profiles obtained by radial shooting and the minimum principle. -/

open Set
namespace DefocusingNLS

theorem exists_radial_scalar_dirichlet_regular (p : ℕ) (R lo hi C : ℝ) (hR : 0 < R)
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ 1) (hC : 0 ≤ C)
    (V : ℝ → ℝ) (hV : Continuous V) (hVC : ∀ r ∈ Icc 0 R, ‖V r‖ ≤ C)
    (hLower : ∀ r ∈ Icc 0 R, lo^p ≤ V r*lo)
    (hUpper : ∀ r ∈ Icc 0 R, V r*hi ≤ hi^p) :
    ∃ A : ℝ → ℝ, Differentiable ℝ A ∧
      (∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv A) r) ∧
      A R=lo ∧ HasDerivAt A 0 0 ∧
      (∀ r ∈ Icc 0 R, A r ∈ Icc lo hi) ∧
      (∀ r ∈ Ioo 0 R,
        -deriv (deriv A) r-11/r*deriv A r+(A r)^p=V r*A r) := by
  let N := radialTruncatedNonlinearity p lo hi V
  let L : ℝ := (p : ℝ)+C
  let M : ℝ := 1+C
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hN : Continuous (Function.uncurry N) :=
    continuous_radialTruncatedNonlinearity p lo hi V hV
  have hBound : ∀ t ∈ Icc 0 R, ∀ x : ℝ, ‖N t x‖ ≤ M := by
    intro t ht x
    exact radialTruncatedNonlinearity_bound p lo hi C hlo hlohi hhi hC V t (hVC t ht) x
  have hLip : ∀ t ∈ Icc 0 R, ∀ x y : ℝ, ‖N t x-N t y‖ ≤ L*‖x-y‖ := by
    intro t ht x y
    exact radialTruncatedNonlinearity_lipschitz p lo hi C hlo hlohi hhi hC V t (hVC t ht) x y
  have hNeg : ∀ t ∈ Icc 0 R, ∀ x ≤ lo, N t x ≤ 0 := by
    intro t ht x hx
    have hc : radialAmplitudeClamp lo hi x=lo :=
      max_eq_left ((min_le_right hi x).trans hx)
    change (radialAmplitudeClamp lo hi x)^p-V t*radialAmplitudeClamp lo hi x ≤ 0
    rw [hc]
    linarith [hLower t ht]
  have hPos : ∀ t ∈ Icc 0 R, ∀ x, hi ≤ x → 0 ≤ N t x := by
    intro t ht x hx
    have hc : radialAmplitudeClamp lo hi x=hi := by
      simp only [radialAmplitudeClamp,min_eq_left hx,max_eq_right hlohi]
    change 0 ≤ (radialAmplitudeClamp lo hi x)^p-V t*radialAmplitudeClamp lo hi x
    rw [hc]
    linarith [hUpper t ht]
  let F := fun a => radialShootingAmplitude R L M hR.le hL hM N hN hBound hLip a R
  have hFc : Continuous F :=
    continuous_radialShootingAmplitude_endpoint R L M hR.le hL hM N hN hBound hLip
  have hFl : F lo ≤ lo :=
    radialShooting_lower_start R L M hR.le hL hM N hN hBound hLip lo hNeg R ⟨hR.le,le_rfl⟩
  have hFu : lo ≤ F hi := hlohi.trans
    (radialShooting_upper_start R L M hR.le hL hM N hN hBound hLip hi hPos R ⟨hR.le,le_rfl⟩)
  obtain ⟨a,ha,hend⟩ := intermediate_value_Icc hlohi hFc.continuousOn ⟨hFl,hFu⟩
  let A := radialShootingAmplitude R L M hR.le hL hM N hN hBound hLip a
  have hAd : Differentiable ℝ A :=
    differentiable_radialShootingAmplitude R L M hR.le hL hM N hN hBound hLip a
  obtain ⟨_,_,hzero,_,hEq⟩ :=
    radialShootingAmplitude_equation R L M hR.le hL hM N hN hBound hLip a
  have hAR : A R=lo := hend
  have hLow : ∀ r ∈ Icc 0 R, lo ≤ A r :=
    radial_minimum_principle R lo hR A hAd hzero.deriv (hAR.ge) (by
      intro r hr hlt
      rw [hEq r hr]
      exact hNeg r ⟨hr.1.le,hr.2.le⟩ _ hlt.le)
  have hHigh : ∀ r ∈ Icc 0 R, A r ≤ hi := by
    have hD : Differentiable ℝ (fun r => -A r) := hAd.neg
    have hd : deriv (fun r => -A r)=fun r => -deriv A r := by
      ext r
      exact deriv.neg
    have hzeroA : deriv A 0=0 := hzero.deriv
    have hz : deriv (fun r => -A r) 0=0 := by
      rw [hd]
      change -deriv A 0=0
      rw [hzeroA,neg_zero]
    have hB : -hi ≤ -A R := neg_le_neg (hAR.le.trans hlohi)
    have hm := radial_minimum_principle R (-hi) hR (fun r => -A r) hD hz hB (by
      intro r hr hlt
      rw [hd]
      have hdd : deriv (fun t => -deriv A t) r= -deriv (deriv A) r := deriv.neg
      rw [hdd]
      dsimp only
      have h := hPos r ⟨hr.1.le,hr.2.le⟩ (A r) (by linarith)
      rw [← hEq r hr] at h
      linarith)
    intro r hr
    linarith [hm r hr]
  refine ⟨A,hAd,?_,hAR,hzero,fun r hr => ⟨hLow r hr,hHigh r hr⟩,?_⟩
  · intro r hr
    exact differentiableAt_deriv_radialShootingAmplitude R L M hR.le hL hM N hN hBound hLip a r hr.1.ne'
  · intro r hr
    have h := hEq r hr
    change deriv (deriv A) r+11/r*deriv A r=
      (radialAmplitudeClamp lo hi (A r))^p-V r*radialAmplitudeClamp lo hi (A r) at h
    rw [radialAmplitudeClamp_eq lo hi (A r) ⟨hLow r ⟨hr.1.le,hr.2.le⟩,
      hHigh r ⟨hr.1.le,hr.2.le⟩⟩] at h
    linarith

theorem exists_radial_scalar_dirichlet (p : ℕ) (R lo hi C : ℝ) (hR : 0 < R)
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ 1) (hC : 0 ≤ C)
    (V : ℝ → ℝ) (hV : Continuous V) (hVC : ∀ r ∈ Icc 0 R, ‖V r‖ ≤ C)
    (hLower : ∀ r ∈ Icc 0 R, lo^p ≤ V r*lo)
    (hUpper : ∀ r ∈ Icc 0 R, V r*hi ≤ hi^p) :
    ∃ A : ℝ → ℝ, Differentiable ℝ A ∧ A R=lo ∧ HasDerivAt A 0 0 ∧
      (∀ r ∈ Icc 0 R, A r ∈ Icc lo hi) ∧
      (∀ r ∈ Ioo 0 R,
        -deriv (deriv A) r-11/r*deriv A r+(A r)^p=V r*A r) := by
  obtain ⟨A,hA,_,hR,h0,hI,hEq⟩ := exists_radial_scalar_dirichlet_regular
    p R lo hi C hR hlo hlohi hhi hC V hV hVC hLower hUpper
  exact ⟨A,hA,hR,h0,hI,hEq⟩

end DefocusingNLS

end OAI
