import Mathlib
import OAI.Analysis.BoxTransport.Motion
import OAI.Analysis.BoxTransport.Expressions

namespace OAI

/-! Effective realization of every balanced finite box instruction. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

open scoped BigOperators ContDiff
namespace BoxTransport.Routing.Computation

@[fun_prop] theorem representable_stageSwitch (j : Fin 5) :
    Representable (fun p : SpaceTime => stageSwitch j p.1) := by
  unfold stageSwitch
  fun_prop

@[fun_prop] theorem representable_routeCenters {n : ℕ} (a b : Fin n → RationalSpace) (D : ℚ)
    (i : Fin n) (j : Fin 3) :
    Representable (fun p : SpaceTime => routeCenters a b (D : ℝ) i p.1 j) := by
  fin_cases j <;> dsimp [routeCenters, routeCenterParameters] <;> fun_prop

@[fun_prop] theorem representable_linearBlend {n : ℕ} (h k : Fin n → RationalSpace)
    (i : Fin n) (j : Fin 3) : Representable (fun p : SpaceTime =>
      1 - stageSwitch 2 p.1 + stageSwitch 2 p.1 * scaleRatio h k i j) := by
  unfold scaleRatio
  fun_prop

@[fun_prop] theorem representable_routeScales {n : ℕ} {h k : Fin n → RationalSpace}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j) (i : Fin n) (j : Fin 3) :
    Representable (fun p : SpaceTime => routeScales h k i p.1 j) := by
  fin_cases j
  · exact representable_linearBlend h k i 0
  · exact representable_linearBlend h k i 1
  · change Representable (fun p : SpaceTime =>
      ((1 - stageSwitch 2 p.1 + stageSwitch 2 p.1 * scaleRatio h k i 0) *
        (1 - stageSwitch 2 p.1 + stageSwitch 2 p.1 * scaleRatio h k i 1))⁻¹)
    apply ((representable_linearBlend h k i 0).mul (representable_linearBlend h k i 1)).inv
    refine ⟨min 1 (scaleRatio h k i 0) * min 1 (scaleRatio h k i 1),
      mul_pos (lt_min zero_lt_one (scaleRatio_pos hh hk i 0))
        (lt_min zero_lt_one (scaleRatio_pos hh hk i 1)), fun p => ?_⟩
    have hp (j : Fin 3) := linearBlend_pos (scaleRatio_pos hh hk i j) (stageSwitch_mem 2 p.1)
    rw [abs_of_pos (mul_pos (hp 0) (hp 1))]
    exact mul_le_mul (linearBlend_between (stageSwitch_mem 2 p.1)).1
      (linearBlend_between (stageSwitch_mem 2 p.1)).1
      (le_of_lt (lt_min zero_lt_one (scaleRatio_pos hh hk i 1))) (hp 0).le

theorem routeScales_separated_from_zero {n : ℕ} {h k : Fin n → RationalSpace}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j) (i : Fin n) (j : Fin 3) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p : SpaceTime, ε ≤ |routeScales h k i p.1 j| := by
  have hs := scaleRatio_pos hh hk i
  fin_cases j <;> simp only [Fin.reduceFinMk]
  · refine ⟨min 1 (scaleRatio h k i 0), lt_min zero_lt_one (hs 0), fun p => ?_⟩
    rw [abs_of_pos (routeScales_pos hh hk i p.1 0)]
    exact (linearBlend_between (stageSwitch_mem 2 p.1)).1
  · refine ⟨min 1 (scaleRatio h k i 1), lt_min zero_lt_one (hs 1), fun p => ?_⟩
    rw [abs_of_pos (routeScales_pos hh hk i p.1 1)]
    exact (linearBlend_between (stageSwitch_mem 2 p.1)).1
  · refine ⟨(max 1 (scaleRatio h k i 0) * max 1 (scaleRatio h k i 1))⁻¹,
      inv_pos.mpr (mul_pos (lt_max_of_lt_left zero_lt_one) (lt_max_of_lt_left zero_lt_one)), fun p => ?_⟩
    rw [abs_of_pos (routeScales_pos hh hk i p.1 2)]
    change _ ≤ ((1 - stageSwitch 2 p.1 + stageSwitch 2 p.1 * scaleRatio h k i 0) *
      (1 - stageSwitch 2 p.1 + stageSwitch 2 p.1 * scaleRatio h k i 1))⁻¹
    have hp (j : Fin 3) := linearBlend_pos (hs j) (stageSwitch_mem 2 p.1)
    apply inv_anti₀ (mul_pos (hp 0) (hp 1))
    exact mul_le_mul (linearBlend_between (stageSwitch_mem 2 p.1)).2
      (linearBlend_between (stageSwitch_mem 2 p.1)).2 (hp 1).le
      (le_of_lt (lt_max_of_lt_left zero_lt_one))

theorem time_partial_curve {c : ℝ → Space} (hc : ContDiff ℝ ∞ c) (p : SpaceTime) (j : Fin 3) :
    fderiv ℝ (fun p : SpaceTime => c p.1 j) p (coordinateDirection none) = deriv c p.1 j := by
  have hs : ContDiff ℝ ∞ (fun p : SpaceTime => c p.1) := hc.comp contDiff_fst
  rw [fderiv_apply (hs.differentiable (by simp) p)]
  have hd := ((hc.differentiable (by simp) p.1).hasFDerivAt.comp p hasFDerivAt_fst).fderiv
  change fderiv ℝ (fun p : SpaceTime => c p.1) p = _ at hd
  rw [hd]
  rfl

@[fun_prop] theorem representable_curve_deriv {c : ℝ → Space} (hc : ContDiff ℝ ∞ c)
    (hrep : ∀ j, Representable (fun p : SpaceTime => c p.1 j)) (j : Fin 3) :
    Representable (fun p : SpaceTime => deriv c p.1 j) := by
  have h := (hrep j).directional none
  simpa only [time_partial_curve hc] using h

@[fun_prop] theorem representable_diagonalLogVelocity {n : ℕ} {h k : Fin n → RationalSpace}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j) (i : Fin n) (j : Fin 3) :
    Representable (fun p : SpaceTime => diagonalLogVelocity (routeScales h k i) p.1 j) := by
  exact (representable_curve_deriv (contDiff_routeScales hh hk i) (representable_routeScales hh hk i) j).div
    (representable_routeScales hh hk i j) (routeScales_separated_from_zero hh hk i j)

@[fun_prop] theorem representable_movingAffinePotential {c v l : ℝ → Space}
    (hc : ∀ j, Representable (fun p : SpaceTime => c p.1 j))
    (hv : ∀ j, Representable (fun p : SpaceTime => v p.1 j))
    (hl : ∀ j, Representable (fun p : SpaceTime => l p.1 j)) (j : Fin 3) :
    Representable (fun p => movingAffinePotential c v l p j) := by
  have hr (j : Fin 3) := (Representable.space j).sub (hc j)
  have hcomp (i j : Fin 3) : Representable
      (fun p : SpaceTime => potentialComponent (c p.1) (v p.1) (l p.1) i j p) := by
    exact ((Representable.one.div_nat 2).mul (((hv i).mul (hr j)).sub ((hv j).mul (hr i)))).add
      (((Representable.one.div_nat 3).mul ((hl i).sub (hl j))).mul ((hr i).mul (hr j)))
  fin_cases j
  · exact hcomp 1 2
  · exact hcomp 2 0
  · exact hcomp 0 1

@[fun_prop] theorem representable_movingBoxCutoff {c r : ℝ → Space}
    (hc : ∀ j, Representable (fun p : SpaceTime => c p.1 j))
    (hr : ∀ j, Representable (fun p : SpaceTime => r p.1 j)) (η : ℚ) :
    Representable (movingBoxCutoff c r η) := by
  unfold movingBoxCutoff
  apply Representable.prod
  intro j _
  have hrj := (hr j).add ((Representable.ofNat 2).mul (Representable.rational η))
  have hxj := (Representable.space j).sub (hc j)
  exact ((hrj.add hxj).div_rat η).transition.mul ((hrj.sub hxj).div_rat η).transition

@[fun_prop] theorem representable_familyPotential {n : ℕ} {c v l r : Fin n → ℝ → Space}
    (hc : ∀ i j, Representable (fun p : SpaceTime => c i p.1 j))
    (hv : ∀ i j, Representable (fun p : SpaceTime => v i p.1 j))
    (hl : ∀ i j, Representable (fun p : SpaceTime => l i p.1 j))
    (hr : ∀ i j, Representable (fun p : SpaceTime => r i p.1 j)) (η : ℚ) (j : Fin 3) :
    Representable (fun p => familyPotential c v l r η p j) := by
  simp only [familyPotential, Finset.sum_apply]
  apply Representable.sum
  intro i _
  change Representable (fun p => movingBoxCutoff (c i) (r i) η p * movingAffinePotential (c i) (v i) (l i) p j)
  exact (representable_movingBoxCutoff (hc i) (hr i) η).mul
    (representable_movingAffinePotential (hc i) (hv i) (hl i) j)

@[fun_prop] theorem representable_spatialCurl {A : Field}
    (hrep : ∀ j, Representable (fun p => A p j)) (j : Fin 3) :
    Representable (fun p => spatialCurl A p j) := by
  have hA : ContDiff ℝ ∞ A := contDiff_pi.mpr (fun j => (hrep j).smooth)
  have hd (d : Axis) (k : Fin 3) : Representable (fun p => fderiv ℝ A p (coordinateDirection d) k) := by
    have hh := (hrep k).directional d
    simpa only [fderiv_apply (hA.differentiable (by simp) _), ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply] using hh
  fin_cases j <;> simp only [spatialCurl, curlLinear_apply]
  · exact (hd (some 1) 2).sub (hd (some 2) 1)
  · exact (hd (some 2) 0).sub (hd (some 0) 2)
  · exact (hd (some 0) 1).sub (hd (some 1) 0)

theorem representable_routedField {n : ℕ} (a b h k : Fin n → RationalSpace)
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j) (η : ℚ) (j : Fin 3) :
    Representable (fun p => routedField a b h k η p j) := by
  have hc (i : Fin n) (j : Fin 3) : Representable (fun p : SpaceTime =>
      routeCenters a b (30 * (boxDataBound h k : ℝ)) i p.1 j) := by
    simpa only [Rat.cast_mul, Rat.cast_ofNat] using representable_routeCenters a b (30 * boxDataBound h k) i j
  apply representable_spatialCurl
  apply representable_familyPotential
  · exact hc
  · intro i j
    exact representable_curve_deriv (contDiff_routeCenters a b _ i) (hc i) j
  · exact representable_diagonalLogVelocity hh hk
  · intro i j
    exact (representable_routeScales hh hk i j).mul (Representable.rational (h i j))

theorem effective_routedField {n : ℕ} (a b h k : Fin n → RationalSpace)
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j) (η : ℚ)
    (hs : ContDiff ℝ ∞ (routedField a b h k η)) (hc : HasCompactSupport (routedField a b h k η)) :
    Effective (routedField a b h k η) := by
  choose es he hv using representable_routedField a b h k hh hk η
  exact effective_of_expressions hs hc es he (fun p j => congrFun (hv j) p)

end BoxTransport.Routing.Computation

namespace BoxTransport.Routing

theorem balanced_box_routing
    (n : ℕ) (a b h k : Fin n → RationalSpace)
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (ha : Pairwise fun i j => Disjoint (solidBox (a i) (h i)) (solidBox (a j) (h j)))
    (hb : Pairwise fun i j => Disjoint (solidBox (b i) (k i)) (solidBox (b j) (k j)))
    (hvol : ∀ i, ∏ j : Fin 3, k i j / h i j = 1) :
    ∃ U : Field, ∃ Φ : ℝ → Space → Space,
      AdmissibleField U ∧ IsGlobalFlow U Φ ∧ Delivers a b h k Φ := by
  obtain ⟨η, _, hs, hc, hdiv, ht, Φ, hΦ, hdel⟩ := exists_routedField_realization n a b h k hh hk ha hb hvol
  exact ⟨routedField a b h k η, Φ, ⟨hs, hc, Computation.effective_routedField a b h k hh hk η hs hc,
    hdiv, ht⟩, hΦ, hdel⟩

end BoxTransport.Routing

end

end OAI
