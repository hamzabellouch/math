import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCartesianSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSymbolMembership

namespace OAI

/-! Full physical symbol bounds and homogeneous-space membership for the matched profile. -/

open Set Filter
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radial_symbol_extend_to_unit (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (k : ℕ) (σ D R : ℝ)
    (hb : ∀ y : E, R ≤ ‖y‖ → ‖iteratedFDeriv ℝ k Q y‖ ≤ D*‖y‖^σ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : E, 1 ≤ ‖y‖ →
      ‖iteratedFDeriv ℝ k Q y‖ ≤ B*‖y‖^σ := by
  let S : Set E := Metric.closedBall 0 (max 1 R) ∩ {y | 1 ≤ ‖y‖}
  have hs : IsCompact S := (isCompact_closedBall (0 : E) (max 1 R)).inter_right
    (isClosed_le continuous_const continuous_norm)
  have hnonzero (y : E) (hy : y ∈ S) : ‖y‖ ≠ 0 := by
    have h : 1 ≤ ‖y‖ := hy.2
    linarith
  have hc : ContinuousOn (fun y : E => ‖y‖^(-σ)*‖iteratedFDeriv ℝ k Q y‖) S :=
    (continuous_norm.continuousOn.rpow_const (fun y hy => Or.inl (hnonzero y hy))).mul
      ((hQ.of_le (by simp : (k : ℕ∞ω) ≤ ∞)).continuous_iteratedFDeriv'.norm.continuousOn)
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuousOn hc
  refine ⟨max (max C 0) D,(le_max_right C 0).trans (le_max_left _ _),?_⟩
  intro y hy
  have hr : 0 < ‖y‖ := by linarith
  by_cases hlarge : R ≤ ‖y‖
  · exact (hb y hlarge).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg hr.le _))
  · have hmem : y ∈ S := ⟨by
        simp only [Metric.mem_closedBall,dist_zero_right]
        exact (lt_of_not_ge hlarge).le.trans (le_max_right _ _),hy⟩
    have hbC : ‖y‖^(-σ)*‖iteratedFDeriv ℝ k Q y‖ ≤ C := by
      simpa only [Real.norm_eq_abs,abs_of_nonneg
        (mul_nonneg (Real.rpow_nonneg hr.le _) (norm_nonneg _))] using hC y hmem
    have hbC' := mul_le_mul_of_nonneg_right hbC (Real.rpow_nonneg hr.le σ)
    have hcancel : ‖y‖^(-σ)*‖y‖^σ=1 := by
      rw [← Real.rpow_add hr,neg_add_cancel,Real.rpow_zero]
    have hbC'' : ‖iteratedFDeriv ℝ k Q y‖ ≤ C*‖y‖^σ := by
      calc
        _ = (‖y‖^(-σ)*‖iteratedFDeriv ℝ k Q y‖)*‖y‖^σ := by
          rw [mul_right_comm, hcancel,one_mul]
        _ ≤ _ := hbC'
    exact hbC''.trans (mul_le_mul_of_nonneg_right
      ((le_max_left C 0).trans (le_max_left _ _)) (Real.rpow_nonneg hr.le _))

theorem radialMatchedCartesian_symbol_tail (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (k : ℕ) :
    ∃ D R : ℝ, 0 ≤ D ∧ 0 < R ∧ ∀ y : E, R ≤ ‖y‖ →
      ‖iteratedFDeriv ℝ k (radialMatchedCartesian n z) y‖ ≤
        D*‖y‖^(-2*radialShootingA n-(k : ℝ)) := by
  let ν := radialShootingNu (n+radialInnerShootingThreshold) z
  let Z := radialExteriorCanonical ν (n+radialInnerShootingThreshold)
    (radialShootingM z) (Real.log innerBoundaryRadius)
  let H := fun t : ℝ => Complex.exp (ν*(t : ℂ))*(Z t).1
  have hH : ContDiffOn ℝ ∞ H (Ioi (Real.log innerBoundaryRadius)) :=
    (radial_complexExp_contDiff ν).contDiffOn.mul
      (radialExteriorODE_position_contDiffOn ν _ Z _
        (fun t ht => ((radialExteriorCanonical_spec hX).2.2 t ht.le).2))
  obtain ⟨D,R,hD,hR,hb⟩ := radial_log_composition_symbol H
    (Real.log innerBoundaryRadius) ν.re hH
    (radialExteriorCanonical_logarithmic_symbol ν (radialShootingM z) _ _ hX
      (radialShootingM_ne_zero z)) k
  refine ⟨D,max R (innerBoundaryRadius+1),hD,lt_of_lt_of_le hR (le_max_left _ _),?_⟩
  intro y hy
  have hyr : innerBoundaryRadius < ‖y‖ :=
    lt_of_lt_of_le (by linarith : innerBoundaryRadius < innerBoundaryRadius+1)
      ((le_max_right _ _).trans hy)
  have he : radialMatchedCartesian n z =ᶠ[nhds y]
      (fun x : E => H (Real.log ‖x‖)) := by
    filter_upwards [continuous_norm.continuousAt.eventually (lt_mem_nhds hyr)] with x hx
    simp only [radialMatchedCartesian,radialMatchedProfile,ite_eq_right (not_le.mpr hx),
      radialShootingExteriorProfile,radialPhysicalExterior,H,Z,ν]
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  have hν : ν.re = -2*radialShootingA n := by
    dsimp only [ν]
    rw [radialShootingNu_physical]
    simp
  simpa only [hν] using hb y ((le_max_left _ _).trans hy)

theorem radialMatchedCartesian_symbol (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (k : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y : E, 1 ≤ ‖y‖ →
      ‖iteratedFDeriv ℝ k (radialMatchedCartesian n z) y‖ ≤
        D*‖y‖^(-2*radialShootingA n-(k : ℝ)) := by
  obtain ⟨D,R,_hD,_hR,hb⟩ := radialMatchedCartesian_symbol_tail n z hX k
  exact radial_symbol_extend_to_unit _ (radialMatchedCartesian_contDiff n z hX hz)
    k _ D R hb

theorem radialMatchedCartesian_homogeneous (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (k : ℝ)
    (ha : 0 < radialShootingA n) (ha1 : radialShootingA n < 1) (hk : 8 < k) :
    ∃ q : HomogeneousY (radialShootingA n) k, ∀ y : E,
      homogeneousPhysicalCLM (radialShootingA n) k ha ha1 hk q y = radialMatchedCartesian n z y := by
  apply exists_homogeneous_of_symbol_decay_at_infinity _ k ha ha1 hk _
    (radialMatchedCartesian_contDiff n z hX hz)
  intro j
  obtain ⟨D,_hD,hb⟩ := radialMatchedCartesian_symbol n z hX hz j
  exact ⟨D,hb⟩

end DefocusingNLS

end OAI
