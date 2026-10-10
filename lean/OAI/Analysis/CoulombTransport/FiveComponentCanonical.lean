import OAI.Analysis.CoulombTransport.FiveComponentGeometry
import OAI.Analysis.CoulombTransport.GoodTypePermutation

namespace OAI

noncomputable section
open Set Filter Metric
open scoped ENNReal

namespace Problem356.FiveComponentGeometry

open CenterCertificate GoodTypePermutation

/-- Common component neighborhoods on which both canonical Coulomb
certificates hold, including their one-way symmetric contact localization. -/
theorem exists_canonical_neighborhoods
    (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    ∃ W : Fin 5 → Set E3,
      (∀ i, W i ∈ nhds (point i)) ∧
      LocalTypeCertificate W (potentials C₁ C₂) (branchContact C₁ C₂) 0 1 2 ∧
      LocalTypeCertificate W (potentials C₁ C₂) (branchContact C₁ C₂) 0 3 4 := by
  let R : Fin 5 → ℝ :=
    ![min C₁.stateRadius C₂.stateRadius, C₁.parameterRadius, C₁.stateRadius,
      C₂.parameterRadius, C₂.stateRadius]
  have hR : ∀ i, 0 < R i := by
    intro i
    fin_cases i
    · exact lt_min C₁.stateRadius_pos C₂.stateRadius_pos
    · exact C₁.parameterRadius_pos
    · exact C₁.stateRadius_pos
    · exact C₂.parameterRadius_pos
    · exact C₂.stateRadius_pos
  obtain ⟨r, hr, hsub, hdisj⟩ := Geometry.finite_disjoint_closedBalls_subset
    point point_injective (fun i => ball (point i) (R i))
    (fun _ => isOpen_ball) (fun i => mem_ball_self (hR i))
  let W : Fin 5 → Set E3 := fun i => ball (point i) r
  have hWsub (i : Fin 5) : W i ⊆ ball (point i) (R i) :=
    ball_subset_closedBall.trans (hsub i)
  have hdist {i j : Fin 5} (hij : i ≠ j) {x y : E3}
      (hx : x ∈ W i) (hy : y ∈ W j) : 0 < dist x y := by
    apply dist_pos.mpr
    intro heq
    exact Set.disjoint_left.mp (hdisj hij)
      (heq ▸ ball_subset_closedBall hx) (ball_subset_closedBall hy)
  refine ⟨W, (fun i => ball_mem_nhds (point i) hr), ?_, ?_⟩
  · intro x hx y hy z hz
    have hx' := hWsub 0 hx
    change x ∈ ball (0 : E3) (min C₁.stateRadius C₂.stateRadius) at hx'
    have hx₁ : x ∈ ball (0 : E3) C₁.stateRadius :=
      ball_subset_ball (min_le_left _ _) hx'
    have hy₁ : y ∈ ball (point 1) C₁.parameterRadius := hWsub 1 hy
    have hz₁ : z ∈ ball (-point 1) C₁.stateRadius := by
      have hz' := hWsub 2 hz
      change z ∈ ball (point 2) C₁.stateRadius at hz'
      simpa only [point_two_eq_neg] using hz'
    have hc := ennreal_local_certificate C₁ hy₁ hx₁ hz₁
      (hdist (by decide : (0 : Fin 5) ≠ 1) hx hy)
      (hdist (by decide : (0 : Fin 5) ≠ 2) hx hz)
      (hdist (by decide : (1 : Fin 5) ≠ 2) hy hz)
    refine ⟨hc.1, ?_⟩
    intro heq
    obtain ⟨hxc, hzc⟩ := hc.2.mp heq
    apply Or.inl
    refine ⟨y, ?_, ?_⟩
    · rw [C₁.source_ball]
      exact hy₁
    · simpa only [hxc, hzc] using
        (List.Perm.refl [C₁.charts.central y, y, C₁.charts.opposite y])
  · intro x hx y hy z hz
    have hx' := hWsub 0 hx
    change x ∈ ball (0 : E3) (min C₁.stateRadius C₂.stateRadius) at hx'
    have hx₂ : x ∈ ball (0 : E3) C₂.stateRadius :=
      ball_subset_ball (min_le_right _ _) hx'
    have hy₂ : y ∈ ball (point 3) C₂.parameterRadius := hWsub 3 hy
    have hz₂ : z ∈ ball (-point 3) C₂.stateRadius := by
      have hz' := hWsub 4 hz
      change z ∈ ball (point 4) C₂.stateRadius at hz'
      simpa only [point_four_eq_neg] using hz'
    have hc := ennreal_local_certificate C₂ hy₂ hx₂ hz₂
      (hdist (by decide : (0 : Fin 5) ≠ 3) hx hy)
      (hdist (by decide : (0 : Fin 5) ≠ 4) hx hz)
      (hdist (by decide : (3 : Fin 5) ≠ 4) hy hz)
    refine ⟨hc.1, ?_⟩
    intro heq
    obtain ⟨hxc, hzc⟩ := hc.2.mp heq
    apply Or.inr
    refine ⟨y, ?_, ?_⟩
    · rw [C₂.source_ball]
      exact hy₂
    · simpa only [hxc, hzc] using
        (List.Perm.refl [C₂.charts.central y, y, C₂.charts.opposite y])

/-- The actual chart pair supplies the neighborhood hypothesis for every
good component type in the finite global gluing theorem. -/
theorem eventually_good_certificate
    (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3))
    (i j k : Fin 5) (hg : Good i j k) :
    ∀ᶠ t : Triple in nhds (point i, (point j, point k)),
      ENNReal.ofReal (potentials C₁ C₂ i t.1 + potentials C₁ C₂ j t.2.1 +
        potentials C₁ C₂ k t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (potentials C₁ C₂ i t.1 + potentials C₁ C₂ j t.2.1 +
        potentials C₁ C₂ k t.2.2) = coulombCost t → branchContact C₁ C₂ t) := by
  obtain ⟨W, hW, h012, h034⟩ := exists_canonical_neighborhoods C₁ C₂
  exact GoodTypePermutation.eventually_certificate_of_good point hW
    (fun hp => (branchContact_perm C₁ C₂ hp).mp) h012 h034 i j k hg

end Problem356.FiveComponentGeometry

end

end OAI
