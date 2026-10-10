import OAI.MeasureTheory.Falconer.Radial.DyadicRadialPruning
import OAI.MeasureTheory.Falconer.Incidence.RegularClassRadialIncidence

namespace OAI

/-! # Constructing a pruned pair relation for one original regularization class -/

namespace Falconer.Regularization
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

theorem regular_class_radial_pruning (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    (Q : DyadicCube (n+1)) (hQ : 0 < Q.side)
    (μ ν : Measure (Space (n+1))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) {lam : ℝ}
    (hwidth : (B:ℝ) ≤ lam*(N:ℝ)) (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath (n+1)} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    (J : ℕ) (hJ : 0 < J) (depth : ℕ → ℕ)
    (hdepth : ∀ j ≤ J, depth j ≤ N) (hmono : ∀ j < J, depth j ≤ depth (j+1))
    (r : ℕ → ℝ) (Bs Bp C capRadius : ℝ) (F α u : ℕ → ℝ)
    (K S t : ℕ → ℝ≥0∞) (L : ℕ) (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ))
    (P : Set (Space (n+1))) (hP : MeasurableSet P) (hPfull : ν Pᶜ = 0)
    (hPb : ∀ x ∈ P, ‖x‖ ≤ Bp) (hQb : ∀ z ∈ Q.carrier, ‖z‖ ≤ Bs)
    (hfar : ∀ j < J, Real.sqrt (n+1:ℕ)*(Q.side/(2:ℝ)^depth j) < r j)
    (hfreeze : ∀ j < J,
      8*(Real.sqrt (n+1:ℕ)*(Q.side/(2:ℝ)^depth j))^2/r j ≤ Q.side/(2:ℝ)^depth (j+1))
    (hcap : ∀ j < J,
      Real.sqrt (n+1:ℕ)*(Q.side/(2:ℝ)^depth (j+1))+2*(Bs+Bp)*capRadius ≤
        C*(Q.side/(2:ℝ)^depth (j+1)))
    (hF : ∀ j < J, 0 < F j) (hα : ∀ j < J, 0 < α j ∧ α j ≤ 1)
    (hu : ∀ j < J, 0 ≤ u j)
    (hball : ∀ j < J, ∀ p ∈ Q.occupiedPaths (sourceClass Q μ N B p₀) (depth j),
      ν (ball (Q.descendant p).center (r j)) ≤ K j)
    (hslab : ∀ j < J, ∀ p ∈ Q.occupiedPaths (sourceClass Q μ N B p₀) (depth j),
      ∀ v : Space (n+1), ‖v‖ = 1 →
        ν {x | |inner ℝ v x-inner ℝ v (Q.descendant p).center| ≤ (Bs+Bp)*α j} ≤ S j)
    (hbudget : ∀ j < J,
      (((2*L+1)^(n+1):ℕ)/F j)^(n+1)*
        (generalTubeCountConstant (n+1) ((n+1:ℕ):ℝ)/(α j)^(n+1))^(n*(n+1))*
          (radialClassBallBound Q μ N B p₀ (depth j) (depth (j+1)) lam)^n ≤ (u j)^n)
    (hdelete : ∀ j < J, ENNReal.ofReal (u j)+(n+1:ℝ≥0∞)*S j ≤ (t j)^(n+1))
    (θ : ℝ≥0∞) (hθ : 0 < θ) (hθtop : θ ≠ ∞) :
    ∃ G : Set (Space (n+1) × Space (n+1)), MeasurableSet G ∧
      (ν.prod (sourceClass Q μ N B p₀)) Gᶜ ≤
        (∑ j ∈ Finset.range J, (K j+t j))+(J+1:ℝ≥0∞)*θ ∧
      ∀ x v : Space (n+1),
        sourceClass Q μ N B p₀ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-v‖ ≤ capRadius} ≤
          ∏ j ∈ Finset.range J, θ⁻¹*ENNReal.ofReal (F j) := by
  let ρ := sourceClass Q μ N B p₀
  have : IsProbabilityMeasure ρ := regularization_class_probability Q hQ μ N B hp₀
  apply dyadic_radial_pruning ρ ν Q hQ (sourceClass_root_null Q hQ μ N B p₀)
    N J hJ depth hdepth hmono r (fun j => C*(Q.side/(2:ℝ)^depth (j+1)))
    Bs Bp capRadius (fun j => ENNReal.ofReal (F j)) K t P hP hPfull hPb hQb
    hfar hcap hball _ θ hθ hθtop
  intro j hj p hp
  have hlen := (mem_cubePaths (n+1) (depth j) p).mp (Finset.mem_filter.mp hp).1
  have hpos := (Finset.mem_filter.mp hp).2
  have hR : ∀ᵐ x ∂ν, ‖(Q.descendant p).center-x‖ ≤ Bs+Bp := by
    have hpae : ∀ᵐ x ∂ν, x ∈ P := ae_iff.mpr hPfull
    filter_upwards [hpae] with x hx
    exact (norm_sub_le _ _).trans (add_le_add
      (hQb _ (Q.descendant_subset p ((Q.descendant p).center_mem (Q.descendant_side_pos hQ p))))
      (hPb x hx))
  have hr : 0 < r j := lt_of_le_of_lt (by positivity) (hfar j hj)
  have hh := regular_class_radial_incidence hLW hn Q hQ μ ν hN hB hwidth hlarge hp₀ (Bs := Bs)
    (hdepth j hj.le) (hdepth (j+1) (by omega)) hlen hpos hr (hF j hj)
    (hα j hj).1 (hα j hj).2 (hfreeze j hj) hR (S j) (hslab j hj p hp)
    L hL (hu j hj) (hbudget j hj)
  exact (ENNReal.pow_le_pow_left_iff (by omega : n+1 ≠ 0)).mp
    (hh.trans (hdelete j hj))

end Falconer.Regularization

end OAI
