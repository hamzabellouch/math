import OAI.MeasureTheory.Falconer.Estimates.RegularClassSmallTrouble
import OAI.MeasureTheory.Falconer.Radial.DyadicRadialPruning
import OAI.MeasureTheory.Falconer.Radial.RadialFreezingScales
import OAI.MeasureTheory.Falconer.Radial.RadialProfileProduct

namespace OAI

/-! # The single-scale radial gain for an actual regularization class -/

namespace Falconer.Regularization
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

theorem single_class_radial_gain (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    (Q : DyadicCube (n+1)) (hQ : Q.side = 1)
    (J : ℕ) (hJ : 0 < J) (L : ℕ)
    {e f τ η lam u v c Cp Bs Bp C : ℝ}
    (hη : 0 ≤ η) (hCp : 0 ≤ Cp) (hBs : 0 ≤ Bs) (hBp : 0 ≤ Bp)
    (hτ : 2*(((n+1:ℕ):ℝ)+1)*lam < τ)
    (hcount : 0 < (n+1)*e-n*τ-η*n*(n+1)^2-n*u)
    (hu : c*((n+1:ℕ):ℝ) < u) (hv : c*((n+1:ℕ):ℝ) < v)
    (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ))
    (hC : Real.sqrt (n+1:ℕ)+2*(Bs+Bp) ≤ C)
    (P : Set (Space (n+1))) (hP : MeasurableSet P)
    (hPb : ∀ x ∈ P, ‖x‖ ≤ Bp) (hQb : ∀ z ∈ Q.carrier, ‖z‖ ≤ Bs) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ ν : Measure (Space (n+1))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ν Pᶜ = 0 → ∀ B : ℕ, 0 < B →
      (B:ℝ) ≤ lam*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam →
      ∀ p₀ ∈ regularizationLeaves Q μ N, ∀ loss ℓ : ℝ,
      (n:ℝ)-loss ≤ sourceProfile Q μ N B p₀ N →
      (J:ℝ)*(e+f)-((n:ℝ)/(n+1))*((n:ℝ)-loss-
        ((n+1:ℕ):ℝ)*(2/((J:ℝ)+2)+(J:ℝ)/(N:ℝ))) ≤ -ℓ →
      ∀ K : ℝ≥0∞,
      (∀ x : Space (n+1), ν (ball x (8*((n+1:ℕ):ℝ)/(2:ℝ)^(radialBlockSize N J))) ≤ K) →
      (∀ w : Space (n+1), ‖w‖ = 1 → ∀ a : ℝ,
        ν {x | |inner ℝ w x-a| ≤ (Bs+Bp)*((2:ℝ)^N)^(-η)} ≤
          ENNReal.ofReal (Cp*((2:ℝ)^N)^(-v))) →
      ∃ G : Set (Space (n+1) × Space (n+1)), MeasurableSet G ∧
        (ν.prod (sourceClass Q μ N B p₀)) Gᶜ ≤
          (J:ℝ≥0∞)*(K+ENNReal.ofReal (((2:ℝ)^N)^(-c)))+
            (J+1:ℝ≥0∞)*ENNReal.ofReal (((2:ℝ)^N)^(-f)) ∧
        ∀ x w : Space (n+1), sourceClass Q μ N B p₀
          {z | (x,z) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ ((2:ℝ)^N)⁻¹} ≤
            ENNReal.ofReal (((2:ℝ)^N)^(-ℓ)) := by
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  obtain ⟨N₁,hsmall⟩ := regular_class_small_troublesome hLW hn L hη hCp hτ hcount hu hv
  refine ⟨max 1 N₁,?_⟩
  intro N hN μ ν _ _ hPfull B hB hwidth hlarge p₀ hp₀ loss ℓ hfinal hgap K hball hslab
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num : 0 < 1) ((le_max_left _ _).trans hN)
  have hNN : N₁ ≤ N := (le_max_right _ _).trans hN
  let ρ := sourceClass Q μ N B p₀
  have : IsProbabilityMeasure ρ := regularization_class_probability Q hside μ N B hp₀
  let R : ℝ := (2:ℝ)^N
  let depth := radialBlockDepth N J
  let r : ℝ := 8*((n+1:ℕ):ℝ)/(2:ℝ)^(radialBlockSize N J)
  let F := fun j => R^e/(R^(sourceProfile Q μ N B p₀ (depth (j+1))-
    sourceProfile Q μ N B p₀ (depth j)))^((n:ℝ)/(n+1))
  have hgeom (j : ℕ) :
      Real.sqrt (n+1:ℕ)*(Q.side/(2:ℝ)^depth j) < r ∧
      8*(Real.sqrt (n+1:ℕ)*(Q.side/(2:ℝ)^depth j))^2/r ≤ Q.side/(2:ℝ)^depth (j+1) := by
    have hh := dyadic_reserved_block_freezing (by omega : 0 < n+1)
      (by norm_num : (0:ℝ) < 1) (radialBlockDepth_two_blocks N J j)
    simpa only [hQ,one_mul,mul_one,depth,r,radialBlockDepth_step] using hh
  have hwidth' (j : ℕ) (hj : j < J) :
      Real.sqrt (n+1:ℕ)*(Q.side/(2:ℝ)^depth (j+1))+2*(Bs+Bp)*R⁻¹ ≤
        C*(Q.side/(2:ℝ)^depth (j+1)) := by
    have hs : R⁻¹ ≤ Q.side/(2:ℝ)^depth (j+1) := by
      rw [hQ,one_div]
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num)
        (radialBlockDepth_le N J (by omega)))
    calc
      _ ≤ Real.sqrt (n+1:ℕ)*(Q.side/(2:ℝ)^depth (j+1))+
          2*(Bs+Bp)*(Q.side/(2:ℝ)^depth (j+1)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (by positivity))
      _ = (Real.sqrt (n+1:ℕ)+2*(Bs+Bp))*(Q.side/(2:ℝ)^depth (j+1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC (by positivity)
  have htrouble : ∀ j < J, ∀ p ∈ Q.occupiedPaths ρ (depth j),
      ((ProbabilityTheory.cond ρ (Q.descendant p).carrier).prod ν)
        (troublesomePair (ProbabilityTheory.cond ρ (Q.descendant p).carrier)
          (Q.descendant p).center r (Real.sqrt (n+1:ℕ)*(Q.side/(2:ℝ)^depth j)) Bs
          (C*(Q.side/(2:ℝ)^depth (j+1))) (ENNReal.ofReal (F j))) ≤ ENNReal.ofReal (R^(-c)) := by
    intro j hj p hp
    have hR : ∀ᵐ x ∂ν, ‖(Q.descendant p).center-x‖ ≤ Bs+Bp := by
      have hpae : ∀ᵐ x ∂ν, x ∈ P := ae_iff.mpr hPfull
      filter_upwards [hpae] with x hx
      exact (norm_sub_le _ _).trans (add_le_add
        (hQb _ (Q.descendant_subset p ((Q.descendant p).center_mem (Q.descendant_side_pos hside p))))
        (hPb x hx))
    have hr : 0 < r := by dsimp [r]; positivity
    exact hsmall N hNN Q hside μ ν B hB hwidth hlarge p₀ hp₀ (depth j) (depth (j+1))
      (radialBlockDepth_le N J hj.le) (radialBlockDepth_le N J (by omega)) p
      ((mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hp).1) (Finset.mem_filter.mp hp).2
      r C Bs (Bs+Bp) hr hL (hgeom j).2 hR (fun w hw => hslab w hw _)
  obtain ⟨G,hG,hcost,hcap⟩ := dyadic_radial_pruning ρ ν Q hside
    (sourceClass_root_null Q hside μ N B p₀) N J hJ depth
    (fun j hj => radialBlockDepth_le N J hj)
    (fun j _ => radialBlockDepth_mono N J (Nat.le_succ j)) (fun _ => r)
    (fun j => C*(Q.side/(2:ℝ)^depth (j+1))) Bs Bp R⁻¹
    (fun j => ENNReal.ofReal (F j)) (fun _ => K) (fun _ => ENNReal.ofReal (R^(-c)))
    P hP hPfull hPb hQb (fun j _ => (hgeom j).1) hwidth'
    (fun _ _ _ _ => hball _) htrouble (ENNReal.ofReal (R^(-f)))
    (by dsimp [R]; positivity) ENNReal.ofReal_ne_top
  refine ⟨G,hG,?_,?_⟩
  · simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,R] using hcost
  · intro x w
    apply (hcap x w).trans
    have hR : 0 < R := by dsimp [R]; positivity
    simp only [F,profile_fraction_eq hR]
    apply radial_profile_product_bound Q μ hNpos hB p₀ J (by positivity) hfinal
    simpa only [add_comm e f] using hgap

end Falconer.Regularization

end OAI
