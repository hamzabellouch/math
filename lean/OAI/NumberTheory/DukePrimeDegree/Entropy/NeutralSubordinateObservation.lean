import OAI.NumberTheory.DukePrimeDegree.Entropy.ControlledSubordinateObservation
import OAI.NumberTheory.DukePrimeDegree.Geometry.BilateralNeutralLifts
import OAI.NumberTheory.DukePrimeDegree.Entropy.LowEntropyRadialHeight
import OAI.NumberTheory.DukePrimeDegree.Dynamics.TriangularStabilizer
import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootGlobalCoordinates

namespace OAI

/-! # A bounded subordinate observation with neutral bilateral fibers -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_bounded_neutral_subordinate_observation (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H Q : X (d+1) → ℕ, Measurable H ∧ Measurable Q ∧
      (∀ m, IsCompact {x | H x ≤ m}) ∧
      (∀ m, (Q '' {x | H x ≤ m}).Finite) ∧
      (∀ N, observationEntropyRate μ
        (fun x => rightAction x (diagonalOneParameter ell hell (-1))) (heightClip H N) < ε) ∧
      (∀ x y, (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ g : G (d+1), rightAction x g = y ∧
          ∀ i j, ell j < ell i → g.val i j = 0) ∧
      (∀ᵐ x ∂μ, ∀ s : UpperRootTime (d+1),
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k]
            (rightAction x ((completeRootChain (d+1)).word s))) =
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        s ∈ (completeRootChain (d+1)).cube 1) ∧
      (∀ᵐ x ∂μ, ∀ᶠ s in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
        Q ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k]
          (rightAction x ((completeRootChain (d+1)).word s))) =
        Q ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k] x)) ∧
      (∀ x, H (rightAction x (diagonalOneParameter ell hell (-1))) ≤ H x+1 ∧
        H x ≤ H (rightAction x (diagonalOneParameter ell hell (-1)))+1) ∧
      (∀ x y, Q y=Q x → H y=H x) ∧
      ∀ x y,
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] y) =
          Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)) →
        ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
          ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t) := by
  let a := diagonalOneParameter ell hell (-1)
  have hT : MeasurePreserving (fun x => rightAction x a) μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    dsimp [a]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  obtain ⟨B,D,t,H,hB,hD,hH,ht,hlevel,hcompact,hstep,hnull,hbound,hent⟩ :=
    exists_low_entropy_controlled_radial_height μ a hT hε
  have hheight (x : X (d+1)) :
      quotientLogDistance (Quotient.mk _ (1 : G (d+1))) x ≤ 2*B*(H x:ℝ)+B :=
    ((hlevel x (H x)).mp le_rfl).trans (ht (H x))
  obtain ⟨rB,hrB,_,hbilateral⟩ := exists_radial_radius_bilateral_neutral_lifts
    (Nat.succ_pos d) ell hell B hB H hheight
  obtain ⟨R,hR,hunique⟩ := exists_uniform_triangular_lift_radius d
  have hcube : (completeRootChain (d+1)).cube 1 ∈
      𝓝 (completeRootChain (d+1)).zeroTime :=
    ((completeRootChain (d+1)).cube_open 1).mem_nhds
      ((completeRootChain (d+1)).zeroTime_mem_cube zero_lt_one)
  rw [(upperRootWord_isEmbedding (d+1)).isInducing.nhds_eq_comap,
    EliminationChain.word_zeroTime] at hcube
  obtain ⟨V,hV,hVcube⟩ := Filter.mem_comap.mp hcube
  obtain ⟨S,hS,hSV⟩ := matrixBall_nhds_basis hV
  obtain ⟨r₀,hr₀,hr₀1,hrcap,htri⟩ := exists_radial_radius_small_triangular_lifts
    (Nat.succ_pos d) ell hell B hB H hheight (min (min R S) rB) (lt_min (lt_min hR hS) hrB)
  obtain ⟨Q,hQ,hfinite,hsmall,hgood⟩ := exists_controlled_root_future_observation
    d ell hell hgap μ hA B hB H hH t ht hlevel (fun x => (hstep x).1)
    hnull hD hbound hr₀ hr₀1
  have hweak : ∀ x y, (∀ k : ℕ,
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
      ∃ g : G (d+1), rightAction x g = y ∧
        ∀ i j, ell j < ell i → g.val i j = 0 := by
    intro x y hxy
    obtain ⟨g,_,hg,hentries⟩ := htri Q (fun x y hxy => (hsmall x y hxy).2) x y hxy
    exact ⟨g,hg,hentries⟩
  have hneutral : ∀ x y,
      (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
      (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)) →
      ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t) := by
    apply hbilateral Q
    intro x y hxy
    obtain ⟨g,hg,hgx⟩ := (hsmall x y hxy).2
    exact ⟨g,matrixBall_mono (mul_le_mul_of_nonneg_right
      (hrcap.trans (min_le_right _ _)) (Real.exp_pos _).le) hg,hgx⟩
  refine ⟨H,Q,hH,hQ,hcompact,hfinite,hent,hweak,?_,hgood,hstep,
    (fun x y hxy => (hsmall x y hxy).1),hneutral⟩
  filter_upwards [ae_no_coordinate_zero d μ hA] with x hx s hs
  obtain ⟨g,hg,hgx,hgt⟩ := htri Q (fun x y hxy => (hsmall x y hxy).2)
    x (rightAction x ((completeRootChain (d+1)).word s)) hs
  have hrad : r₀*Real.exp (-(4*B)*(H x:ℝ)) ≤ min R S := by
    apply le_trans _ (hrcap.trans (min_le_left _ _))
    apply mul_le_of_le_one_right hr₀.le
    exact Real.exp_le_one_iff.mpr (by
      nlinarith [mul_nonneg hB.le (Nat.cast_nonneg (H x))])
  have hgR : g ∈ matrixBall (d+1) R :=
    matrixBall_mono (hrad.trans (min_le_left _ _)) hg
  have hgS : g ∈ matrixBall (d+1) S :=
    matrixBall_mono (hrad.trans (min_le_right _ _)) hg
  have hgtri : g.val.IsUpperTriangular := by
    intro i j hji
    apply hgt i j
    have hh := hgap ⟨(j,i), Finset.mem_filter.mpr ⟨Finset.mem_univ _,hji⟩⟩
    have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
    dsimp at hh
    linarith
  have hu := upperRootWord_mem (d+1) s
  have hutri : ((completeRootChain (d+1)).word s).val.IsUpperTriangular := by
    intro i j hji
    have hp := positiveRootGeneratedGroup_pattern (allPositiveRoots (d+1))
      (allPositiveRoots_closed (d+1)) hu i j (by
        simpa [allPositiveRoots] using not_lt_of_ge hji.le)
    change ((completeRootChain (d+1)).word s).val i j =
      (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) i j at hp
    exact hp.trans (Matrix.one_apply_ne (show i ≠ j from ne_of_gt hji))
  have hueq := hunique x hx ((completeRootChain (d+1)).word s) g hutri
    (upperRoot_diagonal hu) hgR hgtri hgx.symm
  exact hVcube (by change (completeRootChain (d+1)).word s ∈ V; rw [hueq]; exact hSV hgS)

end DukePrimeDegree

end

end OAI
