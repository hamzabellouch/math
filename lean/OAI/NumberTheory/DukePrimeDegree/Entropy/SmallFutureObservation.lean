import OAI.NumberTheory.DukePrimeDegree.Entropy.BranchingSubordinateObservation
import OAI.NumberTheory.DukePrimeDegree.Geometry.RadialLocalInjectivity

namespace OAI

/-! # A finite-branching future observation with an exported injective lift radius -/

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_small_future_observation (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ) :
    ∃ (H Q : X (d+1) → ℕ) (r : ℕ → ℝ),
      Measurable H ∧ Measurable Q ∧ Antitone r ∧
      (∀ m, 0 < r m ∧ r m ≤ 1) ∧
      (∀ x, LocalInjectivityAt (r (H x)) x) ∧
      UniformFinitePredecessors
        (fun x => rightAction x (diagonalOneParameter ell hell (-1))) Q ∧
      (∀ x y, (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ g ∈ matrixBall (d+1) (r (H x)), rightAction x g=y ∧
          ∀ i j, ell j < ell i → g.val i j=0) ∧
      (∀ x y,
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] y) =
          Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)) →
        ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
          ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t)) := by
  let a := diagonalOneParameter ell hell (-1)
  have hT : MeasurePreserving (fun x => rightAction x a) μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    dsimp only [a]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  obtain ⟨B,D,t,H,hB,hD,hH,ht,hlevel,_,hstep,hnull,hbound,_⟩ :=
    exists_low_entropy_controlled_radial_height μ a hT (by norm_num : (0:ℝ)<1)
  have hheight (x : X (d+1)) :
      quotientLogDistance (Quotient.mk _ (1 : G (d+1))) x ≤ 2*B*(H x:ℝ)+B :=
    ((hlevel x (H x)).mp le_rfl).trans (ht (H x))
  obtain ⟨rB,hrB,_,hbilateral⟩ := exists_radial_radius_bilateral_neutral_lifts
    (Nat.succ_pos d) ell hell B hB H hheight
  let Kp := predecessorPackingRadius (d+1) a (16*Real.exp (4*B)) 16
  have hKp : 0 < Kp := by dsimp only [Kp,predecessorPackingRadius]; positivity
  have hpackRadius : 0 < 4/((d+1:ℝ)*Kp) := by positivity
  obtain ⟨r₀,hr₀,hr₀1,hrcap,hinj,htri⟩ := exists_radial_radius_injective_triangular_lifts
    (Nat.succ_pos d) ell hell B hB H hheight
    (min rB (4/((d+1:ℝ)*Kp))) (lt_min hrB hpackRadius)
  have hpack : (d+1:ℝ)*Kp*r₀ ≤ 4 := by
    have hh := hrcap.trans (min_le_right _ _)
    have hnK : 0 < (d+1:ℝ)*Kp := by positivity
    have h := (le_div_iff₀ hnK).mp hh
    nlinarith
  obtain ⟨Q,hQ,_,hsmall,_,hbranch,_⟩ := exists_branching_cover_future_observation
    d ell hell hgap μ hA B hB H hH t ht hlevel hstep hnull hD hbound hr₀ hr₀1
    (by simpa only [Kp,a,Nat.cast_add,Nat.cast_one] using hpack)
  let r := fun m : ℕ => r₀*Real.exp (-(4*B)*(m:ℝ))
  have hr (m : ℕ) : 0 < r m ∧ r m ≤ 1 := by
    refine ⟨mul_pos hr₀ (Real.exp_pos _),?_⟩
    have he : Real.exp (-(4*B)*(m:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      nlinarith [mul_nonneg hB.le (Nat.cast_nonneg m)])
    exact (mul_le_of_le_one_right hr₀.le he).trans hr₀1
  refine ⟨H,Q,r,hH,hQ,?_,hr,hinj,hbranch,?_,?_⟩
  · intro i j hij
    apply mul_le_mul_of_nonneg_left _ hr₀.le
    apply Real.exp_le_exp.mpr
    have hcast : (i:ℝ) ≤ j := Nat.cast_le.mpr hij
    exact mul_le_mul_of_nonpos_left hcast (by linarith)
  · exact htri Q (fun x y hxy => (hsmall x y hxy).2)
  · apply hbilateral Q
    intro x y hxy
    obtain ⟨g,hg,hgx⟩ := (hsmall x y hxy).2
    exact ⟨g,matrixBall_mono (mul_le_mul_of_nonneg_right
      (hrcap.trans (min_le_left _ _)) (Real.exp_pos _).le) hg,hgx⟩

end DukePrimeDegree

end

end OAI
