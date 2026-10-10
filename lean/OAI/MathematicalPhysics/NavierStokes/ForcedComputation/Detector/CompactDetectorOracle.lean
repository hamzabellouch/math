import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CompactDetectorExpressions

namespace OAI

/-! Certified calls to the input-field oracle at clocked points.  The
adaptive searches below stop because the input's rational enclosures
converge.  No evaluator for the output force is assumed. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Filter
open scoped ContDiff Topology BigOperators

namespace PlanarJetOracle

variable {F : PlanarComponents} (o : PlanarJetOracle F)

def modulus (α : List (Fin 4)) (j : Fin 2) : ℚ :=
  ∑ k : Fin 4, o.bound (k :: α) j

theorem modulus_nonneg (α : List (Fin 4)) (j : Fin 2) : 0 ≤ o.modulus α j :=
  Finset.sum_nonneg (fun _ _ => o.bound_nonneg _ _)

theorem fderiv_bound (α : List (Fin 4)) (j : Fin 2) (y : SpaceTime) :
    ‖fderiv ℝ (componentJet F α j) y‖ ≤ (o.modulus α j : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Rat.cast_nonneg.mpr (o.modulus_nonneg α j))
  intro v
  conv_lhs => rw [← spaceTimeDirections_sum v]
  rw [map_sum]
  calc
    _ ≤ ∑ k : Fin 4, ‖fderiv ℝ (componentJet F α j) y
        (timeSpaceCoord k v • spaceTimeDirection k)‖ := norm_sum_le _ _
    _ ≤ ∑ k : Fin 4, ‖v‖ * (o.bound (k :: α) j : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      rw [map_smul, norm_smul]
      have hk : ‖fderiv ℝ (componentJet F α j) y (spaceTimeDirection k)‖ ≤
          (o.bound (k :: α) j : ℝ) := o.jet_bound (k :: α) j y
      exact mul_le_mul (timeSpaceCoord_norm k v) hk (norm_nonneg _) (norm_nonneg _)
    _ = _ := by
      rw [modulus, Rat.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem lipschitz (hF : ∀ j, ContDiff ℝ ∞ (F j)) (α : List (Fin 4))
    (j : Fin 2) (x y : SpaceTime) :
    |componentJet F α j x - componentJet F α j y| ≤
      (o.modulus α j : ℝ) * ‖x - y‖ := by
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ (Set.univ : Set SpaceTime)) =>
      (componentJet_smooth hF α j).differentiable (by simp) z)
    (fun z _ => o.fderiv_bound α j z) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using h

def Ready (α : List (Fin 4)) (j : Fin 2) (q : RationalSpaceTime) (ε : ℚ) (n : ℕ) : Prop :=
  (o.enclose α j q n).radius ≤ ε

instance readyDecidable (α : List (Fin 4)) (j : Fin 2) (q : RationalSpaceTime)
    (ε : ℚ) (n : ℕ) : Decidable (o.Ready α j q ε n) :=
  inferInstanceAs (Decidable ((o.enclose α j q n).radius ≤ ε))

theorem ready_exists (α : List (Fin 4)) (j : Fin 2) (q : RationalSpaceTime)
    {ε : ℚ} (hε : 0 < ε) : ∃ n, o.Ready α j q ε n := by
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨n, hn⟩ := ((o.enclose_converges α j q).2.eventually_lt_const hε').exists
  exact ⟨n, by exact_mod_cast hn.le⟩

def evaluate (α : List (Fin 4)) (j : Fin 2) (q : RationalSpaceTime)
    (ε : ℚ) (hε : 0 < ε) : ℚ :=
  (o.enclose α j q (Nat.find (o.ready_exists α j q hε))).center

theorem evaluate_spec (α : List (Fin 4)) (j : Fin 2) (q : RationalSpaceTime)
    (ε : ℚ) (hε : 0 < ε) :
    |componentJet F α j (rationalPoint q) - (o.evaluate α j q ε hε : ℝ)| ≤ (ε : ℝ) := by
  exact (o.enclose_contains α j q (Nat.find (o.ready_exists α j q hε))).trans
    (by exact_mod_cast Nat.find_spec (o.ready_exists α j q hε))

def clockBall (p : ProfileExpr) (α : List (Fin 4)) (j : Fin 2)
    (y : RationalSpaceTime) (n : ℕ) : QBall :=
  let b := p.enclose y.1 n
  ⟨o.evaluate α j (b.center, y.2) (ClockedExpr.dyadic n) (ClockedExpr.dyadic_pos n),
    ClockedExpr.dyadic n + o.modulus α j * b.radius⟩

theorem clockBall_contains (hF : ∀ j, ContDiff ℝ ∞ (F j))
    (p : ProfileExpr) (α : List (Fin 4)) (j : Fin 2) (y : RationalSpaceTime) (n : ℕ) :
    (o.clockBall p α j y n).Contains (componentJet F α j (clockedPoint p (rationalPoint y))) := by
  let b := p.enclose y.1 n
  let z : RationalSpaceTime := (b.center, y.2)
  have hd : ‖clockedPoint p (rationalPoint y) - rationalPoint z‖ ≤ (b.radius : ℝ) := by
    apply norm_prod_le_iff.mpr
    constructor
    · exact p.enclose_contains y.1 n
    · change ‖(fun k => (y.2 k : ℝ)) - (fun k => (y.2 k : ℝ))‖ ≤ (b.radius : ℝ)
      rw [sub_self, norm_zero]
      exact_mod_cast QBall.radius_nonneg (p.enclose_contains y.1 n)
  have h₁ := (o.lipschitz hF α j (clockedPoint p (rationalPoint y)) (rationalPoint z)).trans
    (mul_le_mul_of_nonneg_left hd (Rat.cast_nonneg.mpr (o.modulus_nonneg α j)))
  have h₂ := o.evaluate_spec α j z (ClockedExpr.dyadic n) (ClockedExpr.dyadic_pos n)
  change |componentJet F α j (clockedPoint p (rationalPoint y)) -
    (o.evaluate α j z (ClockedExpr.dyadic n) (ClockedExpr.dyadic_pos n) : ℝ)| ≤ _
  calc
    _ ≤ |componentJet F α j (clockedPoint p (rationalPoint y)) - componentJet F α j (rationalPoint z)| +
        |componentJet F α j (rationalPoint z) -
          (o.evaluate α j z (ClockedExpr.dyadic n) (ClockedExpr.dyadic_pos n) : ℝ)| := abs_sub_le _ _ _
    _ ≤ (o.modulus α j : ℝ) * (b.radius : ℝ) + (ClockedExpr.dyadic n : ℝ) := add_le_add h₁ h₂
    _ = _ := by
      change _ = ((ClockedExpr.dyadic n + o.modulus α j * b.radius : ℚ) : ℝ)
      push_cast
      ring

theorem clockBall_converges (hF : ∀ j, ContDiff ℝ ∞ (F j))
    (p : ProfileExpr) (α : List (Fin 4)) (j : Fin 2) (y : RationalSpaceTime) :
    QBall.Converges (o.clockBall p α j y) (componentJet F α j (clockedPoint p (rationalPoint y))) := by
  apply QBall.converges_of_contains (o.clockBall_contains hF p α j y)
  have h := ClockedExpr.dyadic_tendsto.add
    ((p.enclose_converges y.1).2.const_mul (o.modulus α j : ℝ))
  simpa only [clockBall, Rat.cast_add, Rat.cast_mul, mul_zero, add_zero] using h

end PlanarJetOracle

namespace DetectorExpr

def enclose {F : PlanarComponents} (o : PlanarJetOracle F) :
    (e : DetectorExpr) → e.Valid → RationalSpaceTime → ℕ → QBall
  | .known e, he, y, n => e.enclose he y n
  | .input p α j, _, y, n => o.clockBall p α j y n
  | .add e f, he, y, n => (e.enclose o he.1 y n).add (f.enclose o he.2 y n)
  | .mul e f, he, y, n => (e.enclose o he.1 y n).mul (f.enclose o he.2 y n)

theorem enclose_contains {F : PlanarComponents} (o : PlanarJetOracle F)
    (hF : ∀ j, ContDiff ℝ ∞ (F j)) {e : DetectorExpr} (he : e.Valid)
    (y : RationalSpaceTime) (n : ℕ) : (e.enclose o he y n).Contains (e.val F (rationalPoint y)) := by
  induction e with
  | known e => exact e.enclose_contains he y n
  | input p α j => exact o.clockBall_contains hF p α j y n
  | add e f ihe ihf => exact QBall.contains_add (ihe he.1) (ihf he.2)
  | mul e f ihe ihf => exact QBall.contains_mul (ihe he.1) (ihf he.2)

theorem enclose_converges {F : PlanarComponents} (o : PlanarJetOracle F)
    (hF : ∀ j, ContDiff ℝ ∞ (F j)) {e : DetectorExpr} (he : e.Valid)
    (y : RationalSpaceTime) : QBall.Converges (e.enclose o he y) (e.val F (rationalPoint y)) := by
  induction e with
  | known e => exact e.enclose_converges he y
  | input p α j => exact o.clockBall_converges hF p α j y
  | add e f ihe ihf => exact (ihe he.1).add (ihf he.2)
  | mul e f ihe ihf => exact (ihe he.1).mul (ihf he.2)

end DetectorExpr
end ForcedComputation.VelocityDetector

end

end OAI
