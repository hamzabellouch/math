import OAI.Combinatorics.ContingencyTables.Transport.BalancedFamily
import OAI.Combinatorics.ContingencyTables.Transport.ScalarPenalty

namespace OAI

/-!
# Root penalties and exact nonroot equations

Root lines carry their actual absolute-deviation penalty. Nonroot lines
carry a positive equality softener; its limit is the exact prescribed-line
indicator. Unary interval penalties include the companion's tree factors.
All balanced large-cell sums are performed before this finite limit.
-/

namespace ContingencyTables.EqualitySoftening

open scoped BigOperators Classical Matrix Topology
open Filter CommonBasesFPRAS FactorialSignatures ProductIntegerSignature
open ScalarPenalty IntegerMarginal BalancedBox BalancedFamily

variable {C G : Type*} [Fintype C] [Fintype G]

noncomputable def lineFactor (root : G → Bool) (rate offset slope : G → ℝ)
    (L : ℝ) (g : G) (n : ℕ) : ℝ :=
  factor (if root g then rate g else L) (fun k => |offset g+(k:ℝ)*slope g|) n

noncomputable def exactLineFactor (root : G → Bool) (rate offset slope : G → ℝ)
    (g : G) (n : ℕ) : ℝ :=
  if root g then factor (rate g) (fun k => |offset g+(k:ℝ)*slope g|) n
  else if |offset g+(n:ℝ)*slope g|=0 then 1 else 0

/-- A physical affine coordinate, including a reflected tree coordinate. -/
noncomputable def affineDistance (ell slope cap : ℝ) (n : ℕ) : ℝ :=
  max 0 (max (-(ell+(n:ℝ)*slope)) (ell+(n:ℝ)*slope-cap))

lemma affineDistance_convex (ell slope cap : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    2*affineDistance ell slope cap (n-1) ≤
      affineDistance ell slope cap n+affineDistance ell slope cap (n-2) := by
  unfold affineDistance
  apply max_convex (fun _ => 0)
    (fun k => max (-(ell+(k:ℝ)*slope)) (ell+(k:ℝ)*slope-cap)) n
  · simp
  · apply max_convex (fun k => -(ell+(k:ℝ)*slope))
      (fun k => ell+(k:ℝ)*slope-cap) n
    · have h := affine_midpoint (-ell) (-slope) n hn
      convert le_of_eq h using 1 <;> ring
    · have h := affine_midpoint (ell-cap) slope n hn
      convert le_of_eq h using 1 <;> ring

noncomputable def unaryFactor (rate ell slope cap : C → ℝ) (i : C) (n : ℕ) : ℝ :=
  factor (rate i) (affineDistance (ell i) (slope i) (cap i)) n

noncomputable def softenedWeight (line : C → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : C → ℝ) (L : ℝ) :
    (C → ℕ) → ℝ :=
  productWeight line (lineFactor root rate offset slope L) (unaryFactor urate ell uslope cap)

noncomputable def exactWeight (line : C → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : C → ℝ) : (C → ℕ) → ℝ :=
  productWeight line (exactLineFactor root rate offset slope) (unaryFactor urate ell uslope cap)

lemma softenedWeight_positive (line : C → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : C → ℝ) (L : ℝ) (z : C → ℕ) :
    0 < softenedWeight line root rate offset slope urate ell uslope cap L z := by
  apply mul_pos <;> apply Finset.prod_pos <;> intro i _ <;> apply factor_positive

/-- The actual positive factors prove the raw signature; it is not an
assumption about a previously lifted binary weight. -/
theorem softenedWeight_removal (line : C → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : C → ℝ) (L : ℝ)
    (hrate : ∀ g, 0 ≤ rate g) (hu : ∀ i, 0 ≤ urate i) (hL : 0 ≤ L) (z : C → ℕ) :
    OnePositiveDirection
      (integerRemovalMatrix (softenedWeight line root rate offset slope urate ell uslope cap L) z).toBilin' := by
  apply product_removal_onePositive line (lineFactor root rate offset slope L)
    (unaryFactor urate ell uslope cap) z
  · intro g n _; exact factor_positive _ _ _
  · intro i n _; exact factor_positive _ _ _
  · intro g hn
    apply abs_factor_logConcave _ _ _ _ _ hn
    split_ifs
    · exact hrate g
    · exact hL
  · intro i hn
    exact factor_logConcave (urate i) (hu i) _ _
      (affineDistance_convex (ell i) (uslope i) (cap i) _ hn)

omit [Fintype G] in
lemma lineFactor_tendsto (root : G → Bool) (rate offset slope : G → ℝ) (g : G) (n : ℕ) :
    Tendsto (fun L : ℝ => lineFactor root rate offset slope L g n) atTop
      (nhds (exactLineFactor root rate offset slope g n)) := by
  by_cases hroot : root g
  · simp [lineFactor,exactLineFactor,hroot]
  · simpa [lineFactor,exactLineFactor,hroot,factor] using
      factor_limit |offset g+(n:ℝ)*slope g| (abs_nonneg _)

theorem softenedWeight_tendsto (line : C → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : C → ℝ) (z : C → ℕ) :
    Tendsto (fun L : ℝ => softenedWeight line root rate offset slope urate ell uslope cap L z) atTop
      (nhds (exactWeight line root rate offset slope urate ell uslope cap z)) := by
  apply Tendsto.mul_const
  apply tendsto_finsetProd
  intro g _
  exact lineFactor_tendsto root rate offset slope g (lineTotal line z g)

/-- The exact-equality product itself inherits its finite raw signature. -/
theorem exactWeight_removal (line : C → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : C → ℝ)
    (hrate : ∀ g, 0 ≤ rate g) (hu : ∀ i, 0 ≤ urate i) (z : C → ℕ) :
    OnePositiveDirection
      (integerRemovalMatrix (exactWeight line root rate offset slope urate ell uslope cap) z).toBilin' := by
  apply removal_signature_limit (l := (atTop : Filter ℝ))
    (fun L => softenedWeight line root rate offset slope urate ell uslope cap L)
    (exactWeight line root rate offset slope urate ell uslope cap) z
    (softenedWeight_tendsto line root rate offset slope urate ell uslope cap)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
  exact softenedWeight_removal line root rate offset slope urate ell uslope cap L hrate hu hL z

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- This is the actual finite balanced large-cell marginal with exact
nonroot equations. Positive softening is retained through every sum and
removed only after the last sum. -/
theorem exact_marginal_removal (Ms : List ℕ) (m : I → ℕ) (R : ℕ)
    (line : Coordinates I Ms → G) (root : G → Bool) (rate offset slope : G → ℝ)
    (urate ell uslope cap : Coordinates I Ms → ℝ)
    (hwidth : ∀ M ∈ Ms, 2 ≤ M) (hrate : ∀ g, 0 ≤ rate g) (hu : ∀ i, 0 ≤ urate i) :
    RemovalSlice (eliminate Ms (exactWeight line root rate offset slope urate ell uslope cap)) m R := by
  intro z hz htotal
  apply removal_signature_limit (l := (atTop : Filter ℝ))
    (fun L => eliminate Ms (softenedWeight line root rate offset slope urate ell uslope cap L))
    (eliminate Ms (exactWeight line root rate offset slope urate ell uslope cap)) z
  · intro x
    exact eliminate_tendsto Ms _ _
      (softenedWeight_tendsto line root rate offset slope urate ell uslope cap) x
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
    have hp : PositiveSlice (softenedWeight line root rate offset slope urate ell uslope cap L)
        (bounds m Ms) (R+Ms.sum) := by
      intro x _ _
      exact softenedWeight_positive line root rate offset slope urate ell uslope cap L x
    have hs : RemovalSlice (softenedWeight line root rate offset slope urate ell uslope cap L)
        (bounds m Ms) (R+Ms.sum) := by
      intro x _ _
      convert softenedWeight_removal line root rate offset slope urate ell uslope cap L hrate hu hL x using 1
      congr 2 <;> exact Subsingleton.elim _ _
    exact (eliminate_slices Ms m R _ hwidth hp hs).2 z hz htotal

end ContingencyTables.EqualitySoftening

end OAI
