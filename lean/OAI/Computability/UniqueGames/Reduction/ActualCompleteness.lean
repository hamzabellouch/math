import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import OAI.Computability.UniqueGames.Reduction.ActualCanonicalLemmas
import OAI.Computability.UniqueGames.Reduction.ActualGame
import OAI.Computability.UniqueGames.Reduction.ActualSourceLemmas
import OAI.Computability.UniqueGames.Reduction.BinaryLinear
import OAI.Computability.UniqueGames.Reduction.GapSemanticsLemmas

namespace OAI

section

/-! Actual finite-distribution identities for completeness. -/
namespace UniqueGamesTheorem.Reduction.ActualCompleteness

open UniqueGamesTheorem.Integration.BinaryLinear
open scoped BigOperators

section Evaluation
variable {E R : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup R] [Module F2 R] [Fintype R] [Fintype (E →ₗ[F2] R)]

/-- Evaluation at a point on the homogeneous `h = 1` slice sends the uniform
law on all linear maps to the uniform law on the target vector space. -/
theorem expect_linear_eval (τ : E →ₗ[F2] F2) (x : E) (hx : τ x = 1)
    (g : R → ℚ) :
    (𝔼 X : E →ₗ[F2] R, g (X x)) = 𝔼 r : R, g r := by
  classical
  have hinv (r : R) : (𝔼 X : E →ₗ[F2] R, g (X x + r)) =
      𝔼 X : E →ₗ[F2] R, g (X x) := by
    let e : (E →ₗ[F2] R) ≃ (E →ₗ[F2] R) := Equiv.addRight (τ.smulRight r)
    apply Fintype.expect_equiv e
    intro X
    simp [e, hx]
  calc
    (𝔼 X : E →ₗ[F2] R, g (X x)) =
        𝔼 r : R, 𝔼 X : E →ₗ[F2] R, g (X x + r) := by simp only [hinv, Fintype.expect_const]
    _ = 𝔼 X : E →ₗ[F2] R, 𝔼 r : R, g (X x + r) := Finset.expect_comm _ _ _
    _ = 𝔼 r : R, g r := by
      have hshift (a : R) : (𝔼 r : R, g (a + r)) = 𝔼 r : R, g r := by
        apply Fintype.expect_equiv (Equiv.addLeft a)
        intro r
        rfl
      simp only [hshift, Fintype.expect_const]

/-- Independent uniform linear maps retain independence after evaluating the
same `h = 1` point. In particular the second coordinate is a uniform binary bit. -/
theorem expect_independent_linear_evals [Fintype (E →ₗ[F2] F2)]
    (τ : E →ₗ[F2] F2) (x : E) (hx : τ x = 1) (g : R → F2 → ℚ) :
    (𝔼 X : E →ₗ[F2] R, 𝔼 ell : E →ₗ[F2] F2, g (X x) (ell x)) =
      𝔼 r : R, 𝔼 b : F2, g r b := by
  simp_rw [expect_linear_eval τ x hx]
  exact expect_linear_eval τ x hx (fun r => 𝔼 b : F2, g r b)

end Evaluation

open ActualSource

section Noise
variable {E : Type*} [AddCommGroup E] [Module F2 E] {s d : Nat}
  [Fintype (E →ₗ[F2] Ambient s d)] [Fintype (E →ₗ[F2] F2)]

/-- The actual honest noise test on a fixed valid homogeneous point. -/
noncomputable def localNoiseFailure (g : SplitGadget s d) (x : E) : ℚ :=
  𝔼 X : E →ₗ[F2] Ambient s d, 𝔼 i : g.NoiseIndex, 𝔼 ell : E →ₗ[F2] F2,
    if g.f (X x + ell x • g.noise i) = g.f (X x) then 0 else 1

/-- The independent random functional makes the conditional noise failure
exactly half the gadget's stability error, including indexed noise repetitions. -/
theorem localNoiseFailure_eq_half (g : SplitGadget s d)
    (τ : E →ₗ[F2] F2) (x : E) (hx : τ x = 1) :
    localNoiseFailure g x = g.stabilityError / 2 := by
  classical
  have hbit (r v : Ambient s d) :
      (𝔼 b : F2, if g.f (r + b • v) = g.f r then (0 : ℚ) else 1) =
        (if g.f (r + v) = g.f r then (0 : ℚ) else 1) / 2 := by
    have huniv : (Finset.univ : Finset F2) = {0, 1} := by decide
    by_cases h : g.f (r + v) = g.f r <;> simp [Finset.expect, huniv, h]
  have hinner (X : E →ₗ[F2] Ambient s d) (i : g.NoiseIndex) :
      (𝔼 ell : E →ₗ[F2] F2,
        if g.f (X x + ell x • g.noise i) = g.f (X x) then (0 : ℚ) else 1) =
      (if g.f (X x + g.noise i) = g.f (X x) then (0 : ℚ) else 1) / 2 := by
    exact (expect_linear_eval τ x hx
      (fun b => if g.f (X x + b • g.noise i) = g.f (X x) then (0 : ℚ) else 1)).trans
      (hbit (X x) (g.noise i))
  unfold localNoiseFailure
  simp_rw [hinner]
  rw [expect_linear_eval τ x hx (fun r => 𝔼 i : g.NoiseIndex,
    (if g.f (r + g.noise i) = g.f r then (0 : ℚ) else 1) / 2)]
  have hstab : g.stabilityError = 𝔼 r : Ambient s d, 𝔼 i : g.NoiseIndex,
      if g.f (r + g.noise i) = g.f r then (0 : ℚ) else 1 := by
    exact (Finset.expect_product Finset.univ Finset.univ
      (fun ri : Ambient s d × g.NoiseIndex =>
        if g.f (ri.1 + g.noise ri.2) = g.f ri.1 then (0 : ℚ) else 1))
  rw [hstab]
  simp only [div_eq_mul_inv]
  simp_rw [Finset.expect_mul]

theorem localNoiseFailure_le (g : SplitGadget s d)
    (τ : E →ₗ[F2] F2) (x : E) (hx : τ x = 1) :
    localNoiseFailure g x ≤ g.stabilityError := by
  rw [localNoiseFailure_eq_half g τ x hx]
  have := g.stabilityError_nonneg
  linarith

end Noise

section Source

theorem expect_function_apply {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [Nonempty Ω]
    (j : I) (f : Ω → ℚ) :
    (𝔼 U : I → Ω, f (U j)) = 𝔼 w : Ω, f w := by
  classical
  calc
    (𝔼 U : I → Ω, f (U j)) =
        𝔼 p : Ω × ({j' : I // j' ≠ j} → Ω), f p.1 := by
      apply Fintype.expect_equiv (Equiv.funSplitAt j Ω)
      intro U
      rfl
    _ = 𝔼 w : Ω, f w := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      simp only [Fintype.expect_const]

noncomputable def tupleFailure (S : Source) (A : Fin S.variables → Bool) (k : Nat) : ℚ :=
  𝔼 U : Fin k → Fin S.occurrences,
    if ∀ j, S.satisfied A (U j) = true then 0 else 1

theorem tupleFailure_le (S : Source) (A : Fin S.variables → Bool) (k : Nat) :
    tupleFailure S A k ≤ k * S.failure A := by
  classical
  have hpoint (U : Fin k → Fin S.occurrences) :
      (if ∀ j, S.satisfied A (U j) = true then (0 : ℚ) else 1) ≤
        ∑ j : Fin k, if S.satisfied A (U j) then (0 : ℚ) else 1 := by
    by_cases hgood : ∀ j, S.satisfied A (U j) = true
    · simp [hgood]
    · have hex : ∃ j, S.satisfied A (U j) ≠ true := not_forall.mp hgood
      obtain ⟨j, hj⟩ := hex
      have hsum := Finset.single_le_sum
        (f := fun j : Fin k => if S.satisfied A (U j) then (0 : ℚ) else 1)
        (s := Finset.univ) (a := j) (by intro i _; split <;> norm_num)
        (Finset.mem_univ j)
      simpa [hgood, hj] using hsum
  calc
    tupleFailure S A k ≤ 𝔼 U : Fin k → Fin S.occurrences,
        ∑ j : Fin k, if S.satisfied A (U j) then (0 : ℚ) else 1 :=
      Finset.expect_le_expect (fun U _ => hpoint U)
    _ = ∑ j : Fin k, 𝔼 U : Fin k → Fin S.occurrences,
        if S.satisfied A (U j) then (0 : ℚ) else 1 := Finset.expect_sum_comm _ _ _
    _ = k * S.failure A := by
      have hcoord (j : Fin k) :
          (𝔼 U : Fin k → Fin S.occurrences,
            if S.satisfied A (U j) then (0 : ℚ) else 1) = S.failure A :=
        expect_function_apply j (fun e => if S.satisfied A e then (0 : ℚ) else 1)
      simp_rw [hcoord]
      simp

end Source

section HonestEvaluation
open ActualCanonical ActualHomogeneous
variable {Name Id R : Type*} [AddCommGroup R] [Module F2 R] [DecidableEq R] {k : Nat}

def evalTriple (names : Id → Fin 3 → Name) (A : Name → F2) (e : Id)
    (a : Fin 3 → R) : R := ∑ i, A (names e i) • a i

def evalRecord (names : Id → Fin 3 → Name) (A : Name → F2) : Record Name Id R → R
  | .blank => 0
  | .single n c => A n • c
  | .full e a => evalTriple names A e a

/-- An assignment is evaluated from retained record data only. -/
def evaluate (names : Id → Fin 3 → Name) (A : Name → F2)
    (d : Data k Name Id R) : R := d.1 + ∑ j, evalRecord names A (d.2 j)

theorem record_eval_normalized (names : Id → Fin 3 → Name) (A : Name → F2)
    (e : Id) (a : Fin 3 → R) :
    evalRecord names A (record names e a) = evalTriple names A e (ActualCanonical.normalize a) := by
  classical
  by_cases h01 : a 0 = a 1
  · by_cases h02 : a 0 = a 2
    · simp_all [record, evalRecord, evalTriple, ActualCanonical.normalize, ActualCanonical.translate, pivot,
        Fin.sum_univ_three, ActualCanonical.add_self]
    · simp_all [record, evalRecord, evalTriple, ActualCanonical.normalize, ActualCanonical.translate, pivot,
        Fin.sum_univ_three, ActualCanonical.add_self]
  · by_cases h02 : a 0 = a 2
    · simp_all [record, evalRecord, evalTriple, ActualCanonical.normalize, ActualCanonical.translate, pivot,
        Fin.sum_univ_three, ActualCanonical.add_self]
    · by_cases h12 : a 1 = a 2
      · simp_all [record, evalRecord, evalTriple, ActualCanonical.normalize, ActualCanonical.translate, pivot,
          Fin.sum_univ_three, ActualCanonical.add_self]
      · simp [record, h01, h02, h12, evalRecord]

theorem record_eval_adjustment (names : Id → Fin 3 → Name) (A : Name → F2)
    (rhs : Id → F2) (e : Id) (a : Fin 3 → R)
    (hvalid : ∑ i, A (names e i) = rhs e) :
    rhs e • pivot a + evalRecord names A (record names e a) = evalTriple names A e a := by
  rw [record_eval_normalized]
  simp only [evalTriple, ActualCanonical.normalize, ActualCanonical.translate, smul_add, Finset.sum_add_distrib,
    ← Finset.sum_smul, hvalid]
  calc
    _ = (∑ i, A (names e i) • a i) + (rhs e • pivot a + rhs e • pivot a) := by abel
    _ = _ := by rw [ActualCanonical.add_self, add_zero]

theorem evaluate_data (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (A : Name → F2) (z : R) (a : Fin k → Fin 3 → R)
    (hvalid : ∀ j, ∑ i, A (names (occ j) i) = rhs (occ j)) :
    evaluate names A (data occ names rhs z a) =
      z + ∑ j, evalTriple names A (occ j) (a j) := by
  simp only [evaluate, data]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => record_eval_adjustment names A rhs (occ j) (a j) (hvalid j))

/-- The free-coordinate local assignment always has homogeneous coordinate one. -/
def honestPoint (occ : Fin k → Id) (names : Id → Fin 3 → Name) (A : Name → F2) : E k :=
  (1, fun j => (A (names (occ j) 0), A (names (occ j) 1)))

@[simp] theorem honestPoint_tau (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (A : Name → F2) : tau (honestPoint occ names A) = 1 := rfl

/-- Actual canonical evaluation equals linear-map evaluation on every question
whose occurrences the assignment satisfies. -/
theorem canonical_evaluate (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (A : Name → F2) (X : E k →ₗ[F2] R)
    (hvalid : ∀ j, ∑ i, A (names (occ j) i) = rhs (occ j)) :
    evaluate names A (canonical occ names rhs X) = X (honestPoint occ names A) := by
  rw [canonical, evaluate_data occ names rhs A _ _ hvalid]
  conv_rhs => rw [ActualHomogeneous.linearMap_expansion]
  simp [honestPoint, evalTriple, standardTriple, Fin.sum_univ_three]

end HonestEvaluation

section ActualLabeling
noncomputable section

def honestVertexLabel (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (A : Fin S.variables → Bool) (v : ActualGame.Vertex S k s d) : Alphabet s :=
  g.f ((0, v.val.1) + ∑ j, evalRecord (ActualGame.names S)
    (fun n => ofBit (A n)) (v.val.2 j))

def honestLabeling (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (A : Fin S.variables → Bool) :
    Fin (ActualGame.vertexCount S k s d) → Fin (2^s) :=
  ActualGame.labelingOf S k s d (fun _ => honestVertexLabel S k g A)

/-- Equivariance recovers the dropped alphabet component exactly. -/
theorem honest_unfolded (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (A : Fin S.variables → Bool) (side : Bool) (q : ActualGame.Query S k s d) :
    ActualGame.unfolded S k s d (honestLabeling S k g A) side q =
      g.f (evaluate (ActualGame.names S) (fun n => ofBit (A n))
        (ActualGame.canonical S k s d q)) := by
  simp only [honestLabeling, ActualGame.unfolded, ActualGame.sideLabel_labelingOf,
    ActualOrbit.unfold]
  let z := (ActualGame.canonical S k s d q).1
  let r := ∑ j, evalRecord (ActualGame.names S) (fun n => ofBit (A n))
    ((ActualGame.canonical S k s d q).2 j)
  change g.f ((0, z.2) + r) + z.1 = g.f (z + r)
  have hsplit : ((0, z.2) + r) + (z.1, 0) = z + r := by
    apply Prod.ext <;> simp [add_comm]
  have h := g.equivariant ((0, z.2) + r) z.1
  rw [hsplit] at h
  exact h.symm

def sourcePoint (S : Source) (k : Nat) (A : Fin S.variables → Bool)
    (U : ActualGame.Question S k) : ActualHomogeneous.E k :=
  honestPoint U (ActualGame.names S) (fun n => ofBit (A n))

@[simp] theorem sourcePoint_tau (S : Source) (k : Nat) (A : Fin S.variables → Bool)
    (U : ActualGame.Question S k) : ActualHomogeneous.tau (sourcePoint S k A U) = 1 := rfl

theorem satisfied_parity (S : Source) (A : Fin S.variables → Bool)
    (e : Fin S.occurrences) (h : S.satisfied A e = true) :
    ∑ i : Fin 3, ofBit (A (ActualGame.names S e i)) = ActualGame.rhs S e := by
  have hb : ((A (S.equation e).first ^^ A (S.equation e).second) ^^
      A (S.equation e).third) = (S.equation e).rhs := by
    simpa [Source.satisfied, CloneGap.satisfied] using h
  have hf := congrArg ofBit hb
  simpa [Fin.sum_univ_three, ActualGame.names, ActualGame.rhs, ofBit_xor, add_assoc]
    using hf

theorem honest_unfolded_valid (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (A : Fin S.variables → Bool) (side : Bool) (q : ActualGame.Query S k s d)
    (hgood : ∀ j, S.satisfied A (q.1 j) = true) :
    ActualGame.unfolded S k s d (honestLabeling S k g A) side q =
      g.f (q.2 (sourcePoint S k A q.1)) := by
  rw [honest_unfolded]
  apply congrArg g.f
  exact canonical_evaluate q.1 (ActualGame.names S) (ActualGame.rhs S)
    (fun n => ofBit (A n)) q.2 (fun j => satisfied_parity S A (q.1 j) (hgood j))

private theorem expect_pair {I J : Type*} [Fintype I] [Fintype J] (f : I × J → ℚ) :
    (𝔼 p : I × J, f p) = 𝔼 i : I, 𝔼 j : J, f (i, j) :=
  Finset.expect_product _ _ _

theorem honest_acceptance_bound (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.variables → Bool) :
    1 - (k : ℚ) * S.failure A - g.stabilityError / 2 ≤
      ActualGame.acceptanceProbability S k g (honestLabeling S k g A) := by
  classical
  let P (ω : ActualGame.Outcome S k g) : Prop :=
    ActualGame.unfolded S k s d (honestLabeling S k g A) false
        (ActualGame.leftQuery S k g ω) =
      ActualGame.unfolded S k s d (honestLabeling S k g A) true
        (ActualGame.rightQuery S k g ω)
  let bad (ω : ActualGame.Outcome S k g) : ℚ :=
    if ∀ j, S.satisfied A (ω.1.1 j) = true then 0 else 1
  let noiseBad (ω : ActualGame.Outcome S k g) : ℚ :=
    if g.f (ω.1.2 (sourcePoint S k A ω.1.1) +
        ω.2.2 (sourcePoint S k A ω.1.1) • g.noise ω.2.1) =
      g.f (ω.1.2 (sourcePoint S k A ω.1.1)) then 0 else 1
  have hpoint (ω : ActualGame.Outcome S k g) :
      (if P ω then (0 : ℚ) else 1) ≤ bad ω + noiseBad ω := by
    by_cases hgood : ∀ j, S.satisfied A (ω.1.1 j) = true
    · have hL := honest_unfolded_valid S k g A false (ActualGame.leftQuery S k g ω) hgood
      have hR := honest_unfolded_valid S k g A true (ActualGame.rightQuery S k g ω) hgood
      simp only [P, hL, hR, bad, ite_eq_left hgood, zero_add]
      simp [noiseBad, ActualGame.leftQuery, ActualGame.rightQuery,
        LinearMap.add_apply, LinearMap.smulRight_apply, eq_comm]
      exact le_rfl
    · have hn : 0 ≤ noiseBad ω := by dsimp [noiseBad]; split <;> norm_num
      have hf : (if P ω then (0 : ℚ) else 1) ≤ 1 := by split <;> norm_num
      simpa only [bad, ite_eq_right hgood] using hf.trans (le_add_of_nonneg_right hn)
  have hbad : (𝔼 ω : ActualGame.Outcome S k g, bad ω) = tupleFailure S A k := by
    simp only [expect_pair, bad]
    change (𝔼 U : ActualGame.Question S k, 𝔼 _X : ActualGame.Map k s d,
      𝔼 _i : g.NoiseIndex, 𝔼 _ell : ActualGame.Dual k,
      if ∀ j, S.satisfied A (U j) = true then (0 : ℚ) else 1) = _
    simp_rw [Fintype.expect_const]
    rfl
  have hnoise : (𝔼 ω : ActualGame.Outcome S k g, noiseBad ω) = g.stabilityError / 2 := by
    simp only [expect_pair]
    change (𝔼 U : ActualGame.Question S k, localNoiseFailure g (sourcePoint S k A U)) = _
    have hu (U : ActualGame.Question S k) := localNoiseFailure_eq_half g
      ActualHomogeneous.tau (sourcePoint S k A U) (sourcePoint_tau S k A U)
    simp only [hu, Fintype.expect_const]
  have hfailure : (𝔼 ω : ActualGame.Outcome S k g, if P ω then (0 : ℚ) else 1) ≤
      tupleFailure S A k + g.stabilityError / 2 := by
    calc
      _ ≤ 𝔼 ω : ActualGame.Outcome S k g, (bad ω + noiseBad ω) :=
        Finset.expect_le_expect (fun ω _ => hpoint ω)
      _ = _ := by rw [Finset.expect_add_distrib, hbad, hnoise]
  have hsum : ActualGame.acceptanceProbability S k g (honestLabeling S k g A) +
      (𝔼 ω : ActualGame.Outcome S k g, if P ω then (0 : ℚ) else 1) = 1 := by
    rw [ActualGame.acceptanceProbability_eq_test]
    change (𝔼 ω : ActualGame.Outcome S k g, if P ω then (1 : ℚ) else 0) + _ = _
    rw [← Finset.expect_add_distrib]
    have hp (ω : ActualGame.Outcome S k g) :
        (if P ω then (1 : ℚ) else 0) + (if P ω then (0 : ℚ) else 1) = 1 := by
      split <;> norm_num
    simp only [hp, Fintype.expect_const]
  have htuple := tupleFailure_le S A k
  linarith

theorem honest_acceptance_of_bounds (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.variables → Bool) (γ η ε : ℚ)
    (hsource : S.failure A ≤ γ) (hstable : g.stabilityError ≤ η)
    (hbudget : (k : ℚ) * γ + η / 2 ≤ ε) :
    1 - ε ≤ ActualGame.acceptanceProbability S k g (honestLabeling S k g A) := by
  have hm := mul_le_mul_of_nonneg_left hsource (show (0 : ℚ) ≤ k by positivity)
  have hactual := honest_acceptance_bound S k g A
  linarith

/-- The probability bound is exactly a bound on the generated unweighted list. -/
theorem honest_satisfied_fraction_bound (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.variables → Bool) :
    1 - (k : ℚ) * S.failure A - g.stabilityError / 2 ≤
      (Foundations.Target.countSatisfied (honestLabeling S k g A)
        (ActualGame.outputInstance S k g).constraints : ℚ) /
        (ActualGame.outputInstance S k g).constraints.length := by
  rw [← ActualGame.acceptanceProbability_eq_count]
  exact honest_acceptance_bound S k g A

/-- The honest labeling witnesses the formal target completeness predicate for
the actual generated instance whenever its actual error budget fits the target. -/
theorem actual_completeAt (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.variables → Bool)
    (error : Foundations.Target.RationalError)
    (hbudget : (k : ℚ) * S.failure A + g.stabilityError / 2 ≤
      Integration.GapSemantics.errorValue error) :
    Foundations.Target.CompleteAt error (ActualGame.outputInstance S k g) := by
  apply (Integration.GapSemantics.completeAt_iff error _).2
  refine ⟨honestLabeling S k g A, ?_⟩
  change 1 - Integration.GapSemantics.errorValue error ≤
    (Foundations.Target.countSatisfied (honestLabeling S k g A)
      (ActualGame.outputInstance S k g).constraints : ℚ) /
      (ActualGame.outputInstance S k g).constraints.length
  have h := honest_satisfied_fraction_bound S k g A
  linarith

end
end ActualLabeling

end UniqueGamesTheorem.Reduction.ActualCompleteness

end

end OAI
