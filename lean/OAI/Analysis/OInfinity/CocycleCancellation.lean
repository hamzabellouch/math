import OAI.Analysis.OInfinity.CancellationTransport
import OAI.Analysis.OInfinity.JointRohlinWitness

namespace OAI

/-! # Cancellation transport for the actual binary cocycle

The joint cyclic partitions supply all transport premises for the
length-two versus length-one cancellation in binary fragmentation. The
partition is chosen after the cocycle length and requested error. This
remains a theorem about two commuting coisometric binary rows.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- The three transported components, keeping both shifted indices. -/
def cancellationTowerModel {N : ℕ} (e : ZMod N → E) (a b u : E)
    (da db : ZMod N) (θ : ℝ) (k : ZMod N) : E :=
  e k * (1 + (Real.cos θ ^ 2) •
      (a * (u - 1) * star a + b * (star u - 1) * star b)) +
    e (k + da - db) * ((Real.sin θ * Real.cos θ) • (a * (u - 1) * star b)) -
    e (k + db - da) * ((Real.sin θ * Real.cos θ) • (b * (star u - 1) * star a))

private lemma cocycle_row_norm (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (i : Fin 2) :
    ‖s i‖ ≤ 1 := by
  have h := congrArg norm (hs i i)
  simp only [ite_true, CStarRing.norm_star_mul_self] at h
  have hn1 : ‖(1 : E)‖ ≤ 1 := IsStarProjection.norm_le 1
    (isStarProjection_iff'.mpr ⟨by simp, by simp⟩)
  nlinarith [norm_nonneg (s i)]

/-- A cyclic shift estimate for the row endomorphism gives the actual
one-generator transport estimate. -/
lemma cyclic_row_generator_transport {N : ℕ} (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (e : ZMod N → E) (η : ℝ)
    (hshift : ∀ k, ‖finiteRowShift s (e k) - e (k + 1)‖ ≤ η)
    (i : Fin 2) (k : ZMod N) :
    ‖s i * e k - e (k + 1) * s i‖ ≤ η := by
  have heq : s i * e k - e (k + 1) * s i =
      (finiteRowShift s (e k) - e (k + 1)) * s i := by
    rw [sub_mul, finiteRowShift_mul_row 1 s hs (e k) (mul_one _) i]
  rw [heq]
  exact (norm_mul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _)
    (cocycle_row_norm s hs i)).trans (hshift k))

lemma cyclic_row_two_letter_transport {N : ℕ} (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (e : ZMod N → E) (η : ℝ)
    (hshift : ∀ k, ‖finiteRowShift s (e k) - e (k + 1)‖ ≤ η)
    (i r : Fin 2) (k : ZMod N) :
    ‖(s i * s r) * e k - e (k + 2) * (s i * s r)‖ ≤ 2 * η := by
  have heq : (s i * s r) * e k - e (k + 2) * (s i * s r) =
      s i * (s r * e k - e (k + 1) * s r) +
        (s i * e (k + 1) - e (k + 2) * s i) * s r := by noncomm_ring
  have hi := cyclic_row_generator_transport s hs e η hshift i (k + 1)
  have hr := cyclic_row_generator_transport s hs e η hshift r k
  have hind : (k + 1) + 1 = k + 2 := by ring
  rw [hind] at hi
  rw [heq]
  calc
    _ ≤ ‖s i * (s r * e k - e (k + 1) * s r)‖ +
        ‖(s i * e (k + 1) - e (k + 2) * s i) * s r‖ := norm_add_le _ _
    _ ≤ ‖s r * e k - e (k + 1) * s r‖ +
        ‖s i * e (k + 1) - e (k + 2) * s i‖ := add_le_add
      ((norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (cocycle_row_norm s hs i)))
      ((norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (cocycle_row_norm s hs r)))
    _ ≤ 2 * η := by linarith

/-- All the length-two/length-one quarter cancellations have an actual
joint cyclic partition, and their three-band transport error is arbitrarily
small uniformly in angle and tower cell. -/
lemma exists_cocycle_cancellation_partition (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1)
    (hc : bergRowsCommute s t) (m ℓ : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ e : ZMod (2 ^ m) → E,
      (∀ k, IsStarProjection (e k)) ∧ (∑ k, e k) = 1 ∧
      (∀ k l, k ≠ l → e k * e l = 0) ∧
      (∀ k, ‖finiteRowShift s (e k) - e (k + 1)‖ < ε) ∧
      (∀ k, ‖finiteRowShift t (e k) - e (k + 1)‖ < ε) ∧
      (∀ (i r l : Fin 2), i ≠ l → ∀ (θ : ℝ) (k : ZMod (2 ^ m)),
        ‖cornerCancellationPath (s i * s r) (s l)
            (binaryRowCocycleUnitary s t hs ht hsum htsum ℓ) θ * e k -
          cancellationTowerModel e (s i * s r) (s l)
            (binaryRowCocycleUnitary s t hs ht hsum htsum ℓ) 2 1 θ k‖ < ε) := by
  let η := ε / (40 * ((ℓ : ℝ) + 1) + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηeq : η * (40 * ((ℓ : ℝ) + 1) + 1) = ε := by
    dsimp [η]
    exact div_mul_cancel₀ _ (by positivity)
  have hηε : η < ε := by
    nlinarith [mul_nonneg hη.le (Nat.cast_nonneg (α := ℝ) ℓ)]
  obtain ⟨e, he, hes, heo, hS, hT, hu⟩ :=
    exists_joint_binary_cyclic_partition s t hs ht hsum htsum hc m η hη
  refine ⟨e, he, hes, heo, (fun k => (hS k).trans hηε),
    (fun k => (hT k).trans hηε), ?_⟩
  intro i r l hil θ k
  let δ := 2 * ((ℓ : ℝ) + 1) * η
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have htwo : 2 * η ≤ δ := by
    dsimp [δ]
    nlinarith [mul_nonneg hη.le (Nat.cast_nonneg (α := ℝ) ℓ)]
  have hone : η ≤ δ := by linarith
  have huδ : 2 * (ℓ : ℝ) * η ≤ δ := by dsimp [δ]; nlinarith
  have haa : star (s i * s r) * (s i * s r) = 1 := by
    rw [star_mul]
    calc
      _ = star (s r) * (star (s i) * s i) * s r := by noncomm_ring
      _ = 1 := by simp only [hs, ite_true, mul_one]
  have hab : star (s i * s r) * s l = 0 := by
    rw [star_mul, mul_assoc, hs, ite_eq_right hil, mul_zero]
  have hbound := cornerCancellationPath_tower_transport e
    (fun k => (he k).isSelfAdjoint.star_eq) (s i * s r) (s l)
    (binaryRowCocycleUnitary s t hs ht hsum htsum ℓ) haa
    (by simpa only [ite_true] using hs l l) hab 2 1 δ hδ
    (fun k => (cyclic_row_two_letter_transport s hs e η (fun j => (hS j).le) i r k).trans htwo)
    (fun k => (cyclic_row_generator_transport s hs e η (fun j => (hS j).le) l k).trans hone)
    (fun k => (hu k ℓ).trans huδ) θ k
  change ‖cornerCancellationPath (s i * s r) (s l)
      (binaryRowCocycleUnitary s t hs ht hsum htsum ℓ) θ * e k -
    cancellationTowerModel e (s i * s r) (s l)
      (binaryRowCocycleUnitary s t hs ht hsum htsum ℓ) 2 1 θ k‖ ≤ 20 * δ at hbound
  apply hbound.trans_lt
  dsimp [δ]
  nlinarith

end WeakPureInfiniteness

end

end OAI
