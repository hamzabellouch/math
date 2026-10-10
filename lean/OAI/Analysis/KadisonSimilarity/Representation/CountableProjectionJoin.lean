import OAI.Analysis.KadisonSimilarity.Tracial.ProjectionJoinTrace
import OAI.Analysis.FactorGeneration.ProjectionLimits

namespace OAI

/-! Countable projection joins with the trace bound inherited from finite
unions. Only the concrete faithful vector trace is used for the limit. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance countableJoin_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance

def finiteProjectionJoin (M : VonNeumannAlgebra H)
    (p : ℕ → M.toStarSubalgebra) : ℕ → M.toStarSubalgebra
  | 0 => 0
  | n + 1 => projectionJoin M (finiteProjectionJoin M p n) (p n)

theorem finiteProjectionJoin_isStarProjection (M : VonNeumannAlgebra H)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n)) (n : ℕ) :
    IsStarProjection (finiteProjectionJoin M p n) := by
  induction n with
  | zero => exact IsStarProjection.zero _
  | succ n ih => exact (projectionJoin_properties M _ _ ih (hp n)).1

theorem finiteProjectionJoin_step (M : VonNeumannAlgebra H)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n)) (n : ℕ) :
    finiteProjectionJoin M p (n + 1) * finiteProjectionJoin M p n =
      finiteProjectionJoin M p n :=
  (projectionJoin_properties M _ _ (finiteProjectionJoin_isStarProjection M p hp n) (hp n)).2.1

theorem finiteProjectionJoin_contains (M : VonNeumannAlgebra H)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (n i : ℕ) (hi : i < n) : finiteProjectionJoin M p n * p i = p i := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hin : i < n
    · calc
        finiteProjectionJoin M p (n + 1) * p i =
            finiteProjectionJoin M p (n + 1) * (finiteProjectionJoin M p n * p i) := by rw [ih hin]
        _ = (finiteProjectionJoin M p (n + 1) * finiteProjectionJoin M p n) * p i :=
          (mul_assoc _ _ _).symm
        _ = p i := by rw [finiteProjectionJoin_step M p hp n, ih hin]
    · have he : i = n := by omega
      subst i
      exact (projectionJoin_properties M _ _ (finiteProjectionJoin_isStarProjection M p hp n)
        (hp n)).2.2.1

theorem finiteProjectionJoin_mono (M : VonNeumannAlgebra H)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (i j : ℕ) (hij : i ≤ j) :
    finiteProjectionJoin M p j * finiteProjectionJoin M p i = finiteProjectionJoin M p i := by
  induction j, hij using Nat.le_induction with
  | base => exact (finiteProjectionJoin_isStarProjection M p hp i).isIdempotentElem.eq
  | succ j _ ih =>
    calc
      _ = finiteProjectionJoin M p (j + 1) *
          (finiteProjectionJoin M p j * finiteProjectionJoin M p i) := by rw [ih]
      _ = (finiteProjectionJoin M p (j + 1) * finiteProjectionJoin M p j) *
          finiteProjectionJoin M p i := (mul_assoc _ _ _).symm
      _ = finiteProjectionJoin M p i := by rw [finiteProjectionJoin_step M p hp j, ih]

theorem finiteProjectionJoin_least (M : VonNeumannAlgebra H)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (r : M.toStarSubalgebra) (hr : ∀ n, r * p n = p n) (n : ℕ) :
    r * finiteProjectionJoin M p n = finiteProjectionJoin M p n := by
  induction n with
  | zero => exact mul_zero _
  | succ n ih => exact (projectionJoin_properties M _ _
      (finiteProjectionJoin_isStarProjection M p hp n) (hp n)).2.2.2 r ih (hr n)

theorem trace_finiteProjectionJoin_le (M : VonNeumannAlgebra H)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n)) (n : ℕ) :
    (τ (finiteProjectionJoin M p n)).re ≤ ∑ i ∈ Finset.range n, (τ (p i)).re := by
  induction n with
  | zero => simp [finiteProjectionJoin]
  | succ n ih =>
    change (τ (projectionJoin M (finiteProjectionJoin M p n) (p n))).re ≤ _
    rw [Finset.sum_range_succ]
    have hj := trace_projectionJoin_le M τ htr (finiteProjectionJoin M p n) (p n) (hp n)
    linarith

/-- The join has trace bounded by every common bound on finite trace sums. -/
theorem exists_countable_projection_join (M : VonNeumannAlgebra H)
    (υ : TracialRepresentation M) (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hτ : ∀ a, τ a = υ.trace a)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (C : ℝ) (hC : ∀ n, ∑ i ∈ Finset.range n, (τ (p i)).re ≤ C) :
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ (τ q).re ≤ C ∧
      (∀ n, q * p n = p n) ∧
      ∀ r : M.toStarSubalgebra, IsStarProjection r → (∀ n, r * p n = p n) → r * q = q := by
  have htr (a b : M.toStarSubalgebra) : τ (a * b) = τ (b * a) := by
    rw [hτ, hτ, υ.trace_mul_comm]
  let b : ℕ → AlgebraProjection M := fun n =>
    ⟨finiteProjectionJoin M p n, finiteProjectionJoin_isStarProjection M p hp n⟩
  have hb : Monotone b := fun i j hij => finiteProjectionJoin_mono M p hp i j hij
  have hbt (n : ℕ) : (υ.trace (b n).val).re ≤ C := by
    rw [← hτ]
    exact (trace_finiteProjectionJoin_le M τ htr p hp n).trans (hC n)
  obtain ⟨q, hq, hqt, hleast⟩ := monotone_projection_upper_bound υ b hb C hbt
  refine ⟨q.val, q.property, ?_, ?_, ?_⟩
  · rwa [hτ]
  · intro n
    have hbn := finiteProjectionJoin_contains M p hp (n + 1) n (Nat.lt_succ_self n)
    calc
      q.val * p n = q.val * ((b (n + 1)).val * p n) := by rw [hbn]
      _ = (q.val * (b (n + 1)).val) * p n := (mul_assoc _ _ _).symm
      _ = p n := by rw [hq (n + 1), hbn]
  · intro r hr hrp
    exact hleast ⟨r, hr⟩ (fun n => finiteProjectionJoin_least M p hp r hrp n)

/-- The countable trace bound transports through a star isomorphism. Only
the target trace needs to be presented by a concrete vector. -/
theorem exists_countable_projection_join_of_equiv
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    [IsClosed (N.toStarSubalgebra : Set (K →L[ℂ] K))]
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra)
    (υ : TracialRepresentation N)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (σ : N.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hσ : ∀ b, σ b = υ.trace b) (he : ∀ a, σ (e a) = τ a)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (C : ℝ) (hC : ∀ n, ∑ i ∈ Finset.range n, (τ (p i)).re ≤ C) :
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ (τ q).re ≤ C ∧
      (∀ n, q * p n = p n) ∧
      ∀ r : M.toStarSubalgebra, IsStarProjection r → (∀ n, r * p n = p n) → r * q = q := by
  obtain ⟨q, hq, hqt, hqp, hleast⟩ := exists_countable_projection_join N υ σ hσ
    (fun n => e (p n)) (fun n => (hp n).map e.toStarAlgHom) C (by simpa only [he] using hC)
  have heq : e (e.symm q) = q := e.apply_symm_apply q
  refine ⟨e.symm q, hq.map e.symm.toStarAlgHom, ?_, ?_, ?_⟩
  · have h := he (e.symm q)
    rw [heq] at h
    rwa [← h]
  · intro n
    apply e.injective
    calc
      e (e.symm q * p n) = e (e.symm q) * e (p n) := e.map_mul' _ _
      _ = q * e (p n) := congrArg (fun b => b * e (p n)) heq
      _ = e (p n) := hqp n
  · intro r hr hrp
    have hu (n : ℕ) : e r * e (p n) = e (p n) :=
      (e.map_mul' r (p n)).symm.trans (congrArg e (hrp n))
    have h := hleast (e r) (hr.map e.toStarAlgHom) hu
    apply e.injective
    calc
      e (r * e.symm q) = e r * e (e.symm q) := e.map_mul' _ _
      _ = e r * q := congrArg (fun b => e r * b) heq
      _ = q := h
      _ = e (e.symm q) := heq.symm

end KadisonSimilarity

end

end OAI
