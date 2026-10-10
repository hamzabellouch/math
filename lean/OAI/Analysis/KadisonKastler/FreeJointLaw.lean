import OAI.Analysis.KadisonKastler.ProjectionNormalWords

namespace OAI

/-! # The common joint trace law of a projection and a free Haar unitary

The paired-algebra argument applies the same finite normal forms to both
representations. Its scalar coefficients depend only on the trace of the
projection, so the two traces agree throughout the generated algebra and
its norm closure.
-/

namespace KadisonKastler

noncomputable section

universe u v

variable {B : Type u} {C : Type v} [CStarAlgebra B] [CStarAlgebra C]

local instance freeJointLawProductCStarAlgebra : CStarAlgebra (B × C) where

def pairedHaarUnitary (u : unitary B) (v : unitary C) : unitary (B × C) :=
  ⟨((u : B), (v : C)), ⟨Prod.ext u.property.1 v.property.1, Prod.ext u.property.2 v.property.2⟩⟩

private theorem pairedHaarPower_nat (u : unitary B) (v : unitary C) (n : ℕ) :
    haarPower (pairedHaarUnitary u v) (n : ℤ) =
      (haarPower u (n : ℤ), haarPower v (n : ℤ)) := by
  simp only [haarPower_natCast]
  change ((u : B), (v : C)) ^ n = ((u : B) ^ n, (v : C) ^ n)
  simp

theorem pairedHaarPower (u : unitary B) (v : unitary C) (k : ℤ) :
    haarPower (pairedHaarUnitary u v) k = (haarPower u k, haarPower v k) := by
  cases k with
  | ofNat n => exact pairedHaarPower_nat u v n
  | negSucc n =>
    have hn : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
    rw [hn, haarPower_neg, haarPower_neg, haarPower_neg, pairedHaarPower_nat]
    rfl

private theorem projectionNormalTail_pair (q : B) (r : C) (u : unitary B) (v : unitary C)
    (l : List NonzeroHaarExponent) (right : Bool) :
    projectionNormalTail (q, r) (pairedHaarUnitary u v) l right =
      (projectionNormalTail q u l right, projectionNormalTail r v l right) := by
  induction l with
  | nil => cases right <;> rfl
  | cons k l ih =>
    simp only [projectionNormalTail, pairedHaarPower, ih]
    rfl

theorem projectionNormalEval_pair (q : B) (r : C) (u : unitary B) (v : unitary C)
    (w : ProjectionNormalWord) :
    projectionNormalEval (q, r) (pairedHaarUnitary u v) w =
      (projectionNormalEval q u w, projectionNormalEval r v w) := by
  cases w with
  | one => rfl
  | centered => rfl
  | mixed left k l right =>
    simp only [projectionNormalEval, projectionNormalTail_pair, pairedHaarPower]
    cases left <;> rfl

private def jointTraceDifference (τ : FaithfulTracialState B) (σ : FaithfulTracialState C) :
    B × C →ₗ[ℂ] ℂ :=
  τ.toLinearMap.comp (LinearMap.fst ℂ B C) - σ.toLinearMap.comp (LinearMap.snd ℂ B C)

private theorem trace_centered_normalWord (τ : FaithfulTracialState B)
    {A : StarSubalgebra ℂ B} {u : unitary B} (h : FreeHaarMoments τ A u)
    {p : B} (hpA : p ∈ A) {t : ℂ} (hpτ : τ.toLinearMap p = t)
    (w : ProjectionNormalWord) :
    τ.toLinearMap (projectionNormalEval (p - t • (1 : B)) u w) =
      match w with
      | .one => 1
      | .centered => 0
      | .mixed _ _ _ _ => 0 := by
  have hq : p - t • (1 : B) ∈ A := A.sub_mem hpA (A.smul_mem A.one_mem _)
  have hqτ : τ.toLinearMap (p - t • (1 : B)) = 0 := by simp [hpτ, τ.map_one]
  cases w with
  | one => exact τ.map_one
  | centered => exact hqτ
  | mixed left k l right =>
    simpa only [one_mul] using
      h.trace_base_mul_mixed_normalWord_zero hq hqτ A.one_mem left k l right

/-- Equal projection traces determine the full algebraic joint trace law. -/
theorem freeHaar_joint_trace_eq
    (τ : FaithfulTracialState B) (σ : FaithfulTracialState C)
    {A : StarSubalgebra ℂ B} {D : StarSubalgebra ℂ C}
    {u : unitary B} {v : unitary C}
    (hu : FreeHaarMoments τ A u) (hv : FreeHaarMoments σ D v)
    {p : B} {r : C} (hp : IsStarProjection p) (hr : IsStarProjection r)
    (hpA : p ∈ A) (hrD : r ∈ D) {t : ℂ}
    (hpτ : τ.toLinearMap p = t) (hrσ : σ.toLinearMap r = t)
    {x : B × C}
    (hx : x ∈ Algebra.adjoin ℂ
      (insert (p, r) (Set.range (haarPower (pairedHaarUnitary u v))))) :
    τ.toLinearMap x.1 = σ.toLinearMap x.2 := by
  let q : B × C := (p, r) - t • (1 : B × C)
  have hnormal : x ∈ projectionNormalSpan q (pairedHaarUnitary u v) :=
    adjoin_projection_haar_le_normalSpan (p, r)
      (show IsIdempotentElem (p, r) from Prod.ext hp.isIdempotentElem.eq hr.isIdempotentElem.eq)
      (pairedHaarUnitary u v) t hx
  have hker : projectionNormalSpan q (pairedHaarUnitary u v) ≤ (jointTraceDifference τ σ).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    change τ.toLinearMap (projectionNormalEval q (pairedHaarUnitary u v) w).1 -
      σ.toLinearMap (projectionNormalEval q (pairedHaarUnitary u v) w).2 = 0
    have heq : q = (p - t • (1 : B), r - t • (1 : C)) := rfl
    rw [heq, projectionNormalEval_pair]
    simp only [trace_centered_normalWord τ hu hpA hpτ w,
      trace_centered_normalWord σ hv hrD hrσ w, sub_self]
  exact sub_eq_zero.mp (hker hnormal)

private def boundedTrace (τ : FaithfulTracialState B) : B →L[ℂ] ℂ :=
  τ.toLinearMap.mkContinuous 1 (fun x => by simpa using τ.norm_apply_le_norm x)

/-- The same joint law holds for norm limits, which includes the continuous
functional-calculus operations used in the recovery contraction. -/
theorem freeHaar_joint_trace_eq_of_mem_closure
    (τ : FaithfulTracialState B) (σ : FaithfulTracialState C)
    {A : StarSubalgebra ℂ B} {D : StarSubalgebra ℂ C}
    {u : unitary B} {v : unitary C}
    (hu : FreeHaarMoments τ A u) (hv : FreeHaarMoments σ D v)
    {p : B} {r : C} (hp : IsStarProjection p) (hr : IsStarProjection r)
    (hpA : p ∈ A) (hrD : r ∈ D) {t : ℂ}
    (hpτ : τ.toLinearMap p = t) (hrσ : σ.toLinearMap r = t)
    {x : B × C}
    (hx : x ∈ closure (Algebra.adjoin ℂ
      (insert (p, r) (Set.range (haarPower (pairedHaarUnitary u v)))) : Set (B × C))) :
    τ.toLinearMap x.1 = σ.toLinearMap x.2 := by
  have hclosed : IsClosed {z : B × C | τ.toLinearMap z.1 = σ.toLinearMap z.2} :=
    isClosed_eq ((boundedTrace τ).continuous.comp continuous_fst)
      ((boundedTrace σ).continuous.comp continuous_snd)
  apply closure_minimal (t := {z : B × C | τ.toLinearMap z.1 = σ.toLinearMap z.2}) ?_ hclosed hx
  intro z hz
  exact freeHaar_joint_trace_eq τ σ hu hv hp hr hpA hrD hpτ hrσ hz

end

end KadisonKastler

end OAI
