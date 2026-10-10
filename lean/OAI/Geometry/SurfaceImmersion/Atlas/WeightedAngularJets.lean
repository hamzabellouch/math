import OAI.Geometry.SurfaceImmersion.Correction.WeightedJetExpressions
import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialVector

namespace OAI

/-! Uniform spatial estimates after any fixed number of angular derivatives.
Angular differentiation does not increase the polynomial scale loss. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open LocalPeriodicExpansion WeightedEstimates

namespace Expression

def angles (e : Expression) : ℕ → Expression
  | 0 => e
  | k + 1 => (e.angles k).angle

@[simp] lemma order_angles (e : Expression) (k : ℕ) : (e.angles k).order = e.order := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [angles, order_angle] using ih

@[simp] lemma loss_angles (e : Expression) (k : ℕ) : (e.angles k).loss = e.loss := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [angles, loss_angle] using ih

lemma smoothCoeffs_angles {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) (k : ℕ) : (e.angles k).SmoothCoeffs O := by
  induction k with
  | zero => exact he
  | succ k ih => exact smoothCoeffs_angle hO ih

end Expression

namespace VectorExpression

def angles (R : VectorExpression) (k : ℕ) : VectorExpression := fun i => (R i).angles k

def angularFamily {S : TopologicalSpace.Opens Base} (U : Family S R4) : ℕ → Family S R4
  | 0 => U
  | k + 1 => (angularFamily U k).angle

lemma represents_angles {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hQ : Set.MapsTo (lowJet G) S O)
    {R : VectorExpression} {U : Family S R4} (hRs : R.SmoothCoeffs O)
    (hR : Represents G R U) (k : ℕ) : Represents G (R.angles k) (angularFamily U k) := by
  induction k with
  | zero => exact hR
  | succ k ih =>
    exact represents_angle hO hQ (fun i => Expression.smoothCoeffs_angles hO (hRs i) k) ih

/-- The constant may depend on the derivative orders, but the scale exponent
is unchanged by angular or spatial differentiation. -/
theorem compact_angular_bound {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (R : VectorExpression) (hRs : R.SmoothCoeffs O) (i : Fin 4) (k m : ℕ)
    (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (s : ℝ), 0 < s → s ≤ 1 →
      ContDiff ℝ ∞ G → Set.MapsTo (lowJet G) S K →
      WeightedBound S s (m + (R i).order) B (lowJet G) →
      ∀ (U : Family S R4), Represents G R U → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound S s m (D / s ^ (R i).loss)
          (fun p => (angularFamily U k).val p (t : CovarianceCorrector.Period) i) := by
  obtain ⟨D, hD, hd⟩ := Expression.compact_expression_bound S.isOpen hO hK hKO
    ((R i).angles k) (Expression.smoothCoeffs_angles hO (hRs i) k) m B hB
  refine ⟨D, hD, ?_⟩
  intro G s hs hs1 hG hGK hb U hR t ht
  have hQ : Set.MapsTo (lowJet G) S O := fun _ hp => hKO (hGK hp)
  have hrep := represents_angles hO hQ hRs hR k
  have hb' : WeightedBound S s (m + ((R i).angles k).order) B (lowJet G) := by
    simpa only [Expression.order_angles] using hb
  have h := hd G s hs hs1 hG hGK hb' t ht
  simp only [Expression.loss_angles] at h
  exact h.congr (fun p hp => (hrep i p hp t).symm)

end VectorExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
