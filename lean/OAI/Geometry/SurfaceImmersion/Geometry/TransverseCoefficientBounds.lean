import OAI.Geometry.SurfaceImmersion.Geometry.FiniteFastBounds

namespace OAI

/-! Uniform bounds for the first two transverse derivatives of represented
periodic coefficients. Their common loss is fixed before the slow map. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial.VectorExpression
open LocalPeriodicExpansion WeightedEstimates

def transverse (R : VectorExpression) (second : Bool) : VectorExpression :=
  if second then (R.slow 1).slow 1 else R.slow 1

def transverseFamily {S : TopologicalSpace.Opens Base} (U : Family S R4) (second : Bool) : Family S R4 :=
  if second then (U.slow (coordinateVector 1)).slow (coordinateVector 1) else U.slow (coordinateVector 1)

lemma transverse_smooth {O : Set LowJet} (hO : IsOpen O) {R : VectorExpression}
    (hR : R.SmoothCoeffs O) (second : Bool) : (R.transverse second).SmoothCoeffs O := by
  have h1 : (R.slow 1).SmoothCoeffs O := fun a => Expression.smoothCoeffs_slow hO 1 (hR a)
  cases second
  · exact h1
  · exact fun a => Expression.smoothCoeffs_slow hO 1 (h1 a)

lemma transverse_order {R : VectorExpression} {N : ℕ} (hN : 2 ≤ N)
    (hR : ∀ a, (R a).order ≤ N) (second : Bool) (a : Fin 4) :
    (R.transverse second a).order ≤ N+2 := by
  have h1 := order_slow_le hN hR 1
  cases second
  · exact (h1 a).trans (by omega)
  · exact order_slow_le (by omega) h1 1 a

lemma represents_transverse {S : TopologicalSpace.Opens Base} {O : Set LowJet}
    (hO : IsOpen O) {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hGO : MapsTo (lowJet G) S O)
    {R : VectorExpression} {U : Family S R4} (hRs : R.SmoothCoeffs O) (hR : Represents G R U)
    (second : Bool) : Represents G (R.transverse second) (transverseFamily U second) := by
  have h1 := represents_slow hO hG hGO hRs hR 1
  cases second
  · exact h1
  · exact represents_slow hO hG hGO
      (fun a => Expression.smoothCoeffs_slow hO 1 (hRs a)) h1 1

theorem compact_transverse_coefficients {S : TopologicalSpace.Opens Base} {O Q : Set LowJet}
    (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (R : ℕ → VectorExpression) (L N : ℕ) (hN : 2 ≤ N)
    (hRs : ∀ i < L, (R i).SmoothCoeffs O) (hRo : ∀ i < L, ∀ a, (R i a).order ≤ N)
    (ℓ : Base →L[ℝ] ℝ) :
    ∃ loss : ℕ, ∀ B : ℝ, 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : Base → Space) (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      ContDiff ℝ ∞ G → MapsTo (lowJet G) S Q →
      WeightedBound S s (N+2) B (lowJet G) →
      ∀ U : ℕ → Family S R4, (∀ i < L, Represents G (R i) (U i)) →
      ∀ i < L, ∀ second : Bool, ∀ p ∈ S,
        ‖(transverseFamily (U i) second).fastValue ℓ z p‖ ≤ D/s^loss := by
  classical
  let R' : Bool × Fin L → VectorExpression := fun j => (R j.2).transverse j.1
  let loss := Finset.univ.sup (fun j : Bool × Fin L => Finset.univ.sup (fun a : Fin 4 => (R' j a).loss))
  have hl (j : Bool × Fin L) (a : Fin 4) : (R' j a).loss ≤ loss :=
    (Finset.le_sup (f := fun a : Fin 4 => (R' j a).loss) (Finset.mem_univ a)).trans
      (Finset.le_sup (f := fun j : Bool × Fin L => Finset.univ.sup (fun a : Fin 4 => (R' j a).loss))
        (Finset.mem_univ j))
  refine ⟨loss,?_⟩
  intro B hB
  obtain ⟨D,hD,hd⟩ := compact_finite_fast_bound (S := S) hO hQ hQO R'
    (fun j => transverse_smooth hO (hRs j.2 j.2.isLt) j.1) (N+2) loss
    (fun j a => transverse_order hN (hRo j.2 j.2.isLt) j.1 a) hl ℓ 0 B hB
  refine ⟨D,hD,?_⟩
  intro G s z hz hzs hs1 hG hGQ hb U hrep i hi second p hp
  have hGO : MapsTo (lowJet G) S O := fun _ hx => hQO (hGQ hx)
  have hh := hd G s z hz hzs hs1 hG hGQ (by simpa only [zero_add] using hb)
    (fun j : Bool × Fin L => transverseFamily (U j.2) j.1)
    (fun j => represents_transverse hO hG hGO (hRs j.2 j.2.isLt) (hrep j.2 j.2.isLt) j.1)
    (second,⟨i,hi⟩)
  exact hh.norm_le hp

end ClosedSurfaceR4.JetPolynomial.VectorExpression

end

end OAI
