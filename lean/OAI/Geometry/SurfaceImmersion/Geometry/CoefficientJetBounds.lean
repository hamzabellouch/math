import OAI.Geometry.SurfaceImmersion.Geometry.FiniteFastBounds

namespace OAI

/-! The finite first and second slow/angular coefficient jets needed by the
primitive's five leading derivative estimates share one fixed scale loss. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.JetPolynomial.VectorExpression
open LocalPeriodicExpansion WeightedEstimates

def coefficientDerivative (R : VectorExpression) (k : Fin 3) : VectorExpression :=
  ![R.slow 0,R.slow 1,R.angle] k

def coefficientFamilyDerivative {S : TopologicalSpace.Opens Base}
    (U : Family S R4) (k : Fin 3) : Family S R4 :=
  ![U.slow (coordinateVector 0),U.slow (coordinateVector 1),U.angle] k

lemma coefficientDerivative_smooth {O : Set LowJet} (hO : IsOpen O) {R : VectorExpression}
    (hR : R.SmoothCoeffs O) (k : Fin 3) : (R.coefficientDerivative k).SmoothCoeffs O := by
  fin_cases k
  · exact fun a => Expression.smoothCoeffs_slow hO 0 (hR a)
  · exact fun a => Expression.smoothCoeffs_slow hO 1 (hR a)
  · exact fun a => Expression.smoothCoeffs_angle hO (hR a)

lemma coefficientDerivative_order {R : VectorExpression} {N : ℕ} (hN : 2 ≤ N)
    (hR : ∀ a, (R a).order ≤ N) (k : Fin 3) (a : Fin 4) :
    (R.coefficientDerivative k a).order ≤ N+1 := by
  fin_cases k
  · exact order_slow_le hN hR 0 a
  · exact order_slow_le hN hR 1 a
  · change (R a).angle.order ≤ N+1
    rw [Expression.order_angle]
    exact (hR a).trans (Nat.le_succ N)

lemma represents_coefficientDerivative {S : TopologicalSpace.Opens Base} {O : Set LowJet}
    (hO : IsOpen O) {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hGO : MapsTo (lowJet G) S O)
    {R : VectorExpression} {U : Family S R4} (hRs : R.SmoothCoeffs O) (hR : Represents G R U)
    (k : Fin 3) : Represents G (R.coefficientDerivative k) (coefficientFamilyDerivative U k) := by
  fin_cases k
  · exact represents_slow hO hG hGO hRs hR 0
  · exact represents_slow hO hG hGO hRs hR 1
  · exact represents_angle hO hGO hRs hR

theorem compact_coefficient_two_jets {S : TopologicalSpace.Opens Base} {O Q : Set LowJet}
    (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (R : ℕ → VectorExpression) (L N : ℕ) (hN : 2 ≤ N)
    (hRs : ∀ i < L, (R i).SmoothCoeffs O) (hRo : ∀ i < L, ∀ a, (R i a).order ≤ N)
    (ℓ : Base →L[ℝ] ℝ) :
    ∃ loss : ℕ, ∀ B : ℝ, 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : Base → Space) (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      ContDiff ℝ ∞ G → MapsTo (lowJet G) S Q →
      WeightedBound S s (N+2) B (lowJet G) →
      ∀ U : ℕ → Family S R4, (∀ i < L, Represents G (R i) (U i)) →
      ∀ i < L, ∀ k j : Fin 3, ∀ p ∈ S,
        ‖(coefficientFamilyDerivative (U i) k).fastValue ℓ z p‖ ≤ D/s^loss ∧
        ‖(coefficientFamilyDerivative (coefficientFamilyDerivative (U i) k) j).fastValue ℓ z p‖ ≤
          D/s^loss := by
  classical
  let I := Bool × Fin 3 × Fin 3 × Fin L
  let R' : I → VectorExpression := fun a => if a.1 then
    ((R a.2.2.2).coefficientDerivative a.2.1).coefficientDerivative a.2.2.1
    else (R a.2.2.2).coefficientDerivative a.2.1
  have hR's (a : I) : (R' a).SmoothCoeffs O := by
    dsimp only [R']
    split_ifs
    · exact coefficientDerivative_smooth hO
        (coefficientDerivative_smooth hO (hRs _ a.2.2.2.isLt) _) _
    · exact coefficientDerivative_smooth hO (hRs _ a.2.2.2.isLt) _
  have hR'o (a : I) (v : Fin 4) : (R' a v).order ≤ N+2 := by
    dsimp only [R']
    split_ifs
    · exact coefficientDerivative_order (by omega)
        (coefficientDerivative_order hN (hRo _ a.2.2.2.isLt) _) _ v
    · exact (coefficientDerivative_order hN (hRo _ a.2.2.2.isLt) _ v).trans (by omega)
  let loss := Finset.univ.sup (fun a : I => Finset.univ.sup (fun v : Fin 4 => (R' a v).loss))
  have hl (a : I) (v : Fin 4) : (R' a v).loss ≤ loss :=
    (Finset.le_sup (f := fun v : Fin 4 => (R' a v).loss) (Finset.mem_univ v)).trans
      (Finset.le_sup (f := fun a : I => Finset.univ.sup (fun v : Fin 4 => (R' a v).loss))
        (Finset.mem_univ a))
  refine ⟨loss,?_⟩
  intro B hB
  obtain ⟨D,hD,hd⟩ := compact_finite_fast_bound (S := S) hO hQ hQO R' hR's (N+2) loss hR'o hl ℓ 0 B hB
  refine ⟨D,hD,?_⟩
  intro G s z hz hzs hs1 hG hGQ hb U hrep i hi k j p hp
  have hGO : MapsTo (lowJet G) S O := fun _ hx => hQO (hGQ hx)
  let U' : I → Family S R4 := fun a => if a.1 then
    coefficientFamilyDerivative (coefficientFamilyDerivative (U a.2.2.2) a.2.1) a.2.2.1
    else coefficientFamilyDerivative (U a.2.2.2) a.2.1
  have hrep' (a : I) : Represents G (R' a) (U' a) := by
    dsimp only [R',U']
    split_ifs
    · exact represents_coefficientDerivative hO hG hGO
        (coefficientDerivative_smooth hO (hRs _ a.2.2.2.isLt) _)
        (represents_coefficientDerivative hO hG hGO (hRs _ a.2.2.2.isLt) (hrep _ a.2.2.2.isLt) _) _
    · exact represents_coefficientDerivative hO hG hGO (hRs _ a.2.2.2.isLt) (hrep _ a.2.2.2.isLt) _
  have hh := hd G s z hz hzs hs1 hG hGQ (by simpa only [zero_add] using hb) U' hrep'
  exact ⟨(hh (false,k,j,⟨i,hi⟩)).norm_le hp,(hh (true,k,j,⟨i,hi⟩)).norm_le hp⟩

end ClosedSurfaceR4.JetPolynomial.VectorExpression

end

end OAI
