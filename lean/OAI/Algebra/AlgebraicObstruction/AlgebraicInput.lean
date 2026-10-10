import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.AlgebraicData
import OAI.Algebra.AlgebraicObstruction.RadicalPrimitives
import OAI.Algebra.AlgebraicObstruction.PotentialReplacement

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart
open MvPowerSeries
variable {K α : Type} [Field K] [CharZero K] [IsAlgClosed K] [Finite α]

omit [CharZero K] [IsAlgClosed K] in
lemma completion_map_ideal [CharZero K] [IsAlgClosed K]
    (E : AffineEtaleChart K α) (L : Ideal E.LocalRing) :
    (L.map (algebraMap E.LocalRing
      (AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing))).map
      E.completionEquiv.toRingHom = L.map E.localExpansion.toRingHom := by
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro a
  exact E.completionEquiv_of a

lemma completion_mem_iff (E : AffineEtaleChart K α) (L : Ideal E.LocalRing)
    (b : AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing) :
    E.completionEquiv b ∈ L.map E.localExpansion.toRingHom ↔
    b ∈ L.map (algebraMap E.LocalRing
      (AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing)) := by
  rw [← E.completion_map_ideal L]
  exact Ideal.apply_mem_of_equiv_iff

theorem primitive_series_approximation (E : AffineEtaleChart K α) (L : Ideal E.LocalRing)
    (P : MvPowerSeries α K)
    (hgrad : ∀ j : α, pderiv (R := K) j P ∈ L.map E.localExpansion.toRingHom)
    (hjets : ∀ j : α, ∀ q : ℕ, 1 ≤ q → ∃ a : E.LocalRing,
      pderiv (R := K) j P - E.localExpansion a ∈ (L.map E.localExpansion.toRingHom)^q)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ a : E.LocalRing, P - E.localExpansion a ∈ (L.map E.localExpansion.toRingHom)^m := by
  let b := E.completionEquiv.symm P
  have hb : E.completionEquiv b = P := E.completionEquiv.apply_symm_apply P
  have hd (j : α) : E.completionEquiv (E.completionDeriv j b) = pderiv (R := K) j P := by
    change E.completionEquiv (E.completionEquiv.symm (pderiv (R := K) j (E.completionEquiv b))) = _
    rw [E.completionEquiv.apply_symm_apply,hb]
  obtain ⟨a,ha⟩ := E.primitive_approximation L b (fun j ↦
    (E.completion_mem_iff L _).mp (by rw [hd]; exact hgrad j)) (by
      intro j q hq
      obtain ⟨a,ha⟩ := hjets j q hq
      refine ⟨a,?_⟩
      rw [← Ideal.map_pow]
      apply (E.completion_mem_iff (L^q) _).mp
      rw [map_sub,hd,E.completionEquiv_of,Ideal.map_pow]
      exact ha) m hm
  refine ⟨a,?_⟩
  have h := (E.completion_mem_iff (L^m) _).mpr ha
  rwa [map_sub,hb,E.completionEquiv_of,Ideal.map_pow] at h

end BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart

namespace BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart
open MvPowerSeries
variable {K α : Type} [Field K] [CharZero K] [IsAlgClosed K] [Finite α]

omit [CharZero K] [IsAlgClosed K] in
lemma ideal_map_origin [CharZero K] [IsAlgClosed K]
    (E : AffineEtaleChart K α) (L : Ideal E.LocalRing)
    (hL : L ≤ IsLocalRing.maximalIdeal E.LocalRing) :
    L.map E.localExpansion.toRingHom ≤ originIdeal K α := by
  classical
  let := Fintype.ofFinite α
  apply Ideal.map_le_iff_le_comap.mpr
  intro a ha
  apply mem_origin_iff.mpr
  by_contra hn
  have hu : IsUnit (E.localExpansion a) := MvPowerSeries.isUnit_iff_constantCoeff.mpr
    (isUnit_iff_ne_zero.mpr hn)
  exact (hL ha) (isUnit_of_map_unit E.localExpansion a hu)

end BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart

namespace BoundaryOnly.FormalObstruction.CoefficientRing
open MvPowerSeries FormalCorrection AlgebraicReplacement
open scoped Classical
variable {K : Type} [Field K] [CharZero K] [IsAlgClosed K] {d : ℕ} {n : Fin d → ℕ}

theorem no_algebraic_input (hd : 5 ≤ d)
    (Q : QuadraticData (R := K) (n := n))
    (E : (i : Fin d) → AffineEtaleChart K (WallVar n i))
    (L : (i : Fin d) → Ideal (E i).LocalRing)
    (hL : ∀ i, L i ≤ IsLocalRing.maximalIdeal (E i).LocalRing)
    (hgradient : ∀ i w, pderiv (R := K) w (Q.P i) ∈ (L i).map (E i).localExpansion.toRingHom)
    (hjets : ∀ i w, ∀ q : ℕ, 1 ≤ q → ∃ a : (E i).LocalRing,
      pderiv (R := K) w (Q.P i) - (E i).localExpansion a ∈
        ((L i).map (E i).localExpansion.toRingHom)^q)
    (hpulled : ∀ b i, Ideal.map (wallEval Q.Y Q.centered b i)
      ((L i).map (E i).localExpansion.toRingHom) ≤ originIdeal K (GraphVar n))
    (hcube : ∀ b i, (Ideal.map (wallEval Q.Y Q.centered b i)
      ((L i).map (E i).localExpansion.toRingHom))^3 ≤ gradientIdeal n Q.P Q.Y)
    (hY : ∀ c, Nonempty (LocalEtaleExpansion (Q.Y c))) : False := by
  have happ (i : Fin d) := (E i).primitive_series_approximation (L i) (Q.P i)
    (hgradient i) (hjets i) 9 (by omega)
  choose a ha using happ
  let P := fun i ↦ (E i).localExpansion (a i)
  let W := fun i ↦ (L i).map (E i).localExpansion.toRingHom
  have hW (i : Fin d) : W i ≤ originIdeal K (WallVar n i) :=
    (E i).ideal_map_origin (L i) (hL i)
  have hP (i : Fin d) : P i - Q.P i ∈ (W i)^9 := by
    simpa only [neg_sub] using ((W i)^9).neg_mem (ha i)
  let T : QuadraticData (R := K) (n := n) := Q.replace W hW hpulled hcube P hP
  apply no_algebraic_quadratic_data hd T
  · intro i
    exact ⟨(E i).localGerm (a i)⟩
  · exact hY

end BoundaryOnly.FormalObstruction.CoefficientRing

end

end OAI
