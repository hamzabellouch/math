import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.AlgebraicGerms

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.CoefficientRing
open MvPowerSeries FormalCorrection
open scoped Classical
variable {K : Type} [Field K] {d : ℕ} {n : Fin d → ℕ}

lemma potential_germ (P : (i : Fin d) → MvPowerSeries (WallVar n i) K)
    (hP : ∀ i, Nonempty (LocalEtaleExpansion (P i))) :
    Nonempty (LocalEtaleExpansion (potential n P)) := by
  apply germ_sum
  intro i _
  apply germ_sub
  · apply germ_subst _ (hP i)
    · intro j; cases j <;> exact germ_X _
    · intro j; cases j <;> simp [plusCoordinates]
  · apply germ_subst _ (hP i)
    · intro j; cases j
      · exact germ_zero
      · exact germ_X _
    · intro j; cases j <;> simp [minusCoordinates]

lemma graphCoordinates_germ (Y : InternalVar n → MvPowerSeries (GraphVar n) K)
    (hY : ∀ c, Nonempty (LocalEtaleExpansion (Y c))) :
    ∀ i, Nonempty (LocalEtaleExpansion (graphCoordinates n Y i)) := by
  rintro (a | c)
  · exact germ_X _
  · exact hY c

lemma graphCoordinates_constant (Q : QuadraticData (R := K) (n := n)) :
    ∀ i, constantCoeff (graphCoordinates n Q.Y i) = 0 := by
  rintro (a | c)
  · exact constantCoeff_X _
  · exact origin_constant (Q.centered c)

lemma restrictedGradient_germ (Q : QuadraticData (R := K) (n := n))
    (hP : ∀ i, Nonempty (LocalEtaleExpansion (Q.P i)))
    (hY : ∀ c, Nonempty (LocalEtaleExpansion (Q.Y c))) (c : InternalVar n) :
    Nonempty (LocalEtaleExpansion (restrictedGradient n Q.P Q.Y c)) :=
  germ_subst _ (germ_pderiv (potential_germ Q.P hP) _) (graphCoordinates_germ Q.Y hY)
    (graphCoordinates_constant Q)

lemma negativeSlopeValue_germ (Q : QuadraticData (R := K) (n := n))
    (hP : ∀ i, Nonempty (LocalEtaleExpansion (Q.P i)))
    (hY : ∀ c, Nonempty (LocalEtaleExpansion (Q.Y c))) (i : Fin d) :
    Nonempty (LocalEtaleExpansion (negativeSlopeValue n Q.P Q.Y i)) := by
  apply germ_subst _ _ (fun j ↦ hY (false,⟨i,j⟩))
    (fun j ↦ origin_constant (Q.centered (false,⟨i,j⟩)))
  apply germ_subst _ (germ_pderiv (hP i) _)
  · intro j; cases j
    · exact germ_zero
    · exact germ_X _
  · intro j; cases j <;> simp [zeroSlopes]

theorem QuadraticData.etale_witnesses (Q : QuadraticData (R := K) (n := n))
    (hP : ∀ i, Nonempty (LocalEtaleExpansion (Q.P i)))
    (hY : ∀ c, Nonempty (LocalEtaleExpansion (Q.Y c))) :
    ∃ W : QuadraticWitnesses Q,
      (∀ c e, Nonempty (LocalEtaleExpansion (W.b c e))) ∧
      (∀ t c, Nonempty (LocalEtaleExpansion (W.pos t c))) ∧
      (∀ t c, Nonempty (LocalEtaleExpansion (W.neg t c))) := by
  have hgrad := restrictedGradient_germ Q hP hY
  have hvalue := germ_subst (graphCoordinates n Q.Y) (potential_germ Q.P hP)
    (graphCoordinates_germ Q.Y hY) (graphCoordinates_constant Q)
  obtain ⟨b,hb,hbg⟩ := germ_square_witness _ _ hgrad hvalue Q.graph_square
  have hp : ∀ t : Fin d × Fin d × Fin d,
      ∃ c : InternalVar n → MvPowerSeries (GraphVar n) K,
        slope n t.1 * slope n t.2.1 * slope n t.2.2 =
          ∑ e, c e * restrictedGradient n Q.P Q.Y e ∧
        ∀ e, Nonempty (LocalEtaleExpansion (c e)) := by
    intro t
    apply germ_span_witness _ _ hgrad
    · exact germ_mul (germ_mul (germ_X _) (germ_X _)) (germ_X _)
    · exact Q.positive_cubic t.1 t.2.1 t.2.2
  have hn : ∀ t : Fin d × Fin d × Fin d,
      ∃ c : InternalVar n → MvPowerSeries (GraphVar n) K,
        negativeSlopeValue n Q.P Q.Y t.1 * negativeSlopeValue n Q.P Q.Y t.2.1 *
          negativeSlopeValue n Q.P Q.Y t.2.2 =
          ∑ e, c e * restrictedGradient n Q.P Q.Y e ∧
        ∀ e, Nonempty (LocalEtaleExpansion (c e)) := by
    intro t
    apply germ_span_witness _ _ hgrad
    · exact germ_mul (germ_mul (negativeSlopeValue_germ Q hP hY _)
        (negativeSlopeValue_germ Q hP hY _)) (negativeSlopeValue_germ Q hP hY _)
    · exact Q.negative_cubic t.1 t.2.1 t.2.2
  choose p hp hpg using hp
  choose r hr hrg using hn
  exact ⟨⟨b,p,r,hb,hp,hr⟩,hbg,hpg,hrg⟩

end BoundaryOnly.FormalObstruction.CoefficientRing

namespace BoundaryOnly.FormalObstruction.CoefficientRing
open MvPowerSeries FormalCorrection
open scoped Classical
variable {K : Type} [Field K] [CharZero K] {d : ℕ} {n : Fin d → ℕ}

theorem no_algebraic_quadratic_data (hd : 5 ≤ d)
    (Q : QuadraticData (R := K) (n := n))
    (hP : ∀ i, Nonempty (LocalEtaleExpansion (Q.P i)))
    (hY : ∀ c, Nonempty (LocalEtaleExpansion (Q.Y c))) : False := by
  obtain ⟨W,hb,hpos,hneg⟩ := Q.etale_witnesses hP hY
  apply no_etale_quadratic_data hd Q W
  intro e
  cases e with
  | wall i => exact (hP i).some
  | graph c => exact (hY c).some
  | quadratic c e => exact (hb c e).some
  | positive t c => exact (hpos t c).some
  | negative t c => exact (hneg t c).some

end BoundaryOnly.FormalObstruction.CoefficientRing

end

end OAI
