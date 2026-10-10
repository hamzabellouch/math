import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.Specialization
import OAI.Algebra.AlgebraicObstruction.IdealVanishing

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.CoefficientRing
open MvPowerSeries Matrix FormalCorrection
open scoped Classical
variable {R : Type*} [CommRing R] {d : ℕ} {n : Fin d → ℕ}

 theorem plusCoordinates_centered (i : Fin d) :
    ∀ j, constantCoeff (plusCoordinates (k := R) n i j) = 0 := by
  intro j; cases j <;> simp [plusCoordinates]
 theorem minusCoordinates_centered (i : Fin d) :
    ∀ j, constantCoeff (minusCoordinates (k := R) n i j) = 0 := by
  intro j; cases j <;> simp [minusCoordinates]

 theorem potential_vanishes (P : (i : Fin d) → MvPowerSeries (WallVar n i) R)
    (hP : ∀ i, P i ∈ (originIdeal R (WallVar n i))^3) : Vanishes 3 (potential n P) := by
  apply Vanishes.sum
  intro i _
  simpa only [sub_eq_add_neg] using ((origin_pow_vanishes (hP i)).subst _ (plusCoordinates_centered i)).add
    (((origin_pow_vanishes (hP i)).subst _ (minusCoordinates_centered i)).neg)

 theorem graphCoordinates_centered (Y : InternalVar n → MvPowerSeries (GraphVar n) R)
    (hY : ∀ c, Y c ∈ originIdeal R (GraphVar n)) :
    ∀ i, constantCoeff (graphCoordinates n Y i) = 0 := by
  intro i
  cases i with
  | inl a => exact constantCoeff_X _
  | inr c => exact mem_origin_iff.mp (hY c)

 def correctedGraph (Y : InternalVar n → MvPowerSeries (GraphVar n) R)
    (δ : InternalVar n → MvPowerSeries (GraphVar n) R) := fun c => Y c + δ c

 theorem graph_corrected (Y : InternalVar n → MvPowerSeries (GraphVar n) R)
    (δ : InternalVar n → MvPowerSeries (GraphVar n) R) :
    graphCoordinates n (correctedGraph Y δ) = shiftedGraph (graphCoordinates n Y) δ := by
  funext i
  cases i <;> rfl

 def negativeAmbient (P : (i : Fin d) → MvPowerSeries (WallVar n i) R) (i : Fin d) :
    MvPowerSeries (AmbientVar n) R :=
  subst (fun j => (X (.inr (false,⟨i,j⟩)) : MvPowerSeries (AmbientVar n) R)) (slopeDerivative n P i)

 theorem subst_negativeAmbient (P : (i : Fin d) → MvPowerSeries (WallVar n i) R)
    (Y : InternalVar n → MvPowerSeries (GraphVar n) R)
    (hY : ∀ c, Y c ∈ originIdeal R (GraphVar n)) (i : Fin d) :
    subst (graphCoordinates n Y) (negativeAmbient P i) = negativeSlopeValue n P Y i := by
  let hx := hasSubst_of_constantCoeff_zero (graphCoordinates_centered Y hY)
  let hi := hasSubst_of_constantCoeff_zero (fun j : Fin (n i) =>
    constantCoeff_X (R := R) (Sum.inr (false,⟨i,j⟩) : AmbientVar n))
  rw [negativeAmbient, subst_comp_subst_apply hi hx]
  simp only [subst_X hx, graphCoordinates, negativeSlopeValue]

 theorem complementaryMatrix_jet
    (Y Z : InternalVar n → MvPowerSeries (GraphVar n) R)
    (h : ∀ c, Jet 2 (Z c) (Y c)) : complementaryMatrix n Z = complementaryMatrix n Y := by
  ext c bt
  unfold complementaryMatrix tangentMatrix
  split_ifs <;> exact Jet.pderiv_constant (h _) _

structure QuadraticData where
  P : (i : Fin d) → MvPowerSeries (WallVar n i) R
  Y : InternalVar n → MvPowerSeries (GraphVar n) R
  order_three : ∀ i, P i ∈ (originIdeal R (WallVar n i))^3
  centered : ∀ c, Y c ∈ originIdeal R (GraphVar n)
  complementary : IsUnit (complementaryMatrix n Y).det
  graph_square : subst (graphCoordinates n Y) (potential n P) ∈ (gradientIdeal n P Y)^2
  positive_cubic : ∀ i j l : Fin d,
    slope n i * slope n j * slope n l ∈ gradientIdeal n P Y
  negative_cubic : ∀ i j l : Fin d,
    negativeSlopeValue n P Y i * negativeSlopeValue n P Y j *
      negativeSlopeValue n P Y l ∈ gradientIdeal n P Y

 theorem QuadraticData.correct (Q : QuadraticData (R := R) (n := n)) :
    ∃ D : FormalData (k := R) n, D.P = Q.P ∧
      (∀ c, Jet 2 (D.Y c) (Q.Y c)) := by
  let f := potential n Q.P
  let x := graphCoordinates n Q.Y
  let v := gradientValue f x
  have hf : Vanishes 3 f := potential_vanishes Q.P Q.order_three
  have hx : ∀ i, constantCoeff (x i) = 0 := graphCoordinates_centered Q.Y Q.centered
  have hv : ∀ c, Vanishes 2 (v c) := gradientValue_vanishes f hf x hx
  have hid : vectorIdeal v = gradientIdeal n Q.P Q.Y := rfl
  obtain ⟨b,hb⟩ := quadratic_witness v (subst x f) (hid ▸ Q.graph_square)
  obtain ⟨B,hzero,hjet⟩ := exists_zero_correction f hf x hx b hb
  let Z := correctedGraph Q.Y (B *ᵥ v)
  have hZjet : ∀ c, Jet 2 (Z c) (Q.Y c) := fun c => hjet (.inr c)
  have hZ : ∀ c, Z c ∈ originIdeal R (GraphVar n) := by
    intro c
    apply mem_origin_iff.mpr
    have hh := (hZjet c).mono (by omega : 1 ≤ 2)
    have hh' := Vanishes.one_iff.mp hh
    simp only [map_sub, mem_origin_iff.mp (Q.centered c), sub_zero] at hh'
    exact hh'
  have hgrad : gradientIdeal n Q.P Z = gradientIdeal n Q.P Q.Y := by
    change vectorIdeal (gradientValue f (graphCoordinates n Z)) = vectorIdeal v
    rw [graph_corrected]
    exact gradient_ideal_transport f hf x hx B
  have hdiff : ∀ i, negativeSlopeValue n Q.P Z i - negativeSlopeValue n Q.P Q.Y i ∈
      gradientIdeal n Q.P Q.Y := by
    intro i
    rw [← subst_negativeAmbient Q.P Z hZ, ← subst_negativeAmbient Q.P Q.Y Q.centered, graph_corrected]
    exact scalar_transport_mem (negativeAmbient Q.P i) x hx v hv B
  refine ⟨⟨Q.P, Z, Q.order_three, hZ, ?_, ?_, ?_, ?_⟩, rfl, hZjet⟩
  · rw [complementaryMatrix_jet Q.Y Z hZjet]
    exact Q.complementary
  · rw [graph_corrected]
    exact hzero
  · intro i j l
    rw [hgrad]
    exact Q.positive_cubic i j l
  · intro i j l
    rw [hgrad]
    exact triple_transport_mem _ (hdiff i) (hdiff j) (hdiff l) (Q.negative_cubic i j l)

end BoundaryOnly.FormalObstruction.CoefficientRing
namespace BoundaryOnly.FormalObstruction.CoefficientRing

theorem no_integral_quadratic_data (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    [Algebra.FiniteType ℤ R] (d : ℕ) (hd : 5 ≤ d) (n : Fin d → ℕ) :
    ¬ Nonempty (QuadraticData (R := R) (n := n)) := by
  rintro ⟨Q⟩
  obtain ⟨D,_,_⟩ := Q.correct
  exact no_integral_formal_data R d hd n ⟨D⟩
end BoundaryOnly.FormalObstruction.CoefficientRing

end

end OAI
