import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.IdealBounds

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.CoefficientRing
open MvPowerSeries FormalCorrection AlgebraicReplacement
open scoped Classical
variable {R : Type*} [CommRing R] {d : ℕ} {n : Fin d → ℕ}

def wallCoordinates (b : Bool) (i : Fin d) : WallVar n i → MvPowerSeries (AmbientVar n) R :=
  if b then plusCoordinates n i else minusCoordinates n i

theorem wallCoordinates_centered (b : Bool) (i : Fin d) :
    ∀ w, constantCoeff (wallCoordinates (R := R) (n := n) b i w) = 0 := by
  cases b
  · exact minusCoordinates_centered i
  · exact plusCoordinates_centered i

def wallEval (Y : InternalVar n → MvPowerSeries (GraphVar n) R)
    (hY : ∀ c, Y c ∈ originIdeal R (GraphVar n)) (b : Bool) (i : Fin d) :
    MvPowerSeries (WallVar n i) R →ₐ[R] MvPowerSeries (GraphVar n) R :=
  (substAlgHom (hasSubst_of_constantCoeff_zero (graphCoordinates_centered Y hY))).comp
    (substAlgHom (hasSubst_of_constantCoeff_zero (wallCoordinates_centered b i)))

theorem subst_potential_eq_sum (P : (i : Fin d) → MvPowerSeries (WallVar n i) R)
    (Y : InternalVar n → MvPowerSeries (GraphVar n) R)
    (hY : ∀ c, Y c ∈ originIdeal R (GraphVar n)) :
    subst (graphCoordinates n Y) (potential n P) =
      ∑ i, (wallEval Y hY true i (P i) - wallEval Y hY false i (P i)) := by
  rw [← substAlgHom_apply (hasSubst_of_constantCoeff_zero (graphCoordinates_centered Y hY))]
  simp only [potential, map_sum, map_sub]
  apply Finset.sum_congr rfl
  intro i _
  simp [wallEval, wallCoordinates, AlgHom.comp_apply, substAlgHom_apply]

theorem wallEval_negativeSlope (P : (i : Fin d) → MvPowerSeries (WallVar n i) R)
    (Y : InternalVar n → MvPowerSeries (GraphVar n) R)
    (hY : ∀ c, Y c ∈ originIdeal R (GraphVar n)) (i : Fin d) :
    negativeSlopeValue n P Y i = wallEval Y hY false i (pderiv (.inl 0) (P i)) := by
  have hz : ∀ w : WallVar n i, constantCoeff (zeroSlopes (k := R) n i w) = 0 := by
    intro w; cases w <;> simp [zeroSlopes]
  have hminus : ∀ j : Fin (n i), constantCoeff (Y (false,⟨i,j⟩)) = 0 :=
    fun j => mem_origin_iff.mp (hY _)
  simp only [wallEval, AlgHom.comp_apply, substAlgHom_apply, wallCoordinates, Bool.false_eq_true, ite_false]
  change subst (fun j => Y (false,⟨i,j⟩))
      (subst (zeroSlopes (k := R) n i) (pderiv (.inl 0) (P i))) =
    subst (graphCoordinates n Y)
      (subst (minusCoordinates (k := R) n i) (pderiv (.inl 0) (P i)))
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hz)
      (hasSubst_of_constantCoeff_zero hminus),
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (minusCoordinates_centered i))
      (hasSubst_of_constantCoeff_zero (graphCoordinates_centered Y hY))]
  congr 1
  funext w
  cases w with
  | inl a =>
    simp only [zeroSlopes, minusCoordinates,
      ← substAlgHom_apply (hasSubst_of_constantCoeff_zero hminus),
      ← substAlgHom_apply (hasSubst_of_constantCoeff_zero (graphCoordinates_centered Y hY)), map_zero]
  | inr j =>
    simp only [zeroSlopes, minusCoordinates,
      subst_X (hasSubst_of_constantCoeff_zero hminus),
      subst_X (hasSubst_of_constantCoeff_zero (graphCoordinates_centered Y hY)), graphCoordinates]

theorem origin_le_jacobson {σ : Type*} [Fintype σ] :
    originIdeal R σ ≤ Ideal.jacobson ⊥ := by
  intro f hf
  apply Ideal.mem_jacobson_bot.mpr
  intro g
  apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
  simp [mem_origin_iff.mp hf]

theorem wall_error_bounds
    (Y : InternalVar n → MvPowerSeries (GraphVar n) R)
    (hY : ∀ c, Y c ∈ originIdeal R (GraphVar n))
    (K : (i : Fin d) → Ideal (MvPowerSeries (WallVar n i) R))
    (r : Ideal (MvPowerSeries (GraphVar n) R))
    (hL : ∀ b i, Ideal.map (wallEval Y hY b i) (K i) ≤ originIdeal R (GraphVar n))
    (hcube : ∀ b i, (Ideal.map (wallEval Y hY b i) (K i))^3 ≤ r)
    (E : (i : Fin d) → MvPowerSeries (WallVar n i) R)
    (hE : ∀ i, E i ∈ (K i)^9) :
    (∀ b i, wallEval Y hY b i (E i) ∈ r^3) ∧
    (∀ b i w, wallEval Y hY b i (pderiv w (E i)) ∈ originIdeal R (GraphVar n) * r) := by
  constructor
  · intro b i
    have h := Ideal.mem_map_of_mem (wallEval Y hY b i) (hE i)
    rw [Ideal.map_pow] at h
    exact (ninth_order_bounds _ _ _ (hL b i) (hcube b i)).1 h
  · intro b i w
    have hd := derivation_mem_pow (pderiv w) (K i) 8 (hE i)
    have h := Ideal.mem_map_of_mem (wallEval Y hY b i) hd
    rw [Ideal.map_pow] at h
    exact eighth_le_mul _ _ ((ninth_order_bounds _ _ _ (hL b i) (hcube b i)).2 h)

theorem wall_ambient_derivative_mem
    (Y : InternalVar n → MvPowerSeries (GraphVar n) R)
    (hY : ∀ c, Y c ∈ originIdeal R (GraphVar n))
    (I : Ideal (MvPowerSeries (GraphVar n) R)) (b : Bool) (i : Fin d)
    (E : MvPowerSeries (WallVar n i) R)
    (hE : ∀ w, wallEval Y hY b i (pderiv w E) ∈ I) (c : AmbientVar n) :
    subst (graphCoordinates n Y) (pderiv (R := R) c (subst (wallCoordinates b i) E)) ∈ I := by
  rw [pderiv_subst _ (wallCoordinates_centered b i)]
  rw [← substAlgHom_apply (hasSubst_of_constantCoeff_zero (graphCoordinates_centered Y hY))]
  rw [map_sum]
  apply Ideal.sum_mem
  intro w _
  rw [map_mul]
  have hw := hE w
  simp only [wallEval, AlgHom.comp_apply, substAlgHom_apply] at hw
  simp only [substAlgHom_apply]
  exact I.mul_mem_right _ hw

end BoundaryOnly.FormalObstruction.CoefficientRing

namespace BoundaryOnly.FormalObstruction.CoefficientRing
open MvPowerSeries FormalCorrection AlgebraicReplacement
open scoped Classical
variable {R : Type*} [CommRing R] {d : ℕ} {n : Fin d → ℕ}

theorem potential_sub (P Q : (i : Fin d) → MvPowerSeries (WallVar n i) R) :
    potential n (fun i => P i - Q i) = potential n P - potential n Q := by
  unfold potential
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [← substAlgHom_apply (hasSubst_of_constantCoeff_zero (plusCoordinates_centered i)),
    ← substAlgHom_apply (hasSubst_of_constantCoeff_zero (minusCoordinates_centered i)), map_sub]
  ring

theorem gradient_sub (P Q : (i : Fin d) → MvPowerSeries (WallVar n i) R)
    (Y : InternalVar n → MvPowerSeries (GraphVar n) R)
    (hY : ∀ c, Y c ∈ originIdeal R (GraphVar n)) (c : InternalVar n) :
    restrictedGradient n (fun i => P i - Q i) Y c =
      restrictedGradient n P Y c - restrictedGradient n Q Y c := by
  unfold restrictedGradient
  rw [potential_sub, map_sub]
  exact (substAlgHom_apply (hasSubst_of_constantCoeff_zero (graphCoordinates_centered Y hY)) _).symm.trans
    ((map_sub (substAlgHom (R := R) (S := R) (hasSubst_of_constantCoeff_zero (graphCoordinates_centered Y hY))) _ _).trans (by simp only [substAlgHom_apply]))

theorem gradient_mem_of_wall_derivatives
    (E : (i : Fin d) → MvPowerSeries (WallVar n i) R)
    (Y : InternalVar n → MvPowerSeries (GraphVar n) R)
    (hY : ∀ c, Y c ∈ originIdeal R (GraphVar n))
    (I : Ideal (MvPowerSeries (GraphVar n) R))
    (hE : ∀ b i w, wallEval Y hY b i (pderiv w (E i)) ∈ I)
    (c : InternalVar n) : restrictedGradient n E Y c ∈ I := by
  unfold restrictedGradient potential
  rw [map_sum]
  rw [← substAlgHom_apply (hasSubst_of_constantCoeff_zero (graphCoordinates_centered Y hY))]
  rw [map_sum]
  apply Ideal.sum_mem
  intro i _
  rw [map_sub, map_sub]
  simp only [substAlgHom_apply]
  exact I.sub_mem (wall_ambient_derivative_mem Y hY I true i (E i) (hE true i) _)
    (wall_ambient_derivative_mem Y hY I false i (E i) (hE false i) _)

def QuadraticData.replace (Q : QuadraticData (R := R) (n := n))
    (K : (i : Fin d) → Ideal (MvPowerSeries (WallVar n i) R))
    (hK : ∀ i, K i ≤ originIdeal R (WallVar n i))
    (hL : ∀ b i, Ideal.map (wallEval Q.Y Q.centered b i) (K i) ≤ originIdeal R (GraphVar n))
    (hcube : ∀ b i, (Ideal.map (wallEval Q.Y Q.centered b i) (K i))^3 ≤ gradientIdeal n Q.P Q.Y)
    (P : (i : Fin d) → MvPowerSeries (WallVar n i) R)
    (hP : ∀ i, P i - Q.P i ∈ (K i)^9) : QuadraticData (R := R) (n := n) := by
  let E := fun i => P i - Q.P i
  let r := gradientIdeal n Q.P Q.Y
  let m := originIdeal R (GraphVar n)
  have hbounds := wall_error_bounds Q.Y Q.centered K r hL hcube E hP
  have hvalue := hbounds.1
  have hderiv := hbounds.2
  have hgrad : gradientIdeal n P Q.Y = r := by
    apply span_eq_of_generator_congruence m origin_le_jacobson
    intro c
    rw [← gradient_sub P Q.P Q.Y Q.centered c]
    exact gradient_mem_of_wall_derivatives E Q.Y Q.centered (m*r) hderiv c
  have hval : subst (graphCoordinates n Q.Y) (potential n P) -
      subst (graphCoordinates n Q.Y) (potential n Q.P) ∈ r^3 := by
    simp only [← substAlgHom_apply (hasSubst_of_constantCoeff_zero
      (graphCoordinates_centered Q.Y Q.centered)), ← map_sub]
    rw [substAlgHom_apply, ← potential_sub,
      subst_potential_eq_sum _ _ Q.centered]
    apply Ideal.sum_mem
    intro i _
    exact (r^3).sub_mem (hvalue true i) (hvalue false i)
  have hneg : ∀ i, negativeSlopeValue n P Q.Y i - negativeSlopeValue n Q.P Q.Y i ∈ r := by
    intro i
    rw [wallEval_negativeSlope _ _ Q.centered, wallEval_negativeSlope _ _ Q.centered,
      ← map_sub, ← map_sub]
    exact (show m * r ≤ r from Ideal.mul_le_right) (hderiv false i (.inl 0))
  refine ⟨P, Q.Y, ?_, Q.centered, Q.complementary, ?_, ?_, ?_⟩
  · intro i
    have he : E i ∈ (originIdeal R (WallVar n i))^3 :=
      Ideal.pow_le_pow_right (by omega : 3 ≤ 9) ((pow_le_pow_left' (hK i) 9) (hP i))
    simpa only [E, sub_add_cancel] using (originIdeal R (WallVar n i)^3).add_mem he (Q.order_three i)
  · rw [hgrad]
    have hh := (r^2).add_mem (Ideal.pow_le_pow_right (by omega : 2 ≤ 3) hval) Q.graph_square
    simpa only [sub_add_cancel] using hh
  · intro i j l
    rw [hgrad]
    exact Q.positive_cubic i j l
  · intro i j l
    rw [hgrad]
    exact triple_transport_mem r (hneg i) (hneg j) (hneg l) (Q.negative_cubic i j l)

end BoundaryOnly.FormalObstruction.CoefficientRing

end

end OAI
