import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.QuadraticData
import OAI.Algebra.AlgebraicObstruction.FiniteCoefficients

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries
open scoped Classical
variable {R σ : Type*} [CommRing R] [Fintype σ]

theorem vanishes_mem_origin_pow {f : MvPowerSeries σ R} {n : ℕ}
    (hf : Vanishes n f) : f ∈ (originIdeal R σ)^n := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    let m : σ → σ →₀ ℕ := fun i => Finsupp.single i 1
    have hzero : ∀ e : σ →₀ ℕ, (¬ ∃ i, m i ≤ e) → coeff e f = 0 := by
      intro e he
      have hz : e = 0 := by
        ext i
        by_contra hi
        apply he
        refine ⟨i,Finsupp.single_le_iff.mpr ?_⟩
        change 1 ≤ e i
        have : e i ≠ 0 := by simpa using hi
        omega
      subst e
      apply hf
      simp
    rw [monomial_factorization m f hzero,pow_succ']
    apply Ideal.sum_mem
    intro i _
    apply Ideal.mul_mem_mul
    · exact Ideal.subset_span ⟨i,rfl⟩
    · apply ih
      apply monomialFactor_vanishes m f hf
      intro j
      simp [m]

theorem origin_pow_iff_vanishes {f : MvPowerSeries σ R} {n : ℕ} :
    f ∈ (originIdeal R σ)^n ↔ Vanishes n f :=
  ⟨origin_pow_vanishes,vanishes_mem_origin_pow⟩

end BoundaryOnly.FormalObstruction.FormalCorrection

namespace BoundaryOnly.FormalObstruction.CoefficientRing
open MvPowerSeries FormalCorrection Matrix
open scoped Classical
variable {K : Type*} [CommRing K] {d : ℕ} {n : Fin d → ℕ}

structure QuadraticWitnesses (Q : QuadraticData (R := K) (n := n)) where
  b : InternalVar n → InternalVar n → MvPowerSeries (GraphVar n) K
  pos : (Fin d × Fin d × Fin d) → InternalVar n → MvPowerSeries (GraphVar n) K
  neg : (Fin d × Fin d × Fin d) → InternalVar n → MvPowerSeries (GraphVar n) K
  graph : subst (graphCoordinates n Q.Y) (potential n Q.P) =
    ∑ c, ∑ e, b c e * restrictedGradient n Q.P Q.Y c * restrictedGradient n Q.P Q.Y e
  positive : ∀ t, slope n t.1 * slope n t.2.1 * slope n t.2.2 =
    ∑ c, pos t c * restrictedGradient n Q.P Q.Y c
  negative : ∀ t, negativeSlopeValue n Q.P Q.Y t.1 * negativeSlopeValue n Q.P Q.Y t.2.1 *
    negativeSlopeValue n Q.P Q.Y t.2.2 = ∑ c, neg t c * restrictedGradient n Q.P Q.Y c

theorem QuadraticWitnesses.exists (Q : QuadraticData (R := K) (n := n)) :
    Nonempty (QuadraticWitnesses Q) := by
  obtain ⟨b,hb⟩ := quadratic_witness (restrictedGradient n Q.P Q.Y) _ Q.graph_square
  have hp : ∀ t : Fin d × Fin d × Fin d, ∃ c : InternalVar n → MvPowerSeries (GraphVar n) K,
      ∑ e, c e * restrictedGradient n Q.P Q.Y e = slope n t.1 * slope n t.2.1 * slope n t.2.2 :=
    fun t => Ideal.mem_span_range_iff_exists_fun.mp (Q.positive_cubic t.1 t.2.1 t.2.2)
  have hn : ∀ t : Fin d × Fin d × Fin d, ∃ c : InternalVar n → MvPowerSeries (GraphVar n) K,
      ∑ e, c e * restrictedGradient n Q.P Q.Y e =
        negativeSlopeValue n Q.P Q.Y t.1 * negativeSlopeValue n Q.P Q.Y t.2.1 *
          negativeSlopeValue n Q.P Q.Y t.2.2 :=
    fun t => Ideal.mem_span_range_iff_exists_fun.mp (Q.negative_cubic t.1 t.2.1 t.2.2)
  choose p hp using hp
  choose r hr using hn
  refine ⟨⟨b,p,r,?_,fun t => (hp t).symm,fun t => (hr t).symm⟩⟩
  rw [hb]
  simp only [dotProduct,mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem subtype_series_map_injective (R : Subalgebra ℤ K) {σ : Type*} :
    Function.Injective (MvPowerSeries.map R.val.toRingHom : MvPowerSeries σ R → MvPowerSeries σ K) := by
  intro f g h
  ext e
  exact congrArg (coeff e) h

theorem QuadraticWitnesses.descend (Q : QuadraticData (R := K) (n := n)) (W : QuadraticWitnesses Q)
    (R : Subalgebra ℤ K)
    (hP : ∀ i, coefficientsIn R (Q.P i)) (hY : ∀ c, coefficientsIn R (Q.Y c))
    (hb : ∀ c e, coefficientsIn R (W.b c e))
    (hp : ∀ t c, coefficientsIn R (W.pos t c))
    (hn : ∀ t c, coefficientsIn R (W.neg t c))
    (inv : K) (hi : inv ∈ R) (hunit : (complementaryMatrix n Q.Y).det * inv = 1) :
    Nonempty (QuadraticData (R := R) (n := n)) := by
  let PR := fun i => restrictCoefficients R (Q.P i) (hP i)
  let YR := fun c => restrictCoefficients R (Q.Y c) (hY c)
  let bR := fun c e => restrictCoefficients R (W.b c e) (hb c e)
  let pR := fun t c => restrictCoefficients R (W.pos t c) (hp t c)
  let nR := fun t c => restrictCoefficients R (W.neg t c) (hn t c)
  have hPR : (fun i => map R.val.toRingHom (PR i)) = Q.P :=
    funext fun i => map_restrictCoefficients R _ _
  have hYR : (fun c => map R.val.toRingHom (YR c)) = Q.Y :=
    funext fun c => map_restrictCoefficients R _ _
  have hcenter : ∀ c, YR c ∈ originIdeal R (GraphVar n) := by
    intro c
    apply mem_origin_iff.mpr
    exact restrictCoefficients_centered R _ _ (mem_origin_iff.mp (Q.centered c))
  have hgrad : ∀ c, map R.val.toRingHom (restrictedGradient n PR YR c) =
      restrictedGradient n Q.P Q.Y c := by
    intro c
    rw [map_restrictedGradient n _ PR YR hcenter,hPR,hYR]
  have hnegative : ∀ i, map R.val.toRingHom (negativeSlopeValue n PR YR i) =
      negativeSlopeValue n Q.P Q.Y i := by
    intro i
    rw [map_negativeSlopeValue n _ PR YR hcenter,hPR,hYR]
  have hgraph : subst (graphCoordinates n YR) (potential n PR) =
      ∑ c, ∑ e, bR c e * restrictedGradient n PR YR c * restrictedGradient n PR YR e := by
    apply subtype_series_map_injective R
    rw [map_subst (graph_hasSubst n YR hcenter),map_graph,map_potential,hPR,hYR]
    simp only [map_sum,map_mul,bR,map_restrictCoefficients,hgrad,W.graph]
  refine ⟨{ P := PR
            Y := YR
            order_three := ?_
            centered := hcenter
            complementary := ?_
            graph_square := ?_
            positive_cubic := ?_
            negative_cubic := ?_ }⟩
  · intro i
    apply vanishes_mem_origin_pow
    exact restrictCoefficients_vanishes R _ _ (origin_pow_vanishes (Q.order_three i))
  · apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨inv,hi⟩,?_⟩
    apply Subtype.ext
    change R.val.toRingHom (complementaryMatrix n YR).det * inv = 1
    rw [RingHom.map_det]
    change ((complementaryMatrix n YR).map R.val.toRingHom).det * inv = 1
    rw [map_complementary,hYR]
    exact hunit
  · rw [hgraph,pow_two]
    apply Ideal.sum_mem
    intro c _
    apply Ideal.sum_mem
    intro e _
    apply Ideal.mul_mem_mul
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨c,rfl⟩)
    · exact Ideal.subset_span ⟨e,rfl⟩
  · intro i j l
    apply Ideal.mem_span_range_iff_exists_fun.mpr
    refine ⟨pR (i,j,l),?_⟩
    apply subtype_series_map_injective R
    simpa only [map_sum,map_mul,pR,map_restrictCoefficients,hgrad,slope,map_X] using
      (W.positive (i,j,l)).symm
  · intro i j l
    apply Ideal.mem_span_range_iff_exists_fun.mpr
    refine ⟨nR (i,j,l),?_⟩
    apply subtype_series_map_injective R
    simpa only [map_sum,map_mul,nR,map_restrictCoefficients,hgrad,hnegative] using
      (W.negative (i,j,l)).symm

end BoundaryOnly.FormalObstruction.CoefficientRing

namespace BoundaryOnly.FormalObstruction.CoefficientRing
open MvPowerSeries FormalCorrection
open scoped Classical
variable {K : Type*} [CommRing K] {d : ℕ} {n : Fin d → ℕ}

inductive QuadraticEntry (n : Fin d → ℕ)
  | wall : Fin d → QuadraticEntry n
  | graph : InternalVar n → QuadraticEntry n
  | quadratic : InternalVar n → InternalVar n → QuadraticEntry n
  | positive : (Fin d × Fin d × Fin d) → InternalVar n → QuadraticEntry n
  | negative : (Fin d × Fin d × Fin d) → InternalVar n → QuadraticEntry n
  deriving Fintype

def QuadraticEntry.variables : QuadraticEntry n → Type
  | .wall i => WallVar n i
  | _ => GraphVar n

instance (e : QuadraticEntry n) : Fintype e.variables := by
  cases e <;> dsimp [QuadraticEntry.variables] <;> infer_instance

def QuadraticWitnesses.entry (Q : QuadraticData (R := K) (n := n)) (W : QuadraticWitnesses Q) :
    (e : QuadraticEntry n) → MvPowerSeries e.variables K
  | .wall i => Q.P i
  | .graph c => Q.Y c
  | .quadratic c e => W.b c e
  | .positive t c => W.pos t c
  | .negative t c => W.neg t c

theorem QuadraticWitnesses.finite_ring (Q : QuadraticData (R := K) (n := n))
    (W : QuadraticWitnesses Q)
    (h : ∀ e, NonsingularPresentation (W.entry Q e)) :
    ∃ R : Subalgebra ℤ K, Algebra.FiniteType ℤ R ∧
      Nonempty (QuadraticData (R := R) (n := n)) := by
  obtain ⟨inv,hi⟩ := isUnit_iff_exists_inv.mp Q.complementary
  obtain ⟨R,hR,hc,he⟩ := finite_ring_presentations (W.entry Q) h {inv}
  refine ⟨R,hR,W.descend Q R (fun i => he (.wall i)) (fun c => he (.graph c))
    (fun c e => he (.quadratic c e)) (fun t c => he (.positive t c))
    (fun t c => he (.negative t c)) inv (hc inv (Finset.mem_singleton_self inv)) hi⟩

end BoundaryOnly.FormalObstruction.CoefficientRing

namespace BoundaryOnly.FormalObstruction.CoefficientRing
open FormalCorrection

theorem no_presented_quadratic_data {K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    {d : ℕ} (hd : 5 ≤ d) {n : Fin d → ℕ}
    (Q : QuadraticData (R := K) (n := n)) (W : QuadraticWitnesses Q)
    (h : ∀ e, NonsingularPresentation (W.entry Q e)) : False := by
  obtain ⟨R,hR,hQ⟩ := W.finite_ring Q h
  let : Algebra.FiniteType ℤ R := hR
  exact no_integral_quadratic_data R d hd n hQ
end BoundaryOnly.FormalObstruction.CoefficientRing

end

end OAI
