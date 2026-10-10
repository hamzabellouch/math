import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.RepulsionBound
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.BoundedFormCross
import Mathlib.Algebra.Order.Chebyshev
import OAI.Analysis.CoulombRadii.FieldAnalysis.ConfigurationMeasurableEquiv

namespace OAI

/-! The actual Coulomb interaction has a polynomial mixed-form bound.
The multiplier acts on full spinful H1 states and takes values in L2. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def repulsionMultiplier {n : ℕ} (u : Coulomb.H1Vector n) (s : SpinConfiguration n) :
    Lp ℂ 2 (volume : Measure (Configuration n)) :=
  (repulsion_mul_memLp u s).toLp (fun x => (repulsionPotential x:ℂ)*u.value s x)

def repulsionCross {n : ℕ} (u v : Coulomb.H1Vector n) : ℝ :=
  ∑ s, inner ℝ (repulsionMultiplier u s) (h1Coordinates v (Sum.inl s))

theorem repulsionMultiplier_norm_sq {n : ℕ} (u : Coulomb.H1Vector n) (s : SpinConfiguration n) :
    ‖repulsionMultiplier u s‖^2 = ∫ x, ‖(repulsionPotential x:ℂ)*u.value s x‖^2 :=
  Coulomb.norm_toLp_sq_complex (repulsion_mul_memLp u s)

theorem repulsionCross_square_bound {n : ℕ} (u v : Coulomb.H1Vector n) :
    (repulsionCross u v)^2 ≤ 8*(n:ℝ)^3*Coulomb.kinetic u*Coulomb.mass v := by
  have ha : |repulsionCross u v| ≤
      ∑ s, ‖repulsionMultiplier u s‖*‖h1Coordinates v (Sum.inl s)‖ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum (fun s _ => abs_real_inner_le_norm _ _)
  have hq : (repulsionCross u v)^2 ≤
      (∑ s, ‖repulsionMultiplier u s‖^2)*(∑ s, ‖h1Coordinates v (Sum.inl s)‖^2) := by
    calc
      _ = |repulsionCross u v|^2 := (sq_abs _).symm
      _ ≤ (∑ s, ‖repulsionMultiplier u s‖*‖h1Coordinates v (Sum.inl s)‖)^2 :=
        pow_le_pow_left₀ (abs_nonneg _) ha 2
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hb : (∑ s, ‖h1Coordinates v (Sum.inl s)‖^2) = Coulomb.mass v := by
    simp only [h1Coordinates_norm_sq,h1CoordinateFunction,Coulomb.mass]
  rw [hb] at hq
  apply hq.trans
  apply mul_le_mul_of_nonneg_right _ (Coulomb.mass_nonneg v)
  simpa only [repulsionMultiplier_norm_sq] using repulsion_mul_norm_bound u

theorem repulsionCross_integral {n : ℕ} (u v : Coulomb.H1Vector n) :
    repulsionCross u v = ∑ s, ∫ x, repulsionPotential x * inner ℝ (u.value s x) (v.value s x) := by
  unfold repulsionCross
  apply Finset.sum_congr rfl
  intro s _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(repulsion_mul_memLp u s).coeFn_toLp,
    (h1Coordinate_memLp v (Sum.inl s)).coeFn_toLp] with x hu hv
  change repulsionMultiplier u s x = (repulsionPotential x:ℂ)*u.value s x at hu
  change h1Coordinates v (Sum.inl s) x = v.value s x at hv
  rw [hu,hv,← Complex.real_smul,real_inner_smul_left]

theorem repulsionCross_comm {n : ℕ} (u v : Coulomb.H1Vector n) :
    repulsionCross u v = repulsionCross v u := by
  rw [repulsionCross_integral,repulsionCross_integral]
  simp only [real_inner_comm]

theorem pairEnergy_eq_repulsionCross {n : ℕ} (u : Coulomb.H1Vector n) :
    Coulomb.pairEnergy u = repulsionCross u u := by
  rw [repulsionCross_integral]
  simp only [Coulomb.pairEnergy,repulsionPotential,pairRepulsionTerm,
    Fintype.sum_prod_type,real_inner_self_eq_norm_sq]

theorem repulsionMultiplier_add {n : ℕ} (u v : Coulomb.H1Vector n) (s : SpinConfiguration n) :
    repulsionMultiplier (u.add v) s = repulsionMultiplier u s+repulsionMultiplier v s := by
  apply Lp.ext
  filter_upwards [(repulsion_mul_memLp (u.add v) s).coeFn_toLp,
    (repulsion_mul_memLp u s).coeFn_toLp,(repulsion_mul_memLp v s).coeFn_toLp,
    Lp.coeFn_add (repulsionMultiplier u s) (repulsionMultiplier v s)] with x huv hu hv ha
  change repulsionMultiplier (u.add v) s x = _ at huv
  change repulsionMultiplier u s x = _ at hu
  change repulsionMultiplier v s x = _ at hv
  rw [ha]
  simp only [Pi.add_apply]
  rw [hu,hv,huv]
  change (repulsionPotential x:ℂ)*(u.value s x+v.value s x) = _
  exact mul_add _ _ _

theorem pairEnergy_add {n : ℕ} (u v : Coulomb.H1Vector n) :
    Coulomb.pairEnergy (u.add v) = Coulomb.pairEnergy u+Coulomb.pairEnergy v+
      2*repulsionCross u v := by
  simp only [pairEnergy_eq_repulsionCross,repulsionCross,repulsionMultiplier_add,
    h1Coordinates_add,Pi.add_apply,inner_add_left,inner_add_right,Finset.sum_add_distrib]
  have h := repulsionCross_comm u v
  unfold repulsionCross at h
  linarith

end ContinuumCoulomb

end

end OAI
