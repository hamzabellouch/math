import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.NuclearMultiplier

namespace OAI

/-! Polarization of the actual unit-nucleus potential on weak-H1 states. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def pointChargeMultiplier {m n : ℕ} (R : Fin m → Position)
    (u : Coulomb.H1Vector n) (s : SpinConfiguration n) :
    Lp ℂ 2 (volume : Measure (Configuration n)) :=
  (pointChargePotential_mul_memLp R u s).toLp (fun x => (pointChargePotential R x:ℂ)*u.value s x)

def pointChargeCross {m n : ℕ} (R : Fin m → Position) (u v : Coulomb.H1Vector n) : ℝ :=
  ∑ s, inner ℝ (pointChargeMultiplier R u s) (h1Coordinates v (Sum.inl s))

def pointChargeEnergy {m n : ℕ} (R : Fin m → Position) (u : Coulomb.H1Vector n) : ℝ :=
  ∑ s, ∫ x, pointChargePotential R x*‖u.value s x‖^2

theorem pointChargeMultiplier_norm_sq {m n : ℕ} (R : Fin m → Position)
    (u : Coulomb.H1Vector n) (s : SpinConfiguration n) :
    ‖pointChargeMultiplier R u s‖^2 = ∫ x, ‖(pointChargePotential R x:ℂ)*u.value s x‖^2 :=
  Coulomb.norm_toLp_sq_complex (pointChargePotential_mul_memLp R u s)

theorem pointChargeCross_square_bound {m n : ℕ} (R : Fin m → Position)
    (u v : Coulomb.H1Vector n) :
    (pointChargeCross R u v)^2 ≤ 8*(n:ℝ)*(m:ℝ)^2*Coulomb.kinetic u*Coulomb.mass v := by
  have ha : |pointChargeCross R u v| ≤
      ∑ s, ‖pointChargeMultiplier R u s‖*‖h1Coordinates v (Sum.inl s)‖ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum (fun s _ => abs_real_inner_le_norm _ _)
  have hq : (pointChargeCross R u v)^2 ≤
      (∑ s, ‖pointChargeMultiplier R u s‖^2)*(∑ s, ‖h1Coordinates v (Sum.inl s)‖^2) := by
    calc
      _ = |pointChargeCross R u v|^2 := (sq_abs _).symm
      _ ≤ (∑ s, ‖pointChargeMultiplier R u s‖*‖h1Coordinates v (Sum.inl s)‖)^2 :=
        pow_le_pow_left₀ (abs_nonneg _) ha 2
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hb : (∑ s, ‖h1Coordinates v (Sum.inl s)‖^2) = Coulomb.mass v := by
    simp only [h1Coordinates_norm_sq,h1CoordinateFunction,Coulomb.mass]
  rw [hb] at hq
  apply hq.trans
  apply mul_le_mul_of_nonneg_right _ (Coulomb.mass_nonneg v)
  simpa only [pointChargeMultiplier_norm_sq] using pointChargePotential_mul_norm_bound R u

theorem pointChargeCross_integral {m n : ℕ} (R : Fin m → Position)
    (u v : Coulomb.H1Vector n) :
    pointChargeCross R u v =
      ∑ s, ∫ x, pointChargePotential R x*inner ℝ (u.value s x) (v.value s x) := by
  unfold pointChargeCross
  apply Finset.sum_congr rfl
  intro s _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(pointChargePotential_mul_memLp R u s).coeFn_toLp,
    (h1Coordinate_memLp v (Sum.inl s)).coeFn_toLp] with x hu hv
  change pointChargeMultiplier R u s x = (pointChargePotential R x:ℂ)*u.value s x at hu
  change h1Coordinates v (Sum.inl s) x = v.value s x at hv
  rw [hu,hv,← Complex.real_smul,real_inner_smul_left]

theorem pointChargeCross_comm {m n : ℕ} (R : Fin m → Position)
    (u v : Coulomb.H1Vector n) : pointChargeCross R u v = pointChargeCross R v u := by
  rw [pointChargeCross_integral,pointChargeCross_integral]
  simp only [real_inner_comm]

theorem pointChargeEnergy_eq_cross {m n : ℕ} (R : Fin m → Position)
    (u : Coulomb.H1Vector n) : pointChargeEnergy R u = pointChargeCross R u u := by
  rw [pointChargeCross_integral]
  simp only [pointChargeEnergy,real_inner_self_eq_norm_sq]

theorem pointChargeMultiplier_add {m n : ℕ} (R : Fin m → Position)
    (u v : Coulomb.H1Vector n) (s : SpinConfiguration n) :
    pointChargeMultiplier R (u.add v) s = pointChargeMultiplier R u s+pointChargeMultiplier R v s := by
  apply Lp.ext
  filter_upwards [(pointChargePotential_mul_memLp R (u.add v) s).coeFn_toLp,
    (pointChargePotential_mul_memLp R u s).coeFn_toLp,
    (pointChargePotential_mul_memLp R v s).coeFn_toLp,
    Lp.coeFn_add (pointChargeMultiplier R u s) (pointChargeMultiplier R v s)] with x huv hu hv ha
  change pointChargeMultiplier R (u.add v) s x = _ at huv
  change pointChargeMultiplier R u s x = _ at hu
  change pointChargeMultiplier R v s x = _ at hv
  rw [ha]
  simp only [Pi.add_apply]
  rw [hu,hv,huv]
  change (pointChargePotential R x:ℂ)*(u.value s x+v.value s x) = _
  exact mul_add _ _ _

theorem pointChargeEnergy_add {m n : ℕ} (R : Fin m → Position)
    (u v : Coulomb.H1Vector n) :
    pointChargeEnergy R (u.add v) = pointChargeEnergy R u+pointChargeEnergy R v+
      2*pointChargeCross R u v := by
  simp only [pointChargeEnergy_eq_cross,pointChargeCross,pointChargeMultiplier_add,
    h1Coordinates_add,Pi.add_apply,inner_add_left,inner_add_right,Finset.sum_add_distrib]
  have h := pointChargeCross_comm R u v
  unfold pointChargeCross at h
  linarith

theorem nuclearEnergy_eq_pointChargeEnergy {m n : ℕ} (S : Coulomb.Nuclei m)
    (hcharge : ∀ a, S.charge a = 1) (u : Coulomb.H1Vector n) :
    Coulomb.nuclearEnergy S u = pointChargeEnergy S.position u := by
  simp only [Coulomb.nuclearEnergy,pointChargeEnergy,pointChargePotential,
    Coulomb.attraction,hcharge,one_mul,Fintype.sum_prod_type]

end ContinuumCoulomb

end

end OAI
