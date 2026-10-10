import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.FlatBodyDensity
import OAI.Analysis.CoulombRadii.FieldAnalysis.SpinConfigurationIntegral
import OAI.Analysis.CoulombRadii.Variational.PhysicalBridge

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom

lemma firstParticleDensity_physical_slice {N : ℕ} (u : Coulomb.H1Vector (N+1))
    (s : Fin 2) (x : Position)
    (hi : ∀ σ : Spins N,Integrable (fun y : Configuration N =>
      ‖fromH1Wave u (Fin.cons s σ) (Fin.cons x y)‖^2)) :
    Coulomb.firstParticleDensity (μ := Coulomb.spinSpaceMeasure) (Coulomb.cubeState u)
      (s,WithLp.ofLp x) = (N+1:ℝ)*∑ σ : Spins N,∫ y : Configuration N,
        ‖fromH1Wave u (Fin.cons s σ) (Fin.cons x y)‖^2 := by
  unfold Coulomb.firstParticleDensity
  simp only [Nat.cast_add,Nat.cast_one]
  congr 1
  let F (σ : Coulomb.Spins N) (z : Coulomb.Configuration N) : ℝ :=
    ‖fromH1Wave u (Fin.cons s σ) (Fin.cons x ((flattenConfiguration N).symm z))‖^2
  have hF (σ) : Integrable (F σ) :=
    (flattenConfiguration_symm_measurePreserving N).integrable_comp_of_integrable (hi σ)
  calc
    _=∫ z,F ((Coulomb.spinCubeEquiv N) z).1
        (WithLp.toLp 2 ((Coulomb.spinCubeEquiv N) z).2)
        ∂(Measure.pi fun _ : Fin N => Coulomb.spinSpaceMeasure) := by
      apply integral_congr_ae
      filter_upwards [] with z
      congr 2
      unfold Coulomb.firstFiber Coulomb.cubeState fromH1Wave
      congr 1
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      · ext ⟨i,a⟩
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    _=∑ σ,∫ z,F σ z := Coulomb.spinConfiguration_integral F hF
    _=_ := by
      apply Finset.sum_congr rfl
      intro σ _
      exact (flattenConfiguration_symm_measurePreserving N).integral_comp'
        (fun y : Configuration N => ‖fromH1Wave u (Fin.cons s σ) (Fin.cons x y)‖^2)

theorem density_fromH1_eq_oneBodyDensity {N : ℕ} (u : Coulomb.H1Vector (N+1)) :
    density (fromH1Wave u)=ᵐ[volume] Coulomb.oneBodyDensity u := by
  have hL (σ : Spins (N+1)) : Integrable (fun z : Configuration (N+1) => ‖fromH1Wave u σ z‖^2) :=
    ((u.value_L2 σ).comp_measurePreserving (flattenConfiguration_measurePreserving (N+1))).norm.integrable_sq
  have hi : ∀ᵐ x : Position,∀ σ : Spins (N+1),Integrable
      (fun y : Configuration N => ‖fromH1Wave u σ (Fin.cons x y)‖^2) := by
    rw [ae_all_iff]
    intro σ
    exact (integrable_cons (hL σ)).prod_right_ae
  filter_upwards [hi] with x hx
  unfold Coulomb.oneBodyDensity Coulomb.flatOneBodyDensity
  simp_rw [firstParticleDensity_physical_slice u _ x (fun σ => hx _)]
  rw [←Finset.mul_sum]
  unfold density
  congr 1
  let e : Spins (N+1) ≃ (Fin 2 × Spins N) :=
    { toFun := fun σ => (σ 0,Fin.tail σ)
      invFun := fun p => Fin.cons p.1 p.2
      left_inv := fun σ => Fin.cons_self_tail σ
      right_inv := fun p => by cases p; rfl }
  calc
    _=∑ p : Fin 2 × Spins N,∫ y : Configuration N,
        ‖fromH1Wave u (Fin.cons p.1 p.2) (Fin.cons x y)‖^2 := by
      apply Fintype.sum_equiv e
      intro σ
      change (∫ y : Configuration N,‖fromH1Wave u σ (Fin.cons x y)‖^2)=
        ∫ y : Configuration N,‖fromH1Wave u (Fin.cons (σ 0) (Fin.tail σ)) (Fin.cons x y)‖^2
      rw [Fin.cons_self_tail]
    _=_ := Fintype.sum_prod_type _

theorem physical_density_power_bound {N : ℕ} (u : Coulomb.H1Vector (N+1))
    (hu : Coulomb.Antisymmetric u) (hm : Coulomb.mass u≤1) :
    Integrable (fun x => (density (fromH1Wave u) x)^(5/3:ℝ)) ∧
    (∫ x,(density (fromH1Wave u) x)^(5/3:ℝ))≤(32768/(3*Real.pi^2))*Coulomb.kinetic u := by
  have he := (density_fromH1_eq_oneBodyDensity u).fun_comp (fun t : ℝ => t^(5/3:ℝ))
  obtain ⟨hi,hb⟩ := Coulomb.oneBodyDensity_power_bound u hu hm
  exact ⟨hi.congr he.symm,(integral_congr_ae he).trans_le hb⟩
end NeutralAtom
end

end
end

end OAI
