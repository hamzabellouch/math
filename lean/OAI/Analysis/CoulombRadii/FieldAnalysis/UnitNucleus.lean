import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.FiniteProdSum
import OAI.Analysis.CoulombRadii.FieldAnalysis.LeftPotential

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
namespace Coulomb
noncomputable def unitNucleus (R : Space) : Nuclei 1 where
  nonempty := by decide
  position := fun _ => R
  distinct := Function.injective_of_subsingleton _
  charge := fun _ => 1
  charge_ge_one := fun _ => le_rfl

lemma attraction_unitNucleus (R x : Space) :
    attraction (unitNucleus R) x = coulombKernel (x-R) := by
  simp [attraction, unitNucleus]

lemma crossPotential_nuclear {m k : ℕ} (x : Configuration m) (y : Configuration k) :
    crossPotential x y = ∑ i : Fin m, nuclearPotential (unitNucleus (position x i)) y := by
  simp only [crossPotential,nuclearPotential,attraction_unitNucleus]
  congr 1
  funext i
  congr 1
  funext j
  exact coulombKernel_sub_comm _ _

lemma crossPotential_slice_integrable {m k : ℕ} (x : Configuration m) (v : H1Vector k)
    (t : Spins k) : Integrable (fun y => crossPotential x y*‖v.value t y‖^2) := by
  simp only [crossPotential_nuclear,Finset.sum_mul]
  exact integrable_finsetSum _ (fun i _ => v.nuclear_integrable (unitNucleus (position x i)) t)

lemma crossPotential_spin_integral {m k : ℕ} (x : Configuration m) (v : H1Vector k) :
    (∑ t : Spins k, ∫ y, crossPotential x y*‖v.value t y‖^2) =
      ∑ i : Fin m, nuclearEnergy (unitNucleus (position x i)) v := by
  have h (t : Spins k) (i : Fin m) : Integrable (fun y =>
      nuclearPotential (unitNucleus (position x i)) y*‖v.value t y‖^2) :=
    v.nuclear_integrable (unitNucleus (position x i)) t
  simp only [crossPotential_nuclear,Finset.sum_mul]
  simp_rw [integral_finsetSum _ (fun i _ => h _ i)]
  exact Finset.sum_comm

lemma tensor_cross_prod_integrable {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins m) (t : Spins k) : Integrable
      (fun z : Configuration m × Configuration k =>
        crossPotential z.1 z.2*(‖u.value s z.1‖^2*‖v.value t z.2‖^2))
        (volume.prod volume) := by
  have H := (joinConfiguration_measurePreserving m k).integrable_comp_of_integrable
    (tensor_crossPotential_integrable u v (joinSpins m k (s,t)))
  apply H.congr
  filter_upwards [] with z
  change crossPotential ((joinConfiguration m k).symm (joinConfiguration m k z)).1
      ((joinConfiguration m k).symm (joinConfiguration m k z)).2 *
      ‖tensorValue u v (joinSpins m k (s,t)) (joinConfiguration m k z)‖^2 = _
  rw [ContinuousLinearEquiv.symm_apply_apply,tensorValue_join,joinSpins_left,joinSpins_right,norm_mul,mul_pow]

lemma cross_integral_core_integrable {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins m) (t : Spins k) : Integrable (fun x =>
      (∫ y, crossPotential x y*‖v.value t y‖^2)*‖u.value s x‖^2) := by
  have H := (tensor_cross_prod_integrable u v s t).integral_prod_left
  apply H.congr
  filter_upwards [] with x
  have he (y : Configuration k) :
      crossPotential x y*(‖u.value s x‖^2*‖v.value t y‖^2) =
      (crossPotential x y*‖v.value t y‖^2)*‖u.value s x‖^2 := by ring
  simp_rw [he, integral_mul_const]

lemma crossEnergy_iterated {m k : ℕ} (u : H1Vector m) (v : H1Vector k) :
    crossEnergy u v = ∑ s : Spins m, ∑ t : Spins k,
      ∫ x, (∫ y, crossPotential x y*‖v.value t y‖^2)*‖u.value s x‖^2 := by
  unfold crossEnergy potentialEnergy
  rw [sum_joinSpins]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  rw [← (joinConfiguration_measurePreserving m k).integral_comp']
  change (∫ z : Configuration m × Configuration k,
    crossPotential ((joinConfiguration m k).symm (joinConfiguration m k z)).1
      ((joinConfiguration m k).symm (joinConfiguration m k z)).2 *
      ‖tensorValue u v (joinSpins m k (s,t)) (joinConfiguration m k z)‖^2
        ∂(volume.prod volume)) = _
  simp only [ContinuousLinearEquiv.symm_apply_apply,tensorValue_join,joinSpins_left,joinSpins_right,
    norm_mul,mul_pow]
  rw [integral_prod _ (tensor_cross_prod_integrable u v s t)]
  apply integral_congr_ae
  filter_upwards [] with x
  have he (y : Configuration k) :
      crossPotential x y*(‖u.value s x‖^2*‖v.value t y‖^2) =
      (crossPotential x y*‖v.value t y‖^2)*‖u.value s x‖^2 := by ring
  simp_rw [he, integral_mul_const]

lemma cross_core_integrable {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins m) : Integrable (fun x =>
      (∑ i : Fin m, nuclearEnergy (unitNucleus (position x i)) v)*‖u.value s x‖^2) := by
  simp_rw [← crossPotential_spin_integral,Finset.sum_mul]
  exact integrable_finsetSum _ (fun t _ => cross_integral_core_integrable u v s t)

lemma crossEnergy_core {m k : ℕ} (u : H1Vector m) (v : H1Vector k) :
    crossEnergy u v = ∑ s : Spins m,
      ∫ x, (∑ i : Fin m, nuclearEnergy (unitNucleus (position x i)) v)*‖u.value s x‖^2 := by
  rw [crossEnergy_iterated]
  apply Finset.sum_congr rfl
  intro s _
  rw [← integral_finsetSum _ (fun t _ => cross_integral_core_integrable u v s t)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← Finset.sum_mul,crossPotential_spin_integral]

noncomputable def coreInteractionDensity {m : ℕ} (u : H1Vector m) (d : Space → ℝ) : ℝ :=
  ∑ s : Spins m, ∫ x, (∑ i : Fin m, ∫ z : Space,
    coulombKernel (z-position x i)*d z)*‖u.value s x‖^2

lemma selectedSlater_spatialSupport {ι : Type*} [Fintype ι]
    (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s)) (B : Set Space)
    (hB : ∀ a s x, x ∉ B → v a x s = 0) (w : ι → Bool) :
    SpatiallySupported (selectedSlater v hv hC w) B := by
  intro s
  filter_upwards [] with x hx
  change ¬∀ i, position x i ∈ B at hx
  obtain ⟨j,hj⟩ := not_forall.mp hx
  change slaterConfiguration (fun a => v (occupiedIndex w a)) s x = 0
  rw [slaterConfiguration_expansion]
  have hp (p : Equiv.Perm (Fin (Fintype.card {i // w i = true}))) :
      tensorOrbital (fun a => v (occupiedIndex w a)) p s x = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact hB _ _ _ hj
  simp only [hp,mul_zero,Finset.sum_const_zero]

lemma bernoulli_core_cross_mean {ι : Type*} [Fintype ι] {m : ℕ}
    (u : H1Vector m) (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x : Space, star (v a x s)*v b x s) =
      if a = b then (1:ℂ) else 0) (lam : ι → ℝ) :
    (∑ w : ι → Bool, bernoulliWeight lam w * crossEnergy u (selectedSlater v hv hC w)) =
      coreInteractionDensity u (finiteFermiDensity v lam) := by
  simp only [crossEnergy_core,Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold coreInteractionDensity
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun w _ =>
    (cross_core_integrable u (selectedSlater v hv hC w) s).const_mul (bernoulliWeight lam w))]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [← mul_assoc,← Finset.sum_mul]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [bernoulli_slater_nuclear_mean _ v hv hC ho lam]
  simp only [attraction_unitNucleus]

theorem finite_fermi_core_trial {ι : Type*} [Fintype ι] {M m : ℕ}
    (S : Nuclei M) (u : H1Vector m) (hu : Antisymmetric u) (hm : mass u = 1)
    (A B : Set Space) (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (hsu : SpatiallySupported u A) (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (hsv : ∀ a s x, x ∉ B → v a x s = 0)
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x : Space, star (v a x s)*v b x s) =
      if a = b then (1:ℂ) else 0) (lam : ι → ℝ)
    (h0 : ∀ i, 0 ≤ lam i) (h1 : ∀ i, lam i ≤ 1) :
    ∃ n : ℕ, ∃ ψ : H1Vector n, Antisymmetric ψ ∧ mass ψ = 1 ∧
      form S ψ ≤ form S u +
      ((1/2:ℝ)*(∑ i, lam i * ∑ s, ∑ b : Fin 3,
        ∫ x : Space, ‖fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)‖^2) -
      (∫ x, attraction S x*finiteFermiDensity v lam x) +
      (1/2:ℝ)*(∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*
        (finiteFermiDensity v lam xy.1*finiteFermiDensity v lam xy.2))) +
      coreInteractionDensity u (finiteFermiDensity v lam) := by
  have he (w : ι → Bool) : form S (u.wedge (selectedSlater v hv hC w)) =
      form S u+form S (selectedSlater v hv hC w)+crossEnergy u (selectedSlater v hv hC w) := by
    rw [form_wedge S u (selectedSlater v hv hC w) hu (selectedSlater_antisymmetric v hv hC w)
      A B hsu (selectedSlater_spatialSupport v hv hC B hsv w) hA hB hAB,
      selectedSlater_normalized v hv hC ho w,hm,mul_one,one_mul]
  obtain ⟨w, hw⟩ := exists_le_weighted_average (bernoulliWeight lam)
    (fun w => form S (u.wedge (selectedSlater v hv hC w)))
    (bernoulliWeight_nonneg lam h0 h1) (bernoulliWeight_sum lam)
  refine ⟨_, u.wedge (selectedSlater v hv hC w), wedge_antisymmetric _ _, ?_, hw.trans ?_⟩
  · rw [mass_wedge u (selectedSlater v hv hC w) hu (selectedSlater_antisymmetric v hv hC w)
      A B hsu (selectedSlater_spatialSupport v hv hC B hsv w) hAB,
      selectedSlater_normalized v hv hC ho w,hm,mul_one]
  · simp only [he,mul_add,Finset.sum_add_distrib]
    rw [← Finset.sum_mul,bernoulliWeight_sum,one_mul,bernoulli_core_cross_mean u v hv hC ho lam]
    gcongr
    exact bernoulli_slater_form_upper S v hv hC ho lam
end Coulomb

end

end OAI
