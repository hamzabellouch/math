import Mathlib
import OAI.Analysis.CoulombRadii.LimitTheory.UniformGroundStateCountControl
import OAI.Analysis.CoulombRadii.Propagation.NuclearPotential

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
noncomputable section
namespace NeutralAtom

def flattenConfiguration (n : ℕ) : Configuration n ≃L[ℝ] Coulomb.Configuration n :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun x => WithLp.toLp 2 (fun ia => x ia.1 ia.2)
    invFun := fun x i => Coulomb.position x i
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }

@[simp] lemma flattenConfiguration_apply (n : ℕ) (x : Configuration n) (i : Fin n) (a : Fin 3) :
    flattenConfiguration n x (i,a) = x i a := rfl
@[simp] lemma flattenConfiguration_symm_apply (n : ℕ) (x : Coulomb.Configuration n) (i : Fin n) :
    (flattenConfiguration n).symm x i = Coulomb.position x i := rfl

lemma flattenConfiguration_symm_measurePreserving (n : ℕ) :
    MeasurePreserving (flattenConfiguration n).symm.toHomeomorph.toMeasurableEquiv :=
  Coulomb.configurationMeasurableEquiv_measurePreserving n
lemma flattenConfiguration_measurePreserving (n : ℕ) :
    MeasurePreserving (flattenConfiguration n).toHomeomorph.toMeasurableEquiv :=
  (flattenConfiguration_symm_measurePreserving n).symm

lemma flattenConfiguration_coordinateDirection {n : ℕ} (i : Fin n) (a : Fin 3) :
    flattenConfiguration n (coordinateDirection i a) = EuclideanSpace.single (i,a) 1 := by
  ext ⟨j,b⟩
  simp [flattenConfiguration_apply,coordinateDirection,Pi.single_apply,PiLp.single_apply]
  split_ifs <;> simp_all

lemma flattenConfiguration_permute {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Configuration n) :
    flattenConfiguration n (x ∘ p) = Coulomb.permute p (flattenConfiguration n x) := rfl
lemma flattenConfiguration_symm_permute {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Coulomb.Configuration n) :
    (flattenConfiguration n).symm (Coulomb.permute p x) = (flattenConfiguration n).symm x ∘ p := rfl

lemma weakDirectional_pullback {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasureSpace F] [BorelSpace F]
    (L : E ≃L[ℝ] F) (hp : MeasurePreserving L.toHomeomorph.toMeasurableEquiv)
    {u g : F → ℂ} {v : F}
    (hw : ∀ (φ : F → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, u x * (fderiv ℝ φ x v : ℂ)) = -(∫ x, g x * (φ x : ℂ)))
    {w : E} (hL : L w = v) (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    (∫ x, u (L x) * (fderiv ℝ φ x w : ℂ)) = -(∫ x, g (L x) * (φ x : ℂ)) := by
  have H := hw (φ ∘ L.symm) (hφ.comp L.symm.contDiff)
    (hc.comp_homeomorph L.symm.toHomeomorph)
  have hd (x : F) : fderiv ℝ (φ ∘ L.symm) x v = fderiv ℝ φ (L.symm x) w := by
    rw [fderiv_comp x (hφ.differentiable (by simp) _) L.symm.differentiableAt]
    rw [L.symm.fderiv]
    change fderiv ℝ φ (L.symm x) (L.symm v) = _
    rw [← hL, L.symm_apply_apply]
  simp_rw [hd] at H
  rw [← hp.integral_comp' (fun x => u x * (fderiv ℝ φ (L.symm x) w : ℂ)),
      ← hp.integral_comp' (fun x => g x * ((φ ∘ L.symm) x : ℂ))] at H
  change (∫ x, u (L x) * (fderiv ℝ φ (L.symm (L x)) w : ℂ)) =
    -(∫ x, g (L x) * (φ (L.symm (L x)) : ℂ)) at H
  simpa only [L.symm_apply_apply] using H

def asH1 {n : ℕ} (ψ : Wavefunction n) (g : Gradient n)
    (hw : HasWeakGradient ψ g) (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    (hg : ∀ σ i a, MemLp (g σ i a) 2 volume) : Coulomb.H1Vector n where
  value := fun s x => ψ s ((flattenConfiguration n).symm x)
  gradient := fun s ia x => g s ia.1 ia.2 ((flattenConfiguration n).symm x)
  value_L2 := fun s => (hψ s).comp_measurePreserving (flattenConfiguration_symm_measurePreserving n)
  partial_L2 := fun s ia => (hg s ia.1 ia.2).comp_measurePreserving
    (flattenConfiguration_symm_measurePreserving n)
  weak_partial := by
    intro s ia φ hφ hc
    apply weakDirectional_pullback (flattenConfiguration n).symm
      (flattenConfiguration_symm_measurePreserving n)
      (fun φ hφ hc => by simpa only [mul_comm] using hw s ia.1 ia.2 φ hφ hc)
      (w := EuclideanSpace.single ia 1) _ φ hφ hc
    rw [ContinuousLinearEquiv.symm_apply_eq]
    exact (flattenConfiguration_coordinateDirection ia.1 ia.2).symm

def fromH1Wave {n : ℕ} (ψ : Coulomb.H1Vector n) : Wavefunction n :=
  fun s x => ψ.value s (flattenConfiguration n x)
def fromH1Gradient {n : ℕ} (ψ : Coulomb.H1Vector n) : Gradient n :=
  fun s i a x => ψ.gradient s (i,a) (flattenConfiguration n x)

lemma fromH1_weak {n : ℕ} (ψ : Coulomb.H1Vector n) :
    HasWeakGradient (fromH1Wave ψ) (fromH1Gradient ψ) := by
  intro s i a φ hφ hc
  have H := weakDirectional_pullback (flattenConfiguration n)
    (flattenConfiguration_measurePreserving n) (ψ.weak_partial s (i,a))
    (flattenConfiguration_coordinateDirection i a) φ hφ hc
  simpa only [fromH1Wave,fromH1Gradient,mul_comm] using H

lemma asH1_antisymmetric {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) : Coulomb.Antisymmetric (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1) := by
  intro p s
  have H := (flattenConfiguration_symm_measurePreserving n).quasiMeasurePreserving.ae (hd.1 p s)
  exact H

lemma fromH1_domain {n : ℕ} (ψ : Coulomb.H1Vector n) (ha : Coulomb.Antisymmetric ψ) :
    FormDomain (fromH1Wave ψ) (fromH1Gradient ψ) := by
  refine ⟨?_, fromH1_weak ψ, ?_, ?_, ?_, ?_⟩
  · intro p s
    exact (flattenConfiguration_measurePreserving n).quasiMeasurePreserving.ae (ha p s)
  · intro s
    exact (ψ.value_L2 s).comp_measurePreserving (flattenConfiguration_measurePreserving n)
  · intro s i a
    exact (ψ.partial_L2 s (i,a)).comp_measurePreserving (flattenConfiguration_measurePreserving n)
  · intro s i
    have H := (flattenConfiguration_measurePreserving n).integrable_comp_of_integrable
      (ψ.nuclear_coulomb_integrable_bound s i 0 (by norm_num : (0:ℝ)<1)).1
    change Integrable (fun x : Configuration n => ‖x i-0‖⁻¹*‖fromH1Wave ψ s x‖^2) at H
    simpa only [sub_zero] using H
  · intro s i j hij
    exact (flattenConfiguration_measurePreserving n).integrable_comp_of_integrable
      (ψ.pair_coulomb_integrable_bound s i j hij.ne (by norm_num : (0:ℝ)<1)).1

lemma fromH1_mass {n : ℕ} (ψ : Coulomb.H1Vector n) :
    normSquared (fromH1Wave ψ) = Coulomb.mass ψ := by
  unfold normSquared Coulomb.mass fromH1Wave
  apply Finset.sum_congr rfl
  intro s _
  exact (flattenConfiguration_measurePreserving n).integral_comp' (fun x => ‖ψ.value s x‖^2)

lemma asH1_mass {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hw : HasWeakGradient ψ g) (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    (hg : ∀ σ i a, MemLp (g σ i a) 2 volume) :
    Coulomb.mass (asH1 ψ g hw hψ hg) = normSquared ψ := by
  unfold normSquared Coulomb.mass asH1
  apply Finset.sum_congr rfl
  intro s _
  exact (flattenConfiguration_symm_measurePreserving n).integral_comp' (fun x => ‖ψ s x‖^2)

@[simp] lemma position_flattenConfiguration {n : ℕ} (x : Configuration n) (i : Fin n) :
    Coulomb.position (flattenConfiguration n x) i = x i := rfl

lemma coulombPotential_flatten {n : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) (x : Configuration n) :
    coulombPotential Z x = -Coulomb.nuclearPotential (Coulomb.atom Z hZ)
      (flattenConfiguration n x) + Coulomb.pairPotential (flattenConfiguration n x) := by
  classical
  simp [coulombPotential,Coulomb.nuclearPotential,Coulomb.pairPotential,Coulomb.attraction,
    Coulomb.atom,Coulomb.coulombKernel,Finset.sum_filter,Finset.mul_sum,neg_mul]

lemma fromH1_energy {n : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) (ψ : Coulomb.H1Vector n) :
    energy Z (fromH1Wave ψ) (fromH1Gradient ψ) = Coulomb.form (Coulomb.atom Z hZ) ψ := by
  have hK : (∑ s : Spins n, ∑ i : Fin n, ∑ a : Fin 3,
      ∫ x : Configuration n, ‖fromH1Gradient ψ s i a x‖^2) =
      ∑ s : Coulomb.Spins n, ∑ ia : Fin n × Fin 3,
        ∫ x : Coulomb.Configuration n, ‖ψ.gradient s ia x‖^2 := by
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    exact (flattenConfiguration_measurePreserving n).integral_comp' (fun x => ‖ψ.gradient s (i,a) x‖^2)
  have hV (s : Spins n) :
      (∫ x : Configuration n, coulombPotential Z x * ‖fromH1Wave ψ s x‖^2) =
      -(∫ x, Coulomb.nuclearPotential (Coulomb.atom Z hZ) x * ‖ψ.value s x‖^2) +
        ∫ x, Coulomb.pairPotential x * ‖ψ.value s x‖^2 := by
    simp_rw [coulombPotential_flatten Z hZ]
    change (∫ x, (-Coulomb.nuclearPotential (Coulomb.atom Z hZ) (flattenConfiguration n x) +
      Coulomb.pairPotential (flattenConfiguration n x)) * ‖ψ.value s (flattenConfiguration n x)‖^2) = _
    calc
      _ = ∫ x, (-Coulomb.nuclearPotential (Coulomb.atom Z hZ) x + Coulomb.pairPotential x) * ‖ψ.value s x‖^2 :=
        (flattenConfiguration_measurePreserving n).integral_comp'
          (fun x => (-Coulomb.nuclearPotential (Coulomb.atom Z hZ) x + Coulomb.pairPotential x) * ‖ψ.value s x‖^2)
      _ = _ := ?_

    simp_rw [add_mul,neg_mul]
    have hn : Integrable (fun x => -(Coulomb.nuclearPotential (Coulomb.atom Z hZ) x * ‖ψ.value s x‖^2)) :=
      (ψ.nuclear_integrable (Coulomb.atom Z hZ) s).neg
    have hp : Integrable (fun x => Coulomb.pairPotential x * ‖ψ.value s x‖^2) := ψ.pair_integrable s
    rw [integral_add hn hp, integral_neg]
  unfold energy Coulomb.form Coulomb.kinetic Coulomb.nuclearEnergy Coulomb.pairEnergy
  rw [hK]
  simp_rw [hV, Finset.sum_add_distrib,Finset.sum_neg_distrib]
  unfold Coulomb.nuclearPotential Coulomb.pairPotential
  ring

lemma asH1_energy {n : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction n} {g : Gradient n}
    (hw : HasWeakGradient ψ g) (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    (hg : ∀ σ i a, MemLp (g σ i a) 2 volume) :
    Coulomb.form (Coulomb.atom Z hZ) (asH1 ψ g hw hψ hg) = energy Z ψ g := by
  exact (fromH1_energy Z hZ (asH1 ψ g hw hψ hg)).symm

lemma asH1_groundState (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction Z} {g : Gradient Z}
    (hd : FormDomain ψ g) (hn : normSquared ψ = 1)
    (hm : ∀ (χ : Wavefunction Z) (h : Gradient Z),
      FormDomain χ h → normSquared χ = 1 → energy Z ψ g ≤ energy Z χ h) :
    Coulomb.GroundState (Coulomb.atom Z hZ) (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1) := by
  let u := asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1
  have ha : Coulomb.Antisymmetric u := asH1_antisymmetric hd
  have hu : Coulomb.mass u = 1 := (asH1_mass ..).trans hn
  refine ⟨ha,hu,le_antisymm ?_ (Coulomb.energy_le_form _ (by omega) u ha hu)⟩
  unfold Coulomb.energy
  rw [ite_eq_right (show Z ≠ 0 by omega)]
  refine le_csInf ?_ ?_
  · exact ⟨Coulomb.form (Coulomb.atom Z hZ) u, u, ha, hu, rfl⟩
  rintro e ⟨v,hv,hvm,rfl⟩
  rw [asH1_energy Z hZ]
  have H := hm (fromH1Wave v) (fromH1Gradient v) (fromH1_domain v hv)
    ((fromH1_mass v).trans hvm)
  rwa [fromH1_energy Z hZ] at H

lemma fromH1_groundState (Z : ℕ) (hZ : 1 ≤ Z) (ψ : Coulomb.H1Vector Z)
    (hψ : Coulomb.GroundState (Coulomb.atom Z hZ) ψ) :
    IsNormalizedGroundState Z (fromH1Wave ψ) := by
  refine ⟨fromH1Gradient ψ, fromH1_domain ψ hψ.1, (fromH1_mass ψ).trans hψ.2.1, ?_⟩
  intro χ h hd hm
  rw [fromH1_energy Z hZ]
  have H := hψ.minimizes (by omega) (asH1 χ h hd.2.1 hd.2.2.1 hd.2.2.2.1)
    (asH1_antisymmetric hd) ((asH1_mass ..).trans hm)
  rwa [asH1_energy Z hZ] at H

lemma fromH1_exteriorMass {N : ℕ} (ψ : Coulomb.H1Vector (N+1))
    (ha : Coulomb.Antisymmetric ψ) (r : ℝ) :
    exteriorMass (fromH1Wave ψ) r = Coulomb.exteriorMass ψ r := by
  have hd := fromH1_domain ψ ha
  let S : Set Position := {x | r < ‖x‖}
  have hS : MeasurableSet S := measurableSet_lt measurable_const continuous_norm.measurable
  rw [exteriorMass, ← rawExpectation_count_eq_density hd.1 hd.2.2.1 hS]
  unfold rawExpectation configurationDensity
  simp_rw [Finset.mul_sum]
  have hi s : Integrable (fun x => rawCount S x * ‖fromH1Wave ψ s x‖^2) := by
    simp_rw [rawCount, Finset.sum_mul]
    exact integrable_finsetSum _ fun i _ =>
      integrable_siteWeight (hd.2.2.1 s).norm.integrable_sq hS i
  rw [integral_finsetSum _ (fun s _ => hi s)]
  unfold Coulomb.exteriorMass
  apply Finset.sum_congr rfl
  intro s _
  have he (x : Configuration (N+1)) :
      rawCount S x = ∑ i : Fin (N+1), if r < ‖Coulomb.position (flattenConfiguration (N+1) x) i‖ then (1:ℝ) else 0 := by
    unfold rawCount
    apply Finset.sum_congr rfl
    intro i _
    simp only [S, Set.indicator_apply, Set.mem_ofPred_eq, position_flattenConfiguration]
    rfl
  simp_rw [he]
  exact (flattenConfiguration_measurePreserving (N+1)).integral_comp'
    (fun x => (∑ i : Fin (N+1), if r < ‖Coulomb.position x i‖ then (1:ℝ) else 0)*‖ψ.value s x‖^2)

lemma asH1_exteriorMass {N : ℕ} {ψ : Wavefunction (N+1)} {g : Gradient (N+1)}
    (hd : FormDomain ψ g) (r : ℝ) :
    Coulomb.exteriorMass (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1) r = exteriorMass ψ r := by
  exact (fromH1_exteriorMass _ (asH1_antisymmetric hd) r).symm

end NeutralAtom

end

end
end

end OAI
