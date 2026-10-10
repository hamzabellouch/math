import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoreOrbitalProjection
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OneElectronCoordinates
import OAI.Analysis.CoulombRadii.FieldAnalysis.WedgeMultiplicity

namespace OAI

/-! The one-electron finite-rank lower bound acts on every electron slot.
All coordinate changes preserve the full spinful weak-H1 domain. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def electronSlotKinetic {n : ℕ} (u : Coulomb.H1Vector n) (i : Fin n) : ℝ :=
  (1/2:ℝ)*∑ s, ∑ a : Fin 3, ∫ x, ‖u.gradient s (i,a) x‖^2

theorem sum_electronSlotKinetic {n : ℕ} (u : Coulomb.H1Vector n) :
    (∑ i, electronSlotKinetic u i) = Coulomb.kinetic u := by
  unfold electronSlotKinetic Coulomb.kinetic
  rw [← Finset.mul_sum,Finset.sum_comm]
  simp only [Fintype.sum_prod_type]

theorem coreKinetic_permutation_one {n : ℕ} (u : Coulomb.H1Vector (n+1))
    (p : Equiv.Perm (Fin (n+1))) :
    Coulomb.coreKinetic (u.permutation p) = electronSlotKinetic u (p.symm (Fin.last n)) := by
  unfold Coulomb.coreKinetic electronSlotKinetic
  simp only [Coulomb.permutation_gradient,Fintype.sum_prod_type,Fin.sum_univ_one]
  have hlast : Fin.natAdd n (0 : Fin 1) = Fin.last n := Fin.ext rfl
  have he (s : SpinConfiguration (n+1)) (a : Fin 3) :
      (∫ x, ‖u.gradient (s ∘ p) (p.symm (Fin.natAdd n (0 : Fin 1)),a) (Coulomb.permute p x)‖^2) =
        ∫ x, ‖u.gradient (s ∘ p) (p.symm (Fin.last n),a) x‖^2 := by
    simpa only [Coulomb.permutationIsometry_apply,hlast] using
      (Coulomb.permutationIsometry p).measurePreserving.integral_comp
        (Coulomb.permutationIsometry p).toHomeomorph.measurableEmbedding
        (fun x => ‖u.gradient (s ∘ p) (p.symm (Fin.last n),a) x‖^2)
  simp_rw [he]
  congr 1
  exact Equiv.sum_comp (Coulomb.permutationSpins p)
    (fun s => ∑ a : Fin 3, ∫ x, ‖u.gradient s (p.symm (Fin.last n),a) x‖^2)

theorem oneElectronCoordinates_core {n : ℕ} (x : Configuration (n+1)) :
    oneElectronCoordinates ((Coulomb.joinConfiguration n 1).symm x).2 =
      Coulomb.position x (Fin.last n) := by
  ext a
  have h := Coulomb.joinConfiguration_right n 1
    ((Coulomb.joinConfiguration n 1).symm x).1
    ((Coulomb.joinConfiguration n 1).symm x).2 (0 : Fin 1) a
  change ((Coulomb.joinConfiguration n 1).symm x).2 (0,a) = x (Fin.last n,a)
  have hlast : Fin.natAdd n (0 : Fin 1) = Fin.last n := Fin.ext rfl
  simpa only [Prod.mk.eta,ContinuousLinearEquiv.apply_symm_apply,hlast] using h.symm

theorem corePotential_permutation_one {n : ℕ} (u : Coulomb.H1Vector (n+1))
    (p : Equiv.Perm (Fin (n+1))) (V : Position → ℝ) :
    Coulomb.potentialForm (fun z => V (oneElectronCoordinates
      ((Coulomb.joinConfiguration n 1).symm z).2)) (u.permutation p) =
        Coulomb.potentialForm (fun x => V (Coulomb.position x (p.symm (Fin.last n)))) u := by
  simp only [Coulomb.potentialForm,Coulomb.permutation_value,oneElectronCoordinates_core]
  have he (s : SpinConfiguration (n+1)) :
      (∫ x, V (Coulomb.position x (Fin.last n))*‖u.value (s ∘ p) (Coulomb.permute p x)‖^2) =
        ∫ x, V (Coulomb.position x (p.symm (Fin.last n)))*‖u.value (s ∘ p) x‖^2 := by
    have h := (Coulomb.permutationIsometry p).measurePreserving.integral_comp
      (Coulomb.permutationIsometry p).toHomeomorph.measurableEmbedding
      (fun x => V (Coulomb.position x (p.symm (Fin.last n)))*‖u.value (s ∘ p) x‖^2)
    simpa only [Coulomb.permutationIsometry_apply,Coulomb.position,Coulomb.permute,
      Equiv.apply_symm_apply] using h
  simp_rw [he]
  exact Equiv.sum_comp (Coulomb.permutationSpins p)
    (fun s => ∫ x, V (Coulomb.position x (p.symm (Fin.last n)))*‖u.value s x‖^2)

def electronSlotOrbitalMass {n : ℕ} {ι : Type*} [Fintype ι]
    (u : Coulomb.H1Vector (n+1))
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1))) (i : Fin (n+1)) : ℝ :=
  coreOrbitalMass (u.permutation (Equiv.swap (Fin.last n) i)) φ

def totalOrbitalMass {n : ℕ} {ι : Type*} [Fintype ι]
    (u : Coulomb.H1Vector (n+1))
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1))) : ℝ :=
  ∑ i, electronSlotOrbitalMass u φ i

theorem electronSlot_projection_lower {n : ℕ} {ι : Type*} [Fintype ι]
    (V : Position → ℝ) (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B)
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1))) (E κ : ℝ)
    (hbound : ∀ v : Coulomb.H1Vector 1,
      E*Coulomb.mass v-κ*graphOrbitalMass φ (h1Coordinates v) ≤
        boundedPotentialForm (fun x => V (oneElectronCoordinates x)) v)
    (u : Coulomb.H1Vector (n+1)) (i : Fin (n+1)) :
    E*Coulomb.mass u-κ*electronSlotOrbitalMass u φ i ≤ electronSlotKinetic u i+
      Coulomb.potentialForm (fun x => V (Coulomb.position x i)) u := by
  have h := coreOneBody_projection_lower _ (hV.comp oneElectronCoordinates.continuous)
    B (fun x => hB _) φ E κ hbound (u.permutation (Equiv.swap (Fin.last n) i))
  simp only [Function.comp_apply] at h
  rw [Coulomb.mass_permutation,coreKinetic_permutation_one,corePotential_permutation_one] at h
  simpa only [Equiv.symm_swap,Equiv.swap_apply_left,electronSlotOrbitalMass] using h

theorem manyElectron_projection_lower {n : ℕ} {ι : Type*} [Fintype ι]
    (V : Position → ℝ) (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B)
    (φ : ι → Lp ℂ 2 (volume : Measure (Configuration 1))) (E κ : ℝ)
    (hbound : ∀ v : Coulomb.H1Vector 1,
      E*Coulomb.mass v-κ*graphOrbitalMass φ (h1Coordinates v) ≤
        boundedPotentialForm (fun x => V (oneElectronCoordinates x)) v)
    (u : Coulomb.H1Vector (n+1)) :
    (n+1:ℕ)*E*Coulomb.mass u-κ*totalOrbitalMass u φ ≤
      boundedPotentialForm (fun x => ∑ i, V (Coulomb.position x i)) u := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => electronSlot_projection_lower V hV B hB φ E κ hbound u i)
  have hi (s : SpinConfiguration (n+1)) (i : Fin (n+1)) :
      Integrable (fun x => V (Coulomb.position x i)*‖u.value s x‖^2) :=
    bounded_state_potential_integrable u _ (hV.comp (Coulomb.positionCLM i).continuous)
      B (fun x => hB _) s
  have hp : (∑ i, Coulomb.potentialForm (fun x => V (Coulomb.position x i)) u) =
      Coulomb.potentialForm (fun x => ∑ i, V (Coulomb.position x i)) u := by
    unfold Coulomb.potentialForm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    simp only [Finset.sum_mul]
    exact (integral_finsetSum _ (fun i _ => hi s i)).symm
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,sum_electronSlotKinetic,hp] at h
  simpa only [Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← Finset.mul_sum,
    totalOrbitalMass,boundedPotentialForm,
    Coulomb.potentialForm,mul_assoc] using h

end ContinuumCoulomb

end

end OAI
