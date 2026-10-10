import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CutCoreNumber
import OAI.Analysis.CoulombIonization.Variational.CorePriceExcess
import OAI.Analysis.CoulombIonization.FormDomain.BlockEnergetics

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom

lemma coreCoulombAt_mass_zero {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (hm : formMass ψ = 0) (y : Space) : coreCoulombAt ψ y = 0 := by
  have hz (s : Spins N) : (∫ x, ‖ψ.value s x‖^2) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => integral_nonneg fun x => sq_nonneg _)).mp hm s
      (Finset.mem_univ _)
  unfold coreCoulombAt
  apply Finset.sum_eq_zero
  intro s _
  apply Finset.sum_eq_zero
  intro i _
  have he := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _)
    (hψ.1 s).norm.integrable_sq).mp (hz s)
  calc
    _ = ∫ _x : Configuration N, (0:ℝ) := integral_congr_ae (he.mono fun x hx => by simp only [hx,Pi.zero_apply,zero_div])
    _ = 0 := integral_zero _ _

lemma normalizedCoreField_mul_mass {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (Z lam : ℝ) (y : Space) :
    normalizedCoreField Z lam ψ y*formMass ψ =
      Z*formMass ψ/‖y‖-coreCoulombAt ψ y-lam*formMass ψ := by
  by_cases hm : formMass ψ = 0
  · simp only [hm,mul_zero,zero_div,coreCoulombAt_mass_zero hψ hm,sub_zero]
  · unfold normalizedCoreField
    rw [sub_mul,div_mul_cancel₀ _ hm]

lemma coreSlice_mass_div {N M : ℕ} (ψ : FormVector (N+M)) (t : Spins M)
    (y : Configuration M) (j : Fin M) :
    formMass (coreSlice ψ t y)/‖y j‖ =
      ∑ s : Spins N, ∫ x : Configuration N, ‖ψ.value (joinLists s t) (joinLists x y)‖^2/‖y j‖ := by
  simp only [formMass,Finset.sum_div,integral_div,coreSlice]

lemma coreSlice_mass_div_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (j : Fin M) :
    Integrable (fun y : Configuration M => formMass (coreSlice ψ t y)/‖y j‖) := by
  simp_rw [coreSlice_mass_div]
  apply integrable_finsetSum
  intro s _
  have hh := (integrable_join (N := N) (M := M) (nuclear_integrable
    (finSumFinEquiv (Sum.inr j)) (hψ.1 (joinLists s t))
    (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))).integral_prod_right
  simpa only [joinLists_right] using hh

lemma coreSlice_cross_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (j : Fin M) :
    Integrable (fun y : Configuration M => coreCoulombAt (coreSlice ψ t y) (y j)) := by
  unfold coreCoulombAt
  apply integrable_finsetSum
  intro s _
  apply integrable_finsetSum
  intro i _
  have hne : (finSumFinEquiv (Sum.inl i) : Fin (N+M)) ≠ finSumFinEquiv (Sum.inr j) := by
      intro h
      have hh := finSumFinEquiv.injective h
      cases hh
  have hh := (integrable_join (N := N) (M := M) (pair_integrable _ _ hne
    (hψ.1 (joinLists s t)) (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))).integral_prod_right
  simpa only [coreSlice,joinLists_left,joinLists_right] using hh

lemma integral_coreSlice_mass_div {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) :
    (∑ t : Spins M, ∫ y : Configuration M, ∑ j : Fin M, formMass (coreSlice ψ t y)/‖y j‖) =
      outNuclear ψ := by
  have hi (s : Spins N) (t : Spins M) (j : Fin M) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖ψ.value (joinLists s t) (joinLists x y)‖^2/‖y j‖) := by
    simpa only [joinLists_right] using (integrable_join (N := N) (M := M)
      (nuclear_integrable (finSumFinEquiv (Sum.inr j)) (hψ.1 (joinLists s t))
        (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))).integral_prod_right
  simp_rw [integral_finsetSum _ (fun j _ => coreSlice_mass_div_integrable hψ _ j),
    coreSlice_mass_div,integral_finsetSum _ (fun s _ => hi s _ _)]
  have he (s : Spins N) (t : Spins M) (j : Fin M) :
      (∫ y : Configuration M, ∫ x : Configuration N,
        ‖ψ.value (joinLists s t) (joinLists x y)‖^2/‖y j‖) =
      ∫ z, ‖ψ.value (joinLists s t) z‖^2/‖z (finSumFinEquiv (Sum.inr j))‖ := by
    simpa only [joinLists_right] using integral_join (N := N) (M := M)
      (nuclear_integrable (finSumFinEquiv (Sum.inr j)) (hψ.1 (joinLists s t))
        (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))
  simp_rw [he]
  conv_lhs => arg 2; ext t; rw [Finset.sum_comm]
  exact sum_spin_join (fun s => ∑ j : Fin M, ∫ z,
    ‖ψ.value s z‖^2/‖z (finSumFinEquiv (Sum.inr j))‖)

lemma integral_coreSlice_cross {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) :
    (∑ t : Spins M, ∫ y : Configuration M, ∑ j : Fin M, coreCoulombAt (coreSlice ψ t y) (y j)) =
      crossRepulsion ψ := by
  have hi (s : Spins N) (t : Spins M) (i : Fin N) (j : Fin M) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖ψ.value (joinLists s t) (joinLists x y)‖^2/‖x i-y j‖) := by
    have hne : (finSumFinEquiv (Sum.inl i) : Fin (N+M)) ≠ finSumFinEquiv (Sum.inr j) := by
      intro h
      have hh := finSumFinEquiv.injective h
      cases hh
    simpa only [joinLists_right,joinLists_left] using (integrable_join (N := N) (M := M)
      (pair_integrable _ _ hne (hψ.1 (joinLists s t))
        (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))).integral_prod_right
  simp_rw [integral_finsetSum _ (fun j _ => coreSlice_cross_integrable hψ _ j),coreCoulombAt,coreSlice]
  simp_rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ => hi s _ i _)),
    integral_finsetSum _ (fun i _ => hi _ _ i _)]
  have he (s : Spins N) (t : Spins M) (i : Fin N) (j : Fin M) :
      (∫ y : Configuration M, ∫ x : Configuration N,
        ‖ψ.value (joinLists s t) (joinLists x y)‖^2/‖x i-y j‖) =
      ∫ z, ‖ψ.value (joinLists s t) z‖^2/
        ‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inr j))‖ := by
    have hne : (finSumFinEquiv (Sum.inl i) : Fin (N+M)) ≠ finSumFinEquiv (Sum.inr j) := by
      intro h
      have hh := finSumFinEquiv.injective h
      cases hh
    simpa only [joinLists_right,joinLists_left] using integral_join (N := N) (M := M)
      (pair_integrable _ _ hne (hψ.1 (joinLists s t))
        (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))
  simp_rw [he]
  conv_lhs => arg 2; ext t; rw [Finset.sum_comm]; arg 2; ext s; rw [Finset.sum_comm]
  exact sum_spin_join (fun s => ∑ i : Fin N, ∑ j : Fin M, ∫ z,
    ‖ψ.value s z‖^2/‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inr j))‖)

def conditionalFieldSum {N M : ℕ} (Z lam : ℝ) (ψ : FormVector (N+M))
    (t : Spins M) (y : Configuration M) : ℝ :=
  formMass (coreSlice ψ t y)*∑ j : Fin M,
    normalizedCoreField Z lam (coreSlice ψ t y) (y j)

lemma conditionalFieldSum_ae {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam : ℝ) (t : Spins M) :
    conditionalFieldSum Z lam ψ t =ᵐ[volume]
      fun y => Z*(∑ j : Fin M, formMass (coreSlice ψ t y)/‖y j‖)-
        (∑ j : Fin M, coreCoulombAt (coreSlice ψ t y) (y j))-
        lam*M*formMass (coreSlice ψ t y) := by
  apply (hψ.ae_coreSlice t).mono
  intro y hy
  unfold conditionalFieldSum
  rw [Finset.mul_sum]
  simp_rw [mul_comm (formMass _),normalizedCoreField_mul_mass hy,mul_div_assoc]
  simp only [Finset.sum_sub_distrib,←Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

lemma conditionalFieldSum_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam : ℝ) (t : Spins M) :
    Integrable (conditionalFieldSum Z lam ψ t) := by
  have hi := ((integrable_finsetSum Finset.univ (fun j _ => coreSlice_mass_div_integrable hψ t j)).const_mul Z).sub
    (integrable_finsetSum Finset.univ (fun j _ => coreSlice_cross_integrable hψ t j))
  exact (hi.sub ((hψ.coreSlice_mass_integrable t).const_mul (lam*M))).congr
    (conditionalFieldSum_ae hψ Z lam t).symm

lemma integral_conditionalFieldSum {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam : ℝ) :
    (∑ t : Spins M, ∫ y, conditionalFieldSum Z lam ψ t y) =
      Z*outNuclear ψ-crossRepulsion ψ-lam*M*formMass ψ := by
  have ht (t : Spins M) : (∫ y, conditionalFieldSum Z lam ψ t y) =
      Z*(∫ y, ∑ j : Fin M, formMass (coreSlice ψ t y)/‖y j‖)-
      (∫ y, ∑ j : Fin M, coreCoulombAt (coreSlice ψ t y) (y j))-
      lam*M*(∫ y, formMass (coreSlice ψ t y)) := by
    rw [integral_congr_ae (conditionalFieldSum_ae hψ Z lam t)]
    have hi := (integrable_finsetSum Finset.univ (fun j _ => coreSlice_mass_div_integrable hψ t j)).const_mul Z
    have hj := integrable_finsetSum Finset.univ (fun j _ => coreSlice_cross_integrable hψ t j)
    rw [integral_sub (f := fun y => Z*(∑ j : Fin M, formMass (coreSlice ψ t y)/‖y j‖)-
      (∑ j : Fin M, coreCoulombAt (coreSlice ψ t y) (y j)))
      (g := fun y => lam*M*formMass (coreSlice ψ t y))
      (hi.sub hj) ((hψ.coreSlice_mass_integrable t).const_mul (lam*M)),
      integral_sub hi hj,integral_const_mul,integral_const_mul]
  simp_rw [ht]
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,
    integral_coreSlice_mass_div hψ,integral_coreSlice_cross hψ,hψ.integral_coreSlice_mass]

theorem priced_conditional_energy_identity {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam : ℝ) :
    formEnergy Z ψ+lam*(N+M)*formMass ψ =
      (∑ t : Spins M, ∫ y, formEnergy Z (coreSlice ψ t y)+
        lam*N*formMass (coreSlice ψ t y))+
      outKinetic ψ-(∑ t : Spins M, ∫ y, conditionalFieldSum Z lam ψ t y)+
      outRepulsion ψ := by
  have ht (t : Spins M) : (∫ y, formEnergy Z (coreSlice ψ t y)+
      lam*N*formMass (coreSlice ψ t y)) =
      (∫ y, formEnergy Z (coreSlice ψ t y))+lam*N*(∫ y, formMass (coreSlice ψ t y)) := by
    rw [integral_add (hψ.coreSlice_energy_integrable Z t)
      ((hψ.coreSlice_mass_integrable t).const_mul (lam*N)),integral_const_mul]
  simp_rw [ht]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,hψ.integral_coreSlice_mass,
    integrated_core_parts hψ Z,integral_conditionalFieldSum hψ Z lam,
    formEnergy_core_out_cross]
  ring

theorem fresh_cut_priced_localization_identity {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevVector ψ) (Z lam : ℝ) :
    formEnergy Z ψ+lam*L*formMass ψ+
        (1/2:ℝ)*weightedParticleCount ψ (spatialErrorWeight p) =
      (∑ b : Fin L → Fin 2, ∑ t : Spins (cutOutNumber b), ∫ y,
        formEnergy Z (coreSlice (orderedCutForm p hp ψ b) t y)+
          lam*cutCoreNumber b*formMass (coreSlice (orderedCutForm p hp ψ b) t y))+
      (∑ b : Fin L → Fin 2, outKinetic (orderedCutForm p hp ψ b))-
      (∑ b : Fin L → Fin 2, ∑ t : Spins (cutOutNumber b), ∫ y,
        conditionalFieldSum Z lam (orderedCutForm p hp ψ b) t y)+
      (∑ b : Fin L → Fin 2, outRepulsion (orderedCutForm p hp ψ b)) := by
  have hb (b : Fin L → Fin 2) := priced_conditional_energy_identity
    (orderedCutForm_sobolev p hp hψ b) Z lam
  have hcard (b : Fin L → Fin 2) : (cutCoreNumber b : ℝ)+cutOutNumber b = L := by
    exact_mod_cast cutNumbers_sum b
  simp_rw [hcard,orderedCutForm_energy,orderedCutForm_mass] at hb
  have hsum := congrArg (fun f : (Fin L → Fin 2) → ℝ => ∑ b, f b) (funext hb)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib] at hsum
  rw [←Finset.mul_sum,spatial_cut_mass p hp hψ,spatial_cut_ims p hp hψ Z] at hsum
  have hw : (∑ s : Spins L, ∑ i : Fin L, ∫ x,
      spatialErrorWeight p (x i)*‖ψ.value s x‖^2) =
      weightedParticleCount ψ (spatialErrorWeight p) := rfl
  rw [hw] at hsum
  linarith

end CoulombAtom

end

end OAI
