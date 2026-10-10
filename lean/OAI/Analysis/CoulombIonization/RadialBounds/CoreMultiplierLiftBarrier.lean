import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CutCoreNumber
import OAI.Analysis.CoulombIonization.Variational.TensorLp

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CoreMultiplierLift_barrier_scope

open MeasureTheory Filter
open scoped BigOperators ContDiff

def coreLeftLinear (N M : ℕ) : Configuration (N+M) →L[ℝ] Configuration N :=
  (ContinuousLinearMap.fst ℝ (Configuration N) (Configuration M)).comp
    (configurationJoin N M).symm.toContinuousLinearMap

lemma coreLeftLinear_apply {N M : ℕ} (x : Configuration (N+M)) :
    coreLeftLinear N M x = leftList x := by
  simp only [coreLeftLinear,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,configurationJoin_symm_apply]
  rfl

lemma coreLeftLinear_direction_left {N M : ℕ} (i : Fin N) (a : Fin 3) :
    coreLeftLinear N M (direction (finSumFinEquiv (Sum.inl i)) a) = direction i a := by
  rw [←configurationJoin_direction]
  simp only [coreLeftLinear,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply]
  rfl

lemma coreLeftLinear_direction_right {N M : ℕ} (i : Fin M) (a : Fin 3) :
    coreLeftLinear N M (direction (finSumFinEquiv (Sum.inr i)) a) = 0 := by
  rw [←configurationJoin_direction_right]
  simp only [coreLeftLinear,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply]
  rfl

def coreLiftValue {N : ℕ} (M : ℕ) (p : SmoothMultiplier (sectorDirections N)) :
    Configuration (N+M) → ℝ := p.value ∘ coreLeftLinear N M

lemma coreLiftValue_regular {N : ℕ} (M : ℕ) (p : SmoothMultiplier (sectorDirections N)) :
    ContDiff ℝ ∞ (coreLiftValue M p) := p.regular.comp (coreLeftLinear N M).contDiff

lemma coreLiftValue_derivative {N : ℕ} (M : ℕ) (p : SmoothMultiplier (sectorDirections N))
    (x v : Configuration (N+M)) :
    lineDeriv ℝ (coreLiftValue M p) x v =
      lineDeriv ℝ p.value (coreLeftLinear N M x) (coreLeftLinear N M v) := by
  rw [((coreLiftValue_regular M p).differentiable (by simp) x).lineDeriv_eq_fderiv,
    (p.regular.differentiable (by simp) _).lineDeriv_eq_fderiv]
  have hh := (p.regular.differentiable (by simp) (coreLeftLinear N M x)).hasFDerivAt.comp
    x (coreLeftLinear N M).hasFDerivAt
  exact congrArg (fun A : Configuration (N+M) →L[ℝ] ℝ => A v) hh.fderiv

def coreLiftMultiplier {N : ℕ} (M : ℕ) (p : SmoothMultiplier (sectorDirections N)) :
    SmoothMultiplier (sectorDirections (N+M)) where
  value := coreLiftValue M p
  regular := coreLiftValue_regular M p
  bound := by
    obtain ⟨C,hC⟩ := p.bound
    exact ⟨C,fun x => hC (coreLeftLinear N M x)⟩
  gradient_bound := by
    intro j
    obtain ⟨i,hi⟩ := finSumFinEquiv.surjective j.1
    cases i with
    | inl i =>
      obtain ⟨C,hC⟩ := p.gradient_bound (i,j.2)
      refine ⟨C,fun x => ?_⟩
      change |lineDeriv ℝ (coreLiftValue M p) x (direction j.1 j.2)| ≤ C
      rw [←hi,coreLiftValue_derivative,coreLeftLinear_direction_left]
      exact hC _
    | inr i =>
      refine ⟨0,fun x => ?_⟩
      change |lineDeriv ℝ (coreLiftValue M p) x (direction j.1 j.2)| ≤ 0
      rw [←hi,coreLiftValue_derivative,coreLeftLinear_direction_right]
      simp only [lineDeriv_zero,abs_zero,le_refl]

lemma coreSlice_coreLiftMultiplier {N M : ℕ} (ψ : FormVector (N+M))
    (p : SmoothMultiplier (sectorDirections N)) (t : Spins M) (y : Configuration M) :
    coreSlice (multiplyForm (coreLiftMultiplier M p) ψ) t y =
      multiplyForm p (coreSlice ψ t y) := by
  apply congrArg₂ FormVector.mk
  · funext s x
    simp only [coreSlice,multiplyForm,coreLiftMultiplier,coreLiftValue,
      Function.comp_apply,coreLeftLinear_apply,leftList_join]
  · funext s i a x
    change (coreLiftValue M p (joinLists x y) : ℂ)*_+
      Complex.ofReal (lineDeriv ℝ (coreLiftValue M p) (joinLists x y)
        (direction (finSumFinEquiv (Sum.inl i)) a))*_ = _
    rw [coreLiftValue_derivative,coreLeftLinear_direction_left,coreLeftLinear_apply,leftList_join]
    simp only [coreLiftValue,Function.comp_apply,coreLeftLinear_apply,leftList_join,
      coreSlice]

lemma SobolevVector.coreSlice_cut_mass_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (p : SmoothMultiplier (sectorDirections N)) (t : Spins M) :
    Integrable (fun y => formMass (multiplyForm p (coreSlice ψ t y))) := by
  simpa only [coreSlice_coreLiftMultiplier] using
    (hψ.multiply (coreLiftMultiplier M p)).coreSlice_mass_integrable t

lemma SobolevVector.coreSlice_cut_energy_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (p : SmoothMultiplier (sectorDirections N)) (t : Spins M) (Z : ℝ) :
    Integrable (fun y => formEnergy Z (multiplyForm p (coreSlice ψ t y))) := by
  simpa only [coreSlice_coreLiftMultiplier] using
    (hψ.multiply (coreLiftMultiplier M p)).coreSlice_energy_integrable Z t

end Work_CoreMultiplierLift_barrier_scope

open MeasureTheory Filter
open scoped BigOperators

def liftCoreOrder {K N : ℕ} (M : ℕ) (e : Fin K ≃ Fin N) :
    Fin (K+M) ≃ Fin (N+M) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl (Fin M))).trans finSumFinEquiv)

@[simp] lemma liftCoreOrder_left {K N M : ℕ} (e : Fin K ≃ Fin N) (i : Fin K) :
    liftCoreOrder M e (finSumFinEquiv (Sum.inl i)) = finSumFinEquiv (Sum.inl (e i)) := by
  simp [liftCoreOrder]

@[simp] lemma liftCoreOrder_right {K N M : ℕ} (e : Fin K ≃ Fin N) (i : Fin M) :
    liftCoreOrder M e (finSumFinEquiv (Sum.inr i)) = finSumFinEquiv (Sum.inr i) := by
  simp [liftCoreOrder]

lemma liftCoreOrder_symm {K N M : ℕ} (e : Fin K ≃ Fin N) :
    (liftCoreOrder M e).symm = liftCoreOrder M e.symm := by
  rfl

lemma joinLists_order {α : Type*} {K N M : ℕ} (e : Fin K ≃ Fin N)
    (s : Fin K → α) (t : Fin M → α) :
    joinLists s t ∘ (liftCoreOrder M e).symm = joinLists (s ∘ e.symm) t := by
  funext i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  cases j <;> simp only [Function.comp_apply,liftCoreOrder_symm,
    liftCoreOrder_left,liftCoreOrder_right,joinLists_left,joinLists_right]

lemma coreSlice_reindex_lift {K N M : ℕ} (e : Fin K ≃ Fin N)
    (ψ : FormVector (N+M)) (s : Spins M) (u : Configuration M) :
    coreSlice (reindexForm (liftCoreOrder M e) ψ) s u =
      reindexForm e (coreSlice ψ s u) := by
  apply congrArg₂ FormVector.mk
  · funext t x
    change ψ.value _ _ = ψ.value _ _
    rw [joinLists_order,joinLists_order]
  · funext t i a x
    change ψ.gradient _ _ _ _ = ψ.gradient _ _ _ _
    rw [joinLists_order,joinLists_order,liftCoreOrder_left]

lemma liftCoreOrder_perm_comp {α : Type*} {K N M : ℕ} (e : Fin K ≃ Fin N)
    (π : Equiv.Perm (Fin K)) (f : Fin (K+M) → α) :
    (f ∘ corePerm M π) ∘ (liftCoreOrder M e).symm =
      (f ∘ (liftCoreOrder M e).symm) ∘ corePerm M (e.permCongr π) := by
  funext i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  cases j <;> simp [Function.comp_apply,corePerm,liftCoreOrder,Equiv.permCongr_apply]

lemma CoreAntisymmetric.reindex_lift {K N M : ℕ} {ψ : FormVector (N+M)}
    (ha : CoreAntisymmetric ψ) (e : Fin K ≃ Fin N) :
    CoreAntisymmetric (reindexForm (liftCoreOrder M e) ψ) := by
  intro π s
  have hh := (configurationReindex_preserving (liftCoreOrder M e)).quasiMeasurePreserving.ae
    (ha (e.permCongr π) (s ∘ (liftCoreOrder M e).symm))
  filter_upwards [hh] with x hx
  change ψ.value ((s ∘ corePerm M π) ∘ (liftCoreOrder M e).symm)
    ((x ∘ corePerm M π) ∘ (liftCoreOrder M e).symm) = _
  rw [liftCoreOrder_perm_comp,liftCoreOrder_perm_comp]
  simpa only [configurationReindex_apply,Equiv.Perm.sign_permCongr,reindexForm] using hx

def repeatedCutForm {N M : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector (N+M)) (c : Fin N → Fin 2) :
    FormVector ((cutCoreNumber c+cutOutNumber c)+M) :=
  reindexForm (liftCoreOrder M (cutOrder c))
    (multiplyForm (coreLiftMultiplier M (spatialProduct p hp c)) ψ)

lemma repeatedCutForm_sobolev {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2) :
    SobolevVector (repeatedCutForm p hp ψ c) := (hψ.multiply _).reindex _

lemma repeatedCutForm_slice {N M : ℕ} (ψ : FormVector (N+M))
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2)
    (s : Spins M) (u : Configuration M) :
    coreSlice (repeatedCutForm p hp ψ c) s u = orderedCutForm p hp (coreSlice ψ s u) c := by
  unfold repeatedCutForm
  rw [coreSlice_reindex_lift,coreSlice_coreLiftMultiplier]
  rfl

end CoulombAtom

end

end OAI
