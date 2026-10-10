import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.Slater
import OAI.Analysis.CoulombIonization.FormDomain.FiniteFermionEnsemble

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

theorem price_le_correlated_finite_insertion {N n : ℕ} {ψ : FormVector N}
    (hψ : FormAdmissible ψ) {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (hsep : ∀ i s, Disjoint A (tsupport (fun y : Space => φ i (s,y))))
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) {p : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    priceEnergy (energy Z) lam ≤ formEnergy Z ψ + lam * N +
      finiteOccupationEnergy Z lam p φ + ∑ i : Fin n, p i * orbitalCoreInteraction ψ (φ i) := by
  have he (m : Fin n → Bool) : priceEnergy (energy Z) lam ≤
      (formEnergy Z ψ + lam*N) +
      (formEnergy Z (slaterForm (occupationOrbitals φ m)) + lam * Fintype.card (Occupied m)) +
      blockTensorCross ψ (slaterForm (occupationOrbitals φ m)) := by
    have ha := occupationSlater_admissible hφ hc ho m
    have hb := energy_le_block_insertion hZ hψ ha A hcore (occupationSlater_outside φ A hsep m)
    have ht := quantum_price_le_sector hZ hlam (N + Fintype.card (Occupied m))
    push_cast at ht
    linarith
  have hm := occupation_mean_lower hp _ he
  simp only [mul_add,Finset.sum_add_distrib] at hm
  rw [← Finset.sum_mul,occupationWeight_sum,one_mul,
    occupationSlater_cross hψ.sobolevFermion.sobolevVector hφ hc ho] at hm
  simp only [← Finset.sum_mul,occupationWeight_sum,one_mul] at hm
  have hb := occupationSlater_energy_le hφ hc ho Z lam p
  simp only [mul_add,Finset.sum_add_distrib] at hb
  linarith

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

def spinLift (u : Space → ℂ) (σ : Fin 2) (z : SlaterParticle) : ℂ := if z.1=σ then u z.2 else 0

lemma spinLift_smooth {u : Space → ℂ} (hu : ContDiff ℝ ∞ u) (σ s : Fin 2) :
    ContDiff ℝ ∞ (fun x : Space => spinLift u σ (s,x)) := by
  by_cases h : s=σ <;> simp only [spinLift,h,ite_true,ite_false]
  · exact hu
  · exact contDiff_const

lemma spinLift_compact {u : Space → ℂ} (hu : HasCompactSupport u) (σ s : Fin 2) :
    HasCompactSupport (fun x : Space => spinLift u σ (s,x)) := by
  by_cases h : s=σ <;> simp only [spinLift,h,ite_true,ite_false]
  · exact hu
  · exact HasCompactSupport.zero

lemma spinLift_separated {u : Space → ℂ} {A : Set Space}
    (hu : Disjoint A (tsupport u)) (σ s : Fin 2) :
    Disjoint A (tsupport (fun x : Space => spinLift u σ (s,x))) := by
  by_cases h : s=σ <;> simp only [spinLift,h,ite_true,ite_false]
  · exact hu
  · simp

lemma spinLift_fderiv (u : Space → ℂ) (σ s : Fin 2) (x v : Space) :
    fderiv ℝ (fun y : Space => spinLift u σ (s,y)) x v =
      spinLift (fun y => fderiv ℝ u y v) σ (s,x) := by
  by_cases h : s=σ <;> simp [spinLift,h]

lemma spinLift_inner (u v : Space → ℂ) (σ τ : Fin 2) :
    (∫ z : SlaterParticle, conj (spinLift u σ z) * spinLift v τ z ∂slaterParticleMeasure) =
      if σ=τ then ∫ x : Space, conj (u x)*v x else 0 := by
  have he (z : SlaterParticle) : conj (spinLift u σ z) * spinLift v τ z =
      (if z.1=σ ∧ z.1=τ then (1:ℂ) else 0) * (conj (u z.2)*v z.2) := by
    simp only [spinLift]
    (split_ifs <;> simp_all); aesop
  simp_rw [he]
  rw [show slaterParticleMeasure = Measure.count.prod volume from rfl,
    integral_prod_mul (fun s : Fin 2 => if s=σ ∧ s=τ then (1:ℂ) else 0)
      (fun x : Space => conj (u x)*v x),integral_count]
  by_cases h : σ=τ
  · subst τ
    simp
  · have hz : (fun s : Fin 2 => if s=σ ∧ s=τ then (1:ℂ) else 0) = 0 := by
      funext s
      simp only [Pi.zero_apply,ite_eq_right_iff,one_ne_zero,imp_false]
      exact fun hs => h (hs.1.symm.trans hs.2)
    simp only [hz,Pi.zero_apply,Finset.sum_const_zero,zero_mul,ite_eq_right h]

lemma spinLift_weight (u : Space → ℂ) (σ : Fin 2) (W : Space → ℝ) :
    (∫ z : SlaterParticle, W z.2 * ‖spinLift u σ z‖^2 ∂slaterParticleMeasure) =
      ∫ x : Space, W x * ‖u x‖^2 := by
  have he (z : SlaterParticle) : W z.2 * ‖spinLift u σ z‖^2 =
      (if z.1=σ then (1:ℝ) else 0) * (W z.2 * ‖u z.2‖^2) := by
    by_cases h : z.1=σ <;> simp [spinLift,h]
  simp_rw [he]
  rw [show slaterParticleMeasure = Measure.count.prod volume from rfl,
    integral_prod_mul (fun s : Fin 2 => if s=σ then (1:ℝ) else 0)
      (fun x : Space => W x*‖u x‖^2),integral_count]
  simp

lemma spinLift_mass (u : Space → ℂ) (σ : Fin 2) :
    (∫ z : SlaterParticle, ‖spinLift u σ z‖^2 ∂slaterParticleMeasure) = ∫ x : Space, ‖u x‖^2 := by
  simpa only [one_mul] using spinLift_weight u σ (fun _ => 1)

lemma spinLift_derivative_mass (u : Space → ℂ) (σ : Fin 2) (v : Space) :
    (∫ z : SlaterParticle, ‖fderiv ℝ (fun y : Space => spinLift u σ (z.1,y)) z.2 v‖^2
      ∂slaterParticleMeasure) = ∫ x : Space, ‖fderiv ℝ u x v‖^2 := by
  simp_rw [spinLift_fderiv]
  exact spinLift_mass _ σ

lemma spinSpace_integral_spatial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Space → E) : (∫ z : SlaterParticle, F z.2 ∂slaterParticleMeasure) = (2:ℝ) • ∫ x : Space, F x := by
  have he := integral_prod_smul (μ := (Measure.count : Measure (Fin 2))) (ν := volume)
    (fun _ : Fin 2 => (1:ℝ)) F
  simpa [integral_count,slaterParticleMeasure] using he

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

universe u

def finiteOrbitalDensity {ι : Type u} [Fintype ι] (p : ι → ℝ)
    (φ : ι → SlaterParticle → ℂ) (z : SlaterParticle) : ℝ := ∑ i, p i * ‖φ i z‖^2

def finiteOrbitalKinetic {ι : Type u} [Fintype ι] (p : ι → ℝ)
    (φ : ι → SlaterParticle → ℂ) : ℝ :=
  (1/2:ℝ) * ∑ a : Fin 3, ∑ i, p i * ∫ z : SlaterParticle,
    ‖fderiv ℝ (fun x : Space => φ i (z.1,x)) z.2 (EuclideanSpace.single a 1)‖^2 ∂slaterParticleMeasure

def finiteOrbitalEnergy {ι : Type u} [Fintype ι] (Z lam : ℝ) (p : ι → ℝ)
    (φ : ι → SlaterParticle → ℂ) : ℝ :=
  finiteOrbitalKinetic p φ -
    Z * ∑ i, p i * ∫ z : SlaterParticle, ‖φ i z‖^2 / ‖z.2‖ ∂slaterParticleMeasure +
    (1/2:ℝ) * ∫ z : SlaterParticle × SlaterParticle,
      (finiteOrbitalDensity p φ z.1 * finiteOrbitalDensity p φ z.2) / ‖z.1.2-z.2.2‖
        ∂slaterParticleMeasure.prod slaterParticleMeasure + lam * ∑ i, p i

lemma finiteOrbitalEnergy_reindex {ι : Type u} [Fintype ι] {n : ℕ}
    (e : Fin n ≃ ι) (Z lam : ℝ) (p : ι → ℝ) (φ : ι → SlaterParticle → ℂ) :
    finiteOccupationEnergy Z lam (p ∘ e) (φ ∘ e) = finiteOrbitalEnergy Z lam p φ := by
  unfold finiteOccupationEnergy finiteOrbitalEnergy finiteOrbitalKinetic spatialOrbitalDerivative
  simp only [Function.comp_apply]
  have hd (z : SlaterParticle) : weightedSlaterDensity (p ∘ e) (φ ∘ e) z = finiteOrbitalDensity p φ z :=
    e.sum_comp (fun i => p i * ‖φ i z‖^2)
  simp only [hd]
  have hk (a : Fin 3) :
      (∑ j : Fin n, p (e j) * ∫ z : SlaterParticle,
        ‖fderiv ℝ (fun x : Space => φ (e j) (z.1,x)) z.2 (EuclideanSpace.single a 1)‖^2 ∂slaterParticleMeasure) =
      ∑ i, p i * ∫ z : SlaterParticle,
        ‖fderiv ℝ (fun x : Space => φ i (z.1,x)) z.2 (EuclideanSpace.single a 1)‖^2 ∂slaterParticleMeasure :=
    e.sum_comp (fun i => p i * ∫ z : SlaterParticle,
      ‖fderiv ℝ (fun x : Space => φ i (z.1,x)) z.2 (EuclideanSpace.single a 1)‖^2 ∂slaterParticleMeasure)
  have hn : (∑ j : Fin n, p (e j) * ∫ z : SlaterParticle, ‖φ (e j) z‖^2 / ‖z.2‖ ∂slaterParticleMeasure) =
      ∑ i, p i * ∫ z : SlaterParticle, ‖φ i z‖^2 / ‖z.2‖ ∂slaterParticleMeasure :=
    e.sum_comp (fun i => p i * ∫ z : SlaterParticle, ‖φ i z‖^2 / ‖z.2‖ ∂slaterParticleMeasure)
  simp only [hk,hn,e.sum_comp p]

theorem price_le_correlated_fintype_insertion {ι : Type u} [Fintype ι] [DecidableEq ι]
    {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ) {φ : ι → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (hsep : ∀ i s, Disjoint A (tsupport (fun y : Space => φ i (s,y))))
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    priceEnergy (energy Z) lam ≤ formEnergy Z ψ + lam * N +
      finiteOrbitalEnergy Z lam p φ + ∑ i, p i * orbitalCoreInteraction ψ (φ i) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have ho' (i j) : (∫ z, conj ((φ ∘ e) i z)*(φ ∘ e) j z ∂slaterParticleMeasure) =
      if i=j then 1 else 0 := by
    simp only [Function.comp_apply, ho, Equiv.apply_eq_iff_eq]
  have h := price_le_correlated_finite_insertion hψ (fun i s => hφ (e i) s)
    (fun i s => hc (e i) s) ho' A hcore (fun i s => hsep (e i) s) hZ hlam (fun i => hp (e i))
  change priceEnergy (energy Z) lam ≤ formEnergy Z ψ + lam * N +
    finiteOccupationEnergy Z lam (p ∘ e) (φ ∘ e) +
      ∑ i, p (e i) * orbitalCoreInteraction ψ (φ (e i)) at h
  rw [finiteOrbitalEnergy_reindex e Z lam p φ] at h
  convert h using 1
  congr 1
  exact (e.sum_comp (fun i => p i * orbitalCoreInteraction ψ (φ i))).symm

end CoulombAtom

end

end OAI
