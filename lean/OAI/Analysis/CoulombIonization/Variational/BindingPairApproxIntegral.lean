import Mathlib
import OAI.Analysis.CoulombIonization.Variational.BindingWeightContinuous

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators

lemma bindingPairApprox_integral_le {N : ℕ} (n : ℕ) (i j : Fin N)
    {f : Configuration N → ℂ} (hf : MemLp f 2)
    (hij : Integrable (fun x => ‖f x‖ ^ 2 / ‖x i-x j‖)) :
    (∫ x, bindingPairApprox n i j x * ‖f x‖ ^ 2) ≤
      (∫ x, bindingApprox n (x i) * (‖f x‖ ^ 2 / ‖x i-x j‖)) +
      (∫ x, bindingApprox n (x j) * (‖f x‖ ^ 2 / ‖x i-x j‖)) := by
  rw [← integral_add (bindingApprox_integrable n i hij) (bindingApprox_integrable n j hij)]
  apply integral_mono (bindingPairApprox_integrable n i j hf)
    ((bindingApprox_integrable n i hij).add (bindingApprox_integrable n j hij))
  intro x
  calc
    _ ≤ ((bindingApprox n (x i) + bindingApprox n (x j)) / ‖x i-x j‖) * ‖f x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
    _ = _ := by dsimp only [Pi.add_apply]; ring

lemma bindingPairApprox_integral_le_rev {N : ℕ} (n : ℕ) (i j : Fin N)
    {f : Configuration N → ℂ} (hf : MemLp f 2)
    (hij : Integrable (fun x => ‖f x‖ ^ 2 / ‖x i-x j‖)) :
    (∫ x, bindingPairApprox n i j x * ‖f x‖ ^ 2) ≤
      (∫ x, bindingApprox n (x i) * (‖f x‖ ^ 2 / ‖x i-x j‖)) +
      (∫ x, bindingApprox n (x j) * (‖f x‖ ^ 2 / ‖x j-x i‖)) := by
  have he : (∫ x, bindingApprox n (x j) * (‖f x‖ ^ 2 / ‖x i-x j‖)) =
      ∫ x, bindingApprox n (x j) * (‖f x‖ ^ 2 / ‖x j-x i‖) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [norm_sub_rev (x i) (x j)]
  exact (bindingPairApprox_integral_le n i j hf hij).trans_eq (congrArg _ he)

lemma sum_pair_bound {α : Type*} [Fintype α] (A B : α → α → ℝ)
    (h : ∀ i j, B i j ≤ A i j + A j i) :
    (∑ i, ∑ j, B i j) ≤ 2*(∑ i, ∑ j, A i j) := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => h i j))
  simp only [Finset.sum_add_distrib] at hh
  have hc : (∑ i, ∑ j, A j i) = ∑ i, ∑ j, A i j := Finset.sum_comm
  rw [hc] at hh
  linarith

lemma sum_excluding_const {N : ℕ} (i : Fin (N+1)) (c : ℝ) :
    (∑ j : Fin (N+1), if i ≠ j then c else 0) = (N:ℝ)*c := by
  have hh := sum_excluding_add i (fun _ => c)
  simp only [ne_eq, ne_comm, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hh
  linarith


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

section

lemma integral_weighted_deletedDensity {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (Z : ℝ) (s : Spins N) (i : Fin N)
    (w : Configuration N → ℝ) (hw : Continuous w) {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) :
    (∫ x, w x * quantumEnergyDensity Z ψ s x) =
      (∫ x, w x * quantumCoreDensity Z ψ i s x) +
      (1/2:ℝ) * (∑ a : Fin 3, ∫ x, w x * ‖ψ.gradient s i a x‖ ^ 2) -
      Z * (∫ x, w x * (‖ψ.value s x‖ ^ 2 / ‖x i‖)) +
      (∑ j : Fin N, ∫ x, w x * (if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)) := by
  classical
  have hc := weighted_integrable (hψ.quantumCoreDensity_integrable Z i s) hw hC
  have hk (a : Fin 3) := weighted_integrable (hψ.2.1 s i a).norm.integrable_sq hw hC
  have hn := weighted_integrable
    (nuclear_integrable i (hψ.1 s) (hψ.2.1 s i) (hψ.2.2.1 s i)) hw hC
  have hp (j : Fin N) : Integrable (fun x => w x *
      (if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)) := by
    split_ifs with hij
    · exact weighted_integrable (pair_integrable i j hij (hψ.1 s)
        (hψ.2.1 s i) (hψ.2.2.1 s i)) hw hC
    · simp only [mul_zero]; exact integrable_zero _ _ _
  have hks := integrable_finsetSum Finset.univ (fun a _ => hk a)
  have hps := integrable_finsetSum Finset.univ (fun j _ => hp j)
  have he : (∫ x, w x * quantumEnergyDensity Z ψ s x) =
      ∫ x, w x * quantumCoreDensity Z ψ i s x +
        (1/2:ℝ) * (∑ a : Fin 3, w x * ‖ψ.gradient s i a x‖ ^ 2) -
        Z * (w x * (‖ψ.value s x‖ ^ 2 / ‖x i‖)) +
        (∑ j : Fin N, w x * (if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [quantumEnergyDensity_delete Z ψ i s x]
      simp only [mul_add, mul_sub, mul_left_comm (w x) (1/2:ℝ),
        mul_left_comm (w x) Z, Finset.mul_sum]
  have ha := integral_add ((hc.add (hks.const_mul (1/2:ℝ))).sub (hn.const_mul Z)) hps
  have hb := integral_sub (hc.add (hks.const_mul (1/2:ℝ))) (hn.const_mul Z)
  have hd := integral_add hc (hks.const_mul (1/2:ℝ))
  simp only [Pi.sub_apply, Pi.add_apply] at ha hb hd
  rw [he, ha, hb, hd]
  simp only [integral_const_mul]
  rw [integral_finsetSum _ (fun a _ => hk a), integral_finsetSum _ (fun j _ => hp j)]

attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply

lemma binding_total_kinetic_lower {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : fermionGraph N) :
    (∑ s : Spins N, ∑ i : Fin N, ((∑ j : Fin N, ∑ a : Fin 3, ∫ x, bindingWeight R ε (x i) *
        ‖graphComponent s (some (j,a)) F x‖ ^ 2) -
      (∑ a : Fin 3, ∫ x, bindingWeight R ε (x i) * ‖graphComponent s (some (i,a)) F x‖ ^ 2))) ≤
      ∑ s : Spins N, ∑ j : Fin N, ∑ a : Fin 3, (⟪graphComponent s (some (j,a)) ((bindingTotalMultiplier hR hε).apply F),
        graphComponent s (some (j,a)) F⟫_ℂ).re := by
  classical
  have h (s : Spins N) := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => bindingKinetic_lower hR hε (F.val s) i)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun s _ => h s)
  simp only [← graphComponent_apply] at hs
  apply le_trans hs
  apply le_of_eq
  apply Finset.sum_congr rfl; intro s _
  simp only [bindingTotalMultiplier_component, sum_inner, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_comm]

end
section

attribute [local irreducible] graphNuclear graphPair graphComponent graphFormVector FermionMultiplier.apply coulombFormOperator fermionGraph weakGraph fermionGraphValue

lemma integral_weighted_quantumDensity_ordered {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (Z : ℝ) (s : Spins N)
    (w : Configuration N → ℝ) (hw : Continuous w) {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) :
    (∫ x, w x * quantumEnergyDensity Z ψ s x) =
      (1/2:ℝ) * (∑ i : Fin N, ∑ a : Fin 3, ∫ x, w x * ‖ψ.gradient s i a x‖ ^ 2) -
      Z * (∑ i : Fin N, ∫ x, w x * (‖ψ.value s x‖ ^ 2 / ‖x i‖)) +
      (∑ i : Fin N, ∑ j : Fin N, if i < j then (∫ x, w x * (‖ψ.value s x‖ ^ 2 / ‖x i-x j‖)) else 0) := by
  classical
  have hp (i j : Fin N) : (∫ x, w x * (‖ψ.value s x‖ ^ 2 / ‖x i-x j‖)) =
      ∫ x, w x * (‖ψ.value s x‖ ^ 2 / ‖x j-x i‖) := by simp only [norm_sub_rev]
  have hi (i j : Fin N) :
      (∫ x, w x * (if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)) =
      if i ≠ j then (∫ x, w x * (‖ψ.value s x‖ ^ 2 / ‖x i-x j‖)) else 0 := by
    split_ifs <;> simp
  rw [integral_weighted_quantumDensity hψ Z s w hw hC]
  simp only [hi]
  rw [← sum_pairs_half _ hp]

lemma FermionMultiplier.density_weighted_identity {N : ℕ} (Z : ℝ) (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) :
    (∫ x, p.value x * quantumEnergyDensity Z (graphFormVector F) s x) =
      (1/2:ℝ) * (∑ i : Fin N, ∑ a : Fin 3, ∫ x, p.value x * ‖graphComponent s (some (i,a)) F x‖ ^ 2) -
      Z * (∑ i : Fin N, ∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i‖)) +
      (∑ i : Fin N, ∑ j : Fin N, if i < j then
        (∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i-x j‖)) else 0) := by
  let C : ℝ := Classical.choose p.toSmoothMultiplier.bound
  have hC : ∀ x, |p.value x| ≤ C := Classical.choose_spec p.toSmoothMultiplier.bound
  have hCp (x : Configuration N) : ‖p.value x‖ ≤ C := by
    simpa only [Real.norm_eq_abs] using hC x
  simpa only [graphFormVector_value_eq, graphFormVector_gradient_eq] using
    integral_weighted_quantumDensity_ordered (graphFormVector_sobolev F) Z s p.value p.regular.continuous hCp

lemma FermionMultiplier.operator_weighted_pairing {N : ℕ} (Z : ℝ) (p : FermionMultiplier N)
    (F : fermionGraph N) :
    (⟪p.apply F, coulombFormOperator Z N F⟫_ℂ).re =
      (1/2:ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        (⟪graphComponent s (some (i,a)) (p.apply F), graphComponent s (some (i,a)) F⟫_ℂ).re) -
      Z * (∑ s : Spins N, ∑ i : Fin N, ∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i‖)) +
      (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N, if i < j then
        (∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i-x j‖)) else 0) := by
  have hh := coulombFormOperator_pairing Z N F (p.apply F)
  simpa only [p.nuclear_weighted_pairing, p.pair_weighted_pairing, dite_eq_ite] using hh

lemma weighted_form_algebra (Z K G V W D A : ℝ)
    (hd : D = (1/2:ℝ)*K-Z*V+W) (ha : A = (1/2:ℝ)*G-Z*V+W) :
    A = D+(1/2:ℝ)*(G-K) := by rw [hd, ha]; ring

lemma FermionMultiplier.density_weighted_sum {N : ℕ} (Z : ℝ) (p : FermionMultiplier N)
    (F : fermionGraph N) :
    (∑ s : Spins N, ∫ x, p.value x * quantumEnergyDensity Z (graphFormVector F) s x) =
      (1/2:ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        ∫ x, p.value x * ‖graphComponent s (some (i,a)) F x‖ ^ 2) -
      Z * (∑ s : Spins N, ∑ i : Fin N,
        ∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i‖)) +
      (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N, if i < j then
        (∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i-x j‖)) else 0) := by
  classical
  have he := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun s _ => p.density_weighted_identity Z F s)
  simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] using he

lemma FermionMultiplier.form_weighted_identity {N : ℕ} (Z : ℝ) (p : FermionMultiplier N)
    (F : fermionGraph N) :
    (⟪p.apply F, coulombFormOperator Z N F⟫_ℂ).re =
      (∑ s : Spins N, ∫ x, p.value x * quantumEnergyDensity Z (graphFormVector F) s x) +
      (1/2:ℝ) * ((∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        (⟪graphComponent s (some (i,a)) (p.apply F), graphComponent s (some (i,a)) F⟫_ℂ).re) -
        (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3, ∫ x, p.value x * ‖graphComponent s (some (i,a)) F x‖ ^ 2)) := by
  exact weighted_form_algebra Z _ _ _ _ _ _ (p.density_weighted_sum Z F) (p.operator_weighted_pairing Z F)

end

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end CoulombAtom

end

end OAI
