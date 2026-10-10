import Mathlib
import OAI.Analysis.CoulombIonization.Variational.BindingPairApproxIntegral

namespace OAI

noncomputable section

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
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace CoulombAtom

attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply coulombFormOperator fermionGraph weakGraph fermionGraphValue

def weightedMass {N : ℕ} (F : fermionGraph N) (w : Configuration N → ℝ) : ℝ :=
  ∑ s, ∫ x, w x * ‖graphComponent s none F x‖ ^ 2

def weightedGradient {N : ℕ} (F : fermionGraph N) (w : Configuration N → ℝ) (i : Fin N) : ℝ :=
  ∑ s, ∑ a, ∫ x, w x * ‖graphComponent s (some (i,a)) F x‖ ^ 2

def weightedFullDensity {N : ℕ} (Z : ℝ) (F : fermionGraph N) (w : Configuration N → ℝ) : ℝ :=
  ∑ s, ∫ x, w x * quantumEnergyDensity Z (graphFormVector F) s x

def weightedCoreDensity {N : ℕ} (Z : ℝ) (F : fermionGraph N) (i : Fin N)
    (w : Configuration N → ℝ) : ℝ :=
  ∑ s, ∫ x, w x * quantumCoreDensity Z (graphFormVector F) i s x

def weightedNuclear {N : ℕ} (F : fermionGraph N) (i : Fin N)
    (w : Configuration N → ℝ) : ℝ :=
  ∑ s, ∫ x, w x * (‖graphComponent s none F x‖ ^ 2 / ‖x i‖)

def weightedPairs {N : ℕ} (F : fermionGraph N) (i : Fin N)
    (w : Configuration N → ℝ) : ℝ :=
  ∑ s, ∑ j, ∫ x, w x * (if i ≠ j then ‖graphComponent s none F x‖ ^ 2 / ‖x i-x j‖ else 0)

lemma weightedMass_nonneg {N : ℕ} (F : fermionGraph N) {w : Configuration N → ℝ}
    (hw : ∀ x, 0 ≤ w x) : 0 ≤ weightedMass F w := by
  exact Finset.sum_nonneg fun s _ => integral_nonneg fun x => mul_nonneg (hw x) (sq_nonneg _)

lemma weightedFullDensity_delete {N : ℕ} (Z : ℝ) (F : fermionGraph N) (i : Fin N)
    (w : Configuration N → ℝ) (hw : Continuous w) {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) :
    weightedFullDensity Z F w = weightedCoreDensity Z F i w +
      (1/2:ℝ) * weightedGradient F w i - Z * weightedNuclear F i w + weightedPairs F i w := by
  have h := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun s _ => integral_weighted_deletedDensity (graphFormVector_sobolev F) Z s i w hw hC)
  simpa only [weightedFullDensity, weightedCoreDensity, weightedGradient, weightedNuclear, weightedPairs,
    graphFormVector_value_eq, graphFormVector_gradient_eq,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] using h

lemma FermionMultiplier.value_weighted_pairing {N : ℕ} (F : fermionGraph N) (p : FermionMultiplier N) :
    (⟪fermionGraphValue N (p.apply F), fermionGraphValue N F⟫_ℂ).re = weightedMass F p.value := by
  rw [graphValue_pairing]
  apply Finset.sum_congr rfl; intro s _
  exact l2_real_weight_pairing p.value _ _ (p.apply_value F s)

lemma ground_weighted_identity {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (F : fermionGraph N) (hn : ‖fermionGraphValue N F‖ ^ 2 = 1)
    (hF : formEnergy Z (graphFormVector F) = energy Z N) (p : FermionMultiplier N) :
    (⟪p.apply F, coulombFormOperator Z N F⟫_ℂ).re = energy Z N * weightedMass F p.value := by
  rw [quantum_ground_form_equation hZ F hn hF]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    p.value_weighted_pairing F]

attribute [local irreducible] bindingTotalMultiplier graphNuclear graphPair
  weightedMass weightedGradient weightedFullDensity weightedCoreDensity weightedNuclear weightedPairs

lemma sum_rotate_three {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : A → B → C → ℝ) : (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

def graphKineticPair {N : ℕ} (G F : fermionGraph N) : ℝ :=
  ∑ s, ∑ i, ∑ a, (⟪graphComponent s (some (i,a)) G,
    graphComponent s (some (i,a)) F⟫_ℂ).re

def weightedKinetic {N : ℕ} (F : fermionGraph N) (w : Configuration N → ℝ) : ℝ :=
  ∑ i, weightedGradient F w i

attribute [local irreducible] weightedKinetic graphKineticPair

lemma weightedKinetic_expand {N : ℕ} (F : fermionGraph N) (w : Configuration N → ℝ) :
    weightedKinetic F w =
      ∑ s, ∑ i, ∑ a, ∫ x, w x * ‖graphComponent s (some (i,a)) F x‖ ^ 2 := by
  unfold weightedKinetic weightedGradient
  exact Finset.sum_comm

lemma bindingTotal_full {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (Z : ℝ) (F : fermionGraph N) :
    weightedFullDensity Z F (bindingTotalMultiplier hR hε).value =
      ∑ i, weightedFullDensity Z F (fun x => bindingWeight R ε (x i)) := by
  unfold weightedFullDensity
  simp only [bindingTotal_integral hR hε ((graphFormVector_sobolev F).quantumEnergyDensity_integrable Z _)]
  exact Finset.sum_comm

lemma bindingTotal_kinetic {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : fermionGraph N) :
    weightedKinetic F (bindingTotalMultiplier hR hε).value =
      ∑ s, ∑ j, ∑ i, ∑ a, ∫ x, bindingWeight R ε (x j) *
        ‖graphComponent s (some (i,a)) F x‖ ^ 2 := by
  rw [weightedKinetic_expand]
  simp only [bindingTotal_integral hR hε (Lp.memLp _).norm.integrable_sq]
  apply Finset.sum_congr rfl; intro s _
  exact sum_rotate_three (fun i a j => ∫ x, bindingWeight R ε (x j) *
    ‖graphComponent s (some (i,a)) F x‖ ^ 2)

lemma sum_sub_le_transport {α β : Type*} [Fintype α] [Fintype β]
    (a b : α → β → ℝ) (G W K : ℝ)
    (ha : (∑ s, ∑ i, a s i) = W) (hb : (∑ s, ∑ i, b s i) = K)
    (hc : (∑ s, ∑ i, (a s i-b s i)) ≤ G) : W-K ≤ G := by
  rw [← ha, ← hb]
  simpa only [Finset.sum_sub_distrib] using hc

lemma bindingTotal_kinetic_diagonal {N : ℕ} (F : fermionGraph N) (R ε : ℝ) :
    (∑ s, ∑ i, ∑ a, ∫ x, bindingWeight R ε (x i) *
      ‖graphComponent s (some (i,a)) F x‖ ^ 2) =
      ∑ i, weightedGradient F (fun x => bindingWeight R ε (x i)) i := by
  unfold weightedGradient
  exact Finset.sum_comm

lemma bindingTotal_kinetic_lower_packed {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : fermionGraph N) :
    weightedKinetic F (bindingTotalMultiplier hR hε).value -
      (∑ i, weightedGradient F (fun x => bindingWeight R ε (x i)) i) ≤
      graphKineticPair ((bindingTotalMultiplier hR hε).apply F) F := by
  exact sum_sub_le_transport
    (fun s i => ∑ j, ∑ a, ∫ x, bindingWeight R ε (x i) *
      ‖graphComponent s (some (j,a)) F x‖ ^ 2)
    (fun s i => ∑ a, ∫ x, bindingWeight R ε (x i) *
      ‖graphComponent s (some (i,a)) F x‖ ^ 2)
    _ _ _ (bindingTotal_kinetic hR hε F).symm
    (bindingTotal_kinetic_diagonal F R ε) (by
      unfold graphKineticPair
      exact binding_total_kinetic_lower hR hε F)

lemma FermionMultiplier.form_weighted_packed {N : ℕ} (Z : ℝ) (p : FermionMultiplier N)
    (F : fermionGraph N) :
    (⟪p.apply F, coulombFormOperator Z N F⟫_ℂ).re =
      weightedFullDensity Z F p.value + (1/2:ℝ)*
        (graphKineticPair (p.apply F) F-weightedKinetic F p.value) := by
  simpa only [weightedKinetic_expand, weightedFullDensity, graphKineticPair] using
    p.form_weighted_identity Z F

lemma binding_form_sum_arithmetic {ι : Type*} [Fintype ι]
    (D C K V P : ι → ℝ) (Z W G A Dt : ℝ)
    (hD : ∀ i, D i = C i + (1/2:ℝ)*K i - Z*V i + P i)
    (hG : W-(∑ i, K i) ≤ G) (hDt : Dt = ∑ i, D i)
    (hA : A = Dt+(1/2:ℝ)*(G-W)) :
    (∑ i, (C i-Z*V i+P i)) ≤ A := by
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ => hD i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hs ⊢
  linarith

lemma binding_form_lower {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (Z : ℝ) (F : fermionGraph N) :
    (∑ i : Fin N, (weightedCoreDensity Z F i (fun x => bindingWeight R ε (x i)) -
      Z * weightedNuclear F i (fun x => bindingWeight R ε (x i)) +
      weightedPairs F i (fun x => bindingWeight R ε (x i)))) ≤
      (⟪(bindingTotalMultiplier hR hε).apply F, coulombFormOperator Z N F⟫_ℂ).re := by
  let w : Fin N → Configuration N → ℝ := fun i x => bindingWeight R ε (x i)
  have hc (i : Fin N) : Continuous (w i) :=
    (bindingWeight_continuous hR hε).comp (continuous_apply i)
  have hb (i : Fin N) (x : Configuration N) : ‖w i x‖ ≤ R := by
    change ‖bindingWeight R ε (x i)‖ ≤ R
    rw [Real.norm_of_nonneg (bindingWeight_pos hR hε (x i)).le]
    exact bindingWeight_le hR hε (x i)
  exact binding_form_sum_arithmetic _ _ _ _ _ Z _ _ _ _
    (fun i => weightedFullDensity_delete Z F i (w i) (hc i) (hb i))
    (bindingTotal_kinetic_lower_packed hR hε F) (bindingTotal_full hR hε Z F)
    ((bindingTotalMultiplier hR hε).form_weighted_packed Z F)

lemma bindingTotal_mass {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : fermionGraph N) :
    weightedMass F (bindingTotalMultiplier hR hε).value =
      ∑ i, weightedMass F (fun x => bindingWeight R ε (x i)) := by
  unfold weightedMass
  simp only [bindingTotal_integral hR hε (Lp.memLp _).norm.integrable_sq]
  rw [Finset.sum_comm]

lemma energy_weighted_core_le {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (F : fermionGraph (N+1)) (hstep : energy Z (N+1) ≤ energy Z N)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (i : Fin (N+1)) :
    energy Z (N+1) * weightedMass F (fun x => bindingWeight R ε (x i)) ≤
      weightedCoreDensity Z F i (fun x => bindingWeight R ε (x i)) := by
  have hm := weightedMass_nonneg F (fun x => (bindingWeight_pos hR hε (x i)).le)
  have hb (y : Space) : ‖bindingWeight R ε y‖ ≤ R := by
    rw [Real.norm_of_nonneg (bindingWeight_pos hR hε y).le]
    exact bindingWeight_le hR hε y
  have hi := weighted_core_coordinate F hZ i (bindingWeight R ε)
    (bindingWeight_continuous hR hε) (fun y => (bindingWeight_pos hR hε y).le) hb
  apply (mul_le_mul_of_nonneg_right hstep hm).trans
  simpa only [weightedMass, weightedCoreDensity] using hi

lemma binding_cancellation {ι : Type*} [Fintype ι] (C V P M : ι → ℝ) (E Z A Mt : ℝ)
    (hC : ∀ i, E*M i ≤ C i) (hM : Mt = ∑ i, M i) (hA : A = E*Mt)
    (hL : (∑ i, (C i-Z*V i+P i)) ≤ A) : (∑ i, P i) ≤ Z*(∑ i, V i) := by
  rw [hM] at hA
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hC i)
  rw [← Finset.mul_sum] at hs
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hL
  linarith

theorem quantum_ground_binding_regularized {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (F : fermionGraph (N+1)) (hn : ‖fermionGraphValue (N+1) F‖ ^ 2 = 1)
    (hF : formEnergy Z (graphFormVector F) = energy Z (N+1))
    (hstep : energy Z (N+1) ≤ energy Z N)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    (∑ i, weightedPairs F i (fun x => bindingWeight R ε (x i))) ≤
      Z * (∑ i, weightedNuclear F i (fun x => bindingWeight R ε (x i))) := by
  exact binding_cancellation _ _ _ _ _ _ _ _
    (fun i => energy_weighted_core_le hZ F hstep hR hε i)
    (bindingTotal_mass hR hε F)
    (ground_weighted_identity hZ F hn hF (bindingTotalMultiplier hR hε))
    (binding_form_lower hR hε Z F)

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end

end OAI
