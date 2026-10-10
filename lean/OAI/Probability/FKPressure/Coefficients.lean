import OAI.Probability.FKPressure.Taylor

namespace OAI

 
noncomputable section
open Finset FormalMultilinearSeries
open scoped Classical Topology NNReal ENNReal
namespace BelowOne.PressureSeries
open MultiaffineDerivative
variable {V : Type*} [Fintype V]

abbrev Labels (V : Type*) := Σ n : ℕ, Fin n → V

def multiplicity (a : Labels V) (i : V) : ℕ :=
  ((univ : Finset (Fin a.1)).filter (fun j => a.2 j = i)).card

lemma sum_multiplicity (a : Labels V) : ∑ i, multiplicity a i = a.1 := by
  simpa only [multiplicity, mem_univ, filter_true, card_univ, Fintype.card_fin] using
    sum_card_fiberwise_eq_card_filter (univ : Finset (Fin a.1)) (univ : Finset V) a.2

omit [Fintype V] in
lemma multiplicity_pos (a : Labels V) (i : V) : 0 < multiplicity a i ↔ i ∈ Set.range a.2 := by
  simp only [multiplicity, card_pos, filter_nonempty_iff, mem_univ, true_and, Set.mem_range]

lemma prod_multiplicity {R : Type*} [CommMonoid R] (x : V → R) (a : Labels V) :
    ∏ i, x i ^ multiplicity a i = ∏ j, x (a.2 j) := by
  rw [← prod_fiberwise (univ : Finset (Fin a.1)) a.2 (fun j => x (a.2 j))]
  apply prod_congr rfl
  intro i hi
  rw [multiplicity, ← prod_const]
  apply prod_congr rfl
  intro j hj
  rw [(mem_filter.mp hj).2]

def weight (p : FormalMultilinearSeries ℝ (V → ℝ) ℝ) (a : Labels V) : ℝ :=
  p a.1 (coordinate ∘ a.2)

def coefficient (p : FormalMultilinearSeries ℝ (V → ℝ) ℝ) (m : V → ℕ) : ℝ :=
  ∑' a : multiplicity (V := V) ⁻¹' {m}, weight p a

omit [Fintype V] in
lemma coefficient_nonneg (p : FormalMultilinearSeries ℝ (V → ℝ) ℝ)
    (hp : ∀ a, 0 ≤ weight p a) (m : V → ℕ) : 0 ≤ coefficient p m :=
  tsum_nonneg (fun a => hp a)

lemma coefficient_zero (p : FormalMultilinearSeries ℝ (V → ℝ) ℝ)
    (hp : p 0 = 0) : coefficient p 0 = 0 := by
  change (∑' a : multiplicity (V := V) ⁻¹' {0}, weight p a) = 0
  suffices hz : ∀ a : multiplicity (V := V) ⁻¹' {0}, weight p a = 0 by simp only [hz, tsum_zero]
  intro a
  have hm : multiplicity a.val = 0 := a.property
  have hn : a.val.1 = 0 := by simpa only [hm, Pi.zero_apply, sum_const_zero] using (sum_multiplicity a.val).symm
  obtain ⟨⟨n,τ⟩,ha⟩ := a
  dsimp only at hn
  subst n
  simp only [weight, hp, _root_.zero_apply]

omit [Fintype V] in
lemma coefficient_pos_has_label (p : FormalMultilinearSeries ℝ (V → ℝ) ℝ)
    (m : V → ℕ) (h : 0 < coefficient p m) :
    ∃ a : Labels V, multiplicity a = m ∧ weight p a ≠ 0 := by
  by_contra! hh
  have hz : coefficient p m = 0 := by
    unfold coefficient
    simp only [show ∀ a : multiplicity (V := V) ⁻¹' {m}, weight p a = 0 from fun a => hh a a.property, tsum_zero]
  linarith

lemma summable_labels (p : FormalMultilinearSeries ℝ (V → ℝ) ℝ)
    (hp : ∀ a, 0 ≤ weight p a) {r : ℝ} (hr : 0 ≤ r)
    (hR : ENNReal.ofReal r < p.radius) :
    Summable (fun a : Labels V => weight p a * r ^ a.1) := by
  have hnorm : ‖(fun _ : V => r)‖ ≤ r :=
    (pi_norm_le_iff_of_nonneg hr).mpr (fun _ => by simp [Real.norm_of_nonneg hr])
  have he : ‖(fun _ : V => r)‖ₑ < p.radius := by
    apply lt_of_le_of_lt _ hR
    simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hnorm
  have hs := p.summable (mem_eball_zero_iff.mpr he)
  apply (summable_sigma_of_nonneg (fun a => mul_nonneg (hp a) (pow_nonneg hr a.1))).mpr
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  apply hs.congr
  intro n
  rw [tsum_fintype, PositiveMultilinear.expansion]
  apply sum_congr rfl
  intro τ hτ
  simp only [prod_const, card_univ, Fintype.card_fin, weight]
  ring

lemma summable_complex_labels (p : FormalMultilinearSeries ℝ (V → ℝ) ℝ)
    (hp : ∀ a, 0 ≤ weight p a) {r : ℝ} (hr : 0 ≤ r)
    (hR : ENNReal.ofReal r < p.radius) (x : V → ℂ) (hx : ∀ i, ‖x i‖ ≤ r) :
    Summable (fun a : Labels V => (weight p a : ℂ) * ∏ j, x (a.2 j)) := by
  apply (summable_labels p hp hr hR).of_norm_bounded
  intro a
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp a), norm_prod]
  apply mul_le_mul_of_nonneg_left _ (hp a)
  calc
    ∏ j, ‖x (a.2 j)‖ ≤ ∏ _j : Fin a.1, r := prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hx _)
    _ = r ^ a.1 := by simp

lemma fiber_complex (p : FormalMultilinearSeries ℝ (V → ℝ) ℝ) (x : V → ℂ)
    (m : V → ℕ) :
    (∑' a : multiplicity (V := V) ⁻¹' {m}, (weight p a : ℂ) * ∏ j, x (a.val.2 j)) =
      (coefficient p m : ℂ) * ∏ i, x i ^ m i := by
  simp only [coefficient, Complex.ofReal_tsum, ← tsum_mul_right]
  apply tsum_congr
  intro a
  rw [← prod_multiplicity, show multiplicity a.val = m from a.property]

lemma hasSum_coefficients_of_complex_degrees (p : FormalMultilinearSeries ℝ (V → ℝ) ℝ)
    (hp : ∀ a, 0 ≤ weight p a) {r : ℝ} (hr : 0 ≤ r)
    (hR : ENNReal.ofReal r < p.radius) (x : V → ℂ) (hx : ∀ i, ‖x i‖ ≤ r)
    {z : ℂ} (hz : HasSum (fun n => ∑ τ : Fin n → V, (weight p ⟨n,τ⟩ : ℂ) * ∏ j, x (τ j)) z) :
    HasSum (fun m : V → ℕ => (coefficient p m : ℂ) * ∏ i, x i ^ m i) z := by
  have hs := summable_complex_labels p hp hr hR x hx
  have hsl : HasSum (fun a : Labels V => (weight p a : ℂ) * ∏ j, x (a.2 j)) z :=
    HasSum.sigma_of_hasSum (f := fun a : Labels V => (weight p a : ℂ) * ∏ j, x (a.2 j))
      hz (fun n => hasSum_fintype _) hs
  have hf : HasSum (fun m : V → ℕ => ∑' a : multiplicity (V := V) ⁻¹' {m},
      (weight p a : ℂ) * ∏ j, x (a.val.2 j)) z := hsl.tsum_fiberwise multiplicity
  exact hf.congr_fun (fun m => (fiber_complex p x m).symm)

end BelowOne.PressureSeries

end

end OAI
