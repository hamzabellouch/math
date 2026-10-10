import Mathlib
import OAI.Analysis.CoulombRadii.Localization.CutCombinatorics
import OAI.Analysis.CoulombRadii.RandomFields.CutJensen

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma positive_square_tangent (b c : ℝ) (hc : 0≤c) :
    2*c*b-c^2 ≤ (max b 0)^2 := by
  nlinarith [sq_nonneg (max b 0-c),mul_le_mul_of_nonneg_left (le_max_left b 0) hc]

lemma finite_mass_positive_jensen {P : Type*} [Fintype P]
    (M H : P → ℝ) (hM : ∀ p, 0≤M p) (m h : ℝ)
    (hm : ∑ p, M p=m) (hh : ∑ p, M p*H p=m*h) :
    m*(max h 0)^2 ≤ ∑ p, M p*(max (H p) 0)^2 := by
  let c := max h 0
  have hc : 0≤c := le_max_right _ _
  have H0 := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) =>
    mul_le_mul_of_nonneg_left (positive_square_tangent (H p) c hc) (hM p))
  have he : (∑ p, M p*(2*c*H p-c^2))=2*c*(m*h)-c^2*m := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    have h1 : (∑ p, M p*(2*c*H p))=2*c*∑ p, M p*H p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros
      ring
    rw [h1,←Finset.sum_mul,hh,hm]
    ring
  rw [he] at H0
  by_cases hp : 0≤h
  · have hec : c=h := max_eq_left hp
    rw [hec] at H0
    rw [max_eq_left hp]
    nlinarith
  · have hec : c=0 := max_eq_right (le_of_not_ge hp)
    rw [hec] at H0
    rw [max_eq_right (le_of_not_ge hp)]
    nlinarith

lemma labelCut_coreSlice_law {m k : ℕ} {L : Type*} [Fintype L]
    (u : H1Vector (m+k)) (χ : L → Space → ℝ)
    (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (s : Spins m) :
    ∀ᵐ x, ∀ t : Spins k, ∀ v : Configuration k,
      (∑ p : Fin (m+k) → L,
        ‖((u.labelCut χ hχ hp D hD hd p).coreSlice s x).value t v‖^2)=
          ‖(u.coreSlice s x).value t v‖^2 := by
  have hall : ∀ᵐ x, ∀ p : Fin (m+k) → L,
      (u.labelCut χ hχ hp D hD hd p).CoreSliceRegular s x :=
    ae_all_iff.mpr (fun p => (u.labelCut χ hχ hp D hD hd p).coreSliceRegular_ae s)
  filter_upwards [u.coreSliceRegular_ae s,hall] with x hx ha
  intro t v
  simp_rw [(u.labelCut χ hχ hp D hD hd _).coreSlice_value s (ha _) t v]
  rw [u.coreSlice_value s hx]
  simp only [H1Vector.labelCut,H1Vector.smoothMul,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,
    ←Finset.sum_mul,tensorCut_partition χ hp,one_mul]

lemma fiber_mass_law {P : Type*} [Fintype P] {k : ℕ}
    (u : H1Vector k) (v : P → H1Vector k)
    (hlaw : ∀ s x, (∑ p, ‖(v p).value s x‖^2)=‖u.value s x‖^2) :
    (∑ p, mass (v p))=mass u := by
  unfold mass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [←integral_finsetSum _ (fun p _ => ((v p).value_L2 s).integrable_norm_pow (by norm_num))]
  exact integral_congr_ae (Eventually.of_forall (hlaw s))

lemma fiber_potential_law {P : Type*} [Fintype P] {k : ℕ}
    (u : H1Vector k) (v : P → H1Vector k)
    (hlaw : ∀ s x, (∑ p, ‖(v p).value s x‖^2)=‖u.value s x‖^2)
    (W : Configuration k → ℝ) (hW : Measurable W) {B : ℝ} (hB : ∀ x, |W x| ≤ B) :
    (∑ p, potentialForm W (v p))=potentialForm W u := by
  unfold potentialForm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [←integral_finsetSum _ (fun p _ => boundedObservable_integrable (v p) W hW hB s)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [←Finset.mul_sum,hlaw]

theorem labelCut_conditional_positive_jensen {m k : ℕ} {L : Type*} [Fintype L]
    (u : H1Vector (m+k)) (χ : L → Space → ℝ)
    (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (W : Configuration (m+k) → ℝ) (hW : Measurable W) {B : ℝ} (hB0 : 0≤B)
    (hB : ∀ x, |W x| ≤ B) :
    sliceExpectation u (fun s x => (max (coreConditionalObservable u W s x) 0)^2) ≤
      ∑ p : Fin (m+k) → L, sliceExpectation (u.labelCut χ hχ hp D hD hd p)
        (fun s x => (max (coreConditionalObservable (u.labelCut χ hχ hp D hD hd p) W s x) 0)^2) := by
  let v := fun p : Fin (m+k) → L => u.labelCut χ hχ hp D hD hd p
  unfold sliceExpectation
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro s hs
  rw [←integral_finsetSum _ (fun p _ => coreConditionalObservable_positive_weight_integrable (v p) W hW hB0 hB s 2)]
  apply integral_mono_ae (coreConditionalObservable_positive_weight_integrable u W hW hB0 hB s 2)
    (integrable_finsetSum _ (fun p _ => coreConditionalObservable_positive_weight_integrable (v p) W hW hB0 hB s 2))
  filter_upwards [labelCut_coreSlice_law u χ hχ hp D hD hd s] with x hx
  apply finite_mass_positive_jensen (fun p => mass ((v p).coreSlice s x))
    (fun p => coreConditionalObservable (v p) W s x) (fun p => mass_nonneg _) _ _
  · exact fiber_mass_law _ _ hx
  · simp only [coreConditionalObservable,potentialForm_normalized_weight]
    exact fiber_potential_law _ _ hx _
      (hW.comp ((joinConfiguration m k).continuous.measurable.comp (measurable_const.prodMk measurable_id)))
      (fun _ => hB _)

end Coulomb
end

end
end

end OAI
