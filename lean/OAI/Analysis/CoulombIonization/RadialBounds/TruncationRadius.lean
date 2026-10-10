import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.RadialInside

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace CoulombAtom

def truncationRadius (k : ℕ) : ℝ := (k : ℝ)+1
lemma truncationRadius_pos (k : ℕ) : 0 < truncationRadius k := by
  unfold truncationRadius; positivity
lemma truncationRadius_one_le (k : ℕ) : 1 ≤ truncationRadius k := by
  unfold truncationRadius; linarith [Nat.cast_nonneg (α := ℝ) k]

def truncationMultiplier (N k : ℕ) : FermionMultiplier N where
  toSmoothMultiplier := spatialProduct
    (radialCut 0 (truncationRadius_pos k).le (truncationRadius_pos k))
    (radialCut_partition 0 (truncationRadius_pos k).le (truncationRadius_pos k)) (fun _ => 0)
  symmetric π x := spatialProduct_invariant _ _ π rfl x

def truncateForm {N : ℕ} (k : ℕ) (ψ : FormVector N) : FormVector N :=
  multiplyForm (truncationMultiplier N k).toSmoothMultiplier ψ

lemma SobolevFermion.truncate {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ) (k : ℕ) :
    SobolevFermion (truncateForm k ψ) := hψ.multiply (truncationMultiplier N k)

lemma truncation_value_le_one {N : ℕ} (k : ℕ) (x : Configuration N) :
    |(truncationMultiplier N k).value x| ≤ 1 :=
  spatial_product_sub_bound
    (radialCut 0 (truncationRadius_pos k).le (truncationRadius_pos k))
    (radialCut_partition 0 (truncationRadius_pos k).le (truncationRadius_pos k))
    (fun _ : Fin N => 0) x Finset.univ

lemma truncation_value_one {N : ℕ} (k : ℕ) (x : Configuration N)
    (hx : ∀ i, ‖x i‖ ≤ truncationRadius k) :
    (truncationMultiplier N k).value x = 1 := by
  change (∏ i, (radialCut 0 (truncationRadius_pos k).le
    (truncationRadius_pos k) 0).value (x i)) = 1
  apply Finset.prod_eq_one
  intro i _
  exact (radialCut_inner (truncationRadius_pos k).le (truncationRadius_pos k)
    (by simpa only [sub_zero] using hx i)).1

lemma truncation_derivative_zero {N : ℕ} (k : ℕ) (x : Configuration N) (i : Fin N) (a : Fin 3)
    (hx : ‖x i‖ ≤ truncationRadius k) :
    lineDeriv ℝ (truncationMultiplier N k).value x (direction i a) = 0 := by
  change lineDeriv ℝ (spatialProductValue _ _) x (direction i a) = 0
  rw [spatialProduct_derivative]
  change _ * lineDeriv ℝ (fun z => Real.cos (radialPhase 0 (truncationRadius k)
    (truncationRadius k) z)) (x i) (spaceDirections a) = 0
  rw [radial_cos_derivative, radialPhase_zero (truncationRadius_pos k).le
    (truncationRadius_pos k) (by simpa only [sub_zero] using hx)]
  simp only [Real.sin_zero, neg_zero, zero_mul, mul_zero]

lemma truncation_derivative_bound {N : ℕ} (k : ℕ) (x : Configuration N) (i : Fin N) (a : Fin 3) :
    |lineDeriv ℝ (truncationMultiplier N k).value x (direction i a)| ≤
      Real.pi * smoothTransitionBound := by
  change |lineDeriv ℝ (spatialProductValue _ _) x (direction i a)| ≤ _
  rw [spatialProduct_derivative, abs_mul]
  have hprod := spatial_product_sub_bound
    (radialCut 0 (truncationRadius_pos k).le (truncationRadius_pos k))
    (radialCut_partition 0 (truncationRadius_pos k).le (truncationRadius_pos k))
    (fun _ : Fin N => 0) x (Finset.univ.erase i)
  apply (mul_le_mul_of_nonneg_right hprod (abs_nonneg _)).trans
  rw [one_mul]
  change |lineDeriv ℝ (fun z => Real.cos (radialPhase 0 (truncationRadius k)
    (truncationRadius k) z)) (x i) (spaceDirections a)| ≤ _
  rw [radial_cos_derivative, abs_mul, abs_neg]
  apply (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)).trans
  rw [one_mul]
  apply (radialPhase_derivative_le 0 (truncationRadius_pos k).le (truncationRadius_pos k) (x i) a).trans
  exact div_le_self (mul_pos Real.pi_pos smoothTransitionBound_pos).le (truncationRadius_one_le k)

lemma truncation_eventually_identity {N : ℕ} (x : Configuration N) :
    ∀ᶠ k : ℕ in atTop, (truncationMultiplier N k).value x = 1 ∧
      ∀ i a, lineDeriv ℝ (truncationMultiplier N k).value x (direction i a) = 0 := by
  obtain ⟨K,hK⟩ := exists_nat_gt ‖x‖
  refine eventually_atTop.mpr ⟨K,fun k hk => ?_⟩
  have hx (i : Fin N) : ‖x i‖ ≤ truncationRadius k := by
    have hki : (K:ℝ) ≤ k := by exact_mod_cast hk
    have hi : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
    unfold truncationRadius
    linarith
  exact ⟨truncation_value_one k x hx, fun i a => truncation_derivative_zero k x i a (hx i)⟩

lemma truncateForm_eventually_identity {N : ℕ} (ψ : FormVector N) (s : Spins N)
    (x : Configuration N) :
    ∀ᶠ k : ℕ in atTop, (truncateForm k ψ).value s x = ψ.value s x ∧
      ∀ i a, (truncateForm k ψ).gradient s i a x = ψ.gradient s i a x := by
  filter_upwards [truncation_eventually_identity x] with k hk
  constructor
  · change ((truncationMultiplier N k).value x : ℂ) * _ = _
    rw [hk.1]; simp only [Complex.ofReal_one, one_mul]
  · intro i a
    change ((truncationMultiplier N k).value x : ℂ) * _ +
      Complex.ofReal (lineDeriv ℝ (truncationMultiplier N k).value x (direction i a)) * _ = _
    rw [hk.1,hk.2 i a]
    simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, add_zero]

lemma truncateForm_value_sq_le {N : ℕ} (k : ℕ) (ψ : FormVector N) (s : Spins N)
    (x : Configuration N) : ‖(truncateForm k ψ).value s x‖^2 ≤ ‖ψ.value s x‖^2 := by
  change ‖((truncationMultiplier N k).value x : ℂ) * ψ.value s x‖^2 ≤ _
  rw [scaled_norm_sq]
  have hh := truncation_value_le_one k x
  have hs : (truncationMultiplier N k).value x ^ 2 ≤ 1 := by
    nlinarith [sq_abs ((truncationMultiplier N k).value x), abs_nonneg ((truncationMultiplier N k).value x)]
  exact mul_le_of_le_one_left (sq_nonneg _) hs

lemma truncateForm_gradient_sq_le {N : ℕ} (k : ℕ) (ψ : FormVector N) (s : Spins N)
    (x : Configuration N) (i : Fin N) (a : Fin 3) :
    ‖(truncateForm k ψ).gradient s i a x‖^2 ≤
      2*‖ψ.gradient s i a x‖^2 + 2*(Real.pi*smoothTransitionBound)^2*‖ψ.value s x‖^2 := by
  have hC : 0 < Real.pi*smoothTransitionBound := mul_pos Real.pi_pos smoothTransitionBound_pos
  have hnorm : ‖(truncateForm k ψ).gradient s i a x‖ ≤
      ‖ψ.gradient s i a x‖ + (Real.pi*smoothTransitionBound)*‖ψ.value s x‖ := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) (truncation_value_le_one k x))
      (mul_le_mul_of_nonneg_right (truncation_derivative_bound k x i a) (norm_nonneg _))
  nlinarith [sq_nonneg (‖ψ.gradient s i a x‖-(Real.pi*smoothTransitionBound)*‖ψ.value s x‖),
    norm_nonneg ((truncateForm k ψ).gradient s i a x), norm_nonneg (ψ.gradient s i a x),
    norm_nonneg (ψ.value s x)]

lemma truncateForm_mass_tendsto {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ) :
    Tendsto (fun k => formMass (truncateForm k ψ)) atTop (𝓝 (formMass ψ)) := by
  unfold formMass
  apply tendsto_finsetSum
  intro s _
  apply tendsto_integral_of_dominated_convergence (fun x => ‖ψ.value s x‖^2)
  · intro k; exact ((hψ.truncate k).1 s).norm.integrable_sq.aestronglyMeasurable
  · exact (hψ.1 s).norm.integrable_sq
  · intro k
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact truncateForm_value_sq_le k ψ s x
  · exact Eventually.of_forall fun x => tendsto_const_nhds.congr'
      ((truncateForm_eventually_identity ψ s x).mono fun _ hk => by simp only [hk.1])

lemma truncateForm_kinetic_tendsto {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (s : Spins N) (i : Fin N) (a : Fin 3) :
    Tendsto (fun k => ∫ x, ‖(truncateForm k ψ).gradient s i a x‖^2) atTop
      (𝓝 (∫ x, ‖ψ.gradient s i a x‖^2)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun x => 2*‖ψ.gradient s i a x‖^2 + 2*(Real.pi*smoothTransitionBound)^2*‖ψ.value s x‖^2)
  · intro k; exact ((hψ.truncate k).2.1 s i a).norm.integrable_sq.aestronglyMeasurable
  · exact ((hψ.2.1 s i a).norm.integrable_sq.const_mul 2).add
      ((hψ.1 s).norm.integrable_sq.const_mul _)
  · intro k
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact truncateForm_gradient_sq_le k ψ s x i a
  · exact Eventually.of_forall fun x => tendsto_const_nhds.congr'
      ((truncateForm_eventually_identity ψ s x).mono fun _ hk => by simp only [hk.2 i a])

lemma truncateForm_coulomb_tendsto {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (s : Spins N) (d : Configuration N → ℝ) (hd : Measurable d) (hd0 : ∀ x, 0 ≤ d x)
    (hi : Integrable (fun x => ‖ψ.value s x‖^2 / d x)) :
    Tendsto (fun k => ∫ x, ‖(truncateForm k ψ).value s x‖^2 / d x) atTop
      (𝓝 (∫ x, ‖ψ.value s x‖^2 / d x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖ψ.value s x‖^2 / d x)
  · intro k
    exact (((hψ.truncate k).1 s).norm.integrable_sq.aemeasurable.div
      hd.aemeasurable).aestronglyMeasurable
  · exact hi
  · intro k
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (hd0 x))]
      exact div_le_div_of_nonneg_right (truncateForm_value_sq_le k ψ s x) (hd0 x)
  · exact Eventually.of_forall fun x => tendsto_const_nhds.congr'
      ((truncateForm_eventually_identity ψ s x).mono fun _ hk => by simp only [hk.1])

lemma truncateForm_energy_tendsto {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (Z : ℝ) : Tendsto (fun k => formEnergy Z (truncateForm k ψ)) atTop
      (𝓝 (formEnergy Z ψ)) := by
  unfold formEnergy
  apply Tendsto.add
  · apply Tendsto.sub
    · apply Tendsto.const_mul
      apply tendsto_finsetSum; intro s _
      apply tendsto_finsetSum; intro i _
      apply tendsto_finsetSum; intro a _
      exact truncateForm_kinetic_tendsto hψ s i a
    · apply Tendsto.const_mul
      apply tendsto_finsetSum; intro s _
      apply tendsto_finsetSum; intro i _
      exact truncateForm_coulomb_tendsto hψ s (fun x => ‖x i‖)
        (measurable_pi_apply i).norm (fun _ => norm_nonneg _)
        (hψ.sobolevVector.nuclear_integrable s i)
  · apply tendsto_finsetSum; intro s _
    apply tendsto_finsetSum; intro i _
    apply tendsto_finsetSum; intro j _
    by_cases hij : i < j
    · simp only [ite_eq_left hij]
      exact truncateForm_coulomb_tendsto hψ s (fun x => ‖x i-x j‖)
        ((measurable_pi_apply i).sub (measurable_pi_apply j)).norm (fun _ => norm_nonneg _)
        (hψ.sobolevVector.pair_integrable s i j (ne_of_lt hij))
    · simp only [ite_eq_right hij]
      exact tendsto_const_nhds

lemma truncation_value_zero {N : ℕ} (k : ℕ) (x : Configuration N) (i : Fin N)
    (hx : 2*truncationRadius k ≤ ‖x i‖) : (truncationMultiplier N k).value x = 0 := by
  classical
  change (∏ j, (radialCut 0 (truncationRadius_pos k).le
    (truncationRadius_pos k) 0).value (x j)) = 0
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply (radialCut_outer (truncationRadius_pos k).le (truncationRadius_pos k) ?_).1
  simpa only [sub_zero, two_mul] using hx

lemma truncateForm_support {N : ℕ} (k : ℕ) (ψ : FormVector N) (s : Spins N)
    (x : Configuration N) (i : Fin N) (hx : 2*truncationRadius k ≤ ‖x i‖) :
    (truncateForm k ψ).value s x = 0 := by
  change ((truncationMultiplier N k).value x : ℂ) * _ = _
  rw [truncation_value_zero k x i hx]
  simp

lemma truncation_gradient_zero {N : ℕ} (k : ℕ) (x : Configuration N) (i j : Fin N)
    (a : Fin 3) (hx : 2*truncationRadius k < ‖x i‖) :
    lineDeriv ℝ (truncationMultiplier N k).value x (direction j a) = 0 := by
  have he : (truncationMultiplier N k).value =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
    have hh : ∀ᶠ z : Configuration N in 𝓝 x, 2*truncationRadius k < ‖z i‖ :=
      ((continuous_apply i).norm.tendsto x).eventually (eventually_gt_nhds hx)
    exact hh.mono fun z hz => truncation_value_zero k z i hz.le
  rw [he.lineDeriv_eq (𝕜 := ℝ)]
  simp only [lineDeriv, deriv_const]

lemma truncateForm_gradient_support {N : ℕ} (k : ℕ) (ψ : FormVector N) (s : Spins N)
    (x : Configuration N) (i j : Fin N) (a : Fin 3) (hx : 2*truncationRadius k < ‖x i‖) :
    (truncateForm k ψ).gradient s j a x = 0 := by
  change ((truncationMultiplier N k).value x : ℂ) * _ +
    Complex.ofReal (lineDeriv ℝ (truncationMultiplier N k).value x (direction j a)) * _ = 0
  rw [truncation_value_zero k x i hx.le, truncation_gradient_zero k x i j a hx]
  simp

theorem admissible_compact_approximation {N : ℕ} {ψ : FormVector N}
    (hψ : FormAdmissible ψ) (Z : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∃ φ : FormVector N, FormAdmissible φ ∧
      formEnergy Z φ < formEnergy Z ψ + ε ∧
      ∀ s x i, R ≤ ‖x i‖ → φ.value s x = 0 ∧ ∀ j a, φ.gradient s j a x = 0 := by
  let φ : ℕ → FormVector N := fun k =>
    scaleForm (Real.sqrt (formMass (truncateForm k ψ)))⁻¹ (truncateForm k ψ)
  have hm := truncateForm_mass_tendsto hψ.sobolevFermion
  have hmass : formMass ψ = 1 := hψ.2.2.2.2.1
  rw [hmass] at hm
  have he : Tendsto (fun k => formEnergy Z (φ k)) atTop (𝓝 (formEnergy Z ψ)) := by
    have hh := (((Real.continuous_sqrt.tendsto 1).comp hm).inv₀ (by norm_num)).pow 2
    have hh' := hh.mul (truncateForm_energy_tendsto hψ.sobolevFermion Z)
    simpa only [φ, formEnergy_scale, Real.sqrt_one, inv_one, one_pow, one_mul, Function.comp_apply] using hh'
  have hp : ∀ᶠ k : ℕ in atTop, 0 < formMass (truncateForm k ψ) :=
    hm.eventually (eventually_gt_nhds (by norm_num : (0:ℝ) < 1))
  have hene : ∀ᶠ k : ℕ in atTop, formEnergy Z (φ k) < formEnergy Z ψ + ε :=
    he.eventually (eventually_lt_nhds (lt_add_of_pos_right _ hε))
  obtain ⟨k,hk,hke⟩ := (hp.and hene).exists
  refine ⟨3*truncationRadius k, mul_pos (by norm_num) (truncationRadius_pos k), φ k,
    (hψ.sobolevFermion.truncate k).normalize hk,hke,?_⟩
  intro s x i hx
  have hx' : 2*truncationRadius k < ‖x i‖ := by linarith [truncationRadius_pos k]
  constructor
  · change _ * (truncateForm k ψ).value s x = 0
    rw [truncateForm_support k ψ s x i hx'.le, mul_zero]
  · intro j a
    change _ * (truncateForm k ψ).gradient s j a x = 0
    rw [truncateForm_gradient_support k ψ s x i j a hx', mul_zero]

theorem quantum_sector_compact_near_minimizer (Z : ℝ) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∃ φ : FormVector N, FormAdmissible φ ∧
      formEnergy Z φ < energy Z N + ε ∧
      ∀ s x i, R ≤ ‖x i‖ → φ.value s x = 0 ∧ ∀ j a, φ.gradient s j a x = 0 := by
  obtain ⟨F,hF,he⟩ := quantum_sector_near_minimizer Z N (half_pos hε)
  obtain ⟨R,hR,φ,hφ,hq,hs⟩ := admissible_compact_approximation
    (graphFormVector_admissible F hF) Z (half_pos hε)
  exact ⟨R,hR,φ,hφ,by linarith,hs⟩

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff

end

end OAI
