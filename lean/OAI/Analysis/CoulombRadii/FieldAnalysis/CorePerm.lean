import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.Add
import OAI.Analysis.CoulombRadii.FormDomain.CoreSliceRegular

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
namespace Coulomb

noncomputable def corePerm (m : ℕ) {k : ℕ} (p : Equiv.Perm (Fin k)) :
    Equiv.Perm (Fin (m+k)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr (Equiv.refl (Fin m)) p)

lemma corePerm_left (m : ℕ) {k : ℕ} (p : Equiv.Perm (Fin k)) (i : Fin m) :
    corePerm m p (Fin.castAdd k i) = Fin.castAdd k i := by
  simp [corePerm]

lemma corePerm_right (m : ℕ) {k : ℕ} (p : Equiv.Perm (Fin k)) (i : Fin k) :
    corePerm m p (Fin.natAdd m i) = Fin.natAdd m (p i) := by
  simp [corePerm]

lemma corePerm_sign (m : ℕ) {k : ℕ} (p : Equiv.Perm (Fin k)) :
    (corePerm m p).sign = p.sign := by
  simp [corePerm, Equiv.Perm.sign_sumCongr]

lemma append_corePerm {m k : ℕ} (s : Spins m) (t : Spins k) (p : Equiv.Perm (Fin k)) :
    Fin.append s t ∘ corePerm m p = Fin.append s (t ∘ p) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [corePerm_left]
  · intro j
    simp [corePerm_right]

lemma permute_core_join {m k : ℕ} (p : Equiv.Perm (Fin k)) (x : Configuration m)
    (y : Configuration k) :
    permute (corePerm m p) (joinConfiguration m k (x,y)) =
      joinConfiguration m k (x, permute p y) := by
  ext ⟨i,b⟩
  refine Fin.addCases ?_ ?_ i
  · intro j
    change joinConfiguration m k (x,y) (corePerm m p (Fin.castAdd k j),b) = _
    rw [corePerm_left, joinConfiguration_left, joinConfiguration_left]
  · intro j
    change joinConfiguration m k (x,y) (corePerm m p (Fin.natAdd m j),b) = _
    rw [corePerm_right, joinConfiguration_right, joinConfiguration_right]
    rfl

lemma H1Vector.coreSlice_antisymmetric {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m)
    (hψ : ∀ (p : Equiv.Perm (Fin k)) (t : Spins k),
      ∀ᵐ z ∂volume, ψ.value (Fin.append s t ∘ corePerm m p) (permute (corePerm m p) z) =
        (((corePerm m p).sign : ℤ) : ℂ) * ψ.value (Fin.append s t) z) :
    ∀ᵐ x ∂volume, Antisymmetric (ψ.coreSlice s x) := by
  have h (p : Equiv.Perm (Fin k)) (t : Spins k) :=
    Measure.ae_ae_of_ae_prod ((joinConfiguration_measurePreserving m k).quasiMeasurePreserving.ae (hψ p t))
  have hall := ae_all_iff.mpr (fun p => ae_all_iff.mpr (h p))
  filter_upwards [ψ.coreSliceRegular_ae s, hall] with x hx hxA
  intro p t
  filter_upwards [hxA p t] with y hy
  change ψ.value (Fin.append s t ∘ corePerm m p)
      (permute (corePerm m p) (joinConfiguration m k (x,y))) =
    (((corePerm m p).sign : ℤ) : ℂ) * ψ.value (Fin.append s t)
      (joinConfiguration m k (x,y)) at hy
  simpa only [ψ.coreSlice_value s hx, append_corePerm, corePerm_sign, permute_core_join] using hy

lemma Antisymmetric.coreSlice {m k : ℕ} {ψ : H1Vector (m+k)} (hψ : Antisymmetric ψ)
    (s : Spins m) : ∀ᵐ x ∂volume, Antisymmetric (ψ.coreSlice s x) :=
  ψ.coreSlice_antisymmetric s (fun p t => hψ (corePerm m p) (Fin.append s t))

lemma H1Vector.value_eq_zero_of_mass_zero {n : ℕ} (ψ : H1Vector n)
    (hψ : mass ψ = 0) (s : Spins n) : ψ.value s =ᵐ[volume] 0 := by
  have hnon (t : Spins n) : 0 ≤ ∫ x, ‖ψ.value t x‖^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hz : (∫ x, ‖ψ.value s x‖^2) = 0 := by
    apply le_antisymm _ (hnon s)
    exact hψ ▸ Finset.single_le_sum (fun t _ => hnon t) (Finset.mem_univ s)
  have ha := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖ψ.value s x‖)
    ((ψ.value_L2 s).integrable_norm_pow (p := 2) (by decide))).mp hz
  filter_upwards [ha] with x hx
  simpa using hx

lemma H1Vector.gradient_eq_zero_of_mass_zero {n : ℕ} (ψ : H1Vector n)
    (hψ : mass ψ = 0) (s : Spins n) (a : Fin n × Fin 3) :
    ψ.gradient s a =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((ψ.partial_L2 s a).locallyIntegrable (by norm_num))
  intro φ hφ hφC
  have H := ψ.weak_partial s a φ hφ hφC
  have hv : (∫ x, ψ.value s x *
      (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ψ.value_eq_zero_of_mass_zero hψ s] with x hx
    simp [hx]
  rw [hv, eq_neg_iff_add_eq_zero, zero_add] at H
  simpa only [Complex.real_smul, mul_comm] using H

lemma kinetic_eq_zero_of_mass_zero {n : ℕ} (ψ : H1Vector n)
    (hψ : mass ψ = 0) : kinetic ψ = 0 := by
  have hzero (s : Spins n) (a : Fin n × Fin 3) : ∫ x, ‖ψ.gradient s a x‖^2 = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ψ.gradient_eq_zero_of_mass_zero hψ s a] with x hx
    simp [hx]
  simp [kinetic, hzero]

lemma kinetic_coreSlice_ae {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m) :
    (fun x => kinetic (ψ.coreSlice s x)) =ᵐ[volume]
      fun x => (1/2 : ℝ) * ∑ t : Spins k, ∑ a : Fin k × Fin 3,
        ∫ y, ‖ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2)
          (joinConfiguration m k (x,y))‖^2 := by
  filter_upwards [ψ.coreSliceRegular_ae s] with x hx
  simp only [kinetic, ψ.coreSlice_gradient s hx]

lemma kinetic_coreSlice_integrable {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m) :
    Integrable (fun x => kinetic (ψ.coreSlice s x)) := by
  apply Integrable.congr _ (kinetic_coreSlice_ae ψ s).symm
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro t _
  apply integrable_finsetSum
  intro a _
  exact (((ψ.partial_L2 (Fin.append s t) (Fin.natAdd m a.1,a.2)).comp_measurePreserving
    (joinConfiguration_measurePreserving m k)).integrable_norm_pow (p := 2) (by decide)).integral_prod_left

lemma integral_kinetic_coreSlice {m k : ℕ} (ψ : H1Vector (m+k)) :
    (∑ s : Spins m, ∫ x, kinetic (ψ.coreSlice s x)) =
      (1/2 : ℝ) * ∑ st : Spins (m+k), ∑ a : Fin k × Fin 3,
        ∫ z, ‖ψ.gradient st (Fin.natAdd m a.1,a.2) z‖^2 := by
  have hs (s : Spins m) : (∫ x, kinetic (ψ.coreSlice s x)) =
      (1/2 : ℝ) * ∑ t : Spins k, ∑ a : Fin k × Fin 3,
        ∫ z, ‖ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2) z‖^2 := by
    rw [integral_congr_ae (kinetic_coreSlice_ae ψ s), integral_const_mul]
    congr 1
    have hi (t : Spins k) (a : Fin k × Fin 3) :
        Integrable (fun z : Configuration m × Configuration k =>
          ‖ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2) (joinConfiguration m k z)‖^2)
          (volume.prod volume) :=
      ((ψ.partial_L2 (Fin.append s t) (Fin.natAdd m a.1,a.2)).comp_measurePreserving
        (joinConfiguration_measurePreserving m k)).integrable_norm_pow (p := 2) (by decide)
    rw [integral_finsetSum _ (fun t _ => integrable_finsetSum _ (fun a _ => (hi t a).integral_prod_left))]
    apply Finset.sum_congr rfl
    intro t _
    rw [integral_finsetSum _ (fun a _ => (hi t a).integral_prod_left)]
    apply Finset.sum_congr rfl
    intro a _
    rw [← integral_prod _ (hi t a)]
    exact (joinConfiguration_measurePreserving m k).integral_comp'
      (fun z => ‖ψ.gradient (Fin.append s t) (Fin.natAdd m a.1,a.2) z‖^2)
  simp_rw [hs]
  rw [← Finset.mul_sum, ← Fintype.sum_prod_type (f := fun st : Spins m × Spins k =>
    ∑ a : Fin k × Fin 3, ∫ z, ‖ψ.gradient (Fin.append st.1 st.2) (Fin.natAdd m a.1,a.2) z‖^2)]
  congr 1
  exact Fintype.sum_equiv (Fin.appendEquiv m k) _ _ (fun _ => rfl)

noncomputable def H1Vector.normalized {n : ℕ} (ψ : H1Vector n) : H1Vector n :=
  ψ.rsmul (Real.sqrt (mass ψ))⁻¹

lemma mass_normalized {n : ℕ} (ψ : H1Vector n) (hψ : 0 < mass ψ) :
    mass ψ.normalized = 1 := by
  rw [H1Vector.normalized, mass_rsmul, inv_pow, Real.sq_sqrt hψ.le, inv_mul_cancel₀ hψ.ne']

lemma Antisymmetric.normalized {n : ℕ} {ψ : H1Vector n} (hψ : Antisymmetric ψ) :
    Antisymmetric ψ.normalized := hψ.rsmul _

lemma kinetic_normalized_weight {n : ℕ} (ψ : H1Vector n) :
    mass ψ * kinetic ψ.normalized = kinetic ψ := by
  have hm : 0 ≤ mass ψ := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  by_cases hz : mass ψ = 0
  · rw [hz, zero_mul, kinetic_eq_zero_of_mass_zero ψ hz]
  · rw [H1Vector.normalized, kinetic_rsmul, inv_pow, Real.sq_sqrt hm, ← mul_assoc,
      mul_inv_cancel₀ hz, one_mul]

lemma conditional_core_kinetic_identity {m k : ℕ} (ψ : H1Vector (m+k)) :
    (∑ s : Spins m, ∫ x, mass (ψ.coreSlice s x) * kinetic (ψ.coreSlice s x).normalized) =
      (1/2 : ℝ) * ∑ st : Spins (m+k), ∑ a : Fin k × Fin 3,
        ∫ z, ‖ψ.gradient st (Fin.natAdd m a.1,a.2) z‖^2 := by
  simp_rw [kinetic_normalized_weight]
  exact integral_kinetic_coreSlice ψ

noncomputable def potentialForm {n : ℕ} (V : Configuration n → ℝ) (ψ : H1Vector n) : ℝ :=
  ∑ s, ∫ x, V x * ‖ψ.value s x‖^2

lemma potentialForm_rsmul {n : ℕ} (V : Configuration n → ℝ) (ψ : H1Vector n) (t : ℝ) :
    potentialForm V (ψ.rsmul t) = t^2 * potentialForm V ψ := by
  simp only [potentialForm, H1Vector.rsmul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]
  simp_rw [mul_left_comm (V _) (t^2), integral_const_mul, ← Finset.mul_sum]

lemma potentialForm_eq_zero_of_mass_zero {n : ℕ} (V : Configuration n → ℝ)
    (ψ : H1Vector n) (hψ : mass ψ = 0) : potentialForm V ψ = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  apply integral_eq_zero_of_ae
  filter_upwards [ψ.value_eq_zero_of_mass_zero hψ s] with x hx
  simp [hx]

lemma potentialForm_normalized_weight {n : ℕ} (V : Configuration n → ℝ) (ψ : H1Vector n) :
    mass ψ * potentialForm V ψ.normalized = potentialForm V ψ := by
  have hm : 0 ≤ mass ψ := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  by_cases hz : mass ψ = 0
  · rw [hz, zero_mul, potentialForm_eq_zero_of_mass_zero V ψ hz]
  · rw [H1Vector.normalized, potentialForm_rsmul, inv_pow, Real.sq_sqrt hm, ← mul_assoc,
      mul_inv_cancel₀ hz, one_mul]

lemma potentialForm_coreSlice_ae {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m)
    (V : Configuration k → ℝ) :
    (fun x => potentialForm V (ψ.coreSlice s x)) =ᵐ[volume]
      fun x => ∑ t : Spins k, ∫ y, V y * ‖ψ.value (Fin.append s t) (joinConfiguration m k (x,y))‖^2 := by
  filter_upwards [ψ.coreSliceRegular_ae s] with x hx
  simp only [potentialForm, ψ.coreSlice_value s hx]

lemma potentialForm_coreSlice_integrable {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m)
    (V : Configuration k → ℝ)
    (hV : ∀ t : Spins k, Integrable (fun z => V ((joinConfiguration m k).symm z).2 *
      ‖ψ.value (Fin.append s t) z‖^2)) :
    Integrable (fun x => potentialForm V (ψ.coreSlice s x)) := by
  apply Integrable.congr _ (potentialForm_coreSlice_ae ψ s V).symm
  apply integrable_finsetSum
  intro t _
  have H := ((joinConfiguration_measurePreserving m k).integrable_comp_emb
    (joinConfiguration m k).toHomeomorph.toMeasurableEquiv.measurableEmbedding).mpr (hV t)
  have H' : Integrable (fun z : Configuration m × Configuration k =>
      V z.2 * ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2) (volume.prod volume) := by
    change Integrable (fun z : Configuration m × Configuration k =>
      V ((joinConfiguration m k).symm (joinConfiguration m k z)).2 *
        ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2) (volume.prod volume) at H
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using H
  exact H'.integral_prod_left

lemma integral_potentialForm_coreSlice {m k : ℕ} (ψ : H1Vector (m+k))
    (V : Configuration k → ℝ)
    (hV : ∀ st : Spins (m+k), Integrable (fun z => V ((joinConfiguration m k).symm z).2 *
      ‖ψ.value st z‖^2)) :
    (∑ s : Spins m, ∫ x, potentialForm V (ψ.coreSlice s x)) =
      ∑ st : Spins (m+k), ∫ z, V ((joinConfiguration m k).symm z).2 * ‖ψ.value st z‖^2 := by
  have hs (s : Spins m) : (∫ x, potentialForm V (ψ.coreSlice s x)) =
      ∑ t : Spins k, ∫ z, V ((joinConfiguration m k).symm z).2 * ‖ψ.value (Fin.append s t) z‖^2 := by
    rw [integral_congr_ae (potentialForm_coreSlice_ae ψ s V)]
    have hi (t : Spins k) : Integrable (fun z : Configuration m × Configuration k =>
        V z.2 * ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2) (volume.prod volume) := by
      have H := ((joinConfiguration_measurePreserving m k).integrable_comp_emb
        (joinConfiguration m k).toHomeomorph.toMeasurableEquiv.measurableEmbedding).mpr
        (hV (Fin.append s t))
      change Integrable (fun z : Configuration m × Configuration k =>
        V ((joinConfiguration m k).symm (joinConfiguration m k z)).2 *
          ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2) (volume.prod volume) at H
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using H
    rw [integral_finsetSum _ (fun t _ => (hi t).integral_prod_left)]
    apply Finset.sum_congr rfl
    intro t _
    rw [← integral_prod _ (hi t)]
    have H := (joinConfiguration_measurePreserving m k).integral_comp'
        (fun z => V ((joinConfiguration m k).symm z).2 * ‖ψ.value (Fin.append s t) z‖^2)
    change (∫ z : Configuration m × Configuration k,
        V ((joinConfiguration m k).symm (joinConfiguration m k z)).2 *
          ‖ψ.value (Fin.append s t) (joinConfiguration m k z)‖^2 ∂volume.prod volume) = _ at H
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using H
  simp_rw [hs]
  rw [← Fintype.sum_prod_type (f := fun st : Spins m × Spins k =>
    ∫ z, V ((joinConfiguration m k).symm z).2 * ‖ψ.value (Fin.append st.1 st.2) z‖^2)]
  exact Fintype.sum_equiv (Fin.appendEquiv m k) _ _ (fun _ => rfl)

end Coulomb

end

end OAI
