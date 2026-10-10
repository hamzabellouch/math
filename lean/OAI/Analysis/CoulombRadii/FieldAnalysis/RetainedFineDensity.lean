import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.RotatedDensityPower
import OAI.Analysis.CoulombRadii.FieldAnalysis.CoulombBilinear

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
namespace Coulomb

def retainedFineDensity {n : ℕ} (b : ℝ) (r : Finset (Fin n))
    (x : Fin n → Space) (y : Space) : ℝ := ∑ i ∈ r, fineKernel b (y-x i)

lemma retainedFineDensity_nonneg {n : ℕ} (b : ℝ) (r : Finset (Fin n))
    (x : Fin n → Space) (y : Space) : 0 ≤ retainedFineDensity b r x y :=
  Finset.sum_nonneg (fun _ _ => fineKernel_nonneg ..)

lemma retainedFineDensity_le {n : ℕ} (b : ℝ) (r : Finset (Fin n))
    (x : Fin n → Space) (y : Space) : retainedFineDensity b r x y ≤ fineDensity b x y := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ r)
    (fun _ _ _ => fineKernel_nonneg ..)

lemma retainedFineDensity_integrable {n : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Finset (Fin n)) (x : Fin n → Space) : Integrable (retainedFineDensity b r x) :=
  integrable_finsetSum _ (fun i _ => fineKernel_shift_integrable hb (x i))

lemma retainedFineDensity_measurable {n : ℕ} (b : ℝ) (r : Finset (Fin n))
    (x : Fin n → Space) : Measurable (retainedFineDensity b r x) :=
  Finset.measurable_sum _ (fun _ _ => (fineKernel_continuous b).measurable.comp (by fun_prop))

lemma retainedFineDensity_integral {n : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Finset (Fin n)) (x : Fin n → Space) :
    (∫ y, retainedFineDensity b r x y) = r.card := by
  unfold retainedFineDensity
  rw [integral_finsetSum _ (fun i _ => fineKernel_shift_integrable hb (x i))]
  simp_rw [fineKernel_shift_integral hb]
  simp

lemma retainedFineDensity_coulomb_expansion {n : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Finset (Fin n)) (x : Fin n → Space) :
    coulombBilinear (retainedFineDensity b r x) (retainedFineDensity b r x) =
      ∑ i ∈ r, ∑ j ∈ r, coulombBilinear (fun y => fineKernel b (y-x i))
        (fun y => fineKernel b (y-x j)) := by
  have hi (i j : Fin n) : Integrable (fun p : Space × Space =>
      fineKernel b (p.1-x i)*fineKernel b (p.2-x j)*coulombKernel (p.1-p.2)) :=
    coulomb_pair_integrable (fineKernel_shift_integrable hb _) ((fineKernel_continuous b).measurable.comp (by fun_prop))
      (fineKernel_shift_integrable hb _) ((fineKernel_continuous b).measurable.comp (by fun_prop))
      (fun y => by rw [Real.norm_of_nonneg (fineKernel_nonneg ..)]; exact fineKernel_le hb _)
  unfold coulombBilinear retainedFineDensity
  simp_rw [Finset.sum_mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  congr 1
  ext i
  exact integral_finsetSum _ (fun j _ => hi i j)

lemma coulombKernel_sub_symm (x y : Space) : coulombKernel (x-y) = coulombKernel (y-x) := by
  unfold coulombKernel
  rw [norm_sub_rev]

theorem retained_fine_pair_lower {n : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Finset (Fin n)) (x : Fin n → Space) (hx : Function.Injective x) :
    coulombBilinear (retainedFineDensity b r x) (retainedFineDensity b r x)/2 -
      ((2*Real.pi+1)/(2*b)) * r.card ≤
      ∑ i : Fin n, ∑ j : Fin n, if i < j then coulombKernel (x i-x j) else 0 := by
  have hdiag : (∑ i ∈ r, ∑ j ∈ r,
      coulombBilinear (fun y => fineKernel b (y-x i)) (fun y => fineKernel b (y-x j))) ≤
      ∑ i ∈ r, ∑ j ∈ r, if i = j then (2*Real.pi+1)/b else coulombKernel (x i-x j) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    split_ifs with h
    · subst j; exact fineKernel_pair_self_le hb _
    · exact fineKernel_pair_le hb (hx.ne h)
  have hs (i : Fin n) : (∑ j ∈ r, if i = j then (2*Real.pi+1)/b else coulombKernel (x i-x j)) =
      (if i ∈ r then (2*Real.pi+1)/b else 0) + ∑ j ∈ r, coulombKernel (x i-x j) := by
    have hterm (j : Fin n) : (if i = j then (2*Real.pi+1)/b else coulombKernel (x i-x j)) =
        (if i = j then (2*Real.pi+1)/b else 0) + coulombKernel (x i-x j) := by
      by_cases h : i = j
      · subst j; simp [coulombKernel]
      · simp [h]
    simp_rw [hterm, Finset.sum_add_distrib]
    simp
  have hall : (∑ i ∈ r, ∑ j ∈ r, coulombKernel (x i-x j)) ≤
      ∑ i : Fin n, ∑ j : Fin n, coulombKernel (x i-x j) := by
    apply (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ r) (fun _ _ _ => coulombKernel_nonneg _))).trans
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ r)
      (fun _ _ _ => Finset.sum_nonneg (fun _ _ => coulombKernel_nonneg _))
  have hsplit : (∑ i : Fin n, ∑ j : Fin n, coulombKernel (x i-x j)) =
      2 * (∑ i : Fin n, ∑ j : Fin n, if i < j then coulombKernel (x i-x j) else 0) := by
    have h (i j : Fin n) : coulombKernel (x i-x j) =
        (if i < j then coulombKernel (x i-x j) else 0) +
        (if j < i then coulombKernel (x j-x i) else 0) := by
      rcases lt_trichotomy i j with h | h | h
      · simp [h, not_lt.mpr h.le]
      · subst j; simp [coulombKernel]
      · simp only [h, not_lt.mpr h.le, ite_false, ite_true, zero_add]
        exact coulombKernel_sub_symm _ _
    calc
      _ = ∑ i : Fin n, ∑ j : Fin n, ((if i < j then coulombKernel (x i-x j) else 0) +
          (if j < i then coulombKernel (x j-x i) else 0)) :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h i j))
      _ = _ := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i j : Fin n => if j < i then coulombKernel (x j-x i) else 0)]
        ring
  simp_rw [hs] at hdiag
  simp only [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul] at hdiag
  rw [hsplit] at hall
  rw [retainedFineDensity_coulomb_expansion hb]
  have he : ((2*Real.pi+1)/(2*b))*r.card*2 = r.card*((2*Real.pi+1)/b) := by ring
  linarith

lemma ae_position_injective (n : ℕ) : ∀ᵐ x : Configuration n, Function.Injective (position x) := by
  have hpair (i j : Fin n) (hij : i ≠ j) : ∀ᵐ x : Configuration n, position x i ≠ position x j := by
    let L : Configuration n →ₗ[ℝ] ℝ :=
      { toFun := fun x => x (i,0)-x (j,0)
        map_add' := by intro x y; simp only [PiLp.add_apply]; ring
        map_smul' := by intro c x; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
    have hL : LinearMap.ker L ≠ ⊤ := by
      intro h
      have hx : EuclideanSpace.single (i,0) (1:ℝ) ∈ LinearMap.ker L := by rw [h]; trivial
      simp [LinearMap.mem_ker, L, hij] at hx
    have hm := Measure.addHaar_submodule (volume : Measure (Configuration n)) (LinearMap.ker L) hL
    have hnull : (volume : Measure (Configuration n)) {x | position x i = position x j} = 0 := by
      apply measure_mono_null _ hm
      intro x hx
      change x (i,0)-x (j,0) = 0
      exact sub_eq_zero.mpr (congrArg (fun z : Space => z 0) hx)
    rw [ae_iff]
    simpa only [not_not] using hnull
  simp only [Function.Injective, ae_all_iff]
  intro i j
  by_cases h : i = j
  · exact Eventually.of_forall fun _ _ => h
  · exact (hpair i j h).mono fun _ hx he => (hx he).elim

lemma ae_retained_fine_pair_lower {n : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Configuration n → Finset (Fin n)) :
    ∀ᵐ x : Configuration n,
      coulombBilinear (retainedFineDensity b (r x) (position x))
        (retainedFineDensity b (r x) (position x))/2 -
      ((2*Real.pi+1)/(2*b)) * (r x).card ≤
        ∑ i : Fin n, ∑ j : Fin n, if i < j then coulombKernel (position x i-position x j) else 0 :=
  (ae_position_injective n).mono fun x hx => retained_fine_pair_lower hb (r x) (position x) hx

lemma retainedFineDensity_eq_sum_ite {n : ℕ} (b : ℝ) (r : Finset (Fin n))
    (x : Fin n → Space) (y : Space) :
    retainedFineDensity b r x y = ∑ i, if i ∈ r then fineKernel b (y-x i) else 0 := by
  simp [retainedFineDensity, Finset.sum_ite_mem]

lemma fineDensity_power_integrable {n : ℕ} {b : ℝ} (hb : 0 < b) (x : Fin n → Space) :
    Integrable (fun y => fineDensity b x y ^ (5/3:ℝ)) := by
  apply ((fineDensity_integrable hb x).const_mul ((n*(b⁻¹)^3)^(2/3:ℝ))).mono'
  · exact ((fineDensity_measurable b x).pow_const _).aestronglyMeasurable
  · exact Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (fineDensity_nonneg ..) _)]
      exact rpow_five_thirds_le_linear (fineDensity_nonneg ..) (fineDensity_le hb ..)

lemma retainedFineDensity_power_integrable {n : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Finset (Fin n)) (x : Fin n → Space) :
    Integrable (fun y => retainedFineDensity b r x y ^ (5/3:ℝ)) := by
  apply (fineDensity_power_integrable hb x).mono'
  · exact ((retainedFineDensity_measurable b r x).pow_const _).aestronglyMeasurable
  · exact Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (retainedFineDensity_nonneg ..) _)]
      exact Real.rpow_le_rpow (retainedFineDensity_nonneg ..) (retainedFineDensity_le ..) (by norm_num)

lemma retainedFineDensity_power_le {n : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Finset (Fin n)) (x : Fin n → Space) :
    (∫ y, retainedFineDensity b r x y^(5/3:ℝ)) ≤ fineDensityPower b x :=
  integral_mono (retainedFineDensity_power_integrable hb r x) (fineDensity_power_integrable hb x)
    (fun y => Real.rpow_le_rpow (retainedFineDensity_nonneg ..) (retainedFineDensity_le ..) (by norm_num))

lemma retainedFineDensity_power_configuration_measurable {n : ℕ} (b : ℝ)
    (r : Configuration n → Finset (Fin n)) (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    Measurable (fun x => ∫ y, retainedFineDensity b (r x) (position x) y^(5/3:ℝ)) := by
  have hm : Measurable (fun p : Configuration n × Space => retainedFineDensity b (r p.1) (position p.1) p.2) := by
    simp_rw [retainedFineDensity_eq_sum_ite]
    apply Finset.measurable_sum
    intro i hi
    apply Measurable.ite ((hr i).preimage measurable_fst)
    · exact (fineKernel_continuous b).measurable.comp
        (measurable_snd.sub ((continuous_position i).measurable.comp measurable_fst))
    · exact measurable_const
  exact (hm.pow_const (5/3:ℝ)).stronglyMeasurable.integral_prod_right'.measurable

lemma retainedFineDensity_power_weight_integrable {n : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Configuration n → Finset (Fin n)) (hr : ∀ i, MeasurableSet {x | i ∈ r x})
    {w : Configuration n → ℝ} (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x) :
    Integrable (fun x => (∫ y, retainedFineDensity b (r x) (position x) y^(5/3:ℝ))*w x) := by
  apply (weighted_fineDensityPower_integrable hb hw hw0).mono'
  · exact (retainedFineDensity_power_configuration_measurable b r hr).aestronglyMeasurable.mul
      hw.aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (integral_nonneg (fun y =>
        Real.rpow_nonneg (retainedFineDensity_nonneg ..) _)) (hw0 x))]
      exact mul_le_mul_of_nonneg_right (retainedFineDensity_power_le hb (r x) (position x)) (hw0 x)

theorem retained_fine_kinetic_lower {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {b : ℝ} (hb : 0 < b)
    (r : Configuration n → Finset (Fin n)) (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    thomasFermiCoefficient * (∑ s, ∫ x : Configuration n,
      (∫ y, retainedFineDensity b (r x) (position x) y^(5/3:ℝ))*‖ψ.value s x‖^2) -
      ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n:ℝ)^(4/3:ℝ)) * mass ψ ≤ kinetic ψ := by
  apply le_trans _ (fine_density_kinetic_lower hn ψ hψ hb)
  apply sub_le_sub_right
  apply mul_le_mul_of_nonneg_left _ (by unfold thomasFermiCoefficient; positivity)
  apply Finset.sum_le_sum
  intro s hs
  have hw : Integrable (fun x => ‖ψ.value s x‖^2) :=
    (ψ.value_L2 s).integrable_norm_pow (p:=2) (by decide)
  exact integral_mono (retainedFineDensity_power_weight_integrable hb r hr hw (fun _ => sq_nonneg _))
    (weighted_fineDensityPower_integrable hb hw (fun _ => sq_nonneg _))
    (fun x => mul_le_mul_of_nonneg_right (retainedFineDensity_power_le hb _ _) (sq_nonneg _))
end Coulomb

end

end OAI
