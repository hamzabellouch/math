import Mathlib
import OAI.Combinatorics.StripMass.HeightOne

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
theorem columnVertex_adjacent (k : ℕ) : adjacent (columnVertex k) (columnVertex (k + 1)) := by
  simp only [columnVertex]
  split_ifs <;> simp [adjacent, upDownAdjacent, up, down] <;> omega

 
def diagonalBridge (N : ℕ) : List Triangle := (List.range (2 * N)).map columnVertex

@[simp] theorem diagonalBridge_length (N : ℕ) : (diagonalBridge N).length = 2 * N := by
  simp [diagonalBridge]

theorem diagonalBridge_spec {N : ℕ} (hN : 0 < N) :
    IsPath N (down 0 (N - 1)) (diagonalBridge N) := by
  have h2N : 2 * N ≠ 0 := by omega
  have hl : columnVertex (2 * N - 1) = down 0 (N - 1) := by
    have he : (2 * N - 1) % 2 ≠ 0 := by omega
    have hd : (2 * N - 1) / 2 = N - 1 := by omega
    simp [columnVertex, he, hd]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [diagonalBridge, List.head?_map, List.head?_range, h2N, columnVertex]
  · simp [diagonalBridge, List.getLast?_map, List.getLast?_range, h2N, hl]
  · exact List.nodup_range.map columnVertex_injective
  · apply (List.isChain_map _).mpr
    apply (List.isChain_range _ _).mpr
    intro k hk
    exact columnVertex_adjacent k
  · intro v hv
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
    simp only [List.mem_range] at hk
    simp only [columnVertex_band]
    omega

theorem diagonalBridge_weight {N : ℕ} (hN : 0 < N) :
    bridgeWeight N 0 (diagonalBridge N) = rho ^ (2 * N) := by
  classical
  simp only [bridgeWeight, hN, diagonalBridge_spec hN, and_self, ↓reduceIte,
    diagonalBridge_length]

 

theorem bridgeMass_lower_bound {N : ℕ} (hN : 1 ≤ N) (hf : StripSumsFinite N) :
    rho ^ (2 * N) ≤ bridgeMass N := by
  calc
    rho ^ (2 * N) = bridgeWeight N 0 (diagonalBridge N) := (diagonalBridge_weight (by omega)).symm
    _ ≤ bridgeKernel N 0 := (hf.2.1 0).le_tsum (diagonalBridge N) (by
      intro p hp
      exact bridgeWeight_nonneg N 0 p)
    _ ≤ bridgeMass N := hf.2.2.2.1.le_tsum 0 (by
      intro k hk
      exact bridgeKernel_nonneg N k)

theorem bridgeMass_pos_of_finite {N : ℕ} (hN : 1 ≤ N) (hf : StripSumsFinite N) :
    0 < bridgeMass N := lt_of_lt_of_le (pow_pos rho_pos _) (bridgeMass_lower_bound hN hf)

theorem moment_lower_bound {N : ℕ} (hN : 1 ≤ N) (hf : StripSumsFinite N) :
    rho ^ 3 / (1 - rho ^ 2) ^ 2 ≤ moment N := by
  rw [← moment_one]
  exact moment_le_of_finite hN hf

theorem moment_pos_of_finite {N : ℕ} (hN : 1 ≤ N) (hf : StripSumsFinite N) :
    0 < moment N := by
  apply lt_of_lt_of_le _ (moment_lower_bound hN hf)
  exact div_pos (pow_pos rho_pos _) (sq_pos_of_pos (sub_pos.mpr rho_sq_lt_one))

end

 

noncomputable section
open scoped BigOperators
open Set MeasureTheory

 
def laguerreDomain (N : ℕ) : Set (Fin N → ℝ) :=
  {r | StrictMono r ∧ ∀ i, 0 < r i}

def laguerreWeight (a x : ℝ) : ℝ := x ^ (a - 1) * Real.exp (-x)

def laguerreDensity (N : ℕ) (a : ℝ) (r : Fin N → ℝ) : ℝ :=
  (∏ i, laguerreWeight a (r i)) *
    ∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (r i) (r j)

def laguerreNormalizer (N : ℕ) (a : ℝ) : ℝ :=
  ∫ r in laguerreDomain N, laguerreDensity N a r

def laguerreExpectation (N : ℕ) (a : ℝ) (f : (Fin N → ℝ) → ℝ) : ℝ :=
  (∫ r in laguerreDomain N, f r * laguerreDensity N a r) / laguerreNormalizer N a

theorem laguerreWeight_pos (a : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < laguerreWeight a x :=
  mul_pos (Real.rpow_pos_of_pos hx _) (Real.exp_pos _)

theorem measurable_laguerreWeight (a : ℝ) : Measurable (laguerreWeight a) := by
  unfold laguerreWeight
  fun_prop

theorem laguerreDensity_pos {N : ℕ} (a : ℝ) {r : Fin N → ℝ}
    (hr : r ∈ laguerreDomain N) : 0 < laguerreDensity N a r := by
  apply mul_pos
  · exact Finset.prod_pos fun i _ => laguerreWeight_pos a (hr.2 i)
  · apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    exact pairKernel_pos (hr.2 i) (hr.1 (Finset.mem_Ioi.1 hj))

theorem measurable_laguerreDensity (N : ℕ) (a : ℝ) :
    Measurable (laguerreDensity N a) := by
  unfold laguerreDensity pairKernel
  apply Measurable.mul
  · exact Finset.measurable_prod _ fun i _ =>
      (measurable_laguerreWeight a).comp (measurable_pi_apply i)
  · apply Finset.measurable_prod
    intro i _
    apply Finset.measurable_prod
    intro j _
    fun_prop

theorem isOpen_laguerreDomain (N : ℕ) : IsOpen (laguerreDomain N) := by
  have heq : laguerreDomain N =
      (⋂ i : Fin N, ⋂ j : Fin N, ⋂ (_ : i < j), {r | r i < r j}) ∩
      (⋂ i : Fin N, {r | 0 < r i}) := by
    ext r
    simp only [laguerreDomain, mem_ofPred_eq, mem_inter_iff, mem_iInter, StrictMono]
  rw [heq]
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt (continuous_apply i) (continuous_apply j)
  · exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (continuous_apply i)

theorem laguerreDomain_nonempty (N : ℕ) : (laguerreDomain N).Nonempty := by
  refine ⟨fun i => (i : ℝ) + 1, ?_, ?_⟩
  · intro i j hij
    dsimp
    exact_mod_cast (show i.val + 1 < j.val + 1 by omega)
  · intro i
    positivity

theorem pairKernel_le_right {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hxy : x ≤ y) :
    pairKernel x y ≤ y := by
  unfold pairKernel
  apply (div_le_iff₀ (by linarith : 0 < y + x)).2
  have hxx := mul_le_mul_of_nonneg_left hxy hx
  nlinarith [mul_nonneg hx hy.le]

theorem prod_pair_right (N : ℕ) (r : Fin N → ℝ) :
    (∏ i, ∏ j ∈ Finset.Ioi i, r j) = ∏ j, r j ^ j.val := by
  classical
  calc
    (∏ i, ∏ j ∈ Finset.Ioi i, r j) =
        ∏ i, ∏ j : Fin N, if i < j then r j else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← Finset.prod_filter]
      congr 1
      ext j
      simp
    _ = ∏ j : Fin N, ∏ i : Fin N, if i < j then r j else 1 := Finset.prod_comm
    _ = ∏ j : Fin N, r j ^ j.val := by
      apply Finset.prod_congr rfl
      intro j _
      rw [← Finset.prod_filter]
      simp [show Finset.univ.filter (fun i : Fin N => i < j) = Finset.Iio j by ext; simp]

theorem laguerreDensity_le_product {N : ℕ} (a : ℝ) {r : Fin N → ℝ}
    (hr : r ∈ laguerreDomain N) :
    laguerreDensity N a r ≤ ∏ i, laguerreWeight (a + i.val) (r i) := by
  have hp : (∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (r i) (r j)) ≤
      ∏ i, ∏ j ∈ Finset.Ioi i, r j := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact Finset.prod_nonneg fun j _ => pairKernel_nonneg (hr.2 i).le (hr.2 j).le
    · intro i _
      apply Finset.prod_le_prod₀
      · intro j _
        exact pairKernel_nonneg (hr.2 i).le (hr.2 j).le
      · intro j hj
        exact pairKernel_le_right (hr.2 i).le (hr.2 j) (hr.1 (Finset.mem_Ioi.1 hj)).le
  rw [prod_pair_right] at hp
  calc
    laguerreDensity N a r ≤ (∏ i, laguerreWeight a (r i)) * ∏ i, r i ^ i.val :=
      mul_le_mul_of_nonneg_left hp (Finset.prod_nonneg fun i _ => (laguerreWeight_pos a (hr.2 i)).le)
    _ = ∏ i, laguerreWeight (a + i.val) (r i) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      unfold laguerreWeight
      rw [show a + (i.val : ℝ) - 1 = (a - 1) + (i.val : ℝ) by ring,
        Real.rpow_add (hr.2 i), Real.rpow_natCast]
      ring

theorem integrableOn_laguerreWeight {a : ℝ} (ha : 0 < a) :
    IntegrableOn (laguerreWeight a) (Ioi 0) := by
  change IntegrableOn (fun x : ℝ => x ^ (a - 1) * Real.exp (-x)) (Ioi 0)
  simpa only [mul_comm] using Real.GammaIntegral_convergent ha

theorem integral_laguerreWeight {a : ℝ} (ha : 0 < a) :
    (∫ x in Ioi 0, laguerreWeight a x) = Real.Gamma a := by
  simpa only [laguerreWeight, mul_comm] using (Real.Gamma_eq_integral ha).symm

theorem integrableOn_laguerre_product {N : ℕ} {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun r : Fin N → ℝ => ∏ i, laguerreWeight (a + i.val) (r i))
      (Set.univ.pi fun _ : Fin N => Ioi (0 : ℝ)) := by
  unfold IntegrableOn
  rw [volume_pi, Measure.restrict_pi_pi]
  exact Integrable.fintype_prod fun i =>
    integrableOn_laguerreWeight (by positivity : 0 < a + (i.val : ℝ))

theorem integrableOn_laguerreDensity (N : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (laguerreDensity N a) (laguerreDomain N) := by
  have hp := (integrableOn_laguerre_product (N := N) ha).mono_set
    (show laguerreDomain N ⊆ Set.univ.pi (fun _ : Fin N => Ioi (0 : ℝ)) from
      fun r hr i _ => hr.2 i)
  apply hp.mono' (measurable_laguerreDensity N a).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
  simpa only [Real.norm_eq_abs, abs_of_pos (laguerreDensity_pos a hr)] using
    laguerreDensity_le_product a hr

theorem laguerreNormalizer_pos (N : ℕ) {a : ℝ} (ha : 0 < a) :
    0 < laguerreNormalizer N a := by
  have hpos : 0 ≤ᵐ[volume.restrict (laguerreDomain N)] laguerreDensity N a := by
    filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
    exact (laguerreDensity_pos a hr).le
  apply (integral_pos_iff_support_of_nonneg_ae hpos (integrableOn_laguerreDensity N ha)).2
  have hs : laguerreDomain N ⊆ Function.support (laguerreDensity N a) :=
    fun r hr => (laguerreDensity_pos a hr).ne'
  calc
    0 < volume (laguerreDomain N) :=
      (isOpen_laguerreDomain N).measure_pos volume (laguerreDomain_nonempty N)
    _ = (volume.restrict (laguerreDomain N)) (laguerreDomain N) :=
      (Measure.restrict_apply_self _ _).symm
    _ ≤ (volume.restrict (laguerreDomain N)) (Function.support (laguerreDensity N a)) :=
      measure_mono hs

theorem integral_laguerre_product (N : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ r : Fin N → ℝ in Set.univ.pi (fun _ => Ioi 0),
      ∏ i, laguerreWeight (a + i.val) (r i)) = ∏ i : Fin N, Real.Gamma (a + i.val) := by
  rw [volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact integral_laguerreWeight (by positivity)

theorem laguerreNormalizer_le_gamma_product (N : ℕ) {a : ℝ} (ha : 0 < a) :
    laguerreNormalizer N a ≤ ∏ i : Fin N, Real.Gamma (a + i.val) := by
  have hs : laguerreDomain N ⊆ Set.univ.pi (fun _ : Fin N => Ioi (0 : ℝ)) :=
    fun r hr i _ => hr.2 i
  have hprod := integrableOn_laguerre_product (N := N) ha
  calc
    laguerreNormalizer N a ≤ ∫ r in laguerreDomain N,
        ∏ i, laguerreWeight (a + i.val) (r i) := by
      apply integral_mono_ae (integrableOn_laguerreDensity N ha) (hprod.mono_set hs)
      filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
      exact laguerreDensity_le_product a hr
    _ ≤ ∫ r : Fin N → ℝ in Set.univ.pi (fun _ => Ioi 0),
        ∏ i, laguerreWeight (a + i.val) (r i) := by
      apply setIntegral_mono_set hprod ?_ (Filter.Eventually.of_forall hs)
      filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioi)] with r hr
      exact Finset.prod_nonneg fun i _ => (laguerreWeight_pos _ (hr i (mem_univ i))).le
    _ = ∏ i : Fin N, Real.Gamma (a + i.val) := integral_laguerre_product N ha

 

theorem integrableOn_laguerre_inverse_coordinate {N : ℕ} {a p : ℝ}
    (ha : 0 < a) (i : Fin N) (hp : p < a + i.val) :
    IntegrableOn (fun r => (r i) ^ (-p) * laguerreDensity N a r) (laguerreDomain N) := by
  classical
  let b : Fin N → ℝ := fun j => a + j.val - if j = i then p else 0
  have hb : ∀ j, 0 < b j := by
    intro j
    by_cases hj : j = i
    · simpa [b, hj] using sub_pos.mpr hp
    · simp only [b, hj, ite_false, sub_zero]
      positivity
  have heq : ∀ r : Fin N → ℝ, (∀ j, 0 < r j) →
      (r i) ^ (-p) * (∏ j, laguerreWeight (a + j.val) (r j)) =
        ∏ j, laguerreWeight (b j) (r j) := by
    intro r hr
    calc
      _ = (∏ j, if j = i then (r j) ^ (-p) else 1) *
          ∏ j, laguerreWeight (a + j.val) (r j) := by simp
      _ = ∏ j, (if j = i then (r j) ^ (-p) else 1) *
          laguerreWeight (a + j.val) (r j) := (Finset.prod_mul_distrib).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro j _
        by_cases hj : j = i
        · simp only [b, hj, ite_true, laguerreWeight]
          rw [show a + (i.val : ℝ) - p - 1 = -p + (a + i.val - 1) by ring,
            Real.rpow_add (hr i)]
          ring
        · simp [b, hj]
  have hi : IntegrableOn (fun r : Fin N → ℝ => ∏ j, laguerreWeight (b j) (r j))
      (Set.univ.pi fun _ : Fin N => Ioi (0 : ℝ)) := by
    unfold IntegrableOn
    rw [volume_pi, Measure.restrict_pi_pi]
    exact Integrable.fintype_prod fun j => integrableOn_laguerreWeight (hb j)
  have hs : laguerreDomain N ⊆ Set.univ.pi (fun _ : Fin N => Ioi (0 : ℝ)) :=
    fun r hr j _ => hr.2 j
  apply (hi.mono_set hs).mono'
    (((measurable_pi_apply i).pow_const _).mul (measurable_laguerreDensity N a)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
  change ‖(r i) ^ (-p) * laguerreDensity N a r‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos (hr.2 i) _).le
    (laguerreDensity_pos a hr).le),
    ← heq r hr.2]
  exact mul_le_mul_of_nonneg_left (laguerreDensity_le_product a hr)
    (Real.rpow_pos_of_pos (hr.2 i) _).le

 

theorem integrableOn_laguerre_inverseQuarterSum {N : ℕ} {a : ℝ} (ha : 1 / 4 < a) :
    IntegrableOn (fun r : Fin N → ℝ => (∑ i, (r i)⁻¹) ^ (1 / 4 : ℝ) *
      laguerreDensity N a r) (laguerreDomain N) := by
  have hi : IntegrableOn (fun r : Fin N → ℝ =>
      ∑ i, (r i) ^ (-(1 / 4 : ℝ)) * laguerreDensity N a r) (laguerreDomain N) :=
    integrable_finsetSum _ fun i _ =>
      integrableOn_laguerre_inverse_coordinate (by linarith : 0 < a) i
        (by
          have h : (0 : ℝ) ≤ i.val := by positivity
          linarith)
  have hm : Measurable (fun r : Fin N → ℝ =>
      (∑ i, (r i)⁻¹) ^ (1 / 4 : ℝ) * laguerreDensity N a r) := by
    apply Measurable.mul _ (measurable_laguerreDensity N a)
    fun_prop
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
  have hh : 0 ≤ ∑ i : Fin N, (r i)⁻¹ := Finset.sum_nonneg fun i _ => (inv_pos.mpr (hr.2 i)).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hh _)
    (laguerreDensity_pos a hr).le), ← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ (laguerreDensity_pos a hr).le
  calc
    (∑ i : Fin N, (r i)⁻¹) ^ (1 / 4 : ℝ) ≤ ∑ i : Fin N, ((r i)⁻¹) ^ (1 / 4 : ℝ) :=
      fourthRoot_sum_le_sum _ _ (fun i _ => (inv_pos.mpr (hr.2 i)).le)
    _ = ∑ i : Fin N, (r i) ^ (-(1 / 4 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.inv_rpow (hr.2 i).le, Real.rpow_neg (hr.2 i).le]

 

def laguerreLaw (N : ℕ) (a : ℝ) : Measure (Fin N → ℝ) :=
  (ENNReal.ofReal (laguerreNormalizer N a))⁻¹ •
    (volume.restrict (laguerreDomain N)).withDensity
      (fun r => ENNReal.ofReal (laguerreDensity N a r))

theorem laguerreLaw_isProbabilityMeasure (N : ℕ) {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (laguerreLaw N a) := by
  refine ⟨?_⟩
  rw [laguerreLaw, Measure.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal (integrableOn_laguerreDensity N ha)]
  · exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (laguerreNormalizer_pos N ha)).ne'
      ENNReal.ofReal_ne_top
  · filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
    exact (laguerreDensity_pos a hr).le

theorem ae_laguerreDomain (N : ℕ) (a : ℝ) :
    ∀ᵐ r ∂laguerreLaw N a, r ∈ laguerreDomain N := by
  apply Measure.ae_smul_measure
  apply (ae_withDensity_iff (measurable_laguerreDensity N a).ennreal_ofReal).2
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
  exact fun _ => hr

theorem integral_laguerreLaw (N : ℕ) {a : ℝ} (ha : 0 < a) (f : (Fin N → ℝ) → ℝ) :
    (∫ r, f r ∂laguerreLaw N a) = laguerreExpectation N a f := by
  rw [laguerreLaw, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul (measurable_laguerreDensity N a).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (laguerreNormalizer_pos N ha).le,
    smul_eq_mul, laguerreExpectation, div_eq_mul_inv]
  rw [mul_comm]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
  rw [ENNReal.toReal_ofReal (laguerreDensity_pos a hr).le, mul_comm]

theorem integrable_laguerreLaw {N : ℕ} {a : ℝ} (ha : 0 < a)
    {f : (Fin N → ℝ) → ℝ}
    (hf : IntegrableOn (fun r => f r * laguerreDensity N a r) (laguerreDomain N)) :
    Integrable f (laguerreLaw N a) := by
  apply Integrable.smul_measure (c := (ENNReal.ofReal (laguerreNormalizer N a))⁻¹) ?_
    (by simp [laguerreNormalizer_pos N ha])
  apply (integrable_withDensity_iff_integrable_smul' (measurable_laguerreDensity N a).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).2
  apply hf.congr
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (laguerreDensity_pos a hr).le, mul_comm]

theorem integrable_laguerreLaw_inverse_coordinate {N : ℕ} {a p : ℝ}
    (ha : 0 < a) (i : Fin N) (hp : p < a + i.val) :
    Integrable (fun r => (r i) ^ (-p)) (laguerreLaw N a) :=
  integrable_laguerreLaw ha (integrableOn_laguerre_inverse_coordinate ha i hp)

theorem integrable_laguerreLaw_inverseQuarterSum {N : ℕ} {a : ℝ} (ha : 1 / 4 < a) :
    Integrable (fun r : Fin N → ℝ => (∑ i, (r i)⁻¹) ^ (1 / 4 : ℝ)) (laguerreLaw N a) :=
  integrable_laguerreLaw (by linarith) (integrableOn_laguerre_inverseQuarterSum ha)

end
end CriticalStrip

end OAI
