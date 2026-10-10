import Mathlib
import OAI.Combinatorics.StripMass.QuarterMoments

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory
theorem positiveLaw_inverseQuarterSum_growth_upper (n : ℕ) :
    (∫ y, inverseQuarterStatistic (n+1) y ∂positiveLaw (n+1)) ≤
      (2*(64:ℝ)^(1/4:ℝ)*referenceUpperConstant) * ((n:ℝ)+1)^(3/4:ℝ) := by
  let b : ℝ := 64*((n:ℝ)+1)
  have hb : 4 ≤ b := by dsimp [b]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hb0 : 0 < b := by linarith
  have hp : (1/2:ℝ) ≤ (laguerreLaw (n+1) (1/2)).real (cutoffEvent (n+1) (b/2)) := by
    have he : b/2 = 32*((n:ℝ)+1) := by dsimp [b]; ring
    rw [he]
    exact laguerreLaw_cutoff_half_uniform n
  have H := positiveLaw_inverseQuarter_le_reference (n+1) hb
  have hRef := laguerre_inverseQuarterSum_upper n
  change (∫ r, inverseQuarterStatistic (n+1) r ∂laguerreLaw (n+1) (1/2)) ≤
    referenceUpperConstant*((n:ℝ)+1)^(1/2:ℝ) at hRef
  have hbpow : 0 ≤ b^(1/4:ℝ) := (Real.rpow_pos_of_pos hb0 _).le
  calc
    _ ≤ _ := H
    _ ≤ b^(1/4:ℝ)*(referenceUpperConstant*((n:ℝ)+1)^(1/2:ℝ)) /
        (laguerreLaw (n+1) (1/2)).real (cutoffEvent (n+1) (b/2)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hRef hbpow) (by linarith)
    _ ≤ b^(1/4:ℝ)*(referenceUpperConstant*((n:ℝ)+1)^(1/2:ℝ)) / (1/2) :=
      div_le_div_of_nonneg_left (by positivity [referenceUpperConstant_pos]) (by norm_num) hp
    _ = _ := by
      dsimp only [b]
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤64) (by positivity)]
      have hn : 0 < (n:ℝ)+1 := by positivity
      have he : ((n:ℝ)+1)^(1/4:ℝ)*((n:ℝ)+1)^(1/2:ℝ) = ((n:ℝ)+1)^(3/4:ℝ) := by
        rw [← Real.rpow_add hn]
        norm_num
      calc
        _ = (2*(64:ℝ)^(1/4:ℝ)*referenceUpperConstant) *
            (((n:ℝ)+1)^(1/4:ℝ)*((n:ℝ)+1)^(1/2:ℝ)) := by ring
        _ = _ := by rw [he]

 

theorem positiveLaw_least_inverseQuarter_growth_lower (n : ℕ) :
    ((2:ℝ)^(-(1/4:ℝ))*(1/2:ℝ)^(1/4:ℝ)*(Real.exp (-1)/48)) * ((n:ℝ)+1)^(3/4:ℝ) ≤
      ∫ y, (y 0)^(-(1/4:ℝ)) ∂positiveLaw (n+1) := by
  let b : ℝ := ((n:ℝ)+2)/2
  have hb : 1 ≤ b := by dsimp [b]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hb' : b ≤ ((n+1:ℕ)+1:ℝ)/2 := by dsimp [b]; push_cast; linarith
  have hb0 : 0 < b := by linarith
  have H := positiveLaw_inverseQuarter_ge_reference (0 : Fin (n+1)) hb hb'
  have hRef := laguerre_least_inverseQuarter_lower n
  rw [← integral_laguerreLaw _ (by norm_num : (0:ℝ)<1)] at hRef
  have hscale : ((1/2:ℝ)*((n:ℝ)+1))^(1/4:ℝ) ≤ b^(1/4:ℝ) := by
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    dsimp [b]
    linarith
  have hlow : 0 ≤ (Real.exp (-1)/48)*((n:ℝ)+1)^(1/2:ℝ) := by positivity
  calc
    _ = (2:ℝ)^(-(1/4:ℝ)) * (((1/2:ℝ)*((n:ℝ)+1))^(1/4:ℝ)) *
        ((Real.exp (-1)/48) * ((n:ℝ)+1)^(1/2:ℝ)) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤1/2) (by positivity)]
      have hn : 0 < (n:ℝ)+1 := by positivity
      have he : ((n:ℝ)+1)^(1/4:ℝ)*((n:ℝ)+1)^(1/2:ℝ) = ((n:ℝ)+1)^(3/4:ℝ) := by
        rw [← Real.rpow_add hn]
        norm_num
      calc
        _ = ((2:ℝ)^(-(1/4:ℝ))*(1/2:ℝ)^(1/4:ℝ)*(Real.exp (-1)/48)) *
          (((n:ℝ)+1)^(1/4:ℝ)*((n:ℝ)+1)^(1/2:ℝ)) := by rw [he]
        _ = _ := by ring
    _ ≤ (2:ℝ)^(-(1/4:ℝ))*b^(1/4:ℝ)*
        ((Real.exp (-1)/48)*((n:ℝ)+1)^(1/2:ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale (by positivity)) hlow
    _ ≤ (2:ℝ)^(-(1/4:ℝ))*b^(1/4:ℝ)*
        (∫ r, (r 0)^(-(1/4:ℝ)) ∂laguerreLaw (n+1) 1) :=
      mul_le_mul_of_nonneg_left hRef (by positivity)
    _ ≤ _ := H

 

theorem positive_arch_integral_growth :
    Comparable (fun N => ∫ x in Ioo 0 1, momentIntegrand N x)
      (fun N => (N:ℝ)^(3/4:ℝ)) := by
  refine ⟨(1/96) * ((2:ℝ)^(-(1/4:ℝ))*(1/2:ℝ)^(1/4:ℝ)*(Real.exp (-1)/48)),
    (32/3) * (2*(64:ℝ)^(1/4:ℝ)*referenceUpperConstant), by positivity,
    by have := referenceUpperConstant_pos; positivity, ?_⟩
  intro N hN
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hI := integral_inverse_comparison hN
  have hL := positiveLaw_least_inverseQuarter_growth_lower n
  have hU := positiveLaw_inverseQuarterSum_growth_upper n
  rw [integral_positiveLaw] at hL hU
  constructor
  · have H := (mul_le_mul_of_nonneg_left hL (by norm_num : (0:ℝ)≤1/96)).trans hI.1
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, mul_assoc] using H
  · have H := hI.2.trans (mul_le_mul_of_nonneg_left hU (by norm_num : (0:ℝ)≤32/3))
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, mul_assoc] using H


 


lemma pairKernel_symm (x y : ℝ) : pairKernel x y = pairKernel y x := by
  unfold pairKernel
  rw [add_comm x y]
  congr 1
  ring

lemma prod_upper_square {n : ℕ} (g : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, g i j = g j i) :
    (∏ i, ∏ j ∈ Finset.Ioi i, g i j)^2 =
      ∏ i, ∏ j, if i = j then 1 else g i j := by
  classical
  have he : (∏ i, ∏ j ∈ Finset.Ioi i, g i j) =
      ∏ i, ∏ j, if i < j then g i j else 1 := by
    congr 1
    ext i
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  rw [he, pow_two]
  conv_lhs => rhs; rw [Finset.prod_comm]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, not_lt.mpr h.le, h.ne]
  · simp
  · simp [h, not_lt.mpr h.le, h.ne', hsym]

lemma prod_upper_perm {n : ℕ} (g : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, g i j = g j i) (hpos : ∀ i j, 0 ≤ g i j)
    (σ : Equiv.Perm (Fin n)) :
    (∏ i, ∏ j ∈ Finset.Ioi i, g (σ i) (σ j)) =
      ∏ i, ∏ j ∈ Finset.Ioi i, g i j := by
  classical
  have ha : 0 ≤ ∏ i, ∏ j ∈ Finset.Ioi i, g (σ i) (σ j) :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => hpos _ _
  have hb : 0 ≤ ∏ i, ∏ j ∈ Finset.Ioi i, g i j :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => hpos _ _
  have he : (∏ i, ∏ j ∈ Finset.Ioi i, g (σ i) (σ j))^2 =
      (∏ i, ∏ j ∈ Finset.Ioi i, g i j)^2 := by
    rw [prod_upper_square _ (fun i j => hsym _ _), prod_upper_square g hsym]
    apply Fintype.prod_equiv σ
    intro i
    apply Fintype.prod_equiv σ
    intro j
    simp
  nlinarith

lemma density_perm_of_nonneg {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i)
    (σ : Equiv.Perm (Fin n)) : density n (x ∘ σ) = density n x := by
  unfold density
  congr 1
  · exact Fintype.prod_equiv σ _ _ (fun _ => rfl)
  · exact prod_upper_perm _ (fun i j => pairKernel_symm _ _)
      (fun i j => pairKernel_nonneg (hx i) (hx j)) σ

lemma density_zero_of_not_injective {n : ℕ} {x : Fin n → ℝ}
    (hx : ¬ Function.Injective x) : density n x = 0 := by
  classical
  obtain ⟨i, j, he, hne⟩ : ∃ i j, x i = x j ∧ i ≠ j := by
    simpa only [Function.Injective, not_forall, exists_prop] using hx
  suffices (∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (x i) (x j)) = 0 by
    simp [density, this]
  rcases hne.lt_or_gt with h | h
  · apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply Finset.prod_eq_zero (Finset.mem_Ioi.mpr h)
    simp [pairKernel, he]
  · apply Finset.prod_eq_zero (Finset.mem_univ j)
    apply Finset.prod_eq_zero (Finset.mem_Ioi.mpr h)
    simp [pairKernel, he]

abbrev unitCubeMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => volume.restrict (Ioo (0:ℝ) 1))

lemma ae_unitCube (n : ℕ) :
    ∀ᵐ x ∂unitCubeMeasure n, ∀ i, x i ∈ Ioo (0:ℝ) 1 := by
  rw [unitCubeMeasure, ← Measure.restrict_pi_pi, ← volume_pi]
  exact (ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)).mono
    fun _ hx i => hx i (mem_univ i)

lemma unitCube_restrict_ordered (n : ℕ) :
    (unitCubeMeasure n).restrict (orderedDomain n) = volume.restrict (orderedDomain n) := by
  rw [unitCubeMeasure, ← Measure.restrict_pi_pi, ← volume_pi,
    Measure.restrict_restrict (isOpen_orderedDomain n).measurableSet]
  congr 1
  exact inter_eq_left.mpr (fun _ hx i _ => hx.2 i)

lemma integral_symmetric_unitCube {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (hperm : ∀ σ : Equiv.Perm (Fin n), ∀ x, (∀ i, x i ∈ Ioo (0:ℝ) 1) → F (x ∘ σ) = F x)
    (hzero : ∀ x, ¬Function.Injective x → F x = 0)
    (hint : IntegrableOn F (orderedDomain n)) :
    (∫ x, F x ∂unitCubeMeasure n) =
      (n.factorial : ℝ) * ∫ x in orderedDomain n, F x := by
  classical
  let G := (orderedDomain n).indicator F
  have hi : Integrable G (unitCubeMeasure n) := by
    rw [integrable_indicator_iff (isOpen_orderedDomain n).measurableSet]
    simpa only [IntegrableOn, unitCube_restrict_ordered] using hint
  have his (σ : Equiv.Perm (Fin n)) :
      Integrable (fun x => G (x ∘ σ)) (unitCubeMeasure n) := by
    simpa only [Function.comp_def, StripPfaffian.piCongrLeft_const_apply, Equiv.symm_symm] using
      (measurePreserving_piCongrLeft (fun _ : Fin n => volume.restrict (Ioo (0:ℝ) 1)) σ.symm).integrable_comp_of_integrable hi
  have heq (σ : Equiv.Perm (Fin n)) :
      (∫ x, G (x ∘ σ) ∂unitCubeMeasure n) = ∫ x in orderedDomain n, F x := by
    have he := (measurePreserving_piCongrLeft
      (fun _ : Fin n => volume.restrict (Ioo (0:ℝ) 1)) σ.symm).integral_comp' G
    simp only [StripPfaffian.piCongrLeft_const_apply, Equiv.symm_symm] at he
    rw [he, integral_indicator (isOpen_orderedDomain n).measurableSet, unitCube_restrict_ordered]
  have hs (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Ioo (0:ℝ) 1) :
      ∑ σ : Equiv.Perm (Fin n), G (x ∘ σ) = F x := by
    by_cases hinj : Function.Injective x
    · have hsort : x ∘ Tuple.sort x ∈ orderedDomain n :=
        ⟨(Tuple.monotone_sort x).strictMono_of_injective (hinj.comp (Tuple.sort x).injective),
          fun i => hx _⟩
      rw [Finset.sum_eq_single (Tuple.sort x)]
      · exact (indicator_of_mem hsort F).trans (hperm _ _ hx)
      · intro σ _ hne
        apply indicator_of_notMem
        intro hσ
        apply hne
        apply Equiv.ext
        intro i
        exact hinj (congrFun (Tuple.unique_monotone hσ.1.monotone (Tuple.monotone_sort x)) i)
      · simp
    · rw [hzero x hinj]
      apply Finset.sum_eq_zero
      intro σ _
      by_cases hm : x ∘ σ ∈ orderedDomain n
      · exact (indicator_of_mem hm F).trans ((hperm _ _ hx).trans (hzero x hinj))
      · exact indicator_of_notMem hm _
  calc
    _ = ∫ x, ∑ σ : Equiv.Perm (Fin n), G (x ∘ σ) ∂unitCubeMeasure n :=
      integral_congr_ae ((ae_unitCube n).mono fun x hx => (hs x hx).symm)
    _ = ∑ σ : Equiv.Perm (Fin n), ∫ x, G (x ∘ σ) ∂unitCubeMeasure n :=
      integral_finsetSum _ (fun σ _ => his σ)
    _ = _ := by simp only [heq, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

lemma integral_density_unitCube (n : ℕ) :
    (∫ x, density n x ∂unitCubeMeasure n) = (n.factorial:ℝ) * normalizer n := by
  exact integral_symmetric_unitCube _
    (fun σ x hx => density_perm_of_nonneg (fun i => (hx i).1.le) σ)
    (fun _ hx => density_zero_of_not_injective hx) (integrableOn_density n)

lemma density_cons (n : ℕ) (x : ℝ) (y : Fin n → ℝ) :
    density (n+1) (Fin.cons x y) =
      omega x * density n y * ∏ i, pairKernel x (y i) := by
  rw [density, Fin.prod_univ_succ, pairProduct_cons]
  simp only [Fin.cons_zero, Fin.cons_succ, density]
  ring

lemma density_nonneg_of_nonneg {n : ℕ} {y : Fin n → ℝ} (hy : ∀ i, 0 ≤ y i) :
    0 ≤ density n y := by
  unfold density
  apply mul_nonneg (Finset.prod_nonneg fun _ _ => omega_nonneg _)
  exact Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => pairKernel_nonneg (hy i) (hy j)

lemma density_cube_le_product {n : ℕ} {y : Fin n → ℝ} (hy : ∀ i, y i ∈ Ioo (0:ℝ) 1) :
    density n y ≤ ∏ i, omega (y i) := by
  have h0 : 0 ≤ ∏ i : Fin n, omega (y i) := Finset.prod_nonneg fun _ _ => omega_nonneg _
  unfold density
  apply (mul_le_mul_of_nonneg_left _ h0).trans_eq (mul_one _)
  exact Finset.prod_le_one₀
    (fun i _ => Finset.prod_nonneg fun j _ => pairKernel_nonneg (hy i).1.le (hy j).1.le)
    (fun i _ => Finset.prod_le_one₀
      (fun j _ => pairKernel_nonneg (hy i).1.le (hy j).1.le)
      (fun j _ => pairKernel_le_one (hy i) (hy j)))

lemma integrable_density_unitCube (n : ℕ) : Integrable (density n) (unitCubeMeasure n) := by
  apply (Integrable.fintype_prod (fun _ : Fin n => integrableOn_omega)).mono'
    (measurable_density n).aestronglyMeasurable
  filter_upwards [ae_unitCube n] with y hy
  simpa only [Real.norm_eq_abs, abs_of_nonneg (density_nonneg_of_nonneg (fun i => (hy i).1.le))]
    using density_cube_le_product hy

lemma integrable_cube_mul_density {n : ℕ} {g : (Fin n → ℝ) → ℝ} (hg : Measurable g)
    {b : ℝ} (hbd : ∀ y, (∀ i, y i ∈ Ioo (0:ℝ) 1) → |g y| ≤ b) :
    Integrable (fun y => g y * density n y) (unitCubeMeasure n) := by
  apply ((integrable_density_unitCube n).const_mul b).mono'
    (hg.mul (measurable_density n)).aestronglyMeasurable
  filter_upwards [ae_unitCube n] with y hy
  change ‖g y * density n y‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (density_nonneg_of_nonneg (fun i => (hy i).1.le))]
  exact mul_le_mul_of_nonneg_right (hbd y hy) (density_nonneg_of_nonneg (fun i => (hy i).1.le))

lemma reflectionProduct_perm {n : ℕ} (x : ℝ) (y : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    reflectionProduct n x (y ∘ σ) = reflectionProduct n x y := by
  exact Fintype.prod_equiv σ _ _ (fun _ => rfl)

lemma expectation_reflection_unitCube (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    expectation n (reflectionProduct n x) =
      (∫ y, reflectionProduct n x y * density n y ∂unitCubeMeasure n) /
        (∫ y, density n y ∂unitCubeMeasure n) := by
  rw [integral_symmetric_unitCube _
    (fun σ y hy => by rw [reflectionProduct_perm, density_perm_of_nonneg (fun i => (hy i).1.le)])
    (fun y hy => by rw [density_zero_of_not_injective hy, mul_zero])
    (integrableOn_reflectionProduct_density n hx), integral_density_unitCube]
  rw [mul_div_mul_left _ _ (by exact_mod_cast (Nat.factorial_ne_zero n))]
  rfl

 def reflectionResidue (n : ℕ) (y : Fin n → ℝ) (i : Fin n) : ℝ :=
  2 * ∏ j ∈ Finset.univ.erase i, (y j + y i) / (y j - y i)

lemma reflectionResidue_perm {n : ℕ} (y : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    reflectionResidue n (y ∘ σ) i = reflectionResidue n y (σ i) := by
  classical
  unfold reflectionResidue
  congr 1
  apply Finset.prod_equiv σ
  · intro j
    simp
  · intro j hj
    rfl

lemma reflectionResidue_zero_cons {n : ℕ} (x : ℝ) (y : Fin n → ℝ) :
    reflectionResidue (n+1) (Fin.cons x y) 0 = 2 * ∏ j, (y j+x)/(y j-x) := by
  classical
  unfold reflectionResidue
  congr 1
  have he : (Finset.univ.erase (0 : Fin (n+1))) = Finset.univ.filter (fun i => i ≠ 0) := by ext; simp
  rw [he, Finset.prod_filter, Fin.prod_univ_succ]
  simp

lemma reflectionResidue_density_cons {n : ℕ} {x : ℝ} {y : Fin n → ℝ}
    (hx : 0 < x) (hy : ∀ i, 0 < y i) :
    reflectionResidue (n+1) (Fin.cons x y) 0 * density (n+1) (Fin.cons x y) =
      2 * omega x * density n y * ∏ i, (y i-x) := by
  rw [reflectionResidue_zero_cons, density_cons]
  have hprod : (∏ i, (y i+x)/(y i-x)) * (∏ i, pairKernel x (y i)) = ∏ i, (y i-x) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    unfold pairKernel
    by_cases hi : y i = x
    · simp [hi]
    · field_simp [(add_pos (hy i) hx).ne', sub_ne_zero.mpr hi]
  calc
    _ = 2 * omega x * density n y *
        ((∏ i, (y i+x)/(y i-x)) * (∏ i, pairKernel x (y i))) := by ring
    _ = _ := by rw [hprod]

end
end CriticalStrip

end OAI
