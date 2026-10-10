import Mathlib
import OAI.Probability.SphericalField.Positivity.Patterns

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
def replicaMean {n : ℕ} (v : Fin n → H) : H := (n : ℝ)⁻¹ • ∑ i, v i

lemma inner_replicaMean {n : ℕ} (v w : Fin n → H) :
    ⟪replicaMean v, replicaMean w⟫_ℝ =
      (n : ℝ)⁻¹ ^ 2 * ∑ i, ∑ j, ⟪v i, w j⟫_ℝ := by
  simp only [replicaMean, real_inner_smul_left, real_inner_smul_right]
  rw [sum_inner]
  simp_rw [inner_sum]
  ring

lemma replicaMean_norm_sq_le {n : ℕ} (hn : 0 < n) (v : Fin n → H) {c : ℝ}
    (hdiag : ∀ i, ‖v i‖ ^ 2 ≤ 1)
    (hoff : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ ≤ c) :
    ‖replicaMean v‖ ^ 2 ≤ c + (1 - c) / n := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hrow (i : Fin n) : (∑ j, ⟪v i, v j⟫_ℝ) ≤ 1 + ((n : ℝ) - 1) * c := by
    have hs : (∑ j ∈ Finset.univ.erase i, ⟪v i, v j⟫_ℝ) ≤
        ∑ _j ∈ Finset.univ.erase i, c :=
      Finset.sum_le_sum fun j hj => hoff i j (Ne.symm (Finset.ne_of_mem_erase hj))
    have hc : ((Finset.univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
      simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
      rw [Nat.cast_sub hn]
      norm_num
    simp only [Finset.sum_const, nsmul_eq_mul, hc] at hs
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    rw [real_inner_self_eq_norm_sq]
    linarith [hdiag i]
  rw [← real_inner_self_eq_norm_sq, inner_replicaMean]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hrow i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  calc
    (n : ℝ)⁻¹ ^ 2 * (∑ i, ∑ j, ⟪v i, v j⟫_ℝ) ≤
      (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * (1 + ((n : ℝ) - 1) * c)) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = c + (1 - c) / n := by field_simp; ring

lemma inner_replicaMean_eq {n : ℕ} (hn : 0 < n) (v w : Fin n → H) {a : ℝ}
    (h : ∀ i j, ⟪v i, w j⟫_ℝ = a) :
    ⟪replicaMean v, replicaMean w⟫_ℝ = a := by
  rw [inner_replicaMean]
  simp_rw [h]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  field_simp

lemma duplicate_blocks_bound {n : ℕ} (hn : 0 < n) (v : Fin 3 → Fin n → H)
    {a b c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hdiag : ∀ k i, ‖v k i‖ ^ 2 ≤ 1)
    (hoff : ∀ k i j, i ≠ j → ⟪v k i, v k j⟫_ℝ ≤ c)
    (h12 : ∀ i j, ⟪v 0 i, v 1 j⟫_ℝ = a)
    (h13 : ∀ i j, ⟪v 0 i, v 2 j⟫_ℝ = b)
    (h23 : ∀ i j, ⟪v 1 i, v 2 j⟫_ℝ = c) :
    (a - b) ^ 2 ≤ 2 / (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let x := replicaMean (v 0)
  let y := replicaMean (v 1)
  let z := replicaMean (v 2)
  have hx := replicaMean_norm_sq_le hn (v 0) (hdiag 0) (hoff 0)
  have hy := replicaMean_norm_sq_le hn (v 1) (hdiag 1) (hoff 1)
  have hz := replicaMean_norm_sq_le hn (v 2) (hdiag 2) (hoff 2)
  have hxy : ⟪x, y⟫_ℝ = a := inner_replicaMean_eq hn _ _ h12
  have hxz : ⟪x, z⟫_ℝ = b := inner_replicaMean_eq hn _ _ h13
  have hyz : ⟪y, z⟫_ℝ = c := inner_replicaMean_eq hn _ _ h23
  change ‖x‖ ^ 2 ≤ _ at hx
  change ‖y‖ ^ 2 ≤ _ at hy
  change ‖z‖ ^ 2 ≤ _ at hz
  have hsmall : (1 - c) / n ≤ 1 - c :=
    (div_le_iff₀ hnpos).mpr (by nlinarith)
  have hx1 : ‖x‖ ^ 2 ≤ 1 := by linarith
  have hdiff : ‖y - z‖ ^ 2 ≤ 2 * ((1 - c) / n) := by
    rw [norm_sub_sq_real, hyz]
    linarith
  have hcs : (a - b) ^ 2 ≤ ‖x‖ ^ 2 * ‖y - z‖ ^ 2 := by
    have h := abs_real_inner_le_norm x (y - z)
    rw [inner_sub_right, hxy, hxz] at h
    have hs := sq_le_sq₀ (abs_nonneg (a - b))
      (mul_nonneg (norm_nonneg x) (norm_nonneg (y - z))) |>.mpr h
    simpa only [sq_abs, mul_pow] using hs
  calc
    (a - b) ^ 2 ≤ ‖x‖ ^ 2 * ‖y - z‖ ^ 2 := hcs
    _ ≤ 1 * ‖y - z‖ ^ 2 := mul_le_mul_of_nonneg_right hx1 (sq_nonneg _)
    _ ≤ 2 * ((1 - c) / n) := by simpa using hdiff
    _ ≤ 2 / n := by apply (le_div_iff₀ hnpos).mpr; nlinarith [div_mul_cancel₀ (1 - c) (ne_of_gt hnpos)]

lemma arbitrary_duplicate_blocks_equal {a b c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hdup : ∀ n : ℕ, 0 < n → ∃ v : Fin 3 → Fin n → H,
      (∀ k i, ‖v k i‖ ^ 2 ≤ 1) ∧
      (∀ k i j, i ≠ j → ⟪v k i, v k j⟫_ℝ ≤ c) ∧
      (∀ i j, ⟪v 0 i, v 1 j⟫_ℝ = a) ∧
      (∀ i j, ⟪v 0 i, v 2 j⟫_ℝ = b) ∧
      (∀ i j, ⟪v 1 i, v 2 j⟫_ℝ = c)) : a = b := by
  have hbound (n : ℕ) : (a - b) ^ 2 ≤ 2 / ((n : ℝ) + 1) := by
    obtain ⟨v, hd, ho, h12, h13, h23⟩ := hdup (n + 1) (by omega)
    simpa only [Nat.cast_add, Nat.cast_one] using
      duplicate_blocks_bound (by omega : 0 < n + 1) v hc0 hc1 hd ho h12 h13 h23
  have ht : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, mul_one_div] using
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ) |>.const_mul 2
  have hs : (a - b) ^ 2 ≤ 0 := ge_of_tendsto ht (Eventually.of_forall hbound)
  nlinarith [sq_nonneg (a - b)]

lemma replicaMean_norm_le_one {n : ℕ} (hn : 0 < n) (v : Fin n → H)
    (hdiag : ∀ i, ‖v i‖ ^ 2 ≤ 1) : ‖replicaMean v‖ ≤ 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hsum : ‖∑ i, v i‖ ≤ (n : ℝ) := by
    calc
      ‖∑ i, v i‖ ≤ ∑ i, ‖v i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        nlinarith [hdiag i, norm_nonneg (v i)]
      _ = n := by simp
  calc
    ‖replicaMean v‖ = (n : ℝ)⁻¹ * ‖∑ i, v i‖ := by
      simp [replicaMean, norm_smul]
    _ ≤ (n : ℝ)⁻¹ * n := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := inv_mul_cancel₀ hn0

lemma inner_replicaMean_le {n : ℕ} (hn : 0 < n) (v w : Fin n → H) {a : ℝ}
    (h : ∀ i j, ⟪v i, w j⟫_ℝ ≤ a) : ⟪replicaMean v, replicaMean w⟫_ℝ ≤ a := by
  rw [inner_replicaMean]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h i j))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  calc
    (n : ℝ)⁻¹ ^ 2 * (∑ i, ∑ j, ⟪v i, w j⟫_ℝ) ≤
      (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * ((n : ℝ) * a)) := mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = a := by field_simp

lemma le_inner_replicaMean {n : ℕ} (hn : 0 < n) (v w : Fin n → H) {a : ℝ}
    (h : ∀ i j, a ≤ ⟪v i, w j⟫_ℝ) : a ≤ ⟪replicaMean v, replicaMean w⟫_ℝ := by
  rw [inner_replicaMean]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h i j))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  calc
    a = (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * ((n : ℝ) * a)) := by field_simp
    _ ≤ (n : ℝ)⁻¹ ^ 2 * (∑ i, ∑ j, ⟪v i, w j⟫_ℝ) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)

lemma duplicate_ordered_blocks_bound {n : ℕ} (hn : 0 < n) (v : Fin 3 → Fin n → H)
    {a b c t : ℝ} (hab : a ≤ b)
    (hdiag : ∀ k i, ‖v k i‖ ^ 2 ≤ 1)
    (hoff : ∀ k i j, i ≠ j → ⟪v k i, v k j⟫_ℝ ≤ t)
    (h12 : ∀ i j, ⟪v 0 i, v 1 j⟫_ℝ ≤ a)
    (h13 : ∀ i j, b ≤ ⟪v 0 i, v 2 j⟫_ℝ)
    (h23 : ∀ i j, c ≤ ⟪v 1 i, v 2 j⟫_ℝ) :
    (b - a) ^ 2 ≤ 2 * (t - c) + 2 * ((1 - t) / n) := by
  let x := replicaMean (v 0)
  let y := replicaMean (v 1)
  let z := replicaMean (v 2)
  have hx := replicaMean_norm_le_one hn (v 0) (hdiag 0)
  have hy := replicaMean_norm_sq_le hn (v 1) (hdiag 1) (hoff 1)
  have hz := replicaMean_norm_sq_le hn (v 2) (hdiag 2) (hoff 2)
  have hxy : ⟪x, y⟫_ℝ ≤ a := inner_replicaMean_le hn _ _ h12
  have hxz : b ≤ ⟪x, z⟫_ℝ := le_inner_replicaMean hn _ _ h13
  have hyz : c ≤ ⟪y, z⟫_ℝ := le_inner_replicaMean hn _ _ h23
  change ‖x‖ ≤ _ at hx
  change ‖y‖ ^ 2 ≤ _ at hy
  change ‖z‖ ^ 2 ≤ _ at hz
  have hx1 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  have hdiff : ‖z - y‖ ^ 2 ≤ 2 * (t - c) + 2 * ((1 - t) / n) := by
    rw [norm_sub_sq_real, real_inner_comm]
    linarith
  have hinner : b - a ≤ ⟪x, z - y⟫_ℝ := by rw [inner_sub_right]; linarith
  have hnonneg : 0 ≤ ⟪x, z - y⟫_ℝ := by linarith
  have habsq : (b - a) ^ 2 ≤ ⟪x, z - y⟫_ℝ ^ 2 :=
    (sq_le_sq₀ (sub_nonneg.mpr hab) hnonneg).mpr hinner
  have hcs : ⟪x, z - y⟫_ℝ ^ 2 ≤ ‖x‖ ^ 2 * ‖z - y‖ ^ 2 := by
    have h := abs_real_inner_le_norm x (z - y)
    have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg x) (norm_nonneg _))).mpr h
    simpa only [sq_abs, mul_pow] using hs
  exact habsq.trans (hcs.trans ((mul_le_mul_of_nonneg_right hx1 (sq_nonneg _)).trans
    (by simpa using hdiff)))

lemma posSemidef_standard_basis_inner {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.PosSemidef) (i j : Fin n) :
    letI := B.toSeminormedAddCommGroup hB
    letI := B.toInnerProductSpace hB
    ⟪(Pi.single i 1 : Fin n → ℝ), Pi.single j 1⟫_ℝ = B i j := by
  change (B *ᵥ Pi.single j 1) ⬝ᵥ star (Pi.single i 1) = B i j
  simp

def triangleConstraints (a b c t : ℝ) (k l : Fin 3) : Set ℝ :=
  if k = l then Iio t
  else if (k = 0 ∧ l = 1) ∨ (k = 1 ∧ l = 0) then Iio a
  else if (k = 0 ∧ l = 2) ∨ (k = 2 ∧ l = 0) then Ioo b t
  else Ioo c t

lemma triangleConstraints_measurable (a b c t : ℝ) (k l : Fin 3) :
    MeasurableSet (triangleConstraints a b c t k l) := by
  unfold triangleConstraints
  split_ifs <;> measurability

lemma triangleConstraints_diag (a b c t : ℝ) (k : Fin 3) :
    triangleConstraints a b c t k k = Iio t := by simp [triangleConstraints]

lemma triangleConstraints_cut {a : ℝ} (b c t : ℝ) (hat : a ≤ t) (k l : Fin 3) :
    triangleConstraints a b c t k l ⊆ Iio t := by
  unfold triangleConstraints
  split_ifs
  · exact Subset.rfl
  · exact Iio_subset_Iio hat
  · exact Ioo_subset_Iio_self
  · exact Ioo_subset_Iio_self

def tripleIndex {n : ℕ} (k : Fin 3) (i : Fin n) : Fin (3 * n) :=
  ⟨3 * i.val + k.val, by have := i.isLt; have := k.isLt; omega⟩

@[simp] lemma tripleLabels_tripleIndex {n : ℕ} (k : Fin 3) (i : Fin n) :
    tripleLabels (3 * n) (tripleIndex k i) = k := by
  apply Fin.ext
  simp [tripleLabels, tripleIndex, Nat.add_mod]

lemma tripleIndex_ne {n : ℕ} {k l : Fin 3} (hkl : k ≠ l) (i j : Fin n) :
    tripleIndex k i ≠ tripleIndex l j := by
  intro h
  have := congrArg (tripleLabels (3 * n)) h
  exact hkl (by simpa using this)

lemma tripleIndex_inj {n : ℕ} (k : Fin 3) {i j : Fin n} (hij : i ≠ j) :
    tripleIndex k i ≠ tripleIndex k j := by
  intro h
  apply hij
  apply Fin.ext
  have h' := congrArg Fin.val h
  dsimp [tripleIndex] at h'
  omega

lemma triangle_pattern_psd_bound {n : ℕ} (hn : 0 < n)
    (B : OverlapBlock (3 * n)) (hB : Matrix.PosSemidef B)
    (hdiag : ∀ i, B i i ≤ 1) {a b c t : ℝ} (hab : a ≤ b)
    (hpattern : B ∈ patternMatrices (tripleLabels (3 * n)) (triangleConstraints a b c t)) :
    (b - a) ^ 2 ≤ 2 * (t - c) + 2 * ((1 - t) / n) := by
  let _ := Matrix.toSeminormedAddCommGroup B hB
  let _ := Matrix.toInnerProductSpace B hB
  let v : Fin 3 → Fin n → (Fin (3 * n) → ℝ) := fun k i => Pi.single (tripleIndex k i) 1
  have hv (k l : Fin 3) (i j : Fin n) :
      ⟪v k i, v l j⟫_ℝ = B (tripleIndex k i) (tripleIndex l j) :=
    posSemidef_standard_basis_inner B hB _ _
  apply duplicate_ordered_blocks_bound hn v hab
  · intro k i
    rw [← real_inner_self_eq_norm_sq, hv]
    exact hdiag _
  · intro k i j hij
    rw [hv]
    have h := hpattern _ _ (tripleIndex_inj k hij)
    simp only [tripleLabels_tripleIndex, triangleConstraints_diag, mem_Iio] at h
    exact h.le
  · intro i j
    rw [hv]
    have h := hpattern _ _ (tripleIndex_ne (by decide : (0 : Fin 3) ≠ 1) i j)
    simp [triangleConstraints] at h
    exact h.le
  · intro i j
    rw [hv]
    have h := hpattern _ _ (tripleIndex_ne (by decide : (0 : Fin 3) ≠ 2) i j)
    simp [triangleConstraints] at h
    exact h.1.le
  · intro i j
    rw [hv]
    have h := hpattern _ _ (tripleIndex_ne (by decide : (1 : Fin 3) ≠ 2) i j)
    simp [triangleConstraints] at h
    exact h.1.le

theorem gg_triangle_pattern_bound (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n Q))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, Q i i ≤ 1)
    {a b c t : ℝ} (hab : a ≤ b) (hat : a ≤ t)
    (hA : 0 < μ.real (overlapBlock id 3 ⁻¹'
      patternMatrices (tripleLabels 3) (triangleConstraints a b c t))) :
    (b - a) ^ 2 ≤ 2 * (t - c) := by
  have hall := gg_triple_pattern μ hEx hGG hSym (triangleConstraints a b c t)
    (triangleConstraints_measurable a b c t) t (triangleConstraints_diag a b c t)
    (triangleConstraints_cut b c t hat) hA
  have hbound (n : ℕ) : (b - a) ^ 2 ≤ 2 * (t - c) + 2 * ((1 - t) / (n + 1 : ℝ)) := by
    have hpos := hall (3 * (n + 1)) (by omega)
    have hne : μ (overlapBlock id (3 * (n + 1)) ⁻¹'
        patternMatrices (tripleLabels (3 * (n + 1))) (triangleConstraints a b c t)) ≠ 0 := by
      intro hz
      simp [Measure.real, hz] at hpos
    obtain ⟨Q, hQ, hG, hD⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hne
      (ae_restrict_of_ae (hGram.and hdiag))
    have h := triangle_pattern_psd_bound (by omega : 0 < n + 1)
      (overlapBlock id (3 * (n + 1)) Q) (hG _) (fun i => hD i) hab hQ
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have ht : Tendsto (fun n : ℕ => 2 * (t - c) + 2 * ((1 - t) / (n + 1 : ℝ))) atTop
      (𝓝 (2 * (t - c))) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ) |>.const_mul (2 * (1 - t))
    have h' := h.const_add (2 * (t - c))
    simpa only [mul_zero, add_zero, mul_one_div, mul_div_assoc] using h'
  exact ge_of_tendsto ht (Eventually.of_forall hbound)

end SphericalPerceptron
end
end

end OAI
