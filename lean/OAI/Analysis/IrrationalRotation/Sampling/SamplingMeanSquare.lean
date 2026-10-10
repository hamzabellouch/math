import OAI.Analysis.IrrationalRotation.Sampling.SamplingAsymptotics

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open InvariantRotation.SamplingMomentBounds

namespace Invariant233.SamplingAsymptotics

theorem integral_coordinate_product_sub_one_sq
    {κ : Type*} [Fintype κ] {Ω : κ → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : κ) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)]
    (z : (i : κ) → Ω i → ℝ) (hz : ∀ i, MemLp (z i) 2 (μ i)) :
    (∫ x, ((∏ i, z i (x i)) - 1) ^ 2 ∂Measure.pi μ) =
      (∏ i, ∫ x, (z i x) ^ 2 ∂μ i) -
        2 * (∏ i, ∫ x, z i x ∂μ i) + 1 := by
  let Z : ((i : κ) → Ω i) → ℝ := fun x => ∏ i, z i (x i)
  have hZ : MemLp Z 2 (Measure.pi μ) := memLp_coordinate_prod z hz
  have hZi : Integrable Z (Measure.pi μ) := hZ.integrable (by norm_num)
  have hpoly : (fun x => (Z x - 1) ^ 2) =
      (fun x => (Z x) ^ 2 - 2 * Z x + 1) := by
    funext x
    ring
  change (∫ x, (Z x - 1) ^ 2 ∂Measure.pi μ) = _
  have hdiff : Integrable (fun x => (Z x) ^ 2 - 2 * Z x) (Measure.pi μ) :=
    hZ.integrable_sq.sub (hZi.const_mul 2)
  rw [hpoly, integral_add hdiff (integrable_const 1)]
  have hsub : (∫ x, (Z x) ^ 2 - 2 * Z x ∂Measure.pi μ) =
      (∫ x, (Z x) ^ 2 ∂Measure.pi μ) - 2 * (∫ x, Z x ∂Measure.pi μ) := by
    rw [integral_sub hZ.integrable_sq (hZi.const_mul 2), integral_const_mul]
  rw [hsub]
  simp only [integral_const, smul_eq_mul]
  rw [show (∫ x, (Z x) ^ 2 ∂Measure.pi μ) =
      ∏ i, ∫ x, (z i x) ^ 2 ∂μ i from integral_coordinate_prod_sq z]
  rw [show (∫ x, Z x ∂Measure.pi μ) =
      ∏ i, ∫ x, z i x ∂μ i from integral_fintype_prod_eq_prod z]
  simp

theorem integral_ideal_product_sub_one_sq_le
    (m : ℕ) {Ω : Fin m → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : Fin m) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)]
    (z : (i : Fin m) → Ω i → ℝ) (hz : ∀ i, MemLp (z i) 2 (μ i))
    (hmean : ∀ i, (∫ x, z i x ∂μ i) = kernelMass m)
    (hbase : ∀ i, (∫ x, (z i x) ^ 2 ∂μ i) ≤ momentBase m) :
    (∫ x, ((∏ i, z i (x i)) - 1) ^ 2 ∂Measure.pi μ) ≤ idealError m := by
  rw [integral_coordinate_product_sub_one_sq z hz]
  have hprod : (∏ i, ∫ x, (z i x) ^ 2 ∂μ i) ≤ (momentBase m) ^ m := by
    calc
      (∏ i, ∫ x, (z i x) ^ 2 ∂μ i) ≤ ∏ _i : Fin m, momentBase m :=
        Finset.prod_le_prod₀ (fun i _ => integral_nonneg (fun x => sq_nonneg _))
          (fun i _ => hbase i)
      _ = (momentBase m) ^ m := by simp
  simp only [hmean, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  dsimp [idealError]
  linarith

theorem integral_sub_one_sq_le_split {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (v z : Ω → ℝ)
    (hv : MemLp v 2 μ) (hz : MemLp z 2 μ) :
    (∫ x, (v x - 1) ^ 2 ∂μ) ≤
      2 * (∫ x, (v x - z x) ^ 2 ∂μ) + 2 * (∫ x, (z x - 1) ^ 2 ∂μ) := by
  have h1 : MemLp (fun _ : Ω => (1 : ℝ)) 2 μ := memLp_const 1
  have hleft : Integrable (fun x => (v x - 1) ^ 2) μ := (hv.sub h1).integrable_sq
  have hvz : Integrable (fun x => (v x - z x) ^ 2) μ := (hv.sub hz).integrable_sq
  have hz1 : Integrable (fun x => (z x - 1) ^ 2) μ := (hz.sub h1).integrable_sq
  calc
    (∫ x, (v x - 1) ^ 2 ∂μ) ≤
        ∫ x, 2 * (v x - z x) ^ 2 + 2 * (z x - 1) ^ 2 ∂μ := by
      apply integral_mono hleft ((hvz.const_mul 2).add (hz1.const_mul 2))
      intro x
      change (v x - 1) ^ 2 ≤ 2 * (v x - z x) ^ 2 + 2 * (z x - 1) ^ 2
      nlinarith [sq_nonneg (v x - 2 * z x + 1)]
    _ = _ := by rw [integral_add (hvz.const_mul 2) (hz1.const_mul 2),
      integral_const_mul, integral_const_mul]

theorem integral_sample_mean_square_le
    (m : ℕ) (hm : 1 ≤ m) {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {Ω : Fin m → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : Fin m) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    (v : ι → (i : Fin m) → Ω i → ℝ) (z : (i : Fin m) → Ω i → ℝ)
    (hv : ∀ n i, MemLp (v n i) 2 (μ i)) (hz : ∀ i, MemLp (z i) 2 (μ i))
    (C : ℝ) (hC : 0 ≤ C)
    (hcard : (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ (s.card : ℝ))
    (hmean : ∀ i, (∫ x, z i x ∂μ i) = kernelMass m)
    (hbase : ∀ i, (∫ x, (z i x) ^ 2 ∂μ i) ≤ momentBase m)
    (hdiag : ∀ n ∈ s, ∀ i, (∫ x, (v n i x) ^ 2 ∂μ i) ≤
      8 * (m : ℝ) ^ (3 / 5 : ℝ) * Real.log m)
    (hoff : ∀ n ∈ s, ∀ n' ∈ s, n ≠ n' → ∀ i,
      |(∫ x, v n i x * v n' i x ∂μ i) - (∫ x, (z i x) ^ 2 ∂μ i)| ≤
        C * (m : ℝ) ^ (-(50 : ℝ)))
    (hcross : ∀ n ∈ s, ∀ i,
      |(∫ x, v n i x * z i x ∂μ i) - (∫ x, (z i x) ^ 2 ∂μ i)| ≤
        C * (m : ℝ) ^ (-(50 : ℝ))) :
    (∫ x, ((s.card : ℝ)⁻¹ * (∑ n ∈ s, ∏ i, v n i (x i)) - 1) ^ 2
      ∂Measure.pi μ) ≤ meanSquareBound C m := by
  have hB : 0 ≤ momentBase m := by unfold momentBase; positivity
  have hε : 0 ≤ C * (m : ℝ) ^ (-(50 : ℝ)) := by positivity
  have hb := integral_average_coordinate_products_sub_sq_le s hs v z hv hz
    hB hε hbase hdiag hoff hcross
  simp only [Fintype.card_fin] at hb
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hd : (8 * (m : ℝ) ^ (3 / 5 : ℝ) * Real.log m) ^ m / (s.card : ℝ) ≤
      diagonalError m := by
    apply div_le_div_of_nonneg_left
    · exact pow_nonneg (mul_nonneg (by positivity) (Real.log_nonneg hmreal)) m
    · exact Real.rpow_pos_of_pos hmpos _
    · exact hcard
  have hb' : (∫ x, ((s.card : ℝ)⁻¹ * (∑ n ∈ s, ∏ i, v n i (x i)) -
      ∏ i, z i (x i)) ^ 2 ∂Measure.pi μ) ≤ diagonalError m + 3 * productError C m := by
    dsimp [productError]
    linarith
  have hi := integral_ideal_product_sub_one_sq_le m z hz hmean hbase
  have hvprod (n : ι) : MemLp (fun x => ∏ i, v n i (x i)) 2 (Measure.pi μ) :=
    memLp_coordinate_prod (v n) (hv n)
  have hva : MemLp (fun x => (s.card : ℝ)⁻¹ * (∑ n ∈ s, ∏ i, v n i (x i)))
      2 (Measure.pi μ) :=
    (memLp_finsetSum s (fun n _ => hvprod n)).const_mul _
  have hsplit := integral_sub_one_sq_le_split _ _ hva (memLp_coordinate_prod z hz)
  exact hsplit.trans (add_le_add (mul_le_mul_of_nonneg_left hb' (by norm_num))
    (mul_le_mul_of_nonneg_left hi (by norm_num)))

theorem lintegral_sample_mean_square_eq_ofReal
    (m : ℕ) {ι : Type*} (s : Finset ι)
    {Ω : Fin m → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : Fin m) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    (v : ι → (i : Fin m) → Ω i → ℝ)
    (hv : ∀ n i, MemLp (v n i) 2 (μ i)) :
    (∫⁻ x, ENNReal.ofReal
      (((s.card : ℝ)⁻¹ * (∑ n ∈ s, ∏ i, v n i (x i)) - 1) ^ 2) ∂Measure.pi μ) =
      ENNReal.ofReal (∫ x,
        ((s.card : ℝ)⁻¹ * (∑ n ∈ s, ∏ i, v n i (x i)) - 1) ^ 2 ∂Measure.pi μ) := by
  have hvprod (n : ι) : MemLp (fun x => ∏ i, v n i (x i)) 2 (Measure.pi μ) :=
    memLp_coordinate_prod (v n) (hv n)
  have hva : MemLp (fun x => (s.card : ℝ)⁻¹ * (∑ n ∈ s, ∏ i, v n i (x i)))
      2 (Measure.pi μ) :=
    (memLp_finsetSum s (fun n _ => hvprod n)).const_mul _
  have h1 : MemLp (fun _ : (i : Fin m) → Ω i => (1 : ℝ)) 2 (Measure.pi μ) :=
    memLp_const 1
  exact (ofReal_integral_eq_lintegral_ofReal (hva.sub h1).integrable_sq
    (Eventually.of_forall fun x => sq_nonneg _)).symm

theorem tendsto_ofReal_meanSquareBound (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun m => ENNReal.ofReal (meanSquareBound C m)) atTop (𝓝 0) := by
  simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (tendsto_meanSquareBound C hC)

theorem tendsto_zero_of_meanSquareBound {E : ℕ → ℝ≥0∞} (C : ℝ) (hC : 0 ≤ C)
    (hE : ∀ᶠ m in atTop, E m ≤ ENNReal.ofReal (meanSquareBound C m)) :
    Tendsto E atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_ofReal_meanSquareBound C hC) (Eventually.of_forall fun _ => bot_le) hE

end Invariant233.SamplingAsymptotics

end

end OAI
