import OAI.Analysis.IrrationalRotation.Sampling.SamplingMomentBounds

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace InvariantRotation.SamplingMomentBounds

theorem memLp_coordinate_prod {κ : Type*} [Fintype κ] {Ω : κ → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : κ) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] (f : (i : κ) → Ω i → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (μ i)) :
    MemLp (fun x => ∏ i, f i (x i)) 2 (Measure.pi μ) := by
  have hm : AEStronglyMeasurable (fun x => ∏ i, f i (x i)) (Measure.pi μ) := by
    apply Finset.aestronglyMeasurable_fun_prod
    intro i _
    exact (hf i).aestronglyMeasurable.comp_measurePreserving (measurePreserving_eval μ i)
  apply (memLp_two_iff_integrable_sq hm).2
  simpa only [Finset.prod_pow] using
    Integrable.fintype_prod_dep (fun i => (hf i).integrable_sq)

theorem integral_coordinate_prod_mul {κ : Type*} [Fintype κ] {Ω : κ → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : κ) → Measure (Ω i)}
    [∀ i, SigmaFinite (μ i)] (f g : (i : κ) → Ω i → ℝ) :
    (∫ x, (∏ i, f i (x i)) * (∏ i, g i (x i)) ∂Measure.pi μ) =
      ∏ i, ∫ x, f i x * g i x ∂μ i := by
  simp_rw [← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (fun i x => f i x * g i x)

theorem integral_coordinate_prod_sq {κ : Type*} [Fintype κ] {Ω : κ → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : κ) → Measure (Ω i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : κ) → Ω i → ℝ) :
    (∫ x, (∏ i, f i (x i)) ^ 2 ∂Measure.pi μ) =
      ∏ i, ∫ x, (f i x) ^ 2 ∂μ i := by
  simpa only [pow_two] using integral_coordinate_prod_mul f f (μ := μ)

theorem coordinate_product_pair_error_le
    {κ : Type*} [Fintype κ] {Ω : κ → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : κ) → Measure (Ω i)}
    [∀ i, SigmaFinite (μ i)] (f g z : (i : κ) → Ω i → ℝ)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hbase : ∀ i, (∫ x, (z i x) ^ 2 ∂μ i) ≤ B)
    (herror : ∀ i, |(∫ x, f i x * g i x ∂μ i) - (∫ x, (z i x) ^ 2 ∂μ i)| ≤ ε) :
    |(∫ x, (∏ i, f i (x i)) * (∏ i, g i (x i)) ∂Measure.pi μ) -
        (∫ x, (∏ i, z i (x i)) ^ 2 ∂Measure.pi μ)| ≤
      (Fintype.card κ : ℝ) * ε * (B + ε) ^ (Fintype.card κ - 1) := by
  rw [integral_coordinate_prod_mul, integral_coordinate_prod_sq]
  let A : κ → ℝ := fun i => ∫ x, (z i x) ^ 2 ∂μ i
  have he := product_perturbation_bound (Finset.univ : Finset κ) A
    (fun i => (∫ x, f i x * g i x ∂μ i) - A i) hB hε
    (fun i _ => integral_nonneg (fun _ => sq_nonneg _)) (fun i _ => hbase i)
    (fun i _ => herror i)
  simpa only [add_sub_cancel, Finset.card_univ] using he

theorem coordinate_product_sq_le_pow
    {κ : Type*} [Fintype κ] {Ω : κ → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : κ) → Measure (Ω i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : κ) → Ω i → ℝ)
    {D : ℝ} (h : ∀ i, (∫ x, (f i x) ^ 2 ∂μ i) ≤ D) :
    (∫ x, (∏ i, f i (x i)) ^ 2 ∂Measure.pi μ) ≤ D ^ Fintype.card κ := by
  rw [integral_coordinate_prod_sq]
  calc
    (∏ i, ∫ x, (f i x) ^ 2 ∂μ i) ≤ ∏ _i : κ, D :=
      Finset.prod_le_prod₀ (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
        (fun index _ => h index)
    _ = D ^ Fintype.card κ := by simp

theorem integral_average_coordinate_products_sub_sq_le
    {κ ι : Type*} [Fintype κ] {Ω : κ → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : κ) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)]
    (s : Finset ι) (hs : s.Nonempty)
    (v : ι → (i : κ) → Ω i → ℝ) (z : (i : κ) → Ω i → ℝ)
    (hv : ∀ n i, MemLp (v n i) 2 (μ i)) (hz : ∀ i, MemLp (z i) 2 (μ i))
    {B D ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hbase : ∀ i, (∫ x, (z i x) ^ 2 ∂μ i) ≤ B)
    (hdiag : ∀ n ∈ s, ∀ i, (∫ x, (v n i x) ^ 2 ∂μ i) ≤ D)
    (hoff : ∀ n ∈ s, ∀ m ∈ s, n ≠ m → ∀ i,
      |(∫ x, v n i x * v m i x ∂μ i) - (∫ x, (z i x) ^ 2 ∂μ i)| ≤ ε)
    (hcross : ∀ n ∈ s, ∀ i,
      |(∫ x, v n i x * z i x ∂μ i) - (∫ x, (z i x) ^ 2 ∂μ i)| ≤ ε) :
    (∫ x, ((s.card : ℝ)⁻¹ * (∑ n ∈ s, ∏ i, v n i (x i)) -
        ∏ i, z i (x i)) ^ 2 ∂Measure.pi μ) ≤
      D ^ Fintype.card κ / (s.card : ℝ) +
        3 * ((Fintype.card κ : ℝ) * ε * (B + ε) ^ (Fintype.card κ - 1)) := by
  let E : ℝ := (Fintype.card κ : ℝ) * ε * (B + ε) ^ (Fintype.card κ - 1)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hd (n : ι) (hn : n ∈ s) :
      (∫ x, (∏ i, v n i (x i)) ^ 2 ∂Measure.pi μ) ≤ D ^ Fintype.card κ :=
    coordinate_product_sq_le_pow (v n) (hdiag n hn)
  have ho (n : ι) (hn : n ∈ s) (m : ι) (hm : m ∈ s) (hnm : n ≠ m) :
      (∫ x, (∏ i, v n i (x i)) * (∏ i, v m i (x i)) ∂Measure.pi μ) ≤
        (∫ x, (∏ i, z i (x i)) ^ 2 ∂Measure.pi μ) + E := by
    have he := coordinate_product_pair_error_le (v n) (v m) z hB hε hbase (hoff n hn m hm hnm)
    have hu := (abs_le.mp he).2
    change _ ≤ _ + E
    linarith
  have hc (n : ι) (hn : n ∈ s) :
      (∫ x, (∏ i, z i (x i)) ^ 2 ∂Measure.pi μ) - E ≤
        (∫ x, (∏ i, v n i (x i)) * (∏ i, z i (x i)) ∂Measure.pi μ) := by
    have he := coordinate_product_pair_error_le (v n) z z hB hε hbase (hcross n hn)
    have hl := (abs_le.mp he).1
    change _ - E ≤ _
    linarith
  exact integral_average_sub_sq_le_of_memLp (μ := Measure.pi μ) s hs
    (fun n x => ∏ i, v n i (x i)) (fun x => ∏ i, z i (x i))
    (fun n => memLp_coordinate_prod (v n) (hv n)) (memLp_coordinate_prod z hz)
    hE hd ho hc

theorem integral_iterated_eq_coordinate_prod {κ α β : Type*} [Fintype κ]
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : κ → Measure α) (ν : κ → Measure β)
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (F : (κ → α) → (κ → β) → ℝ)
    (hF : Integrable (fun q : κ → α × β => F (fun i => (q i).1) (fun i => (q i).2))
      (Measure.pi (fun i => (μ i).prod (ν i)))) :
    (∫ a, ∫ b, F a b ∂Measure.pi ν ∂Measure.pi μ) =
      ∫ q : κ → α × β, F (fun i => (q i).1) (fun i => (q i).2)
        ∂Measure.pi (fun i => (μ i).prod (ν i)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow α β κ
  have he := measurePreserving_arrowProdEquivProdArrow α β κ μ ν
  have hgroup : Integrable (fun p : (κ → α) × (κ → β) => F p.1 p.2)
      ((Measure.pi μ).prod (Measure.pi ν)) := by
    apply (he.integrable_comp_emb e.measurableEmbedding).1
    exact hF
  rw [← integral_prod _ hgroup]
  exact (he.integral_comp' (fun p => F p.1 p.2)).symm

theorem memLp_average_coordinate_products {κ ι : Type*} [Fintype κ] {Ω : κ → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : κ) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] (s : Finset ι)
    (v : ι → (i : κ) → Ω i → ℝ) (z : (i : κ) → Ω i → ℝ)
    (hv : ∀ n i, MemLp (v n i) 2 (μ i)) (hz : ∀ i, MemLp (z i) 2 (μ i)) :
    MemLp (fun x => (s.card : ℝ)⁻¹ * (∑ n ∈ s, ∏ i, v n i (x i)) -
      ∏ i, z i (x i)) 2 (Measure.pi μ) := by
  exact ((memLp_finsetSum s (fun n _ => memLp_coordinate_prod (v n) (hv n))).const_mul
    (s.card : ℝ)⁻¹).sub (memLp_coordinate_prod z hz)

theorem expected_integral_average_products_sub_sq_le
    {κ ι α β : Type*} [Fintype κ] [MeasurableSpace α] [MeasurableSpace β]
    (μ : κ → Measure α) (ν : κ → Measure β)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (s : Finset ι) (hs : s.Nonempty) (v : ι → κ → α → β → ℝ) (z : κ → β → ℝ)
    (hv : ∀ n i, MemLp (fun p : α × β => v n i p.1 p.2) 2 ((μ i).prod (ν i)))
    (hz : ∀ i, MemLp (z i) 2 (ν i))
    {B D ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hbase : ∀ i, (∫ x, (z i x) ^ 2 ∂ν i) ≤ B)
    (hdiag : ∀ n ∈ s, ∀ i, (∫ p : α × β, (v n i p.1 p.2) ^ 2 ∂(μ i).prod (ν i)) ≤ D)
    (hoff : ∀ n ∈ s, ∀ m ∈ s, n ≠ m → ∀ i,
      |(∫ p : α × β, v n i p.1 p.2 * v m i p.1 p.2 ∂(μ i).prod (ν i)) -
        (∫ x, (z i x) ^ 2 ∂ν i)| ≤ ε)
    (hcross : ∀ n ∈ s, ∀ i,
      |(∫ p : α × β, v n i p.1 p.2 * z i p.2 ∂(μ i).prod (ν i)) -
        (∫ x, (z i x) ^ 2 ∂ν i)| ≤ ε) :
    (∫ a, ∫ b, ((s.card : ℝ)⁻¹ * (∑ n ∈ s, ∏ i, v n i (a i) (b i)) -
        ∏ i, z i (b i)) ^ 2 ∂Measure.pi ν ∂Measure.pi μ) ≤
      D ^ Fintype.card κ / (s.card : ℝ) +
        3 * ((Fintype.card κ : ℝ) * ε * (B + ε) ^ (Fintype.card κ - 1)) := by
  let V : ι → κ → α × β → ℝ := fun n i p => v n i p.1 p.2
  let Z : κ → α × β → ℝ := fun i p => z i p.2
  have hZ (i : κ) : MemLp (Z i) 2 ((μ i).prod (ν i)) := (hz i).comp_snd (μ i)
  have hZsq (i : κ) : (∫ p : α × β, (Z i p) ^ 2 ∂(μ i).prod (ν i)) =
      ∫ x, (z i x) ^ 2 ∂ν i := by
    simpa [Z] using (integral_fun_snd (μ := μ i) (ν := ν i) (fun x => (z i x) ^ 2))
  have hb : ∀ i, (∫ p : α × β, (Z i p) ^ 2 ∂(μ i).prod (ν i)) ≤ B := by
    simpa only [hZsq] using hbase
  have ho : ∀ n ∈ s, ∀ m ∈ s, n ≠ m → ∀ i,
      |(∫ p, V n i p * V m i p ∂(μ i).prod (ν i)) -
        (∫ p, (Z i p) ^ 2 ∂(μ i).prod (ν i))| ≤ ε := by
    simpa only [hZsq] using hoff
  have hc : ∀ n ∈ s, ∀ i,
      |(∫ p, V n i p * Z i p ∂(μ i).prod (ν i)) -
        (∫ p, (Z i p) ^ 2 ∂(μ i).prod (ν i))| ≤ ε := by
    simpa only [hZsq] using hcross
  have h := integral_average_coordinate_products_sub_sq_le
    (μ := fun i => (μ i).prod (ν i)) s hs V Z hv hZ hB hε hb hdiag ho hc
  have hi := (memLp_average_coordinate_products s V Z hv hZ).integrable_sq
  rw [integral_iterated_eq_coordinate_prod μ ν _ hi]
  exact h

end InvariantRotation.SamplingMomentBounds

end OAI
