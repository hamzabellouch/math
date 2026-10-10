import Mathlib
import OAI.Probability.JammingConcavity.RPCRankUniqueness

namespace OAI

/-! Deletion. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
open Classical
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
open scoped NNReal BigOperators
open MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace MicroscopicJamming
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open scoped Function in
lemma separated_unit_card (s : Finset E) {δ : ℝ} (hδ : 0 < δ)
    (hs : ∀ c ∈ s, ‖c‖ ≤ 1)
    (h : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → δ ≤ ‖c-d‖) :
    (s.card : ℝ) ≤ (1+2/δ)^Module.finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let r : ℝ := δ/2
  let ρ : ℝ := 1+δ/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let A := ⋃ c ∈ s, ball (c : E) r
  have hD : Set.Pairwise (s : Set E) (Disjoint on fun c => ball (c : E) r) := by
    rintro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    simpa [r] using h c hc d hd hcd
  have hA : A ⊆ ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    simpa [ρ, r, dist_zero_right, add_comm] using add_le_add_left (hs x hx) r
  have hI : (s.card : ℝ≥0∞) * ENNReal.ofReal (r^Module.finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal (ρ^Module.finrank ℝ E) * μ (ball 0 1) := by
    calc
      _ = μ A := by
        rw [show A = ⋃ c ∈ s, ball (c : E) r from rfl,
          measure_biUnion_finset hD (fun _ _ => measurableSet_ball)]
        simp only [μ.addHaar_ball_of_pos _ hr, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono hA
      _ = _ := by rw [μ.addHaar_ball_of_pos _ hρ]
  have hJ : (s.card : ℝ≥0∞) * ENNReal.ofReal (r^Module.finrank ℝ E) ≤
      ENNReal.ofReal (ρ^Module.finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne'
      measure_ball_lt_top.ne).mp hI
  have hK : (s.card : ℝ) * r^Module.finrank ℝ E ≤ ρ^Module.finrank ℝ E := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg hr.le _)] using
      ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) hJ
  have hratio : ρ / r = 1+2/δ := by
    dsimp [ρ, r]
    field_simp
    ring
  rw [← hratio, div_pow]
  exact (le_div_iff₀ (pow_pos hr _)).mpr hK

 
theorem unit_sphere_net {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : Finset E, (∀ y ∈ S, ‖y‖ = 1) ∧
      (∀ x : E, ‖x‖ = 1 → ∃ y ∈ S, dist x y ≤ δ) ∧
      (S.card : ℝ) ≤ (1+2/δ)^Module.finrank ℝ E := by
  classical
  let d : ℝ≥0 := ⟨δ, hδ.le⟩
  let A := sphere (0 : E) 1
  have hhalf : d/2 ≠ 0 := by
    apply div_ne_zero
    · exact ne_of_gt (show 0 < d from hδ)
    · norm_num
  obtain ⟨T, _, hTf, hTcover⟩ := exists_finite_isCover_of_isCompact hhalf (isCompact_sphere (0:E) 1)
  have hpack : packingNumber d A ≠ ⊤ := by
    apply ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hTf)
    calc packingNumber d A = packingNumber (2*(d/2)) A := by rw [mul_div_cancel₀ _ (by norm_num)]
         _ ≤ externalCoveringNumber (d/2) A := packingNumber_two_mul_le_externalCoveringNumber _ _
         _ ≤ T.encard := hTcover.externalCoveringNumber_le_encard
  let C := maximalSeparatedSet d A
  have hCf : C.Finite := Set.encard_ne_top_iff.mp (by
    rw [show C = maximalSeparatedSet d A from rfl, encard_maximalSeparatedSet hpack]
    exact hpack)
  have hsub : C ⊆ A := maximalSeparatedSet_subset
  have hsep : IsSeparated d C := isSeparated_maximalSeparatedSet
  have hcover : IsCover d A C := isCover_maximalSeparatedSet hpack
  refine ⟨hCf.toFinset, ?_, ?_, ?_⟩
  · intro y hy
    simpa [A, mem_sphere, dist_zero_right] using hsub (hCf.mem_toFinset.mp hy)
  · intro x hx
    have hxA : x ∈ A := by simpa [A, mem_sphere, dist_zero_right] using hx
    obtain ⟨y, hy, hxy⟩ := hcover hxA
    refine ⟨y, hCf.mem_toFinset.mpr hy, ?_⟩
    exact_mod_cast hxy
  · apply separated_unit_card _ hδ
    · intro y hy
      have h := hsub (hCf.mem_toFinset.mp hy)
      exact le_of_eq (by simpa [A, mem_sphere, dist_zero_right] using h)
    · intro x hx y hy hxy
      have hd := hsep (hCf.mem_toFinset.mp hx) (hCf.mem_toFinset.mp hy) hxy
      have : δ < dist x y := by
        dsimp at hd
        rw [ENNReal.coe_nnreal_eq, edist_dist] at hd
        exact ENNReal.ofReal_lt_ofReal_iff'.mp hd |>.1
      simpa only [dist_eq_norm] using this.le

end MicroscopicJamming

 
open Metric
open scoped RealInnerProductSpace

namespace MicroscopicJamming
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma opNorm_le_of_quarter_nets (A : E →L[ℝ] F) (S : Finset E) (T : Finset F)
    (_hS : ∀ x ∈ S, ‖x‖ = 1) (hT : ∀ v ∈ T, ‖v‖ = 1)
    (hSc : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ S, dist x y ≤ 1/4)
    (hTc : ∀ v : F, ‖v‖ = 1 → ∃ w ∈ T, dist v w ≤ 1/4)
    {t : ℝ} (ht : 0 ≤ t)
    (hA : ∀ x ∈ S, ∀ v ∈ T, |inner ℝ v (A x)| ≤ t) : ‖A‖ ≤ 2*t := by
  have hAll : ∀ x : E, ‖x‖ = 1 → ∀ v : F, ‖v‖ = 1 →
      |inner ℝ v (A x)| ≤ t+‖A‖/2 := by
    intro x hx v hv
    obtain ⟨y, hy, hxy⟩ := hSc x hx
    obtain ⟨w, hw, hvw⟩ := hTc v hv
    have hdecomp : inner ℝ v (A x) = inner ℝ (v-w) (A x) +
        inner ℝ w (A (x-y)) + inner ℝ w (A y) := by
      rw [map_sub, inner_sub_left, inner_sub_right]
      ring
    have h1 : |inner ℝ (v-w) (A x)| ≤ ‖A‖/4 := by
      calc
        _ ≤ ‖v-w‖ * ‖A x‖ := abs_real_inner_le_norm _ _
        _ ≤ (1/4) * (‖A‖ * 1) := by
          gcongr
          · simpa only [dist_eq_norm] using hvw
          · simpa only [hx] using A.le_opNorm x
        _ = _ := by ring
    have h2 : |inner ℝ w (A (x-y))| ≤ ‖A‖/4 := by
      calc
        _ ≤ ‖w‖ * ‖A (x-y)‖ := abs_real_inner_le_norm _ _
        _ ≤ 1 * (‖A‖ * (1/4)) := by
          rw [hT w hw]
          gcongr
          calc ‖A (x-y)‖ ≤ ‖A‖ * ‖x-y‖ := A.le_opNorm _
               _ ≤ ‖A‖ * (1/4) := by gcongr; simpa only [dist_eq_norm] using hxy
        _ = _ := by ring
    rw [hdecomp]
    calc
      _ ≤ |inner ℝ (v-w) (A x)| + |inner ℝ w (A (x-y))| +
          |inner ℝ w (A y)| := (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
      _ ≤ t+‖A‖/2 := by linarith [hA y hy w hw]
  have hnorm : ‖A‖ ≤ t+‖A‖/2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    by_cases hz : A x = 0
    · simp [hz]; positivity
    have hn : ‖A x‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hv : ‖(‖A x‖⁻¹ : ℝ) • A x‖ = 1 := by
      simp only [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact inv_mul_cancel₀ hn
    have h := hAll x hx ((‖A x‖⁻¹ : ℝ) • A x) hv
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq] at h
    have he : ‖A x‖⁻¹ * ‖A x‖^2 = ‖A x‖ := by field_simp
    rw [he, abs_of_nonneg (norm_nonneg _)] at h
    exact h
  linarith

end MicroscopicJamming
namespace MicroscopicJamming
open scoped RealInnerProductSpace

lemma subGaussian_abs_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (h : HasSubgaussianMGF X (3/2) μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {a | t < |X a|} ≤ 2 * Real.exp (-t^2/3) := by
  calc
    _ ≤ μ.real ({a | t ≤ X a} ∪ {a | t ≤ -X a}) := by
      apply measureReal_mono _ (measure_ne_top μ _)
      intro a ha
      change t < |X a| at ha
      rcases lt_abs.mp ha with ha | ha
      · exact Or.inl ha.le
      · exact Or.inr ha.le
    _ ≤ μ.real {a | t ≤ X a} + μ.real {a | t ≤ -X a} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-t^2/3) := by
      have h1 := h.measure_ge_le ht
      have h2 := h.neg.measure_ge_le ht
      norm_num only [NNReal.coe_div, NNReal.coe_ofNat] at h1 h2
      change μ.real {a | t ≤ -X a} ≤ _ at h2
      linarith

lemma quarter_net_operator_tail {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (L : Ω → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hg : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 →
      ∀ v : EuclideanSpace ℝ (Fin m), ‖v‖ = 1 →
      HasSubgaussianMGF (fun a => inner ℝ v (L a x)) (3/2) μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {a | 2*t < ‖L a‖} ≤ 2 * (9:ℝ)^(m+n) * Real.exp (-t^2/3) := by
  classical
  obtain ⟨S, hS, hSc, hSb⟩ := unit_sphere_net (E := EuclideanSpace ℝ (Fin n)) (δ := 1/4) (by norm_num)
  obtain ⟨T, hT, hTc, hTb⟩ := unit_sphere_net (E := EuclideanSpace ℝ (Fin m)) (δ := 1/4) (by norm_num)
  have hsub : {a | 2*t < ‖L a‖} ⊆
      ⋃ p ∈ S ×ˢ T, {a | t < |inner ℝ p.2 (L a p.1)|} := by
    intro a ha
    by_contra hnot
    have hAll : ∀ x ∈ S, ∀ v ∈ T, |inner ℝ v (L a x)| ≤ t := by
      intro x hx v hv
      by_contra h
      apply hnot
      exact mem_iUnion₂.mpr ⟨(x,v), Finset.mem_product.mpr ⟨hx,hv⟩, lt_of_not_ge h⟩
    exact (not_le_of_gt ha) (opNorm_le_of_quarter_nets (L a) S T hS hT hSc hTc ht hAll)
  calc
    _ ≤ μ.real (⋃ p ∈ S ×ˢ T, {a | t < |inner ℝ p.2 (L a p.1)|}) := measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ ∑ p ∈ S ×ˢ T, μ.real {a | t < |inner ℝ p.2 (L a p.1)|} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ S ×ˢ T, 2 * Real.exp (-t^2/3) := by
      apply Finset.sum_le_sum
      intro p hp
      rcases Finset.mem_product.mp hp with ⟨hx,hv⟩
      exact subGaussian_abs_tail (hg _ (hS _ hx) _ (hT _ hv)) ht
    _ = ((S.card:ℝ) * (T.card:ℝ)) * (2 * Real.exp (-t^2/3)) := by
      simp only [Finset.sum_const, Finset.card_product, nsmul_eq_mul, Nat.cast_mul]
    _ ≤ ((9:ℝ)^n * (9:ℝ)^m) * (2 * Real.exp (-t^2/3)) := by
      norm_num only [finrank_euclideanSpace_fin] at hSb hTb
      gcongr
    _ = _ := by rw [← pow_add]; rw [add_comm n m]; ring

def matrixOperator {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  LinearMap.toContinuousLinearMap A.toEuclideanLin

lemma matrixOperator_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (j : Fin m) :
    matrixOperator A x j = ∑ i, A j i * x i := rfl

lemma measurePreserving_uncurry {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : (ι × κ) → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] :
    MeasurePreserving (fun a : ι → κ → ℝ => Function.uncurry a)
      (Measure.pi fun i => Measure.pi fun k => μ (i, k)) (Measure.pi μ) := by
  refine ⟨by fun_prop, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  have he : (fun a : ι → κ → ℝ => Function.uncurry a) ⁻¹' Set.univ.pi s =
      (Set.univ.pi (fun i => Set.univ.pi fun k => s (i, k))) := by
    ext a
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.uncurry_apply_pair,
      Prod.forall]
  rw [he]
  rw [Measure.pi_pi]
  simp only [Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun p : ι × κ => μ p (s p))).symm

lemma matrix_bilinear_subGaussian {m n : ℕ} {ε : ℝ}
    (he : ε ∈ Set.Icc (0 : ℝ) (1/2))
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1)
    (v : EuclideanSpace ℝ (Fin m)) (hv : ‖v‖ = 1) :
    HasSubgaussianMGF (fun A : Fin m → Fin n → ℝ => inner ℝ v (matrixOperator A x))
      (3/2) (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε) := by
  let w : Fin m × Fin n → ℝ := fun p => v p.1 * x p.2
  have h := mixture_linear_subGaussian he w
  have hc : (∑ i, NNReal.mk ((w i)^2) (sq_nonneg (w i)) * (3/2)) = (3/2:ℝ≥0) := by
    apply NNReal.eq
    simp only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_mk]
    rw [← Finset.sum_mul, Fintype.sum_prod_type]
    have hsx : ∑ i, x i^2 = 1 := by simpa only [hx, one_pow] using (EuclideanSpace.real_norm_sq_eq x).symm
    have hsv : ∑ j, v j^2 = 1 := by simpa only [hv, one_pow] using (EuclideanSpace.real_norm_sq_eq v).symm
    simp only [w, mul_pow, ← Finset.mul_sum, hsx, mul_one, hsv, one_mul]
  rw [hc] at h
  rw [← (measurePreserving_uncurry (fun _ : Fin m × Fin n => coordinateLaw ε)).map_eq] at h
  have hm := h.of_map (by fun_prop : Measurable (fun A : Fin m → Fin n → ℝ => Function.uncurry A)).aemeasurable
  have hf : ((fun a => ∑ i, w i * a i) ∘ fun A : Fin m → Fin n → ℝ => Function.uncurry A) =
      (fun A => inner ℝ v (matrixOperator A x)) := by
    funext A
    simp only [Function.comp_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Fintype.sum_prod_type, w]
    apply Finset.sum_congr rfl
    intro j _
    change (∑ i, v j * x i * A j i) = (∑ i, A j i * x i) * v j
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rwa [hf] at hm

 

theorem mixture_operator_tail {m n : ℕ} {ε : ℝ}
    (he : ε ∈ Set.Icc (0 : ℝ) (1/2)) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε).real
      {A | 2*t < ‖matrixOperator A‖} ≤ 2 * (9:ℝ)^(m+n) * Real.exp (-t^2/3) := by
  exact quarter_net_operator_tail _ (fun A : Fin m → Fin n → ℝ => matrixOperator A) (matrix_bilinear_subGaussian he) ht

end MicroscopicJamming

end

end OAI
