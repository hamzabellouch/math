import Mathlib
import OAI.Geometry.CAT0Fillings.Mass.TestDensity

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
namespace BorelCoefficients
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] {k : ℕ}

theorem exists_measurable_coefficient_density {T : Functional X k}
    (hT : IsMetricCurrent T) (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : Controls T μ) (π : Fin k → X → ℝ) (hπ : ∀ i, LipschitzWith 1 (π i)) :
    ∃ ρ : X → ℝ, Measurable ρ ∧ (∀ x, |ρ x| ≤ 1) ∧
      ∀ b : X → ℝ, BoundedLip b → T b π = ∫ x, b x * ρ x ∂μ := by
  obtain ⟨r,hrm,hri,hr1,hr⟩ := exists_coefficient_density μ hT hμ π hπ
  let ρ := fun x => max (-1) (min 1 (hrm.mk r x))
  have heq : ρ =ᵐ[μ] r := by
    filter_upwards [hrm.ae_eq_mk,hr1] with x hx hy
    dsimp only [ρ]
    rw [←hx,min_eq_right (abs_le.mp hy).2,max_eq_right (abs_le.mp hy).1]
  refine ⟨ρ,measurable_const.max (measurable_const.min hrm.stronglyMeasurable_mk.measurable),?_,?_⟩
  · intro x
    exact abs_le.mpr ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  · intro b hb
    rw [hr b hb]
    apply integral_congr_ae
    filter_upwards [heq] with x hx
    rw [hx]

theorem exists_mass_spectrum (k : ℕ) :
    ∃ π : ℕ → Fin k → X → ℝ, (∀ j i, LipschitzWith 1 (π j i)) ∧
      ∀ {T : Functional X k} (hT : IsMetricCurrent T),
      ∃ ρ : ℕ → X → ℝ,
        (∀ j, Measurable (ρ j)) ∧ (∀ j x, |ρ j x| ≤ 1) ∧
        (∀ j b, BoundedLip b → T b (π j) =
          ∫ x, b x * ρ j x ∂MassMeasure.currentMassMeasure hT) ∧
        mass T = ∫ x, ⨆ j, |ρ j x| ∂MassMeasure.currentMassMeasure hT := by
  obtain ⟨b,π,ht,hdet⟩ := Foundations.exists_countable_mass_tests (X := X) k
  let tup j := π (Nat.unpair j).1 (Nat.unpair j).2
  refine ⟨tup,fun j => (ht _ _).2,?_⟩
  intro T hT
  let μ := MassMeasure.currentMassMeasure hT
  have hμ : Controls T μ := MassMeasure.currentMassMeasure_controls hT
  choose ρ hρm hρ1 hρ using fun j =>
    exists_measurable_coefficient_density hT μ hμ (tup j) ((ht _ _).2)
  let R x := ⨆ j, |ρ j x|
  have hbd x : BddAbove (range (fun j => |ρ j x|)) := ⟨1,by rintro _ ⟨j,rfl⟩; exact hρ1 j x⟩
  have hR0 x : 0 ≤ R x := (abs_nonneg (ρ 0 x)).trans (le_ciSup (hbd x) 0)
  have hR1 x : R x ≤ 1 := ciSup_le (hρ1 · x)
  have hRm : Measurable R := Measurable.iSup (fun j => (hρm j).abs)
  have hRi : Integrable R μ := Integrable.mono' (integrable_const (1:ℝ)) hRm.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (hR0 x)]; exact hR1 x)
  let ν := μ.withDensity (fun x => ENNReal.ofReal (R x))
  have hνle : ν ≤ μ := by
    calc ν ≤ μ.withDensity (fun _ => 1) := withDensity_mono (Eventually.of_forall fun x => by
          simpa using ENNReal.ofReal_le_ofReal (hR1 x))
         _ = μ := withDensity_one
  let : IsFiniteMeasure ν := isFiniteMeasure_of_le μ hνle
  have hνint (f : X → ℝ) : (∫ x, f x ∂ν) = ∫ x, R x*f x ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul (hRm.ennreal_ofReal)]
    · simp only [ENNReal.toReal_ofReal (hR0 _),smul_eq_mul]
    · exact Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hνc : Controls T ν := by
    apply hdet T hT ν inferInstance
    intro K j
    have hh := hρ (Nat.pair K j) (b K j) (ht K j).1
    simp only [tup,Nat.unpair_pair] at hh
    rw [hh,hνint]
    apply (abs_integral_le_integral_abs).trans
    apply integral_mono
    · exact ((BorelCoefficients.integrable_boundedLip μ (ht K j).1).abs).mono'
        (((ht K j).1.continuous.measurable.mul (hρm _)).abs.aestronglyMeasurable)
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs,abs_abs,abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hρ1 _ _))
    · exact (BorelCoefficients.integrable_boundedLip μ (ht K j).1).abs.bdd_mul hRm.aestronglyMeasurable
        (Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (hR0 x)]; exact hR1 x)
    · intro x
      dsimp only
      rw [abs_mul,mul_comm (R x)]
      exact mul_le_mul_of_nonneg_left (le_ciSup (hbd x) (Nat.pair K j)) (abs_nonneg _)
  have htotal : mass T ≤ ∫ x, R x ∂μ := by
    calc mass T ≤ ν.real univ := mass_le_measure inferInstance hνc
         _ = ∫ x, (1:ℝ) ∂ν := by simp
         _ = ∫ x, R x ∂μ := by rw [hνint]; simp
  refine ⟨ρ,hρm,hρ1,hρ,le_antisymm htotal ?_⟩
  calc (∫ x, R x ∂μ) ≤ ∫ x, (1:ℝ) ∂μ := integral_mono hRi (integrable_const _) hR1
       _ = mass T := by simpa only [integral_const,smul_eq_mul,mul_one] using
          MassMeasure.currentMassMeasure_total hT

end BorelCoefficients
end CAT0Fillings
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal BigOperators

namespace CAT0Fillings
namespace BorelCoefficients

lemma abs_div_sub_div_le {a b A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hb : |b| ≤ B) : |a/A-b/B| ≤ |a-b|+|A-B| := by
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  calc |a/A-b/B| = |(a-b)/A+b*(B-A)/(A*B)| := by
         congr 1; field_simp; ring
       _ ≤ |(a-b)/A|+|b*(B-A)/(A*B)| := abs_add_le _ _
       _ = |a-b|/A+|b| *|A-B|/(A*B) := by
         rw [abs_div,abs_div,abs_mul,abs_mul,abs_of_pos hA0,abs_of_pos hB0,abs_sub_comm B A]
       _ ≤ |a-b|+|A-B| := by
         apply add_le_add
         · exact div_le_self (abs_nonneg _) hA
         · apply (div_le_iff₀ (mul_pos hA0 hB0)).mpr
           calc |b| *|A-B| ≤ B*|A-B| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
                _ ≤ |A-B| *(A*B) := by
                  have hh := mul_le_mul_of_nonneg_left hA hB0.le
                  nlinarith [mul_le_mul_of_nonneg_left hh (abs_nonneg (A-B))]

variable {ι : Type*} [Fintype ι]
noncomputable def coefficientScale (v : ι → ℝ) : ℝ := max 1 (∑ i, |v i|)
noncomputable def normalizeCoefficients (v : ι → ℝ) (i : ι) : ℝ := v i/coefficientScale v

lemma coefficientScale_one_le (v : ι → ℝ) : 1 ≤ coefficientScale v := le_max_left _ _
lemma abs_le_coefficientScale (v : ι → ℝ) (i : ι) : |v i| ≤ coefficientScale v :=
  (Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)).trans (le_max_right _ _)
lemma normalizeCoefficients_budget (v : ι → ℝ) : ∑ i, |normalizeCoefficients v i| ≤ 1 := by
  simp only [normalizeCoefficients,abs_div,abs_of_pos (lt_of_lt_of_le zero_lt_one (coefficientScale_one_le v)),
    ←Finset.sum_div]
  exact (div_le_one (lt_of_lt_of_le zero_lt_one (coefficientScale_one_le v))).mpr (le_max_right _ _)
lemma normalizeCoefficients_fixed (v : ι → ℝ) (hv : ∑ i, |v i| ≤ 1) :
    normalizeCoefficients v = v := by
  funext i
  simp only [normalizeCoefficients,coefficientScale,max_eq_left hv,div_one]

lemma abs_coefficientScale_sub_le (v w : ι → ℝ) :
    |coefficientScale v-coefficientScale w| ≤ ∑ i, |v i-w i| := by
  calc |coefficientScale v-coefficientScale w| ≤ |(∑ i, |v i|)-(∑ i, |w i|)| := by
         simpa [coefficientScale,Real.dist_eq,max_comm] using
           (LipschitzWith.id.max (LipschitzWith.const (1:ℝ))).dist_le_mul
             (∑ i, |v i|) (∑ i, |w i|)
       _ ≤ ∑ i, |v i-w i| := by
         rw [←Finset.sum_sub_distrib]
         exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => abs_abs_sub_abs_le _ _)

lemma normalizeCoefficients_dist_le (v w : ι → ℝ) (i : ι) :
    |normalizeCoefficients v i-normalizeCoefficients w i| ≤ 2*∑ j, |v j-w j| := by
  exact (abs_div_sub_div_le (coefficientScale_one_le v) (coefficientScale_one_le w)
    (abs_le_coefficientScale w i)).trans (by
      have hi := Finset.single_le_sum (fun j _ => abs_nonneg (v j-w j)) (Finset.mem_univ i)
      linarith [abs_coefficientScale_sub_le v w])

variable {X : Type*} [MetricSpace X]

lemma normalizeCoefficients_boundedLip [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    {f : ι → X → ℝ} (hf : ∀ i, BoundedLip (f i))
    (i : ι) : BoundedLip (fun x => normalizeCoefficients (fun j => f j x) i) := by
  choose K hK using fun j => (hf j).1
  refine ⟨⟨2*∑ j, K j,?_⟩,1,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    calc |normalizeCoefficients (fun j => f j x) i-normalizeCoefficients (fun j => f j y) i| ≤
          2*∑ j, |f j x-f j y| := normalizeCoefficients_dist_le _ _ i
         _ ≤ 2*∑ j, (K j:ℝ)*dist x y := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ =>
            by simpa only [Real.dist_eq] using (hK j).dist_le_mul x y) (by norm_num)
         _ = _ := by push_cast; rw [←Finset.sum_mul]; ring
  · intro x
    exact (Finset.single_le_sum (fun j _ => abs_nonneg (normalizeCoefficients (fun l => f l x) j))
      (Finset.mem_univ i)).trans (normalizeCoefficients_budget _)

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

lemma exists_lip_l1_approx {b : X → ℝ} (hb : Integrable b μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : X → ℝ, BoundedLip f ∧ (∫ x, |f x-b x| ∂μ) < ε := by
  obtain ⟨f,hf⟩ := (lipToL1_dense μ).exists_dist_lt (hb.toL1 b) hε
  refine ⟨f.val,f.property,?_⟩
  rw [dist_comm,dist_eq_norm,L1.norm_eq_integral_norm] at hf
  have he : (fun x => ‖(lipToL1 μ f-hb.toL1 b : Lp ℝ 1 μ) x‖) =ᵐ[μ]
      (fun x => |f.val x-b x|) := by
    filter_upwards [Lp.coeFn_sub (lipToL1 μ f) (hb.toL1 b),hb.coeFn_toL1,
      ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) μ f.val] with x h1 h2 h3
    rw [h1,Pi.sub_apply,h2]
    change ‖(ContinuousMap.toLp 1 μ ℝ f.val : Lp ℝ 1 μ) x-b x‖ = _
    rw [h3,Real.norm_eq_abs]
  simpa only [integral_congr_ae he] using hf

theorem exists_admissible_coefficient_approx (b : ι → X → ℝ)
    (hb : ∀ i, Measurable (b i)) (hbudget : ∀ x, ∑ i, |b i x| ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ι → X → ℝ, (∀ i, BoundedLip (f i)) ∧
      (∀ x, ∑ i, |f i x| ≤ 1) ∧ (∑ i, ∫ x, |f i x-b i x| ∂μ) < ε := by
  let N : ℝ := Fintype.card ι
  have hN : 0 ≤ N := Nat.cast_nonneg _
  let δ := ε/(2*(N+1)^2)
  have hδ : 0 < δ := div_pos hε (by dsimp only [N]; positivity)
  have hbi i : Integrable (b i) μ := Integrable.mono' (integrable_const (1:ℝ)) (hb i).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact (Finset.single_le_sum (fun j _ => abs_nonneg (b j x)) (Finset.mem_univ i)).trans (hbudget x))
  choose a ha happrox using fun i => exists_lip_l1_approx μ (hbi i) hδ
  let f i x := normalizeCoefficients (fun j => a j x) i
  have hfi i : BoundedLip (f i) := normalizeCoefficients_boundedLip ha i
  have hdi i : Integrable (fun x => |a i x-b i x|) μ :=
    ((integrable_boundedLip μ (ha i)).sub (hbi i)).abs
  have hfd i : Integrable (fun x => |f i x-b i x|) μ :=
    ((integrable_boundedLip μ (hfi i)).sub (hbi i)).abs
  refine ⟨f,hfi,fun x => normalizeCoefficients_budget _,?_⟩
  have hbound i : (∫ x, |f i x-b i x| ∂μ) ≤ 2*∑ j, ∫ x, |a j x-b j x| ∂μ := by
    rw [←integral_finsetSum _ (fun j _ => hdi j),←integral_const_mul]
    apply integral_mono (hfd i) ((integrable_finsetSum _ fun j _ => hdi j).const_mul _)
    intro x
    have hh := normalizeCoefficients_dist_le (fun j => a j x) (fun j => b j x) i
    rw [normalizeCoefficients_fixed _ (hbudget x)] at hh
    exact hh
  have hs : (∑ i, ∫ x, |a i x-b i x| ∂μ) ≤ N*δ := by
    calc _ ≤ ∑ i : ι, δ := Finset.sum_le_sum fun i _ => (happrox i).le
         _ = _ := by simp [N]
  calc _ ≤ ∑ i : ι, (2*∑ j, ∫ x, |a j x-b j x| ∂μ) := Finset.sum_le_sum fun i _ => hbound i
       _ = 2*N*(∑ j, ∫ x, |a j x-b j x| ∂μ) := by simp [N]; ring
       _ ≤ 2*N*(N*δ) := mul_le_mul_of_nonneg_left hs (by positivity)
       _ < ε := by
         dsimp only [δ]
         have hden : 0 < 2*(N+1)^2 := by positivity
         rw [show 2*N*(N*(ε/(2*(N+1)^2))) = ε*(N^2/(N+1)^2) by field_simp]
         apply (mul_lt_iff_lt_one_right hε).mpr
         apply (div_lt_one (by positivity : 0 < (N+1)^2)).mpr
         nlinarith

end BorelCoefficients
end CAT0Fillings
end

end OAI
