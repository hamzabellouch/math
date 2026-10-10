import OAI.NumberTheory.DirichletL.Hecke.DetectorFourierSeparation

namespace OAI

namespace SevenEighths.HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

lemma frequency_interval_compl (R : ℝ) :
    (Set.Icc (-R) R)ᶜ = {t : ℝ | R < ‖t‖} := by
  ext t
  simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_ofPred_eq, Real.norm_eq_abs,
    ← abs_le, not_le]

private lemma exists_interval_norm_product (f h : ℝ → ℂ) (hf : Continuous f)
    (hh : Integrable h) (hprod : Integrable (fun u => h u * f u))
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ t : ℝ, ‖t‖ ≤ R ∧
      ‖∫ u : ℝ in Set.Icc (-R) R, h u * f u‖ ≤ (∫ u : ℝ, ‖h u‖) * ‖f t‖ := by
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc (-R) R).Nonempty from ⟨0, by constructor <;> linarith⟩)
    hf.norm.continuousOn
  refine ⟨t, by simpa only [Real.norm_eq_abs, abs_le, Set.mem_Icc] using ht, ?_⟩
  have hb : Integrable (fun u => ‖h u‖ * ‖f t‖) := hh.norm.mul_const _
  calc
    _ ≤ ∫ u : ℝ in Set.Icc (-R) R, ‖h u * f u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in Set.Icc (-R) R, ‖h u‖ * ‖f t‖ := by
      apply setIntegral_mono_on hprod.norm.integrableOn hb.integrableOn measurableSet_Icc
      intro u hu
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hmax hu) (norm_nonneg _)
    _ ≤ ∫ u : ℝ, ‖h u‖ * ‖f t‖ :=
      setIntegral_le_integral hb (Filter.Eventually.of_forall (by intro u; positivity))
    _ = _ := integral_mul_const _ _

theorem exists_interval_frequency {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ)
    (g : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ t : ℝ, ‖t‖ ≤ R ∧
      ‖∫ u : ℝ in Set.Icc (-R) R,
        (𝓕 g) u*phasePolynomial S a x u*phasePolynomial T b y u‖ ≤
        (∫ u : ℝ, ‖(𝓕 g) u‖)*
          ‖phasePolynomial S a x t*phasePolynomial T b y t‖ := by
  have hf : Continuous (fun u => phasePolynomial S a x u * phasePolynomial T b y u) :=
    (phasePolynomial_continuous S a x).mul (phasePolynomial_continuous T b y)
  have hi : Integrable (fun u => (𝓕 g) u *
      (phasePolynomial S a x u * phasePolynomial T b y u)) := by
    simpa only [mul_assoc] using separated_pair_integrable S T a b x y g
  obtain ⟨t, ht, hb⟩ := exists_interval_norm_product
    (fun u => phasePolynomial S a x u * phasePolynomial T b y u)
    (fun u => (𝓕 g) u) hf (𝓕 g).integrable hi R hR
  exact ⟨t, ht, by simpa only [mul_assoc] using hb⟩

private theorem integral_sub_interval_norm_le (f w : ℝ → ℂ) (E R : ℝ)
    (hf : Integrable f) (hw : Integrable w)
    (hbound : ∀ u, ‖f u‖ ≤ E * ‖w u‖) :
    ‖(∫ u : ℝ, f u) - (∫ u : ℝ in Set.Icc (-R) R, f u)‖ ≤
      E * (∫ u : ℝ in {u | R < ‖u‖}, ‖w u‖) := by
  have hsplit := integral_add_compl (s := Set.Icc (-R) R) measurableSet_Icc hf
  have heq : (∫ u : ℝ, f u) - (∫ u : ℝ in Set.Icc (-R) R, f u) =
      ∫ u : ℝ in {u | R < ‖u‖}, f u := by
    rw [← hsplit, frequency_interval_compl]
    abel
  rw [heq]
  have hm : MeasurableSet {u : ℝ | R < ‖u‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  calc
    _ ≤ ∫ u : ℝ in {u | R < ‖u‖}, ‖f u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in {u | R < ‖u‖}, E * ‖w u‖ :=
      setIntegral_mono_on hf.norm.integrableOn (hw.norm.const_mul E).integrableOn hm
        (fun u _ => hbound u)
    _ = _ := integral_const_mul _ _

private theorem separated_pair_norm_le {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ) (z : ℂ) (u : ℝ) :
    ‖z * phasePolynomial S a x u * phasePolynomial T b y u‖ ≤
      ((∑ i ∈ S, ‖a i‖) * (∑ j ∈ T, ‖b j‖)) * ‖z‖ := by
  rw [mul_assoc, norm_mul, norm_mul, mul_comm ‖z‖]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
  exact mul_le_mul (phasePolynomial_norm S a x u) (phasePolynomial_norm T b y u)
    (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

private theorem schwartz_tail_le (g : SchwartzMap ℝ ℂ) (R : ℝ)
    (hR : 0 < R) (N : ℕ) :
    (∫ u : ℝ in {u | R < ‖u‖}, ‖(𝓕 g) u‖) ≤
      (∫ u : ℝ, (1+‖u‖)^N * ‖(𝓕 g) u‖) / R^N := by
  apply (le_div_iff₀ (pow_pos hR N)).mpr
  simpa only [pow_zero, one_mul, Nat.zero_add, mul_comm] using
    schwartz_weighted_tail g 0 N R hR

private theorem separated_pair_tail_of_bound {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ)
    (w : ℝ → ℂ) (R M : ℝ) (N : ℕ)
    (hi : Integrable (fun u => w u * phasePolynomial S a x u * phasePolynomial T b y u))
    (hw : Integrable w) (hbound : (∫ u : ℝ in {u | R < ‖u‖}, ‖w u‖) ≤ M / R^N) :
    ‖(∫ u : ℝ, w u * phasePolynomial S a x u * phasePolynomial T b y u) -
      (∫ u : ℝ in Set.Icc (-R) R,
        w u * phasePolynomial S a x u * phasePolynomial T b y u)‖ ≤
      ((∑ i ∈ S, ‖a i‖) * (∑ j ∈ T, ‖b j‖)) / R^N * M := by
  let E := (∑ i ∈ S, ‖a i‖) * (∑ j ∈ T, ‖b j‖)
  have hE : 0 ≤ E := mul_nonneg
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have htail := integral_sub_interval_norm_le
    (fun u => w u * phasePolynomial S a x u * phasePolynomial T b y u)
    w E R hi hw (fun u => separated_pair_norm_le S T a b x y (w u) u)
  calc
    _ ≤ E * (∫ u : ℝ in {u | R < ‖u‖}, ‖w u‖) := htail
    _ ≤ E * (M / R^N) := mul_le_mul_of_nonneg_left hbound hE
    _ = _ := by rw [div_mul_eq_mul_div, mul_div_assoc]

theorem separated_pair_tail {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ)
    (g : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0 < R) (N : ℕ) :
    ‖(∫ u : ℝ, (𝓕 g) u*phasePolynomial S a x u*phasePolynomial T b y u) -
      (∫ u : ℝ in Set.Icc (-R) R,
        (𝓕 g) u*phasePolynomial S a x u*phasePolynomial T b y u)‖ ≤
      ((∑ i ∈ S, ‖a i‖)*(∑ j ∈ T, ‖b j‖))/R^N *
        (∫ u : ℝ, (1+‖u‖)^N*‖(𝓕 g) u‖) := by
  exact separated_pair_tail_of_bound S T a b x y (fun u : ℝ => (𝓕 g : SchwartzMap ℝ ℂ) u)
    R (∫ u : ℝ, (1+‖u‖)^N * ‖(𝓕 g) u‖) N
    (separated_pair_integrable S T a b x y g) (𝓕 g).integrable
    (schwartz_tail_le g R hR N)

theorem exists_bounded_frequency {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ)
    (g : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0 < R) (N : ℕ) :
    ∃ t : ℝ, ‖t‖ ≤ R ∧
      ‖∑ i ∈ S, ∑ j ∈ T, a i*b j*g (x i+y j)‖ ≤
      ((∑ i ∈ S, ‖a i‖)*(∑ j ∈ T, ‖b j‖))/R^N *
        (∫ u : ℝ, (1+‖u‖)^N*‖(𝓕 g) u‖) +
      (∫ u : ℝ, ‖(𝓕 g) u‖)*
        ‖phasePolynomial S a x t*phasePolynomial T b y t‖ := by
  obtain ⟨t,ht,hb⟩ := exists_interval_frequency S T a b x y g R hR.le
  refine ⟨t,ht,?_⟩
  rw [finite_pair_separation]
  have htail := separated_pair_tail S T a b x y g R hR N
  exact (norm_le_norm_sub_add _ _).trans (add_le_add htail hb)

end
end SevenEighths.HeckeDetectorFourier

end OAI
