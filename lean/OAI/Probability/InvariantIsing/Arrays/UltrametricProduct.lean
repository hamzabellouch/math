import OAI.Probability.InvariantIsing.Arrays.ReplicaPairLaw

namespace OAI

/-! An atom-preserving decomposition for synchronized replica products. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators ENNReal

namespace InvariantIsing

def replicaProductFirst (a b : ℝ → ℝ) (x y : ℝ) : ℝ :=
  if y < x then a y * b y else a y * b x

def replicaProductSecond (a b : ℝ → ℝ) (x z : ℝ) : ℝ :=
  if x < z then a x * (b z - b x) else 0

lemma ultrametric_product_decomposition (a b : ℝ → ℝ) {x y z : ℝ}
    (hx : min y z ≤ x) (hy : min x z ≤ y) (hz : min x y ≤ z) :
    a y * b z = replicaProductFirst a b x y + replicaProductSecond a b x z := by
  by_cases hyx : y < x
  · have hzy : z = y := by
      apply le_antisymm
      · by_contra! h
        exact (lt_min hyx h).not_ge hy
      · simpa only [min_eq_right hyx.le] using hz
    rw [hzy]
    simp [replicaProductFirst, replicaProductSecond, hyx, not_lt_of_ge hyx.le]
  · by_cases hxy : x < y
    · have hzx : z = x := by
        apply le_antisymm
        · by_contra! h
          exact (lt_min hxy h).not_ge hx
        · simpa only [min_eq_left hxy.le] using hz
      rw [hzx]
      simp [replicaProductFirst, replicaProductSecond, hyx]
    · have hy' : y = x := le_antisymm (le_of_not_gt hxy) (le_of_not_gt hyx)
      subst y
      have hxz : x ≤ z := by simpa using hz
      rcases hxz.eq_or_lt with h | h
      · rw [← h]
        simp [replicaProductFirst, replicaProductSecond]
      · simp only [replicaProductFirst, replicaProductSecond, lt_self_iff_false, ↓reduceIte, h]
        ring

lemma measurable_replicaProductFirst {a b : ℝ → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun p : ℝ × ℝ => replicaProductFirst a b p.1 p.2) := by
  exact Measurable.ite (measurableSet_lt measurable_snd measurable_fst)
    ((ha.comp measurable_snd).mul (hb.comp measurable_snd))
    ((ha.comp measurable_snd).mul (hb.comp measurable_fst))

lemma measurable_replicaProductSecond {a b : ℝ → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun p : ℝ × ℝ => replicaProductSecond a b p.1 p.2) := by
  exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
    ((ha.comp measurable_fst).mul ((hb.comp measurable_snd).sub (hb.comp measurable_fst)))
    measurable_const

lemma replicaProductFirst_abs_le {a b : ℝ → ℝ} {A B : ℝ}
    (hA : 0 ≤ A) (ha : ∀ x, |a x| ≤ A) (hb : ∀ x, |b x| ≤ B) (x y : ℝ) :
    |replicaProductFirst a b x y| ≤ A * B := by
  unfold replicaProductFirst
  split_ifs <;> rw [abs_mul] <;> exact mul_le_mul (ha _) (hb _) (abs_nonneg _) hA

lemma replicaProductSecond_abs_le {a b : ℝ → ℝ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : ∀ x, |a x| ≤ A) (hb : ∀ x, |b x| ≤ B) (x y : ℝ) :
    |replicaProductSecond a b x y| ≤ 2 * (A * B) := by
  unfold replicaProductSecond
  split_ifs
  · rw [abs_mul]
    have hd : |b y - b x| ≤ B + B := (abs_sub _ _).trans (add_le_add (hb y) (hb x))
    exact (mul_le_mul (ha x) hd (abs_nonneg _) hA).trans_eq (by ring)
  · simp only [abs_zero]
    positivity

/-- The full synchronized triple product is reduced to its two-link GG
marginals. Strict comparisons retain the diagonal contribution at atoms. -/
theorem gg_ultrametric_product_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → RealArray) (hR : Measurable R)
    (hgg : HasEntryGhirlandaGuerra R μ)
    (hs : ∀ᵐ x ∂μ, ∀ i j, R x i j = R x j i)
    (hu : ∀ᵐ x ∂μ, IsUltrametricArray (R x))
    (a b Φ : ℝ → ℝ) (ha : Measurable a) (hb : Measurable b) (hΦ : Measurable Φ)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (haB : ∀ x, |a x| ≤ A) (hbB : ∀ x, |b x| ≤ B) (hΦB : ∀ x, |Φ x| ≤ C) :
    2 * (∫ x, Φ (R x 0 1) * (a (R x 0 2) * b (R x 1 2)) ∂μ) =
      (∫ x, ∫ y, Φ x * replicaProductFirst a b x y ∂scalarOverlapLaw μ R ∂scalarOverlapLaw μ R) +
      (∫ x, ∫ y, Φ x * replicaProductSecond a b x y ∂scalarOverlapLaw μ R ∂scalarOverlapLaw μ R) +
      ∫ x, Φ x * (a x * b x) ∂scalarOverlapLaw μ R := by
  let F : ℝ × ℝ → ℝ := fun p => Φ p.1 * replicaProductFirst a b p.1 p.2
  let G : ℝ × ℝ → ℝ := fun p => Φ p.1 * replicaProductSecond a b p.1 p.2
  have hFm : Measurable F := (hΦ.comp measurable_fst).mul (measurable_replicaProductFirst ha hb)
  have hGm : Measurable G := (hΦ.comp measurable_fst).mul (measurable_replicaProductSecond ha hb)
  have hFb (p : ℝ × ℝ) : |F p| ≤ C * (A * B) := by
    change |Φ p.1 * replicaProductFirst a b p.1 p.2| ≤ _
    rw [abs_mul]
    exact mul_le_mul (hΦB p.1) (replicaProductFirst_abs_le hA haB hbB p.1 p.2) (abs_nonneg _) hC
  have hGb (p : ℝ × ℝ) : |G p| ≤ C * (2 * (A * B)) := by
    change |Φ p.1 * replicaProductSecond a b p.1 p.2| ≤ _
    rw [abs_mul]
    exact mul_le_mul (hΦB p.1) (replicaProductSecond_abs_le hA hB haB hbB p.1 p.2) (abs_nonneg _) hC
  have hm (i j : ℕ) : Measurable (fun x => R x i j) := by fun_prop
  have hiF : Integrable (fun x => F (R x 0 1, R x 0 2)) μ :=
    integrable_of_measurable_abs_le (hFm.comp ((hm 0 1).prodMk (hm 0 2))) (fun x => hFb _)
  have hiG : Integrable (fun x => G (R x 0 1, R x 1 2)) μ :=
    integrable_of_measurable_abs_le (hGm.comp ((hm 0 1).prodMk (hm 1 2))) (fun x => hGb _)
  have hdecomp : (fun x => Φ (R x 0 1) * (a (R x 0 2) * b (R x 1 2))) =ᵐ[μ]
      fun x => F (R x 0 1, R x 0 2) + G (R x 0 1, R x 1 2) := by
    filter_upwards [hs, hu] with x hsym hultra
    have hx := hultra 0 1 2
    have hy := hultra 0 2 1
    have hz := hultra 1 2 0
    rw [hsym 2 1] at hy
    rw [hsym 1 0, hsym 2 0] at hz
    rw [ultrametric_product_decomposition a b hx hy hz, mul_add]
  have heF := gg_two_link_integral μ R hR hgg hs 0 F hFm hFb
  have heG := gg_two_link_integral μ R hR hgg hs 1 G hGm hGb
  have hdiagF (x : ℝ) : F (x,x) = Φ x * (a x * b x) := by simp [F, replicaProductFirst]
  have hdiagG (x : ℝ) : G (x,x) = 0 := by simp [G, replicaProductSecond]
  simp_rw [hdiagF] at heF
  simp_rw [hdiagG, integral_zero] at heG
  rw [integral_congr_ae hdecomp, integral_add hiF hiG]
  change 2 * ((∫ x, F (R x 0 1, R x 0 2) ∂μ) + ∫ x, G (R x 0 1, R x 1 2) ∂μ) = _
  dsimp only [F, G] at heF heG ⊢
  simp only [Fin.val_zero, Fin.val_one] at heF heG
  linarith

end InvariantIsing

end

end OAI
