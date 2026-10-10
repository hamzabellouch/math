import OAI.Probability.InvariantIsing.Arrays.QuantileProductPath

namespace OAI

/-! The synchronized GG triple product equals the manuscript product path. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

theorem gg_quantile_triple_product {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → RealArray) (hR : Measurable R)
    (hgg : HasEntryGhirlandaGuerra R μ)
    (hsym : ∀ᵐ x ∂μ, ∀ i j, R x i j = R x j i)
    (hu : ∀ᵐ x ∂μ, IsUltrametricArray (R x))
    (p : OverlapPath) (hl : pathMeasure.map p = scalarOverlapLaw μ R)
    (a b Φ : ℝ → ℝ) (ha : Measurable a) (hb : Measurable b) (hΦ : Measurable Φ)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (haB : ∀ x, |a x| ≤ A) (hbB : ∀ x, |b x| ≤ B) (hΦB : ∀ x, |Φ x| ≤ C) :
    2 * (∫ x, Φ (R x 0 1) * (a (R x 0 2) * b (R x 1 2)) ∂μ) =
      ∫ s, Φ (p s) * ((∫ u, replicaProductFirst a b (p s) (p u) +
        replicaProductSecond a b (p s) (p u) ∂pathMeasure) + a (p s) * b (p s)) ∂pathMeasure := by
  let ζ := scalarOverlapLaw μ R
  have hmR : Measurable (fun x => R x 0 1) := by fun_prop
  let : IsProbabilityMeasure ζ :=
    (Measure.isProbabilityMeasure_map_iff hmR.aemeasurable).mpr inferInstance
  let F : ℝ × ℝ → ℝ := fun z => Φ z.1 * replicaProductFirst a b z.1 z.2
  let G : ℝ × ℝ → ℝ := fun z => Φ z.1 * replicaProductSecond a b z.1 z.2
  let D : ℝ → ℝ := fun x => Φ x * (a x * b x)
  have hFm : Measurable F := (hΦ.comp measurable_fst).mul (measurable_replicaProductFirst ha hb)
  have hGm : Measurable G := (hΦ.comp measurable_fst).mul (measurable_replicaProductSecond ha hb)
  have hDm : Measurable D := hΦ.mul (ha.mul hb)
  have hFb (z : ℝ × ℝ) : |F z| ≤ C * (A * B) := by
    change |Φ z.1 * replicaProductFirst a b z.1 z.2| ≤ _
    rw [abs_mul]
    exact mul_le_mul (hΦB _) (replicaProductFirst_abs_le hA haB hbB _ _) (abs_nonneg _) hC
  have hGb (z : ℝ × ℝ) : |G z| ≤ C * (2 * (A * B)) := by
    change |Φ z.1 * replicaProductSecond a b z.1 z.2| ≤ _
    rw [abs_mul]
    exact mul_le_mul (hΦB _) (replicaProductSecond_abs_le hA hB haB hbB _ _) (abs_nonneg _) hC
  have hDb (x : ℝ) : |D x| ≤ C * (A * B) := by
    change |Φ x * (a x * b x)| ≤ _
    rw [abs_mul, abs_mul]
    exact mul_le_mul (hΦB x) (mul_le_mul (haB x) (hbB x) (abs_nonneg _) hA)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hC
  let Fp : ℝ × ℝ → ℝ := fun z => F (p z.1,p z.2)
  let Gp : ℝ × ℝ → ℝ := fun z => G (p z.1,p z.2)
  have hFpm : Measurable Fp := hFm.comp
    ((p.measurable.comp measurable_fst).prodMk (p.measurable.comp measurable_snd))
  have hGpm : Measurable Gp := hGm.comp
    ((p.measurable.comp measurable_fst).prodMk (p.measurable.comp measurable_snd))
  have hiF : Integrable (fun s => ∫ u, Fp (s,u) ∂pathMeasure) pathMeasure := by
    apply integrable_of_measurable_abs_le
      hFpm.stronglyMeasurable.integral_prod_right'.measurable
    intro s
    exact abs_integral_le_const_of_bound (hFpm.comp (measurable_const.prodMk measurable_id))
      (fun u => hFb _)
  have hiG : Integrable (fun s => ∫ u, Gp (s,u) ∂pathMeasure) pathMeasure := by
    apply integrable_of_measurable_abs_le
      hGpm.stronglyMeasurable.integral_prod_right'.measurable
    intro s
    exact abs_integral_le_const_of_bound (hGpm.comp (measurable_const.prodMk measurable_id))
      (fun u => hGb _)
  have hiD : Integrable (fun s => D (p s)) pathMeasure :=
    integrable_of_measurable_abs_le (hDm.comp p.measurable) (fun s => hDb _)
  have he := gg_ultrametric_product_integral μ R hR hgg hsym hu a b Φ ha hb hΦ
    hA hB hC haB hbB hΦB
  have hfirst := integral_pair_quantile_map ζ p hl F hFm
  have hsecond := integral_pair_quantile_map ζ p hl G hGm
  have hdiag : (∫ x, D x ∂ζ) = ∫ s, D (p s) ∂pathMeasure := by
    change (∫ x, D x ∂scalarOverlapLaw μ R) = _
    rw [← hl]
    exact integral_map_of_stronglyMeasurable p.measurable hDm.stronglyMeasurable
  change 2 * (∫ x, Φ (R x 0 1) * (a (R x 0 2) * b (R x 1 2)) ∂μ) =
    (∫ x, ∫ y, F (x,y) ∂ζ ∂ζ) + (∫ x, ∫ y, G (x,y) ∂ζ ∂ζ) + ∫ x, D x ∂ζ at he
  rw [hfirst, hsecond, hdiag] at he
  rw [he, ← integral_add hiF hiG]
  have hadd := integral_add (hiF.add hiG) hiD
  simp only [Pi.add_apply] at hadd
  rw [← hadd]
  apply integral_congr_ae
  exact ae_of_all _ fun s => by
    have hfi : Integrable (fun u => replicaProductFirst a b (p s) (p u)) pathMeasure :=
      integrable_of_measurable_abs_le
        ((measurable_replicaProductFirst ha hb).comp (measurable_const.prodMk p.measurable))
        (fun u => replicaProductFirst_abs_le hA haB hbB _ _)
    have hgi : Integrable (fun u => replicaProductSecond a b (p s) (p u)) pathMeasure :=
      integrable_of_measurable_abs_le
        ((measurable_replicaProductSecond ha hb).comp (measurable_const.prodMk p.measurable))
        (fun u => replicaProductSecond_abs_le hA hB haB hbB _ _)
    change (∫ u, Φ (p s) * replicaProductFirst a b (p s) (p u) ∂pathMeasure) +
      (∫ u, Φ (p s) * replicaProductSecond a b (p s) (p u) ∂pathMeasure) + D (p s) = _
    dsimp only [D]
    rw [integral_const_mul, integral_const_mul, integral_add hfi hgi]
    ring

/-- The off-diagonal replica product has exactly the path used in the
rotation identities, including its contributions at overlap atoms. -/
theorem gg_replicaProductPath_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → RealArray) (hR : Measurable R)
    (hgg : HasEntryGhirlandaGuerra R μ)
    (hsym : ∀ᵐ x ∂μ, ∀ i j, R x i j = R x j i)
    (hu : ∀ᵐ x ∂μ, IsUltrametricArray (R x))
    (p : OverlapPath) (hl : pathMeasure.map p = scalarOverlapLaw μ R)
    (a b Φ : ℝ → ℝ) (ha : Measurable a) (hb : Measurable b) (hΦ : Measurable Φ)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (haB : ∀ x, |a x| ≤ A) (hbB : ∀ x, |b x| ≤ B) (hΦB : ∀ x, |Φ x| ≤ C)
    (da db : ℝ) :
    (∫ x, Φ (R x 0 1) * (da * b (R x 0 1) + a (R x 0 1) * db -
      2 * (a (R x 0 2) * b (R x 1 2))) ∂μ) =
      ∫ s, Φ (p s) * replicaProductPath da (fun u => a (p u)) db
        (fun u => b (p u)) s ∂pathMeasure := by
  let L : ℝ → ℝ := fun r => Φ r * (da * b r + a r * db)
  let T : Ω → ℝ := fun x => Φ (R x 0 1) * (a (R x 0 2) * b (R x 1 2))
  let K : ℝ → ℝ := fun s => Φ (p s) *
    ((∫ u, replicaProductFirst a b (p s) (p u) +
      replicaProductSecond a b (p s) (p u) ∂pathMeasure) + a (p s) * b (p s))
  have hmR (i j : ℕ) : Measurable (fun x => R x i j) := by fun_prop
  have hLm : Measurable L := hΦ.mul ((hb.const_mul da).add (ha.mul_const db))
  have hLb (r : ℝ) : |L r| ≤ C * (|da| * B + A * |db|) := by
    dsimp only [L]
    rw [abs_mul]
    apply mul_le_mul (hΦB r) _ (abs_nonneg _) hC
    exact (abs_add_le _ _).trans (add_le_add
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hbB r) (abs_nonneg da))
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (haB r) (abs_nonneg db)))
  have hTi : Integrable T μ := by
    apply integrable_of_measurable_abs_le
      ((hΦ.comp (hmR 0 1)).mul ((ha.comp (hmR 0 2)).mul (hb.comp (hmR 1 2))))
    intro x
    change |Φ (R x 0 1) * (a (R x 0 2) * b (R x 1 2))| ≤ C * (A * B)
    rw [abs_mul, abs_mul]
    exact mul_le_mul (hΦB _) (mul_le_mul (haB _) (hbB _) (abs_nonneg _) hA)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hC
  have hLi : Integrable (fun x => L (R x 0 1)) μ :=
    integrable_of_measurable_abs_le (hLm.comp (hmR 0 1)) (fun x => hLb _)
  have hLpi : Integrable (fun s => L (p s)) pathMeasure :=
    integrable_of_measurable_abs_le (hLm.comp p.measurable) (fun s => hLb _)
  let J : ℝ × ℝ → ℝ := fun z => replicaProductFirst a b (p z.1) (p z.2) +
    replicaProductSecond a b (p z.1) (p z.2)
  have hJm : Measurable J :=
    ((measurable_replicaProductFirst ha hb).add (measurable_replicaProductSecond ha hb)).comp
      ((p.measurable.comp measurable_fst).prodMk (p.measurable.comp measurable_snd))
  have hJb (z : ℝ × ℝ) : |J z| ≤ 3 * (A * B) := by
    exact (abs_add_le _ _).trans ((add_le_add
      (replicaProductFirst_abs_le hA haB hbB _ _)
      (replicaProductSecond_abs_le hA hB haB hbB _ _)).trans_eq (by ring))
  have hKi : Integrable K pathMeasure := by
    apply integrable_of_measurable_abs_le
      ((hΦ.comp p.measurable).mul
        (hJm.stronglyMeasurable.integral_prod_right'.measurable.add
          ((ha.comp p.measurable).mul (hb.comp p.measurable))))
    intro s
    change |Φ (p s) * ((∫ u, J (s,u) ∂pathMeasure) + a (p s) * b (p s))| ≤ C * (4 * (A * B))
    rw [abs_mul]
    apply mul_le_mul (hΦB _) _ (abs_nonneg _) hC
    have hj := abs_integral_le_const_of_bound (μ := pathMeasure)
      (hJm.comp (measurable_const.prodMk measurable_id)) (fun u => hJb (s,u))
    have hab : |a (p s) * b (p s)| ≤ A * B := by
      rw [abs_mul]
      exact mul_le_mul (haB _) (hbB _) (abs_nonneg _) hA
    exact (abs_add_le _ _).trans ((add_le_add hj hab).trans_eq (by ring))
  have hLmap : (∫ x, L (R x 0 1) ∂μ) = ∫ s, L (p s) ∂pathMeasure := by
    calc
      _ = ∫ r, L r ∂scalarOverlapLaw μ R :=
        (integral_map_of_stronglyMeasurable (hmR 0 1) hLm.stronglyMeasurable).symm
      _ = _ := by
        rw [← hl]
        exact integral_map_of_stronglyMeasurable p.measurable hLm.stronglyMeasurable
  have ht := gg_quantile_triple_product μ R hR hgg hsym hu p hl a b Φ ha hb hΦ
    hA hB hC haB hbB hΦB
  change 2 * (∫ x, T x ∂μ) = ∫ s, K s ∂pathMeasure at ht
  calc
    _ = ∫ x, L (R x 0 1) - 2 * T x ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only [L, T]; ring
    _ = (∫ x, L (R x 0 1) ∂μ) - 2 * ∫ x, T x ∂μ := by
      rw [integral_sub hLi (hTi.const_mul 2), integral_const_mul]
    _ = (∫ s, L (p s) ∂pathMeasure) - ∫ s, K s ∂pathMeasure := by rw [hLmap, ht]
    _ = ∫ s, L (p s) - K s ∂pathMeasure := (integral_sub hLpi hKi).symm
    _ = _ := by
      apply integral_congr_ae
      have hunit : ∀ᵐ s ∂pathMeasure, s ∈ Ioo (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioo
      filter_upwards [hunit] with s hs
      rw [replicaProductPath_eq_quantile_kernel p a b ha hb hA haB hbB da db
        ⟨hs.1.le, hs.2.le⟩]
      dsimp only [L, K]
      ring

end InvariantIsing

end

end OAI
