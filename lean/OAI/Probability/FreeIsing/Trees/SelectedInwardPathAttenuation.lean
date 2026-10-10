import OAI.Probability.FreeIsing.Trees.InwardCutFields
import OAI.Probability.FreeIsing.Trees.PathSideInwardLocality
import OAI.Probability.FreeIsing.Trees.SelectedPathAttenuation

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367

section Ordered
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable [IsProbabilityMeasure μ]

private lemma integral_prod_le_of_condExp_le_earlier {q : ℝ} (hq : 0 ≤ q)
    (A : ℕ → Ω → ℝ) (m : ℕ → MeasurableSpace Ω) (s : Finset ℕ)
    (hMeas : ∀ i ∈ s, Measurable (A i))
    (hBound : ∀ i ∈ s, ∀ w, 0 ≤ A i w ∧ A i w ≤ 1)
    (hm : ∀ i ∈ s, m i ≤ mΩ)
    (hCE : ∀ i ∈ s, ∀ᵐ w ∂μ, (μ[A i | m i]) w ≤ q)
    (hEarlier : ∀ i ∈ s, ∀ j ∈ s, j < i → Measurable[m i] (A j)) :
    (∫ w, ∏ i ∈ s, A i w ∂μ) ≤ q ^ s.card := by
  classical
  revert hMeas hBound hm hCE hEarlier
  induction s using Finset.induction_on_max with
  | empty =>
      intros
      simp
  | insert i s hmax ih =>
      intro hMeas hBound hm hCE hEarlier
      have his : i ∉ s := by
        intro hi
        exact (lt_irrefl i) (hmax i hi)
      have hiMem : i ∈ insert i s := Finset.mem_insert_self i s
      have hsMem : ∀ j ∈ s, j ∈ insert i s := fun j hj => Finset.mem_insert_of_mem hj
      have htail : (∫ w, ∏ j ∈ s, A j w ∂μ) ≤ q ^ s.card :=
        ih (fun j hj => hMeas j (hsMem j hj))
          (fun j hj => hBound j (hsMem j hj))
          (fun j hj => hm j (hsMem j hj))
          (fun j hj => hCE j (hsMem j hj))
          (fun j hj k hk => hEarlier j (hsMem j hj) k (hsMem k hk))
      have hprodMeas : Measurable[m i] (fun w => ∏ j ∈ s, A j w) := by
        apply Finset.measurable_fun_prod
        intro j hj
        exact hEarlier i hiMem j (hsMem j hj) (hmax j hj)
      have hprodBound : ∀ w, 0 ≤ (∏ j ∈ s, A j w) ∧ (∏ j ∈ s, A j w) ≤ 1 := by
        intro w
        exact ⟨Finset.prod_nonneg (fun j hj => (hBound j (hsMem j hj) w).1),
          Finset.prod_le_one₀ (fun j hj => (hBound j (hsMem j hj) w).1)
            (fun j hj => (hBound j (hsMem j hj) w).2)⟩
      calc
        (∫ w, ∏ j ∈ insert i s, A j w ∂μ) =
            ∫ w, A i w * (∏ j ∈ s, A j w) ∂μ := by simp [Finset.prod_insert, his]
        _ ≤ q * ∫ w, ∏ j ∈ s, A j w ∂μ :=
          integral_mul_le_of_condExp_le (hm i hiMem)
            (integrable_of_measurable_unit_interval (hMeas i hiMem) (hBound i hiMem))
            hprodMeas hprodBound (hCE i hiMem)
        _ ≤ q * q ^ s.card := mul_le_mul_of_nonneg_left htail hq
        _ = q ^ (insert i s).card := by rw [Finset.card_insert_of_notMem his, pow_succ']

end Ordered

namespace PathSideBranches

abbrev inwardCutGaussianField {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (t : ℝ≥0) (v : TreeVertex d) (cut i : ℕ) :=
  cutInwardGaussianField μ t v cut (i + 1)

theorem measurable_inwardCutGaussianField {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0)
    (v : TreeVertex d) (cut i : ℕ) :
    Measurable (inwardCutGaussianField μ t v cut i) :=
  (measurable_cutInwardGaussianField_noisyRegion μ t v cut (i + 1)).mono
    (noisyRegionSigma_le _) le_rfl

private theorem condExp_selected_region_attenuation_le_critical
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hθ0 : 0 < Real.tanh beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (r : TreeVertex d) (hr : r.1 ≠ [])
    (S : Set (TreeVertex d)) (hcone : cone r ⊆ S)
    (hp : parentVertex r ∈ S) :
    let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
    ∀ᵐ z ∂P,
      (P[fun z => responseAttenuation (Real.tanh beta)
        (Real.artanh (selectedPosterior P F
          (Subtype.val : S → TreeVertex d) (parentVertex r) z)) ^ 2 |
        noisyRegionSigma (A := ℝ) (cone r)ᶜ]) z ≤
      1 - ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
        min (Real.sqrt (t : ℝ)) 1 := by
  have h := hμ.condExp_selected_cone_field_attenuation_le_critical
    hbeta hθ0 hcritical ht r hr (S \ cone r)
    (fun _ hu => hu.2) ⟨hp, parent_not_mem_cone r hr⟩
  have heq : (S \ cone r) ∪ cone r = S := Set.sdiff_union_of_subset hcone
  dsimp only at h ⊢
  rw [heq] at h
  exact h

theorem inwardCutGaussianField_attenuation_mem_Icc
    {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0)
    (v : TreeVertex d) (cut i : ℕ) {theta : ℝ} (hθ : theta ^ 2 ≤ 1)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :
    responseAttenuation theta (inwardCutGaussianField μ t v cut i z) ^ 2 ∈
      Set.Icc (0 : ℝ) 1 := by
  have hp := responseAttenuation_pos hθ (inwardCutGaussianField μ t v cut i z)
  have hl := responseAttenuation_le_one hθ (inwardCutGaussianField μ t v cut i z)
  exact ⟨sq_nonneg _, by nlinarith⟩

theorem measurable_inwardCutGaussianField_cutCone
    {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0)
    (v : TreeVertex d) (cut i : ℕ) :
    Measurable[noisyRegionSigma (A := ℝ) (cone (ConnectedHull.takeVertex v cut))]
      (inwardCutGaussianField μ t v cut i) := by
  exact measurable_cutInwardGaussianField_noisyRegion μ t v cut (i + 1)

private theorem integral_inwardCutGaussianField_attenuation_of_geometry
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (v : TreeVertex d) (cut : ℕ)
    (s : Finset ℕ) (hs : ∀ i ∈ s, i < v.1.length)
    (hside : ∀ i : Fin v.1.length, i.1 ∈ s →
      cone (sideVertex hd v i) ⊆
        cone (ConnectedHull.takeVertex v cut) \ cone (ConnectedHull.takeVertex v (i.1 + 2)))
    (hown : ∀ i : Fin v.1.length, i.1 ∈ s →
      ConnectedHull.takeVertex v (i.1 + 1) ∈
        cone (ConnectedHull.takeVertex v cut) \ cone (ConnectedHull.takeVertex v (i.1 + 2)))
    (hprev : ∀ i : Fin v.1.length, i.1 ∈ s → ∀ j ∈ s, j < i.1 →
      cone (ConnectedHull.takeVertex v cut) \ cone (ConnectedHull.takeVertex v (j + 2)) ⊆
        (cone (sideVertex hd v i))ᶜ) :
    (∫ z, ∏ i ∈ s,
       responseAttenuation (Real.tanh beta) (inwardCutGaussianField μ t v cut i z) ^ 2
       ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
      Real.exp (-(ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
        min (Real.sqrt (t : ℝ)) 1) * (s.card : ℝ)) := by
  classical
  let := hμ.isProbabilityMeasure
  let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
  let A : ℕ → ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) → ℝ :=
    fun i z => responseAttenuation (Real.tanh beta) (inwardCutGaussianField μ t v cut i z) ^ 2
  let m : ℕ → MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :=
    fun i => if hi : i < v.1.length then
      noisyRegionSigma (A := ℝ) (cone (sideVertex hd v ⟨i, hi⟩))ᶜ else ⊥
  let δ := ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
    min (Real.sqrt (t : ℝ)) 1
  have hθ0 : 0 < Real.tanh beta := by
    have hn := tanh_nonneg_of_beta_nonneg hbeta
    by_contra h
    have hz : Real.tanh beta = 0 := le_antisymm (not_lt.mp h) hn
    simp [hz] at hcritical
  have hθ1 := Real.tanh_lt_one beta
  have hθ : Real.tanh beta ^ 2 ≤ 1 := by nlinarith
  have hc := (ComponentSignalAttenuation.lossCoefficient_pos hθ0 hθ1).le
  have hc1 := ComponentSignalAttenuation.lossCoefficient_le_half (Real.tanh beta)
  have hδ : δ ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left (min_le_right (Real.sqrt (t : ℝ)) (1 : ℝ)) hc
    dsimp [δ]
    nlinarith
  have hresp : Measurable (fun z : ℝ => responseAttenuation (Real.tanh beta) z ^ 2) :=
    (continuous_responseAttenuation hθ).measurable.pow_const 2
  have hMeas (i : ℕ) : Measurable (A i) :=
    hresp.comp (measurable_inwardCutGaussianField μ t v cut i)
  have hBound (i : ℕ) (z) : 0 ≤ A i z ∧ A i z ≤ 1 :=
    inwardCutGaussianField_attenuation_mem_Icc μ t v cut i hθ z
  have hm (i : ℕ) (hi : i ∈ s) : m i ≤ (inferInstance : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ))) := by
    have hi' := hs i hi
    simpa only [m, dite_eq_left hi'] using
      noisyRegionSigma_le (A := ℝ) (cone (sideVertex hd v ⟨i, hi'⟩))ᶜ
  have hcond (i : ℕ) (hi : i ∈ s) :
      ∀ᵐ z ∂P, (P[A i | m i]) z ≤ 1 - δ := by
    have hi' := hs i hi
    have hr : (sideVertex hd v ⟨i, hi'⟩).1 ≠ [] := by
      intro he
      have hl := sideVertex_length hd v ⟨i, hi'⟩
      rw [he] at hl
      simp at hl
    have hp : parentVertex (sideVertex hd v ⟨i, hi'⟩) ∈
        cone (ConnectedHull.takeVertex v cut) \ cone (ConnectedHull.takeVertex v (i + 2)) := by
      rw [parent_sideVertex]
      exact hown ⟨i, hi'⟩ hi
    have hh := condExp_selected_region_attenuation_le_critical hμ hbeta hθ0 hcritical ht
      (sideVertex hd v ⟨i, hi'⟩) hr
      (cone (ConnectedHull.takeVertex v cut) \ cone (ConnectedHull.takeVertex v (i + 2)))
      (hside ⟨i, hi'⟩ hi) hp
    simpa only [P, A, m, dite_eq_left hi', δ, parent_sideVertex, inwardCutGaussianField, cutInwardGaussianField, regionGaussianField, Nat.add_assoc] using hh
  have hEarlier (i : ℕ) (hi : i ∈ s) (j : ℕ) (hj : j ∈ s) (hji : j < i) :
      Measurable[m i] (A j) := by
    have hi' := hs i hi
    have hfield := (measurable_regionGaussianField_noisyRegion μ t
      (cone (ConnectedHull.takeVertex v cut) \ cone (ConnectedHull.takeVertex v (j + 2)))
      (ConnectedHull.takeVertex v (j + 1))).mono
        (noisyRegionSigma_mono (hprev ⟨i, hi'⟩ hi j hj hji)) le_rfl
    have hmi : m i = noisyRegionSigma (A := ℝ)
        (cone (sideVertex hd v ⟨i, hi'⟩))ᶜ := by simp only [m, dite_eq_left hi']
    have hh : Measurable[noisyRegionSigma (A := ℝ)
        (cone (sideVertex hd v ⟨i, hi'⟩))ᶜ] (A j) := hresp.comp hfield
    exact hmi.symm ▸ hh
  have hprod := integral_prod_le_of_condExp_le_earlier (μ := P) (sub_nonneg.mpr hδ)
    A m s (fun i _ => hMeas i) (fun i _ => hBound i) hm hcond hEarlier
  have hexp : (1 - δ) ^ s.card ≤ Real.exp (-δ * (s.card : ℝ)) := by
    calc
      _ ≤ (Real.exp (-δ)) ^ s.card := by
        apply pow_le_pow_left₀ (sub_nonneg.mpr hδ)
        have hh := Real.add_one_le_exp (-δ)
        linarith
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  exact hprod.trans hexp

theorem integral_inwardCutGaussianField_subset_attenuation_le_exp_critical
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (v : TreeVertex d) (cut : ℕ)
    (s : Finset ℕ) (hs : ∀ i ∈ s, cut ≤ i + 1 ∧ i + 1 < v.1.length) :
    (∫ z, ∏ i ∈ s,
       responseAttenuation (Real.tanh beta) (cutInwardGaussianField μ t v cut (i + 1) z) ^ 2
       ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
      Real.exp (-(ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
        min (Real.sqrt (t : ℝ)) 1) * (s.card : ℝ)) := by
  apply integral_inwardCutGaussianField_attenuation_of_geometry hμ hbeta hd hcritical ht v cut s
    (fun i hi => (Nat.lt_succ_self i).trans (hs i hi).2)
  · intro i hi
    exact sideCone_subset_inward hd v (ConnectedHull.takeVertex v cut) i
      (List.take_prefix_take_left (hs i.1 hi).1) (hs i.1 hi).2
  · intro i hi
    exact (target_mem_inward_without_side hd v (ConnectedHull.takeVertex v cut) i
      (List.take_prefix_take_left (hs i.1 hi).1) (hs i.1 hi).2).1
  · intro i hi j hj hji
    exact earlier_inward_subset_side_complement hd v (ConnectedHull.takeVertex v cut)
      (j := ⟨j, (Nat.lt_succ_self j).trans (hs j hj).2⟩) hji

theorem integral_cutInwardGaussianField_subset_attenuation_le_exp_critical
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (v : TreeVertex d) (cut : ℕ) (hcut : 0 < cut)
    (s : Finset ℕ) (hs : ∀ i ∈ s, cut ≤ i ∧ i < v.1.length) :
    (∫ z, ∏ i ∈ s,
       responseAttenuation (Real.tanh beta) (cutInwardGaussianField μ t v cut i z) ^ 2
       ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
      Real.exp (-(ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
        min (Real.sqrt (t : ℝ)) 1) * (s.card : ℝ)) := by
  classical
  have hinj : Set.InjOn (fun i : ℕ => i - 1) s := by
    intro i hi j hj hij
    change i - 1 = j - 1 at hij
    have := (hs i hi).1
    have := (hs j hj).1
    omega
  have h := integral_inwardCutGaussianField_subset_attenuation_le_exp_critical
    hμ hbeta hd hcritical ht v cut (s.image (fun i => i - 1)) (by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      have hj' := hs j hj
      constructor <;> omega)
  have hcard : (s.image (fun i => i - 1)).card = s.card := Finset.card_image_of_injOn hinj
  have hprod (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :
      (∏ i ∈ s.image (fun i => i - 1), responseAttenuation (Real.tanh beta)
        (cutInwardGaussianField μ t v cut (i + 1) z) ^ 2) =
      ∏ i ∈ s, responseAttenuation (Real.tanh beta)
        (cutInwardGaussianField μ t v cut i z) ^ 2 := by
    rw [Finset.prod_image hinj]
    apply Finset.prod_congr rfl
    intro i hi
    have hi' := (hs i hi).1
    rw [show i - 1 + 1 = i by omega]
  simpa only [hprod, hcard] using h

theorem integral_cutInwardGaussianField_continuation_attenuation_le_exp_critical
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (v : TreeVertex d) (k L : ℕ)
    (hlen : k + L + 1 ≤ v.1.length) :
    (∫ z, ∏ j ∈ Finset.range L,
       responseAttenuation (Real.tanh beta)
         (cutInwardGaussianField μ t v (k + 1) (k + j + 1) z) ^ 2
       ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
      Real.exp (-(ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
        min (Real.sqrt (t : ℝ)) 1) * (L : ℝ)) := by
  have h := integral_inwardCutGaussianField_subset_attenuation_le_exp_critical
    hμ hbeta hd hcritical ht v (k + 1) (Finset.Ico k (k + L)) (by
      intro i hi
      have hi' := Finset.mem_Ico.mp hi
      constructor <;> omega)
  simpa only [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel_left,
    Nat.card_Ico] using h

end PathSideBranches
end Problem367

end

end OAI
