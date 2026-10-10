import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

abbrev Site (d : ℕ) := Fin d → ℤ
abbrev Step (d : ℕ) := Fin d × Bool

def stepVector {d : ℕ} (e : Step d) : Site d :=
  fun i => if i = e.1 then (if e.2 then 1 else -1) else 0

def Row (d : ℕ) :=
  {p : Step d → ℝ // (∀ e, p e ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ e, p e = 1}

instance (d : ℕ) : MeasurableSpace (Row d) := inferInstanceAs
  (MeasurableSpace {p : Step d → ℝ //
    (∀ e, p e ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ e, p e = 1})

abbrev Environment (d : ℕ) := Site d → Row d
abbrev Path (d : ℕ) := ℕ → Site d
abbrev State (d : ℕ) := Environment d × Site d

def StrictEllipticity {d : ℕ} (μ : Measure (Row d)) : Prop :=
  ∀ᵐ p ∂μ, ∀ e, 0 < p.val e

noncomputable def environmentLaw {d : ℕ} (μ : Measure (Row d))
    [IsProbabilityMeasure μ] : Measure (Environment d) :=
  Measure.infinitePi (fun _ => μ)

noncomputable def transition (d : ℕ) : Kernel (State d) (State d) where
  toFun s := ∑ e : Step d,
    ENNReal.ofReal ((s.1 s.2).val e) • Measure.dirac (s.1, s.2 + stepVector e)
  measurable' := by
    apply measurable_from_prod_countable_left
    intro x
    apply Finset.measurable_sum
    intro e he
    apply Measure.measurable_of_measurable_coe
    intro t ht
    simp only [Measure.smul_apply, smul_eq_mul]
    apply Measurable.mul
    · exact (measurable_pi_apply e |>.comp
        (measurable_subtype_coe.comp (measurable_pi_apply x))).ennreal_ofReal
    · exact (Measure.measurable_coe ht).comp
        (Measure.measurable_dirac.comp (measurable_id.prodMk measurable_const))

instance (d : ℕ) : IsMarkovKernel (transition d) where
  isProbabilityMeasure s := by
    constructor
    change (∑ e : Step d,
      ENNReal.ofReal ((s.1 s.2).val e) •
        Measure.dirac (s.1, s.2 + stepVector e)) Set.univ = 1
    simp only [Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [(s.1 s.2).property.2, ENNReal.ofReal_one]
    · intro e he
      exact ((s.1 s.2).property.1 e).1

noncomputable def historyKernel (d n : ℕ) :
    Kernel ((i : Finset.Iic n) → State d) (State d) :=
  (transition d).comap (fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply _)

instance (d n : ℕ) : IsMarkovKernel (historyKernel d n) := by
  unfold historyKernel
  infer_instance

noncomputable def initialLaw {d : ℕ} (μ : Measure (Row d))
    [IsProbabilityMeasure μ] (x : Site d) : Measure (State d) :=
  (environmentLaw μ).map (fun ω => (ω, x))

noncomputable def annealed {d : ℕ} (μ : Measure (Row d))
    [IsProbabilityMeasure μ] (x : Site d) : Measure (Path d) :=
  (Kernel.trajMeasure (X := fun _ => State d) (initialLaw μ x) (historyKernel d)).map
    (fun z n => (z n).2)

def escape {d : ℕ} (ℓ : Fin d → ℝ) : Set (Path d) :=
  {X | Tendsto (fun n => ∑ i, (X n i : ℝ) * ℓ i) atTop atTop}

lemma probabilityMeasure_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α → β}
    (hf : AEMeasurable f μ) : IsProbabilityMeasure (μ.map f) :=
  (Measure.isProbabilityMeasure_map_iff hf).2 inferInstance

instance {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (environmentLaw μ) := by
  unfold environmentLaw
  infer_instance

instance {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] (x : Site d) :
    IsProbabilityMeasure (initialLaw μ x) := by
  apply probabilityMeasure_map
  exact (measurable_id.prodMk measurable_const).aemeasurable

instance {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] (x : Site d) :
    IsProbabilityMeasure (annealed μ x) := by
  apply probabilityMeasure_map
  exact (Measurable.of_eval (fun n => measurable_snd.comp (measurable_pi_apply n))).aemeasurable

lemma measurableSet_escape {d : ℕ} (ℓ : Fin d → ℝ) : MeasurableSet (escape ℓ) := by
  apply measurableSet_tendsto
  intro n
  exact (measurable_of_countable (fun x : Site d => ∑ i, (x i : ℝ) * ℓ i)).comp
    (measurable_pi_apply n)

lemma all_rows_strictly_positive {d : ℕ} (μ : Measure (Row d))
    [IsProbabilityMeasure μ] (hμ : StrictEllipticity μ) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ x e, 0 < (ω x).val e := by
  rw [ae_all_iff]
  intro x
  apply ae_of_ae_map (μ := environmentLaw μ) (f := fun ω : Environment d => ω x)
    (p := fun p : Row d => ∀ e, 0 < p.val e) (measurable_pi_apply x).aemeasurable
  simpa only [environmentLaw, Measure.infinitePi_map_eval, StrictEllipticity] using hμ

abbrev rowSigma {d : ℕ} (s : Set (Site d)) : MeasurableSpace (Environment d) :=
  ⨆ x ∈ s, MeasurableSpace.comap (fun ω : Environment d => ω x) inferInstance

lemma rowSigma_le {d : ℕ} (s : Set (Site d)) : rowSigma s ≤ (inferInstance : MeasurableSpace (Environment d)) := by
  exact iSup₂_le (fun x _ => (measurable_pi_apply x).comap_le)

lemma measurable_row {d : ℕ} {s : Set (Site d)} {x : Site d} (hx : x ∈ s) :
    @Measurable (Environment d) (Row d) (rowSigma s) _ (fun ω => ω x) := by
  exact measurable_iff_comap_le.mpr (le_iSup₂_of_le x hx le_rfl)

lemma independent_rowSigma {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    {s t : Set (Site d)} (hst : Disjoint s t) :
    Indep (rowSigma s) (rowSigma t) (environmentLaw μ) := by
  apply indep_iSup_of_disjoint (fun x => (measurable_pi_apply x).comap_le) _ hst
  exact iIndepFun_infinitePi (X := fun _ (p : Row d) => p) (fun _ => measurable_id)

noncomputable def quenchedWeight {d n : ℕ} (x : Fin n → Site d) (e : Fin n → Step d)
    (ω : Environment d) : ℝ≥0∞ := ∏ j, ENNReal.ofReal ((ω (x j)).val (e j))

noncomputable def wordWeight {d n : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Fin n → Site d) (e : Fin n → Step d) : ℝ≥0∞ :=
  ∫⁻ ω, quenchedWeight x e ω ∂environmentLaw μ

lemma measurable_quenchedWeight_on_rows {d n : ℕ} (x : Fin n → Site d)
    (e : Fin n → Step d) :
    @Measurable (Environment d) ℝ≥0∞ (rowSigma (Set.range x)) _
      (quenchedWeight x e) := by
  apply Finset.measurable_prod
  intro j hj
  exact ((measurable_pi_apply (e j)).comp
    (measurable_subtype_coe.comp (measurable_row (s := Set.range x) (x := x j) ⟨j, rfl⟩))).ennreal_ofReal

lemma measurable_quenchedWeight {d n : ℕ} (x : Fin n → Site d)
    (e : Fin n → Step d) : Measurable (quenchedWeight x e) :=
  (measurable_quenchedWeight_on_rows x e).mono (rowSigma_le _) le_rfl

lemma departure_transfer {d n : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Fin n → Site d) (e : Fin n → Step d) (f : Environment d → ℝ≥0∞)
    (hf : @Measurable (Environment d) ℝ≥0∞ (rowSigma ((Set.range x)ᶜ)) _ f) :
    (∫⁻ ω, quenchedWeight x e ω * f ω ∂environmentLaw μ) =
      wordWeight μ x e * ∫⁻ ω, f ω ∂environmentLaw μ := by
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (rowSigma_le _) (rowSigma_le _)
    (independent_rowSigma μ disjoint_compl_right)
    (measurable_quenchedWeight_on_rows x e) hf

lemma quenchedWeight_le_one {d n : ℕ} (x : Fin n → Site d) (e : Fin n → Step d)
    (ω : Environment d) : quenchedWeight x e ω ≤ 1 := by
  apply Finset.prod_le_one
  intro j hj
  exact ENNReal.ofReal_le_one.mpr ((ω (x j)).property.1 (e j)).2

lemma wordWeight_le_one {d n : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Fin n → Site d) (e : Fin n → Step d) : wordWeight μ x e ≤ 1 :=
  lintegral_le_const (ae_of_all _ (quenchedWeight_le_one x e))

lemma wordWeight_pos {d n : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hμ : StrictEllipticity μ) (x : Fin n → Site d) (e : Fin n → Step d) :
    0 < wordWeight μ x e := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hzero := (lintegral_eq_zero_iff (measurable_quenchedWeight x e)).mp hz
  obtain ⟨ω, hω, hωzero⟩ := ((all_rows_strictly_positive μ hμ).and hzero).exists
  have hp : 0 < quenchedWeight x e ω := by
    apply pos_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (hω (x j) (e j)))
  exact (ne_of_gt hp) hωzero

noncomputable def meanStep {d : ℕ} (μ : Measure (Row d)) (e : Step d) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (p.val e) ∂μ

lemma meanStep_pos {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hμ : StrictEllipticity μ) (e : Step d) : 0 < meanStep μ e := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hm : Measurable (fun p : Row d => ENNReal.ofReal (p.val e)) :=
    ((measurable_pi_apply e).comp measurable_subtype_coe).ennreal_ofReal
  have hzero := (lintegral_eq_zero_iff hm).mp hz
  obtain ⟨p, hp, hpzero⟩ := (hμ.and hzero).exists
  exact (ne_of_gt (ENNReal.ofReal_pos.mpr (hp e))) hpzero

lemma meanStep_le_one {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (e : Step d) : meanStep μ e ≤ 1 := by
  apply lintegral_le_const
  exact ae_of_all _ (fun p => ENNReal.ofReal_le_one.mpr (p.property.1 e).2)

lemma meanStep_at_site {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) (e : Step d) :
    (∫⁻ ω, ENNReal.ofReal ((ω x).val e) ∂environmentLaw μ) = meanStep μ e := by
  have hm : Measurable (fun p : Row d => ENNReal.ofReal (p.val e)) :=
    ((measurable_pi_apply e).comp measurable_subtype_coe).ennreal_ofReal
  rw [← lintegral_map hm (measurable_pi_apply x)]
  simp only [environmentLaw, Measure.infinitePi_map_eval, meanStep]

lemma fresh_word_weight {d n : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Fin n → Site d) (e : Fin n → Step d) (hx : Function.Injective x) :
    wordWeight μ x e = ∏ j, meanStep μ (e j) := by
  have hi : iIndepFun (fun j : Fin n => fun ω : Environment d => ω (x j))
      (environmentLaw μ) :=
    iIndepFun.precomp hx
      (iIndepFun_infinitePi (X := fun _ (p : Row d) => p) (fun _ => measurable_id))
  let f : Fin n → Row d → ℝ≥0∞ := fun j p => ENNReal.ofReal (p.val (e j))
  have hf : ∀ j, Measurable (f j) := fun j =>
    ((measurable_pi_apply (e j)).comp measurable_subtype_coe).ennreal_ofReal
  have hid := hi.comp f hf
  unfold wordWeight quenchedWeight
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun]
  · exact Finset.prod_congr rfl (fun j hj => meanStep_at_site μ (x j) (e j))
  · exact hid
  · intro j
    exact (hf j).comp (measurable_pi_apply (x j))

end DirectionalZeroOne

end OAI
