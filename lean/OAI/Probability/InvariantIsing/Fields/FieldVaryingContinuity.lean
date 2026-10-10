import OAI.Probability.InvariantIsing.Fields.FieldVaryingRecursion

namespace OAI

/-! Joint continuity of the actual finite scalar recursion and its
physical-spin second moments, including zero variance increments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped NNReal

namespace InvariantIsing

lemma field_continuous_tanh : Continuous Real.tanh := by
  change Continuous (fun z : ℝ => Real.tanh z)
  simp only [Real.tanh_eq]
  exact (Real.continuous_exp.sub (Real.continuous_exp.comp continuous_neg)).div
    (Real.continuous_exp.add (Real.continuous_exp.comp continuous_neg))
    (fun z => (add_pos (Real.exp_pos z) (Real.exp_pos (-z))).ne')

theorem continuous_fieldVaryingValue {E : Type*} [TopologicalSpace E]
    [FirstCountableTopology E] (L : List (ℝ × (E → ℝ≥0)))
    (hL : ∀ av ∈ L, 0 < av.1) (hc : ∀ av ∈ L, Continuous av.2)
    {V : ℝ} (hV : 0 ≤ V) (hv : ∀ av ∈ L, ∀ t, (av.2 t : ℝ) ≤ V) :
    Continuous (fun p : E × ℝ => fieldVaryingValue L p.1 p.2) := by
  induction L with
  | nil =>
    change Continuous (fun p : E × ℝ => Real.log (Real.cosh p.2))
    exact (Real.continuous_cosh.comp continuous_snd).log (fun p => (Real.cosh_pos p.2).ne')
  | cons av L ih =>
    have hLt : ∀ bv ∈ L, 0 < bv.1 := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hct := fun bv hb => hc bv (List.mem_cons_of_mem av hb)
    have hvt := fun bv hb t => hv bv (List.mem_cons_of_mem av hb) t
    have hval := ih hLt hct hvt
    obtain ⟨hcap, hb⟩ := fieldVaryingValue_bound L hLt hV hvt
    change Continuous (fun p : E × ℝ => gaussianOperator av.1 (av.2 p.1)
      (fieldVaryingValue L p.1) p.2)
    simp_rw [gaussianOperator_eq_transform]
    exact continuous_field_gaussian_transform (E := E × ℝ)
      (U := fun p y => fieldVaryingValue L p.1 y)
      (hval.comp (continuous_fst.fst.prodMk continuous_snd))
      ((NNReal.continuous_coe.comp (hc av List.mem_cons_self)).comp continuous_fst) continuous_snd
      hcap zero_le_one (fun p y => by simpa only [one_mul] using hb p.1 y) av.1

theorem continuous_fieldVaryingMean {E : Type*} [TopologicalSpace E]
    [FirstCountableTopology E] (L : List (ℝ × (E → ℝ≥0)))
    (hL : ∀ av ∈ L, 0 < av.1) (hc : ∀ av ∈ L, Continuous av.2)
    {V : ℝ} (hV : 0 ≤ V) (hv : ∀ av ∈ L, ∀ t, (av.2 t : ℝ) ≤ V) :
    Continuous (fun p : E × ℝ => fieldVaryingMean L p.1 p.2) := by
  induction L with
  | nil =>
    change Continuous (fun p : E × ℝ => Real.tanh p.2)
    exact field_continuous_tanh.comp continuous_snd
  | cons av L ih =>
    have hLt : ∀ bv ∈ L, 0 < bv.1 := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hct := fun bv hb => hc bv (List.mem_cons_of_mem av hb)
    have hvt := fun bv hb t => hv bv (List.mem_cons_of_mem av hb) t
    have hval := continuous_fieldVaryingValue L hLt hct hV hvt
    have hmean := ih hLt hct hvt
    obtain ⟨hcap, hb⟩ := fieldVaryingValue_bound L hLt hV hvt
    have hcont := continuous_field_gaussian_tilt_average (E := E × ℝ)
      (U := fun p y => fieldVaryingValue L p.1 y)
      (A := fun p y => fieldVaryingMean L p.1 y)
      (hval.comp (continuous_fst.fst.prodMk continuous_snd))
      (hmean.comp (continuous_fst.fst.prodMk continuous_snd))
      ((NNReal.continuous_coe.comp (hc av List.mem_cons_self)).comp continuous_fst) continuous_snd
      hcap zero_le_one zero_le_one (fun p y => by simpa only [one_mul] using hb p.1 y)
      (fun p y => (fieldVaryingMean_regular L hLt p.1).2 y) av.1
    convert hcont using 1
    funext p
    exact fieldSpinTransition_eq_standard av.1 (av.2 p.1)
      (fieldVaryingValue_regular L hLt p.1).1 (fieldVaryingMean_regular L hLt p.1).1 p.2

theorem continuous_fieldVaryingSquares {E : Type*} [TopologicalSpace E]
    [FirstCountableTopology E] (L : List (ℝ × (E → ℝ≥0)))
    (hL : ∀ av ∈ L, 0 < av.1) (hc : ∀ av ∈ L, Continuous av.2)
    {V : ℝ} (hV : 0 ≤ V) (hv : ∀ av ∈ L, ∀ t, (av.2 t : ℝ) ≤ V)
    (i : Fin (L.length + 1)) :
    Continuous (fun p : E × ℝ => fieldVaryingSquares L p.1 i p.2) := by
  induction L with
  | nil =>
    change Continuous (fun p : E × ℝ => (Real.tanh p.2) ^ 2)
    exact (field_continuous_tanh.comp continuous_snd).pow 2
  | cons av L ih =>
    have hLt : ∀ bv ∈ L, 0 < bv.1 := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hct := fun bv hb => hc bv (List.mem_cons_of_mem av hb)
    have hvt := fun bv hb t => hv bv (List.mem_cons_of_mem av hb) t
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (continuous_fieldVaryingMean (av :: L) hL hc hV hv).pow 2
    · have hval := continuous_fieldVaryingValue L hLt hct hV hvt
      have hsq := ih hLt hct hvt j
      obtain ⟨hcap, hb⟩ := fieldVaryingValue_bound L hLt hV hvt
      have hcont := continuous_field_gaussian_tilt_average (E := E × ℝ)
        (U := fun p y => fieldVaryingValue L p.1 y)
        (A := fun p y => fieldVaryingSquares L p.1 j y)
        (hval.comp (continuous_fst.fst.prodMk continuous_snd))
        (hsq.comp (continuous_fst.fst.prodMk continuous_snd))
        ((NNReal.continuous_coe.comp (hc av List.mem_cons_self)).comp continuous_fst) continuous_snd
        hcap zero_le_one zero_le_one (fun p y => by simpa only [one_mul] using hb p.1 y)
        (fun p y => by
          have hr := (fieldVaryingSquares_regular L hLt p.1 j).2 y
          rw [abs_of_nonneg hr.1]
          exact hr.2) av.1
      convert hcont using 1
      funext p
      exact fieldSpinTransition_eq_standard av.1 (av.2 p.1)
        (fieldVaryingValue_regular L hLt p.1).1
        (fieldVaryingSquares_regular L hLt p.1 j).1 p.2

theorem continuous_fieldVaryingOverlaps {E : Type*} [TopologicalSpace E]
    [FirstCountableTopology E] (L : List (ℝ × (E → ℝ≥0)))
    (hL : ∀ av ∈ L, 0 < av.1) (hc : ∀ av ∈ L, Continuous av.2)
    {V : ℝ} (hV : 0 ≤ V) (hv : ∀ av ∈ L, ∀ t, (av.2 t : ℝ) ≤ V)
    (root : E → ℝ≥0) (hr : Continuous root) (i : Fin (L.length + 1)) :
    Continuous (fun t => ∫ u, fieldVaryingSquares L t i
      (Real.sqrt (root t : ℝ) * u) ∂gaussianReal 0 1) := by
  have hsq := continuous_fieldVaryingSquares L hL hc hV hv i
  have hshift : Continuous (fun p : E × ℝ => fieldVaryingSquares L p.1 i
      (Real.sqrt (root p.1 : ℝ) * p.2)) :=
    hsq.comp (continuous_fst.prodMk
      (((Real.continuous_sqrt.comp (NNReal.continuous_coe.comp hr)).comp continuous_fst).mul continuous_snd))
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => (1 : ℝ))
  · exact Eventually.of_forall (fun s =>
      (hshift.comp (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable)
  · exact Eventually.of_forall (fun s => ae_of_all _ (fun u => by
      have h := (fieldVaryingSquares_regular L hL s i).2 (Real.sqrt (root s : ℝ) * u)
      rw [Real.norm_eq_abs, abs_of_nonneg h.1]
      exact h.2))
  · exact integrable_const _
  · exact ae_of_all _ (fun u =>
      (hshift.comp (continuous_id.prodMk continuous_const)).continuousAt)

end InvariantIsing

end

end OAI
