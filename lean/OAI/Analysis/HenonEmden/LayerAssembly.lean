import OAI.Analysis.HenonEmden.LayerSplit

namespace OAI

universe uZ

section LayerAssembly

open MeasureTheory Set
open scoped ENNReal
namespace HenonLaneEmden.LayerPressure
open LineComponents IntervalGeometry LayerTonelli

variable {Z : Type uZ} [NormedAddCommGroup Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]


noncomputable def sourceWeight (f h d : Z × ℝ → ℝ) (δ : ℝ) (a : (Z × ℝ) × ℝ) : ℝ :=
  lineWeight {s | ((a.1.1,a.2),s) ∈ parameterLayer f} (fun s => h (a.1.1,s))
    (fun s => d (a.1.1,s)) δ a.1.2

noncomputable def sourceLower (f : Z × ℝ → ℝ) (a : (Z × ℝ) × ℝ) : Z × ℝ :=
  (a.1.1,lowerEndpoint (parameterLayer f) ((a.1.1,a.2),a.1.2))
noncomputable def sourceUpper (f : Z × ℝ → ℝ) (a : (Z × ℝ) × ℝ) : Z × ℝ :=
  (a.1.1,upperEndpoint (parameterLayer f) ((a.1.1,a.2),a.1.2))

omit [SecondCountableTopology Z] in
lemma measurable_sourceWeight {f h d : Z × ℝ → ℝ} (hf : IsOpen (parameterLayer f))
    (hh : Continuous h) (hd : Continuous d) (δ : ℝ) : Measurable (sourceWeight f h d δ) := by
  let h' : (Z × ℝ) × ℝ → ℝ := fun z => h (z.1.1,z.2)
  let d' : (Z × ℝ) × ℝ → ℝ := fun z => d (z.1.1,z.2)
  have hh' : Continuous h' := hh.comp (continuous_fst.fst.prodMk continuous_snd)
  have hd' : Continuous d' := hd.comp (continuous_fst.fst.prodMk continuous_snd)
  have he : Measurable (fun p : (Z × ℝ) × ℝ =>
      (setWeight (fun s => h' (p.1,s)) (fun s => d' (p.1,s)) δ
        (connectedComponentIn {s | (p.1,s) ∈ parameterLayer f} p.2)).toReal) :=
    (measurable_parametric_setWeight hf hh' hd' δ).ennreal_toReal
  have hem := he.comp (tripleSwap : (Z × ℝ) × ℝ ≃ᵐ (Z × ℝ) × ℝ).measurable
  unfold sourceWeight lineWeight
  simpa only [Function.comp_def,tripleSwap_apply,h',d'] using hem

omit [SecondCountableTopology Z] in
lemma measurable_sourceLower {f : Z × ℝ → ℝ} (hf : IsOpen (parameterLayer f)) :
    Measurable (sourceLower f) := by
  exact measurable_fst.fst.prodMk ((measurable_lowerEndpoint hf).comp
    (measurable_fst.fst.prodMk measurable_snd |>.prodMk measurable_fst.snd))
omit [SecondCountableTopology Z] in
lemma measurable_sourceUpper {f : Z × ℝ → ℝ} (hf : IsOpen (parameterLayer f)) :
    Measurable (sourceUpper f) := by
  exact measurable_fst.fst.prodMk ((measurable_upperEndpoint hf).comp
    (measurable_fst.fst.prodMk measurable_snd |>.prodMk measurable_fst.snd))

omit [NormedAddCommGroup Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] in
lemma sourceWeight_nonneg (f h d : Z × ℝ → ℝ) (δ : ℝ) (a : (Z × ℝ) × ℝ) :
    0 ≤ sourceWeight f h d δ a := ENNReal.toReal_nonneg

omit [NormedAddCommGroup Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] in
lemma sourceWeight_le {f h d : Z × ℝ → ℝ} {δ : ℝ} {a : (Z × ℝ) × ℝ}
    (ha : a ∈ sourceSubgraph f) (hh : 0 ≤ h a.1) : sourceWeight f h d δ a ≤ h a.1 :=
  lineWeight_le ha hh

noncomputable def splitKernel (n : ℕ) (C : ℝ) (z : (Z × ℝ) × (Z × ℝ)) : ℝ :=
  kernel n ‖z.1.1-z.2.1‖ C (z.1.2-z.2.2)
noncomputable def splitDirection (z : (Z × ℝ) × (Z × ℝ)) : ℝ :=
  (z.1.2-z.2.2)^2/(‖z.1.1-z.2.1‖^2+(z.1.2-z.2.2)^2)

lemma measurable_splitKernel (n : ℕ) (C : ℝ) : Measurable (splitKernel (Z := Z) n C) := by
  unfold splitKernel kernel
  fun_prop
lemma measurable_splitDirection : Measurable (splitDirection (Z := Z)) := by
  unfold splitDirection
  fun_prop

noncomputable def pairLeft (n : ℕ) (C : ℝ) (f g h d : Z × ℝ → ℝ) (δ : ℝ)
    (z : ((Z × ℝ) × ℝ) × ((Z × ℝ) × ℝ)) : ℝ :=
  (sourceWeight f h d δ z.1+sourceWeight g h d δ z.2)*splitKernel n C (z.1.1,z.2.1)

noncomputable def pairRight (n : ℕ) (C : ℝ) (f g h d : Z × ℝ → ℝ) (δ : ℝ)
    (z : ((Z × ℝ) × ℝ) × ((Z × ℝ) × ℝ)) : ℝ :=
  sourceWeight f h d δ z.1 *
    ((splitKernel n C (sourceLower f z.1,z.2.1)+splitKernel n C (sourceUpper f z.1,z.2.1))/2) +
  sourceWeight g h d δ z.2 *
    ((splitKernel n C (z.1.1,sourceLower g z.2)+splitKernel n C (z.1.1,sourceUpper g z.2))/2) +
  (((n:ℝ)-2)*h z.1.1*splitDirection (z.1.1,z.2.1)+
    |sourceWeight f h d δ z.1-sourceWeight g h d δ z.2|)*splitKernel n C (z.1.1,z.2.1)

lemma measurable_pairLeft (n : ℕ) (C : ℝ) {f g h d : Z × ℝ → ℝ}
    (hf : IsOpen (parameterLayer f)) (hg : IsOpen (parameterLayer g))
    (hh : Continuous h) (hd : Continuous d) (δ : ℝ) : Measurable (pairLeft n C f g h d δ) := by
  unfold pairLeft
  have hχf := measurable_sourceWeight hf hh hd δ
  have hχg := measurable_sourceWeight hg hh hd δ
  have hk := measurable_splitKernel (Z := Z) n C
  fun_prop

lemma measurable_pairRight (n : ℕ) (C : ℝ) {f g h d : Z × ℝ → ℝ}
    (hf : IsOpen (parameterLayer f)) (hg : IsOpen (parameterLayer g))
    (hh : Continuous h) (hd : Continuous d) (δ : ℝ) : Measurable (pairRight n C f g h d δ) := by
  unfold pairRight
  have hχf := measurable_sourceWeight hf hh hd δ
  have hχg := measurable_sourceWeight hg hh hd δ
  have hlof := measurable_sourceLower hf
  have hlog := measurable_sourceLower hg
  have hhif := measurable_sourceUpper hf
  have hhig := measurable_sourceUpper hg
  have hk := measurable_splitKernel (Z := Z) n C
  have hD := measurable_splitDirection (Z := Z)
  fun_prop

omit [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] in
lemma weighted_leftAverage_eq {f h d : Z × ℝ → ℝ} (hf : IsOpen (parameterLayer f))
    (δ : ℝ) {p : Z × ℝ} {s : ℝ} (hs : (p,s) ∈ parameterLayer f)
    (k : ℝ → ℝ) (y : ℝ) :
    lineWeight {s | (p,s) ∈ parameterLayer f} (fun s => h (p.1,s)) (fun s => d (p.1,s)) δ s *
      leftAverage {s | (p,s) ∈ parameterLayer f} k s y =
    lineWeight {s | (p,s) ∈ parameterLayer f} (fun s => h (p.1,s)) (fun s => d (p.1,s)) δ s *
      ((k (lowerEndpoint (parameterLayer f) (p,s)-y)+k (upperEndpoint (parameterLayer f) (p,s)-y))/2) := by
  by_cases hz : lineWeight {s | (p,s) ∈ parameterLayer f} (fun s => h (p.1,s))
      (fun s => d (p.1,s)) δ s = 0
  · rw [hz,zero_mul,zero_mul]
  · have he := relative_endpoints_eq_of_weight_pos hf hs
      (lt_of_le_of_ne (lineWeight_nonneg _ _ _ _ _) (Ne.symm hz))
    simp only [leftAverage,he.1,he.2]

omit [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] in
lemma weighted_rightAverage_eq {g h d : Z × ℝ → ℝ} (hg : IsOpen (parameterLayer g))
    (δ : ℝ) {p : Z × ℝ} {s : ℝ} (hs : (p,s) ∈ parameterLayer g)
    (k : ℝ → ℝ) (x : ℝ) :
    lineWeight {s | (p,s) ∈ parameterLayer g} (fun s => h (p.1,s)) (fun s => d (p.1,s)) δ s *
      rightAverage {s | (p,s) ∈ parameterLayer g} k x s =
    lineWeight {s | (p,s) ∈ parameterLayer g} (fun s => h (p.1,s)) (fun s => d (p.1,s)) δ s *
      ((k (x-lowerEndpoint (parameterLayer g) (p,s))+k (x-upperEndpoint (parameterLayer g) (p,s)))/2) := by
  by_cases hz : lineWeight {s | (p,s) ∈ parameterLayer g} (fun s => h (p.1,s))
      (fun s => d (p.1,s)) δ s = 0
  · rw [hz,zero_mul,zero_mul]
  · have he := relative_endpoints_eq_of_weight_pos hg hs
      (lt_of_le_of_ne (lineWeight_nonneg _ _ _ _ _) (Ne.symm hz))
    simp only [rightAverage,he.1,he.2]

omit [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] in
lemma pair_line_comparison (n : ℕ) (hn : 3 ≤ n) {C : ℝ} (hC : 0 ≤ C)
    {f g h d : Z × ℝ → ℝ} (hf : IsOpen (parameterLayer f)) (hg : IsOpen (parameterLayer g))
    (hhn : ∀ x, 0 ≤ h x) (δ : ℝ) (p : (Z × ℝ) × (Z × ℝ)) (hp : p.1.1 ≠ p.2.1) :
    (∫⁻ s : ℝ × ℝ in {s | (p.1,s) ∈ parameterLayer f} ×ˢ {s | (p.2,s) ∈ parameterLayer g},
      ENNReal.ofReal (pairLeft n C f g h d δ (((p.1.1,s.1),p.1.2),((p.2.1,s.2),p.2.2)))) ≤
    ∫⁻ s : ℝ × ℝ in {s | (p.1,s) ∈ parameterLayer f} ×ˢ {s | (p.2,s) ∈ parameterLayer g},
      ENNReal.ofReal (pairRight n C f g h d δ (((p.1.1,s.1),p.1.2),((p.2.1,s.2),p.2.2))) := by
  have hfo := isOpen_section hf p.1
  have hgo := isOpen_section hg p.2
  have hl : 0 < ‖p.1.1-p.2.1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hp)
  have hh := weighted_source_layer_comparison n hn hfo hgo
    (fun s => h (p.1.1,s)) (fun s => h (p.2.1,s))
    (fun s => d (p.1.1,s)) (fun s => d (p.2.1,s)) δ hl hC (fun x _ => hhn _)
  change (∫⁻ s in _, ENNReal.ofReal _) ≤ _ at hh
  convert hh using 1
  · rfl
  · apply setLIntegral_congr_fun (hfo.measurableSet.prod hgo.measurableSet)
    intro s hs
    unfold pairRight splitKernel splitDirection sourceLower sourceUpper sourceWeight
    dsimp only
    rw [weighted_leftAverage_eq hf δ hs.1,weighted_rightAverage_eq hg δ hs.2]

lemma ae_distinct_transverse (μ : Measure Z) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ p : (Z × ℝ) × (Z × ℝ) ∂(μ.prod volume).prod (μ.prod volume), p.1.1 ≠ p.2.1 := by
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  apply ae_of_all
  intro x
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [μ.ae_ne x.1] with z hz
  exact ae_of_all _ (fun _ => Ne.symm hz)

/-- The globally integrated nonnegative interval comparison. No source,
endpoint, or energy integrability is assumed; all terms are still extended values. -/
lemma global_nonnegative_pressure (μ : Measure Z) [SFinite μ] [NullSingletonClass μ]
    (n : ℕ) (hn : 3 ≤ n) {C : ℝ} (hC : 0 ≤ C)
    {f g h d : Z × ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfo : IsOpen (parameterLayer f)) (hgo : IsOpen (parameterLayer g))
    (hh : Continuous h) (hd : Continuous d) (hhn : ∀ x, 0 ≤ h x) (δ : ℝ) :
    (∫⁻ z, ENNReal.ofReal (pairLeft n C f g h d δ z)
      ∂(layerMeasure (μ.prod volume) f).prod (layerMeasure (μ.prod volume) g)) ≤
    ∫⁻ z, ENNReal.ofReal (pairRight n C f g h d δ z)
      ∂(layerMeasure (μ.prod volume) f).prod (layerMeasure (μ.prod volume) g) := by
  rw [lintegral_pair_layer_split μ hf hg (measurable_pairLeft n C hfo hgo hh hd δ).ennreal_ofReal,
    lintegral_pair_layer_split μ hf hg (measurable_pairRight n C hfo hgo hh hd δ).ennreal_ofReal]
  apply lintegral_mono_ae
  filter_upwards [ae_distinct_transverse μ] with p hp
  exact pair_line_comparison n hn hC hfo hgo hhn δ p hp

end HenonLaneEmden.LayerPressure
end LayerAssembly

end OAI
