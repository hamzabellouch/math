import OAI.Analysis.HenonEmden.LayerAssembly

namespace OAI

universe uE uZ

section PressureRecovery

open MeasureTheory Set
open scoped ENNReal
namespace HenonLaneEmden.LayerTonelli
variable {E : Type uE} [MeasurableSpace E]

lemma lintegral_pair_endpoint_right (μ : Measure E) [SFinite μ] {f g : E → ℝ}
    {k : E × E → ℝ≥0∞} {b : E × ℝ → ℝ≥0∞} {endpoint : E × ℝ → E}
    (hf : Measurable f) (hk : Measurable k) (hs : ∀ x y, k (x,y) = k (y,x))
    (hb : Measurable b) (he : Measurable endpoint) :
    ∫⁻ z, b z.2*k (z.1.1,endpoint z.2) ∂(layerMeasure μ f).prod (layerMeasure μ g) =
      ∫⁻ z, b z*potential μ k f (endpoint z) ∂layerMeasure μ g := by
  rw [← lintegral_prod_swap]
  simp only [Prod.swap]
  simp_rw [hs _ (endpoint _)]
  exact lintegral_pair_endpoint μ hf hk hb he

lemma lintegral_pair_position_right (μ : Measure E) [SFinite μ] {f g : E → ℝ}
    {k : E × E → ℝ≥0∞} {b : E × ℝ → ℝ≥0∞}
    (hf : Measurable f) (hk : Measurable k) (hs : ∀ x y, k (x,y) = k (y,x))
    (hb : Measurable b) :
    ∫⁻ z, b z.2*k (z.1.1,z.2.1) ∂(layerMeasure μ f).prod (layerMeasure μ g) =
      ∫⁻ z, b z*potential μ k f z.1 ∂layerMeasure μ g :=
  lintegral_pair_endpoint_right μ hf hk hs hb measurable_fst

lemma lintegral_pair_endpoint_average_right (μ : Measure E) [SFinite μ] {f g : E → ℝ}
    {k : E × E → ℝ≥0∞} {b : E × ℝ → ℝ≥0∞} {lo hi : E × ℝ → E}
    (hf : Measurable f) (hk : Measurable k) (hs : ∀ x y, k (x,y) = k (y,x))
    (hb : Measurable b) (hlo : Measurable lo) (hhi : Measurable hi) :
    ∫⁻ z, b z.2*((k (z.1.1,lo z.2)+k (z.1.1,hi z.2))/2)
        ∂(layerMeasure μ f).prod (layerMeasure μ g) =
      ∫⁻ z, b z*((potential μ k f (lo z)+potential μ k f (hi z))/2)
        ∂layerMeasure μ g := by
  rw [← lintegral_prod_swap]
  change (∫⁻ z, b z.1*((k (z.2.1,lo z.1)+k (z.2.1,hi z.1))/2)
    ∂(layerMeasure μ g).prod (layerMeasure μ f)) = _
  simp_rw [hs _ (lo _),hs _ (hi _)]
  exact lintegral_pair_endpoint_average μ hf hk hb hlo hhi

lemma lintegral_pair_weight_sum (μ : Measure E) [SFinite μ] {f g : E → ℝ}
    {k : E × E → ℝ≥0∞} {a b : E × ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hk : Measurable k)
    (hs : ∀ x y, k (x,y) = k (y,x)) (ha : Measurable a) (hb : Measurable b) :
    ∫⁻ z, (a z.1+b z.2)*k (z.1.1,z.2.1) ∂(layerMeasure μ f).prod (layerMeasure μ g) =
      (∫⁻ z, a z*potential μ k g z.1 ∂layerMeasure μ f) +
      ∫⁻ z, b z*potential μ k f z.1 ∂layerMeasure μ g := by
  simp_rw [add_mul]
  rw [lintegral_add_left (by fun_prop),lintegral_pair_position μ hg hk ha,
    lintegral_pair_position_right μ hf hk hs hb]

end HenonLaneEmden.LayerTonelli

namespace HenonLaneEmden.LayerPressure
open LineComponents LayerTonelli IntervalGeometry
variable {Z : Type uZ} [NormedAddCommGroup Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

omit [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] in
lemma splitKernel_symm (n : ℕ) (C : ℝ) (x y : Z × ℝ) :
    splitKernel n C (x,y) = splitKernel n C (y,x) := by
  unfold splitKernel kernel
  dsimp only
  rw [norm_sub_rev x.1 y.1,show (x.2-y.2)^2=(y.2-x.2)^2 by ring]

omit [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] in
lemma splitKernel_nonneg (n : ℕ) {C : ℝ} (hC : 0 ≤ C) (z : (Z × ℝ) × (Z × ℝ)) :
    0 ≤ splitKernel n C z := kernel_nonneg n hC _

lemma pairLeft_recovery (μ : Measure Z) [SFinite μ] (n : ℕ) (C : ℝ)
    {f g h d : Z × ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfo : IsOpen (parameterLayer f)) (hgo : IsOpen (parameterLayer g))
    (hh : Continuous h) (hd : Continuous d) (δ : ℝ) :
    (∫⁻ z, ENNReal.ofReal (pairLeft n C f g h d δ z)
      ∂(layerMeasure (μ.prod volume) f).prod (layerMeasure (μ.prod volume) g)) =
      (∫⁻ z, ENNReal.ofReal (sourceWeight f h d δ z)*
        potential (μ.prod volume) (fun p => ENNReal.ofReal (splitKernel n C p)) g z.1
        ∂layerMeasure (μ.prod volume) f) +
      ∫⁻ z, ENNReal.ofReal (sourceWeight g h d δ z)*
        potential (μ.prod volume) (fun p => ENNReal.ofReal (splitKernel n C p)) f z.1
        ∂layerMeasure (μ.prod volume) g := by
  have he (z : ((Z × ℝ) × ℝ) × ((Z × ℝ) × ℝ)) :
      ENNReal.ofReal (pairLeft n C f g h d δ z) =
      (ENNReal.ofReal (sourceWeight f h d δ z.1)+ENNReal.ofReal (sourceWeight g h d δ z.2))*
        ENNReal.ofReal (splitKernel n C (z.1.1,z.2.1)) := by
    rw [pairLeft,ENNReal.ofReal_mul (add_nonneg (sourceWeight_nonneg _ _ _ _ _) (sourceWeight_nonneg _ _ _ _ _)),
      ENNReal.ofReal_add (sourceWeight_nonneg _ _ _ _ _) (sourceWeight_nonneg _ _ _ _ _)]
  simp_rw [he]
  exact lintegral_pair_weight_sum (μ.prod volume) hf hg (measurable_splitKernel n C).ennreal_ofReal
    (fun x y => congrArg ENNReal.ofReal (splitKernel_symm n C x y))
    (measurable_sourceWeight hfo hh hd δ).ennreal_ofReal
    (measurable_sourceWeight hgo hh hd δ).ennreal_ofReal

/-- Finite cancellation is used only after the endpoint contributions have
been proved finite. -/
lemma pressure_cancellation {U V R P M Q L T : ℝ≥0∞} (hV : V ≠ ⊤)
    (hcomp : U ≤ V+P+M) (hrec : R+V ≤ U+L+T) (hmis : M ≤ Q+L) :
    R ≤ P+Q+2*L+T := by
  apply (ENNReal.add_le_add_iff_right hV).mp
  calc
    R+V ≤ U+L+T := hrec
    _ ≤ (V+P+M)+L+T := by gcongr
    _ ≤ (V+P+(Q+L))+L+T := by gcongr
    _ = (P+Q+2*L+T)+V := by ring

end HenonLaneEmden.LayerPressure
end PressureRecovery

end OAI
