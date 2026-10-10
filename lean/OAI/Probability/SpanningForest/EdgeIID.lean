import OAI.Probability.SpanningForest.IIDBlocks
import OAI.Probability.SpanningForest.UniformSampler
import OAI.Probability.SpanningForest.EdgeAllocationMeasurable
import OAI.Probability.SpanningForest.CanonicalIID

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem336.EdgeIID

local instance : IsProbabilityMeasure uniform01 := sampler_uniform01_probability
local instance : IsProbabilityMeasure privatePoolLaw := privatePoolLaw_probability
local instance : NullSingletonClass uniform01 := by
  unfold uniform01
  infer_instance

abbrev Stream := Option ℕ → ℝ

def streamLaw : Measure Stream := Measure.infinitePi (fun _ : Option ℕ => uniform01)

local instance : IsProbabilityMeasure streamLaw := by
  unfold streamLaw
  infer_instance

def stream : ℝ → Stream := Classical.choose (exists_uniform01_sampler streamLaw)

@[fun_prop] theorem measurable_stream : Measurable stream :=
  (Classical.choose_spec (exists_uniform01_sampler streamLaw)).1

theorem map_stream : uniform01.map stream = streamLaw :=
  (Classical.choose_spec (exists_uniform01_sampler streamLaw)).2

def expanded (U : ℕ → ℝ) (p : ℕ × Option ℕ) : ℝ := stream (U p.1) p.2

@[fun_prop] theorem measurable_expanded : Measurable expanded := by
  apply Measurable.of_eval
  intro p
  exact (measurable_pi_apply p.2).comp (measurable_stream.comp (measurable_pi_apply p.1))

theorem map_expanded :
    privatePoolLaw.map expanded =
      Measure.infinitePi (fun _ : ℕ × Option ℕ => uniform01) := by
  have hm : Measurable (fun U : ℕ → ℝ => fun v => stream (U v)) := by fun_prop
  have heq : expanded = (MeasurableEquiv.curry ℕ (Option ℕ) ℝ).symm ∘
      (fun U : ℕ → ℝ => fun v => stream (U v)) := rfl
  rw [heq, ← Measure.map_map (MeasurableEquiv.curry ℕ (Option ℕ) ℝ).symm.measurable hm]
  unfold privatePoolLaw
  rw [Measure.infinitePi_map_pi _ (fun _ => measurable_stream)]
  simp only [map_stream, streamLaw]
  exact Measure.infinitePi_map_curry_symm (fun (_ : ℕ) (_ : Option ℕ) => uniform01)

def keys (U : ℕ → ℝ) (v : ℕ) : ℝ := expanded U (v, none)

def pool (U : ℕ → ℝ) (p : ℕ × ℕ) : ℝ := expanded U (p.1, some p.2)

@[fun_prop] theorem measurable_keys : Measurable keys := by
  exact Measurable.of_eval (fun v => (measurable_pi_apply (v, none)).comp measurable_expanded)

@[fun_prop] theorem measurable_pool : Measurable pool := by
  exact Measurable.of_eval (fun p =>
    (measurable_pi_apply (p.1, some p.2)).comp measurable_expanded)

theorem map_keys_pool :
    privatePoolLaw.map (fun U => (keys U, pool U)) =
      privatePoolLaw.prod (Measure.infinitePi (fun _ : ℕ × ℕ => uniform01)) := by
  let a : ℕ → ℕ × Option ℕ := fun v => (v, none)
  let b : ℕ × ℕ → ℕ × Option ℕ := fun p => (p.1, some p.2)
  have ha : Function.Injective a := by
    intro i j h
    exact congrArg Prod.fst h
  have hb : Function.Injective b := by
    intro p q h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact Prod.ext h1 (Option.some.inj h2)
  have hab : Disjoint (Set.range a) (Set.range b) := by
    rw [Set.disjoint_left]
    rintro _ ⟨v, rfl⟩ ⟨p, h⟩
    have hh := congrArg Prod.snd h
    simp [a, b] at hh
  have hm : Measurable (fun z : (ℕ × Option ℕ) → ℝ =>
      ((fun v => z (a v)), (fun p => z (b p)))) := by fun_prop
  have heq : (fun U => (keys U, pool U)) =
      (fun z : (ℕ × Option ℕ) → ℝ =>
        ((fun v => z (a v)), (fun p => z (b p)))) ∘ expanded := rfl
  rw [heq, ← Measure.map_map hm measurable_expanded, map_expanded]
  exact RandomReindex.map_infinitePi_two_blocks uniform01 a b ha hb hab

abbrev GraphEdge (G : GraphCode) := {e : EdgeCode // Adj G e.1.1 e.1.2}

def raw (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode) : ℝ :=
  pool U (EdgeAllocation.coordinate G (keys U) e)

theorem map_keys_raw (G : GraphCode) (hG : GraphLocallyFinite G)
    (hm : ∀ e : EdgeCode, Measurable (fun k => EdgeAllocation.coordinate G k e)) :
    privatePoolLaw.map (fun U => (keys U, fun e : GraphEdge G => raw G U e)) =
      privatePoolLaw.prod (Measure.infinitePi (fun _ : GraphEdge G => uniform01)) := by
  apply RandomReindex.map_random_injective_reindex_of_joint_law
    privatePoolLaw privatePoolLaw uniform01 keys pool measurable_keys measurable_pool
    map_keys_pool (fun k (e : GraphEdge G) => EdgeAllocation.coordinate G k e)
    (fun e => hm e)
  filter_upwards [RandomReindex.ae_injective_infinitePi (J := ℕ) uniform01] with k hk
  intro e f hef
  apply Subtype.ext
  exact EdgeAllocation.coordinate_injOn hG hk e.property f.property hef

theorem measurable_coordinate_fixed (G : GraphCode) (e : EdgeCode) :
    Measurable (fun k => EdgeAllocation.coordinate G k e) :=
  EdgeAllocation.measurable_coordinate.comp
    ((measurable_const.prodMk measurable_id).prodMk measurable_const)

@[fun_prop] theorem measurable_raw (G : GraphCode) (e : EdgeCode) :
    Measurable (fun U => raw G U e) := by
  have hm := (measurable_coordinate_fixed G e).comp measurable_keys
  exact (RandomReindex.measurable_random_eval
    (fun U => EdgeAllocation.coordinate G (keys U) e) hm).comp
      (measurable_id.prodMk measurable_pool)

theorem map_keys : privatePoolLaw.map keys = privatePoolLaw := by
  have h := congrArg (fun μ : Measure ((ℕ → ℝ) × ((ℕ × ℕ) → ℝ)) =>
    μ.map Prod.fst) map_keys_pool
  rw [Measure.map_map measurable_fst (measurable_keys.prodMk measurable_pool),
    Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h

theorem ae_injective_keys : ∀ᵐ U ∂privatePoolLaw, Function.Injective (keys U) := by
  apply ae_of_ae_map measurable_keys.aemeasurable
  rw [map_keys]
  exact RandomReindex.ae_injective_infinitePi uniform01

theorem map_raw (G : GraphCode) (hG : GraphLocallyFinite G) :
    privatePoolLaw.map (fun U => fun e : GraphEdge G => raw G U e) =
      Measure.infinitePi (fun _ : GraphEdge G => uniform01) := by
  have h := congrArg (fun μ : Measure ((ℕ → ℝ) × (GraphEdge G → ℝ)) =>
    μ.map Prod.snd) (map_keys_raw G hG (measurable_coordinate_fixed G))
  rw [Measure.map_map measurable_snd (measurable_keys.prodMk
      (Measurable.of_eval (fun e : GraphEdge G => measurable_raw G e))),
    Measure.map_snd_prod, measure_univ, one_smul] at h
  exact h

theorem map_rule_of_eq_raw (G : GraphCode) (hG : GraphLocallyFinite G)
    (F : (ℕ → ℝ) → EdgeCode → ℝ)
    (hF : ∀ U, Function.Injective (keys U) → ∀ e, F U e = raw G U e) :
    privatePoolLaw.map (fun U => fun e : GraphEdge G => F U e) =
      Measure.infinitePi (fun _ : GraphEdge G => uniform01) := by
  rw [← map_raw G hG]
  apply Measure.map_congr
  filter_upwards [ae_injective_keys] with U hU
  exact funext (fun e => hF U hU e)

theorem map_rule_of_vertexIID {Ω : Type} [MeasurableSpace Ω]
    (G : GraphCode) (hG : GraphLocallyFinite G)
    (P : Measure Ω) (U : ℕ → Ω → ℝ) (hU : IsVertexIID P U)
    (F : (ℕ → ℝ) → EdgeCode → ℝ)
    (hm : ∀ e, Measurable (fun labels => F labels e))
    (hF : ∀ labels, Function.Injective (keys labels) →
      ∀ e, F labels e = raw G labels e) :
    P.map (fun ω => fun e : GraphEdge G => F (fun v => U v ω) e) =
      Measure.infinitePi (fun _ : GraphEdge G => uniform01) := by
  have hlabels : Measurable (fun ω v => U v ω) := Measurable.of_eval hU.1
  rw [show (fun ω => fun e : GraphEdge G => F (fun v => U v ω) e) =
      (fun labels => fun e : GraphEdge G => F labels e) ∘ (fun ω v => U v ω) from rfl,
    ← Measure.map_map (Measurable.of_eval (fun e : GraphEdge G => hm e)) hlabels,
    CanonicalIID.map_labels hU]
  exact map_rule_of_eq_raw G hG F hF

theorem map_sampled_rule_of_vertexIID {Ω Y : Type} [MeasurableSpace Ω]
    [MeasurableSpace Y] (ν : Measure Y)
    (sample : ℝ → Y) (hsample : Measurable sample)
    (hsample_law : uniform01.map sample = ν)
    (G : GraphCode) (hG : GraphLocallyFinite G)
    (P : Measure Ω) (U : ℕ → Ω → ℝ) (hU : IsVertexIID P U)
    (F : (ℕ → ℝ) → EdgeCode → ℝ)
    (hm : ∀ e, Measurable (fun labels => F labels e))
    (hF : ∀ labels, Function.Injective (keys labels) →
      ∀ e, F labels e = raw G labels e) :
    P.map (fun ω => fun e : GraphEdge G => sample (F (fun v => U v ω) e)) =
      Measure.infinitePi (fun _ : GraphEdge G => ν) := by
  have hlabels : Measurable (fun ω v => U v ω) := Measurable.of_eval hU.1
  have hfield : Measurable (fun ω => fun e : GraphEdge G => F (fun v => U v ω) e) :=
    Measurable.of_eval (fun e => (hm e).comp hlabels)
  have happly : Measurable (fun x : GraphEdge G → ℝ => fun e => sample (x e)) :=
    Measurable.of_eval (fun e => hsample.comp (measurable_pi_apply e))
  rw [show (fun ω => fun e : GraphEdge G => sample (F (fun v => U v ω) e)) =
      (fun x : GraphEdge G → ℝ => fun e => sample (x e)) ∘
        (fun ω => fun e : GraphEdge G => F (fun v => U v ω) e) from rfl,
    ← Measure.map_map happly hfield, map_rule_of_vertexIID G hG P U hU F hm hF,
    Measure.infinitePi_map_pi _ (fun _ => hsample)]
  simp only [hsample_law]

end Problem336.EdgeIID

end

end OAI
