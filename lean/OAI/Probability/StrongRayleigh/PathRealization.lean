import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24
universe u_25 u_26 u_27 u_28 u_29 u_30

noncomputable section
open MeasureTheory
open scoped NNReal Topology

namespace Problem336AdditiveD139.PathRealization

abbrev Path := C(ℝ≥0, ℝ)

local instance : MeasurableSpace Path := borel Path
local instance : BorelSpace Path := ⟨rfl⟩

theorem measurableEmbedding_denseEval (d : ℕ → ℝ≥0) (hd : DenseRange d) :
    MeasurableEmbedding (fun f : Path => fun n : ℕ => f (d n)) := by
  apply Measurable.measurableEmbedding
  · exact Measurable.of_eval (fun n => (continuous_eval_const (d n)).measurable)
  · intro f g h
    apply ContinuousMap.coe_injective
    exact hd.equalizer f.continuous g.continuous h

theorem measurable_path_iff {Ω : Type u_1} [MeasurableSpace Ω] {X : Ω → Path} :
    Measurable X ↔ ∀ t : ℝ≥0, Measurable (fun ω => X ω t) := by
  constructor
  · intro h t
    exact (continuous_eval_const t).measurable.comp h
  · intro h
    obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq ℝ≥0
    apply (measurableEmbedding_denseEval d hd).measurable_comp_iff.mp
    exact Measurable.of_eval (fun n => h (d n))

theorem measurable_bundle {Ω : Type u_2} [MeasurableSpace Ω]
    (X : Ω → ℝ≥0 → ℝ) (hc : ∀ ω, Continuous (X ω))
    (hm : ∀ t, Measurable (fun ω => X ω t)) :
    Measurable (fun ω => (⟨X ω, hc ω⟩ : Path)) := by
  exact measurable_path_iff.mpr hm

theorem measurable_bundle_family {Ω : Type u_3} {I : Type u_4} [MeasurableSpace Ω]
    (X : Ω → I → ℝ≥0 → ℝ) (hc : ∀ ω i, Continuous (X ω i))
    (hm : ∀ i t, Measurable (fun ω => X ω i t)) :
    Measurable (fun ω i => (⟨X ω i, hc ω i⟩ : Path)) := by
  exact Measurable.of_eval (fun i => measurable_bundle (fun ω => X ω i)
    (fun ω => hc ω i) (hm i))

theorem measurable_joint_eval {Ω : Type u_5} [MeasurableSpace Ω]
    {X : Ω → Path} (hm : Measurable X) :
    Measurable (fun p : Ω × ℝ≥0 => X p.1 p.2) := by
  exact continuous_eval.measurable.comp ((hm.comp measurable_fst).prodMk measurable_snd)

theorem measurable_joint_family_eval {Ω : Type u_6} {I : Type u_7} [MeasurableSpace Ω]
    {X : Ω → I → Path} (hm : Measurable X) :
    Measurable (fun p : Ω × ℝ≥0 => fun i => X p.1 i p.2) := by
  exact Measurable.of_eval (fun i =>
    measurable_joint_eval ((measurable_pi_apply i).comp hm))

def observationPath (x : ℝ) (B : Path) : Path :=
  ⟨fun t => (t : ℝ) * x + B t, by fun_prop⟩

theorem measurable_observationPath :
    Measurable (fun p : ℝ × Path => observationPath p.1 p.2) := by
  apply measurable_path_iff.mpr
  intro t
  exact (measurable_const.mul measurable_fst).add
    ((continuous_eval_const t).measurable.comp measurable_snd)

theorem measurable_observationFamily {I : Type u_8} :
    Measurable (fun p : (I → ℝ) × (I → Path) =>
      fun i => observationPath (p.1 i) (p.2 i)) := by
  refine Measurable.of_eval (fun i => ?_)
  apply measurable_path_iff.mpr
  intro t
  change Measurable (fun p : (I → ℝ) × (I → Path) =>
    (t : ℝ) * p.1 i + p.2 i t)
  exact (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).add
    ((continuous_eval_const t).measurable.comp
      ((measurable_pi_apply i).comp measurable_snd))

def driftIntegrand {I : Type u_9} (b : (ℝ≥0 × (I → ℝ)) → I → ℝ)
    (y : I → Path) (i : I) (s : ℝ) : ℝ :=
  b (s.toNNReal, fun j => y j s.toNNReal) i

theorem measurable_driftIntegrand {I : Type u_10}
    {b : (ℝ≥0 × (I → ℝ)) → I → ℝ} (hb : Measurable b) (i : I) :
    Measurable (fun p : (I → Path) × ℝ => driftIntegrand b p.1 i p.2) := by
  apply ((measurable_pi_apply i).comp hb).comp
  refine (continuous_real_toNNReal.measurable.comp measurable_snd).prodMk ?_
  refine Measurable.of_eval (fun j => ?_)
  exact continuous_eval.measurable.comp
    (((measurable_pi_apply j).comp measurable_fst).prodMk
      (continuous_real_toNNReal.measurable.comp measurable_snd))

theorem intervalIntegrable_driftIntegrand {I : Type u_11}
    {b : (ℝ≥0 × (I → ℝ)) → I → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C) (y : I → Path) (i : I) (u v : ℝ) :
    IntervalIntegrable (driftIntegrand b y i) volume u v := by
  apply (intervalIntegrable_const (c := C)).mono_fun'
  · exact ((measurable_driftIntegrand hb i).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · filter_upwards [] with s
    exact hbound (s.toNNReal, fun j => y j s.toNNReal) i

def driftPrimitive {I : Type u_12} (b : (ℝ≥0 × (I → ℝ)) → I → ℝ)
    (hb : Measurable b) (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    (y : I → Path) (i : I) : Path :=
  ⟨fun t => ∫ s in (0 : ℝ)..(t : ℝ), driftIntegrand b y i s,
    (intervalIntegral.continuous_primitive
      (intervalIntegrable_driftIntegrand hb C hbound y i) 0).comp continuous_subtype_val⟩

theorem measurable_driftPrimitive {I : Type u_13}
    {b : (ℝ≥0 × (I → ℝ)) → I → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C) (i : I) :
    Measurable (fun y : I → Path => driftPrimitive b hb C hbound y i) := by
  apply measurable_path_iff.mpr
  intro t
  change Measurable (fun y : I → Path =>
    ∫ s in (0 : ℝ)..(t : ℝ), driftIntegrand b y i s)
  simp only [intervalIntegral]
  exact ((measurable_driftIntegrand hb i).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Ioc (0 : ℝ) t))).measurable.sub
    ((measurable_driftIntegrand hb i).stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Set.Ioc (t : ℝ) 0))).measurable

def innovation {I : Type u_14} (b : (ℝ≥0 × (I → ℝ)) → I → ℝ)
    (hb : Measurable b) (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    (y : I → Path) (i : I) : Path :=
  y i - driftPrimitive b hb C hbound y i

theorem measurable_innovation {I : Type u_15}
    {b : (ℝ≥0 × (I → ℝ)) → I → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C) :
    Measurable (innovation b hb C hbound) := by
  refine Measurable.of_eval (fun i => ?_)
  apply measurable_path_iff.mpr
  intro t
  exact ((continuous_eval_const t).measurable.comp (measurable_pi_apply i)).sub
    ((continuous_eval_const t).measurable.comp (measurable_driftPrimitive hb C hbound i))

theorem innovation_reconstruction {I : Type u_16}
    {b : (ℝ≥0 × (I → ℝ)) → I → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C) (y : I → Path) (i : I) (t : ℝ≥0) :
    y i t = innovation b hb C hbound y i t +
      ∫ s in (0 : ℝ)..(t : ℝ), driftIntegrand b y i s := by
  simp [innovation, driftPrimitive]

theorem driftPrimitive_eq_of_agree {I : Type u_17}
    {b : (ℝ≥0 × (I → ℝ)) → I → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    {y z : I → Path} (t : ℝ≥0)
    (h : ∀ i s, s ≤ t → y i s = z i s) (i : I) :
    driftPrimitive b hb C hbound y i t = driftPrimitive b hb C hbound z i t := by
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Set.Icc (0 : ℝ) (t : ℝ) := by
    simpa only [Set.uIcc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] using hs
  have hst : s.toNNReal ≤ t := by
    exact_mod_cast (show (s.toNNReal : ℝ) ≤ (t : ℝ) by
      simpa [Real.toNNReal_of_nonneg hs'.1] using hs'.2)
  have heq : (fun j => y j s.toNNReal) = (fun j => z j s.toNNReal) :=
    funext (fun j => h j s.toNNReal hst)
  simp only [driftIntegrand, heq]

theorem innovation_eq_of_agree {I : Type u_18}
    {b : (ℝ≥0 × (I → ℝ)) → I → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    {y z : I → Path} (t : ℝ≥0)
    (h : ∀ i s, s ≤ t → y i s = z i s) (i : I) :
    innovation b hb C hbound y i t = innovation b hb C hbound z i t := by
  change y i t - driftPrimitive b hb C hbound y i t =
    z i t - driftPrimitive b hb C hbound z i t
  rw [h i t le_rfl, driftPrimitive_eq_of_agree hb C hbound t h i]

def stoppedPath (t : ℝ≥0) (y : Path) : Path :=
  ⟨fun s => y (min s t), y.continuous.comp (continuous_id.min continuous_const)⟩

abbrev rawHistory {Ω : Type u_19} {I : Type u_20} (Y : Ω → I → Path) (t : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ i : I, ⨆ s : ℝ≥0, ⨆ (_ : s ≤ t),
    MeasurableSpace.comap (fun ω => Y ω i s) inferInstance

theorem measurable_rawHistory_eval {Ω : Type u_21} {I : Type u_22} (Y : Ω → I → Path)
    (t s : ℝ≥0) (hs : s ≤ t) (i : I) :
    @Measurable Ω ℝ (rawHistory Y t) _ (fun ω => Y ω i s) := by
  apply Measurable.of_comap_le
  exact le_iSup_of_le i (le_iSup_of_le s (le_iSup_of_le hs le_rfl))

theorem measurable_stoppedFamily_rawHistory {Ω : Type u_23} {I : Type u_24} (Y : Ω → I → Path)
    (t : ℝ≥0) :
    @Measurable Ω (I → Path) (rawHistory Y t) _
      (fun ω i => stoppedPath t (Y ω i)) := by
  let : MeasurableSpace Ω := rawHistory Y t
  refine Measurable.of_eval (fun i => ?_)
  apply measurable_path_iff.mpr
  intro s
  exact measurable_rawHistory_eval Y t (min s t) (min_le_right _ _) i

theorem rawHistory_mono {Ω : Type u_25} {I : Type u_26} (Y : Ω → I → Path)
    {s t : ℝ≥0} (hst : s ≤ t) : rawHistory Y s ≤ rawHistory Y t := by
  refine iSup_le (fun i => iSup_le (fun u => iSup_le (fun hus => ?_)))
  exact le_iSup_of_le i (le_iSup_of_le u (le_iSup_of_le (hus.trans hst) le_rfl))

theorem rawHistory_le {Ω : Type u_27} {I : Type u_28} [MeasurableSpace Ω]
    {Y : Ω → I → Path} (hY : Measurable Y) (t : ℝ≥0) :
    rawHistory Y t ≤ ‹MeasurableSpace Ω› := by
  refine iSup_le (fun i => iSup_le (fun s => iSup_le (fun _ => ?_)))
  exact ((continuous_eval_const s).measurable.comp
    ((measurable_pi_apply i).comp hY)).comap_le

theorem measurable_innovation_eval_rawHistory {Ω : Type u_29} {I : Type u_30}
    {b : (ℝ≥0 × (I → ℝ)) → I → ℝ} (hb : Measurable b)
    (C : ℝ) (hbound : ∀ p i, |b p i| ≤ C)
    (Y : Ω → I → Path) (t : ℝ≥0) (i : I) :
    @Measurable Ω ℝ (rawHistory Y t) _
      (fun ω => innovation b hb C hbound (Y ω) i t) := by
  let : MeasurableSpace Ω := rawHistory Y t
  have hm : Measurable (fun ω =>
      innovation b hb C hbound (fun j => stoppedPath t (Y ω j)) i t) :=
    (measurable_path_iff.mp
      ((measurable_pi_apply i).comp (measurable_innovation hb C hbound)) t).comp
        (measurable_stoppedFamily_rawHistory Y t)
  convert hm using 1
  funext ω
  apply innovation_eq_of_agree hb C hbound t
  intro j s hs
  simp [stoppedPath, min_eq_left hs]

end Problem336AdditiveD139.PathRealization

end

end OAI
