import Mathlib

namespace OAI

universe u_1 u_2

noncomputable section

open MeasureTheory
open scoped Topology NNReal

attribute [local instance] Measure.Subtype.measureSpace

namespace Problem336AdditiveD139.InnovationAdapted

variable {Ω : Type u_1} {I : Type u_2} {mΩ : MeasurableSpace Ω}

theorem measurable_history_coordinates
    (H : Filtration ℝ mΩ) (Y : ℝ → Ω → I → ℝ)
    (hY : ∀ i, Adapted H (fun t ω => Y t ω i))
    (hcont : ∀ ω i, Continuous (fun t => Y t ω i)) (T : ℝ) :
    Measurable[Subtype.instMeasurableSpace.prod (H T)]
      (fun p : Set.Iic T × Ω => Y p.1 p.2) := by
  let : MeasurableSpace Ω := H T
  apply Measurable.of_eval
  intro i
  exact ((hY i).stronglyAdapted.isStronglyProgressive_of_continuous
    (fun ω => hcont ω i) T).measurable

theorem progressive_drift
    (H : Filtration ℝ mΩ) (Y : ℝ → Ω → I → ℝ)
    (hY : ∀ i, Adapted H (fun t ω => Y t ω i))
    (hcont : ∀ ω i, Continuous (fun t => Y t ω i))
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (i : I) : IsProgressive H (fun t ω => b t (Y t ω) i) := by
  intro T
  exact (hb i).comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_history_coordinates H Y hY hcont T))

theorem measurable_intervalIntegral_of_history
    (m : MeasurableSpace Ω) (f : ℝ → Ω → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hf : Measurable[Subtype.instMeasurableSpace.prod m]
      (fun p : Set.Iic T × Ω => f p.1 p.2)) :
    Measurable[m] (fun ω => ∫ s in (0 : ℝ)..T, f s ω) := by
  let : MeasurableSpace Ω := m
  have hsub : Measurable (fun p : Set.Ioc (0 : ℝ) T × Ω =>
      ((⟨p.1.1, p.1.2.2⟩ : Set.Iic T), p.2)) := by
    exact ((measurable_subtype_coe.comp measurable_fst).subtype_mk).prodMk measurable_snd
  have hjoint : Measurable (fun p : Set.Ioc (0 : ℝ) T × Ω => f p.1 p.2) :=
    hf.comp hsub
  let : IsFiniteMeasure (volume : Measure (Set.Ioc (0 : ℝ) T)) :=
    ⟨by rw [Measure.Subtype.volume_univ measurableSet_Ioc.nullMeasurableSet]; simp⟩
  have hint : Measurable (fun ω => ∫ s : Set.Ioc (0 : ℝ) T, f s ω) :=
    hjoint.stronglyMeasurable.integral_prod_left'.measurable
  convert hint using 1
  funext ω
  rw [intervalIntegral.integral_of_le hT]
  exact (integral_subtype measurableSet_Ioc (fun s => f s ω)).symm

theorem measurable_driftIntegral
    (H : Filtration ℝ mΩ) (Y : ℝ → Ω → I → ℝ)
    (hY : ∀ i, Adapted H (fun t ω => Y t ω i))
    (hcont : ∀ ω i, Continuous (fun t => Y t ω i))
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (i : I) (T : ℝ) (hT : 0 ≤ T) :
    Measurable[H T] (fun ω => ∫ s in (0 : ℝ)..T, b s (Y s ω) i) :=
  measurable_intervalIntegral_of_history (H T) _ T hT
    (progressive_drift H Y hY hcont b hb i T)

theorem measurable_innovation
    (H : Filtration ℝ mΩ) (Y : ℝ → Ω → I → ℝ)
    (hY : ∀ i, Adapted H (fun t ω => Y t ω i))
    (hcont : ∀ ω i, Continuous (fun t => Y t ω i))
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (i : I) (T : ℝ) (hT : 0 ≤ T) :
    Measurable[H T] (fun ω => Y T ω i - ∫ s in (0 : ℝ)..T, b s (Y s ω) i) :=
  (hY i T).sub (measurable_driftIntegral H Y hY hcont b hb i T hT)

theorem measurable_innovation_increment
    (H : Filtration ℝ mΩ) (Y : ℝ → Ω → I → ℝ)
    (hY : ∀ i, Adapted H (fun t ω => Y t ω i))
    (hcont : ∀ ω i, Continuous (fun t => Y t ω i))
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (i : I) (u v T : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huT : u ≤ T) (hvT : v ≤ T) :
    Measurable[H T] (fun ω =>
      (Y v ω i - ∫ s in (0 : ℝ)..v, b s (Y s ω) i) -
      (Y u ω i - ∫ s in (0 : ℝ)..u, b s (Y s ω) i)) := by
  exact ((measurable_innovation H Y hY hcont b hb i v hv).mono
    (H.mono hvT) le_rfl).sub
    ((measurable_innovation H Y hY hcont b hb i u hu).mono (H.mono huT) le_rfl)

theorem intervalIntegrable_drift
    (Y : ℝ → I → ℝ) (hY : ∀ i, Continuous (fun t => Y t i))
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (C : ℝ) (hbound : ∀ t y i, |b t y i| ≤ C) (i : I) (u v : ℝ) :
    IntervalIntegrable (fun t => b t (Y t) i) volume u v := by
  have hm : Measurable (fun t => b t (Y t) i) :=
    (hb i).comp (measurable_id.prodMk (Measurable.of_eval (fun j => (hY j).measurable)))
  rw [intervalIntegrable_iff]
  exact IntegrableOn.of_bound (by simp [Set.uIoc]) hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun t => by simpa only [Real.norm_eq_abs] using hbound t (Y t) i))

theorem continuous_driftIntegral
    (Y : ℝ → I → ℝ) (hY : ∀ i, Continuous (fun t => Y t i))
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (C : ℝ) (hbound : ∀ t y i, |b t y i| ≤ C) (i : I) :
    Continuous (fun t => ∫ s in (0 : ℝ)..t, b s (Y s) i) :=
  intervalIntegral.continuous_primitive
    (fun u v => intervalIntegrable_drift Y hY b hb C hbound i u v) 0

theorem continuous_innovation
    (Y : ℝ → I → ℝ) (hY : ∀ i, Continuous (fun t => Y t i))
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (C : ℝ) (hbound : ∀ t y i, |b t y i| ≤ C) (i : I) :
    Continuous (fun t => Y t i - ∫ s in (0 : ℝ)..t, b s (Y s) i) :=
  (hY i).sub (continuous_driftIntegral Y hY b hb C hbound i)

def nonnegativeTimeExtension (H : Filtration ℝ≥0 mΩ) : Filtration ℝ mΩ where
  seq t := H t.toNNReal
  mono' := fun _ _ h => H.mono (Real.toNNReal_mono h)
  le' t := H.le t.toNNReal

theorem measurable_innovation_nnreal
    (H : Filtration ℝ≥0 mΩ) (Y : ℝ≥0 → Ω → I → ℝ)
    (hY : ∀ i, Adapted H (fun t ω => Y t ω i))
    (hcont : ∀ ω i, Continuous (fun t => Y t ω i))
    (b : ℝ → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1 p.2 i))
    (i : I) (T : ℝ≥0) :
    Measurable[H T] (fun ω => Y T ω i -
      ∫ s in (0 : ℝ)..(T : ℝ), b s (Y s.toNNReal ω) i) := by
  have h := measurable_innovation (nonnegativeTimeExtension H)
    (fun t => Y t.toNNReal) (fun i t => hY i t.toNNReal)
    (fun ω i => (hcont ω i).comp continuous_real_toNNReal) b hb i T T.property
  change Measurable[H (T : ℝ).toNNReal] (fun ω => Y (T : ℝ).toNNReal ω i -
    ∫ s in (0 : ℝ)..(T : ℝ), b s (Y s.toNNReal ω) i) at h
  rw [Real.toNNReal_coe] at h
  exact h

end Problem336AdditiveD139.InnovationAdapted

end

end OAI
