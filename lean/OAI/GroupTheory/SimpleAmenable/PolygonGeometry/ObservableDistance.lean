import Mathlib

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ObservableDistance
open Classical MeasureTheory Set

def ObservableClose {X : Type*} [MeasurableSpace X] (μ ν : Measure X) (ε : ℝ) : Prop :=
  ∀f : X → ℝ,Measurable f → (∀x,f x∈Icc (0:ℝ) 1) →
    |(∫x,f x ∂μ)-(∫x,f x ∂ν)| ≤ ε

theorem boundedObservable_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Measurable f) (hb : ∀x,f x∈Icc (0:ℝ) 1) : Integrable f μ := by
  apply (integrable_const (1:ℝ)).mono' hf.aestronglyMeasurable
  filter_upwards with x
  simpa only [Real.norm_eq_abs,abs_of_nonneg (hb x).1] using (hb x).2

theorem ObservableClose.mono {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} {ε δ : ℝ} (h : ObservableClose μ ν ε) (he : ε ≤ δ) :
    ObservableClose μ ν δ := fun f hf hb => (h f hf hb).trans he

theorem ObservableClose.symm {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} {ε : ℝ} (h : ObservableClose μ ν ε) :
    ObservableClose ν μ ε := by
  intro f hf hb
  rw [abs_sub_comm]
  exact h f hf hb

theorem ObservableClose.map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ ν : Measure X} {ε : ℝ} (h : ObservableClose μ ν ε) {g : X → Y} (hg : Measurable g) :
    ObservableClose (μ.map g) (ν.map g) ε := by
  intro f hf hb
  rw [integral_map hg.aemeasurable hf.aestronglyMeasurable,
    integral_map hg.aemeasurable hf.aestronglyMeasurable]
  exact h (f ∘ g) (hf.comp hg) (fun x => hb (g x))

theorem ObservableClose.event {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {ε : ℝ} (h : ObservableClose μ ν ε) {s : Set X} (hs : MeasurableSet s) :
    |μ.real s-ν.real s| ≤ ε := by
  have hh := h (s.indicator (fun _ => (1:ℝ))) (measurable_const.indicator hs) (by
    intro x
    by_cases hx : x∈s <;> simp [hx])
  simpa only [integral_indicator hs,integral_const,smul_eq_mul,mul_one,Measure.real,Measure.restrict_apply_univ] using hh

theorem ObservableClose.prod_right {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ρ : Measure Y) [IsProbabilityMeasure ρ] {ε : ℝ} (h : ObservableClose μ ν ε) :
    ObservableClose (μ.prod ρ) (ν.prod ρ) ε := by
  intro f hf hb
  have hiμ := boundedObservable_integrable (μ.prod ρ) hf hb
  have hiν := boundedObservable_integrable (ν.prod ρ) hf hb
  rw [integral_prod f hiμ,integral_prod f hiν]
  apply h (fun x => ∫y,f (x,y) ∂ρ)
  · have hh : StronglyMeasurable (Function.uncurry (fun (x : X) (y : Y) => f (x,y))) :=
      hf.stronglyMeasurable
    exact hh.integral_prod_right.measurable
  · intro x
    refine ⟨integral_nonneg (fun y => (hb (x,y)).1),?_⟩
    have hi := boundedObservable_integrable ρ (hf.comp (measurable_const.prodMk measurable_id))
      (fun y => hb (x,y))
    calc
      _ ≤ ∫_ : Y,(1:ℝ) ∂ρ := integral_mono hi (integrable_const 1) (fun y => (hb (x,y)).2)
      _ = 1 := by simp

theorem observableClose_of_density {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {p q : X → ℝ} (hp : Measurable p) (hq : Measurable q)
    (hp₀ : ∀x,0 ≤ p x) (hq₀ : ∀x,0 ≤ q x)
    (hip : Integrable p μ) (hiq : Integrable q μ) :
    ObservableClose (μ.withDensity (fun x => ENNReal.ofReal (p x)))
      (μ.withDensity (fun x => ENNReal.ofReal (q x))) (∫x,|p x-q x| ∂μ) := by
  intro f hf hb
  have hb' : ∀ᵐx ∂μ,‖f x‖ ≤ (1:ℝ) := ae_of_all _ (fun x => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hb x).1] using (hb x).2)
  have hipf := hip.mul_bdd hf.aestronglyMeasurable hb'
  have hiqf := hiq.mul_bdd hf.aestronglyMeasurable hb'
  rw [integral_withDensity_eq_integral_toReal_smul hp.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)),
    integral_withDensity_eq_integral_toReal_smul hq.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hp₀ _),ENNReal.toReal_ofReal (hq₀ _),smul_eq_mul]
  rw [← integral_sub hipf hiqf]
  calc
    _ ≤ ∫x,|p x*f x-q x*f x| ∂μ := abs_integral_le_integral_abs
    _ ≤ _ := by
      apply integral_mono (hipf.sub hiqf).abs (hip.sub hiq).abs
      intro x
      change |p x*f x-q x*f x| ≤ |p x-q x|
      rw [← sub_mul,abs_mul,abs_of_nonneg (hb x).1]
      exact mul_le_of_le_one_right (abs_nonneg _) (hb x).2

end ObservableDistance

section InfiniteSplit
open Classical MeasureTheory Set

theorem infinitePi_split {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (p : ι → Prop) :
    ((Measure.infinitePi (fun _ : Subtype p => μ)).prod
      (Measure.infinitePi (fun _ : Subtype (fun i => ¬p i) => μ))).map
        (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) p).symm=
      Measure.infinitePi (fun _ : ι => μ) := by
  apply Measure.eq_infinitePi
  intro s t ht
  let e := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) p).symm
  rw [Measure.map_apply e.measurable (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  have he (x : (Subtype p → X) × (Subtype (fun i => ¬p i) → X)) (i : ι) :
      e x i=(if h : p i then x.1 ⟨i,h⟩ else x.2 ⟨i,h⟩) := rfl
  have hpre : (e : _ → _) ⁻¹' ((s : Set ι).pi t)=
      ((s.subtype p : Set (Subtype p)).pi (fun i => t i.val)) ×ˢ
      ((s.subtype (fun i => ¬p i) : Set (Subtype (fun i => ¬p i))).pi (fun i => t i.val)) := by
    ext x
    simp only [mem_preimage,mem_pi,Finset.mem_coe,mem_prod,Finset.mem_subtype]
    constructor
    · intro h
      constructor
      · intro i hi
        simpa only [he,dite_eq_left i.property] using h i.val hi
      · intro i hi
        simpa only [he,dite_eq_right i.property] using h i.val hi
    · rintro ⟨h₁,h₂⟩ i hi
      by_cases hp : p i
      · simpa only [he,dite_eq_left hp] using h₁ ⟨i,hp⟩ hi
      · simpa only [he,dite_eq_right hp] using h₂ ⟨i,hp⟩ hi
  rw [hpre,Measure.prod_prod,Measure.infinitePi_pi (fun _ : Subtype p => μ) (fun i _ => ht i.val),
    Measure.infinitePi_pi (fun _ : Subtype (fun i => ¬p i) => μ) (fun i _ => ht i.val)]
  rw [Finset.prod_subtype_eq_prod_filter (s:=s) (p:=p) (fun i => μ (t i)),
    Finset.prod_subtype_eq_prod_filter (s:=s) (p:=fun i => ¬p i) (fun i => μ (t i))]
  exact Finset.prod_filter_mul_prod_filter_not s p (fun i => μ (t i))

end InfiniteSplit

end SimpleAmenable
end
end

end OAI
