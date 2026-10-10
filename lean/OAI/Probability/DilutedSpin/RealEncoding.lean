import OAI.Probability.DilutedSpin.FiniteHierarchyDense
import OAI.Probability.DilutedSpin.ProductTower
import OAI.Probability.DilutedSpin.TrialPhysical

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable def mapModel {p : ℕ} (M : Model p) (T : InteractionSample p → InteractionSample p)
    (g : ℝ → ℝ) (hT : Measurable T) (hg : Measurable g) : Model p where
  alpha := M.alpha
  disorder := ⟨Measure.map T M.disorder.toMeasure,
    (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).mpr inferInstance⟩
  field := ⟨Measure.map g M.field.toMeasure,
    (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).mpr inferInstance⟩

lemma mapModel_interaction_integrable {p : ℕ} (M : Model p)
    (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g)
    (hi : Integrable (fun z => ‖(T z).1‖) M.disorder.toMeasure) :
    Integrable (fun z : InteractionSample p => ‖z.1‖) (mapModel M T g hT hg).disorder.toMeasure := by
  change Integrable (fun z : InteractionSample p => ‖z.1‖) (Measure.map T M.disorder.toMeasure)
  exact (integrable_map_measure (by fun_prop) hT.aemeasurable).mpr hi

lemma mapModel_field_integrable {p : ℕ} (M : Model p)
    (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g)
    (hi : Integrable (fun z => |g z|) M.field.toMeasure) :
    Integrable (fun z : ℝ => |z|) (mapModel M T g hT hg).field.toMeasure := by
  change Integrable (fun z : ℝ => |z|) (Measure.map g M.field.toMeasure)
  exact (integrable_map_measure (by fun_prop) hg.aemeasurable).mpr hi

lemma integral_pi_map {ι X Y : Type} [Fintype ι] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (g : X → Y) (hg : Measurable g)
    (F : (ι → Y) → ℝ) (hF : Measurable F) :
    (∫ y,F y ∂Measure.pi (fun _ : ι => Measure.map g μ)) =
      ∫ x,F (fun i => g (x i)) ∂Measure.pi (fun _ : ι => μ) := by
  let : IsProbabilityMeasure (Measure.map g μ) :=
    (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).mpr inferInstance
  rw [← Measure.pi_map_pi (fun _ : ι => hg.aemeasurable)]
  exact integral_map (Measurable.of_eval (fun index => hg.comp (measurable_pi_apply index))).aemeasurable hF.aestronglyMeasurable

lemma indexAverage_mapModel {p N k : ℕ} (M : Model p)
    (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g) (θ : Fin k → InteractionSample p) :
    fieldAverage (N := N) (mapModel M T g hT hg) θ =
      ∫ h : Fin N → ℝ,indexAverage θ (fun i => g (h i)) ∂Measure.pi (fun _ : Fin N => M.field.toMeasure) := by
  change (∫ h : Fin N → ℝ,indexAverage θ h ∂Measure.pi (fun _ : Fin N => Measure.map g M.field.toMeasure))=_
  exact integral_pi_map _ g hg _ (continuous_indexAverage.comp (continuous_const.prodMk continuous_id)).measurable

lemma pressure_mapModel {p : ℕ} (M : Model p)
    (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g) (N : ℕ) :
    pressure (mapModel M T g hT hg) N =
      (∫ k : ℕ,∫ θ : Fin k → InteractionSample p,∫ h : Fin N → ℝ,
        indexAverage (fun j => T (θ j)) (fun i => g (h i))
        ∂Measure.pi (fun _ : Fin N => M.field.toMeasure)
        ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) ∂poissonMeasure (M.alpha*N))/N := by
  change (∫ k : ℕ,∫ θ : Fin k → InteractionSample p,fieldAverage (mapModel M T g hT hg) θ
    ∂Measure.pi (fun _ : Fin k => Measure.map T M.disorder.toMeasure) ∂poissonMeasure (M.alpha*N))/N=_
  congr 1
  apply integral_congr_ae
  filter_upwards [] with k
  rw [integral_pi_map _ T hT _ (stronglyMeasurable_fieldAverage (mapModel M T g hT hg) N k).measurable]
  apply integral_congr_ae
  filter_upwards [] with θ
  exact indexAverage_mapModel M T g hT hg _

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators
local instance hierarchyTranslationMeasurableSpace (space : TopCat) : MeasurableSpace space := borel space
local instance hierarchyTranslationBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

lemma logMean_add_constant {ι : Type} [Fintype ι] (r : ℕ)
    (g : (ι → ℝ) → ℝ) (hg : Continuous g) {B : ℝ} (hB : ∀ x, |g x|≤B)
    (m : Fin r → ℝ) (hm : ∀ i,0 < m i) (a : ℝ) (eta : ι → Hierarchy r) :
    logMean r (fun x => g x+a) m eta=logMean r g m eta+a := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [logMean,ih (fun i => m i.succ) (fun i => hm i.succ)]
    obtain ⟨hc,hb⟩ := logMean_continuous_bound r g hg hB (fun i => m i.succ) (fun i => hm i.succ)
    exact MeasureMean.logMean_add_const (ProbabilityMeasure.pi eta).toMeasure (hm 0).ne' hc.measurable hb a

lemma trialLog_add_constant {ι : Type} [Fintype ι] (r : ℕ)
    (g : (ι → ℝ) → ℝ) (hg : Continuous g) {B : ℝ} (hB : ∀ x, |g x|≤B)
    (m : Fin r → ℝ) (hm : ∀ i,0 < m i) (a : ℝ) (ζ : Hierarchy (r+1)) :
    trialLog r ζ m (fun x => g x+a)=trialLog r ζ m g+a := by
  unfold trialLog
  simp_rw [logMean_add_constant r g hg hB m hm a]
  obtain ⟨hc,hb⟩ := logMean_continuous_bound r g hg hB m hm
  let μ : ProbabilityMeasure (ι → Hierarchy r) := ProbabilityMeasure.pi (fun _ : ι => ζ)
  change (∫ x,logMean r g m x+a ∂μ.toMeasure)=(∫ x,logMean r g m x ∂μ.toMeasure)+a
  rw [integral_add (MeasureMean.bounded_integrable μ.toMeasure hc.measurable hb) (integrable_const a)]
  simp
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory Set TopologicalSpace
open scoped BigOperators NNReal
local instance realEncodingMeasurableSpace (space : TopCat) : MeasurableSpace space := borel space
local instance realEncodingBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

namespace FiniteLaw
lemma asProbability_map {Ω Λ X : Type} [Fintype Ω] [Fintype Λ]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [MetrizableSpace X]
    (P : FiniteLaw Ω) (f : Ω → Λ) (v : Λ → X) :
    (P.map f).asProbability v = P.asProbability (fun x => v (f x)) := by
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  apply Subtype.ext
  change ((P.map f).asProbability v).toMeasure = (P.asProbability (fun x => v (f x))).toMeasure
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  simp only [integral_asProbability,expect_map]
end FiniteLaw

namespace KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

/-- Literal messages at leaves, with no spin terminal transition. -/
noncomputable def realEncode : (r : ℕ) → KernelTower Ω r →
    (FinitePath Ω r → ℝ) → Hierarchy r
  | 0,_,V => V ()
  | r+1,T,V => T.1.asProbability (fun a => realEncode r (T.2 a) (fun y => V (a,y)))

/-- Pad a finite conditional law along an injection with a specified retraction.
Off-support children are harmless but are specified, rather than postulated. -/
noncomputable def embed (f : Ω → Λ) (g : Λ → Ω) : (r : ℕ) →
    KernelTower Ω r → KernelTower Λ r
  | 0,_ => ()
  | r+1,T => (T.1.map f, fun a => embed f g r (T.2 (g a)))

lemma realEncode_embed (f : Ω → Λ) (g : Λ → Ω)
    (h : Function.LeftInverse g f) (r : ℕ) (T : KernelTower Ω r)
    (V : FinitePath Ω r → ℝ) :
    realEncode r (embed f g r T) (fun y => V (pathMap g r y)) = realEncode r T V := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change FiniteLaw Ω × (Ω → KernelTower Ω r) at T
    change (Ω × FinitePath Ω r) → ℝ at V
    rcases T with ⟨P,Q⟩
    let : MetrizableSpace (Hierarchy r) := (hierarchy_properties r).1
    change (P.map f).asProbability (fun a => realEncode r (embed f g r (Q (g a)))
      (fun y => V (g a,pathMap g r y))) =
      P.asProbability (fun a => realEncode r (Q a) (fun y => V (a,y)))
    have hc (a : Λ) := ih (Q (g a)) (fun y => V (g a,y))
    simp_rw [hc]
    rw [FiniteLaw.asProbability_map]
    congr 1
    funext a
    rw [h a]

lemma backwardLog_realEncode {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : ι → Type} [∀ i,Fintype (α i)] (r : ℕ)
    (T : (i : ι) → KernelTower (α i) r) (V : (i : ι) → FinitePath (α i) r → ℝ)
    (F : (ι → ℝ) → ℝ) (m : Fin r → ℝ) :
    backwardLog r (pi r T) m (fun y => F (fun i => V i (FinitePath.proj r y i))) =
      DilutedSpinGlass.logMean r F m (fun i => realEncode r (T i) (V i)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (i : ι) → FiniteLaw (α i) × (α i → KernelTower (α i) r) at T
    change (i : ι) → (α i × FinitePath (α i) r) → ℝ at V
    change (FiniteLaw.pi (fun i => (T i).1)).logMean (m 0)
      (fun a => backwardLog r (pi r (fun i => (T i).2 (a i))) (fun j => m j.succ)
        (fun y => F (fun i => V i (a i,FinitePath.proj r y i)))) =
      Real.log (∫ x, Real.exp (m 0 * DilutedSpinGlass.logMean r F (fun j => m j.succ) x)
        ∂Measure.pi (fun i => ((T i).1.asProbability
          (fun a => realEncode r ((T i).2 a) (fun y => V i (a,y)))).toMeasure)) / m 0
    have hc (a : (i : ι) → α i) := ih (fun i => (T i).2 (a i))
      (fun i y => V i (a i,y)) (fun j => m j.succ)
    simp_rw [hc]
    change Real.log ((FiniteLaw.pi (fun i => (T i).1)).expect (fun a =>
      Real.exp (m 0 * DilutedSpinGlass.logMean r F (fun j => m j.succ)
        (fun i => realEncode r ((T i).2 (a i)) (fun y => V i (a i,y)))))) / m 0 =
      Real.log (∫ x, Real.exp (m 0 * DilutedSpinGlass.logMean r F (fun j => m j.succ) x)
        ∂Measure.pi (fun i => ((T i).1.asProbability
          (fun a => realEncode r ((T i).2 a) (fun y => V i (a,y)))).toMeasure)) / m 0
    rw [FiniteLaw.integral_pi_asProbability]

end KernelTower

/-- Every genuinely finitely branching measure hierarchy has a finite alphabet
realization. Padding changes no law; in particular this imposes no restriction
on the original variational class after density. -/
lemma finiteHierarchy_realization (r : ℕ) (ζ : Hierarchy r) (hζ : FiniteHierarchy r ζ) :
    ∃ (n : ℕ) (_hn : 0 < n) (T : KernelTower (Fin n) r) (V : FinitePath (Fin n) r → ℝ),
      KernelTower.realEncode r T V = ζ := by
  classical
  induction r with
  | zero => exact ⟨1,by omega,(),fun _ => ζ,rfl⟩
  | succ r ih =>
    obtain ⟨k,x,w,hx,rfl⟩ := hζ
    choose n hn T V hV using fun i => ih (x i) (hx i)
    let P : FiniteLaw (Fin k) := ⟨fun i => w.val i,fun i => (w.val i).coe_nonneg,
      by simpa only [NNReal.coe_sum,NNReal.coe_one] using congrArg ((↑) : ℝ≥0 → ℝ) w.property⟩
    have hk : 0 < k := by
      by_contra hk
      have hk0 : k=0 := by omega
      subst k
      have hh := P.total
      simp at hh
    let : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
    let (i : Fin k) : Nonempty (Fin (n i)) := ⟨⟨0,hn i⟩⟩
    let d : (i : Fin k) → Fin (n i) := fun i => ⟨0,hn i⟩
    let Ω := Fin k × ((i : Fin k) → Fin (n i))
    let f (i : Fin k) (a : Fin (n i)) : Ω := (i,Function.update d i a)
    let g (i : Fin k) (a : Ω) : Fin (n i) := a.2 i
    have hgf (i : Fin k) : Function.LeftInverse (g i) (f i) := by
      intro a
      exact Function.update_self i a d
    let U : KernelTower Ω (r+1) :=
      (P.map (fun i => (i,d)), fun a => KernelTower.embed (f a.1) (g a.1) r (T a.1))
    let W : FinitePath Ω (r+1) → ℝ := fun y =>
      V y.1.1 (KernelTower.pathMap (g y.1.1) r y.2)
    have hU : KernelTower.realEncode (r+1) U W = atomicProbability x w := by
      let : MetrizableSpace (Hierarchy r) := (hierarchy_properties r).1
      change (P.map (fun i => (i,d))).asProbability (fun a =>
        KernelTower.realEncode r (KernelTower.embed (f a.1) (g a.1) r (T a.1))
          (fun y => V a.1 (KernelTower.pathMap (g a.1) r y))) = _
      simp_rw [KernelTower.realEncode_embed _ _ (hgf _),hV]
      rw [FiniteLaw.asProbability_map]
      congr 1
    let e := Fintype.equivFin Ω
    refine ⟨Fintype.card Ω,Fintype.card_pos,
      KernelTower.embed e e.symm (r+1) U,
      fun y => W (KernelTower.pathMap e.symm (r+1) y),?_⟩
    rw [KernelTower.realEncode_embed e e.symm e.symm_apply_apply]
    exact hU

end DilutedSpinGlass

end

end OAI
