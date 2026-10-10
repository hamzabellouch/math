import Mathlib
import OAI.Probability.Ballisticity.Stationary.Array
import OAI.Probability.Ballisticity.Estimates.BudgetNormalize

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

def horizontalProjection {d : ℕ} (e : Direction d) (x : Lattice d) : HorizontalSpace e :=
  ⟨Function.update x e.1 0, by simp [horizontalSubgroup]⟩

def horizontalLift {d : ℕ} (e : Direction d) (h : ℤ) (z : HorizontalSpace e) : Lattice d :=
  z.val+h • step e

lemma signedHeight_horizontalLift {d : ℕ} (e : Direction d) (h : ℤ) (z : HorizontalSpace e) :
    signedHeight e (horizontalLift e h z)=h := by
  have hz : z.val e.1=0 := z.property
  rw [horizontalLift,signedHeight_add,signedHeight_zsmul_step]
  simp [signedHeight,hz]

lemma horizontalProjection_lift {d : ℕ} (e : Direction d) (h : ℤ) (z : HorizontalSpace e) :
    horizontalProjection e (horizontalLift e h z)=z := by
  apply Subtype.ext
  funext i
  by_cases hi : i=e.1
  · subst i
    have hz : z.val e.1=0 := z.property
    simp [horizontalProjection,hz]
  · simp [horizontalProjection,horizontalLift,step,hi]

lemma horizontalLift_projection {d : ℕ} (e : Direction d) (x : Lattice d) :
    horizontalLift e (signedHeight e x) (horizontalProjection e x)=x := by
  funext i
  by_cases hi : i=e.1
  · subst i
    simp only [horizontalLift,horizontalProjection,Pi.add_apply,Function.update_self,
      Pi.smul_apply,step,ite_true,zero_add,smul_eq_mul,signedHeight]
    split <;> simp_all
  · simp [horizontalLift,horizontalProjection,step,hi]

def heightHorizontalEquiv {d : ℕ} (e : Direction d) : Lattice d ≃ ℤ×HorizontalSpace e where
  toFun x := (signedHeight e x,horizontalProjection e x)
  invFun p := horizontalLift e p.1 p.2
  left_inv := horizontalLift_projection e
  right_inv p := by simp [signedHeight_horizontalLift,horizontalProjection_lift]

noncomputable def globalEndpointProfile {d : ℕ} (e : Direction d) (H : ℕ)
    (ω : Environment d) : Measure (Lattice d) :=
  normalizeOr (variableHitKernel (realPosition (step e)) H (ω,0))
    (Measure.dirac (H • step e))

instance globalEndpointProfile_probability {d : ℕ} (e : Direction d) (H : ℕ) (ω : Environment d) :
    IsProbabilityMeasure (globalEndpointProfile e H ω) := normalizeOr_probability _ _

lemma globalEndpointProfile_measurable_below {d : ℕ} (e : Direction d) (H : ℕ) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) H)) _ (globalEndpointProfile e H) := by
  let : MeasurableSpace (Environment d) := rowSigma (BelowHeight (realPosition (step e)) H)
  apply measurable_normalizeOr _ _ _ measurable_const
  have hm := measurable_rawWordLaw_rows (realPosition (step e)) H (0:Lattice d)
  have hS : Strip (realPosition (step e)) (0:Lattice d) H⊆BelowHeight (realPosition (step e)) H := by
    intro x hx
    simpa [Strip,BelowHeight,dot,realPosition] using hx.2
  have hmap := (Measure.measurable_map (fun w : List (Direction d) => wordPath (0:Lattice d) w w.length)
      (measurable_of_countable _)).comp (hm.mono (rowSigma_mono hS) le_rfl)
  simpa only [Function.comp_def,rawWordLaw_endpoint] using hmap

lemma globalEndpointProfile_mass {d : ℕ} (e : Direction d) (H : ℕ) (ω : Environment d) :
    crossingQuenched (realPosition (step e)) 0 H ω • globalEndpointProfile e H ω=
      variableHitKernel (realPosition (step e)) H (ω,0) := by
  have he : crossingQuenched (realPosition (step e)) 0 H ω=
      variableHitKernel (realPosition (step e)) H (ω,0) Set.univ := by
    simpa only [variableHitKernel,Kernel.coe_mk] using crossingQuenched_eq_hitKernel (realPosition (step e)) 0 H ω
  rw [he]
  exact normalizeOr_mass _ _

lemma globalEndpointProfile_normalized {d : ℕ} (e : Direction d) (H : ℕ) (ω : Environment d)
    (h : crossingQuenched (realPosition (step e)) 0 H ω≠0) :
    globalEndpointProfile e H ω=normalizedMeasure (variableHitKernel (realPosition (step e)) H (ω,0)) := by
  unfold globalEndpointProfile normalizeOr
  have he : variableHitKernel (realPosition (step e)) H (ω,0) Set.univ≠0 := by
    simpa only [variableHitKernel,Kernel.coe_mk,←crossingQuenched_eq_hitKernel] using h
  exact ite_eq_right he

noncomputable def globalHorizontalProfile {d : ℕ} (e : Direction d) (H : ℕ) (ω : Environment d) :
    Measure (HorizontalSpace e) := (globalEndpointProfile e H ω).map (horizontalProjection e)

instance globalHorizontalProfile_probability {d : ℕ} (e : Direction d) (H : ℕ) (ω : Environment d) :
    IsProbabilityMeasure (globalHorizontalProfile e H ω) :=
  inferInstanceAs (IsProbabilityMeasure ((globalEndpointProfile e H ω).map (horizontalProjection e)))

lemma globalHorizontalProfile_measurable_below {d : ℕ} (e : Direction d) (H : ℕ) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) H)) _ (globalHorizontalProfile e H) :=
  (Measure.measurable_map _ (measurable_of_countable _)).comp (globalEndpointProfile_measurable_below e H)

lemma globalHorizontalProfile_measurable {d : ℕ} (e : Direction d) (H : ℕ) :
    Measurable (globalHorizontalProfile e H) :=
  (globalHorizontalProfile_measurable_below e H).mono (rowSigma_le _) le_rfl

noncomputable def globalHorizontalCoordinate {d : ℕ} (e : Direction d) (H : ℕ)
    (ω : Environment d) (z : HorizontalSpace e) : Set.Icc (0:ℝ) 1 :=
  ⟨(globalHorizontalProfile e H ω {z}).toReal, ENNReal.toReal_nonneg,
    ENNReal.toReal_le_of_le_ofReal (by exact_mod_cast (zero_le_one: (0:ℝ)≤1)) (by simpa using prob_le_one (μ:=globalHorizontalProfile e H ω) (s:={z}))⟩

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped ENNReal Classical BigOperators
namespace DirectionalTransience.AnchorSampling

variable {D I : Type*} {X : I → Type*}
  [MeasurableSpace D] [∀ i, MeasurableSpace (X i)]

lemma measurable_infinitePi (μ : D → (i : I) → Measure (X i))
    (hm : ∀ i, Measurable fun d => μ d i)
    [∀ d i, IsProbabilityMeasure (μ d i)] :
    Measurable (fun d => Measure.infinitePi (μ d)) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ => isPiSystem_measurableSet) (by simp))
  rintro _ ⟨s,t,ht,rfl⟩
  have htm : ∀ i, MeasurableSet (t i) := by simpa only [Set.mem_univ_pi,Set.mem_ofPred_eq] using ht
  simp_rw [Measure.infinitePi_pi _ (fun i _ => htm i)]
  exact Finset.measurable_fun_prod s (fun i _ => (Measure.measurable_coe (htm i)).comp (hm i))

noncomputable def anchorKernel {H : Type*} [MeasurableSpace H]
    (μ : D → ℤ → Measure H) (hm : ∀ i, Measurable fun d => μ d i)
    [∀ d i, IsProbabilityMeasure (μ d i)] : Kernel D ((ℤ×ℕ) → H) where
  toFun d := Measure.infinitePi (fun p : ℤ×ℕ => μ d p.1)
  measurable' := measurable_infinitePi _ fun p => hm p.1

instance anchorKernel_markov {H : Type*} [MeasurableSpace H]
    (μ : D → ℤ → Measure H) (hm : ∀ i, Measurable fun d => μ d i)
    [∀ d i, IsProbabilityMeasure (μ d i)] : IsMarkovKernel (anchorKernel μ hm) where
  isProbabilityMeasure d := by
    change IsProbabilityMeasure (Measure.infinitePi (fun p : ℤ×ℕ => μ d p.1))
    infer_instance

lemma anchorKernel_cylinder {H : Type*} [MeasurableSpace H]
    (μ : D → ℤ → Measure H) (hm : ∀ i, Measurable fun d => μ d i)
    [∀ d i, IsProbabilityMeasure (μ d i)] (d : D)
    (s : Finset (ℤ×ℕ)) (t : ℤ×ℕ → Set H) (ht : ∀ p∈s, MeasurableSet (t p)) :
    anchorKernel μ hm d (Set.pi s t) = ∏ p∈s, μ d p.1 (t p) :=
  Measure.infinitePi_pi _ ht

end DirectionalTransience.AnchorSampling

end

end OAI
