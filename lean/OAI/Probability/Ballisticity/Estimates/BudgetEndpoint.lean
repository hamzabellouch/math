import Mathlib
import OAI.Probability.Ballisticity.Estimates.BudgetAdapted

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience
namespace TupleKernel

lemma countable_map_bind {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [Countable A] [Countable B] [Countable C]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] [MeasurableSingletonClass C]
    (μ : Measure A) (K : A → Measure B) (F : B → C) :
    (μ.bind K).map F = μ.bind (fun a => (K a).map F) := by
  ext s hs
  rw [Measure.map_apply (measurable_of_countable _) hs,
    Measure.bind_apply ((measurable_of_countable F) hs) (measurable_of_countable _).aemeasurable,
    Measure.bind_apply hs (measurable_of_countable _).aemeasurable]
  congr 1
  funext a
  exact (Measure.map_apply (measurable_of_countable _) hs).symm

lemma countable_bind_map {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [Countable A] [Countable B] [Countable C]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] [MeasurableSingletonClass C]
    (μ : Measure A) (F : A → B) (K : B → Measure C) :
    (μ.map F).bind K = μ.bind (fun a => K (F a)) := by
  ext s hs
  rw [Measure.bind_apply hs (measurable_of_countable _).aemeasurable,
    Measure.bind_apply hs (measurable_of_countable _).aemeasurable,
    lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

lemma dependentPair_map {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [Countable A] [Countable B] [Countable C]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] [MeasurableSingletonClass C]
    (μ : Measure A) (K : A → Measure B) (F : A × B → C) :
    (dependentPair μ K).map F = μ.bind (fun a => (K a).map (fun b => F (a,b))) := by
  rw [dependentPair,countable_map_bind]
  congr 1
  funext a
  exact Measure.map_map (measurable_of_countable _) (measurable_of_countable _)

lemma countable_bind_mono {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Countable A] [Countable B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure A) (K L : A → Measure B) (h : ∀ a, K a ≤ L a) : μ.bind K ≤ μ.bind L := by
  intro s
  rw [Measure.bind_apply (Set.to_countable s).measurableSet (measurable_of_countable _).aemeasurable,
    Measure.bind_apply (Set.to_countable s).measurableSet (measurable_of_countable _).aemeasurable]
  exact lintegral_mono fun a => h a s

end TupleKernel

lemma tupleWordEndpoint_concat {d k : ℕ} (x : Fin k → Lattice d)
    (p : (Fin k → List (Direction d)) × (Fin k → List (Direction d))) :
    tupleWordEndpoint x (tupleWordConcat p) = tupleWordEndpoint (tupleWordEndpoint x p.1) p.2 := by
  funext j
  exact (show wordPath (x j) (p.1 j++p.2 j) (p.1 j++p.2 j).length =
    wordPath (wordPath (x j) (p.1 j) (p.1 j).length) (p.2 j) (p.2 j).length by
      rw [List.length_append,wordPath_append_suffix])

lemma relativeBudgetEndpointLaw_comp_le {d k : ℕ} (e f : Direction d) (h m : ℕ)
    (r q : ℝ) (hq : 0 ≤ q) (ω : Environment d) (x : Fin k → Lattice d) :
    (relativeBudgetEndpointLaw e f h r ω x).bind (relativeBudgetEndpointLaw e f m q ω) ≤
      relativeBudgetEndpointLaw e f (h+m) (r+q) ω x := by
  have hm := Measure.map_mono (relativeBudgetWordLaw_comp_le e f h m r q hq ω x)
    (measurable_of_countable (tupleWordEndpoint x))
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at hm
  have he : (tupleWordEndpoint x ∘ tupleWordConcat) = fun p => tupleWordEndpoint (tupleWordEndpoint x p.1) p.2 := by
    funext p; exact tupleWordEndpoint_concat x p
  rw [he,relativeBudgetSplitLaw,TupleKernel.dependentPair_map] at hm
  change _ ≤ (relativeBudgetWordLaw e f (h+m) (r+q) ω x).map (tupleWordEndpoint x)
  rw [relativeBudgetEndpointLaw,TupleKernel.countable_bind_map]
  exact hm

noncomputable def budgetEndpointMixture {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (π : Measure (Fin k → Lattice d)) (ω : Environment d) :
    Measure (Fin k → Lattice d) := π.bind (relativeBudgetEndpointLaw e f H r ω)

lemma budgetEndpointMixture_apply {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (π : Measure (Fin k → Lattice d)) (ω : Environment d)
    (A : Set (Fin k → Lattice d)) :
    budgetEndpointMixture e f H r π ω A = ∫⁻ x, relativeBudgetEndpointLaw e f H r ω x A ∂π := by
  exact Measure.bind_apply (Set.to_countable _).measurableSet (measurable_of_countable _).aemeasurable

lemma budgetEndpointMixture_univ {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (π : Measure (Fin k → Lattice d)) (ω : Environment d) :
    budgetEndpointMixture e f H r π ω Set.univ = relativeBudgetMassENN e f H r π ω := by
  rw [budgetEndpointMixture_apply,relativeBudgetMassENN]
  congr 1; funext x
  exact Measure.map_apply_of_aemeasurable (measurable_of_countable _).aemeasurable MeasurableSet.univ

lemma budgetEndpointMixture_comp_le {d k : ℕ} (e f : Direction d) (h m : ℕ)
    (r q : ℝ) (hq : 0 ≤ q) (π : Measure (Fin k → Lattice d)) (ω : Environment d) :
    budgetEndpointMixture e f m q (budgetEndpointMixture e f h r π ω) ω ≤
      budgetEndpointMixture e f (h+m) (r+q) π ω := by
  unfold budgetEndpointMixture
  rw [Measure.bind_bind (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]
  exact TupleKernel.countable_bind_mono _ _ _ fun x => relativeBudgetEndpointLaw_comp_le e f h m r q hq ω x

instance budgetEndpointMixture_finite {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π] (ω : Environment d) :
    IsFiniteMeasure (budgetEndpointMixture e f H r π ω) := by
  constructor
  rw [budgetEndpointMixture_univ]
  exact lt_of_le_of_lt (relativeBudgetMassENN_le_one e f H r π ω) ENNReal.one_lt_top

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma relativeBudgetWordLaw_ae {d k : ℕ} (e f : Direction d) (H : ℕ) (r : ℝ)
    (ω : Environment d) (x : Fin k → Lattice d) :
    ∀ᵐ w ∂relativeBudgetWordLaw e f H r ω x,
      TupleRelativeBudget e f x H r w ∧ ∀ j,
      wordPath (x j) (w j) ∈ HitAt (Strip (realPosition (step e)) (x j) H)
        (Upper (realPosition (step e)) (x j) H) (w j).length := by
  apply ae_iff_of_countable.mpr
  intro w hw
  rw [relativeBudgetWordLaw_singleton] at hw
  by_cases hb : TupleRelativeBudget e f x H r w
  · rw [ite_eq_left hb,rawTupleWordLaw_singleton] at hw
    refine ⟨hb,?_⟩
    intro j
    by_contra hj
    apply hw
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [rawWordLaw_singleton,ite_eq_right hj]
  · exact False.elim (hw (by rw [ite_eq_right hb]))

lemma relativeBudgetEndpointLaw_support {d k : ℕ} (e f : Direction d) (H : ℕ)
    (a G r : ℝ) (ω : Environment d) (x : Fin k → Lattice d)
    (hx : x ∈ TupleAtHeight (realPosition (step e)) a) (hG : TupleSeparated f G x) :
    ∀ᵐ y ∂relativeBudgetEndpointLaw e f H r ω x,
      y ∈ TupleAtHeight (realPosition (step e)) (a+H) ∧ TupleSeparated f (G-r) y := by
  rw [relativeBudgetEndpointLaw,ae_map_iff (measurable_of_countable _).aemeasurable (Set.to_countable _).measurableSet]
  filter_upwards [relativeBudgetWordLaw_ae e f H r ω x] with w hw
  let u j : HitWord (x j) (Strip (realPosition (step e)) (x j) H) (Upper (realPosition (step e)) (x j) H) := ⟨w j,hw.2 j⟩
  refine ⟨?_,tupleRelativeBudget_separation e f x H G r u hG hw.1⟩
  intro j
  change dot (realPosition (wordPath (x j) (w j) (w j).length)) (realPosition (step e))=a+H
  have hh := wordPath_hit_exact e (x j) H (u j)
  have hr : dot (realPosition (wordPath (x j) (w j) (w j).length)) (realPosition (step e)) =
      dot (realPosition (x j)) (realPosition (step e))+(H:ℝ) := by
    rw [signedHeight_projection,signedHeight_projection]
    exact_mod_cast hh
  simpa only [hx j] using hr

lemma TupleKernel.countable_bind_ae {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Countable A] [Countable B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure A) (K : A → Measure B) (P : B → Prop)
    (hP : ∀ᵐ a ∂μ, ∀ᵐ b ∂K a, P b) : ∀ᵐ b ∂μ.bind K, P b := by
  rw [ae_iff,Measure.bind_apply (Set.to_countable _).measurableSet (measurable_of_countable _).aemeasurable]
  have he : (fun a => K a {b | ¬ P b}) =ᵐ[μ] fun _ => 0 := hP.mono fun a ha => ae_iff.mp ha
  rw [lintegral_congr_ae he,lintegral_zero]

lemma budgetEndpointMixture_support {d k : ℕ} (e f : Direction d) (H : ℕ) (a G r : ℝ)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d)
    (hπ : ∀ᵐ x ∂π, x ∈ TupleAtHeight (realPosition (step e)) a ∧ TupleSeparated f G x) :
    ∀ᵐ y ∂budgetEndpointMixture e f H r π ω,
      y ∈ TupleAtHeight (realPosition (step e)) (a+H) ∧ TupleSeparated f (G-r) y := by
  apply TupleKernel.countable_bind_ae
  exact hπ.mono fun x hx => relativeBudgetEndpointLaw_support e f H a G r ω x hx.1 hx.2

lemma tupleSeparated_mono {d k : ℕ} (f : Direction d) {G g : ℝ} (h : g ≤ G)
    (x : Fin k → Lattice d) (hx : TupleSeparated f G x) : TupleSeparated f g x :=
  fun i j hij => h.trans (hx i j hij)

lemma tupleSeparated_coordinate {d k : ℕ} (f : Direction d) (G : ℕ) (x : Fin k → Lattice d) :
    TupleSeparated f (G:ℝ) x ↔ Pairwise fun i j => (G:ℤ) ≤ |x i f.1-x j f.1| := by
  have he (i j) : |signedCoordinate f (x i)-signedCoordinate f (x j)| = (|x i f.1-x j f.1|:ℤ) := by
    rw [Int.cast_abs,Int.cast_sub]
    simp only [signedCoordinate]
    split
    · rfl
    · rw [show -(x i f.1:ℝ)- -(x j f.1:ℝ) = -((x i f.1:ℝ)-(x j f.1:ℝ)) by ring, abs_neg]
  simp only [TupleSeparated,Pairwise,he]
  norm_cast

end DirectionalTransience

end

end OAI
