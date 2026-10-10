import OAI.Analysis.CircleDomains.Selection.ResidualConstraints
import OAI.Analysis.CircleDomains.Probability.CountableVisitNorm
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

namespace OAI

/-! Finite deletion constraints exclude residual incidences off the support
of the toll whenever the actual full path toll is finite. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

theorem tendsto_deleted_series_zero {A : Type*} [Countable A]
    (f : A → ℝ≥0∞) (hf : (∑' a, f a) ≠ ∞) (P : ℕ → Set A)
    (hP : ∀ a, ∀ᶠ n in atTop, a ∈ P n) :
    Tendsto (fun n => ∑' a, if a ∈ P n then 0 else f a) atTop (𝓝 0) := by
  let : MeasurableSpace A := ⊤
  have h := tendsto_lintegral_of_dominated_convergence (μ := Measure.count)
    (F := fun n a => if a ∈ P n then 0 else f a) (f := fun _ => 0) f
    (fun _ => measurable_of_countable _)
    (fun n => Eventually.of_forall fun a => by
      change (if a ∈ P n then 0 else f a) ≤ f a
      split_ifs <;> simp)
    (by simpa only [lintegral_count] using hf)
    (Eventually.of_forall fun a => tendsto_const_nhds.congr' ((hP a).mono fun n hn => by simp [hn]))
  simpa only [lintegral_count, tsum_zero] using h

variable {X : Type*} [MetricSpace X]

theorem residualVisitCount_le_visitCount (B : Set X) (I : Set PathTime)
    (Γ : TaggedPath X) (x : X) : residualVisitCount B I Γ x ≤ visitCount Γ.1 x := by
  rw [residualVisitCount, timeCount, visitCount_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro t
  by_cases h : (Γ.1 t = x)
  · simp only [h, ite_true]
    split_ifs <;> simp
  · have hn : ((Γ, x), t) ∉ residualVisitRelation B I := fun hh => h hh.2.2
    simp only [h, hn, ite_false, le_refl]

theorem residualToll_deleted_le (B : Set X) (I : Set PathTime)
    (m : X → ℝ≥0∞) (P : Set X) (Γ : TaggedPath X) :
    residualToll B I (deletedWeight P m) Γ ≤
      ∑' x : support m, if x.val ∈ P then 0 else m x.val * visitCount Γ.1 x.val := by
  rw [residualToll_eq_visits]
  have he : (∑' x, deletedWeight P m x * residualVisitCount B I Γ x) =
      ∑' x : support m, deletedWeight P m x.val * residualVisitCount B I Γ x.val := by
    symm
    apply tsum_subtype_eq_of_support_subset
      (f := fun x : X => deletedWeight P m x * residualVisitCount B I Γ x)
    intro x hx
    by_contra hn
    have hz : m x = 0 := notMem_support.mp hn
    simp [deletedWeight, hz] at hx
  rw [he]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x.val ∈ P
  · simp [deletedWeight, hx]
  · simpa only [deletedWeight, hx, ite_false] using
      mul_le_mul' (le_refl (m x.val)) (residualVisitCount_le_visitCount B I Γ x.val)

theorem residual_incidence_envelope_null {Z : Type*} [MeasurableSpace Z]
    (B : Set X) (I : Set PathTime) (R : Set (Z × X)) (ν : Measure Z)
    (m : X → ℝ≥0∞) (hm : (support m).Countable) (P : ℕ → Set X)
    (hcover : ∀ x ∈ support m, ∀ᶠ n in atTop, x ∈ P n)
    (Γ : TaggedPath X) (hfinite : boundaryToll Γ.1 m < ∞)
    (hbound : ∀ n, ResidualIncidenceBound B I R (P n) ν m Γ) :
    ν (⋂ n, {z | (Γ, z) ∈ residualIncidence B I R (P n)}) = 0 := by
  let : Countable (support m) := hm.to_subtype
  have ht := tendsto_deleted_series_zero
    (fun x : support m => m x.val * visitCount Γ.1 x.val)
    (by simpa only [← boundaryToll_eq_support] using hfinite.ne)
    (fun n => {x : support m | x.val ∈ P n})
    (fun x => hcover x.val x.property)
  apply le_antisymm _ bot_le
  apply ge_of_tendsto ht
  apply Eventually.of_forall
  intro n
  exact (measure_mono (iInter_subset _ n)).trans
    ((hbound n).trans (residualToll_deleted_le B I m (P n) Γ))

theorem residual_incidence_null_off_support {Z : Type*} [MeasurableSpace Z]
    (B : Set X) (I : Set PathTime) (R : Set (Z × X)) (ν : Measure Z)
    (m : X → ℝ≥0∞) (hm : (support m).Countable) (P : ℕ → Set X)
    (hP : ∀ n, P n ⊆ support m)
    (hcover : ∀ x ∈ support m, ∀ᶠ n in atTop, x ∈ P n)
    (Γ : TaggedPath X) (hfinite : boundaryToll Γ.1 m < ∞)
    (hbound : ∀ n, ResidualIncidenceBound B I R (P n) ν m Γ) :
    ν {z | ∃ t ∈ residualTimes B Γ, t ∈ I ∧ (z, Γ.1 t) ∈ R ∧
      Γ.1 t ∉ support m} = 0 := by
  let : Countable (support m) := hm.to_subtype
  have ht := tendsto_deleted_series_zero
    (fun x : support m => m x.val * visitCount Γ.1 x.val)
    (by simpa only [← boundaryToll_eq_support] using hfinite.ne)
    (fun n => {x : support m | x.val ∈ P n})
    (fun x => hcover x.val x.property)
  apply le_antisymm _ bot_le
  apply ge_of_tendsto ht
  apply Eventually.of_forall
  intro n
  apply (measure_mono ?_).trans ((hbound n).trans (residualToll_deleted_le B I m (P n) Γ))
  rintro z ⟨t, ht, hI, hR, hm⟩
  exact ⟨t, ht, hI, hR, fun hp => hm (hP n hp)⟩

end CircleDomainRigidity

end

end OAI
