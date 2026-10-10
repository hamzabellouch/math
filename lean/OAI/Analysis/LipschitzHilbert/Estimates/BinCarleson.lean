import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace OAI

/-! A finite Carleson mass bound from disjoint intervals within each bin. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LipschitzHilbert

variable {ι B X : Type*} [Fintype ι] [Fintype B]

/-- At a point, pairwise disjointness within each bin prevents that bin's
function from being counted more than once. -/
theorem sum_bin_indicators_le (Q : ι → Set X) (bin : ι → B) (f : B → X → ℝ)
    (hf : ∀ b x, 0 ≤ f b x)
    (hdisj : ∀ i j, i ≠ j → bin i = bin j → Disjoint (Q i) (Q j)) (x : X) :
    (∑ i, (Q i).indicator (f (bin i)) x) ≤ ∑ b, f b x := by
  classical
  let s := Finset.univ.filter (fun i => x ∈ Q i)
  have hinj : Set.InjOn bin (s : Set ι) := by
    intro i hi j hj hij
    by_contra hne
    exact Set.disjoint_left.mp (hdisj i j hne hij)
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have hsum : (∑ i, (Q i).indicator (f (bin i)) x) = ∑ i ∈ s, f (bin i) x := by
    simp only [s, Finset.sum_filter, Set.indicator_apply]
  rw [hsum]
  exact Finset.sum_le_sum_of_injOn bin hinj (by simp) (fun _ _ => le_rfl)
    (fun b _ _ => hf b x)

variable [MeasurableSpace X]

/-- The finite mass bound underlying the line counting lemma. Different
bins may select the same interval; disjointness is needed only within a bin. -/
theorem finite_bin_carleson (Q : ι → Set X) (bin : ι → B) (f : B → X → ℝ)
    (μ : Measure X) {P : Set X} (hP : MeasurableSet P) (hPfinite : μ P ≠ ∞)
    (hQ : ∀ i, MeasurableSet (Q i)) (hsub : ∀ i, Q i ⊆ P)
    (hf : ∀ b, IntegrableOn (f b) P μ) (hnonneg : ∀ b x, 0 ≤ f b x)
    (hdisj : ∀ i j, i ≠ j → bin i = bin j → Disjoint (Q i) (Q j))
    {β C : ℝ} (hβ : 0 < β) (hsum : ∀ x ∈ P, (∑ b, f b x) ≤ C)
    (hbad : ∀ i, β * μ.real (Q i) ≤ ∫ x in Q i, f (bin i) x ∂μ) :
    (∑ i, μ.real (Q i)) ≤ (C / β) * μ.real P := by
  have : IsFiniteMeasure (μ.restrict P) := isFiniteMeasure_restrict.mpr hPfinite
  have hind : ∀ i, Integrable (fun x => (Q i).indicator (f (bin i)) x) (μ.restrict P) :=
    fun i => (hf (bin i)).indicator (hQ i)
  have heq : (∑ i, ∫ x in Q i, f (bin i) x ∂μ) =
      ∫ x in P, ∑ i, (Q i).indicator (f (bin i)) x ∂μ := by
    rw [integral_finsetSum _ (fun i _ => hind i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [setIntegral_indicator (hQ i), inter_eq_right.mpr (hsub i)]
  have hbound : β * (∑ i, μ.real (Q i)) ≤ C * μ.real P := by
    calc
      _ = ∑ i, β * μ.real (Q i) := Finset.mul_sum _ _ _
      _ ≤ ∑ i, ∫ x in Q i, f (bin i) x ∂μ := Finset.sum_le_sum (fun i _ => hbad i)
      _ = _ := heq
      _ ≤ ∫ _ in P, C ∂μ := by
        apply setIntegral_mono_on (integrable_finsetSum _ (fun i _ => hind i))
          (integrable_const C) hP
        intro x hx
        exact (sum_bin_indicators_le Q bin f hnonneg hdisj x).trans (hsum x hx)
      _ = C * μ.real P := by simp [mul_comm]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hβ).2
  simpa only [mul_comm] using hbound

/-- The same estimate for an arbitrary bin type, using only a uniform bound
on its finite partial sums. -/
theorem finite_bin_carleson_of_finite_sums {B' : Type*}
    (Q : ι → Set X) (bin : ι → B') (f : B' → X → ℝ)
    (μ : Measure X) {P : Set X} (hP : MeasurableSet P) (hPfinite : μ P ≠ ∞)
    (hQ : ∀ i, MeasurableSet (Q i)) (hsub : ∀ i, Q i ⊆ P)
    (hf : ∀ b, IntegrableOn (f b) P μ) (hnonneg : ∀ b x, 0 ≤ f b x)
    (hdisj : ∀ i j, i ≠ j → bin i = bin j → Disjoint (Q i) (Q j))
    {β C : ℝ} (hβ : 0 < β) (hsum : ∀ s : Finset B', ∀ x ∈ P, (∑ b ∈ s, f b x) ≤ C)
    (hbad : ∀ i, β * μ.real (Q i) ≤ ∫ x in Q i, f (bin i) x ∂μ) :
    (∑ i, μ.real (Q i)) ≤ (C / β) * μ.real P := by
  classical
  let bins := Finset.univ.image bin
  let bin' (i : ι) : bins := ⟨bin i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  apply finite_bin_carleson Q bin' (fun b => f b.1) μ hP hPfinite hQ hsub
    (fun b => hf b.1) (fun b => hnonneg b.1)
  · intro i j hij hb
    exact hdisj i j hij (congrArg Subtype.val hb)
  · exact hβ
  · intro x hx
    calc
      _ = ∑ b ∈ bins, f b x := (Finset.sum_subtype bins (fun _ => Iff.rfl) (fun b => f b x)).symm
      _ ≤ C := hsum bins x hx
  · exact hbad

end LipschitzHilbert

end

end OAI
