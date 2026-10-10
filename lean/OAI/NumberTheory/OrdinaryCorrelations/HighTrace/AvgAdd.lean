import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Avg
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RankBot
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.BoundedLists

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.SourceCylinder
open Finset Classical OrdinaryCorrelations.FiniteIntegration
variable {α ι : Type*} [Fintype α] [Fintype ι] {Ω : ι → Type*} [∀ p, Fintype (Ω p)]

lemma avg_add' {β : Type*} [Fintype β] (f g : β → ℝ) :
    avg (fun x => f x + g x) = avg f + avg g := by
  simp only [avg,sum_add_distrib,mul_add]

lemma avg_sub' {β : Type*} [Fintype β] (f g : β → ℝ) :
    avg (fun x => f x - g x) = avg f - avg g := by
  simp only [avg,sum_sub_distrib,mul_sub]

lemma avg_sum' {β γ : Type*} [Fintype β] (s : Finset γ) (f : γ → β → ℝ) :
    avg (fun x => ∑ a ∈ s, f a x) = ∑ a ∈ s, avg (f a) := by
  unfold avg
  rw [sum_comm,mul_sum]

lemma avg_ite_add_sum_mul {β γ : Type*} [Fintype β] (s : Finset γ)
    (G : β → Prop) (f : γ → β → ℝ) (g : β → ℝ) (c d : ℝ) :
    avg (fun a => if G a then c*(∑ l ∈ s, f l a)+d*g a else 0) =
      c*(∑ l ∈ s, avg (fun a => if G a then f l a else 0)) +
      d*avg (fun a => if G a then g a else 0) := by
  have he (a : β) : (if G a then c*(∑ l ∈ s, f l a)+d*g a else 0) =
      (∑ l ∈ s, c*(if G a then f l a else 0)) + d*(if G a then g a else 0) := by
    by_cases ha : G a
    · simp only [ha,ite_true,mul_sum]
    · simp only [ha,ite_false,mul_zero,sum_const_zero,add_zero]
  simp_rw [he]
  rw [avg_add',avg_sum']
  simp_rw [avg_mul_left]
  rw [← mul_sum]

lemma truncated_real (E : Finset (Cylinder Ω)) (t : ℕ) (x : ∀ p, Ω p) :
    (truncated E t x : ℝ) = ∑ I : {I : Intersection E // I ∈ retained E t},
      (coefficient E I.val : ℝ) * (if I.val.val.Holds x then 1 else 0) := by
  simp only [truncated,Int.cast_sum,Int.cast_ite,Int.cast_zero]
  rw [← sum_attach (retained E t)]
  apply sum_congr rfl
  intro I hI
  split_ifs <;> simp

theorem signed_list_reduction (V : Finset α) (f : α → Cylinder Ω)
    (hproper : ∀ e ∈ V.image f, e ≠ ⊥) (t w : ℕ) (ht : 1 ≤ t)
    (hwidth : ∀ e ∈ V.image f, e.support.card ≤ w) (K : (∀ p, Ω p) → ℝ) :
    |avg (fun x => K x * (avoidance (V.image f) x : ℝ))| ≤
      (max 1 ((t*w)^(t*w+1)) : ℕ) *
        (∑ l ∈ boundedLists α t, |avg (fun x => K x * labelledIndicator V f l x)|) +
      ((2^(t*w) * max 1 ((t*w)^(t*w+1)) : ℕ) : ℝ) *
        avg (fun x => |K x| * (witnessCount (V.image f) t x : ℝ)) := by
  let E := V.image f
  let U : ℕ := max 1 ((t*w)^(t*w+1))
  let W : ℕ := 2^(t*w)*U
  have err (x : ∀ p, Ω p) :
      |(avoidance E x : ℝ) - (truncated E t x : ℝ)| ≤ (W:ℝ)*witnessCount E t x := by
    have he := truncation_bound E hproper t w ht hwidth x
    have he' : ((avoidance E x-truncated E t x).natAbs:ℝ) ≤
      (W:ℝ)*(witnessCount E t x:ℝ) := by exact_mod_cast he
    simpa only [Nat.cast_natAbs,Int.cast_abs,Int.cast_sub] using he'
  have trunc : avg (fun x => K x*(truncated E t x:ℝ)) =
      ∑ I : LowRank V f t, (coefficient E I.val:ℝ)*
        avg (fun x => K x * labelledIndicator V f (generatingList V f t I) x) := by
    simp_rw [truncated_real,mul_sum]
    rw [avg_sum']
    apply sum_congr rfl
    intro I hI
    rw [← avg_mul_left]
    congr 1
    funext x
    rw [generatingList_indicator]
    ring
  have hc (I : LowRank V f t) : |(coefficient E I.val:ℝ)| ≤ (U:ℝ) := by
    have hc := retained_coefficient_bound E t w hwidth I.val I.property
    have hc' : ((coefficient E I.val).natAbs:ℝ) ≤ (U:ℝ) := by exact_mod_cast hc
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hc'
  have htr : |avg (fun x => K x*(truncated E t x:ℝ))| ≤
      (U:ℝ) * ∑ l ∈ boundedLists α t, |avg (fun x => K x*labelledIndicator V f l x)| := by
    rw [trunc]
    calc
      _ ≤ ∑ I : LowRank V f t, |(coefficient E I.val:ℝ) *
        avg (fun x => K x*labelledIndicator V f (generatingList V f t I) x)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ I : LowRank V f t, (U:ℝ) *
        |avg (fun x => K x*labelledIndicator V f (generatingList V f t I) x)| := by
          apply sum_le_sum
          intro I hI
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hc I) (abs_nonneg _)
      _ = (U:ℝ) * ∑ I : LowRank V f t,
        |avg (fun x => K x*labelledIndicator V f (generatingList V f t I) x)| := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (generatingList_sum_le V f t (fun l => |avg (fun x => K x*labelledIndicator V f l x)|)
          (fun l => abs_nonneg _)) (Nat.cast_nonneg _)
  have herr : |avg (fun x => K x*((avoidance E x:ℝ)-(truncated E t x:ℝ)))| ≤
      (W:ℝ)*avg (fun x => |K x| *(witnessCount E t x:ℝ)) := by
    calc
      _ ≤ avg (fun x => |K x*((avoidance E x:ℝ)-(truncated E t x:ℝ))|) := abs_avg_le _
      _ ≤ avg (fun x => (W:ℝ)*(|K x| *(witnessCount E t x:ℝ))) := by
        apply avg_mono
        intro x
        rw [abs_mul]
        calc
          _ ≤ |K x| *((W:ℝ)*(witnessCount E t x:ℝ)) :=
            mul_le_mul_of_nonneg_left (err x) (abs_nonneg _)
          _ = _ := by ring
      _ = _ := avg_mul_left _ _
  have he : (fun x => K x*(avoidance E x:ℝ)) =
      fun x => K x*(truncated E t x:ℝ) + K x*((avoidance E x:ℝ)-(truncated E t x:ℝ)) := by
    funext x
    ring
  rw [show V.image f=E from rfl,he,avg_add']
  exact (abs_add_le _ _).trans (add_le_add htr herr)

end OrdinaryCorrelations.SourceCylinder

end

end OAI
