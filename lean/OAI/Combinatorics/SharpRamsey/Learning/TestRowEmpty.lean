import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.TestRowScore

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory ProbabilityTheory SharpLogRamsey.PoissonSchedules
open SharpLogRamsey.EmptyExceptional
open scoped BigOperators Classical NNReal
noncomputable section
variable {A H : Type*}

def coordinates (S : Finset A) (R : ℕ) (inc : H → A → Prop) (h : H) :
    Finset (Fin R × S) := univ ×ˢ univ.filter (fun y : S => inc h y.1)

lemma coordinates_empty (S : Finset A) (R : ℕ) (inc : H → A → Prop)
    (ω : Schedule S R) (h : H) :
    ω∈emptyLedger (coordinates S R inc h) ↔ empty S inc ω h := by
  simp only [emptyLedger,coordinates,empty,mem_product,mem_univ,mem_filter,true_and]
  constructor
  · intro he r y hy
    exact he (r,y) hy
  · intro he i hi
    exact he i.1 i.2 hi

lemma sub_inc_card (S : Finset A) (inc : H → A → Prop) (h : H) :
    (univ.filter (fun y : S => inc h y.1)).card=(S.filter (inc h)).card := by
  apply card_bij (fun y _ => y.1)
  · intro y hy
    exact mem_filter.mpr ⟨y.2,(mem_filter.mp hy).2⟩
  · intro y _ z _ he
    exact Subtype.ext he
  · intro y hy
    exact ⟨⟨y,(mem_filter.mp hy).1⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hy).2⟩,rfl⟩

lemma coordinates_mass (S : Finset A) (R : ℕ) (inc : H → A → Prop) (h : H)
    (γ : ℝ≥0) :
    (∑ _i∈coordinates S R inc h,(γ:ℝ))=(γ:ℝ)*R*((S.filter (inc h)).card:ℝ) := by
  simp only [sum_const,nsmul_eq_mul,coordinates,card_product,card_univ,Fintype.card_fin,
    sub_inc_card,Nat.cast_mul]
  ring

lemma empty_count (S : Finset A) (E : Finset H) (R : ℕ) (inc : H → A → Prop)
    (ω : Schedule S R) :
    emptySum E (coordinates S R inc) (fun _ => 1) ω=(emptySet S E inc ω).card := by
  simp only [emptySum,coordinates_empty,emptySet,card_filter,Nat.cast_sum,Nat.cast_ite,
    Nat.cast_one,Nat.cast_zero]

lemma empty_weight (S : Finset A) (E : Finset H) (R : ℕ) (inc : H → A → Prop)
    (l : H → ℝ) (ω : Schedule S R) :
    emptySum E (coordinates S R inc) l ω=∑ h∈emptySet S E inc ω,l h := by
  simp only [emptySum,coordinates_empty,emptySet,sum_filter]

theorem actual_empty_good (S : Finset A) (E E₀ : Finset H) (R : ℕ)
    (inc : H → A → Prop) (γ : ℝ≥0) (l : H → ℝ) (P b δ u zmin W : ℝ)
    (hE₀ : E₀.Nonempty) (hsub : E₀⊆E) (hP : 0≤P) (hδ : 0≤δ)
    (hu : 0<u) (hz : 0<zmin) (hl : ∀ h∈E,0≤l h)
    (hmass : ∀ h∈E,(γ:ℝ)*R*((S.filter (inc h)).card:ℝ)=P*l h)
    (hb : ∀ h∈E₀,(γ:ℝ)*R*((S.filter (inc h)).card:ℝ)≤b)
    (hW : ∑ h∈E,l h≤W) (hzmin : zmin≤(E₀.card:ℝ)*Real.exp (-b)/2) :
    Real.exp (-b)/2-W*Real.exp (-P*δ)/(u*zmin)≤
      (scheduleLaw (fun _ : Fin R×S => γ)).real {ω |
        zmin≤(emptySet S E inc ω).card ∧
        (∑ h∈emptySet S E inc ω,l h)≤(δ+u)*(emptySet S E inc ω).card} := by
  have he := empty_good_event (fun _ : Fin R×S => γ) E E₀ hE₀ hsub
    (coordinates S R inc) l P b δ u zmin W hP hδ hu hz hl
    (fun h hh => (coordinates_mass S R inc h γ).trans (hmass h hh))
    (fun h hh => (coordinates_mass S R inc h γ).trans_le (hb h hh)) hW hzmin
  simpa only [empty_count,empty_weight,sum_const,nsmul_eq_mul,mul_one] using he

end
end SharpLogRamsey.PreparedRow

end

end OAI
