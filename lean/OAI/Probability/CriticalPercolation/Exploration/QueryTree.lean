import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.MulLogDivScaled

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical
open Real
open Set Real
open scoped Topology

namespace CriticalPercolation
open FiniteEntropy

universe u

inductive QueryTree (E : Type u) : Type u where
  | stop : QueryTree E
  | ask (e : E) (left right : QueryTree E) : QueryTree E

namespace QueryTree
variable {E : Type u}

@[reducible] def Leaf : QueryTree E → Type u
  | .stop => PUnit
  | .ask _ left right => Sum left.Leaf right.Leaf

instance leafFintype : (t : QueryTree E) → Fintype t.Leaf
  | .stop => inferInstanceAs (Fintype PUnit)
  | .ask _ left right => @instFintypeSum _ _ left.leafFintype right.leafFintype

def run : (t : QueryTree E) → (E → Bool) → t.Leaf
  | .stop, _ => PUnit.unit
  | .ask e left right, ω => if ω e then Sum.inr (right.run ω) else Sum.inl (left.run ω)

def reads : (t : QueryTree E) → (E → Bool) → List E
  | .stop, _ => []
  | .ask e left right, ω => e :: if ω e then right.reads ω else left.reads ω

def Valid [DecidableEq E] : QueryTree E → Finset E → Prop
  | .stop, _ => True
  | .ask e left right, used => e ∉ used ∧ left.Valid (insert e used) ∧ right.Valid (insert e used)

noncomputable def reference (p : ℝ) : (t : QueryTree E) → t.Leaf → ℝ
  | .stop, _ => 1
  | .ask _ left _, Sum.inl x => (1-p)*left.reference p x
  | .ask _ _ right, Sum.inr x => p*right.reference p x

lemma reference_pos {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    ∀ (t : QueryTree E) (x : t.Leaf), 0 < t.reference p x := by
  intro t
  induction t with
  | stop => intro x; exact zero_lt_one
  | ask e left right hl hr =>
    intro x
    cases x with
    | inl x => exact mul_pos (sub_pos.mpr hp.2) (hl x)
    | inr x => exact mul_pos hp.1 (hr x)

lemma reference_sum (p : ℝ) (t : QueryTree E) : ∑ x, t.reference p x = 1 := by
  induction t with
  | stop => simp [reference, Leaf]
  | ask e left right hl hr =>
    change (∑ x : Sum left.Leaf right.Leaf, (ask e left right).reference p x) = 1
    rw [Fintype.sum_sum_type]
    simp only [reference, ← Finset.mul_sum, hl, hr, mul_one]
    ring

noncomputable def charge (F : ℝ → ℝ) : (t : QueryTree E) → (t.Leaf → ℝ) → ℝ
  | .stop, _ => 0
  | .ask _ left right, P =>
      let l := ∑ x, P (Sum.inl x)
      let r := ∑ x, P (Sum.inr x)
      (l+r)*F (r/(l+r)) + left.charge F (fun x => P (Sum.inl x)) +
        right.charge F (fun x => P (Sum.inr x))

lemma charge_mono {F H : ℝ → ℝ} (hFH : ∀ r ∈ Set.Icc (0:ℝ) 1, F r ≤ H r)
    (t : QueryTree E) (P : t.Leaf → ℝ) (hP : ∀ x, 0 ≤ P x) :
    t.charge F P ≤ t.charge H P := by
  induction t with
  | stop => rfl
  | ask e left right hl hr =>
    let l := ∑ x, P (Sum.inl x)
    let r := ∑ x, P (Sum.inr x)
    have hn : 0 ≤ l+r := add_nonneg (Finset.sum_nonneg fun x _ => hP (.inl x))
      (Finset.sum_nonneg fun x _ => hP (.inr x))
    have hb : r/(l+r) ∈ Set.Icc (0:ℝ) 1 := by
      constructor
      · exact div_nonneg (Finset.sum_nonneg fun x _ => hP (.inr x)) hn
      · by_cases hz : l+r = 0
        · simp [hz]
        · apply (div_le_one (lt_of_le_of_ne hn (Ne.symm hz))).mpr
          have : 0 ≤ l := Finset.sum_nonneg fun x _ => hP (.inl x)
          linarith
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hFH _ hb) hn)
      (hl _ fun x => hP (.inl x))) (hr _ fun x => hP (.inr x))

lemma charge_const_mul (F : ℝ → ℝ) (c : ℝ) (t : QueryTree E) (P : t.Leaf → ℝ) :
    t.charge (fun r => c*F r) P = c*t.charge F P := by
  induction t with
  | stop => simp [charge]
  | ask e left right hl hr => simp only [charge, hl, hr]; ring

theorem divergence_reference_eq_charge {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (t : QueryTree E) (P : t.Leaf → ℝ) (hP : ∀ x, 0 ≤ P x) :
    divergence P (t.reference p) =
      t.charge (fun r => binaryDivergence r p) P + (∑ x, P x)*Real.log (∑ x, P x) := by
  induction t with
  | stop => simp [divergence, reference, charge, Leaf]
  | ask e left right hl hr =>
    let P₀ : left.Leaf → ℝ := fun x => P (Sum.inl x)
    let P₁ : right.Leaf → ℝ := fun x => P (Sum.inr x)
    have hb := binaryDivergence_mass_split
      (Finset.sum_nonneg (s := Finset.univ) (fun x _ => hP (.inl x)))
      (Finset.sum_nonneg (s := Finset.univ) (fun x _ => hP (.inr x))) hp
    change (∑ x : Sum left.Leaf right.Leaf, P x*Real.log (P x/(ask e left right).reference p x)) = _
    rw [Fintype.sum_sum_type]
    change divergence P₀ (fun x => (1-p)*left.reference p x) +
      divergence P₁ (fun x => p*right.reference p x) = _
    rw [divergence_scale_reference P₀ (left.reference p) (fun x => hP (.inl x))
      (fun x _ => reference_pos hp left x) (sub_pos.mpr hp.2),
      divergence_scale_reference P₁ (right.reference p) (fun x => hP (.inr x))
      (fun x _ => reference_pos hp right x) hp.1,
      hl P₀ (fun x => hP (.inl x)), hr P₁ (fun x => hP (.inr x))]
    change _ = _ + (∑ x : Sum left.Leaf right.Leaf, P x)*Real.log (∑ x : Sum left.Leaf right.Leaf, P x)
    rw [Fintype.sum_sum_type]
    dsimp only [charge, P₀, P₁]
    linarith

theorem divergence_reference_bounds {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (t : QueryTree E) (P : t.Leaf → ℝ) (hP : ∀ x, 0 ≤ P x) (hMass : ∑ x, P x = 1) :
    2*t.charge (fun r => (r-p)^2) P ≤ divergence P (t.reference p) ∧
    divergence P (t.reference p) ≤ (p*(1-p))⁻¹*t.charge (fun r => (r-p)^2) P := by
  rw [divergence_reference_eq_charge hp t P hP, hMass, Real.log_one, mul_zero, add_zero]
  constructor
  · have h := charge_mono (fun r hr => binaryDivergence_lower hp hr) t P hP
    rwa [charge_const_mul] at h
  · have h := charge_mono (fun r hr => binaryDivergence_upper hp hr) t P hP
    have heq : (fun r => (r-p)^2/(p*(1-p))) =
        (fun r => (p*(1-p))⁻¹*(r-p)^2) := by
      funext r; simp only [div_eq_mul_inv, mul_comm]
    rwa [heq, charge_const_mul] at h

lemma valid_mono [DecidableEq E] (t : QueryTree E) {s u : Finset E} (hsu : s ⊆ u)
    (hv : t.Valid u) : t.Valid s := by
  induction t generalizing s u with
  | stop => trivial
  | ask e left right hl hr =>
    exact ⟨fun he => hv.1 (hsu he), hl (Finset.insert_subset_insert e hsu) hv.2.1,
      hr (Finset.insert_subset_insert e hsu) hv.2.2⟩

lemma run_dependsOn [DecidableEq E] (t : QueryTree E) (used : Finset E) (hv : t.Valid used) :
    DependsOn t.run (↑used : Set E)ᶜ := by
  intro ω ω' hω
  induction t generalizing used with
  | stop => rfl
  | ask e left right hl hr =>
    have he : ω e = ω' e := hω e hv.1
    have hc : ∀ i ∈ (↑(insert e used) : Set E)ᶜ, ω i = ω' i := by
      intro i hi
      exact hω i (fun hu => hi (Finset.mem_insert_of_mem hu))
    simp only [run, he]
    split_ifs
    · exact congrArg Sum.inr (hr _ hv.2.2 hc)
    · exact congrArg Sum.inl (hl _ hv.2.1 hc)

lemma reads_disjoint [DecidableEq E] (t : QueryTree E) (used : Finset E)
    (hv : t.Valid used) (ω : E → Bool) : ∀ e ∈ t.reads ω, e ∉ used := by
  induction t generalizing used with
  | stop => simp [reads]
  | ask e left right hl hr =>
    intro f hf
    simp only [reads, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact hv.1
    · split_ifs at hf with he
      · exact fun hu => hr _ hv.2.2 _ hf (Finset.mem_insert_of_mem hu)
      · exact fun hu => hl _ hv.2.1 _ hf (Finset.mem_insert_of_mem hu)

lemma reads_nodup [DecidableEq E] (t : QueryTree E) (used : Finset E)
    (hv : t.Valid used) (ω : E → Bool) : (t.reads ω).Nodup := by
  induction t generalizing used with
  | stop => simp [reads]
  | ask e left right hl hr =>
    simp only [reads, List.nodup_cons]
    split_ifs
    · exact ⟨fun he => reads_disjoint right _ hv.2.2 ω e he (Finset.mem_insert_self _ _),
        hr _ hv.2.2⟩
    · exact ⟨fun he => reads_disjoint left _ hv.2.1 ω e he (Finset.mem_insert_self _ _),
        hl _ hv.2.1⟩

end QueryTree
end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
