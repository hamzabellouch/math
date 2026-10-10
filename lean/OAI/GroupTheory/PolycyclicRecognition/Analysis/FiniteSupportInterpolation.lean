import OAI.GroupTheory.PolycyclicRecognition.Geometry.OrderedInterpolationWeights
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finset.Sort

namespace OAI

/-! # Compatible interpolation on finite supports -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {I G : Type*} [LinearOrder I] [MetricSpace G]

omit [LinearOrder I] in
theorem listMass_eq_list_sum (a : I → ℝ) (l : List I) :
    listMass a l = (l.map a).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simpa only [listMass, List.map_cons, List.sum_cons] using congrArg (a i + ·) ih

theorem listMass_sort (a : I → ℝ) (s : Finset I) :
    listMass a (s.sort (· ≤ ·)) = ∑ i ∈ s, a i := by
  rw [listMass_eq_list_sum]
  change Multiset.sum (Multiset.map a (s.sort (· ≤ ·) : Multiset I)) = _
  rw [Finset.sort_eq]
  rfl

theorem filter_sort_support (a : I →₀ ℝ) (s : Finset I) (hs : a.support ⊆ s) :
    (s.sort (· ≤ ·)).filter (fun i => a i ≠ 0) = a.support.sort (· ≤ ·) := by
  classical
  let l := (s.sort (· ≤ ·)).filter (fun i => a i ≠ 0)
  have hl : l.toFinset = a.support := by
    ext i
    simp only [l, List.mem_toFinset, List.mem_filter, Finset.mem_sort, decide_eq_true_eq,
      Finsupp.mem_support_iff]
    exact ⟨fun h => h.2, fun h => ⟨hs (Finsupp.mem_support_iff.mpr h), h⟩⟩
  have hp : l.Pairwise (· ≤ ·) := (s.pairwise_sort (· ≤ ·)).filter _
  have hn : l.Nodup := (s.sort_nodup (· ≤ ·)).filter _
  have h := (List.toFinset_sort (r := (· ≤ ·)) hn).mpr hp
  rw [hl] at h
  exact h.symm

def finiteSupportCenter (c : ControlledContraction G) (p₀ : G) (v : I → G) (a : I →₀ ℝ) : G :=
  orderedCenter c p₀ v a (a.support.sort (· ≤ ·))

theorem finiteSupportCenter_eq_on_superset (c : ControlledContraction G) (p₀ : G)
    (v : I → G) (a : I →₀ ℝ) (s : Finset I) (hs : a.support ⊆ s)
    (ha : ∀ i, 0 ≤ a i) (hm : 0 < a.sum (fun _ r => r)) :
    finiteSupportCenter c p₀ v a = orderedCenter c p₀ v a (s.sort (· ≤ ·)) := by
  have hsum : listMass a (s.sort (· ≤ ·)) = a.sum (fun _ r => r) := by
    rw [listMass_sort, Finsupp.sum_of_support_subset _ hs _ (by simp)]
  have h := orderedCenter_filter_zero c p₀ v a (s.sort (· ≤ ·)) (fun i _ => ha i) (hsum.symm ▸ hm)
  rw [filter_sort_support a s hs] at h
  exact h

/-- A common finite support allows the list stability estimate to compare
two probability vectors, even when some coordinates vanish in just one. -/
theorem finiteSupportCenter_dist_le (c : ControlledContraction G) {D K : ℝ} {n : ℕ}
    (hK : InterpolationWeightControl (I := I) c D n K) (p₀ : G) (v : I → G)
    (a b : I →₀ ℝ) (s : Finset I)
    (has : a.support ⊆ s) (hbs : b.support ⊆ s) (hs : s.card ≤ n)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (ham : a.sum (fun _ r => r) = 1) (hbm : b.sum (fun _ r => r) = 1)
    (hdiam : ∀ i ∈ s, ∀ j ∈ s, dist (v i) (v j) ≤ D) :
    dist (finiteSupportCenter c p₀ v a) (finiteSupportCenter c p₀ v b) ≤
      K * (∑ i ∈ s, |a i - b i|) := by
  have hm (u : I →₀ ℝ) (hu : u.support ⊆ s) (hut : u.sum (fun _ r => r) = 1) :
      listMass u (s.sort (· ≤ ·)) = 1 := by
    rw [listMass_sort, ← Finsupp.sum_of_support_subset u hu (fun _ (r : ℝ) => r) (by simp), hut]
  rw [finiteSupportCenter_eq_on_superset c p₀ v a s has ha (by rw [ham]; norm_num),
    finiteSupportCenter_eq_on_superset c p₀ v b s hbs hb (by rw [hbm]; norm_num)]
  have h := hK (s.sort (· ≤ ·)) p₀ v a b (by simpa using hs)
    (fun i _ => ha i) (fun i _ => hb i)
    (fun i hi j hj => hdiam i ((Finset.mem_sort (· ≤ ·)).mp hi) j ((Finset.mem_sort (· ≤ ·)).mp hj))
  rw [hm a has ham, hm b hbs hbm, min_self, one_mul] at h
  simpa only [listVariation, listMass_sort] using h

theorem finiteSupportCenter_dist_anchor_le (c : ControlledContraction G) {D R : ℝ} {n : ℕ}
    (hR : InterpolationRadius (I := I) c D n R) (p₀ : G) (v : I → G) (a : I →₀ ℝ)
    (ha : ∀ i, 0 ≤ a i) (ham : a.sum (fun _ r => r) = 1) (hcard : a.support.card ≤ n)
    (hdiam : ∀ i ∈ a.support, ∀ j ∈ a.support, dist (v i) (v j) ≤ D)
    (p : G) (hp : ∀ i ∈ a.support, dist (v i) p ≤ D) :
    dist (finiteSupportCenter c p₀ v a) p ≤ R := by
  have hsum : listMass a (a.support.sort (· ≤ ·)) = 1 := by
    rw [listMass_sort]
    exact ham
  have hne : a.support.sort (· ≤ ·) ≠ [] := by
    intro hn
    rw [hn] at hsum
    norm_num [listMass] at hsum
  exact hR _ p₀ v a hne (by simpa using hcard) (fun i _ => ha i)
    (fun i hi j hj => hdiam i ((Finset.mem_sort (· ≤ ·)).mp hi) j ((Finset.mem_sort (· ≤ ·)).mp hj))
    p (fun i hi => hp i ((Finset.mem_sort (· ≤ ·)).mp hi))

end PolycyclicRecognition

end

end OAI
