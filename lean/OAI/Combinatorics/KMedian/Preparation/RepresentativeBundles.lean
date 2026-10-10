import Mathlib
import OAI.Combinatorics.KMedian.Preparation.RepresentativeGeometry

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {T I X : Type*} [Fintype T] [DecidableEq T] [DecidableEq I]
  [PseudoMetricSpace X]

structure BundleGeometry (F : T → Finset I) (y : I → ℝ) (s : T → X) (i : I → X)
    (V : T → ℝ) (M δ : ℝ) where
  P : T → Finset I
  A : T → Finset I
  p : T → ℝ
  c : T → ℝ
  L : T → ℝ
  next : T → T
  sub : ∀ t, P t ⊆ F t
  missing : ∀ t, A t=F t \ P t
  mass : ∀ t, ∑ a ∈ P t, y a=p t
  deficit_mass : ∀ t, ∑ a ∈ A t, y a=c t
  unit : ∀ t, p t+c t=1
  nonneg : ∀ t, 0 ≤ c t
  small : ∀ t, c t ≤ 1/(M*δ)
  large : ∀ t, 1-1/(M*δ) ≤ p t
  disjoint : Pairwise (fun t u => Disjoint (P t) (P u))
  next_distance : ∀ t, L t=dist (s t) (s (next t))
  closest : ∀ t u, t ≠ u → L t ≤ dist (s t) (s u)
  radius : ∀ t, next t ≠ t → ∀ a ∈ P t, dist (s t) (i a) ≤ δ*L t
  outside_radius : ∀ t, next t ≠ t → ∀ a ∈ A t, δ*L t < dist (s t) (i a)
  self_singleton : ∀ t, next t=t → ∀ u, u=t
  self_zero : ∀ t, next t=t → c t=0
  zero_full : ∀ t, c t=0 → P t=F t
  charge : ∀ t, δ*L t*c t ≤ V t

theorem bundle_geometry (F : T → Finset I) (y : I → ℝ) (s : T → X) (i : I → X)
    (V : T → ℝ) {M δ : ℝ} (hy : ∀ a, 0 < y a)
    (hM : 0 < M) (hδ : 0 < δ) (hδ1 : δ < 1/2)
    (hunit : ∀ t, ∑ a ∈ F t, y a=1)
    (hcost : ∀ t, ∑ a ∈ F t, y a*dist (s t) (i a)=V t)
    (hsep : ∀ t u, t ≠ u → M*max (V t) (V u) < dist (s t) (s u)) :
    Nonempty (BundleGeometry F y s i V M δ) := by
  classical
  have hV : ∀ t, 0 ≤ V t := fun t => (hcost t) ▸
    sum_nonneg (fun a _ => mul_nonneg (hy a).le dist_nonneg)
  by_cases hsingle : Subsingleton T
  · let := hsingle
    refine ⟨{
      P := F
      A := fun _ => ∅
      p := fun _ => 1
      c := fun _ => 0
      L := fun _ => 0
      next := id
      sub := fun _ => Subset.rfl
      missing := by simp
      mass := hunit
      deficit_mass := by simp
      unit := by simp
      nonneg := by simp
      small := fun _ => by positivity
      large := fun _ => sub_le_self _ (by positivity)
      disjoint := fun t u htu => (htu (Subsingleton.elim _ _)).elim
      next_distance := by simp
      closest := fun t u htu => (htu (Subsingleton.elim _ _)).elim
      radius := fun t ht => (ht rfl).elim
      outside_radius := fun t ht => (ht rfl).elim
      self_singleton := fun _ _ _ => Subsingleton.elim _ _
      self_zero := by simp
      zero_full := by simp
      charge := fun t => by simpa only [mul_zero] using hV t }⟩
  · have : Nontrivial T := not_subsingleton_iff_nontrivial.mp hsingle
    have hother : ∀ t : T, (univ.erase t).Nonempty := by
      intro t
      obtain ⟨u,hu⟩ := exists_ne t
      exact ⟨u,mem_erase.mpr ⟨hu,mem_univ _⟩⟩
    choose next hnext hmin using fun t => (univ.erase t).exists_min_image
      (fun u => dist (s t) (s u)) (hother t)
    have hn : ∀ t, next t ≠ t := fun t => (mem_erase.mp (hnext t)).1
    let L := fun t => dist (s t) (s (next t))
    have hl : ∀ t u, t ≠ u → L t ≤ dist (s t) (s u) := by
      intro t u htu
      exact hmin t u (mem_erase.mpr ⟨htu.symm,mem_univ _⟩)
    have hLV : ∀ t, M*V t < L t := by
      intro t
      exact (mul_le_mul_of_nonneg_left (le_max_left _ _) hM.le).trans_lt
        (hsep t (next t) (hn t).symm)
    have hL : ∀ t, 0 < L t := fun t => lt_of_le_of_lt (mul_nonneg hM.le (hV t)) (hLV t)
    let P := fun t => (F t).filter (fun a => dist (s t) (i a) ≤ δ*L t)
    let A := fun t => F t \ P t
    let p := fun t => ∑ a ∈ P t, y a
    let c := fun t => ∑ a ∈ A t, y a
    have hsub : ∀ t, P t ⊆ F t := fun t => filter_subset _ _
    have hu : ∀ t, p t+c t=1 := by
      intro t
      dsimp only [p,c,A]
      rw [add_comm,sum_sdiff (hsub t),hunit t]
    have hc : ∀ t, 0 ≤ c t := fun t => sum_nonneg (fun a _ => (hy a).le)
    have hA : ∀ t, A t=(F t).filter (fun a => δ*L t < dist (s t) (i a)) := by
      intro t
      ext a
      simp only [A,P,mem_sdiff,mem_filter,not_and,not_le]
      tauto
    have hd : ∀ t, δ*L t*c t ≤ V t := by
      intro t
      dsimp only [c]
      rw [hA t]
      exact (outside_mass_bound (F t) y (fun a => dist (s t) (i a))
        (fun a _ => (hy a).le) (fun _ _ => dist_nonneg)).trans_eq (hcost t)
    have hs : ∀ t, c t ≤ 1/(M*δ) := fun t => deficit_small hM hδ (hL t) (hd t) (hLV t).le
    refine ⟨{
      P := P
      A := A
      p := p
      c := c
      L := L
      next := next
      sub := hsub
      missing := fun _ => rfl
      mass := fun _ => rfl
      deficit_mass := fun _ => rfl
      unit := hu
      nonneg := hc
      small := hs
      large := fun t => by linarith only [hu t,hs t]
      disjoint := ?_
      next_distance := fun _ => rfl
      closest := hl
      radius := fun _ _ _ ha => (mem_filter.mp ha).2
      outside_radius := fun t _ a ha => by
        have hh : a ∈ (F t).filter (fun a => δ*L t < dist (s t) (i a)) := (hA t) ▸ ha
        exact (mem_filter.mp hh).2
      self_singleton := fun t ht => (hn t ht).elim
      self_zero := fun t ht => (hn t ht).elim
      zero_full := ?_
      charge := hd }⟩
    · intro t u htu
      apply disjoint_left.mpr
      intro a ha hb
      have hdist : 0 < dist (s t) (s u) := lt_of_le_of_lt
        (mul_nonneg hM.le (le_trans (hV t) (le_max_left _ _))) (hsep t u htu)
      exact bundle_disjoint_geometry (s t) (s u) (i a) hδ.le hδ1 hdist
        (hl t u htu) ((hl u t htu.symm).trans_eq (dist_comm _ _))
        (mem_filter.mp ha).2 (mem_filter.mp hb).2
    · intro t ht
      apply Subset.antisymm (hsub t)
      intro a ha
      by_contra hpa
      have haA : a ∈ A t := mem_sdiff.mpr ⟨ha,hpa⟩
      have hle : y a ≤ c t := single_le_sum (fun b _ => (hy b).le) haA
      rw [ht] at hle
      exact (not_lt_of_ge hle) (hy a)

end MetricKMedian.Preparation
end
end

end OAI
