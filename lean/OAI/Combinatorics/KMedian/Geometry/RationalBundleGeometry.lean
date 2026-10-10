import Mathlib
import OAI.Combinatorics.KMedian.Preparation.RepresentativeBundles
import OAI.Combinatorics.KMedian.Optimization.ComputedNearest

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.RationalBundles
open Finset
variable {n m : ℕ}

def next (d : Fin n → Fin n → ℚ) (t : Fin n) : Fin n :=
  if h : (univ.erase t).Nonempty then firstNearest (univ.erase t) (d t) h else t

def bundle (d : Fin n → Fin n → ℚ) (di : Fin n → Fin m → ℚ)
    (F : Fin n → Finset (Fin m)) (δ : ℚ) (t : Fin n) : Finset (Fin m) :=
  if next d t=t then F t else (F t).filter (fun a => di t a ≤ δ*d t (next d t))

def missing (d : Fin n → Fin n → ℚ) (di : Fin n → Fin m → ℚ)
    (F : Fin n → Finset (Fin m)) (δ : ℚ) (t : Fin n) : Finset (Fin m) :=
  F t \ bundle d di F δ t

def mass (y : Fin m → ℚ) (P : Fin n → Finset (Fin m)) (t : Fin n) : ℚ := ∑ a ∈ P t, y a

theorem next_self (d : Fin n → Fin n → ℚ) (t : Fin n) (h : next d t=t) : ∀ u, u=t := by
  intro u
  by_contra hu
  have hn : (univ.erase t).Nonempty := ⟨u, mem_erase.mpr ⟨hu,mem_univ _⟩⟩
  have hm := (firstNearest_spec (univ.erase t) (d t) hn).1
  simp only [next, dite_eq_left hn] at h
  rw [h] at hm
  exact notMem_erase _ _ hm

theorem next_min (d : Fin n → Fin n → ℚ) (t u : Fin n) (htu : t≠u) :
    d t (next d t) ≤ d t u := by
  have hn : (univ.erase t).Nonempty := ⟨u,mem_erase.mpr ⟨htu.symm,mem_univ _⟩⟩
  simp only [next,dite_eq_left hn]
  exact (firstNearest_spec _ _ hn).2 u (mem_erase.mpr ⟨htu.symm,mem_univ _⟩)

theorem bundle_sub (d : Fin n → Fin n → ℚ) (di : Fin n → Fin m → ℚ)
    (F : Fin n → Finset (Fin m)) (δ : ℚ) (t : Fin n) : bundle d di F δ t ⊆ F t := by
  unfold bundle
  split_ifs
  · exact Subset.rfl
  · exact filter_subset _ _

noncomputable def geometry {X : Type} [PseudoMetricSpace X]
    (F : Fin n → Finset (Fin m)) (y : Fin m → ℚ) (s : Fin n → X) (i : Fin m → X)
    (d : Fin n → Fin n → ℚ) (di : Fin n → Fin m → ℚ) (V : Fin n → ℚ) (M δ : ℚ)
    (hd : ∀ t u, dist (s t) (s u)=(d t u:ℝ))
    (hdi : ∀ t a, dist (s t) (i a)=(di t a:ℝ))
    (hy : ∀ a, 0 < y a) (hM : 0 < M) (hδ : 0 < δ) (hδ1 : (δ:ℝ) < 1/2)
    (hu : ∀ t, ∑ a ∈ F t, y a=1)
    (hv : ∀ t, ∑ a ∈ F t, y a*di t a=V t)
    (hs : ∀ t u, t ≠ u → M*max (V t) (V u) < d t u) :
    BundleGeometry F (fun a => (y a:ℝ)) s i (fun t => (V t:ℝ)) (M:ℝ) (δ:ℝ) := by
  let P := bundle d di F δ
  let A := missing d di F δ
  let p := mass y P
  let c := mass y A
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  have hδ' : (0:ℝ) < δ := by exact_mod_cast hδ
  have hy' : ∀ a, (0:ℝ) < y a := by intro a; exact_mod_cast hy a
  have hu' : ∀ t, ∑ a ∈ F t, (y a:ℝ)=1 := by intro t; exact_mod_cast hu t
  have hv' : ∀ t, ∑ a ∈ F t, (y a:ℝ)*dist (s t) (i a)=(V t:ℝ) := by
    intro t
    simp only [hdi]
    exact_mod_cast hv t
  have hV : ∀ t, (0:ℝ) ≤ V t := fun t => (hv' t) ▸
    sum_nonneg (fun a _ => mul_nonneg (hy' a).le dist_nonneg)
  have hsub : ∀ t, P t ⊆ F t := bundle_sub d di F δ
  have hcm : ∀ t, (c t:ℝ)=∑ a ∈ A t, (y a:ℝ) := by intro t; simp only [c,mass,Rat.cast_sum]
  have hpm : ∀ t, (p t:ℝ)=∑ a ∈ P t, (y a:ℝ) := by intro t; simp only [p,mass,Rat.cast_sum]
  have hunit : ∀ t, (p t:ℝ)+(c t:ℝ)=1 := by
    intro t
    rw [hpm,hcm]
    change (∑ a ∈ P t, (y a:ℝ))+(∑ a ∈ F t \ P t, (y a:ℝ))=1
    rw [add_comm,sum_sdiff (hsub t),hu']
  have hc : ∀ t, (0:ℝ) ≤ c t := by intro t; rw [hcm]; exact sum_nonneg (fun a _ => (hy' a).le)
  have hzero : ∀ t, next d t=t → c t=0 := by
    intro t ht
    simp [c,mass,A,missing,bundle,ht]
  have hL : ∀ t, next d t≠t → M*V t < d t (next d t) := by
    intro t ht
    exact (mul_le_mul_of_nonneg_left (le_max_left _ _) hM.le).trans_lt
      (hs t (next d t) ht.symm)
  have hcharge : ∀ t, (δ:ℝ)*dist (s t) (s (next d t))*(c t:ℝ) ≤ (V t:ℝ) := by
    intro t
    by_cases ht : next d t=t
    · rw [hzero t ht,Rat.cast_zero,mul_zero]
      exact hV t
    · have he : A t=(F t).filter (fun a => (δ:ℝ)*dist (s t) (s (next d t))<dist (s t) (i a)) := by
        ext a
        simp only [A,missing,bundle,ite_eq_right ht,mem_sdiff,mem_filter,not_and,hd,hdi]
        have hcast : ((δ*d t (next d t):ℚ):ℝ)= (δ:ℝ)*(d t (next d t):ℝ) := by push_cast; rfl
        rw [← hcast, Rat.cast_lt]
        constructor
        · rintro ⟨ha,hb⟩
          exact ⟨ha,lt_of_not_ge (hb ha)⟩
        · rintro ⟨ha,hb⟩
          exact ⟨ha,fun _ => not_le.mpr hb⟩
      rw [hcm,he]
      exact (outside_mass_bound (F t) (fun a => (y a:ℝ)) (fun a => dist (s t) (i a))
        (fun a _ => (hy' a).le) (fun _ _ => dist_nonneg)).trans_eq (hv' t)
  have hsmall : ∀ t, (c t:ℝ) ≤ 1/((M:ℝ)*(δ:ℝ)) := by
    intro t
    by_cases ht : next d t=t
    · rw [hzero t ht,Rat.cast_zero]
      positivity
    · have hVL : (M:ℝ)*(V t:ℝ)<dist (s t) (s (next d t)) := by
        rw [hd]
        exact_mod_cast hL t ht
      have hLp : 0 < dist (s t) (s (next d t)) :=
        (mul_nonneg hM'.le (hV t)).trans_lt hVL
      exact deficit_small hM' hδ' hLp (hcharge t) hVL.le
  refine {
    P := P
    A := A
    p := fun t => (p t:ℝ)
    c := fun t => (c t:ℝ)
    L := fun t => dist (s t) (s (next d t))
    next := next d
    sub := hsub
    missing := fun _ => rfl
    mass := fun t => (hpm t).symm
    deficit_mass := fun t => (hcm t).symm
    unit := hunit
    nonneg := hc
    small := hsmall
    large := fun t => by linarith only [hunit t,hsmall t]
    disjoint := ?_
    next_distance := fun _ => rfl
    closest := ?_
    radius := ?_
    outside_radius := ?_
    self_singleton := next_self d
    self_zero := by intro t ht; rw [hzero t ht,Rat.cast_zero]
    zero_full := ?_
    charge := hcharge }
  · intro t u htu
    apply disjoint_left.mpr
    intro a ha hb
    have ht : next d t≠t := fun hh => htu ((next_self d t hh u).symm)
    have hu : next d u≠u := fun hh => htu (next_self d u hh t)
    have hdist : 0 < dist (s t) (s u) := by
      rw [hd]
      have hh : (M:ℝ)*max (V t:ℝ) (V u:ℝ) < (d t u:ℝ) := by exact_mod_cast hs t u htu
      exact (mul_nonneg hM'.le ((hV t).trans (le_max_left _ _))).trans_lt hh
    have hta : (di t a:ℝ) ≤ (δ:ℝ)*(d t (next d t):ℝ) := by
      have h := (mem_filter.mp (show a ∈ (F t).filter (fun b => di t b ≤ δ*d t (next d t)) by
        simpa only [P,bundle,ite_eq_right ht] using ha)).2
      exact_mod_cast h
    have hua : (di u a:ℝ) ≤ (δ:ℝ)*(d u (next d u):ℝ) := by
      have h := (mem_filter.mp (show a ∈ (F u).filter (fun b => di u b ≤ δ*d u (next d u)) by
        simpa only [P,bundle,ite_eq_right hu] using hb)).2
      exact_mod_cast h
    exact bundle_disjoint_geometry (s t) (s u) (i a)
      (Ls := dist (s t) (s (next d t))) (Lt := dist (s u) (s (next d u))) hδ'.le hδ1 hdist
      (by rw [hd,hd]; exact_mod_cast next_min d t u htu)
      (by rw [dist_comm (s t) (s u),hd,hd]; exact_mod_cast next_min d u t htu.symm)
      (by rwa [hdi,hd]) (by rwa [hdi,hd])
  · intro t u htu
    rw [hd,hd]
    exact_mod_cast next_min d t u htu
  · intro t ht a ha
    have h := (mem_filter.mp (show a ∈ (F t).filter (fun b => di t b ≤ δ*d t (next d t)) by
      simpa only [P,bundle,ite_eq_right ht] using ha)).2
    rw [hdi,hd]
    exact_mod_cast h
  · intro t ht a ha
    have h := mem_sdiff.mp ha
    have hh : ¬ di t a ≤ δ*d t (next d t) := by
      intro hh
      apply h.2
      simp only [bundle,ite_eq_right ht,mem_filter]
      exact ⟨h.1,hh⟩
    rw [hdi,hd]
    exact_mod_cast lt_of_not_ge hh
  · intro t ht
    apply Subset.antisymm (hsub t)
    intro a ha
    by_contra hpa
    have hle : (y a:ℝ) ≤ (c t:ℝ) := by
      rw [hcm]
      exact single_le_sum (fun b _ => (hy' b).le) (mem_sdiff.mpr ⟨ha,hpa⟩)
    rw [ht] at hle
    exact not_lt_of_ge hle (hy' a)

end MetricKMedian.Preparation.RationalBundles
end

end OAI
