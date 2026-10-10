import Mathlib
import OAI.Geometry.Borsuk.Simplicial.UnitRadial
import OAI.Geometry.Borsuk.Simplicial.GeneralTarget

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
section Supports
variable {E ι : Type*} [NormedAddCommGroup E] [DecidableEq ι]

def supportComplex (f : E → ι → ℝ) : PreAbstractSimplicialComplex ι where
  faces := {s | s.Nonempty ∧ ∃ x : E, ‖x‖ = 1 ∧ ∀ i ∈ s, 0 < f x i}
  isRelLowerSet_faces := by
    rintro s ⟨hs,x,hx,hi⟩
    exact ⟨hs, fun t hts ht => ⟨ht,x,hx,fun i h => hi i (hts h)⟩⟩

end Supports

lemma annulus_ne_zero (n : ℕ) (hn : 0 < n) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ annulus n) : x ≠ 0 := by
  intro hzero
  have hp : (0:ℝ) < 1/(n:ℝ) := div_pos zero_lt_one (by exact_mod_cast hn)
  simp only [annulus, Set.mem_ofPred_eq, hzero, norm_zero] at hx
  linarith [hx.1]

lemma maxIndex_partition_large {m : ℕ} [NeZero m] (g : Fin m → ℝ)
    (hg : ∑ i, g i = 1) : (1:ℝ)/m ≤ g (maxIndex g) := by
  have h : ∑ i : Fin m, g i ≤ (m:ℝ)*g (maxIndex g) := by
    calc
      ∑ i, g i ≤ ∑ _i : Fin m, g (maxIndex g) := Finset.sum_le_sum (fun i _ => maxIndex_le g i)
      _ = _ := by simp
  rw [hg] at h
  exact (div_le_iff₀ (by exact_mod_cast NeZero.pos m)).mpr (by nlinarith)

noncomputable def supportLabel {n m : ℕ} [NeZero m]
    (f : EuclideanSpace ℝ (Fin n) → Fin m → ℝ) (x : EuclideanSpace ℝ (Fin n)) : Fin m :=
  maxIndex (f (unitRadial x))

lemma supportLabel_even {n m : ℕ} [NeZero m]
    (f : EuclideanSpace ℝ (Fin n) → Fin m → ℝ) (hf : ∀ x i, f (-x) i = f x i)
    (x : EuclideanSpace ℝ (Fin n)) : supportLabel f (-x) = supportLabel f x := by
  unfold supportLabel
  rw [unitRadial_neg]
  congr 1
  exact funext (hf _)

lemma exists_fine_supportLabel {n m : ℕ} (hn : 0 < n) [NeZero m]
    (f : EuclideanSpace ℝ (Fin n) → Fin m → ℝ)
    (hc : Continuous f) (hs : ∀ x, ‖x‖ = 1 → ∑ i, f x i = 1) :
    ∃ r, FineTo n r (supportComplex f) (supportLabel f) := by
  classical
  let g : EuclideanSpace ℝ (Fin n) → Fin m → ℝ := fun x => f (unitRadial x)
  have hg : ContinuousOn g (annulus n) := hc.comp_continuousOn
    (unitRadial_continuousOn (fun _ hx => annulus_ne_zero n hn hx))
  have hunif := (annulus_compact n).uniformContinuousOn_of_continuous hg
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp hunif ((1:ℝ)/m)
    (div_pos zero_lt_one (by exact_mod_cast NeZero.pos m))
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hq : ((n:ℝ)-1)/n < 1 := (div_lt_one hn').mpr (by linarith)
  obtain ⟨r,hr⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < δ/2 by linarith) hq
  have hmeshδ : (((n:ℝ)-1)/n)^r * 2 < δ := by linarith
  refine ⟨r,?_⟩
  intro s hsf t ht
  obtain ⟨x,hx⟩ := t.property.1
  have hxa := hemisphere_vertex_annulus n hn t.property hx
  refine ⟨t.property.1.image _, unitRadial x, unitRadial_norm (annulus_ne_zero n hn hxa), ?_⟩
  intro i hi
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hi
  have hya := hemisphere_vertex_annulus n hn t.property hy
  have hxy := hclose x hxa y hya ((fineCrossMap_simplex_mesh n r hsf ht x hx y hy).trans_lt hmeshδ)
  have hl := maxIndex_partition_large (g y) (hs _ (unitRadial_norm (annulus_ne_zero n hn hya)))
  have hd : |g x (maxIndex (g y)) - g y (maxIndex (g y))| < (1:ℝ)/m := by
    rw [← Real.dist_eq]
    exact (dist_le_pi_dist (g x) (g y) (maxIndex (g y))).trans_lt hxy
  change 0 < g x (maxIndex (g y))
  have hd' := (abs_lt.mp hd).1
  linarith

lemma even_partition_support_cycle {n m : ℕ} (hn : 1 < n) [NeZero m]
    (f : EuclideanSpace ℝ (Fin n) → Fin m → ℝ)
    (hc : Continuous f) (hs : ∀ x, ‖x‖ = 1 → ∑ i, f x i = 1)
    (he : ∀ x i, f (-x) i = f x i) :
    ∃ r, FineTo n r (supportComplex f) (supportLabel f) ∧
      projectiveCycle n r (supportComplex f) (supportLabel f) ∈ degreeChains (supportComplex f) n ∧
      boundary (supportComplex f) (projectiveCycle n r (supportComplex f) (supportLabel f)) = 0 := by
  obtain ⟨r,hr⟩ := exists_fine_supportLabel (by omega : 0 < n) f hc hs
  exact ⟨r,hr,projectiveCycle_degree n r (by omega) _ _,
    projectiveCycle_boundary n r hn _ _ hr (fun x _ => supportLabel_even f he x)⟩

end BorsukNine.SimplicialChains

end OAI
