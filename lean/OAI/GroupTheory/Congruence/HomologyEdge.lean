import Mathlib

namespace OAI

/-!
Abstract augmented resolutions and bounded homology edge surjectivity.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace CoboundaryExpanders.HomologyEdge

section
universe u
variable {k G : Type u} [CommRing k] [Group G]

structure ResolutionPieces where
  K : ℕ → Rep.{u} k G
  C : ℕ → Rep.{u} k G
  inc : ∀ s, K (s+1) ⟶ C s
  sur : ∀ s, C s ⟶ K s
  zero : ∀ s, inc s ≫ sur s = 0
  exact : ∀ s, (ShortComplex.mk (inc s) (sur s) (zero s)).ShortExact

variable (P : ResolutionPieces (k := k) (G := G))

abbrev short (s : ℕ) := ShortComplex.mk (P.inc s) (P.sur s) (P.zero s)
abbrev Hmap {A B : Rep.{u} k G} (f : A ⟶ B) (n : ℕ) := (groupHomology.functor k G n).map f

lemma delta_zero_of_mono (s : ℕ) [Mono (Hmap (P.inc s) 0)] :
    groupHomology.δ (P.exact s) 1 0 rfl = 0 := by
  apply (groupHomology.mapShortComplex₁_exact (P.exact s) rfl).mono_g_iff.mp
  change Mono (Hmap (P.inc s) 0)
  infer_instance

theorem kernel_homology_isZero (e s : ℕ)
    (hV : ∀ t ≤ e, IsZero (groupHomology (P.C (s+t)) (e+1-t)))
    (hb : Mono (Hmap (P.inc (s+e)) 0)) :
    IsZero (groupHomology (P.K s) (e+1)) := by
  induction e generalizing s with
  | zero =>
    have hv : IsZero (groupHomology (P.C s) 1) := by simpa using hV 0 (by omega)
    have : Mono (Hmap (P.inc s) 0) := by simpa using hb
    have := groupHomology.mono_δ_of_isZero (P.exact s) 0 hv
    exact IsZero.of_mono_eq_zero _ (delta_zero_of_mono P s)
  | succ e ih =>
    have hv : IsZero (groupHomology (P.C s) (e+2)) := by simpa using hV 0 (by omega)
    have := groupHomology.mono_δ_of_isZero (P.exact s) (e+1) hv
    apply IsZero.of_mono (groupHomology.δ (P.exact s) (e+2) (e+1) rfl)
    apply ih (s+1)
    · intro t ht
      have hv' := hV (t+1) (by omega)
      have ha : s+(t+1) = s+1+t := by omega
      have hd : e+1+1-(t+1) = e+1-t := by omega
      rw [ha, hd] at hv'
      exact hv'
    · have ha : s+1+e = s+(e+1) := by omega
      rw [ha]
      exact hb

theorem epi_edge (q : ℕ)
    (hV : ∀ t, 1 ≤ t → t ≤ q → IsZero (groupHomology (P.C t) (q+1-t)))
    (hb : Mono (Hmap (P.inc q) 0)) : Epi (Hmap (P.sur 0) (q+1)) := by
  apply (groupHomology.mapShortComplex₃_exact (P.exact 0) rfl).epi_f
  change groupHomology.δ (P.exact 0) (q+1) q rfl = 0
  cases q with
  | zero =>
    have := hb
    exact delta_zero_of_mono P 0
  | succ q =>
    apply IsZero.eq_zero_of_tgt
    apply kernel_homology_isZero P q 1
    · intro t ht
      have hv' := hV (1+t) (by omega) (by omega)
      have hd : q+1+1-(1+t) = q+1-t := by omega
      rw [hd] at hv'
      exact hv'
    · have ha : 1+q = q+1 := by omega
      rw [ha]
      exact hb

lemma mono_H0_inc (s : ℕ)
    (he : ∀ x : groupHomology (P.C (s+1)) 0,
      Hmap (P.sur (s+1) ≫ P.inc s) 0 x = 0 →
      ∃ y : groupHomology (P.C (s+2)) 0,
        Hmap (P.sur (s+2) ≫ P.inc (s+1)) 0 y = x) :
    Mono (Hmap (P.inc s) 0) := by
  have : Epi (P.sur (s+1)) := (P.exact (s+1)).epi_g
  have : Epi (Hmap (P.sur (s+1)) 0) := groupHomology.epi_map_0_of_epi _
  rw [ModuleCat.mono_iff_injective]
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨y,hy⟩ := (ModuleCat.epi_iff_surjective (Hmap (P.sur (s+1)) 0)).mp inferInstance x
  have hz : Hmap (P.sur (s+1) ≫ P.inc s) 0 y = 0 := by
    simp only [Hmap, Functor.map_comp]
    change Hmap (P.inc s) 0 (Hmap (P.sur (s+1)) 0 y) = 0
    rw [hy]
    exact hx
  obtain ⟨z,hz⟩ := he y hz
  rw [← hy, ← hz]
  change (Hmap (P.sur (s+2) ≫ P.inc (s+1)) 0 ≫ Hmap (P.sur (s+1)) 0) z = 0
  simp only [Hmap, ← Functor.map_comp, Category.assoc, P.zero, comp_zero, Functor.map_zero]
  rfl

namespace Bounded
structure BoundedPieces (N : ℕ) where
  K : ℕ → Rep.{u} k G
  C : ℕ → Rep.{u} k G
  inc : ∀ s, K (s+1) ⟶ C s
  sur : ∀ s, C s ⟶ K s
  zero : ∀ s, inc s ≫ sur s = 0
  exact : ∀ s, s ≤ N → (ShortComplex.mk (inc s) (sur s) (zero s)).ShortExact

variable {N : ℕ} (P : BoundedPieces (k := k) (G := G) N)

abbrev short (s : ℕ) := ShortComplex.mk (P.inc s) (P.sur s) (P.zero s)
abbrev Hmap {A B : Rep.{u} k G} (f : A ⟶ B) (n : ℕ) := (groupHomology.functor k G n).map f

lemma delta_zero_of_mono (s : ℕ) (hs : s ≤ N) [Mono (Hmap (P.inc s) 0)] :
    groupHomology.δ (P.exact s hs) 1 0 rfl = 0 := by
  apply (groupHomology.mapShortComplex₁_exact (P.exact s hs) rfl).mono_g_iff.mp
  change Mono (Hmap (P.inc s) 0)
  infer_instance

theorem kernel_homology_isZero (e s : ℕ) (hN : s+e ≤ N)
    (hV : ∀ t ≤ e, IsZero (groupHomology (P.C (s+t)) (e+1-t)))
    (hb : Mono (Hmap (P.inc (s+e)) 0)) :
    IsZero (groupHomology (P.K s) (e+1)) := by
  induction e generalizing s with
  | zero =>
    have hs : s ≤ N := by omega
    have hv : IsZero (groupHomology (P.C s) 1) := by simpa using hV 0 (by omega)
    have : Mono (Hmap (P.inc s) 0) := by simpa using hb
    have := groupHomology.mono_δ_of_isZero (P.exact s hs) 0 hv
    exact IsZero.of_mono_eq_zero _ (delta_zero_of_mono P s hs)
  | succ e ih =>
    have hs : s ≤ N := by omega
    have hv : IsZero (groupHomology (P.C s) (e+2)) := by simpa using hV 0 (by omega)
    have := groupHomology.mono_δ_of_isZero (P.exact s hs) (e+1) hv
    apply IsZero.of_mono (groupHomology.δ (P.exact s hs) (e+2) (e+1) rfl)
    apply ih (s+1) (by omega)
    · intro t ht
      have hv' := hV (t+1) (by omega)
      have ha : s+(t+1) = s+1+t := by omega
      have hd : e+1+1-(t+1) = e+1-t := by omega
      rw [ha, hd] at hv'
      exact hv'
    · have ha : s+1+e = s+(e+1) := by omega
      rw [ha]
      exact hb

theorem epi_edge (q : ℕ) (hN : q ≤ N)
    (hV : ∀ t, 1 ≤ t → t ≤ q → IsZero (groupHomology (P.C t) (q+1-t)))
    (hb : Mono (Hmap (P.inc q) 0)) : Epi (Hmap (P.sur 0) (q+1)) := by
  apply (groupHomology.mapShortComplex₃_exact (P.exact 0 (by omega)) rfl).epi_f
  change groupHomology.δ (P.exact 0 (by omega)) (q+1) q rfl = 0
  cases q with
  | zero =>
    have := hb
    exact delta_zero_of_mono P 0 (by omega)
  | succ q =>
    apply IsZero.eq_zero_of_tgt
    apply kernel_homology_isZero P q 1 (by omega)
    · intro t ht
      have hv' := hV (1+t) (by omega) (by omega)
      have hd : q+1+1-(1+t) = q+1-t := by omega
      rw [hd] at hv'
      exact hv'
    · have ha : 1+q = q+1 := by omega
      rw [ha]
      exact hb

lemma mono_H0_inc (s : ℕ) (hN : s+1 ≤ N)
    (he : ∀ x : groupHomology (P.C (s+1)) 0,
      Hmap (P.sur (s+1) ≫ P.inc s) 0 x = 0 →
      ∃ y : groupHomology (P.C (s+2)) 0,
        Hmap (P.sur (s+2) ≫ P.inc (s+1)) 0 y = x) :
    Mono (Hmap (P.inc s) 0) := by
  have : Epi (P.sur (s+1)) := (P.exact (s+1) hN).epi_g
  have : Epi (Hmap (P.sur (s+1)) 0) := groupHomology.epi_map_0_of_epi _
  rw [ModuleCat.mono_iff_injective]
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨y,hy⟩ := (ModuleCat.epi_iff_surjective (Hmap (P.sur (s+1)) 0)).mp inferInstance x
  have hz : Hmap (P.sur (s+1) ≫ P.inc s) 0 y = 0 := by
    simp only [Hmap, Functor.map_comp]
    change Hmap (P.inc s) 0 (Hmap (P.sur (s+1)) 0 y) = 0
    rw [hy]
    exact hx
  obtain ⟨z,hz⟩ := he y hz
  rw [← hy, ← hz]
  change (Hmap (P.sur (s+2) ≫ P.inc (s+1)) 0 ≫ Hmap (P.sur (s+1)) 0) z = 0
  simp only [Hmap, ← Functor.map_comp, Category.assoc, P.zero, comp_zero, Functor.map_zero]
  rfl

end Bounded
end

universe u
variable {k G : Type u} [CommRing k] [Group G]

structure AugmentedData where
  D : ℕ → Rep.{u} k G
  d : ∀ s, D (s+1) ⟶ D s
  square : ∀ s, d (s+1) ≫ d s = 0

namespace AugmentedData
variable (A : AugmentedData (k := k) (G := G))
def K : ℕ → Rep.{u} k G
  | 0 => A.D 0
  | s+1 => kernel (A.d s)
def inc (s : ℕ) : A.K (s+1) ⟶ A.D (s+1) := kernel.ι (A.d s)
instance inc_mono (s : ℕ) : Mono (A.inc s) := by
  change Mono (kernel.ι (A.d s))
  infer_instance
def sur : ∀ s, A.D (s+1) ⟶ A.K s
  | 0 => A.d 0
  | s+1 => kernel.lift (A.d s) (A.d (s+1)) (A.square s)
@[simp] lemma sur_inc (s : ℕ) : A.sur (s+1) ≫ A.inc s = A.d (s+1) := by
  exact kernel.lift_ι _ _ _
lemma zero (s : ℕ) : A.inc s ≫ A.sur s = 0 := by
  cases s with
  | zero => exact kernel.condition _
  | succ s =>
    rw [← cancel_mono (A.inc s), Category.assoc, sur_inc, zero_comp]
    exact kernel.condition _

lemma short_exact (s : ℕ) [Epi (A.sur s)] :
    (ShortComplex.mk (A.inc s) (A.sur s) (A.zero s)).ShortExact := by
  refine {exact := ?_, mono_f := inferInstance, epi_g := inferInstance}
  refine ShortComplex.exact_of_f_is_kernel
    (ShortComplex.mk (A.inc s) (A.sur s) (A.zero s)) ?_
  cases s with
  | zero => exact kernelIsKernel _
  | succ s =>
    apply KernelFork.IsLimit.ofι'
    intro W f hf
    have hfd : f ≫ A.d (s+1) = 0 := by
      rw [← A.sur_inc s, ← Category.assoc, hf, zero_comp]
    exact ⟨kernel.lift (A.d (s+1)) f hfd, kernel.lift_ι _ _ _⟩

def pieces (N : ℕ) (h0 : Epi (A.d 0))
    (he : ∀ s, s < N → (ShortComplex.mk (A.d (s+1)) (A.d s) (A.square s)).Exact) :
    Bounded.BoundedPieces (k := k) (G := G) N where
  K := A.K
  C s := A.D (s+1)
  inc := A.inc
  sur := A.sur
  zero := A.zero
  exact s hs := by
    have : Epi (A.sur s) := by
      cases s with
      | zero => exact h0
      | succ s => exact (he s (by omega)).epi_kernelLift
    exact A.short_exact s

lemma epi_edge (q : ℕ) (h0 : Epi (A.d 0))
    (he : ∀ s, s ≤ q → (ShortComplex.mk (A.d (s+1)) (A.d s) (A.square s)).Exact)
    (hV : ∀ t, 1 ≤ t → t ≤ q → IsZero (groupHomology (A.D (t+1)) (q+1-t)))
    (hq : ∀ x : groupHomology (A.D (q+2)) 0,
      Hmap (A.d (q+1)) 0 x = 0 → ∃ y : groupHomology (A.D (q+3)) 0,
        Hmap (A.d (q+2)) 0 y = x) : Epi (Hmap (A.d 0) (q+1)) := by
  let P := A.pieces (q+1) h0 (fun s hs => he s (by omega))
  have hmono : Mono (Bounded.Hmap (P.inc q) 0) := by
    apply Bounded.mono_H0_inc P q (by omega)
    change ∀ x : groupHomology (A.D (q+2)) 0,
      Hmap (A.sur (q+1) ≫ A.inc q) 0 x = 0 →
      ∃ y : groupHomology (A.D (q+3)) 0,
        Hmap (A.sur (q+2) ≫ A.inc (q+1)) 0 y = x
    simpa only [sur_inc] using hq
  exact Bounded.epi_edge P q (by omega) hV hmono
end AugmentedData
end CoboundaryExpanders.HomologyEdge

end

end OAI
