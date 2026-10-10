import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialGroupDifference
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentLangMap

namespace OAI

/-! # Polynomial Lang transversals from an invertible leading term

All nonlinear errors raise the finite lower central filtration. The inverse
is therefore obtained by the finite correction algorithm already constructed.
-/

noncomputable section
namespace PolycyclicRecognition
open LieModule
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem polynomial_transversal_bijective (A : L ≃ₗ⁅ℝ⁆ L) (P : Module.End ℝ L)
    (hPpres : ∀ k x, x ∈ (lowerCentralSeries ℝ L L k).toSubmodule →
      P x ∈ (lowerCentralSeries ℝ L L k).toSubmodule)
    (e : L ≃ₗ[ℝ] L)
    (he : ∀ z, -(z - P z) + P z + A (z - P z) = e z)
    (hepres : ∀ k x, x ∈ (lowerCentralSeries ℝ L L k).toSubmodule →
      e x ∈ (lowerCentralSeries ℝ L L k).toSubmodule) :
    Function.Bijective (fun x : L => (x - P x)⁻¹ * P x * A (x - P x)) := by
  let Q := (LinearMap.id : Module.End ℝ L) - P
  have hQ (x : L) : Q x = x - P x := rfl
  let U : ℕ → Submodule ℝ L := fun k => (lowerCentralSeries ℝ L L k).toSubmodule
  have hApres (k : ℕ) (x : L) (hx : x ∈ U k) : A x ∈ U k :=
    LieIdeal.map_lowerCentralSeries_le k (LieIdeal.mem_map hx)
  have hQpres (k : ℕ) (x : L) (hx : x ∈ U k) : Q x ∈ U k :=
    (U k).sub_mem hx (hPpres k x hx)
  have hinv (k : ℕ) (x : L) (hx : x ∈ U k) : e.symm x ∈ U k :=
    inverse_mem_of_preserves_submodule e (U k)
      (hepres k) hx
  let g : L → L := fun x => (Q x)⁻¹ * P x
  let f : L → L := fun x => g x * A (Q x)
  have hraise (k : ℕ) (x y : L) (hxy : x - y ∈ U k) :
      (f x - f y) - e (x - y) ∈ U (k + 1) := by
    have hQd : Q x - Q y ∈ U k := by rw [← map_sub]; exact hQpres k _ hxy
    have hPd : P x - P y ∈ U k := by rw [← map_sub]; exact hPpres k _ hxy
    have hQn : -Q x - -Q y ∈ U k := by
      simpa only [neg_sub_neg, neg_sub] using (U k).neg_mem hQd
    have h1 : (g x - g y) - ((-Q x - -Q y) + (P x - P y)) ∈ U (k + 1) := by
      simpa only [g, C.inv_eq_neg] using
        polynomial_mul_difference k (-Q x) (P x) (-Q y) (P y) hQn hPd
    have hgm : g x - g y ∈ U k := by
      have herr : (g x - g y) - ((-Q x - -Q y) + (P x - P y)) ∈ U k :=
        (antitone_lowerCentralSeries ℝ L L (Nat.le_succ k)) h1
      have hlin := (U k).add_mem hQn hPd
      have hh := (U k).add_mem herr hlin
      convert hh using 1; abel
    have hAd : A (Q x) - A (Q y) ∈ U k := by
      rw [← map_sub]
      exact hApres k _ hQd
    have h2 := polynomial_mul_difference k (g x) (A (Q x)) (g y) (A (Q y)) hgm hAd
    have hlead : (-Q x - -Q y) + (P x - P y) + (A (Q x) - A (Q y)) = e (x - y) := by
      rw [← map_sub P, ← map_sub A, ← map_sub Q]
      have hn : -Q x - -Q y = -Q (x - y) := by rw [map_sub]; abel
      rw [hn]
      simpa only [hQ] using he (x - y)
    rw [← hlead]
    change ((g x * A (Q x)) - (g y * A (Q y))) - _ ∈ U (k + 1)
    have hh := (U (k + 1)).add_mem h2 h1
    convert hh using 1; abel
  obtain ⟨c, hc⟩ := (LieModule.isNilpotent_iff ℝ L L).mp (inferInstance : LieModule.IsNilpotent L L)
  have hbij : Function.Bijective (fun x => e.symm (f x)) := by
    apply bijective_of_raises_difference_filtration U (by simp [U])
      (congrArg LieSubmodule.toSubmodule hc)
    intro k x y hxy
    have hh := hinv (k + 1) ((f x - f y) - e (x - y)) (hraise k x y hxy)
    simpa only [map_sub, e.symm_apply_apply] using hh
  have hf := e.bijective.comp hbij
  simpa only [Function.comp_def, e.apply_symm_apply, f, g, hQ] using hf

end PolycyclicRecognition

end

end OAI
