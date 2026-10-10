import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Prod

namespace OAI

/-! # Product Haar measure in increment and endpoint coordinates

The change `(u₁, …, uₕ) ↦ (u₁, u₁u₂, …, u₁⋯uₕ)` preserves product
Haar measure. Its inverse is the successive-difference map used in the
endpoint-tuple volume argument.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

private def prefixShear (n : ℕ) : (G × (Fin n → G)) ≃ᵐ (G × (Fin n → G)) where
  toFun p := (p.1, fun i => p.1 * p.2 i)
  invFun p := (p.1, fun i => p.1⁻¹ * p.2 i)
  left_inv p := by ext i <;> simp
  right_inv p := by ext i <;> simp
  measurable_toFun := measurable_fst.prodMk (measurable_pi_iff.mpr
    (fun i => measurable_fst.mul ((measurable_pi_apply i).comp measurable_snd)))
  measurable_invFun := measurable_fst.prodMk (measurable_pi_iff.mpr
    (fun i => measurable_fst.inv.mul ((measurable_pi_apply i).comp measurable_snd)))

/-- Finite multiplication in successive endpoint coordinates, retaining
the first coordinate as the first increment. -/
def prefixCoordinateEquiv : (n : ℕ) → (Fin n → G) ≃ᵐ (Fin n → G)
  | 0 => MeasurableEquiv.refl _
  | n + 1 =>
    let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) 0
    split.trans (((MeasurableEquiv.refl G).prodCongr (prefixCoordinateEquiv n)).trans
      ((prefixShear n).trans split.symm))

theorem prefixCoordinateEquiv_zero (n : ℕ) (u : Fin (n + 1) → G) :
    prefixCoordinateEquiv (n + 1) u 0 = u 0 := by
  simp [prefixCoordinateEquiv, prefixShear]
  rfl

theorem prefixCoordinateEquiv_succ (n : ℕ) (u : Fin (n + 1) → G) (i : Fin n) :
    prefixCoordinateEquiv (n + 1) u i.succ =
      u 0 * prefixCoordinateEquiv n (fun j => u j.succ) i := by
  simp [prefixCoordinateEquiv, prefixShear]
  rfl

theorem prefixCoordinateEquiv_increment (n : ℕ) (u : Fin (n + 1) → G) (i : Fin n) :
    prefixCoordinateEquiv (n + 1) u i.castSucc * u i.succ =
      prefixCoordinateEquiv (n + 1) u i.succ := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.castSucc_zero, prefixCoordinateEquiv_zero, prefixCoordinateEquiv_succ]
    · simp only [Fin.castSucc_succ, prefixCoordinateEquiv_succ, mul_assoc]
      rw [ih]
      rw [prefixCoordinateEquiv_succ]

/-- The inverse records the first point and the consecutive differences. -/
theorem prefixCoordinateEquiv_symm_increment (n : ℕ) (y : Fin (n + 1) → G) (i : Fin n) :
    (prefixCoordinateEquiv (n + 1)).symm y i.succ = (y i.castSucc)⁻¹ * y i.succ := by
  have h := prefixCoordinateEquiv_increment n ((prefixCoordinateEquiv (n + 1)).symm y) i
  simp only [MeasurableEquiv.apply_symm_apply] at h
  exact (eq_inv_mul_iff_mul_eq).mpr h

theorem prefixCoordinateEquiv_symm_zero (n : ℕ) (y : Fin (n + 1) → G) :
    (prefixCoordinateEquiv (n + 1)).symm y 0 = y 0 := by
  have hh := prefixCoordinateEquiv_zero n ((prefixCoordinateEquiv (n + 1)).symm y)
  simpa only [MeasurableEquiv.apply_symm_apply] using hh.symm

/-- Thickening the total lifts on the right changes an increment only by
the correction on its left and the correction on its right. -/
theorem prefixCoordinateEquiv_symm_mul_increment (n : ℕ)
    (y η : Fin (n + 1) → G) (i : Fin n) :
    (prefixCoordinateEquiv (n + 1)).symm (fun j => y j * η j) i.succ =
      (η i.castSucc)⁻¹ * (prefixCoordinateEquiv (n + 1)).symm y i.succ * η i.succ := by
  rw [prefixCoordinateEquiv_symm_increment, prefixCoordinateEquiv_symm_increment]
  group

theorem continuous_prefixCoordinateEquiv_symm [TopologicalSpace G] [IsTopologicalGroup G]
    (n : ℕ) : Continuous ((prefixCoordinateEquiv (G := G) n).symm) := by
  cases n with
  | zero => exact continuous_id
  | succ n =>
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [prefixCoordinateEquiv_symm_zero] using
        (continuous_apply (0 : Fin (n + 1)))
    · have he : (fun y : Fin (n + 1) → G => (prefixCoordinateEquiv (n + 1)).symm y j.succ) =
          (fun y => (y j.castSucc)⁻¹ * y j.succ) := by
        funext y
        exact prefixCoordinateEquiv_symm_increment n y j
      rw [he]
      exact continuous_mul.comp
        ((continuous_inv.comp (continuous_apply j.castSucc)).prodMk (continuous_apply j.succ))

theorem measurePreserving_prefixCoordinateEquiv (μ : Measure G)
    [SigmaFinite μ] [μ.IsMulLeftInvariant] (n : ℕ) :
    MeasurePreserving (prefixCoordinateEquiv n) (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) := by
  induction n with
  | zero => exact MeasurePreserving.id _
  | succ n ih =>
    let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) 0
    have hs : MeasurePreserving split (Measure.pi fun _ => μ)
        (μ.prod (Measure.pi fun _ : Fin n => μ)) := measurePreserving_piFinSuccAbove _ 0
    have ht := (MeasurePreserving.id μ).prod ih
    have hu : MeasurePreserving (prefixShear n)
        (μ.prod (Measure.pi fun _ : Fin n => μ))
        (μ.prod (Measure.pi fun _ : Fin n => μ)) := by
      change MeasurePreserving (fun p : G × (Fin n → G) => (p.1, fun i => p.1 * p.2 i))
        (μ.prod (Measure.pi fun _ : Fin n => μ)) (μ.prod (Measure.pi fun _ : Fin n => μ))
      apply MeasurePreserving.skew_product (g := fun (g : G) (p : Fin n → G) => fun i => g * p i)
        (MeasurePreserving.id μ)
      · exact measurable_pi_iff.mpr (fun i =>
          measurable_fst.mul ((measurable_pi_apply i).comp measurable_snd))
      · exact Filter.Eventually.of_forall (fun g =>
          map_mul_left_eq_self (Measure.pi fun _ : Fin n => μ) (fun _ => g))
    exact hs.symm.comp (hu.comp (ht.comp hs))

theorem measurePreserving_prefixCoordinateEquiv_symm (μ : Measure G)
    [SigmaFinite μ] [μ.IsMulLeftInvariant] (n : ℕ) :
    MeasurePreserving (prefixCoordinateEquiv n).symm
      (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) :=
  (measurePreserving_prefixCoordinateEquiv μ n).symm

theorem prefixCoordinateEquiv_symm_image_measure (μ : Measure G)
    [SigmaFinite μ] [μ.IsMulLeftInvariant] (n : ℕ)
    {E : Set (Fin n → G)} (hE : MeasurableSet E) :
    (Measure.pi fun _ => μ) ((prefixCoordinateEquiv n).symm '' E) =
      (Measure.pi fun _ => μ) E := by
  let e := prefixCoordinateEquiv (G := G) n
  have hset : e ⁻¹' E = e.symm '' E := by
    ext u
    constructor
    · intro hu
      exact ⟨e u, hu, e.symm_apply_apply u⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  have hm := (measurePreserving_prefixCoordinateEquiv μ n).map_eq
  have hh := Measure.map_apply (μ := Measure.pi fun _ : Fin n => μ) e.measurable hE
  rw [hm, hset] at hh
  exact hh.symm

end PolycyclicRecognition

end

end OAI
