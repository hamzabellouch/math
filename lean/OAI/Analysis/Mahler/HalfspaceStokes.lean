import OAI.Analysis.Mahler.FormLocalization
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MahlerStokes

def lowerHalfspace {d : ℕ} (k : Fin d) (R : ℝ) : Set (Fin d → ℝ) := {x | x k < R}

lemma measurableSet_lowerHalfspace {d : ℕ} (k : Fin d) (R : ℝ) :
    MeasurableSet (lowerHalfspace k R) :=
  (isOpen_lt (continuous_apply k) continuous_const).measurableSet

lemma slice_eq_update {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ) :
    (fun t : ℝ => (i.insertNth t y : Fin (n+1) → ℝ)) =
      Function.update (i.insertNth (0 : ℝ) y : Fin (n+1) → ℝ) i := by
  funext t
  exact (Fin.update_insertNth (α := fun _ : Fin (n+1) => ℝ) i 0 t y).symm

lemma contDiff_slice {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => (i.insertNth t y : Fin (n+1) → ℝ)) := by
  rw [slice_eq_update]
  exact contDiff_update 1 _ _

lemma hasCompactSupport_slice {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ)
    {f : (Fin (n+1) → ℝ) → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun t => f (i.insertNth t y)) := by
  change HasCompactSupport (f ∘ (fun t => i.insertNth t y))
  rw [slice_eq_update]
  exact hf.comp_isClosedEmbedding (isClosedEmbedding_update _ _)

lemma integral_partial_slice_Iio {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ) (R : ℝ)
    {f : (Fin (n+1) → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (∫ t in Iio R, fderiv ℝ f (i.insertNth t y) (Pi.single i 1)) = f (i.insertNth R y) := by
  have hd (t : ℝ) := ((hf.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_insertNth i y t)).deriv
  have hs := hf.comp (contDiff_slice i y)
  have hsc := hasCompactSupport_slice i y hc
  have h := HasCompactSupport.integral_Iic_deriv_eq hs hsc R
  rw [integral_Iic_eq_integral_Iio] at h
  change ∀ t, deriv (fun s => f (i.insertNth s y)) t = _ at hd
  change (∫ t in Iio R, deriv (fun s => f (i.insertNth s y)) t) = _ at h
  simpa only [hd, Function.comp_def] using h

lemma integral_partial_slice_zero {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ)
    {f : (Fin (n+1) → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (∫ t, fderiv ℝ f (i.insertNth t y) (Pi.single i 1)) = 0 := by
  have hs : ContDiff ℝ 1 (fun t => f (i.insertNth t y)) := hf.comp (contDiff_slice i y)
  have hsc := hasCompactSupport_slice i y hc
  have hd (t : ℝ) := (hf.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_insertNth i y t)
  have he (t : ℝ) := (hd t).deriv
  apply integral_eq_zero_of_hasDerivAt_of_integrable hd
  · have hi : Integrable (deriv (fun t => f (i.insertNth t y))) :=
      hs.continuous_deriv le_rfl |>.integrable_of_hasCompactSupport hsc.deriv
    change ∀ t, deriv (fun s => f (i.insertNth s y)) t = _ at he
    change Integrable (fun t => deriv (fun s => f (i.insertNth s y)) t) at hi
    simpa only [he] using hi
  · exact hs.continuous.integrable_of_hasCompactSupport hsc

/-- Coordinate divergence through a flat boundary. Transverse derivatives
integrate to zero; the k derivative gives the upper face with positive sign. -/
theorem integral_partial_lowerHalfspace {n : ℕ} (i k : Fin (n+1)) (R : ℝ)
    {f : (Fin (n+1) → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (∫ x in lowerHalfspace k R, fderiv ℝ f x (Pi.single i 1)) =
      if i = k then ∫ y : Fin n → ℝ, f (k.insertNth R y) else 0 := by
  have hi : Integrable (fun x => fderiv ℝ f x (Pi.single i 1)) :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ (Pi.single i 1))
  rw [setIntegral_slice i (measurableSet_lowerHalfspace k R) _ hi.integrableOn]
  by_cases hik : i = k
  · subst i
    simp only [↓reduceIte]
    have hslice (y : Fin n → ℝ) :
        {t : ℝ | k.insertNth t y ∈ lowerHalfspace k R} = Iio R := by
      ext t
      simp [lowerHalfspace]
    simp_rw [hslice, integral_partial_slice_Iio k _ R hf hc]
  · rw [ite_eq_right hik]
    apply integral_eq_zero_of_ae
    filter_upwards with y
    have he (t : ℝ) : (i.insertNth t y : Fin (n+1) → ℝ) k = (i.insertNth (0 : ℝ) y : Fin (n+1) → ℝ) k := by
      rw [← Fin.update_insertNth (α := fun _ : Fin (n+1) => ℝ) i 0 t y]
      simp [Ne.symm hik]
    by_cases hy : (i.insertNth (0 : ℝ) y : Fin (n+1) → ℝ) k < R
    · have hslice : {t : ℝ | i.insertNth t y ∈ lowerHalfspace k R} = univ := by
        ext t
        simp [lowerHalfspace, he, hy]
      rw [hslice, setIntegral_univ]
      exact integral_partial_slice_zero i y hf hc
    · have hslice : {t : ℝ | i.insertNth t y ∈ lowerHalfspace k R} = ∅ := by
        ext t
        simp [lowerHalfspace, he, hy]
      simp [hslice]

/-- Stokes on a coordinate half-space for an actual compactly supported C1
form. The boundary uses the outward orientation, including (-1)^k. -/
theorem integral_extDeriv_lowerHalfspace {n : ℕ} (k : Fin (n+1)) (R : ℝ)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ 1 ω) (hc : HasCompactSupport ω) :
    (∫ x in lowerHalfspace k R, extDeriv ω x (coordinateBasis (n+1))) =
      (-1 : ℝ)^k.val * ∫ y : Fin n → ℝ,
        ω (k.insertNth R y) (k.removeNth (coordinateBasis (n+1))) := by
  have hs (i : Fin (n+1)) : HasCompactSupport (orientedCoefficient ω i) :=
    hc.comp_left (g := fun A : (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ =>
      (-1 : ℝ)^i.val * A (i.removeNth (coordinateBasis (n+1)))) (by simp)
  have hi (i : Fin (n+1)) : Integrable
      (fun x => fderiv ℝ (orientedCoefficient ω i) x (Pi.single i 1)) :=
    (((contDiff_orientedCoefficient hω i).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).integrable_of_hasCompactSupport ((hs i).fderiv_apply ℝ (Pi.single i 1))
  simp_rw [extDeriv_eq_divergence (hω.differentiable one_ne_zero _)]
  rw [integral_finsetSum _ (fun i _ => (hi i).integrableOn)]
  simp_rw [integral_partial_lowerHalfspace _ k R (contDiff_orientedCoefficient hω _) (hs _)]
  simp [orientedCoefficient, integral_const_mul]

end MahlerStokes

end

end OAI
