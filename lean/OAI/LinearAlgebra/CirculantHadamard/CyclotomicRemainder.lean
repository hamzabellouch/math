import Mathlib.RingTheory.IsAdjoinRoot

namespace OAI

universe uR uS

/-!
# Scalar divisibility and monic remainders

The canonical remainder map for a monic root extension is linear over the
coefficient ring. Consequently, divisibility by a scalar in the extension is
equivalent to divisibility of every coefficient of the monic remainder.

The actual polynomial quotient `AdjoinRoot f` is such an extension;
no additional representation hypothesis is required.
-/

noncomputable section

namespace CirculantHadamard.CyclotomicRemainder

open Polynomial

variable {R : Type uR} {S : Type uS} [CommRing R] [Ring S] [Algebra R S] {f : R[X]}

/-- Scalar divisibility in a monic root extension gives a constant-polynomial
factor of the canonical remainder. -/
theorem C_dvd_modByMonic_of_dvd_map (h : IsAdjoinRootMonic S f)
    (a : R) (F : R[X]) (hdiv : algebraMap R S a ∣ h.map F) :
    C a ∣ F %ₘ f := by
  obtain ⟨x, hx⟩ := hdiv
  refine ⟨h.modByMonicHom x, ?_⟩
  calc
    F %ₘ f = h.modByMonicHom (h.map F) := (h.modByMonicHom_map F).symm
    _ = h.modByMonicHom (a • x) := by rw [hx, Algebra.smul_def]
    _ = a • h.modByMonicHom x := h.modByMonicHom.map_smul a x
    _ = C a * h.modByMonicHom x := Polynomial.smul_eq_C_mul a

/-- A constant factor of the canonical remainder gives scalar divisibility
after passing to the monic root extension. -/
theorem dvd_map_of_C_dvd_modByMonic (h : IsAdjoinRootMonic S f)
    (a : R) (F : R[X]) (hdiv : C a ∣ F %ₘ f) :
    algebraMap R S a ∣ h.map F := by
  obtain ⟨G, hG⟩ := hdiv
  refine ⟨h.map G, ?_⟩
  calc
    h.map F = h.map (F %ₘ f) := (h.map_modByMonic F).symm
    _ = h.map (C a * G) := congrArg h.map hG
    _ = algebraMap R S a * h.map G := by rw [map_mul, ← h.algebraMap_apply]

/-- Exact divisibility equivalence for a monic root extension. -/
theorem map_dvd_iff_C_dvd_modByMonic (h : IsAdjoinRootMonic S f)
    (a : R) (F : R[X]) :
    algebraMap R S a ∣ h.map F ↔ C a ∣ F %ₘ f :=
  ⟨C_dvd_modByMonic_of_dvd_map h a F, dvd_map_of_C_dvd_modByMonic h a F⟩

/-- Scalar divisibility is equivalent to divisibility of every coefficient
of the canonical remainder. -/
theorem map_dvd_iff_dvd_coeff_modByMonic (h : IsAdjoinRootMonic S f)
    (a : R) (F : R[X]) :
    algebraMap R S a ∣ h.map F ↔ ∀ i, a ∣ (F %ₘ f).coeff i :=
  (map_dvd_iff_C_dvd_modByMonic h a F).trans (C_dvd_iff_dvd_coeff a (F %ₘ f))

/-- Coefficient form of the forward divisibility bridge. -/
theorem dvd_coeff_modByMonic_of_dvd_map (h : IsAdjoinRootMonic S f)
    (a : R) (F : R[X]) (hdiv : algebraMap R S a ∣ h.map F) (i : ℕ) :
    a ∣ (F %ₘ f).coeff i :=
  (map_dvd_iff_dvd_coeff_modByMonic h a F).mp hdiv i

/-- The actual quotient by a monic polynomial satisfies the constant-factor
criterion, using its concrete `IsAdjoinRootMonic` constructor. -/
theorem adjoinRoot_dvd_iff_C_dvd_modByMonic (f : R[X]) (hf : f.Monic)
    (a : R) (F : R[X]) :
    algebraMap R (AdjoinRoot f) a ∣ AdjoinRoot.mk f F ↔ C a ∣ F %ₘ f := by
  simpa only [AdjoinRoot.isAdjoinRootMonic_toAdjoinRoot,
    AdjoinRoot.isAdjoinRoot_map_eq_mkₐ, AdjoinRoot.coe_mkₐ] using
    map_dvd_iff_C_dvd_modByMonic (AdjoinRoot.isAdjoinRootMonic f hf) a F

/-- The concrete monic quotient has scalar divisibility exactly when all
coefficients of the monic remainder have that scalar factor. -/
theorem adjoinRoot_dvd_iff_dvd_coeff_modByMonic (f : R[X]) (hf : f.Monic)
    (a : R) (F : R[X]) :
    algebraMap R (AdjoinRoot f) a ∣ AdjoinRoot.mk f F ↔
      ∀ i, a ∣ (F %ₘ f).coeff i :=
  (adjoinRoot_dvd_iff_C_dvd_modByMonic f hf a F).trans
    (C_dvd_iff_dvd_coeff a (F %ₘ f))

/-- Scalar divisibility in a monic quotient implies coefficientwise
divisibility of the remainder. -/
theorem adjoinRoot_dvd_coeff_modByMonic (f : R[X]) (hf : f.Monic)
    (a : R) (F : R[X])
    (hdiv : algebraMap R (AdjoinRoot f) a ∣ AdjoinRoot.mk f F) (i : ℕ) :
    a ∣ (F %ₘ f).coeff i :=
  (adjoinRoot_dvd_iff_dvd_coeff_modByMonic f hf a F).mp hdiv i

end CirculantHadamard.CyclotomicRemainder

end

end OAI
