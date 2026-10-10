import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteRepresentationQuotients

namespace OAI

/-! # Projectivity of the top syzygy

Successive quotient terms of a projective resolution fit into short exact
sequences. Finite projective dimension therefore makes the corresponding
top quotient projective; it remains finitely generated when the old term is.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
variable {G : Type} [Group G] (P : ProjectiveResolution (trivialIntegral G))

def resolutionOpcyclesSequence (n : ℕ) : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (P.complex.fromOpcycles (n + 1) n) (P.complex.pOpcycles n) (by
    rw [← cancel_epi (P.complex.pOpcycles (n + 1)),
      P.complex.p_fromOpcycles_assoc, P.complex.d_pOpcycles, comp_zero])

theorem resolutionOpcyclesSequence_shortExact (n : ℕ) :
    (resolutionOpcyclesSequence P n).ShortExact := by
  have hsc : (P.complex.sc' (n + 2) (n + 1) n).Exact := P.exact_succ n
  let e := P.complex.opcyclesIsoSc' (n + 2) (n + 1) n (by simp) (by simp)
  have : Mono (P.complex.sc' (n + 2) (n + 1) n).fromOpcycles := hsc.mono_fromOpcycles
  have he : P.complex.fromOpcycles (n + 1) n =
      e.hom ≫ (P.complex.sc' (n + 2) (n + 1) n).fromOpcycles := by
    exact (e.inv_comp_eq).mp
      (P.complex.opcyclesIsoSc'_inv_fromOpcycles (n + 2) (n + 1) n (by simp) (by simp))
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · let S := ShortComplex.mk (P.complex.d (n + 1) n) (P.complex.pOpcycles n)
      (P.complex.d_pOpcycles (n + 1) n)
    have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel _
      (P.complex.opcyclesIsCokernel (n + 1) n (by simp))
    let φ : S ⟶ resolutionOpcyclesSequence P n :=
      { τ₁ := P.complex.pOpcycles (n + 1)
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by simp [S, resolutionOpcyclesSequence]
        comm₂₃ := by simp [S, resolutionOpcyclesSequence] }
    have : Epi φ.τ₁ := by
      change Epi (P.complex.pOpcycles (n + 1))
      infer_instance
    have : IsIso φ.τ₂ := by
      change IsIso (𝟙 _)
      infer_instance
    have : Mono φ.τ₃ := by
      change Mono (𝟙 _)
      infer_instance
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp hS
  · change Mono (P.complex.fromOpcycles (n + 1) n)
    have hmono : Mono (e.hom ≫ (P.complex.sc' (n + 2) (n + 1) n).fromOpcycles) :=
      inferInstance
    exact he.symm ▸ hmono
  · change Epi (P.complex.pOpcycles n)
    infer_instance

def resolutionOpcyclesZeroIso : P.complex.opcycles 0 ≅ trivialIntegral G :=
  (P.complex.opcyclesIsCokernel 1 0 (by simp)).coconePointUniqueUpToIso
    P.isColimitCokernelCofork

theorem resolutionOpcycles_projectiveDimension (n d : ℕ)
    [hdim : HasProjectiveDimensionLE (trivialIntegral G) (n + d)] :
    HasProjectiveDimensionLE (P.complex.opcycles n) d := by
  induction n generalizing d with
  | zero =>
    have : HasProjectiveDimensionLT (trivialIntegral G) (d + 1) := by
      simpa only [Nat.zero_add] using hdim
    exact hasProjectiveDimensionLT_of_iso (resolutionOpcyclesZeroIso P).symm (d + 1)
  | succ n ih =>
    have : HasProjectiveDimensionLE (trivialIntegral G) (n + (d + 1)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hdim
    have hq := ih (d + 1)
    exact (resolutionOpcyclesSequence_shortExact P n).hasProjectiveDimensionLT_X₁ (d + 1)
      (hasProjectiveDimensionLT_of_ge (P.complex.X n) 1 (d + 1) (by omega)) hq

theorem resolutionOpcycles_projective (d : ℕ)
    [hdim : HasProjectiveDimensionLE (trivialIntegral G) d] : Projective (P.complex.opcycles d) := by
  have : HasProjectiveDimensionLE (trivialIntegral G) (d + 0) := by simpa using hdim
  exact (projective_iff_hasProjectiveDimensionLE_zero _).mpr
    (resolutionOpcycles_projectiveDimension P d 0)

theorem resolutionOpcycles_finite (d : ℕ)
    (h : IntegralRepresentationFinite G (P.complex.X d)) :
    IntegralRepresentationFinite G (P.complex.opcycles d) :=
  h.of_epi (P.complex.pOpcycles d)

end PolycyclicRecognition

end

end OAI
