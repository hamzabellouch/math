import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalizedResolutionSyzygies

namespace OAI

/-! # Identity cocycles in the normalized resolution

The projection onto the n-th syzygy is a cocycle. If its class vanishes in a
positive degree, the next kernel inclusion splits; this gives a projective
syzygy and hence finite integral dimension for the trivial coefficient.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def normalizedIdentityCycle (A : Rep.{0} ℤ G) (n : ℕ) :
    ((normalizedResolutionComplex A).linearYonedaObj ℤ
      ((iteratedNormalizedSyzygy n).obj A)).cycles n := by
  let C := (normalizedResolutionComplex A).linearYonedaObj ℤ
    ((iteratedNormalizedSyzygy n).obj A)
  exact C.cyclesMk (normalizedResolutionProjection A n) (n + 1) (by simp) (by
    change (normalizedResolutionComplex A).d (n + 1) n ≫
      normalizedResolutionProjection A n = 0
    exact normalizedResolution_d_projection A n)

def normalizedIdentityClass (A : Rep.{0} ℤ G) (n : ℕ) :
    ((normalizedResolutionComplex A).linearYonedaObj ℤ
      ((iteratedNormalizedSyzygy n).obj A)).homology n :=
  ((normalizedResolutionComplex A).linearYonedaObj ℤ
    ((iteratedNormalizedSyzygy n).obj A)).homologyπ n (normalizedIdentityCycle A n)

theorem normalizedIdentityCycle_projection (A : Rep.{0} ℤ G) (n : ℕ) :
    ((normalizedResolutionComplex A).linearYonedaObj ℤ
      ((iteratedNormalizedSyzygy n).obj A)).iCycles n (normalizedIdentityCycle A n) =
        normalizedResolutionProjection A n := by
  let C := (normalizedResolutionComplex A).linearYonedaObj ℤ
    ((iteratedNormalizedSyzygy n).obj A)
  exact C.i_cyclesMk (normalizedResolutionProjection A n) (n + 1) (by simp)
    (by exact normalizedResolution_d_projection A n)

theorem cochain_boundary_of_class_zero (C : CochainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (z : C.cycles (n + 1)) (hz : C.homologyπ (n + 1) z = 0) :
    ∃ y : C.X n, C.d n (n + 1) y = C.iCycles (n + 1) z := by
  let S := ShortComplex.mk (C.toCycles n (n + 1)) (C.homologyπ (n + 1))
    (C.toCycles_comp_homologyπ n (n + 1))
  have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel _
    (C.homologyIsCokernel n (n + 1) (by simp))
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff S).mp hS z hz
  refine ⟨y, ?_⟩
  have he := congrArg (fun v => C.iCycles (n + 1) v) hy
  have hc := congrArg (fun v => v.hom y) (C.toCycles_i n (n + 1))
  exact hc.symm.trans he

theorem normalizedIdentityClass_zero_projective_syzygy (A : Rep.{0} ℤ G) (n : ℕ)
    (h : normalizedIdentityClass A (n + 1) = 0) :
    Projective ((iteratedNormalizedSyzygy (n + 1)).obj A) := by
  let C := (normalizedResolutionComplex A).linearYonedaObj ℤ
    ((iteratedNormalizedSyzygy (n + 1)).obj A)
  obtain ⟨r, hr⟩ := cochain_boundary_of_class_zero C n (normalizedIdentityCycle A (n + 1)) h
  rw [normalizedIdentityCycle_projection] at hr
  change (normalizedResolutionComplex A).d (n + 1) n ≫ r =
    normalizedResolutionProjection A (n + 1) at hr
  rw [normalizedResolutionComplex_d] at hr
  change normalizedFreeStep ((iteratedNormalizedSyzygy n).obj A) ≫ r =
    normalizedFreeAugmentation ((iteratedNormalizedSyzygy (n + 1)).obj A) at hr
  let u := kernel.ι (normalizedFreeAugmentation ((iteratedNormalizedSyzygy n).obj A))
  have hur : u ≫ r = 𝟙 _ := by
    apply (cancel_epi (normalizedFreeAugmentation ((iteratedNormalizedSyzygy (n + 1)).obj A))).mp
    change (normalizedFreeStep ((iteratedNormalizedSyzygy n).obj A)) ≫ r =
      normalizedFreeAugmentation ((iteratedNormalizedSyzygy (n + 1)).obj A) ≫ 𝟙 _
    simpa only [Category.comp_id] using hr
  exact (show Retract ((iteratedNormalizedSyzygy (n + 1)).obj A)
    (normalizedFreeRepresentation ((iteratedNormalizedSyzygy n).obj A)) from ⟨u, r, hur⟩).projective

theorem finiteDimension_of_normalizedIdentityClass_zero (n : ℕ)
    (h : normalizedIdentityClass (trivialIntegral G) (n + 1) = 0) :
    HasFiniteIntegralCohomologicalDimension G := by
  let A := trivialIntegral G
  let P := normalizedProjectiveResolution A
  let : Projective ((iteratedNormalizedSyzygy (n + 1)).obj A) :=
    normalizedIdentityClass_zero_projective_syzygy A n h
  let : Projective (P.complex.opcycles (n + 1)) :=
    Projective.of_iso (normalizedResolutionOpcyclesIso A (n + 1)).symm inferInstance
  refine ⟨n + 1, ?_⟩
  simpa only [Nat.add_zero] using resolution_dimension_of_opcycles_dimension P (n + 1) 0 inferInstance

end PolycyclicRecognition

end

end OAI
