import OAI.NumberTheory.PiExponent.Cohomology.GradedCechExactness
import OAI.NumberTheory.PiExponent.Cohomology.GradedFreeCech

namespace OAI

namespace PiExponent.GradedSerreStep
noncomputable section
open PiExponent.GradedCech PiExponent.GradedPolynomialLaurent
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {J R M σM : Type*} [Fintype J] [DecidableEq J] [CommRing R]
  [IsNoetherianRing R] [AddCommGroup M] [Module (MvPolynomial J R) M]
  [Module.Finite (MvPolynomial J R) M] [SetLike σM M] [AddSubgroupClass σM M]
  (𝓜 : ℤ → σM) [DirectSum.Decomposition 𝓜]
  [SetLike.GradedSMul (grading (J := J) (R := R)) 𝓜]

def HasPrimitive (d : ℤ) (q : ℕ) : Prop :=
  ∀ c : Cochain (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem d (q + 1),
    differential (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem d c = 0 →
    ∃ b : Cochain (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem d q,
      differential (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem d b = c

def HasRecovery (d : ℤ) : Prop :=
  ∀ c : Cochain (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem d 0,
    differential (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem d c = 0 →
    ∃ m : 𝓜 d, augmentation (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem d m = c

omit [IsNoetherianRing R] in
theorem exists_syzygy_eventual_step :
    ∃ (rank : ℕ) (w : Fin rank → ℤ) (g : (Fin rank → MvPolynomial J R) →ₗ[MvPolynomial J R] M),
      ∃ (hg : ∀ d z, g (DirectSum.decompose (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) z d :
          Fin rank → MvPolynomial J R) = (DirectSum.decompose 𝓜 (g z) d : M)),
        Function.Surjective g ∧
        let hK := GradedSerre.kernel_homogeneous (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) 𝓜 g hg
        let 𝓚 := HomogeneousSubmoduleGrading.piece (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) g.ker hK
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          (HasPrimitive (J := J) (R := R) 𝓚 n 0 → HasRecovery (J := J) (R := R) 𝓜 n) ∧
          ∀ q : ℕ, HasPrimitive (J := J) (R := R) 𝓚 n (q + 1) → HasPrimitive (J := J) (R := R) 𝓜 n q := by
  obtain ⟨rank, w, g, hrange, hg⟩ := GradedSerre.exists_graded_free_map
    (grading (J := J) (R := R)) 𝓜 (⊤ : Submodule (MvPolynomial J R) M)
    (fun _ _ _ => trivial) Module.Finite.fg_top
  have hsurj : Function.Surjective g := LinearMap.range_eq_top.mp hrange
  refine ⟨rank, w, g, hg, hsurj, ?_⟩
  let 𝓕 := ShiftedFreeGrading.piece (grading (J := J) (R := R)) w
  let hK := GradedSerre.kernel_homogeneous 𝓕 𝓜 g hg
  let 𝓚 := HomogeneousSubmoduleGrading.piece 𝓕 g.ker hK
  change ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (HasPrimitive (J := J) (R := R) 𝓚 n 0 → HasRecovery (J := J) (R := R) 𝓜 n) ∧
    ∀ q : ℕ, HasPrimitive (J := J) (R := R) 𝓚 n (q + 1) → HasPrimitive (J := J) (R := R) 𝓜 n q
  refine ⟨∑ b, (w b).toNat, ?_⟩
  intro n hn
  have hdeg (b : Fin rank) : 0 ≤ (n : ℤ) - w b := by
    have hb : (w b).toNat ≤ ∑ b, (w b).toNat :=
      Finset.single_le_sum (fun b _ => Nat.zero_le ((w b).toNat)) (Finset.mem_univ b)
    have hb' : ((w b).toNat : ℤ) ≤ (n : ℤ) := by exact_mod_cast hb.trans hn
    omega
  have hf : ∀ d z, g.ker.subtype (DirectSum.decompose 𝓚 z d : g.ker) =
      (DirectSum.decompose 𝓕 (g.ker.subtype z) d : Fin rank → MvPolynomial J R) :=
    HomogeneousSubmoduleGrading.subtype_degree_compatible 𝓕 g.ker hK
  constructor
  · intro hk
    exact GradedCechExactness.augmentation_recovery_of_shortExact
      (grading (J := J) (R := R)) 𝓚 𝓕 𝓜 MvPolynomial.X variable_mem
      g.ker.subtype g hf hg Subtype.val_injective (LinearMap.exact_subtype_ker_map g) hsurj n
      (GradedFreeCech.free_augmentation_recovery w n hdeg) hk
  · intro q hk
    exact GradedCechExactness.primitives_of_shortExact
      (grading (J := J) (R := R)) 𝓚 𝓕 𝓜 MvPolynomial.X variable_mem
      g.ker.subtype g hf hg Subtype.val_injective (LinearMap.exact_subtype_ker_map g) hsurj n q
      (GradedFreeCech.free_cech_exact w n hdeg q) hk

end
end PiExponent.GradedSerreStep

end OAI
