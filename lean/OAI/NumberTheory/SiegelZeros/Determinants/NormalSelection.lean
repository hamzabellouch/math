import Mathlib.Data.Set.Card
import OAI.NumberTheory.SiegelZeros.Differentials.ConormalPairing
import OAI.NumberTheory.SiegelZeros.Differentials.UnconditionalGlobalLogform
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.GenericRegularity

namespace OAI

namespace SiegelZeros

noncomputable section
namespace WeightedTorusJets.ActualNormalSelection
open SiegelZeros.W58 NormalExactness

attribute [local instance] Ideal.Quotient.field
attribute [local instance 2000] Monoid.toMulAction Semiring.toModule

theorem shrink_independent {F Q : Type*} [Field F] [AddCommGroup Q] [Module F Q]
    (v : Fin 3 → Q) (S : Set (Fin 3))
    (hS : LinearIndependent F (fun i : S => v i)) {h : ℕ} (hh : h ≤ Nat.card S) :
    ∃ T : Set (Fin 3), T ⊆ S ∧ Nat.card T = h ∧
      LinearIndependent F (fun i : T => v i) := by
  obtain ⟨T, hTS, hcard⟩ := Set.exists_subset_card_eq
    (show h ≤ S.ncard from hh)
  exact ⟨T, hTS, hcard, (show LinearIndepOn F v S from hS).mono hTS⟩

theorem ideal_derivative_evaluation_surjective {K R A : Type*}
    [CommRing K] [CommRing R] [Algebra K R] (I : Ideal R) [I.IsMaximal]
    [FiniteDimensional (R ⧸ I) I.Cotangent]
    (D : A → Derivation K R (R ⧸ I))
    (hD : LinearIndependent (R ⧸ I) (fun i => residueConormalPairing I (D i))) :
    Function.Surjective (fun x : I => fun i => D i x) := by
  intro a
  obtain ⟨z, hz⟩ := ConormalPairing.independent_forms_evaluation_surjective hD a
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective z
  exact ⟨x, hz⟩

section Generic
variable (K : Type*) [Field K] [PerfectField K]
variable (p : Ideal (TorusRing K)) [p.IsPrime]

@[reducible] local instance genericLocalCommSemiring : CommSemiring (GenericLocalRing K p) :=
  (inferInstance : CommRing (GenericLocalRing K p)).toCommSemiring

abbrev GenericResidue := IsLocalRing.ResidueField (GenericLocalRing K p)
abbrev GenericMaximal := IsLocalRing.maximalIdeal (GenericLocalRing K p)

@[reducible] local instance genericResidueSelfModule :
    Module (GenericResidue K p) (GenericResidue K p) := Semiring.toModule

@[reducible] local instance genericNormalDualModule :
    Module (GenericResidue K p)
      ((GenericMaximal K p).Cotangent →ₗ[GenericResidue K p] GenericResidue K p) :=
  LinearMap.module

@[reducible] local instance genericQuotientNormalDualModule :
    Module (GenericResidue K p)
      ((GenericMaximal K p).Cotangent →ₗ[GenericLocalRing K p ⧸ GenericMaximal K p]
        GenericLocalRing K p ⧸ GenericMaximal K p) :=
  inferInstanceAs (Module (GenericLocalRing K p ⧸ GenericMaximal K p)
    ((GenericMaximal K p).Cotangent →ₗ[GenericLocalRing K p ⧸ GenericMaximal K p]
      GenericLocalRing K p ⧸ GenericMaximal K p))

def genericCoordinates (j : Fin 4) : GenericLocalRing K p :=
  algebraMap (TorusRing K) (GenericLocalRing K p) (coordinate K j)

@[reducible] local instance genericLogKernelModule (c : Fin 4 → GenericResidue K p) :
    Module (GenericResidue K p)
      (logFormOnDerivations (K := K) (GenericMaximal K p) c
        (genericCoordinates K p)).ker :=
  inferInstanceAs (Module (GenericLocalRing K p ⧸ GenericMaximal K p)
    (logFormOnDerivations (K := K) (GenericMaximal K p) c
      (genericCoordinates K p)).ker)

theorem generic_height_selected_normals
    (h : ℕ) (hp : p.height = h)
    (c : Fin 4 → GenericResidue K p)
    (hω : residueLogForm (K := K) (GenericMaximal K p) c
      (genericCoordinates K p) ≠ 0)
    (b : Module.Basis (Fin 3) (GenericResidue K p)
      (logFormOnDerivations (K := K) (GenericMaximal K p) c
        (genericCoordinates K p)).ker) :
    ∃ T : Set (Fin 3), Nat.card T = h ∧
      LinearIndependent (GenericResidue K p)
        (fun i : T => logarithmicNormalMap (K := K) (GenericMaximal K p) c
          (genericCoordinates K p) (b i)) ∧
      Function.Surjective
        (fun x : GenericMaximal K p => fun i : T => (b i).val x) := by
  let : Algebra.FormallySmooth K (GenericLocalRing K p) :=
    generic_local_formallySmooth K p
  let : Algebra.FormallySmooth K (GenericLocalRing K p ⧸ GenericMaximal K p) :=
    generic_residue_formallySmooth K p
  let : FiniteDimensional (GenericLocalRing K p ⧸ GenericMaximal K p)
      (GenericMaximal K p).Cotangent := by
    change FiniteDimensional (IsLocalRing.ResidueField (GenericLocalRing K p))
      (GenericCotangent K p)
    exact generic_cotangent_finite K p
  obtain ⟨S, hS, _, hcard⟩ := select_actual_logarithmic_normals
    (GenericMaximal K p) c (genericCoordinates K p) hω b
  have hdim : h ≤ Module.finrank (GenericLocalRing K p ⧸ GenericMaximal K p)
      ((GenericMaximal K p).Cotangent →ₗ[GenericLocalRing K p ⧸ GenericMaximal K p]
        GenericLocalRing K p ⧸ GenericMaximal K p) := by
    rw [Subspace.dual_finrank_eq]
    have hh := generic_height_le_cotangent_dimension K p
    rw [hp] at hh
    exact_mod_cast hh
  obtain ⟨T, _, hTcard, hT⟩ := shrink_independent
    (fun i => logarithmicNormalMap (K := K) (GenericMaximal K p) c
      (genericCoordinates K p) (b i)) S hS (by simpa only [hcard] using hdim)
  refine ⟨T, hTcard, hT, ?_⟩
  exact ideal_derivative_evaluation_surjective (GenericMaximal K p)
    (fun i : T => (b i).val) hT

theorem generic_original_direction_selection
    (h : ℕ) (hp : p.height = h)
    (c : Fin 4 → GenericResidue K p)
    (hω : residueLogForm (K := K) (GenericMaximal K p) c
      (genericCoordinates K p) ≠ 0)
    (v : Fin 3 → Fin 4 → K)
    (b : Module.Basis (Fin 3) (GenericResidue K p)
      (logFormOnDerivations (K := K) (GenericMaximal K p) c
        (genericCoordinates K p)).ker)
    (hb : ∀ i, (b i).val = reducedDerivation (GenericMaximal K p)
      (W18.localTorusDerivation K p (v i))) :
    ∃ T : Set (Fin 3), Nat.card T = h ∧
      LinearIndependent (GenericResidue K p)
        (fun i : T => derivationNormal (GenericMaximal K p)
          (W18.localTorusDerivation K p (v i))) ∧
      Function.Surjective
        (fun x : GenericMaximal K p => fun i : T =>
          IsLocalRing.residue (GenericLocalRing K p)
            (W18.localTorusDerivation K p (v i) x)) := by
  obtain ⟨T, hcard, hli, hsurj⟩ := generic_height_selected_normals K p h hp c hω b
  refine ⟨T, hcard, ?_, ?_⟩
  · change LinearIndependent (GenericResidue K p)
      (fun i : T => residueConormalPairing (GenericMaximal K p) (b i).val) at hli
    simpa only [hb, derivationNormal] using hli
  · intro a
    obtain ⟨x, hx⟩ := hsurj a
    refine ⟨x, ?_⟩
    funext i
    have hi := congrFun hx i
    have hbi := congrArg
      (fun D : Derivation K (GenericLocalRing K p)
        (GenericLocalRing K p ⧸ GenericMaximal K p) => D (x : GenericLocalRing K p))
      (hb (i : Fin 3))
    exact hbi.symm.trans hi

end Generic

@[reducible] local instance identityResidueSelfModule (K : Type*) [Field K] :
    Module (IdentityCotangentRank.Residue K) (IdentityCotangentRank.Residue K) :=
  Semiring.toModule

@[reducible] local instance identityNormalDualModule (K : Type*) [Field K] :
    Module (IdentityCotangentRank.Residue K)
      (IdentityCotangentRank.Cotangent K →ₗ[IdentityCotangentRank.Residue K]
        IdentityCotangentRank.Residue K) := LinearMap.module

theorem identity_three_selected_normals (K : Type*) [Field K]
    (v : Fin 3 → Fin 4 → K) (hv : LinearIndependent K v) :
    LinearIndependent (IdentityCotangentRank.Residue K)
      (fun i => IdentityCotangentRank.invariantNormal K (v i)) ∧
    Function.Surjective
      (fun x : IdentityCotangentRank.Maximal K => fun i =>
        IsLocalRing.residue (IdentityCotangentRank.LocalRing K)
          (W18.localTorusDerivation K (identityIdeal K) (v i) x)) := by
  let : FiniteDimensional
      (IdentityCotangentRank.LocalRing K ⧸ IdentityCotangentRank.Maximal K)
      (IdentityCotangentRank.Maximal K).Cotangent := by
    change FiniteDimensional (IsLocalRing.ResidueField (GenericLocalRing K (identityIdeal K)))
      (GenericCotangent K (identityIdeal K))
    exact generic_cotangent_finite K (identityIdeal K)
  have hli := IdentityCotangentRank.invariantNormal_linearIndependent K v hv
  refine ⟨hli, ?_⟩
  exact ideal_derivative_evaluation_surjective (IdentityCotangentRank.Maximal K)
    (fun i => reducedDerivation (IdentityCotangentRank.Maximal K)
      (W18.localTorusDerivation K (identityIdeal K) (v i))) hli

end WeightedTorusJets.ActualNormalSelection

end

end SiegelZeros

end OAI
