import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFixedReferenceTransportFactors
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFixedReferenceTransportInteger

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFixedReferenceTransport
open Construction Construction.CanonicalOccurrenceTransport Conclusion
open HistoryOccurrenceVariables HistoryPairPattern HistorySymbolicEncoding HistoryPairSmoothXi
open HistoryPairBulkTransport HistoryBulkSupportConversePlan HistoryBulkReferenceScalarCoordinates
open HistorySignedXiTransport HistoryGiantReferenceMean HistorySignedSpectatorCRT
open HistoryRepresentativeSourceSeparation

section Pair
variable (sources : SourceFamily) (m k₀ : ℕ) (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ)
  (s t : ℤ) (gp gm : ℕ) (P Q : ℤ)
  (x₀ x : SourceAssignment sources (Template.current (Template.initial m k₀) l))
  (π : Equiv.Perm (Fin (Template.current (Template.initial m k₀) l).length))
  (hπ : ∀i, sources ((Template.current (Template.initial m k₀) l).get (π i)).origin =
    sources ((Template.current (Template.initial m k₀) l).get i).origin)
  (c e : HistoryChoices sources (Template.initial m k₀) V l)
local notation "T" => Template.current (Template.initial m k₀) l
local notation "H₀" => assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c
local notation "K₀" => assignedHistory sources (Template.initial m k₀) V l t gp gm
  (sourceAssignmentPermutation sources T π hπ x₀) e
local notation "H₁" => assignedHistory sources (Template.initial m k₀) V l s P.toNat Q.toNat x c
local notation "K₁" => assignedHistory sources (Template.initial m k₀) V l t P.toNat Q.toNat
  (sourceAssignmentPermutation sources T π hπ x) e

theorem integer_sourceIntegrand_residue_transport (d : Decomposition) (hP : 0≤P) (hQ : 0≤Q)
    (had : PairAdmissible H₀ K₀ outside)
    (hs : (H₀).Supported V outside) (ks : (K₀).Supported V outside)
    (hs' : (H₁).Supported V outside) (ks' : (K₁).Supported V outside)
    (hfixed : ∀i : Fin (T).length, ((T).get i).role≠.bulk → (x i).val=(x₀ i).val)
    (J : ℤ→ℤ→ℂ) (bc sc : ℕ) (X tb td G : ℝ) :
    sourceIntegrand d sources (Template.initial m k₀) V outside l
      (sourceState sources T x s)
      (sourceState sources T (sourceAssignmentPermutation sources T π hπ x) t)
      c e J bc sc X tb td G P Q =
    J P Q * (((H₀).compensationProduct:ℂ)*((K₀).compensationProduct:ℂ))*
      residuePairSpectator (residueTransform d) outside outside.prod H₁ K₁ (P,Q)*
      pairedRealXi bc sc X tb td G H₀ K₀ hs ks
        (insertOrderedGiants m k₀ H₀ K₀ hs
          (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c))
          (orderedSourceValues sources m k₀ l x)
          (fun u => if u then (Q:ℝ) else (P:ℝ))) := by
  rw [integer_sourceIntegrand_transport sources m k₀ V outside l s t gp gm P Q
    x₀ x π hπ c e d hP hQ hs ks hs' ks' hfixed J bc sc X tb td G]
  have hd := assigned_pair_leafProduct_eq_residue_of_reference sources
    (Template.initial m k₀) V outside l s t gp gm P.toNat Q.toNat
    x₀ (sourceAssignmentPermutation sources T π hπ x₀)
    x (sourceAssignmentPermutation sources T π hπ x) c e had hs' ks' (residueTransform d)
  have hPD : (P.toNat:ZMod outside.prod)=(P:ZMod outside.prod) := by
    rw [←Int.cast_natCast,Int.toNat_of_nonneg hP]
  have hQD : (Q.toNat:ZMod outside.prod)=(Q:ZMod outside.prod) := by
    rw [←Int.cast_natCast,Int.toNat_of_nonneg hQ]
  rw [hPD,hQD] at hd
  rw [hd]
  exact mul_right_comm _ _ _

end Pair
end Ostmann.Arithmetic.HistoryBulkFixedReferenceTransport

end

end OAI
