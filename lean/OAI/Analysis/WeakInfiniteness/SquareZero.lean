import Mathlib
import OAI.Analysis.WeakInfiniteness.FiniteSelection

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def NonzeroOnNormSlice (D : NonUnitalStarSubalgebra ℂ A) (b : A) (α : ℝ) : Prop :=
  ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
    NonUnitalRepresentationIrreducible π → α ≤ ‖π b‖ →
      ∃ h ∈ D,0 ≤ h ∧ π h ≠ 0

lemma exists_core_perturbationData {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hπ : NonUnitalRepresentationIrreducible π)
    {u v : A} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u*v=0) (hun : π u ≠ 0) (hvn : π v ≠ 0) :
    ∃ F : OrthogonalPerturbationData A n,
      F.p ∈ hereditarySubalgebra u hu.isSelfAdjoint ∧
      F.q ∈ hereditarySubalgebra v hv.isSelfAdjoint ∧ π (positiveCut F.α F.c) ≠ 0 := by
  obtain ⟨p,hpD,h,hhD,hp,hpn,hh,hph,hhn⟩ := exists_supported_positive_core π hu hun
  obtain ⟨q,hqD,k,hkD,hq,hqn,hk,hqk,hkn⟩ := exists_supported_positive_core π hv hvn
  obtain ⟨F,hFp,hFq,hFc⟩ := make_local_perturbationData hn hpi hπ p q h k hp hq hpn hqn
    (mul_zero_of_hereditary hu.isSelfAdjoint hv.isSelfAdjoint huv hpD hqD)
    hh hk hph hqk hhn hkn
  exact ⟨F,by rwa [hFp],by rwa [hFq],hFc⟩

omit [PartialOrder A] [StarOrderedRing A] in
lemma image_hereditary_corner_zero (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    {a b p q x : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hp : p ∈ hereditarySubalgebra a ha) (hq : q ∈ hereditarySubalgebra b hb)
    (hz : π (a*x*b)=0) : π (p*x*q)=0 := by
  have hc : IsClosed {p : A | π (p*x*q)=0} := isClosed_eq (by fun_prop) continuous_const
  apply closure_minimal _ hc hp
  rintro _ ⟨c,rfl⟩
  have hc' : IsClosed {q : A | π ((a*c*a)*x*q)=0} := isClosed_eq (by fun_prop) continuous_const
  apply closure_minimal _ hc' hq
  rintro _ ⟨d,rfl⟩
  change π ((a*c*a)*x*(b*d*b))=0
  have he : (a*c*a)*x*(b*d*b)=(a*c)*(a*x*b)*(d*b) := by noncomm_ring
  rw [he,map_mul,map_mul,hz,mul_zero,zero_mul]

end

end WeakPureInfiniteness
end

end OAI
