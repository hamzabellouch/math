import Mathlib
import OAI.Analysis.SymmetricDomains.VanishingIdealPrime

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set

theorem IsSmooth.canonical_prime_ambient {n : ℕ} {V U : Set (Affine n)}
    (hs : IsSmooth U) (hc : IsConnected U)
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U)) :
    ∃ I : Ideal (MvPolynomial (Fin n) ℂ), I.IsPrime ∧
      U ⊆ MvPolynomial.zeroLocus ℂ I ∧ MvPolynomial.zeroLocus ℂ I ⊆ V ∧
      IsAffineAlgebraic (MvPolynomial.zeroLocus ℂ I) ∧
      IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ I → Affine n) ⁻¹' U) := by
  let I := MvPolynomial.vanishingIdeal ℂ U
  have hIV : MvPolynomial.zeroLocus ℂ I ⊆ V := by
    obtain ⟨P,hP⟩ := hV
    intro x hx
    rw [hP]
    intro p hp
    apply hx p
    intro y hy
    exact (hP ▸ hUV hy) p hp
  refine ⟨I,hs.vanishingIdeal_isPrime hc,MvPolynomial.zeroLocus_vanishingIdeal_le U,
    hIV,?_,?_⟩
  · exact ⟨(I : Set (MvPolynomial (Fin n) ℂ)),rfl⟩
  · exact hU.preimage (continuous_inclusion hIV)

end

theorem cocompact_prime_affine_ambient {n : ℕ} (V U : Set (Affine n))
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (hconn : IsConnected U) (hbounded : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [MulAction Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    ∃ I : Ideal (MvPolynomial (Fin n) ℂ), I.IsPrime ∧
      U ⊆ MvPolynomial.zeroLocus ℂ I ∧ MvPolynomial.zeroLocus ℂ I ⊆ V ∧
      IsAffineAlgebraic (MvPolynomial.zeroLocus ℂ I) ∧
      IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ I → Affine n) ⁻¹' U) :=
  (cocompact_bounded_affine_smooth V U hV hUV hU hconn hbounded Γ hhol).canonical_prime_ambient
    hconn hV hUV hU

open Set Filter
open scoped Topology

lemma Biholomorph.open_dimension_le {n m : ℕ} {S : Set (Affine n)} {T : Set (Affine m)}
    (e : Biholomorph S T) (hS : IsOpen S) (hT : IsOpen T) (hSn : S.Nonempty) : n ≤ m := by
  obtain ⟨p,hp⟩ := hSn
  let F := ambientExtend (fun x => (e.toHomeomorph x).val)
  let G := ambientExtend (fun x => (e.toHomeomorph.symm x).val)
  have hF : AnalyticOnNhd ℂ F S := e.holomorphic_toFun.analyticOnNhd_extend hS
  have hG : AnalyticOnNhd ℂ G T := e.holomorphic_invFun.analyticOnNhd_extend hT
  have hFp : F p ∈ T := by
    rw [show F p = (e.toHomeomorph ⟨p,hp⟩).val from ambientExtend_apply _ ⟨p,hp⟩]
    exact (e.toHomeomorph ⟨p,hp⟩).property
  have hid : G ∘ F =ᶠ[𝓝 p] id := by
    filter_upwards [hS.mem_nhds hp] with q hq
    change G (F q) = q
    rw [show F q = (e.toHomeomorph ⟨q,hq⟩).val from ambientExtend_apply _ ⟨q,hq⟩]
    rw [show G (e.toHomeomorph ⟨q,hq⟩).val =
      (e.toHomeomorph.symm (e.toHomeomorph ⟨q,hq⟩)).val from ambientExtend_apply _ _]
    simp
  have hd := ((hG (F p) hFp).differentiableAt.hasFDerivAt.comp p
    (hF p hp).differentiableAt.hasFDerivAt).unique
      ((hasFDerivAt_id p).congr_of_eventuallyEq hid)
  have hi : Function.LeftInverse (fderiv ℂ G (F p)) (fderiv ℂ F p) := by
    intro v
    exact congrArg (fun L : Affine n →L[ℂ] Affine n => L v) hd
  have hdim := LinearMap.finrank_le_finrank_of_injective
    (f := (fderiv ℂ F p).toLinearMap) hi.injective
  simpa only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul,mul_one] using hdim

theorem Biholomorph.open_dimension_eq {n m : ℕ} {S : Set (Affine n)} {T : Set (Affine m)}
    (e : Biholomorph S T) (hS : IsOpen S) (hT : IsOpen T) (hSn : S.Nonempty) : n = m := by
  apply Nat.le_antisymm (e.open_dimension_le hS hT hSn)
  apply e.symm.open_dimension_le hT hS
  obtain ⟨p,hp⟩ := hSn
  exact ⟨(e.toHomeomorph ⟨p,hp⟩).val,(e.toHomeomorph ⟨p,hp⟩).property⟩

end Release061

end

end OAI
