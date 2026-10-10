import Mathlib
import OAI.Analysis.SymmetricDomains.PositivePureDimension

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
open Set Filter
open scoped Topology

theorem Biholomorph.chart_dimension_le {N d : ℕ} {W : Set (Affine N)}
    {D : Set (Affine d)} (e : Biholomorph W D) (hD : IsOpen D) (hWn : W.Nonempty) : d ≤ N := by
  obtain ⟨p,hp⟩ := hWn
  let a : D := e.toHomeomorph ⟨p,hp⟩
  let G := ambientExtend (fun x => (e.toHomeomorph.symm x).val)
  have hG : AnalyticOnNhd ℂ G D := e.holomorphic_invFun.analyticOnNhd_extend hD
  have hGa : G a.val = p := by
    rw [show G a.val = (e.toHomeomorph.symm a).val from ambientExtend_apply _ a]
    simp [a]
  obtain ⟨O,hO,hpO,F,hF,he⟩ := e.holomorphic_toFun ⟨p,hp⟩
  have hgo : ∀ᶠ x in 𝓝 a.val, G x ∈ O := by
    exact (hG a.val a.property).continuousAt.preimage_mem_nhds (hGa ▸ hO.mem_nhds hpO)
  have hid : F ∘ G =ᶠ[𝓝 a.val] id := by
    filter_upwards [hD.mem_nhds a.property,hgo] with x hx hxO
    change F (G x) = x
    have hgx : G x = (e.toHomeomorph.symm ⟨x,hx⟩).val := ambientExtend_apply _ ⟨x,hx⟩
    rw [hgx]
    rw [he (e.toHomeomorph.symm ⟨x,hx⟩) (hgx ▸ hxO)]
    simp
  have hFd : HasFDerivAt F (fderiv ℂ F p) (G a.val) := by
    rw [hGa]
    exact (hF p hpO).differentiableAt.hasFDerivAt
  have hd := (hFd.comp a.val
    ((hG a.val a.property).differentiableAt.hasFDerivAt)).unique
      ((hasFDerivAt_id a.val).congr_of_eventuallyEq hid)
  have hi : Function.LeftInverse (fderiv ℂ F p) (fderiv ℂ G a.val) := by
    intro v
    exact congrArg (fun L : Affine d →L[ℂ] Affine d => L v) hd
  have hdim := LinearMap.finrank_le_finrank_of_injective
    (f := (fderiv ℂ G a.val).toLinearMap) hi.injective
  simpa only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul,mul_one] using hdim

end

section
open Set

theorem IsSmooth.positive_bounded_pure_dimension {N : ℕ} {S : Set (Affine N)}
    (hs : IsSmooth S) (hc : IsConnected S) (hn : ¬ S.Subsingleton) :
    ∃ d : ℕ, 0 < d ∧ d ≤ N ∧ ∀ p : S, ∃ W : Set (Affine N), W ⊆ S ∧
      IsOpen ((Subtype.val : S → Affine N) ⁻¹' W) ∧ p.val ∈ W ∧
      ∃ D : Set (Affine d), IsOpen D ∧ Nonempty (Biholomorph W D) := by
  obtain ⟨d,hpos,hd⟩ := hs.positive_pure_dimension hc hn
  obtain ⟨p,hp⟩ := hc.nonempty
  obtain ⟨W,_,_,hpW,D,hDo,⟨e⟩⟩ := hd ⟨p,hp⟩
  exact ⟨d,hpos,e.chart_dimension_le hDo ⟨p,hpW⟩,hd⟩
end

theorem cocompact_bounded_affine_point_or_positive {n : ℕ} (V U : Set (Affine n))
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (hconn : IsConnected U) (hbounded : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [MulAction Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    (∃ (m : ℕ) (D : Set (Affine m)), IsBoundedSymmetricDomain D ∧
      Nonempty (Biholomorph U D)) ∨
    (∃ d : ℕ, 0 < d ∧ d ≤ n ∧ ∀ p : U, ∃ W : Set (Affine n), W ⊆ U ∧
      IsOpen ((Subtype.val : U → Affine n) ⁻¹' W) ∧ p.val ∈ W ∧
      ∃ D : Set (Affine d), IsOpen D ∧ Nonempty (Biholomorph W D)) := by
  by_cases h : U.Subsingleton
  · exact Or.inl (main_point U hconn.nonempty h).2
  · exact Or.inr ((cocompact_bounded_affine_smooth V U hV hUV hU hconn
      hbounded Γ hhol).positive_bounded_pure_dimension hconn h)
end Release061

end

end OAI
