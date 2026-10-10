import Mathlib
import OAI.Analysis.WeakInfiniteness.CoreSelection
import OAI.Analysis.WeakInfiniteness.FiniteCoupling
import OAI.Analysis.WeakInfiniteness.LocalCommon
import OAI.Analysis.WeakInfiniteness.PrimitiveCompactness

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

universe u v w

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma finite_norm_support_cover_nonunital {ι : Type w} (x : ι → A) (b : A) (hb : 0 ≤ b)
    (α : ℝ) (hα : 0 < α)
    (hcover : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),NonUnitalRepresentationIrreducible π →
        α ≤ ‖π b‖ → ∃ i,π (x i) ≠ 0) :
    ∃ F : Finset ι,∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),α ≤ ‖π b‖ → ∃ i ∈ F,π (x i) ≠ 0 := by
  let ιA := Unitization.inrNonUnitalStarAlgHom ℂ A
  obtain ⟨F,hF⟩ := finite_norm_support_cover (fun i => ιA (x i)) (ιA b) (map_nonneg ιA hb) α hα (by
    intro f hf hfb
    let Φ := realStateComplexification f hf.1
    let π := Φ.gnsStarAlgHom.toNonUnitalStarAlgHom.comp ιA
    exact hcover Φ.GNS π
      (irreducible_restrict_unitization Φ.gnsStarAlgHom (extreme_real_state_gns_irreducible f hf)) hfb)
  refine ⟨F,?_⟩
  intro H _ _ _ π hπ
  have hb' : α ≤ ‖(Unitization.starLift π) (ιA b)‖ := by
    change α ≤ ‖(Unitization.starLift π) (b : Unitization ℂ A)‖
    rwa [starLift_inr_apply]
  obtain ⟨i,hi,hin⟩ := hF H (Unitization.starLift π) hb'
  refine ⟨i,hi,?_⟩
  change (Unitization.starLift π) (x i : Unitization ℂ A) ≠ 0 at hin
  rwa [starLift_inr_apply] at hin

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma make_local_perturbationData {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hπ : NonUnitalRepresentationIrreducible π)
    (p q h k : A) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpn : ‖p‖ ≤ 1) (hqn : ‖q‖ ≤ 1)
    (hpq : p*q=0) (hh : 0 ≤ h) (hk : 0 ≤ k) (hph : p*h=h) (hqk : q*k=k)
    (hhn : π h ≠ 0) (hkn : π k ≠ 0) :
    ∃ F : OrthogonalPerturbationData A n,F.p=p ∧ F.q=q ∧ π (positiveCut F.α F.c) ≠ 0 := by
  obtain ⟨c,hc,-,hcn,hch,hck⟩ := exists_local_common_element hn hpi hπ hh hk hhn hkn
  let α := ‖π c‖/2
  have hα : 0 < α := by dsimp [α]; exact half_pos (norm_pos_iff.mpr hcn)
  let F : OrthogonalPerturbationData A n :=
    ⟨p,q,h,k,c,hpn,hqn,hp,hq,hpq,hh,hk,hc,hph,hqk,hch,hck,α,hα⟩
  refine ⟨F,rfl,rfl,?_⟩
  change π (positiveCut α c) ≠ 0
  rw [show π (positiveCut α c)=positiveCut α (π c) from
    π.map_cfcₙ (fun s : ℝ => max (s-α) 0) c (by fun_prop)
      (max_eq_right (by linarith)) (by fun_prop) hc.isSelfAdjoint (map_nonneg π hc).isSelfAdjoint]
  exact positiveCut_ne_zero_of_lt_norm (map_nonneg π hc) hα.le (by dsimp [α]; linarith [norm_pos_iff.mpr hcn])

variable {A : Type 1} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_selected_finite_coupling_of_gap_one
    {γ σ : ℝ} (hσ : 0 < σ) (hσγ : 2*σ ≤ γ)
    (hgap : ∀ (B : Type 1) [CStarAlgebra B] (v : B), ‖v‖ ≤ 1 → Exact B →
      ¬ FiniteContractionModels B v γ)
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosedInner D)
    (b : A) (hb : 0 ≤ b) {α : ℝ} (hα : 0 < α) (Q : A → A → Prop)
    (hloc : ∀ (H : ComplexHilbert.{1}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
      NonUnitalRepresentationIrreducible π → α ≤ ‖π b‖ →
      ∃ F : OrthogonalPerturbationData A n,F.p ∈ D ∧ F.q ∈ D ∧ Q F.p F.q ∧
        π (positiveCut F.α F.c) ≠ 0) :
    ∃ (F : Finset {F : OrthogonalPerturbationData A n // F.p ∈ D ∧ F.q ∈ D ∧ Q F.p F.q})
      (U : A),U ∈ D ∧ IsSelfAdjoint U ∧
      ∀ (H : ComplexHilbert.{1}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        α ≤ ‖π b‖ → ∃ i ∈ F,π (i.val.p*U*i.val.q) ≠ 0 := by
  let I := {F : OrthogonalPerturbationData A n // F.p ∈ D ∧ F.q ∈ D ∧ Q F.p F.q}
  obtain ⟨F,hF⟩ := finite_norm_support_cover_nonunital
    (fun i : I => positiveCut i.val.α i.val.c) b hb α hα (by
      intro H _ _ _ π hπ hπb
      let H' : ComplexHilbert.{1} := ⟨H⟩
      obtain ⟨i,hiD,hjD,hQ,hin⟩ := hloc H' π hπ hπb
      exact ⟨⟨i,hiD,hjD,hQ⟩,hin⟩)
  obtain ⟨U,hUD,hUsa,ε,hε,hU⟩ := exists_finite_coupling_of_gap_one hσ hσγ hgap hA hn hpi
    D hD (fun i : I => i.val) F (fun i _ => ⟨i.property.1,i.property.2.1⟩)
  refine ⟨F,U,hUD,hUsa,?_⟩
  intro H π hπb
  obtain ⟨i,hi,hin⟩ := hF H π hπb
  have hci := norm_lt_of_positiveCut_image_ne_zero π i.val.nonneg_c i.val.pos_α.le hin
  refine ⟨i,hi,?_⟩
  intro hz
  have he := hU i hi H π hci.le
  rw [hz,norm_zero] at he
  exact (not_le_of_gt hε) he

end

end WeakPureInfiniteness
end

end OAI
