import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Absorption.ConnectedUnitaryLift
import OAI.Analysis.JiangSu.Absorption.TensorHalfFlipControl
import OAI.Analysis.JiangSu.Absorption.OneSidedIntertwiningChain

namespace OAI

noncomputable section


namespace CStarAbsorption
open Pureness NormUltra NormUltra.QuotientAlgebra CStarIntertwining
open scoped CStarAlgebra ENNReal TensorProduct

variable {A D B : Type*} [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra B]
variable (U : Ultrafilter ℕ) (ι : A →⋆ₐ[ℂ] B) (κ : D →⋆ₐ[ℂ] B)
    (hic : ∀ a d,Commute (ι a) (κ d))
    (φ : D →⋆ₐ[ℂ] QuotientAlgebra (fun _ : ℕ => A) U)
    (hφ : ∀ a d,Commute (diagonalHom U a) (φ d))

 def CentralHalfFlipTransfer : Prop :=
   ∀ (F : Finset D) (ε : ℝ),0<ε →
     ∃ u : unitary (QuotientAlgebra (fun _ : ℕ => B) U),
       (∀ a,Commute (u : QuotientAlgebra (fun _ : ℕ => B) U) (diagonalHom U (ι a))) ∧
       ∀ d∈F,‖(u : QuotientAlgebra (fun _ : ℕ => B) U)*QuotientAlgebra.map U ι (φ d)*star (u : QuotientAlgebra (fun _ : ℕ => B) U)-diagonalHom U (κ d)‖≤ε

 include hφ
 theorem quotient_conjugacy_of_transfer
    (hd : DenseRange (commutingStarTensorHom ι κ hic))
    (ht : CentralHalfFlipTransfer U ι κ φ) : QuotientConjugacy U ι := by
  classical
  intro F G ε hε
  have hz (y : G) : ∃ z : A ⊗[ℂ] D,‖commutingStarTensorHom ι κ hic z-(y:B)‖<ε/2 := by
    simpa only [dist_eq_norm,norm_sub_rev] using (Metric.denseRange_iff.mp hd y (ε/2) (by positivity))
  choose z hz using hz
  have hc (y : G) := finite_tensor_control U ι κ hic φ hφ (z y)
  choose E C hC hc using hc
  let K : Finset D := Finset.univ.biUnion E
  let L : ℝ := ∑ y : G,C y
  have hL : 0≤L := Finset.sum_nonneg (fun y _ => hC y)
  let δ : ℝ := ε/(2*(L+1))
  have hδ : 0<δ := div_pos hε (by positivity)
  obtain ⟨u,hu,huf⟩ := ht K δ hδ
  refine ⟨u,?_,?_⟩
  · intro a ha
    have he : (u : QuotientAlgebra (fun _ : ℕ => B) U)*diagonalHom U (ι a)*star (u : QuotientAlgebra (fun _ : ℕ => B) U)=diagonalHom U (ι a) := by
      rw [(hu a).eq,mul_assoc,u.2.2, mul_one]
    change ‖(u : QuotientAlgebra (fun _ : ℕ => B) U)*diagonalHom U (ι a)*star (u : QuotientAlgebra (fun _ : ℕ => B) U)-diagonalHom U (ι a)‖<ε
    rw [he,sub_self,norm_zero]
    exact hε
  · intro b hb
    let y : G := ⟨b,hb⟩
    refine ⟨preimageTensor U φ hφ (z y),?_⟩
    have hy := hc y u hu δ hδ.le (fun d hd => huf d (Finset.mem_biUnion.mpr ⟨y,Finset.mem_univ _,hd⟩))
    have hCy : C y≤L := Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ y)
    have hsmall : C y*δ<ε/2 := by
      have heq : (L+1)*δ=ε/2 := by dsimp [δ]; field_simp
      have hlt : C y<L+1 := lt_of_le_of_lt hCy (lt_add_one L)
      calc C y*δ < (L+1)*δ := mul_lt_mul_of_pos_right hlt hδ
           _ = ε/2 := heq
    have hdiag : ‖diagonalHom U (commutingStarTensorHom ι κ hic (z y))-diagonalHom U b‖<ε/2 := by
      rw [←map_sub]
      exact (NonUnitalStarAlgHom.norm_apply_le (diagonalHom (A := B) U) _).trans_lt (hz y)
    have he := norm_sub_le_norm_sub_add_norm_sub ((u : QuotientAlgebra (fun _ : ℕ => B) U)*QuotientAlgebra.map U ι (preimageTensor U φ hφ (z y))*star (u : QuotientAlgebra (fun _ : ℕ => B) U)) (diagonalHom U (commutingStarTensorHom ι κ hic (z y))) (diagonalHom U b)
    have hf := he.trans_lt (add_lt_add (hy.trans_lt hsmall) hdiag)
    rw [add_halves] at hf
    exact hf

 theorem equiv_of_central_half_flip [PartialOrder B] [StarOrderedRing B]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
    (hi : Isometry ι) (hd : DenseRange (commutingStarTensorHom ι κ hic))
    (ht : CentralHalfFlipTransfer U ι κ φ) : Nonempty (A ≃⋆ₐ[ℂ] B) :=
  equiv_of_quotient_conjugacy U ι hi (quotient_conjugacy_of_transfer U ι κ hic φ hφ hd ht)

end CStarAbsorption


namespace CStarAbsorption
open Pureness NormUltra NormUltra.QuotientAlgebra
open scoped CStarAlgebra ENNReal TensorProduct

universe u v w r
variable {D : Type u} [CStarAlgebra D]
variable {T : Type v} [CStarAlgebra T]

 def ApproximateInnerHalfFlip (f : D ⊗[ℂ] D →⋆ₐ[ℂ] T) : Prop :=
   ∀ (F : Finset D) (ε : ℝ),0<ε → ∃ u : unitary T,
     ∀ d∈F,‖(u:T)*f (d ⊗ₜ[ℂ] 1)*star (u:T)-f (1 ⊗ₜ[ℂ] d)‖<ε

 theorem diagonalHom_norm {E : Type*} [CStarAlgebra E] (U : Ultrafilter ℕ) (e : E) :
     ‖diagonalHom U e‖=‖e‖ := by
   change ‖mk U (DirectComparison.boundedDiagonal e)‖=‖e‖
   rw [norm_mk_eq_limsup]
   change Filter.limsup (fun _ : ℕ => ‖e‖) (U : Filter ℕ)=‖e‖
   exact Filter.limsup_const (f := (U : Filter ℕ)) ‖e‖

 theorem diagonalHom_injective {E : Type*} [CStarAlgebra E] (U : Ultrafilter ℕ) :
     Function.Injective (diagonalHom (A := E) U) :=
   (AddMonoidHomClass.isometry_of_norm (diagonalHom U) (diagonalHom_norm U)).injective

variable [Nontrivial D] (hD : IsNuclear.{u,u} D) (hs : TopologicallySimple D)
variable (f : D ⊗[ℂ] D →⋆ₐ[ℂ] T) (hf : Function.Injective f) (hd : DenseRange f)
variable (hh : ApproximateInnerHalfFlip f)
variable {A : Type w} {B : Type r} [CStarAlgebra A] [CStarAlgebra B]
variable (U : Ultrafilter ℕ) (ι : A →⋆ₐ[ℂ] B) (κ : D →⋆ₐ[ℂ] B)
    (hic : ∀ a d,Commute (ι a) (κ d)) (hk : Function.Injective κ)
    (φ : D →⋆ₐ[ℂ] QuotientAlgebra (fun _ : ℕ => A) U)
    (hφ : ∀ a d,Commute (diagonalHom U a) (φ d))

 include hD hs hf hd hh hic hk hφ
 theorem central_transfer_of_half_flip : CentralHalfFlipTransfer U ι κ φ := by
   classical
   let α := (QuotientAlgebra.map U ι).comp φ
   let β := (diagonalHom U).comp κ
   have hβ : Function.Injective β := (diagonalHom_injective U).comp hk
   have hαβ : ∀ d e,Commute (α d) (β e) := by
     intro d e
     exact map_commute_diagonal U ι (κ e) (fun a => hic a e) (φ d)
   let θ := nuclearCommutingHom hD hs f hf hd α β hβ hαβ
   have hleft (d : D) : θ (f (d ⊗ₜ[ℂ] 1))=α d := by
     rw [nuclearCommutingHom_tensor]
     simp [commutingStarTensorHom_tmul]
   have hright (d : D) : θ (f (1 ⊗ₜ[ℂ] d))=β d := by
     rw [nuclearCommutingHom_tensor]
     simp [commutingStarTensorHom_tmul]
   intro F ε hε
   obtain ⟨v,hv⟩ := hh F ε hε
   let u : unitary (QuotientAlgebra (fun _ : ℕ => B) U) := ⟨θ v,Unitary.map_mem θ v.2⟩
   refine ⟨u,?_,?_⟩
   · intro a
     apply nuclearCommutingHom_commute
     · intro d
       exact map_commute U ι a (φ d) (hφ a d).symm
     · intro d
       exact ((hic a d).symm).map (diagonalHom U)
   · intro d hdF
     have he := NonUnitalStarAlgHom.norm_apply_le θ ((v:T)*f (d ⊗ₜ[ℂ] 1)*star (v:T)-f (1 ⊗ₜ[ℂ] d))
     rw [map_sub,map_mul,map_mul,map_star,hleft,hright] at he
     exact he.trans (hv d hdF).le

 theorem equiv_of_nuclear_half_flip [PartialOrder B] [StarOrderedRing B]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
    (hi : Isometry ι) (hab : DenseRange (commutingStarTensorHom ι κ hic)) :
    Nonempty (A ≃⋆ₐ[ℂ] B) :=
   equiv_of_central_half_flip U ι κ hic φ hφ hi hab
     (central_transfer_of_half_flip hD hs f hf hd hh U ι κ hic hk φ hφ)

end CStarAbsorption


namespace CStarAbsorption
open scoped TensorProduct CStarAlgebra

lemma ConnectedApproximateInnerHalfFlip.toApproximate
    {D T : Type*} [CStarAlgebra D] [CStarAlgebra T]
    {f : D ⊗[ℂ] D →⋆ₐ[ℂ] T} (h : ConnectedApproximateInnerHalfFlip f) :
    ApproximateInnerHalfFlip f := by
  intro F ε hε
  obtain ⟨u,-,hu⟩ := h F ε hε
  exact ⟨u,hu⟩
end CStarAbsorption

end

end OAI
