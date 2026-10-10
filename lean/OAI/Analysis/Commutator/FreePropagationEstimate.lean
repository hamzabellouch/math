import Mathlib
import OAI.Analysis.Commutator.FreePropagation
import OAI.Analysis.Commutator.FreeRepeatedWords

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

open Filter _root_.Topology ContinuousLinearMap

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {i j : ι} (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap) (hij : i≠j)

lemma norm_factorVector (d : D) :
    ‖TracialGNS.algebraVector (factorTrace t f hf) d‖=
      ‖(t.functional.toPreGNS (f d) : t.functional.GNS)‖ := by
  simp only [TracialGNS.algebraVector_apply,UniformSpace.Completion.norm_coe,
    PositiveLinearMap.preGNS_norm_def,PositiveLinearMap.ofPreGNS_toPreGNS,
    pullbackState_apply,map_mul,map_star]

lemma scale_normalization (q : D) (hq : IsStarProjection q) (x : A)
    (hx : ‖t.functional.toPreGNS x‖=1) (hxq : x*f q=x) (c : ℝ) (hc : 0≤c)
    (hxx : star x*x=(c:ℂ) • f q) :
    Real.sqrt c*‖TracialGNS.algebraVector (factorTrace t f hf) q‖=1 := by
  let y : t.functional.GNS := t.functional.toPreGNS (f q)
  have hy : t.functional.gnsStarAlgHom (f q) y=y := by
    change t.functional.gnsStarAlgHom (f q) (t.functional.toPreGNS (f q) : t.functional.GNS)=_
    rw [TracialGNS.left_coe,←map_mul,hq.isIdempotentElem.eq]
  have hn := FreeCreation.norm_mul_supported t x (f q) c hc hxx y hy
  have hn' : ‖t.functional.gnsStarAlgHom x y‖=1 := by
    change ‖t.functional.gnsStarAlgHom x (t.functional.toPreGNS (f q) : t.functional.GNS)‖=1
    rw [TracialGNS.left_coe,hxq,UniformSpace.Completion.norm_coe,hx]
  rw [hn'] at hn
  rw [norm_factorVector]
  exact hn.symm

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)

variable (B : ∀ n, multiplicityLevel t S j n →L[ℂ] multiplicityLevel t S j n)

variable (hB : ∀ n d (x : letterSpace t S i) v,
  G (repeatedOutput t S f hf hS hfree hij d x n v)=
    repeatedOutput t S f hf hS hfree hij d x n (B n v))

include hB in
theorem propagation_of_local_module
    (s : letterSpace t S j) (hs : ‖s‖=1)
    (q : D) (hq : IsStarProjection q) (c : ℝ) (hc : 0≤c)
    (x : ℕ → letterSpace t S i) (hx : ∀ n, ‖x n‖=1)
    (hxq : ∀ n, letterValue t S i (x n)*f q=letterValue t S i (x n))
    (hxx : ∀ n, star (letterValue t S i (x n))*letterValue t S i (x n)=(c:ℂ) • f q)
    (hxs : ∀ n, ‖t.functional.toPreGNS (star (letterValue t S i (x n)))‖≤1)
    (hmoment : ∀ a ∈ S i, Tendsto (fun n => t.functional (letterValue t S i (x n)*a)) atTop (𝓝 0))
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))
    (k : ℕ) (M : ℝ) (hM : ∀ n, ‖(letterValue t S j s*letterValue t S i (x n))^k*letterValue t S j s‖≤M)
    (δ : ℝ) (hδ : 0≤δ) (v : multiplicityLevel t S j 0)
    (T : t.functional.GNS →L[ℂ] t.functional.GNS)
    (hT : ∀ a : A, T.comp (t.functional.gnsStarAlgHom a)=(t.functional.gnsStarAlgHom a).comp T)
    (happrox : ∀ z ∈ cyclicSubspace t.functional.gnsStarAlgHom.range
        (t.functional.gnsStarAlgHom (f q) (blockEmbedding t S hfree hij 0 v)),
      ‖G z-T z‖≤δ*‖z‖) :
    ‖B (k+1) (repeatInsertion t S s hs (k+1) v)-
      repeatInsertion t S s hs (k+1) (B 0 v)‖≤2*δ*‖v‖ := by
  have hscale : Real.sqrt c*‖TracialGNS.algebraVector (factorTrace t f hf) q‖≤1 := by
    apply (scale_normalization t f hf q hq (letterValue t S i (x 0)) ?_ (hxq 0) c hc (hxx 0)).le
    change ‖t.functional.toPreGNS (t.functional.ofPreGNS (x 0 : preSpace t))‖=1
    rw [PositiveLinearMap.toPreGNS_ofPreGNS]
    exact hx 0
  let L := t.functional.gnsStarAlgHom
  let b0 := blockEmbedding t S hfree hij 0
  let ξ := L (f q) (b0 v)
  let y := T ξ-G ξ
  have hTapp (a : A) (z : t.functional.GNS) : T (L a z)=L a (T z) :=
    congrArg (fun R : t.functional.GNS →L[ℂ] t.functional.GNS => R z) (hT a)
  have hqξ : L (f q) ξ=ξ := by
    change (L (f q)*L (f q)) (b0 v)=L (f q) (b0 v)
    rw [←map_mul,←map_mul,hq.isIdempotentElem.eq]
  have hGξ : G ξ=L (f q) (b0 (B 0 v)) :=
    base_intertwining t S f hf hS hfree hij G B hB s hs (x 0) q v
  have hqy : L (f q) y=y := by
    dsimp only [y]
    rw [map_sub,←hTapp,hqξ,hGξ]
    change T ξ-(L (f q)*L (f q)) (b0 (B 0 v))=T ξ-L (f q) (b0 (B 0 v))
    rw [←map_mul,←map_mul,hq.isIdempotentElem.eq]
  have hy : ‖y‖≤δ*(‖TracialGNS.algebraVector (factorTrace t f hf) q‖*‖v‖) := by
    have he := happrox ξ (mem_cyclicSubspace_self _ _)
    rw [norm_sub_rev] at he
    have hn := norm_base_mul t S f hf hS hfree hij s hs (x 0) q v
    exact he.trans_eq (congrArg (fun r : ℝ => δ*r) hn)
  have hxy (n : ℕ) : ‖L (letterValue t S i (x n)) y‖≤δ*‖v‖ := by
    rw [FreeCreation.norm_mul_supported t _ (f q) c hc (hxx n) y hqy]
    calc
      _ ≤ Real.sqrt c*(δ*(‖TracialGNS.algebraVector (factorTrace t f hf) q‖*‖v‖)) :=
        mul_le_mul_of_nonneg_left hy (Real.sqrt_nonneg c)
      _ = (Real.sqrt c*‖TracialGNS.algebraVector (factorTrace t f hf) q‖)*(δ*‖v‖) := by ring
      _ ≤ 1*(δ*‖v‖) := mul_le_mul_of_nonneg_right hscale (mul_nonneg hδ (norm_nonneg _))
      _ = _ := one_mul _
  have hnormx (n : ℕ) : ‖t.functional.toPreGNS (letterValue t S i (x n))‖=1 := by
    change ‖t.functional.toPreGNS (t.functional.ofPreGNS (x n : preSpace t))‖=1
    rw [PositiveLinearMap.toPreGNS_ofPreGNS]
    exact hx n
  have hnorms : ‖t.functional.toPreGNS (letterValue t S j s)‖=1 := by
    change ‖t.functional.toPreGNS (t.functional.ofPreGNS (s : preSpace t))‖=1
    rw [PositiveLinearMap.toPreGNS_ofPreGNS]
    exact hs
  apply le_of_forall_pos_le_add
  intro η hη
  have hevent := FreeCreation.repeated_prefix_eventual_bound t S hfree hij
    (fun n => letterValue t S i (x n)) (letterValue t S j s)
    (fun n => (x n).property.1) (fun n => (x n).property.2) hnormx hxs
    s.property.1 s.property.2 hnorms hmoment hgen k M hM y η hη
  obtain ⟨n, hn⟩ := hevent.exists
  let a := (letterValue t S j s*letterValue t S i (x n))^k*letterValue t S j s
  let ξn := L ((letterValue t S j s*letterValue t S i (x n))^(k+1)) (b0 v)
  have hp : (letterValue t S j s*letterValue t S i (x n))^(k+1)=a*letterValue t S i (x n) := by
    dsimp only [a]
    rw [pow_succ,mul_assoc]
  have hξn : ξn=L (a*letterValue t S i (x n)) ξ := by
    dsimp only [ξn,ξ]
    rw [hp]
    change L (a*letterValue t S i (x n)) (b0 v)=
      (L (a*letterValue t S i (x n))*L (f q)) (b0 v)
    have hsupp : (a*letterValue t S i (x n))*f q=a*letterValue t S i (x n) :=
      (mul_assoc _ _ _).trans (congrArg (fun b : A => a*b) (hxq n))
    rw [←map_mul,hsupp]
  have hmem : ξn ∈ cyclicSubspace L.range ξ := by
    rw [hξn]
    exact cyclicSubspace_invariant L.range ξ (show L _ ∈ L.range from ⟨_,rfl⟩) ξ (mem_cyclicSubspace_self _ _)
  have hξnorm : ‖ξn‖=‖v‖ := repeated_norm t S f hf hS hfree hij s hs (x n) (hx n) (k+1) v
  have hcomp (z : t.functional.GNS) : L a (L (letterValue t S i (x n)) (L (f q) z))=
      L ((letterValue t S j s*letterValue t S i (x n))^(k+1)) z := by
    change (L a*(L (letterValue t S i (x n))*L (f q))) z=_
    rw [←map_mul,hxq n,←map_mul,←hp]
  have heq : G ξn-L ((letterValue t S j s*letterValue t S i (x n))^(k+1)) (b0 (B 0 v))=
      (G ξn-T ξn)+L a (L (letterValue t S i (x n)) y) := by
    rw [hξn,hTapp]
    dsimp only [y]
    rw [map_sub,map_sub,hGξ,hcomp]
    simp only [map_mul,mul_apply_eq_comp]
    abel
  have hfixed := repeated_error_norm t S f hf hS hfree hij G B hB s hs (x n) (hx n) (k+1) v
  rw [←hfixed]
  change ‖G ξn-L _ (b0 (B 0 v))‖≤_
  rw [heq]
  have hfirst := happrox ξn hmem
  rw [hξnorm] at hfirst
  have hsecond : ‖L a (L (letterValue t S i (x n)) y)‖≤δ*‖v‖+η :=
    hn.trans (add_le_add (hxy n) le_rfl)
  exact (norm_add_le _ _).trans ((add_le_add hfirst hsecond).trans_eq (by ring))

end Kadison.FreeBlocks

end

end
end

end OAI
