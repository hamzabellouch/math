import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.IteratedSpectrum
import OAI.Analysis.JiangSu.DimensionDrop.SortingNetwork

namespace OAI

noncomputable section


namespace JiangSuConstruction
open scoped CStarAlgebra ComplexOrder Kronecker

theorem continuous_matching_control_two_scales (p n : ℕ) {δ r : ℝ} (hr : 0<r)
    (x y : Fin n → Interval)
    (hxy : ∀ t : ℝ,(Finset.univ.filter fun i => (x i:ℝ)≤t).card≤
      (Finset.univ.filter fun i => (y i:ℝ)≤t+δ).card)
    (hyx : ∀ t : ℝ,(Finset.univ.filter fun i => (y i:ℝ)≤t).card≤
      (Finset.univ.filter fun i => (x i:ℝ)≤t+δ).card)
    (f : Interval → Mat p) {η ηs : ℝ} (hη : 0≤η) (hηs : 0≤ηs)
    (hf : ∀ s t,dist s t≤δ → ‖f s-f t‖≤η)
    (hfs : ∀ s t,dist s t≤r → ‖f s-f t‖≤ηs) :
    ‖unitaryConjugation (continuousMatchingUnitary p n r (x,y))
        (blockDiagonalHom (f ∘ x))-blockDiagonalHom (f ∘ y)‖≤
      6*((sortingNetwork n).length:ℝ)*ηs+η := by
  let ux := networkUnitary p n r (sortingNetwork n) x
  let uy := networkUnitary p n r (sortingNetwork n) y
  let X := blockDiagonalHom (f ∘ x)
  let Y := blockDiagonalHom (f ∘ y)
  let SX := blockDiagonalHom (f ∘ (x ∘ Tuple.sort x))
  let SY := blockDiagonalHom (f ∘ (y ∘ Tuple.sort y))
  have hx : ‖unitaryConjugation ux X-SX‖≤3*((sortingNetwork n).length:ℝ)*ηs :=
    continuous_sort_unitary_control p n hr f hηs hfs x
  have hy : ‖unitaryConjugation uy Y-SY‖≤3*((sortingNetwork n).length:ℝ)*ηs :=
    continuous_sort_unitary_control p n hr f hηs hfs y
  have hs : ‖SX-SY‖≤η := by
    change ‖blockDiagonalHom _-blockDiagonalHom _‖≤_
    rw [←map_sub]
    apply (NonUnitalStarAlgHom.norm_apply_le
      (blockDiagonalHom : (Fin n → Mat p) →⋆ₐ[ℂ] TensorMat p n) _).trans
    apply (pi_norm_le_iff_of_nonneg hη).mpr
    intro i
    exact hf _ _ (interval_sorted_displacement x y δ hxy hyx i)
  have hcancel : unitaryConjugation uy⁻¹ (unitaryConjugation uy Y)=Y := by
    rw [←unitaryConjugation_mul,inv_mul_cancel,unitaryConjugation_one]
  have hb : ‖unitaryConjugation ux X-unitaryConjugation uy Y‖≤
      6*((sortingNetwork n).length:ℝ)*ηs+η := by
    have h₁ := norm_sub_le_norm_sub_add_norm_sub (unitaryConjugation ux X) SX SY
    have h₂ := norm_sub_le_norm_sub_add_norm_sub (unitaryConjugation ux X) SY
      (unitaryConjugation uy Y)
    rw [norm_sub_rev SY] at h₂
    linarith
  change ‖unitaryConjugation (uy⁻¹*ux) X-Y‖≤_
  rw [unitaryConjugation_mul,←hcancel,←map_sub]
  exact (NonUnitalStarAlgHom.norm_apply_le (unitaryConjugation uy⁻¹) _).trans hb


lemma filter_card_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (P : J → Prop) [DecidablePred P] :
    (Finset.univ.filter fun i : I => P (e i)).card=
      (Finset.univ.filter P).card := by
  classical
  rw [←Fintype.card_subtype,←Fintype.card_subtype]
  exact Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))

abbrev iteratedSize (n k : ℕ) := Fintype.card (IteratedIndex n k)
def iteratedTuple (n k : ℕ) (s : Interval) : Fin (iteratedSize n k) → Interval :=
  fun j => iteratedFamily n k ((Fintype.equivFin (IteratedIndex n k)).symm j) s

lemma iteratedTuple_continuous (n k : ℕ) : Continuous (iteratedTuple n k) := by
  apply continuous_pi
  intro j
  exact (iteratedFamily n k _).continuous

lemma iteratedTuple_shifted_counts (n : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∃ k : ℕ,∀ l,k≤l → ∀ s t : Interval,∀ v : ℝ,
      (Finset.univ.filter fun i => (iteratedTuple n l s i:ℝ)≤v).card≤
      (Finset.univ.filter fun i => (iteratedTuple n l t i:ℝ)≤v+δ).card := by
  classical
  obtain ⟨k,hk⟩ := iterated_spectrum_shifted_counts n hδ
  refine ⟨k,?_⟩
  intro l hl s t v
  change (Finset.univ.filter fun i => (iteratedFamily n l
    ((Fintype.equivFin (IteratedIndex n l)).symm i) s:ℝ)≤v).card≤_
  rw [filter_card_equiv (Fintype.equivFin (IteratedIndex n l)).symm
    (fun i => (iteratedFamily n l i s:ℝ)≤v)]
  change _≤(Finset.univ.filter fun i => (iteratedFamily n l
    ((Fintype.equivFin (IteratedIndex n l)).symm i) t:ℝ)≤v+δ).card
  rw [filter_card_equiv (Fintype.equivFin (IteratedIndex n l)).symm
    (fun i => (iteratedFamily n l i t:ℝ)≤v+δ)]
  exact hk l hl s t v

lemma finite_continuous_modulus {p : ℕ} (F : Finset C(Interval,Mat p))
    {η : ℝ} (hη : 0<η) :
    ∃ δ : ℝ,0<δ ∧ ∀ f∈F,∀ s t : Interval,dist s t≤δ → ‖f s-f t‖≤η := by
  classical
  let g : Interval → (F → Mat p) := fun s f => f.val s
  have hc : Continuous g := by apply continuous_pi; intro f; exact f.val.continuous
  have hu := CompactSpace.uniformContinuous_of_continuous hc
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff.mp hu (η/2) (by positivity)
  refine ⟨δ/2,by positivity,?_⟩
  intro f hf s t hst
  have hh : dist (g s) (g t)<η/2 := hd (by linarith)
  have hi := dist_le_pi_dist (g s) (g t) (⟨f,hf⟩:F)
  have hh' : dist (g s (⟨f,hf⟩:F)) (g t (⟨f,hf⟩:F))≤η :=
    hi.trans (le_trans hh.le (by linarith))
  simpa only [g,dist_eq_norm] using hh'

theorem actual_iterated_continuous_matching (n p : ℕ)
    (F : Finset C(Interval,Mat p)) {ε : ℝ} (hε : 0<ε) :
    ∃ k : ℕ,∀ l,k≤l → ∃ U : C(Interval×Interval,unitary (TensorMat p (iteratedSize n l))),
      ∀ f∈F,∀ s t : Interval,
        ‖unitaryConjugation (U (s,t)) (blockDiagonalHom (f ∘ iteratedTuple n l s))-
          blockDiagonalHom (f ∘ iteratedTuple n l t)‖<ε := by
  obtain ⟨δ,hδ,hF⟩ := finite_continuous_modulus F (show 0<ε/3 by positivity)
  obtain ⟨k,hk⟩ := iteratedTuple_shifted_counts n hδ
  refine ⟨k,?_⟩
  intro l hl
  let L : ℝ := ((sortingNetwork (iteratedSize n l)).length:ℝ)
  have hL : 0≤L := Nat.cast_nonneg _
  let ηs := ε/(3*(6*L+1))
  have hηs : 0<ηs := by dsimp [ηs]; positivity
  obtain ⟨r,hr,hFs⟩ := finite_continuous_modulus F hηs
  let U : C(Interval×Interval,unitary (TensorMat p (iteratedSize n l))) :=
    (continuousMatchingUnitary p (iteratedSize n l) r).comp
      ⟨fun z => (iteratedTuple n l z.1,iteratedTuple n l z.2),
        ((iteratedTuple_continuous n l).comp continuous_fst).prodMk
          ((iteratedTuple_continuous n l).comp continuous_snd)⟩
  refine ⟨U,?_⟩
  intro f hf s t
  have hh := continuous_matching_control_two_scales p (iteratedSize n l) hr
    (iteratedTuple n l s) (iteratedTuple n l t) (hk l hl s t) (hk l hl t s)
    f (show 0≤ε/3 by positivity) hηs.le (hF f hf) (hFs f hf)
  change ‖unitaryConjugation (continuousMatchingUnitary p (iteratedSize n l) r
    (iteratedTuple n l s,iteratedTuple n l t)) _-_‖<ε
  apply hh.trans_lt
  change 6*L*ηs+ε/3<ε
  have heq : ηs*(3*(6*L+1))=ε := by
    dsimp [ηs]
    exact div_mul_cancel₀ _ (by positivity)
  nlinarith

end JiangSuConstruction

end

end OAI
