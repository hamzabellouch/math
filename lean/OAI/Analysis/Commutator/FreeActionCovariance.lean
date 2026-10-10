import Mathlib
import OAI.Analysis.Commutator.FreeAction
import OAI.Analysis.Commutator.FreeSymmetry15
import OAI.Analysis.Commutator.TracialConjugation

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeWordAction

open FreeWordTensor FreeMoments

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (α : ι → A ≃⋆ₐ[ℂ] A)
  (hmem : ∀ i a, a∈S i → α i a∈S i)
  (hτ : ∀ i a, t.functional (α i a)=t.functional a)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

include hfree hgen in
lemma ext_reduced {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F G : t.functional.GNS →L[ℂ] E)
    (hw : ∀ w : List (Letter S t.functional.toLinearMap), Reduced w →
      F (TracialGNS.algebraVector t.functional (word w))=
      G (TracialGNS.algebraVector t.functional (word w))) : F=G := by
  apply ActualHilbertSum.map_ext (wordSpace t S) (wordInclusion t S hfree)
    (isHilbertSum_of_generation t S hfree hgen)
  intro is
  ext x
  change F (wordEmbedding t S hfree is.val is.property x) = G (wordEmbedding t S hfree is.val is.property x)
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    simp only [wordEmbedding_coe]
    have hs : x∈Submodule.span ℂ (Set.range (pure t S is.val)) := by rw [span_pure]; trivial
    induction hs using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p,rfl⟩ := hy
      rw [readPre_pure]
      exact hw _ (letters_reduced t S is.val p is.property)
    | zero => simp [Completion.coe_zero]
    | add x y _ _ hx hy => simp only [map_add, Completion.coe_add] at *; exact congrArg₂ (·+·) hx hy
    | smul c x _ hx => simp only [map_smul, Completion.coe_smul] at *; exact congrArg (c • ·) hx

lemma action_generator_word (i : ι) (a : A) (ha : a∈S i)
    (w : List (Letter S t.functional.toLinearMap)) (hw : Reduced w) :
    action t S α hmem hτ hfree hgen (TracialGNS.algebraVector t.functional (a*word w)) =
      TracialGNS.algebraVector t.functional
        (α i a*word (w.map (letter t S α hmem hτ))) := by
  let V := TracialGNS.algebraVector t.functional
  let W := action t S α hmem hτ hfree hgen
  have hword : ∀ w, Reduced w → W (V (word w))=V (word (w.map (letter t S α hmem hτ))) :=
    fun w hw => action_word t S α hmem hτ hfree hgen w hw
  have hone : W (V 1)=V 1 := hword [] reduced_nil
  let c : Letter S t.functional.toLinearMap :=
    ⟨i,a-t.functional a • (1:A),sub_mem ha (SMulMemClass.smul_mem _ (one_mem _)),
      by simp [map_sub,map_smul,t.normalized]⟩
  change W (V (a*word w))=V (α i a*word (w.map (letter t S α hmem hτ)))
  cases w with
  | nil =>
    have h := hword [c] (List.IsChain.singleton c)
    change W (V ((a-t.functional a • (1:A))*1)) =
      V (α i (a-t.functional a • (1:A))*1) at h
    simp only [mul_one,map_sub,map_smul,map_one,hone] at h
    simpa only [word_nil,List.map_nil,mul_one] using (sub_left_inj.mp h)
  | cons b w =>
    by_cases hib : i=b.color
    · let d : Letter S t.functional.toLinearMap :=
        ⟨i,a*b.val-t.functional (a*b.val) • (1:A),
          sub_mem (mul_mem ha (by simpa only [hib] using b.mem))
            (SMulMemClass.smul_mem _ (one_mem _)),
          by simp [map_sub,map_smul,t.normalized]⟩
      have hd : Reduced (d::w) := by
        exact hw.imp_head (by intro c hc; simpa only [d,hib] using hc)
      have ht := hword w hw.tail
      have h := hword (d::w) hd
      have hid : (a*b.val-t.functional (a*b.val) • (1:A))*word w =
          a*word (b::w)-t.functional (a*b.val) • word w := by
        simp only [word_cons,sub_mul,smul_mul_assoc,one_mul,mul_assoc]
      have hj : α i (a*b.val-t.functional (a*b.val) • (1:A))*
            word (w.map (letter t S α hmem hτ)) =
          α i a*word ((b::w).map (letter t S α hmem hτ)) -
            t.functional (a*b.val) • word (w.map (letter t S α hmem hτ)) := by
        simp only [map_sub,map_smul,map_mul,map_one,List.map_cons,word_cons,letter_val,
          sub_mul,smul_mul_assoc,one_mul,mul_assoc,hib]
      change W (V ((a*b.val-t.functional (a*b.val) • (1:A))*word w)) =
        V (α i (a*b.val-t.functional (a*b.val) • (1:A))*
          word (w.map (letter t S α hmem hτ))) at h
      rw [hid,hj] at h
      simp only [map_sub,map_smul,ht] at h
      exact sub_left_inj.mp h
    · have hc : Reduced (c::b::w) := by
        exact List.isChain_cons_cons.mpr ⟨hib,hw⟩
      have ht := hword (b::w) hw
      have h := hword (c::b::w) hc
      change W (V ((a-t.functional a • (1:A))*word (b::w))) =
        V (α i (a-t.functional a • (1:A))*word ((b::w).map (letter t S α hmem hτ))) at h
      simp only [sub_mul,smul_mul_assoc,one_mul,map_sub,map_smul,map_one,ht] at h
      exact sub_left_inj.mp h

lemma action_left (i : ι) (a : A) (ha : a∈S i) :
    (action t S α hmem hτ hfree hgen).toContinuousLinearMap.comp (t.functional.gnsStarAlgHom a) =
    (t.functional.gnsStarAlgHom (α i a)).comp (action t S α hmem hτ hfree hgen).toContinuousLinearMap := by
  apply ext_reduced t S hfree hgen
  intro w hw
  simp only [ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,
    TracialGNS.algebraVector_apply,TracialGNS.left_coe]
  rw [action_word t S α hmem hτ hfree hgen w hw]
  rw [TracialGNS.left_coe]
  exact action_generator_word t S α hmem hτ hfree hgen i a ha w hw

end Kadison.FreeWordAction

end

end
end

end OAI
