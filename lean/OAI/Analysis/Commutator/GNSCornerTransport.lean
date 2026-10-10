import Mathlib
import OAI.Analysis.Commutator.CornerSymmetrization
import OAI.Analysis.Commutator.FreeSymmetrization
import OAI.Analysis.Commutator.NormalTraceProjection
import OAI.Analysis.Commutator.TracialVectorSubalgebra

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder

open ContinuousLinearMap

namespace Kadison.VectorGNS

open FreeWordTensor FreeMoments FreeWordAction FreeBlocks

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (ξ : H)

variable (htr : ∀ a b : M,subalgebraTrace M ξ (a*b)=subalgebraTrace M ξ (b*a))
  (hfaith : ∀ a : M,subalgebraTrace M ξ (star a*a)=0 → a=0)
  (hone : subalgebraTrace M ξ 1=1)

abbrev vectorState : FaithfulState M where
  functional := subalgebraTrace M ξ
  normalized := hone
  faithful := hfaith

include htr in
lemma ambient_range (R : Bool → StarSubalgebra ℂ M)
    {X : (subalgebraTrace M ξ).GNS →L[ℂ] (subalgebraTrace M ξ).GNS}
    (hX : X∈ambientOperators (vectorState M ξ hfaith hone) R) :
    ∃ a : M,(subalgebraTrace M ξ).gnsStarAlgHom a=X := by
  have hb : X∈Set.centralizer (Set.centralizer (Set.range (subalgebraTrace M ξ).gnsStarAlgHom)) := by
    intro Y hY
    apply (mem_ambientOperators _ _).mp hX Y
    rintro Z ⟨a,_,rfl⟩
    exact hY _ ⟨a,rfl⟩
  rw [NormalGNS.range_bicommutant M (subalgebraTrace M ξ) htr
    (subalgebraTrace_normal M ξ)] at hb
  exact hb

variable {D : Type} [CStarAlgebra D] (f : D →⋆ₐ[ℂ] M)
  (R : Bool → StarSubalgebra ℂ M)

private lemma corner_preimage (a : M) (β : ℂ)
    (hX : CornerSymmetrization.CornerElement
      (factorOperators (vectorState M ξ hfaith hone) f)
      (ambientOperators (vectorState M ξ hfaith hone) R)
      (TracialGNS.vacuum (subalgebraTrace M ξ)) β
      ((subalgebraTrace M ξ).gnsStarAlgHom a)) :
    ∃ q : D, IsStarProjection (f q) ∧ subalgebraTrace M ξ (f q)=β ∧
      f q*a=a ∧ a*f q=a := by
  obtain ⟨_,e,⟨q,hqe⟩,he,het,hel,her⟩ := hX
  change (subalgebraTrace M ξ).gnsStarAlgHom (f q)=e at hqe
  subst e
  have hq := (NormalGNS.gns_projection_iff M (subalgebraTrace M ξ) hfaith (f q)).mp he
  have hqt : subalgebraTrace M ξ (f q)=β := by
    change inner ℂ (TracialGNS.vacuum (subalgebraTrace M ξ))
      ((subalgebraTrace M ξ).gnsStarAlgHom (f q) (TracialGNS.vacuum (subalgebraTrace M ξ)))=β at het
    rw [TracialGNS.left_vacuum] at het
    exact (TracialGNS.inner_vacuum_algebraVector _ _).symm.trans het
  change (subalgebraTrace M ξ).gnsStarAlgHom (f q)*(subalgebraTrace M ξ).gnsStarAlgHom a=
    (subalgebraTrace M ξ).gnsStarAlgHom a at hel
  change (subalgebraTrace M ξ).gnsStarAlgHom a*(subalgebraTrace M ξ).gnsStarAlgHom (f q)=
    (subalgebraTrace M ξ).gnsStarAlgHom a at her
  have hl : f q*a=a := NormalGNS.gns_injective M (subalgebraTrace M ξ) hfaith
    ((map_mul (subalgebraTrace M ξ).gnsStarAlgHom (f q) a).trans hel)
  have hr : a*f q=a := NormalGNS.gns_injective M (subalgebraTrace M ξ) hfaith
    ((map_mul (subalgebraTrace M ξ).gnsStarAlgHom a (f q)).trans her)
  exact ⟨q,hq,hqt,hl,hr⟩

include htr in
theorem corner_bound (T : H →L[ℂ] H) (ε : ℝ) (β : ℂ)
    (hbound : ∀ q : D,IsStarProjection (f q) → subalgebraTrace M ξ (f q)=β →
      ∀ a : M,f q*a=a → a*f q=a →
        ‖T*(a:H →L[ℂ] H)-(a:H →L[ℂ] H)*T‖≤ε*‖a‖)
    (X : (subalgebraTrace M ξ).GNS →L[ℂ] (subalgebraTrace M ξ).GNS)
    (hX : CornerSymmetrization.CornerElement
      (factorOperators (vectorState M ξ hfaith hone) f)
      (ambientOperators (vectorState M ξ hfaith hone) R)
      (TracialGNS.vacuum (subalgebraTrace M ξ)) β X) :
    ‖compression (subalgebraTrace M ξ) M.toStarSubalgebra.subtype ξ (subalgebraTrace_subtype M ξ) T*X-
      X*compression (subalgebraTrace M ξ) M.toStarSubalgebra.subtype ξ (subalgebraTrace_subtype M ξ) T‖≤ε*‖X‖ := by
  have hrange := ambient_range M ξ htr hfaith hone R hX.1
  obtain ⟨a,rfl⟩ := hrange
  have hpreimage := corner_preimage M ξ hfaith hone f R a β hX
  obtain ⟨q,hq,hqt,hl,hr⟩ := hpreimage
  calc
    _ ≤ ‖T*(a:H →L[ℂ] H)-(a:H →L[ℂ] H)*T‖ := norm_commutator_compression_le (subalgebraTrace M ξ)
      M.toStarSubalgebra.subtype ξ (subalgebraTrace_subtype M ξ) T a
    _ ≤ ε*‖a‖ := hbound q hq hqt a hl hr
    _ = _ := by rw [NormalGNS.gns_norm M (subalgebraTrace M ξ) hfaith]

lemma commutes (T : H →L[ℂ] H) (a : M)
    (ha : T*(a:H →L[ℂ] H)=(a:H →L[ℂ] H)*T) :
    compression (subalgebraTrace M ξ) M.toStarSubalgebra.subtype ξ (subalgebraTrace_subtype M ξ) T*
      (subalgebraTrace M ξ).gnsStarAlgHom a=
    (subalgebraTrace M ξ).gnsStarAlgHom a*
      compression (subalgebraTrace M ξ) M.toStarSubalgebra.subtype ξ (subalgebraTrace_subtype M ξ) T := by
  apply sub_eq_zero.mp
  refine (compression_commutator (subalgebraTrace M ξ) M.toStarSubalgebra.subtype ξ
    (subalgebraTrace_subtype M ξ) T a).trans ?_
  change compression (subalgebraTrace M ξ) M.toStarSubalgebra.subtype ξ (subalgebraTrace_subtype M ξ)
    (T*(a:H →L[ℂ] H)-(a:H →L[ℂ] H)*T)=0
  rw [ha,sub_self]
  simp only [compression,FreeCorner.compress,comp_zero,zero_comp]

end Kadison.VectorGNS

end

end
end

end OAI
