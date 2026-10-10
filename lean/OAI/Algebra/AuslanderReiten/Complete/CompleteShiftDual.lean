import OAI.Algebra.AuslanderReiten.Complete.CompleteShift

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

namespace HomExactAt

variable {U V W U' V' W' : Type u}
variable [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W] [AddCommGroup U'] [Module R U']
variable [AddCommGroup V'] [Module R V'] [AddCommGroup W'] [Module R W']

theorem congr {e : U →ₗ[R] V} {d : V →ₗ[R] W}
    (h : HomExactAt e d) (e' : U' →ₗ[R] V') (d' : V' →ₗ[R] W')
    (a : U ≃ₗ[R] U') (b : V ≃ₗ[R] V') (c : W ≃ₗ[R] W')
    (he : e'.comp a.toLinearMap = b.toLinearMap.comp e)
    (hd : d'.comp b.toLinearMap = c.toLinearMap.comp d) : HomExactAt e' d' := by
  intro f hf
  have hfb : (f.comp b.toLinearMap).comp e = 0 := by
    rw [LinearMap.comp_assoc, ← he, ← LinearMap.comp_assoc, hf, LinearMap.zero_comp]
  obtain ⟨g, hg⟩ := h (f.comp b.toLinearMap) hfb
  refine ⟨g.comp c.symm.toLinearMap, ?_⟩
  apply LinearMap.ext
  intro x'
  obtain ⟨x, rfl⟩ := b.surjective x'
  change g (c.symm (d' (b x))) = f (b x)
  rw [show d' (b x) = c (d x) from DFunLike.congr_fun hd x, c.symm_apply_apply]
  exact DFunLike.congr_fun hg x

theorem of_shortComplex_iso {S T : ShortComplex (ModuleCat.{u} R)} (E : S ≅ T)
    (h : HomExactAt S.f.hom S.g.hom) : HomExactAt T.f.hom T.g.hom := by
  apply h.congr T.f.hom T.g.hom (asIso E.hom.τ₁).toLinearEquiv
    (asIso E.hom.τ₂).toLinearEquiv (asIso E.hom.τ₃).toLinearEquiv
  · exact congrArg (fun f : S.X₁ ⟶ T.X₂ => f.hom) E.hom.comm₁₂
  · exact congrArg (fun f : S.X₂ ⟶ T.X₃ => f.hom) E.hom.comm₂₃

end HomExactAt

namespace CompleteComparison

noncomputable def reverseShortComplexIso
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (i j l i' j' l' : ℤ)
    (hi : negIndexEmbedding.f i = i') (hj : negIndexEmbedding.f j = j')
    (hl : negIndexEmbedding.f l = l') :
    (chainOfCochain K).sc' i' j' l' ≅ K.sc' i j l :=
  ShortComplex.isoMk (K.extendXIso negIndexEmbedding hi)
    (K.extendXIso negIndexEmbedding hj) (K.extendXIso negIndexEmbedding hl)
    (by
      change (K.extendXIso negIndexEmbedding hi).hom ≫ K.d i j =
        (chainOfCochain K).d i' j' ≫ (K.extendXIso negIndexEmbedding hj).hom
      rw [K.extend_d_eq negIndexEmbedding hi hj]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    (by
      change (K.extendXIso negIndexEmbedding hj).hom ≫ K.d j l =
        (chainOfCochain K).d j' l' ≫ (K.extendXIso negIndexEmbedding hl).hom
      rw [K.extend_d_eq negIndexEmbedding hj hl]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

end CompleteComparison

def DualExactCochain (K : CochainComplex (ModuleCat.{u} R) ℤ) : Prop :=
  ∀ i, HomExactAt (K.d (i - 1) i).hom (K.d i (i + 1)).hom

namespace DualExactCochain

open CompleteComparison

theorem of_chain {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : TotallyAcyclicComplex (chainOfCochain K)) : DualExactCochain K := by
  intro i
  let E := reverseShortComplexIso K (i - 1) i (i + 1) (-i + 1) (-i) (-i - 1)
    (by change -(i - 1) = -i + 1; omega) rfl (by change -(i + 1) = -i - 1; omega)
  exact HomExactAt.of_shortComplex_iso E (hK.dualExact (-i))

theorem to_chain {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : DualExactCochain K) :
    ∀ i, HomExactAt ((chainOfCochain K).d (i + 1) i).hom
      ((chainOfCochain K).d i (i - 1)).hom := by
  intro i
  let E := reverseShortComplexIso K (-i - 1) (-i) (-i + 1) (i + 1) i (i - 1)
    (by change -(-i - 1) = i + 1; omega) (neg_neg i)
    (by change -(-i + 1) = i - 1; omega)
  exact HomExactAt.of_shortComplex_iso E.symm (hK (-i))

theorem shift {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : DualExactCochain K) (a : ℤ) :
    DualExactCochain (K⟦a⟧) := by
  intro i
  let E := (CochainComplex.shiftShortComplexFunctor' (ModuleCat.{u} R) a (i - 1) i (i + 1)
    (i + a - 1) (i + a) (i + a + 1) (by omega) (by omega) (by omega)).app K
  exact HomExactAt.of_shortComplex_iso E.symm (hK (i + a))

end DualExactCochain

structure TotallyAcyclicCochain (K : CochainComplex (ModuleCat.{u} R) ℤ) : Prop
    extends ExactProjectiveCochain K where
  dualExact : DualExactCochain K

namespace TotallyAcyclicCochain

open CompleteComparison

theorem of_chain {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : TotallyAcyclicComplex (chainOfCochain K)) : TotallyAcyclicCochain K where
  toExactProjectiveCochain := ExactProjectiveCochain.of_chain hK.toExactProjectiveComplex
  dualExact := DualExactCochain.of_chain hK

theorem to_chain {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : TotallyAcyclicCochain K) : TotallyAcyclicComplex (chainOfCochain K) where
  toExactProjectiveComplex := hK.toExactProjectiveCochain.to_chain
  dualExact := hK.dualExact.to_chain

theorem shift {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : TotallyAcyclicCochain K) (a : ℤ) : TotallyAcyclicCochain (K⟦a⟧) where
  toExactProjectiveCochain := hK.toExactProjectiveCochain.shift a
  dualExact := hK.dualExact.shift a

end TotallyAcyclicCochain

namespace TotallyAcyclicComplex

open CompleteComparison

theorem cochainShift {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : TotallyAcyclicComplex (chainOfCochain K)) (a : ℤ) :
    TotallyAcyclicComplex (chainOfCochain (K⟦a⟧)) where
  toExactProjectiveComplex := hK.toExactProjectiveComplex.cochainShift a
  dualExact := ((DualExactCochain.of_chain hK).shift a).to_chain

end TotallyAcyclicComplex
end ArExplicit

end OAI
