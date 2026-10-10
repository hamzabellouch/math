import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.InitialPointwiseTable
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.AlignedGroups

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FiniteCovariance

variable {α β ι C G : Type*} [Finite β] [Finite ι] [Group C] [Finite C] [Group G]

theorem finite_covariance_eventually (f : α → G)
    (c : C →* G) (W : C → FreeGroup α) (hW : ∀ s, FreeGroup.lift f (W s) = c s)
    (w : β → FreeGroup α) (v : ι → FreeGroup α)
    (ht : ∀ i j, Commute (FreeGroup.lift f (w i)) (FreeGroup.lift f (w j)))
    (R : C → Multiplicative (FreeAbelianGroup β) →* Multiplicative (FreeAbelianGroup β))
    (b : C → ι → ι)
    (hx : ∀ s i, c s * FreeGroup.lift f (v i) * (c s)⁻¹ = FreeGroup.lift f (v (b s i)))
    (hR : ∀ s k, c s * commutingFamilyHom (fun j => FreeGroup.lift f (w j)) ht k *
      (c s)⁻¹ = commutingFamilyHom (fun j => FreeGroup.lift f (w j)) ht (R s k)) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M →
      ∃ c' : C →* BoundedRelationCover M f,
        (coverMap M f).comp c' = c ∧
        (∀ s, c' s = PresentedGroup.mk (shortRelations M f) (W s)) ∧
        ∀ t : Multiplicative (FreeAbelianGroup β) →* BoundedRelationCover M f,
          (∀ i, t (Multiplicative.ofAdd (FreeAbelianGroup.of i)) =
            PresentedGroup.mk (shortRelations M f) (w i)) →
          (∀ s k, c' s*t k*(c' s)⁻¹ = t (R s k)) ∧
          (∀ s i, c' s*PresentedGroup.mk (shortRelations M f) (v i)*(c' s)⁻¹ =
            PresentedGroup.mk (shortRelations M f) (v (b s i))) := by
  classical
  let T := Multiplicative (FreeAbelianGroup β)
  let q : T →* G := commutingFamilyHom (fun j => FreeGroup.lift f (w j)) ht
  let P : FreeGroup β →* FreeGroup α := FreeGroup.lift w
  have he : (FreeGroup.lift f).comp P = q.comp (translationWordMap β) := by
    ext j
    simp only [MonoidHom.comp_apply,P,translationWordMap,FreeGroup.lift_apply_of]
    exact (commutingFamilyHom_of (fun j => FreeGroup.lift f (w j)) ht j).symm
  choose V hV using fun z : C × β => translationWordMap_surjective
    (R z.1 (Multiplicative.ofAdd (FreeAbelianGroup.of z.2)))
  obtain ⟨L₁,hL₁⟩ := finite_table_lift_eventually f c W hW
  obtain ⟨L₂,hL₂⟩ := finite_word_equalities_eventually f
    (fun z : C × β => W z.1*w z.2*(W z.1)⁻¹) (fun z => P (V z)) (by
      rintro ⟨s,i⟩
      simp only [map_mul,map_inv,hW]
      have hv := DFunLike.congr_fun he (V (s,i))
      simp only [MonoidHom.comp_apply,hV] at hv
      rw [hv,← hR s]
      congr 2
      exact (commutingFamilyHom_of (fun j => FreeGroup.lift f (w j)) ht i).symm)
  obtain ⟨L₃,hL₃⟩ := finite_word_equalities_eventually f
    (fun z : C × ι => W z.1*v z.2*(W z.1)⁻¹) (fun z => v (b z.1 z.2)) (by
      intro z
      simpa only [map_mul,map_inv,hW] using hx z.1 z.2)
  refine ⟨max L₁ (max L₂ L₃),fun M hM => ?_⟩
  obtain ⟨c',hc',hcW⟩ := hL₁ M ((le_max_left _ _).trans hM)
  refine ⟨c',hc',hcW,fun t ht' => ⟨?_,?_⟩⟩
  · have he' : t.comp (translationWordMap β) =
        (PresentedGroup.mk (shortRelations M f)).comp P := by
      ext j
      simpa [translationWordMap,P] using ht' j
    intro s k
    have hh : (MulAut.conj (c' s)).toMonoidHom.comp t = t.comp (R s) := by
      apply freeAbelianHom_ext
      intro i
      change c' s*t (Multiplicative.ofAdd (FreeAbelianGroup.of i))*(c' s)⁻¹ = _
      rw [hcW,ht']
      have hv := DFunLike.congr_fun he' (V (s,i))
      simp only [MonoidHom.comp_apply,hV] at hv
      rw [MonoidHom.comp_apply,hv]
      simpa only [map_mul,map_inv] using hL₂ M
        ((le_max_left _ _).trans ((le_max_right _ _).trans hM)) (s,i)
    exact DFunLike.congr_fun hh k
  · intro s i
    rw [hcW]
    simpa only [map_mul,map_inv] using hL₃ M
      ((le_max_right _ _).trans ((le_max_right _ _).trans hM)) (s,i)

end FiniteCovariance

section SourceConstantCovariance

variable (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)

noncomputable def reindexSmallConditional (s : alternatingGroup (Fin (m+1)))
    (b : SmallConditional m) : SmallConditional m :=
  (b.1,⟨s.val*b.2.val*s.val⁻¹, (alternatingGroup (Fin (m+1))).mul_mem
    ((alternatingGroup (Fin (m+1))).mul_mem s.property b.2.property.1)
    ((alternatingGroup (Fin (m+1))).inv_mem s.property),
    by simpa only [Equiv.Perm.card_support_conj] using b.2.property.2⟩)

@[simp] theorem reindexSmallConditional_support (s : alternatingGroup (Fin (m+1)))
    (b : SmallConditional m) :
    (reindexSmallConditional m s b).2.val.support = b.2.val.support.map s.val.toEmbedding :=
  Equiv.Perm.support_conj

theorem constant_conjugate_conditional (U : polygonAlgebra a)
    (s z : Equiv.Perm (Fin (m+1))) :
    conditionalHom (wholePolygon a) s * conditionalHom U z *
      (conditionalHom (wholePolygon a) s)⁻¹ = conditionalHom U (s*z*s⁻¹) := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  change conditionalPerm (wholePolygon a) s
    (conditionalPerm U z ((conditionalPerm (wholePolygon a) s).symm p)) =
      conditionalPerm U (s*z*s⁻¹) p
  by_cases hp : p.2 ∈ U.val <;>
    simp [conditionalPerm,wholePolygon,hp,Equiv.Perm.mul_apply]

theorem source_constant_lattice_action :
    ∃ R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)),
      ∀ s k, conditionalAlternatingHom (wholePolygon a) s *
        sourceLatticeMap a r m hm k *
        (conditionalAlternatingHom (wholePolygon a) s)⁻¹ =
          sourceLatticeMap a r m hm (R s k) := by
  classical
  let T := Multiplicative (FreeAbelianGroup (Fin m × Fin 2))
  let q := sourceLatticeMap a r m hm
  let c := conditionalAlternatingHom (a := a) (m := m+1) (wholePolygon a)
  have hb : ∀ (s : alternatingGroup (Fin (m+1))) (i : Fin m × Fin 2),
      ∃ k : T, q k = c s*q (Multiplicative.ofAdd (FreeAbelianGroup.of i))*(c s)⁻¹ := by
    intro s i
    let v : CutRing × CutRing := if i.2 = 0 then (cutTau,0) else (0,cutTau)
    obtain ⟨k,hk⟩ := sourceLatticeFullMap_difference a r m hm
      (s.val (Fin.last m)) (s.val i.1.castSucc) v
    refine ⟨k,?_⟩
    apply Subtype.ext
    change sourceLatticeFullMap a r m hm k =
      conditionalHom (wholePolygon a) s.val *
        sourceLatticeFullMap a r m hm (Multiplicative.ofAdd (FreeAbelianGroup.of i)) *
        (conditionalHom (wholePolygon a) s.val)⁻¹
    rw [hk,sourceLatticeFullMap_of]
    change trackTranslation (a := a) _ = conditionalHom (wholePolygon a) s.val *
      trackTranslation (Pi.single i.1.castSucc v - Pi.single (Fin.last m) v) *
      (conditionalHom (wholePolygon a) s.val)⁻¹
    rw [constant_conjugate_translation]
    congr 1
    funext j
    simp only [Pi.sub_apply,Pi.single_apply]
    congr 1 <;> congr 1 <;> exact propext (Equiv.symm_apply_eq s.val).symm
  choose B hB using hb
  let R := fun s => commutingFamilyHom (B s) (fun _ _ => Commute.all _ _)
  refine ⟨R,fun s k => ?_⟩
  have he : (MulAut.conj (c s)).toMonoidHom.comp q = q.comp (R s) := by
    apply freeAbelianHom_ext
    intro i
    rw [MonoidHom.comp_apply,MonoidHom.comp_apply]
    change c s*q (Multiplicative.ofAdd (FreeAbelianGroup.of i))*(c s)⁻¹ =
      q ((commutingFamilyHom (B s) (fun _ _ => Commute.all _ _))
        (Multiplicative.ofAdd (FreeAbelianGroup.of i)))
    rw [commutingFamilyHom_of,hB]
  exact DFunLike.congr_fun he k

theorem source_constant_covariance_eventually
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm' : 15 ≤ m+1) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M →
      ∃ c : alternatingGroup (Fin (m+1)) →*
          BoundedRelationCover M (alternatingGenerator a r m hm),
        (coverMap M (alternatingGenerator a r m hm)).comp c =
          conditionalAlternatingHom (wholePolygon a) ∧
        (∀ b : {σ : Equiv.Perm (Fin (m+1)) // σ ∈ alternatingGroup (Fin (m+1)) ∧
          σ.support.card ≤ 5}, c ⟨b.val,b.property.1⟩ =
            PresentedGroup.of (sourceConditionalLabel m (0,b))) ∧
        ∃ R : alternatingGroup (Fin (m+1)) →
          Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
          Multiplicative (FreeAbelianGroup (Fin m × Fin 2)),
        ∀ t : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
          BoundedRelationCover M (alternatingGenerator a r m hm),
          (∀ i, t (Multiplicative.ofAdd (FreeAbelianGroup.of i)) =
            PresentedGroup.of (Sum.inr i)) →
          (∀ s k, c s*t k*(c s)⁻¹ = t (R s k)) ∧
          (∀ s (b : SmallConditional m), c s*PresentedGroup.of (Sum.inl b)*(c s)⁻¹ =
            PresentedGroup.of (Sum.inl (reindexSmallConditional m s b))) := by
  classical
  let f := alternatingGenerator a r m hm
  let c := conditionalAlternatingHom (a := a) (m := m+1) (wholePolygon a)
  choose W hW using fun s => alternatingGenerator_surjective a r m hr hm' hm (c s)
  obtain ⟨R,hR⟩ := source_constant_lattice_action a r m hm
  obtain ⟨L,hL⟩ := finite_covariance_eventually f c W hW
    (fun i : Fin m × Fin 2 => FreeGroup.of (show SourceGeneratorLabel m from Sum.inr i))
    (fun b : SmallConditional m => FreeGroup.of (show SourceGeneratorLabel m from Sum.inl b))
    (fun i j => by
      change Commute (f (Sum.inr i)) (f (Sum.inr j))
      exact source_translation_commute a r m hm i j)
    R (reindexSmallConditional m) (by
      intro s b
      change c s*f (Sum.inl b)*(c s)⁻¹ = f (Sum.inl (reindexSmallConditional m s b))
      apply Subtype.ext
      exact constant_conjugate_conditional a m (initialTest a r b.1) s.val b.2.val)
    hR
  obtain ⟨L₀,hL₀⟩ := finite_word_equalities_eventually f
    (fun b : {σ : Equiv.Perm (Fin (m+1)) // σ ∈ alternatingGroup (Fin (m+1)) ∧
      σ.support.card ≤ 5} => W ⟨b.val,b.property.1⟩)
    (fun b => FreeGroup.of (sourceConditionalLabel m (0,b))) (by
      intro b
      rw [hW,FreeGroup.lift_apply_of]
      rfl)
  refine ⟨max L L₀,fun M hM => ?_⟩
  obtain ⟨c',hc',hcW,hc⟩ := hL M ((le_max_left _ _).trans hM)
  refine ⟨c',hc',?_,R,hc⟩
  intro b
  rw [hcW]
  exact hL₀ M ((le_max_right _ _).trans hM) b

end SourceConstantCovariance

end SimpleAmenable
end
end

end OAI
