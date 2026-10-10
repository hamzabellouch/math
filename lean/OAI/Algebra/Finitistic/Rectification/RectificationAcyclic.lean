import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import OAI.Algebra.Finitistic.Rectification.RectificationTotal

namespace OAI

namespace LittleFinitistic.RectificationAcyclic
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex

variable {C : Type*} [Category C] [Abelian C]

/-- The ordinary cone of a quasi-isomorphism is acyclic. -/
theorem cone_acyclic {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f] :
    (mappingCone f).Acyclic := by
  let P := HomotopyCategory.subcategoryAcyclic C
  have hf : P.trW ((HomotopyCategory.quotient C (.up ℤ)).map f) := by
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
      HomotopyCategory.quotient_map_mem_quasiIso_iff,HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished f
  have hz := (P.trW_iff_of_distinguished (mappingCone.triangleh f) hT).1 hf
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1 hz

/-- The total of a strict short exact sequence of complexes is acyclic. This is
applied to the associated graded source-index pieces in rectification. -/
theorem short_exact_total_acyclic (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) :
    (RectificationTotal.total S.g S.f (Homotopy.ofEq S.zero)).Acyclic := by
  have he : RectificationTotal.rectifyingMap S.g S.f (Homotopy.ofEq S.zero) =
      mappingCone.descShortComplex S := by
    simp only [RectificationTotal.rectifyingMap,CochainComplex.HomComplex.Cochain.ofHomotopy_ofEq,
      mappingCone.descShortComplex]
  change (mappingCone (RectificationTotal.rectifyingMap S.g S.f (Homotopy.ofEq S.zero))).Acyclic
  rw [he]
  let := mappingCone.quasiIso_descShortComplex hS
  exact cone_acyclic _

/-- Bounded-above acyclic complexes of projectives admit an actual contraction. -/
noncomputable def contractBoundedProjective (K : CochainComplex C ℤ) (hi : ℤ)
    [K.IsStrictlyLE hi] [∀ i, Projective (K.X i)] (hK : K.Acyclic) :
    Homotopy (𝟙 K) 0 := by
  letI := CochainComplex.isKProjective_of_projective K hi
  exact CochainComplex.IsKProjective.homotopyZero (𝟙 K) hK

/-- A quasi-isomorphism between bounded-above projective complexes has an actual
chain-map inverse up to specified homotopies, retaining the given forward map. -/
theorem bounded_projective_homotopy_inverse {K L : CochainComplex C ℤ}
    (f : K ⟶ L) [QuasiIso f] (hi : ℤ) [K.IsStrictlyLE hi] [L.IsStrictlyLE hi]
    [∀ i, Projective (K.X i)] [∀ i, Projective (L.X i)] :
    ∃ g : L ⟶ K, Nonempty (Homotopy (f ≫ g) (𝟙 K)) ∧
      Nonempty (Homotopy (g ≫ f) (𝟙 L)) := by
  classical
  have : (mappingCone f).IsStrictlyLE hi := by
    rw [isStrictlyLE_iff]
    intro i hi'
    rw [mappingCone.isZero_X_iff]
    exact ⟨K.isZero_of_isStrictlyLE hi _ (by omega),L.isZero_of_isStrictlyLE hi _ hi'⟩
  have (degree : ℤ) : Projective ((mappingCone f).X degree) := by
    apply Projective.of_iso (homotopyCofiber.XIsoBiprod f degree (degree+1) (by simp)).symm
    infer_instance
  let q := HomotopyCategory.quotient C (.up ℤ)
  have hzero : IsZero (q.obj (mappingCone f)) :=
    (HomotopyCategory.isZero_quotient_obj_iff _).2
      ⟨contractBoundedProjective _ hi (cone_acyclic f)⟩
  have : IsIso (q.map f) :=
    ((mappingCone.triangleh f).isZero₃_iff_isIso₁
      (HomotopyCategory.mappingCone_triangleh_distinguished f)).1 hzero
  let g := q.preimage (inv (q.map f))
  have hg : q.map g = inv (q.map f) := q.map_preimage _
  refine ⟨g,⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩,
    ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  · change q.map (f ≫ g) = q.map (𝟙 K)
    rw [Functor.map_comp,hg,IsIso.hom_inv_id,q.map_id]
  · change q.map (g ≫ f) = q.map (𝟙 L)
    rw [Functor.map_comp,hg,IsIso.inv_hom_id,q.map_id]

/-- A finite decreasing filtration with acyclic successive quotients is acyclic.
The hypotheses are actual short exact sequences of complexes. -/
theorem finite_exact_filtration_acyclic (n : ℕ)
    (F G : ℕ → CochainComplex C ℤ)
    (u : ∀ i, F (i+1) ⟶ F i) (v : ∀ i, F i ⟶ G i)
    (huv : ∀ i, u i ≫ v i = 0)
    (hseq : ∀ i, i < n → (ShortComplex.mk (u i) (v i) (huv i)).ShortExact)
    (hG : ∀ i, i < n → (G i).Acyclic) (hn : (F n).Acyclic) :
    (F 0).Acyclic := by
  apply Nat.decreasingInduction (motive := fun i _ => (F i).Acyclic) ?_ hn (Nat.zero_le n)
  intro i hi hnext
  exact (hseq i hi).acyclic_X₂ hnext (hG i hi)

/-- A short exact inclusion with acyclic quotient is a quasi-isomorphism. -/
theorem quasiIso_of_acyclic_quotient (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) (hQ : S.X₃.Acyclic) : QuasiIso S.f := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : Mono (HomologicalComplex.homologyMap S.f i) :=
    (hS.homology_exact₁ (i-1) i (by change i-1+1=i; omega)).mono_g
      ((hQ (i-1)).isZero_homology.eq_of_src _ _)
  have : Epi (HomologicalComplex.homologyMap S.f i) :=
    (hS.homology_exact₂ i).epi_f ((hQ i).isZero_homology.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- The given inclusion, rather than an unspecified replacement, has an actual
homotopy inverse once its quotient is proved acyclic by the finite filtration. -/
theorem inclusion_homotopy_inverse (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) (hQ : S.X₃.Acyclic) (hi : ℤ)
    [S.X₁.IsStrictlyLE hi] [S.X₂.IsStrictlyLE hi]
    [∀ i, Projective (S.X₁.X i)] [∀ i, Projective (S.X₂.X i)] :
    ∃ g : S.X₂ ⟶ S.X₁, Nonempty (Homotopy (S.f ≫ g) (𝟙 S.X₁)) ∧
      Nonempty (Homotopy (g ≫ S.f) (𝟙 S.X₂)) := by
  let := quasiIso_of_acyclic_quotient S hS hQ
  exact bounded_projective_homotopy_inverse S.f hi
end LittleFinitistic.RectificationAcyclic

end OAI
