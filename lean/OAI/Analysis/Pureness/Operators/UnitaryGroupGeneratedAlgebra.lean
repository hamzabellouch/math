import OAI.Analysis.Pureness.GroupAlgebra.GroupTraceReconstruction
import OAI.Analysis.Pureness.Cuntz.MatrixTraceCorrespondence

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ComplexOrder
variable {G B : Type*} [Group G] [CStarAlgebra B]
variable (u : G →* unitary B)

def unitaryGroupSpan : StarSubalgebra ℂ B where
  carrier := Submodule.span ℂ (Set.range (fun g => (u g : B)))
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  one_mem' := by
    simpa using (Submodule.subset_span (R := ℂ)
      (s := Set.range (fun g => (u g : B))) ⟨1,rfl⟩)
  mul_mem' := by
    intro a b ha hb
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g,rfl⟩ := hx
      induction hb using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨h,rfl⟩ := hy
        exact Submodule.subset_span ⟨g*h,by simp⟩
      | zero => simp
      | add x y _ _ hx hy => simpa [mul_add] using Submodule.add_mem _ hx hy
      | smul c x _ hx => simpa [mul_smul_comm] using Submodule.smul_mem _ c hx
    | zero => simp
    | add x y _ _ hx hy => simpa [add_mul] using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa [smul_mul_assoc] using Submodule.smul_mem _ c hx
  algebraMap_mem' c := by
    have h : (1 : B) ∈ Submodule.span ℂ (Set.range (fun g => (u g : B))) := by
      simpa using (Submodule.subset_span (R := ℂ) (s := Set.range (fun g => (u g : B))) ⟨1,rfl⟩)
    simpa [Algebra.algebraMap_eq_smul_one] using Submodule.smul_mem _ c h
  star_mem' := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g,rfl⟩ := hx
      exact Submodule.subset_span ⟨g⁻¹,by dsimp only; rw [map_inv]; rfl⟩
    | zero => simp
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa using Submodule.smul_mem _ (star c) hx

def unitaryGroupAlgebra : StarSubalgebra ℂ B := (unitaryGroupSpan u).topologicalClosure

instance unitaryGroupAlgebra_closed : IsClosed (unitaryGroupAlgebra u : Set B) :=
  StarSubalgebra.isClosed_topologicalClosure _
instance unitaryGroupAlgebra_cstar : CStarAlgebra (unitaryGroupAlgebra u) :=
  StarSubalgebra.cstarAlgebra _
instance (priority := 2000) unitaryGroupAlgebra_order : PartialOrder (unitaryGroupAlgebra u) :=
  CStarAlgebra.spectralOrder _
instance (priority := 2000) unitaryGroupAlgebra_preorder : Preorder (unitaryGroupAlgebra u) :=
  (unitaryGroupAlgebra_order u).toPreorder
instance (priority := 2000) unitaryGroupAlgebra_le : LE (unitaryGroupAlgebra u) :=
  (unitaryGroupAlgebra_order u).toLE
instance unitaryGroupAlgebra_starOrdered : StarOrderedRing (unitaryGroupAlgebra u) :=
  CStarAlgebra.spectralOrderedRing _
instance (priority := 2000) unitaryGroupAlgebra_orderedAdd : IsOrderedAddMonoid (unitaryGroupAlgebra u) :=
  StarOrderedRing.toIsOrderedAddMonoid

lemma unitaryGroup_mem (g : G) : (u g : B) ∈ unitaryGroupAlgebra u :=
  StarSubalgebra.le_topologicalClosure _ (Submodule.subset_span ⟨g,rfl⟩)

def unitaryGroupGenerator : G →* unitary (unitaryGroupAlgebra u) where
  toFun g := ⟨⟨u g,unitaryGroup_mem u g⟩,by
    constructor <;> apply Subtype.ext
    · exact Unitary.coe_star_mul_self _
    · exact Unitary.coe_mul_star_self _⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; simp
  map_mul' g h := by apply Subtype.ext; apply Subtype.ext; simp

lemma unitaryGroupGenerator_dense :
    (Submodule.span ℂ (Set.range (fun g => (unitaryGroupGenerator u g : unitaryGroupAlgebra u)))).topologicalClosure = ⊤ := by
  let S := Submodule.span ℂ (Set.range (fun g => (unitaryGroupGenerator u g : unitaryGroupAlgebra u)))
  let v := (unitaryGroupAlgebra u).subtype.toLinearMap
  have he : S.map v = (unitaryGroupSpan u).toSubalgebra.toSubmodule := by
    rw [Submodule.map_span]
    congr 1
    ext b
    constructor
    · rintro ⟨x,⟨g,rfl⟩,rfl⟩
      exact ⟨g,rfl⟩
    · rintro ⟨g,rfl⟩
      exact ⟨unitaryGroupGenerator u g,⟨g,rfl⟩,rfl⟩
  have hc : IsClosed ((S.topologicalClosure).map v : Set B) := by
    have hi : Topology.IsClosedEmbedding (fun x : unitaryGroupAlgebra u => (x : B)) :=
      (unitaryGroupAlgebra_closed u).isClosedEmbedding_subtypeVal
    exact hi.isClosedMap _ S.isClosed_topologicalClosure
  have hle : unitaryGroupAlgebra u ≤
      ((S.topologicalClosure).map v : Set B) := by
    apply closure_minimal ?_ hc
    intro x hx
    have : x ∈ S.map v := by rwa [he]
    exact Submodule.map_mono S.le_topologicalClosure this
  apply top_unique
  intro x _
  obtain ⟨y,hy,hxy⟩ := hle x.property
  have heq : y=x := Subtype.ext hxy
  exact heq ▸ hy

variable [PartialOrder B] [StarOrderedRing B]
variable (τ : TracialState B)

def unitaryGroupTracialState : TracialState (unitaryGroupAlgebra u) :=
  τ.comap (unitaryGroupAlgebra u).subtype

lemma unitaryGroupTracialState_apply (a : unitaryGroupAlgebra u) :
    (unitaryGroupTracialState u τ).functional a = τ.functional (a : B) := rfl

lemma unitaryGroupTracialState_faithful
    (hτ : ∀ b : B, τ.functional (star b*b)=0 → b=0)
    (a : unitaryGroupAlgebra u)
    (ha : (unitaryGroupTracialState u τ).functional (star a*a)=0) : a=0 :=
  Subtype.ext (hτ a ha)
end CuntzPureness

end

end OAI
