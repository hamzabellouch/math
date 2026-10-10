import OAI.Analysis.CharacterCriterion.ConePauli

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [instSize : KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [instPauliData : KirchbergRordam.GenericRW.PauliData]


namespace KirchbergRordam.GenericRW.JointCalculus
open WeakDual
variable {S : Type*} [CommCStarAlgebra S]
variable {I X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable (φ : I → C(X,ℂ) →⋆ₐ[ℂ] S)

def coordinates : C(characterSpace ℂ S,I→X) where
  toFun χ i := (CharacterSpace.homeoEval X ℂ).symm (CharacterSpace.compContinuousMap (φ i) χ)
  continuous_toFun := continuous_pi fun i => (CharacterSpace.homeoEval X ℂ).symm.continuous.comp
    (CharacterSpace.compContinuousMap (φ i)).continuous

def hom : C(I→X,ℂ) →⋆ₐ[ℂ] S :=
  (gelfandStarTransform S).symm.toStarAlgHom.comp ((coordinates φ).compStarAlgHom' ℂ ℂ)

def coordinate (i : I) (f : C(X,ℂ)) : C(I→X,ℂ) := f.comp ⟨fun t => t i,continuous_apply i⟩

omit instSize instPauliData in
lemma hom_coordinate.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {S : Type contextLevel1}
    [CommCStarAlgebra S]
    {I : Type contextLevel2}
    {X : Type contextLevel3}
    [TopologicalSpace X]
    [CompactSpace X]
    [T2Space X]
    (φ : I → C(X, ℂ) →⋆ₐ[ℂ] S)
    (i : I) (f : C(X,ℂ)) : hom φ (coordinate i f)=φ i f := by
  apply (gelfandStarTransform S).injective
  change gelfandStarTransform S ((gelfandStarTransform S).symm _) = _
  rw [StarAlgEquiv.apply_symm_apply]
  ext χ
  change f ((CharacterSpace.homeoEval X ℂ).symm (CharacterSpace.compContinuousMap (φ i) χ)) = χ (φ i f)
  have h := congrArg (fun ψ : characterSpace ℂ C(X,ℂ) => ψ f)
    ((CharacterSpace.homeoEval X ℂ).apply_symm_apply (CharacterSpace.compContinuousMap (φ i) χ))
  exact h

end KirchbergRordam.GenericRW.JointCalculus

namespace KirchbergRordam.GenericRW.CentralCalculus
variable (A : Type*) [CStarAlgebra A]
def center : StarSubalgebra ℂ A := StarSubalgebra.centralizer ℂ Set.univ
instance centerClosed : IsClosed (center A : Set A) := by
  change IsClosed (Set.univ ∪ star Set.univ).centralizer
  exact Set.isClosed_centralizer _
instance centerComm : CommCStarAlgebra (center A) where
  mul_comm a b := Subtype.ext (((StarSubalgebra.mem_centralizer_iff ℂ).mp b.property) a.1 (Set.mem_univ _)).1

def inclusion : center A →⋆ₐ[ℂ] A := (center A).subtype
variable {A}
omit instSize instPauliData in
lemma mem_center.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {a : A} (ha : ∀ b,Commute a b) : a∈center A := by
  apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
  intro b _
  exact ⟨(ha b).eq.symm,(ha (star b)).eq.symm⟩
omit instSize instPauliData in
lemma commute.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    (a : center A) (b : A) : Commute (a:A) b :=
  (((StarSubalgebra.mem_centralizer_iff ℂ).mp a.property) b (Set.mem_univ _)).1.symm

variable {I X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable (φ : I→C(X,ℂ)→⋆ₐ[ℂ] A) (hc : ∀ i f a,Commute (φ i f) a)
def family (i : I) : C(X,ℂ) →⋆ₐ[ℂ] center A :=
  (φ i).codRestrict (center A) fun f => mem_center (hc i f)
def hom : C(I→X,ℂ) →⋆ₐ[ℂ] A :=
  (inclusion A).comp (JointCalculus.hom (family φ hc))
lemma hom_coordinate (i : I) (f : C(X,ℂ)) :
    hom φ hc (JointCalculus.coordinate i f)=φ i f := by
  change ((JointCalculus.hom (family φ hc) _ : center A):A)=_
  rw [JointCalculus.hom_coordinate]
  rfl
lemma hom_commute (f : C(I→X,ℂ)) (a : A) : Commute (hom φ hc f) a := commute _ _
end KirchbergRordam.GenericRW.CentralCalculus

namespace KirchbergRordam.GenericRW.CubeCalculus
open scoped CStarAlgebra
variable {I A : Type*} [CStarAlgebra A]
def coord (i : I) : C(I→unitInterval,ℂ) :=
  ⟨fun t => ((t i:ℝ):ℂ),by fun_prop⟩
omit instSize instPauliData in
lemma ext_coord.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {I : Type contextLevel1}
    {A : Type contextLevel2}
    [CStarAlgebra A]
    (φ ψ : C(I→unitInterval,ℂ) →⋆ₐ[ℂ] A)
    (h : ∀ i,φ (coord i)=ψ (coord i)) : φ=ψ := by
  let S : StarSubalgebra ℂ C(I→unitInterval,ℂ) := StarAlgHom.equalizer φ ψ
  have hc : IsClosed (S : Set C(I→unitInterval,ℂ)) := isClosed_eq (map_continuous φ) (map_continuous ψ)
  have hs : S.SeparatesPoints := by
    intro x y hxy
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hxy
    refine ⟨coord i,⟨coord i,h i,rfl⟩,?_⟩
    intro he
    apply hi
    apply Subtype.ext
    change ((x i:ℝ):ℂ)=((y i:ℝ):ℂ) at he
    exact_mod_cast he
  have ht : S=⊤ := by
    rw [← le_antisymm (StarSubalgebra.topologicalClosure_minimal le_rfl hc) S.le_topologicalClosure]
    exact ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hs
  apply StarAlgHom.ext
  intro f
  exact show f∈S from ht ▸ trivial
end KirchbergRordam.GenericRW.CubeCalculus


namespace KirchbergRordam.GenericRW.CubeFrame
open scoped BigOperators CStarAlgebra
variable {X B T I : Type*} [TopologicalSpace X] [CompactSpace X]
variable [CStarAlgebra B] [CStarAlgebra T] [Fintype I] [DecidableEq I]
variable (κ : C(X,ℂ) →⋆ₐ[ℂ] B) (ρ : B →⋆ₐ[ℂ] C(X,T))
variable (p : I→C(X,ℂ)) (u : I→B) (e : I→T)
variable (hc : ∀ f a,Commute (κ f) a)
variable (hu : ∀ i,star (u i)*u i=κ (star (p i)*p i))

omit hc hu in
omit [Fintype I] [DecidableEq I] in
omit instSize instPauliData in
lemma term_norm.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {X : Type contextLevel1}
    {B : Type contextLevel2}
    {I : Type contextLevel3}
    [TopologicalSpace X]
    [CompactSpace X]
    [CStarAlgebra B]
    (κ : C(X, ℂ) →⋆ₐ[ℂ] B)
    (p : I → C(X, ℂ))
    (u : I → B)
    (hc : ∀ (f : C(X, ℂ)) (a : B), Commute (κ f) a)
    (hu : ∀ (i : I), Star.star (u i) * u i = κ (Star.star (p i) * p i))
    (f : C(X,ℂ)) (i : I) : ‖κ f*u i‖≤‖f*p i‖ := by
  have he : star (κ f*u i)*(κ f*u i)=κ (star (f*p i)*(f*p i)) := by
    rw [star_mul,← map_star,mul_assoc,← mul_assoc (κ (star f)),← map_mul]
    rw [← mul_assoc,← (hc (star f*f) (star (u i))).eq,mul_assoc,hu,← map_mul]
    congr 1
    simp only [star_mul]
    ring
  have hn : ‖κ f*u i‖*‖κ f*u i‖≤‖f*p i‖*‖f*p i‖ := by
    rw [← CStarRing.norm_star_mul_self,he,← CStarRing.norm_star_mul_self]
    exact NonUnitalStarAlgHom.norm_apply_le κ _
  nlinarith [norm_nonneg (κ f*u i),norm_nonneg (f*p i)]

def expansion (f : I→C(X,ℂ)) : B := ∑ i,κ (f i)*u i
variable (hκ : ∀ f t,ρ (κ f) t=algebraMap ℂ T (f t))
variable (hρ : ∀ i t,ρ (u i) t=p i t • e i)
variable (ℓ : I→T →L[ℂ] ℂ) (hℓ : ∀ i j,ℓ i (e j)=if i=j then 1 else 0)

omit hκ hρ hℓ in
omit [CompactSpace X] in
omit instSize instPauliData in
lemma coefficient.{contextLevel1, contextLevel2, contextLevel3, contextLevel4}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {X : Type contextLevel1}
    {B : Type contextLevel2}
    {T : Type contextLevel3}
    {I : Type contextLevel4}
    [TopologicalSpace X]
    [CStarAlgebra B]
    [CStarAlgebra T]
    [Fintype I]
    [DecidableEq I]
    (κ : C(X, ℂ) →⋆ₐ[ℂ] B)
    (ρ : B →⋆ₐ[ℂ] C(X, T))
    (p : I → C(X, ℂ))
    (u : I → B)
    (e : I → T)
    (hκ : ∀ (f : C(X, ℂ)) (t : X), (ρ (κ f)) t = (Algebra.algebraMap ℂ T) (f t))
    (hρ : ∀ (i : I) (t : X), (ρ (u i)) t = (p i) t • e i)
    (ℓ : I → T →L[ℂ] ℂ)
    (hℓ : ∀ (i j : I), (ℓ i) (e j) = if i = j then 1 else 0)
    (f : I→C(X,ℂ)) (i : I) (t : X) :
    ℓ i (ρ (expansion κ u f) t)= (f i*p i) t := by
  simp only [expansion,map_sum,ContinuousMap.sum_apply,map_mul,ContinuousMap.mul_apply,hκ,hρ,
    Algebra.algebraMap_eq_smul_one,smul_mul_smul_comm,one_mul,map_smul,hℓ]
  simp

include hc hu hκ hρ hℓ in
lemma expansion_norm (f : I→C(X,ℂ)) :
    ‖expansion κ u f‖≤(∑ i,‖ℓ i‖)*‖ρ (expansion κ u f)‖ := by
  apply (norm_sum_le _ _).trans
  calc
    ∑ i,‖κ (f i)*u i‖ ≤ ∑ i,‖f i*p i‖ := Finset.sum_le_sum fun i _ => term_norm κ p u hc hu _ i
    _ ≤ ∑ i,‖ℓ i‖*‖ρ (expansion κ u f)‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      intro t
      rw [← coefficient κ ρ p u e hκ hρ ℓ hℓ f i t]
      exact ((ℓ i).le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (ContinuousMap.norm_coe_le_norm _ t) (norm_nonneg _))
    _ = _ := (Finset.sum_mul ..).symm

include hc hu hκ hρ hℓ in


theorem faithful (hd : DenseRange (expansion κ u)) : Function.Injective ρ := by
  have hb (x : B) : ‖x‖≤(∑ i,‖ℓ i‖)*‖ρ x‖ := by
    apply hd.induction_on (p:=fun x => ‖x‖≤(∑ i,‖ℓ i‖)*‖ρ x‖) x
    · exact isClosed_le continuous_norm (continuous_const.mul (map_continuous ρ).norm)
    · exact expansion_norm κ ρ p u e hc hu hκ hρ ℓ hℓ
  intro x y hxy
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have hz : ρ (x-y)=0 := by rw [map_sub,hxy,sub_self]
  simpa only [hz,norm_zero,mul_zero] using hb (x-y)

include hc hu hκ hρ hℓ in
lemma closed_range (hd : DenseRange (expansion κ u)) : IsClosed (Set.range ρ) :=
  (NonUnitalStarAlgHom.isometry ρ (faithful κ ρ p u e hc hu hκ hρ ℓ hℓ hd)).isClosedEmbedding.isClosed_range
end KirchbergRordam.GenericRW.CubeFrame

namespace KirchbergRordam.GenericRW.CubeFrame
open scoped BigOperators
variable {X B T I : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable [CStarAlgebra B] [CStarAlgebra T] [Fintype I] [DecidableEq I]

def scalarSection (a : T) : C(X,ℂ) →ₗ[ℂ] C(X,T) where
  toFun f := ⟨fun t => f t • a,by fun_prop⟩
  map_add' f g := by ext t; simp [add_smul]
  map_smul' c f := by ext t; simp [smul_smul]

omit [CompactSpace X] [T2Space X] in
omit instSize instPauliData in
lemma scalarSection_continuous.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {X : Type contextLevel1}
    {T : Type contextLevel2}
    [TopologicalSpace X]
    [CStarAlgebra T]
    (a : T) : Continuous (scalarSection (X:=X) a) := by
  let g : C(ℂ,T) := ⟨fun c => c • a,by fun_prop⟩
  exact g.continuous_postcomp

variable (κ : C(X,ℂ) →⋆ₐ[ℂ] B) (ρ : B →⋆ₐ[ℂ] C(X,T))
variable (p : I→C(X,ℂ)) (u : I→B) (e : I→T)
variable (hκ : ∀ f t,ρ (κ f) t=algebraMap ℂ T (f t))
variable (hρ : ∀ i t,ρ (u i) t=p i t • e i)
include hκ hρ in
omit [Fintype I] [DecidableEq I] in


lemma coefficient_mem_range (hclosed : IsClosed (Set.range ρ)) (i : I)
    (f : C(X,ℂ)) (hf : ∀ t,p i t=0 → f t=0) :
    scalarSection (e i) f ∈ Set.range ρ := by
  let f' : Vanish.Functions {t | p i t=0} := ⟨f,hf⟩
  have h (g : Vanish.Functions {t | p i t=0}) :
      scalarSection (e i) g.val ∈ Set.range ρ := by
    refine (Vanish.multiplier_dense (p i)).induction_on g
      (hclosed.preimage ((scalarSection_continuous (e i)).comp continuous_subtype_val)) ?_
    intro a
    refine ⟨κ a*u i,?_⟩
    ext t
    simp only [map_mul,ContinuousMap.mul_apply,hκ,hρ,
      Algebra.algebraMap_eq_smul_one,smul_mul_smul_comm,one_mul]
    change (a t*p i t) • e i = (p i t*a t) • e i
    rw [mul_comm]
  exact h f'

variable (ℓ : I→T →L[ℂ] ℂ)
variable (hspan : ∀ a : T,∑ i,ℓ i a • e i=a)
include hκ hρ hspan in
omit [DecidableEq I] in


theorem section_mem_range (hclosed : IsClosed (Set.range ρ)) (f : C(X,T))
    (hf : ∀ i t,p i t=0 → ℓ i (f t)=0) : f∈Set.range ρ := by
  let c (i : I) : C(X,ℂ) := ⟨fun t => ℓ i (f t),(ℓ i).continuous.comp f.continuous⟩
  have hm (i : I) : scalarSection (e i) (c i) ∈ Set.range ρ :=
    coefficient_mem_range κ ρ p u e hκ hρ hclosed i (c i) (hf i)
  have hs : ∑ i,scalarSection (e i) (c i)=f := by
    ext t
    simp only [ContinuousMap.sum_apply]
    exact hspan (f t)
  rw [← hs]
  change (∑ i,scalarSection (e i) (c i)) ∈ ρ.range
  exact sum_mem fun i _ => hm i

variable (hc : ∀ f a,Commute (κ f) a)
variable (hu : ∀ i,star (u i)*u i=κ (star (p i)*p i))
variable (hℓ : ∀ i j,ℓ i (e j)=if i=j then 1 else 0)
include hc hu hκ hρ hℓ hspan in


theorem exists_unique_lift (hd : DenseRange (expansion κ u)) (f : C(X,T))
    (hf : ∀ i t,p i t=0 → ℓ i (f t)=0) :
    ∃! b : B,ρ b=f ∧ ‖b‖=‖f‖ := by
  have hi := faithful κ ρ p u e hc hu hκ hρ ℓ hℓ hd
  obtain ⟨b,hb⟩ := section_mem_range κ ρ p u e hκ hρ ℓ hspan
    (closed_range κ ρ p u e hc hu hκ hρ ℓ hℓ hd) f hf
  refine ⟨b,⟨hb,?_⟩,?_⟩
  · rw [← hb]
    simpa only [map_zero,dist_zero_right] using
      ((NonUnitalStarAlgHom.isometry ρ hi).dist_eq b 0).symm
  · intro a ha
    exact hi (ha.1.trans hb.symm)
end KirchbergRordam.GenericRW.CubeFrame
end

end OAI
