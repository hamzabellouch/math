import OAI.Analysis.CharacterCriterion.PrimeSpectrum

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
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace

namespace KirchbergRordam.PrimeTensorSections
open scoped CStarAlgebra ComplexOrder TensorProduct
open PrimeDimensionDrop MatrixTensor
lemma continuous_starHom {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (f : A →⋆ₐ[ℂ] B) : Continuous f := map_continuous f
abbrev Square := unitInterval × unitInterval
variable {p q r k : ℕ}
abbrev SquareFiber (p q r k : ℕ) := Mat ((Fin p×Fin q)×(Fin r×Fin k))

def leftSection : Algebra p q →⋆ₐ[ℂ] C(Square,SquareFiber p q r k) where
  toFun f := ⟨fun x => MatrixTensor.leftMatrix (f.val x.1),
    (map_continuous MatrixTensor.leftMatrix).comp (f.val.continuous.comp continuous_fst)⟩
  map_zero' := by apply ContinuousMap.ext; intro x; exact map_zero MatrixTensor.leftMatrix
  map_one' := by apply ContinuousMap.ext; intro x; exact map_one MatrixTensor.leftMatrix
  map_add' f g := by apply ContinuousMap.ext; intro x; exact map_add MatrixTensor.leftMatrix _ _
  map_mul' f g := by apply ContinuousMap.ext; intro x; exact map_mul MatrixTensor.leftMatrix _ _
  commutes' z := by apply ContinuousMap.ext; intro x; exact MatrixTensor.leftMatrix.commutes z
  map_star' f := by apply ContinuousMap.ext; intro x; exact map_star MatrixTensor.leftMatrix _
def rightSection : Algebra r k →⋆ₐ[ℂ] C(Square,SquareFiber p q r k) where
  toFun f := ⟨fun x => MatrixTensor.rightMatrix (f.val x.2),
    (map_continuous MatrixTensor.rightMatrix).comp (f.val.continuous.comp continuous_snd)⟩
  map_zero' := by apply ContinuousMap.ext; intro x; exact map_zero MatrixTensor.rightMatrix
  map_one' := by apply ContinuousMap.ext; intro x; exact map_one MatrixTensor.rightMatrix
  map_add' f g := by apply ContinuousMap.ext; intro x; exact map_add MatrixTensor.rightMatrix _ _
  map_mul' f g := by apply ContinuousMap.ext; intro x; exact map_mul MatrixTensor.rightMatrix _ _
  commutes' z := by apply ContinuousMap.ext; intro x; exact MatrixTensor.rightMatrix.commutes z
  map_star' f := by apply ContinuousMap.ext; intro x; exact map_star MatrixTensor.rightMatrix _
lemma sections_commute (a : Algebra p q) (b : Algebra r k) :
    Commute (leftSection (r:=r) (k:=k) a) (rightSection (p:=p) (q:=q) b) := by
  apply ContinuousMap.ext
  intro x
  exact legs_commute (a.val x.1) (b.val x.2)
def sectionMap : MaxTensor.Algebra (Algebra p q) (Algebra r k) →⋆ₐ[ℂ]
    C(Square,SquareFiber p q r k) := by
  refine MaxTensor.lift (A:=Algebra p q) (B:=Algebra r k) (C:=C(Square,SquareFiber p q r k)) ?_ ?_ ?_
  · exact leftSection
  · exact rightSection
  · exact sections_commute
@[simp] lemma sectionMap_left (a : Algebra p q) (x : Square) :
    sectionMap (r:=r) (k:=k) (MaxTensor.includeLeft a) x = MatrixTensor.leftMatrix (a.val x.1) := by
  change MaxTensor.lift (C:=C(Square,SquareFiber p q r k)) _ _ _ (MaxTensor.of (a ⊗ₜ[ℂ] (1 : Algebra r k))) x = _
  rw [MaxTensor.lift_of_tmul]
  change (leftSection (r:=r) (k:=k) a * rightSection (p:=p) (q:=q) (1 : Algebra r k)) x = _
  change MatrixTensor.leftMatrix (a.val x.1) * MatrixTensor.rightMatrix (1:Fiber r k)=_
  rw [map_one,mul_one]
@[simp] lemma sectionMap_right (b : Algebra r k) (x : Square) :
    sectionMap (p:=p) (q:=q) (MaxTensor.includeRight b) x = MatrixTensor.rightMatrix (b.val x.2) := by
  change MaxTensor.lift (C:=C(Square,SquareFiber p q r k)) _ _ _ (MaxTensor.of ((1 : Algebra p q) ⊗ₜ[ℂ] b)) x = _
  rw [MaxTensor.lift_of_tmul]
  change (leftSection (r:=r) (k:=k) (1 : Algebra p q) * rightSection (p:=p) (q:=q) b) x = _
  change MatrixTensor.leftMatrix (1:Fiber p q) * MatrixTensor.rightMatrix (b.val x.2)=_
  rw [map_one,one_mul]
@[simp] lemma sectionMap_tmul (a : Algebra p q) (b : Algebra r k) (x : Square) :
    sectionMap (MaxTensor.of (a ⊗ₜ[ℂ] b)) x = subKronecker
      (evaluation p q x.1).range (evaluation r k x.2).range
      (⟨evaluation p q x.1 a,⟨a,rfl⟩⟩ ⊗ₜ[ℂ] ⟨evaluation r k x.2 b,⟨b,rfl⟩⟩) := by
  rw [MaxTensor.of_tmul,map_mul,ContinuousMap.mul_apply,sectionMap_left,sectionMap_right]
  rfl

lemma scalarLeft_commute (f : C(unitInterval,ℂ)) :
    ∀ x : MaxTensor.Algebra (Algebra p q) (Algebra r k),
      Commute (MaxTensor.includeLeft (scalar p q f)) x := by
  apply MaxTensor.commute_of_legs (StarAlgHom.id ℂ _) _
  · intro a
    exact (scalar_commute f a).map MaxTensor.includeLeft
  · intro b
    exact MaxTensor.legs_commute (scalar p q f) b
lemma scalarRight_commute (f : C(unitInterval,ℂ)) :
    ∀ x : MaxTensor.Algebra (Algebra p q) (Algebra r k),
      Commute (MaxTensor.includeRight (scalar r k f)) x := by
  apply MaxTensor.commute_of_legs (StarAlgHom.id ℂ _) _
  · intro a
    exact (MaxTensor.legs_commute a (scalar r k f)).symm
  · intro b
    exact (scalar_commute f b).map MaxTensor.includeRight
lemma irreducible_left_evaluation
    (π : IrreducibleRepresentation (MaxTensor.Algebra (Algebra p q) (Algebra r k))) :
    ∃ s : unitInterval, ∀ f, π.representation (MaxTensor.includeLeft (scalar p q f))=
        algebraMap ℂ _ (f s) := by
  exact irreducible_central_evaluation π
    (MaxTensor.includeLeft.comp (scalar p q)) scalarLeft_commute
lemma irreducible_right_evaluation
    (π : IrreducibleRepresentation (MaxTensor.Algebra (Algebra p q) (Algebra r k))) :
    ∃ t : unitInterval, ∀ f, π.representation (MaxTensor.includeRight (scalar r k f))=
        algebraMap ℂ _ (f t) := by
  exact irreducible_central_evaluation π
    (MaxTensor.includeRight.comp (scalar r k)) scalarRight_commute
lemma sectionMap_evaluation (s t : unitInterval)
    (x : MaxTensor.Algebra (Algebra p q) (Algebra r k)) :
    fiberMap (evaluation p q s) (evaluation r k t) x=sectionMap x (s,t) := by
  have hsec : Continuous (sectionMap (p:=p) (q:=q) (r:=r) (k:=k)) := continuous_starHom (A:=MaxTensor.Algebra (Algebra p q) (Algebra r k))
    (B:=C(Square,SquareFiber p q r k)) _
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (map_continuous (fiberMap (evaluation p q s) (evaluation r k t)))
      ((continuous_eval_const (s,t)).comp hsec)
  | ih x =>
    change fiberMap (evaluation p q s) (evaluation r k t) (MaxTensor.of x)=sectionMap (MaxTensor.of x) (s,t)
    suffices ∀ tensor : Algebra p q ⊗[ℂ] Algebra r k,
        fiberMap (evaluation p q s) (evaluation r k t)
          (MaxTensor.of (MaxTensor.rawEquiv tensor)) =
        sectionMap (MaxTensor.of (MaxTensor.rawEquiv tensor)) (s,t) from
      this (MaxTensor.rawEquiv.symm x)
    intro tensor
    induction tensor using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add,ContinuousMap.add_apply,hx,hy]
    | tmul a b =>
      change fiberMap (evaluation p q s) (evaluation r k t) (MaxTensor.of (a ⊗ₜ[ℂ] b)) =
        sectionMap (MaxTensor.of (a ⊗ₜ[ℂ] b)) (s,t)
      rw [fiberMap_tmul,MaxTensor.of_tmul,map_mul,ContinuousMap.mul_apply,
        sectionMap_left,sectionMap_right]; rfl

lemma irreducible_fiber_bound
    (π : IrreducibleRepresentation (MaxTensor.Algebra (Algebra p q) (Algebra r k))) :
    ∃ s t : unitInterval, ∀ x, ‖π.representation x‖ ≤ ‖sectionMap x (s,t)‖ := by
  obtain ⟨s,hs⟩ := irreducible_left_evaluation π
  obtain ⟨t,ht⟩ := irreducible_right_evaluation π
  have hkL : ∀ a, evaluation p q s a=0 → π.representation (MaxTensor.includeLeft a)=0 :=
    kills_evaluation_kernel (π.representation.comp MaxTensor.includeLeft) s hs
  have hkR : ∀ b, evaluation r k t b=0 → π.representation (MaxTensor.includeRight b)=0 :=
    kills_evaluation_kernel (π.representation.comp MaxTensor.includeRight) t ht
  have hb := representation_bound (evaluation p q s) (evaluation r k t) π.representation hkL hkR
  refine ⟨s,t,?_⟩
  intro x
  simpa only [sectionMap_evaluation] using hb x


theorem sectionMap_injective : Function.Injective (sectionMap (p:=p) (q:=q) (r:=r) (k:=k)) := by
  cases subsingleton_or_nontrivial (MaxTensor.Algebra (Algebra p q) (Algebra r k))
  · exact fun _ _ _ => Subsingleton.elim _ _
  intro x y h
  have hz : sectionMap (x-y)=0 := by rw [map_sub,h,sub_self]
  apply sub_eq_zero.mp
  apply irreducible_separate_zero
  intro π
  obtain ⟨s,t,hst⟩ := irreducible_fiber_bound π
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [hz,ContinuousMap.zero_apply,norm_zero] using hst (x-y)

end KirchbergRordam.PrimeTensorSections
namespace KirchbergRordam.ContinuousSectionLocality
section
variable {X E : Type*} [TopologicalSpace X] [instCompactSpaceX : CompactSpace X] [instT2SpaceX : T2Space X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
def weight (f : C(X,ℝ)) (g : C(X,E)) : C(X,E) :=
  ⟨fun x => f x • g x,f.continuous.smul g.continuous⟩
omit instCompactSpaceX instT2SpaceX in
@[simp] lemma weight_apply.{contextLevel1, contextLevel2}
    {X : Type contextLevel1}
    {E : Type contextLevel2}
    [TopologicalSpace X]
    [CompactSpace X]
    [T2Space X]
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (f : C(X,ℝ)) (g : C(X,E)) (x : X) :
    weight f g x=f x • g x := rfl


theorem mem_of_pointwise (S : Submodule ℝ C(X,E)) (hS : IsClosed (S : Set C(X,E)))
    (hw : ∀ (f : C(X,ℝ)) (g : C(X,E)), g∈S → weight f g∈S)
    (f : C(X,E)) (hf : ∀ x, ∃ g∈S, g x=f x) : f∈S := by
  classical
  change f ∈ (S : Set C(X,E))
  rw [← hS.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  choose g hg he using hf
  let U : X → Set X := fun x => {y | ‖g x y-f y‖<ε/2}
  have ho (x : X) : IsOpen (U x) :=
    isOpen_lt ((g x).continuous.sub f.continuous).norm continuous_const
  have hcover : Set.univ ⊆ ⋃ x, U x := by
    intro x _
    apply Set.mem_iUnion.mpr
    refine ⟨x,?_⟩
    change ‖g x x-f x‖<ε/2
    rw [he,sub_self,norm_zero]
    linarith
  obtain ⟨J,hJ⟩ := isCompact_univ.elim_finite_subcover U ho hcover
  have hc : Set.univ ⊆ ⋃ i : J, U i.val := by
    intro x hx
    obtain ⟨i,hiJ,hi⟩ := Set.mem_iUnion₂.mp (hJ hx)
    exact Set.mem_iUnion.mpr ⟨⟨i,hiJ⟩,hi⟩
  obtain ⟨ρ,hρ⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite
    isClosed_univ (fun i : J => U i.val) (fun i => ho i.val)
      (locallyFinite_of_finite _) hc
  let G : C(X,E) := ∑ i : J, weight (ρ i) (g i.val)
  have hGS : G∈S := S.sum_mem (fun i _ => hw (ρ i) (g i.val) (hg i.val))
  have hsum (x : X) : ∑ i : J, ρ i x=1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (x:=x) (Set.mem_univ x)
  have hn : ‖G-f‖≤ε/2 := by
    apply (ContinuousMap.norm_le _ (by linarith)).mpr
    intro x
    have heq : (G-f) x=∑ i : J, ρ i x • (g i.val x-f x) := by
      simp only [ContinuousMap.sub_apply,G,ContinuousMap.sum_apply,weight_apply,smul_sub,
        Finset.sum_sub_distrib,← Finset.sum_smul,hsum,one_smul]
    rw [heq]
    calc
      ‖∑ i : J, ρ i x • (g i.val x-f x)‖ ≤
          ∑ i : J, ‖ρ i x • (g i.val x-f x)‖ := norm_sum_le _ _
      _ ≤ ∑ i : J, ρ i x * (ε/2) := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul_of_nonneg (ρ.nonneg i x)]
        by_cases hi : ρ i x=0
        · simp [hi]
        apply mul_le_mul_of_nonneg_left _ (ρ.nonneg i x)
        exact (hρ i (subset_closure (show x∈Function.support (ρ i) from hi))).le
      _ = ε/2 := by rw [← Finset.sum_mul,hsum,one_mul]
  refine ⟨G,hGS,?_⟩
  rw [dist_comm,dist_eq_norm]
  exact hn.trans_lt (by linarith)
end
open scoped CStarAlgebra ComplexOrder
variable {X E : Type*} [TopologicalSpace X] [instCompactSpaceX : CompactSpace X] [instT2SpaceX : T2Space X] [CStarAlgebra E]
def scalarMap : C(X,ℂ) →⋆ₐ[ℂ] C(X,E) where
  toFun f := ⟨fun x => f x • 1,f.continuous.smul continuous_const⟩
  map_zero' := by apply ContinuousMap.ext; intro x; simp
  map_one' := by apply ContinuousMap.ext; intro x; simp
  map_add' f g := by apply ContinuousMap.ext; intro x; exact add_smul _ _ _
  map_mul' f g := by apply ContinuousMap.ext; intro x; change (f x * g x) • (1:E)=(f x • (1:E))*(g x • (1:E)); simp [smul_smul,mul_comm]
  commutes' z := by apply ContinuousMap.ext; intro x; exact (_root_.Algebra.algebraMap_eq_smul_one z).symm
  map_star' f := by apply ContinuousMap.ext; intro x; change star (f x) • (1:E)=star (f x • (1:E)); simp
omit instCompactSpaceX instT2SpaceX in
@[simp] lemma scalarMap_apply.{contextLevel1, contextLevel2}
    {X : Type contextLevel1}
    {E : Type contextLevel2}
    [TopologicalSpace X]
    [CompactSpace X]
    [T2Space X]
    [CStarAlgebra E]
    (f : C(X,ℂ)) (x : X) : scalarMap (E:=E) f x=f x • 1 := rfl

theorem mem_of_pointwise_star (S : StarSubalgebra ℂ C(X,E)) (hS : IsClosed (S : Set C(X,E)))
    (hs : ∀ f : C(X,ℂ), scalarMap f∈S) (f : C(X,E))
    (hf : ∀ x, ∃ g∈S, g x=f x) : f∈S := by
  apply mem_of_pointwise (S.toSubalgebra.toSubmodule.restrictScalars ℝ) hS _ f hf
  intro c g hg
  let z : C(X,ℂ) := ⟨fun x => (c x : ℂ),Complex.continuous_ofReal.comp c.continuous⟩
  have hh : scalarMap z * g∈S := S.mul_mem (hs z) hg
  have he : weight c g=scalarMap z * g := by
    apply ContinuousMap.ext
    intro x
    change c x • g x=((c x:ℂ) • (1:E))*g x
    rw [smul_mul_assoc,one_mul,Complex.coe_smul]
  rw [he]
  exact hh

abbrev Square := unitInterval×unitInterval
def firstCoord : C(Square,ℂ) := ⟨fun x => ((x.1:ℝ):ℂ),by fun_prop⟩
def secondCoord : C(Square,ℂ) := ⟨fun x => ((x.2:ℝ):ℂ),by fun_prop⟩


theorem scalars_of_coordinates (S : StarSubalgebra ℂ C(Square,E))
    (hS : IsClosed (S : Set C(Square,E)))
    (h₁ : scalarMap firstCoord∈S) (h₂ : scalarMap secondCoord∈S) :
    ∀ f : C(Square,ℂ), scalarMap f∈S := by
  let T := S.comap (scalarMap (X:=Square) (E:=E))
  have hT : IsClosed (T : Set C(Square,ℂ)) := hS.preimage (map_continuous scalarMap)
  have hsep : T.SeparatesPoints := by
    intro x y hxy
    by_cases h : x.1=y.1
    · have hh : x.2≠y.2 := fun he => hxy (Prod.ext h he)
      refine ⟨secondCoord,⟨secondCoord,h₂,rfl⟩,?_⟩
      intro he
      apply hh
      apply Subtype.ext
      exact Complex.ofReal_injective he
    · refine ⟨firstCoord,⟨firstCoord,h₁,rfl⟩,?_⟩
      intro he
      apply h
      apply Subtype.ext
      exact Complex.ofReal_injective he
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints T hsep
  have hh := StarSubalgebra.topologicalClosure_minimal (show T≤T from le_rfl) hT
  rw [htop] at hh
  intro f
  exact hh (show f∈(⊤ : StarSubalgebra ℂ C(Square,ℂ)) from trivial)
end KirchbergRordam.ContinuousSectionLocality
namespace KirchbergRordam.PrimeTensorSections
open scoped CStarAlgebra ComplexOrder TensorProduct
open PrimeDimensionDrop MatrixTensor ContinuousSectionLocality
variable {p q r k : ℕ}

lemma sectionMap_isometry : Isometry (sectionMap (p:=p) (q:=q) (r:=r) (k:=k)) :=
  NonUnitalStarAlgHom.isometry _ sectionMap_injective
def sectionRange : StarSubalgebra ℂ C(Square,SquareFiber p q r k) :=
  (sectionMap (p:=p) (q:=q) (r:=r) (k:=k)).range
lemma sectionRange_closed : IsClosed (sectionRange (p:=p) (q:=q) (r:=r) (k:=k) :
    Set C(Square,SquareFiber p q r k)) := sectionMap_isometry.isClosedEmbedding.isClosed_range

lemma sectionRange_scalar (f : C(Square,ℂ)) :
    scalarMap f∈sectionRange (p:=p) (q:=q) (r:=r) (k:=k) := by
  apply scalars_of_coordinates _ sectionRange_closed
  · refine ⟨MaxTensor.includeLeft (scalar p q ⟨fun t => ((t:ℝ):ℂ),by fun_prop⟩),?_⟩
    apply ContinuousMap.ext; intro x
    change sectionMap (p:=p) (q:=q) (r:=r) (k:=k) _ x = _
    rw [sectionMap_left]
    change MatrixTensor.leftMatrix (((x.1:ℝ):ℂ) • (1:Fiber p q))=((x.1:ℝ):ℂ) • (1:SquareFiber p q r k)
    rw [map_smul,map_one]
  · refine ⟨MaxTensor.includeRight (scalar r k ⟨fun t => ((t:ℝ):ℂ),by fun_prop⟩),?_⟩
    apply ContinuousMap.ext; intro x
    change sectionMap (p:=p) (q:=q) (r:=r) (k:=k) _ x = _
    rw [sectionMap_right]
    change MatrixTensor.rightMatrix (((x.2:ℝ):ℂ) • (1:Fiber r k))=((x.2:ℝ):ℂ) • (1:SquareFiber p q r k)
    rw [map_smul,map_one]


def fiberRange (x : Square) : StarSubalgebra ℂ (SquareFiber p q r k) :=
  (subKronecker (evaluation p q x.1).range (evaluation r k x.2).range).range

lemma sectionMap_raw (a : Algebra p q ⊗[ℂ] Algebra r k) (x : Square) :
    sectionMap (MaxTensor.of (MaxTensor.rawEquiv a)) x =
      subKronecker (evaluation p q x.1).range (evaluation r k x.2).range
        (TensorProduct.map (evaluation p q x.1).rangeRestrict.toLinearMap
          (evaluation r k x.2).rangeRestrict.toLinearMap a) := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add,ContinuousMap.add_apply,ha,hb]
  | tmul a b =>
    change sectionMap (MaxTensor.of (a ⊗ₜ[ℂ] b)) x = _
    rw [TensorProduct.map_tmul,sectionMap_tmul]; rfl

lemma fiberRange_lift (x : Square) (a : SquareFiber p q r k)
    (ha : a∈fiberRange (p:=p) (q:=q) (r:=r) (k:=k) x) :
    ∃ b : MaxTensor.Algebra (Algebra p q) (Algebra r k), sectionMap b x=a := by
  obtain ⟨c,hc⟩ := ha
  have hL : Function.Surjective (evaluation p q x.1).rangeRestrict := by
    rintro ⟨a,⟨b,hb⟩⟩
    exact ⟨b,Subtype.ext hb⟩
  have hR : Function.Surjective (evaluation r k x.2).rangeRestrict := by
    rintro ⟨a,⟨b,hb⟩⟩
    exact ⟨b,Subtype.ext hb⟩
  obtain ⟨d,hd⟩ := TensorProduct.map_surjective
    (g:=(evaluation p q x.1).rangeRestrict.toLinearMap)
    (g':=(evaluation r k x.2).rangeRestrict.toLinearMap) hL hR c
  exact ⟨MaxTensor.of (MaxTensor.rawEquiv d),by rw [sectionMap_raw,hd]; exact hc⟩


theorem mem_sectionRange_of_fibers (f : C(Square,SquareFiber p q r k))
    (hf : ∀ x, f x∈fiberRange (p:=p) (q:=q) (r:=r) (k:=k) x) :
    f∈sectionRange (p:=p) (q:=q) (r:=r) (k:=k) := by
  apply mem_of_pointwise_star _ sectionRange_closed sectionRange_scalar f
  intro x
  obtain ⟨b,hb⟩ := fiberRange_lift x (f x) (hf x)
  exact ⟨sectionMap b,⟨b,rfl⟩,hb⟩
end KirchbergRordam.PrimeTensorSections
namespace KirchbergRordam.PrimeDimensionDrop
open scoped CStarAlgebra ComplexOrder
open MatrixTensor
variable {p q : ℕ}

def leftRamp (a : Mat (Fin p)) : Algebra p q :=
  ⟨⟨fun t => ((1-(t:ℝ):ℝ):ℂ) • MatrixTensor.leftMatrix a,by fun_prop⟩,by
    apply (mem_iff _).mpr
    constructor
    · exact ⟨a,by simp⟩
    · exact ⟨0,by simp⟩⟩
def rightRamp (b : Mat (Fin q)) : Algebra p q :=
  ⟨⟨fun t => ((t:ℝ):ℂ) • MatrixTensor.rightMatrix b,by fun_prop⟩,by
    apply (mem_iff _).mpr
    constructor
    · exact ⟨0,by change MatrixTensor.leftMatrix (κ:=Fin q) (0 : Mat (Fin p)) = (0:ℂ) • MatrixTensor.rightMatrix b; rw [map_zero,zero_smul]⟩
    · exact ⟨b,by change MatrixTensor.rightMatrix (ι:=Fin p) b = (1:ℂ) • MatrixTensor.rightMatrix b; rw [one_smul]⟩⟩

lemma evaluation_zero_range : (evaluation p q 0).range=MatrixTensor.leftMatrix.range := by
  ext a
  constructor
  · rintro ⟨f,rfl⟩
    exact f.property.1
  · rintro ⟨b,rfl⟩
    exact ⟨leftRamp b,by simp [evaluation_apply,leftRamp]⟩
lemma evaluation_one_range : (evaluation p q 1).range=MatrixTensor.rightMatrix.range := by
  ext a
  constructor
  · rintro ⟨f,rfl⟩
    exact f.property.2
  · rintro ⟨b,rfl⟩
    exact ⟨rightRamp b,by change (1:ℂ) • MatrixTensor.rightMatrix (ι:=Fin p) b=MatrixTensor.rightMatrix b; rw [one_smul]⟩

def interiorRamp (t : unitInterval) (a : Fiber p q) : Algebra p q :=
  ⟨⟨fun s => (((s:ℝ)*(1-s)/(t*(1-t)):ℝ):ℂ) • a,by fun_prop⟩,by
    apply (mem_iff _).mpr
    constructor <;> refine ⟨0,?_⟩ <;> simp⟩
lemma evaluation_interior_surjective (t : unitInterval) (h0 : t≠0) (h1 : t≠1) :
    Function.Surjective (evaluation p q t) := by
  intro a
  have ht0 : (t:ℝ)≠0 := by intro h; apply h0; exact Subtype.ext h
  have ht1 : 1-(t:ℝ)≠0 := by intro h; apply h1; apply Subtype.ext; change (t:ℝ)=1; linarith
  refine ⟨interiorRamp t a,?_⟩
  change ((((t:ℝ)*(1-t)/(t*(1-t)):ℝ):ℂ) • a)=a
  rw [div_self (mul_ne_zero ht0 ht1)]
  simp
lemma evaluation_interior_range (t : unitInterval) (h0 : t≠0) (h1 : t≠1) :
    (evaluation p q t).range=⊤ := by
  ext a
  exact ⟨fun _ => trivial,fun _ => evaluation_interior_surjective t h0 h1 a⟩
end KirchbergRordam.PrimeDimensionDrop
namespace KirchbergRordam.MatrixTensor
open scoped TensorProduct CStarAlgebra ComplexOrder Matrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
def tensorRange (S : StarSubalgebra ℂ (Mat ι)) (T : StarSubalgebra ℂ (Mat κ)) :
    StarSubalgebra ℂ (Mat (ι×κ)) := (subKronecker S T).range
lemma tensorRange_tmul (S : StarSubalgebra ℂ (Mat ι)) (T : StarSubalgebra ℂ (Mat κ))
    {a : Mat ι} {b : Mat κ} (ha : a∈S) (hb : b∈T) :
    MatrixTensor.leftMatrix a*MatrixTensor.rightMatrix b∈tensorRange S T :=
  ⟨(⟨a,ha⟩:S) ⊗ₜ[ℂ] (⟨b,hb⟩:T),rfl⟩
lemma tensorRange_left (S : StarSubalgebra ℂ (Mat ι)) (T : StarSubalgebra ℂ (Mat κ))
    {a : Mat ι} (ha : a∈S) : MatrixTensor.leftMatrix a∈tensorRange S T := by
  simpa only [map_one,mul_one] using tensorRange_tmul S T ha (T.one_mem)
lemma tensorRange_right (S : StarSubalgebra ℂ (Mat ι)) (T : StarSubalgebra ℂ (Mat κ))
    {b : Mat κ} (hb : b∈T) : MatrixTensor.rightMatrix b∈tensorRange S T := by
  simpa only [map_one,one_mul] using tensorRange_tmul S T (S.one_mem) hb
lemma tensorRange_mono {S₁ S₂ : StarSubalgebra ℂ (Mat ι)}
    {T₁ T₂ : StarSubalgebra ℂ (Mat κ)} (hS : S₁≤S₂) (hT : T₁≤T₂) :
    tensorRange S₁ T₁ ≤ tensorRange S₂ T₂ := by
  rintro a ⟨b,rfl⟩
  change subKronecker S₁ T₁ b ∈ (tensorRange S₂ T₂).toSubalgebra
  induction b using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add]; exact (tensorRange S₂ T₂).add_mem hx hy
  | tmul a b => exact tensorRange_tmul S₂ T₂ (hS a.property) (hT b.property)
lemma matrixUnit_kronecker (i j : ι) (k l : κ) :
    MatrixTensor.leftMatrix (unit i j)*MatrixTensor.rightMatrix (unit k l)=unit (i,k) (j,l) := by
  rw [legs_product]
  ext a b
  change (Matrix.single i j (1:ℂ)) a.1 b.1 * (Matrix.single k l (1:ℂ)) a.2 b.2 =
    (Matrix.single (i,k) (j,l) (1:ℂ)) a b
  rcases a with ⟨a,c⟩; rcases b with ⟨b,d⟩
  simp only [Matrix.single_apply,Prod.mk.injEq]
  split_ifs <;> simp_all
lemma tensorRange_top_top : tensorRange (⊤ : StarSubalgebra ℂ (Mat ι))
    (⊤ : StarSubalgebra ℂ (Mat κ))=⊤ := by
  apply top_unique
  intro a _
  rw [←decompose a]
  change _∈(tensorRange (⊤ : StarSubalgebra ℂ (Mat ι)) (⊤ : StarSubalgebra ℂ (Mat κ))).toSubalgebra
  apply Subalgebra.sum_mem
  intro ij _
  apply Subalgebra.smul_mem
  rw [←matrixUnit_kronecker]
  exact tensorRange_tmul _ _ trivial trivial
end KirchbergRordam.MatrixTensor
end

end OAI
