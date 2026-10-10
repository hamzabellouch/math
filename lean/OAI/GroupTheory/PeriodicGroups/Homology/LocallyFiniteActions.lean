import Mathlib
import OAI.GroupTheory.PeriodicGroups.Frames.ElementaryFrames

namespace OAI

noncomputable section

namespace SourceBurnside.Stability
open Classical
namespace LocallyFinite

lemma finite (G : Type*) [Group G] [Finite G] : LocallyFinite G := by
  intro s
  exact ⟨⊤,fun _ _ => Subgroup.mem_top _,inferInstance⟩

lemma of_injective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (hH : LocallyFinite H) : LocallyFinite G := by
  intro s
  obtain ⟨K,hK,hfin⟩ := hH (s.image f)
  have := hfin
  refine ⟨K.comap f,fun g hg => hK _ (Finset.mem_image_of_mem f hg),?_⟩
  exact Finite.of_injective (fun g : K.comap f => (⟨f g.val,g.property⟩ : K))
    (fun a b h => Subtype.ext (hf (congrArg Subtype.val h)))

lemma of_surjective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hG : LocallyFinite G) : LocallyFinite H := by
  intro s
  let lift : H → G := fun h => (hf h).choose
  have hl : ∀h, f (lift h) = h := fun h => (hf h).choose_spec
  obtain ⟨K,hK,hfin⟩ := hG (s.image lift)
  have := hfin
  refine ⟨K.map f,fun h hh => ?_,?_⟩
  · exact ⟨lift h,hK _ (Finset.mem_image_of_mem lift hh),hl h⟩
  · exact Finite.of_surjective (fun g : K => (⟨f g.val,⟨g.val,g.property,rfl⟩⟩ : K.map f)) (by
      rintro ⟨h,g,hg,rfl⟩
      exact ⟨⟨g,hg⟩,rfl⟩)

lemma commTorsion (G : Type*) [CommGroup G] (hG : IsMulTorsion G) : LocallyFinite G := by
  intro s
  let K := Subgroup.closure (s : Set G)
  have hfg : K.FG := ⟨s,rfl⟩
  have : Group.FG K := (Group.fg_iff_subgroup_fg K).mpr hfg
  refine ⟨K,fun g hg => Subgroup.subset_closure hg,?_⟩
  apply CommGroup.finite_of_fg_isMulTorsion K
  intro g
  obtain ⟨n,hn,he⟩ := (hG g.val).exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,Subtype.ext he⟩

lemma vector2 (A : Type*) [AddCommGroup A] [Module (ZMod 2) A] :
    LocallyFinite (Multiplicative A) := by
  apply commTorsion
  intro a
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨2,by decide,?_⟩
  change (2 : ℕ) • a.toAdd = 0
  have h : ((2 : ℕ) : ZMod 2) • a.toAdd = 0 := by
    rw [show ((2 : ℕ) : ZMod 2) = 0 from rfl,zero_smul]
  exact (Nat.cast_smul_eq_nsmul (ZMod 2) (2 : ℕ) a.toAdd).symm.trans h

end LocallyFinite
end SourceBurnside.Stability

namespace SourceBurnside.Stability.UnorderedStabilizer
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators MatrixK1
open scoped Pointwise
variable {R ι κ : Type} [Ring R] [Algebra (ZMod 2) R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (ε : R →ₐ[ZMod 2] ZMod 2)

abbrev rightVertex (j : κ) : ColumnFrames.Vertex (ι := ι ⊕ κ) ε :=
  ColumnFrames.standard ε (Sum.inr j)

lemma rightVertex_injective : Function.Injective (rightVertex (ι := ι) (κ := κ) ε) :=
  (ColumnFrames.standard_injective ε).comp Sum.inr_injective

abbrev K : Subgroup (E (R := R) (ι := ι ⊕ κ)) :=
  MulAction.stabilizer _ (Set.range (rightVertex (ι := ι) (κ := κ) ε))

def rightEquiv : κ ≃ Set.range (rightVertex (ι := ι) (κ := κ) ε) :=
  Equiv.ofInjective _ (rightVertex_injective ε)

def perm : K (ι := ι) (κ := κ) ε →* Equiv.Perm κ where
  toFun U := (rightEquiv (ι := ι) (κ := κ) ε).trans
    ((MulAction.toPermHom (K (ι := ι) (κ := κ) ε)
      (Set.range (rightVertex (ι := ι) (κ := κ) ε))) U) |>.trans (rightEquiv (ι := ι) (κ := κ) ε).symm
  map_one' := by ext j; simp
  map_mul' U V := by ext j; simp [Equiv.trans_apply, mul_smul]

lemma perm_spec (U : K (ι := ι) (κ := κ) ε) (j : κ) :
    U.val.val • rightVertex (ι := ι) ε j = rightVertex (ι := ι) ε (perm ε U j) := by
  change (U • (rightEquiv (ι := ι) (κ := κ) ε j)).val = _
  exact ((congrArg Subtype.val ((rightEquiv (ι := ι) (κ := κ) ε).apply_symm_apply (U • rightEquiv (ι := ι) (κ := κ) ε j)))).symm

def permRight : Equiv.Perm κ →* (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ :=
  permutation.comp (Equiv.Perm.sumCongrHom ι κ |>.comp ((1 : Equiv.Perm κ →* Equiv.Perm ι).prod (MonoidHom.id _)))

omit [Algebra (ZMod 2) R] in
lemma permRight_eq (p : Equiv.Perm κ) :
    permRight (R := R) (ι := ι) p = permutation (Equiv.sumCongr (Equiv.refl ι) p) := rfl

lemma permRight_smul (p : Equiv.Perm κ) (j : κ) :
    permRight (R := R) (ι := ι) p • rightVertex (ι := ι) ε j = rightVertex (ι := ι) ε (p j) := by
  apply Subtype.ext
  change permutation (Equiv.sumCongr (Equiv.refl ι) p) •
      (Pi.single (Sum.inr j) 1 : ι ⊕ κ → R) = Pi.single (Sum.inr (p j)) 1
  exact permutation_smul_single _ _

def fixedPart (U : K (ι := ι) (κ := κ) ε) : rightFixer (ι := ι) (κ := κ) (R := R) :=
  ⟨U.val.val * permRight ((perm ε U)⁻¹), by
    simp only [rightFixer,Subgroup.mem_iInf,MulAction.mem_stabilizer_iff]
    intro j
    have h : (U.val.val * permRight ((perm ε U)⁻¹)) • rightVertex (ι := ι) ε j = rightVertex (ι := ι) ε j := by
      rw [mul_smul,permRight_smul,perm_spec]
      simp
    exact congrArg Subtype.val h⟩

def topBlock (U : K (ι := ι) (κ := κ) ε) : (Matrix ι ι R)ˣ :=
  rightProjection (fixedPart ε U)

lemma topBlock_entry (U : K (ι := ι) (κ := κ) ε) (i j : ι) :
    (topBlock ε U).val i j = U.val.val.val (Sum.inl i) (Sum.inl j) := by
  change (U.val.val.val * (permRight (R := R) (ι := ι) ((perm ε U)⁻¹)).val) (Sum.inl i) (Sum.inl j) = _
  rw [permRight_eq,mul_permutation]
  rfl

lemma shape (U : K (ι := ι) (κ := κ) ε) :
    U.val.val.val = Matrix.fromBlocks (topBlock ε U).val 0
      (U.val.val.val.submatrix Sum.inr Sum.inl) (permutation (perm ε U)).val := by
  ext i j
  cases j with
  | inl j => cases i with
    | inl i => exact (topBlock_entry ε U i j).symm
    | inr i => rfl
  | inr j =>
    have h := congrArg (fun v : ColumnFrames.Vertex (ι := ι ⊕ κ) ε => v.val i) (perm_spec ε U j)
    change Matrix.mulVec U.val.val.val (Pi.single (Sum.inr j) 1) i =
      (Pi.single (Sum.inr (perm ε U j)) (1 : R) : ι ⊕ κ → R) i at h
    rw [Matrix.mulVec_single_one] at h
    cases i with
    | inl i => simpa [Matrix.fromBlocks,Pi.single_apply] using h
    | inr i => simpa [Matrix.fromBlocks,Pi.single_apply,permutation_entry,eq_comm,Equiv.eq_symm_apply] using h

def projectionGL : K (ι := ι) (κ := κ) ε →* (Matrix ι ι R)ˣ where
  toFun := topBlock ε
  map_one' := by
    apply Units.ext
    ext i j
    simpa [Matrix.one_apply] using topBlock_entry ε 1 i j
  map_mul' U V := by
    apply Units.ext
    ext i j
    rw [topBlock_entry]
    change (U.val.val.val*V.val.val.val) (Sum.inl i) (Sum.inl j) = _
    rw [shape ε U,shape ε V,Matrix.fromBlocks_multiply]
    simp

variable (hI : MatrixNilKernel ε.toRingHom) (hι : 5 ≤ Fintype.card ι)

include hI hι in
lemma topBlock_mem (U : K (ι := ι) (κ := κ) ε) : topBlock ε U ∈ E := by
  apply (block_mem_iff (κ := κ) ε hI hι _).mp
  have hf : (fixedPart ε U).val ∈ E := E.mul_mem U.val.property
    (by exact permutation_mem _)
  rw [rightFixer_decomposition] at hf
  exact (E.mul_mem_cancel_right (rectangle_mem _)).mp hf

def projection : K (ι := ι) (κ := κ) ε →* E (R := R) (ι := ι) :=
  (projectionGL ε).codRestrict E (topBlock_mem ε hI hι)

def quotientMap : K (ι := ι) (κ := κ) ε →* E (R := R) (ι := ι) × Equiv.Perm κ :=
  (projection ε hI hι).prod (perm ε)

lemma section_mem (A : E (R := R) (ι := ι)) (p : Equiv.Perm κ) :
    (⟨blockInclusion A.val * permRight p,
      E.mul_mem (block_mem A.property) (permutation_mem _)⟩ : E (R := R) (ι := ι ⊕ κ)) ∈ K ε := by
  rw [MulAction.mem_stabilizer_iff]
  ext v
  constructor
  · rintro ⟨w,⟨j,rfl⟩,rfl⟩
    have he : (blockInclusion A.val * permRight p) • rightVertex (ι := ι) ε j = rightVertex (ι := ι) ε (p j) := by
      rw [mul_smul,permRight_smul]
      apply Subtype.ext
      exact block_smul_right A.val (p j)
    exact ⟨p j,he.symm⟩
  · rintro ⟨j,rfl⟩
    refine ⟨rightVertex ε (p⁻¹ j),⟨p⁻¹ j,rfl⟩,?_⟩
    change (blockInclusion A.val * permRight p) • rightVertex ε (p⁻¹ j) = _
    rw [mul_smul,permRight_smul]
    change blockInclusion A.val • rightVertex (ι := ι) ε (p (p.symm j)) = _
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    exact block_smul_right A.val j

def sectionElement (A : E (R := R) (ι := ι)) (p : Equiv.Perm κ) : K (ι := ι) (κ := κ) ε :=
  ⟨⟨blockInclusion A.val * permRight p,
      E.mul_mem (block_mem A.property) (permutation_mem _)⟩,section_mem ε A p⟩

lemma section_perm (A : E (R := R) (ι := ι)) (p : Equiv.Perm κ) :
    perm ε (sectionElement ε A p) = p := by
  ext j
  apply rightVertex_injective (ι := ι) (κ := κ) ε
  rw [←perm_spec]
  change (blockInclusion A.val * permRight p) • rightVertex ε j = _
  rw [mul_smul,permRight_smul]
  apply Subtype.ext
  exact block_smul_right A.val (p j)

lemma section_topBlock (A : E (R := R) (ι := ι)) (p : Equiv.Perm κ) :
    topBlock ε (sectionElement ε A p) = A.val := by
  apply Units.ext
  ext i j
  rw [topBlock_entry]
  change (blockInclusion A.val * permRight p).val (Sum.inl i) (Sum.inl j) = _
  rw [Units.val_mul,permRight_eq,mul_permutation]
  rfl

lemma quotientMap_surjective : Function.Surjective (quotientMap (κ := κ) ε hI hι) := by
  rintro ⟨A,p⟩
  refine ⟨sectionElement ε A p,?_⟩
  apply Prod.ext
  · exact Subtype.ext (section_topBlock ε A p)
  · exact section_perm ε A p

lemma kernel_shape (U : (quotientMap (κ := κ) ε hI hι).ker) :
    U.val.val.val.val = Matrix.fromBlocks 1 0
      (U.val.val.val.val.submatrix Sum.inr Sum.inl) 1 := by
  have h := MonoidHom.mem_ker.mp U.property
  have ha : topBlock ε U.val = 1 := congrArg (fun x : E (R := R) (ι := ι) × Equiv.Perm κ => x.1.val) h
  have hp : perm ε U.val = 1 := congrArg Prod.snd h
  rw [shape ε U.val,ha,hp,map_one]
  rfl

def strip : (quotientMap (κ := κ) ε hI hι).ker →* Multiplicative (Matrix κ ι R) where
  toFun U := Multiplicative.ofAdd (U.val.val.val.val.submatrix Sum.inr Sum.inl)
  map_one' := by
    apply (Multiplicative.toAdd : Multiplicative (Matrix κ ι R) ≃ Matrix κ ι R).injective
    ext i j
    simp
  map_mul' U V := by
    apply (Multiplicative.toAdd : Multiplicative (Matrix κ ι R) ≃ Matrix κ ι R).injective
    ext i j
    change (U.val.val.val.val * V.val.val.val.val) (Sum.inr i) (Sum.inl j) = _
    rw [kernel_shape ε hI hι U,kernel_shape ε hI hι V,Matrix.fromBlocks_multiply]
    simp

lemma strip_injective : Function.Injective (strip (κ := κ) ε hI hι) := by
  intro U V h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rw [kernel_shape ε hI hι U,kernel_shape ε hI hι V]
  exact congrArg (fun B => Matrix.fromBlocks (1 : Matrix ι ι R) 0 B (1 : Matrix κ κ R))
    (congrArg Multiplicative.toAdd h)

lemma kernel_locallyFinite : LocallyFinite (quotientMap (κ := κ) ε hI hι).ker :=
  LocallyFinite.of_injective _ (strip_injective ε hI hι) (LocallyFinite.vector2 _)

end SourceBurnside.Stability.UnorderedStabilizer

namespace SourceBurnside.Stability.Frames
open Classical Module
variable {V : Type} [LinearOrder V]

lemma labelMap_basis_congr (f g : V → V) (s : Finset V) (h : ∀v∈s,f v=g v) :
    labelMap f (basis s) = labelMap g (basis s) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert v s hv ih =>
    obtain ⟨c,hc,he⟩ := basis_insert_inverse v s hv
    rw [he,map_smul,map_smul,map_mul,map_mul,labelMap_vertex,labelMap_vertex,
      h v (Finset.mem_insert_self _ _),ih (fun w hw => h w (Finset.mem_insert_of_mem hw))]

lemma labelMap_basis_fixed (f : V → V) (s : Finset V) (h : ∀v∈s,f v=v) :
    labelMap f (basis s) = basis s := by
  rw [labelMap_basis_congr f id s h,labelMap_id]
  rfl

lemma labelMap_basis_swap (f : V → V) (s : Finset V) (v w : V)
    (hv : v∉s) (hw : w∉s) (hvw : v≠w) (hfv : f v=w) (hfw : f w=v)
    (hs : ∀x∈s,f x=x) :
    labelMap f (basis (insert v (insert w s))) = -basis (insert v (insert w s)) := by
  obtain ⟨c,hc,he⟩ := basis_insert_inverse v (insert w s) (by simp [hv,hvw])
  obtain ⟨d,hd,hde⟩ := basis_insert_inverse w s hw
  rw [he,hde,map_smul,map_mul,labelMap_vertex,hfv,map_smul,map_mul,labelMap_vertex,hfw,
    labelMap_basis_fixed f s hs]
  have hanti := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap
    (R := ℚ) (Finsupp.single w (1 : ℚ)) (Finsupp.single v (1 : ℚ)))
  change vertex V w * vertex V v = -(vertex V v * vertex V w) at hanti
  simp only [mul_smul_comm,←mul_assoc,hanti,neg_mul,smul_neg]

lemma labelMap_basis_transposition (f : V → V) (s : Finset V) (v w : V)
    (hv : v ∈ s) (hw : w ∈ s) (hvw : v≠w) (hfv : f v=w) (hfw : f w=v)
    (hs : ∀x∈s, x≠v → x≠w → f x=x) : labelMap f (basis s) = -basis s := by
  let t := (s.erase v).erase w
  have he : insert v (insert w t) = s := by
    ext x
    simp only [t,Finset.mem_insert,Finset.mem_erase]
    by_cases hxv : x=v <;> by_cases hxw : x=w <;> simp_all
  rw [←he]
  apply labelMap_basis_swap f t v w
  · simp [t]
  · simp [t]
  · exact hvw
  · exact hfv
  · exact hfw
  · intro x hx
    simp only [t,Finset.mem_erase] at hx
    exact hs x hx.2.2 hx.2.1 hx.1

end SourceBurnside.Stability.Frames

namespace SourceBurnside.Stability
open Classical CategoryTheory Representation Rep Module
namespace MonomialInduction
variable {G X : Type} [Group G] [MulAction G X] (x₀ : X)

abbrev charRep (χ : (MulAction.stabilizer G x₀) →* ℚˣ) : Rep ℚ (MulAction.stabilizer G x₀) := Rep.of (k := ℚ) (X := ℚ)
  { toFun s := (χ s).val • LinearMap.id
    map_one' := by ext; simp
    map_mul' s t := by ext; simp [mul_smul,mul_comm] }

@[simp] lemma charRep_apply (χ : (MulAction.stabilizer G x₀) →* ℚˣ) (s : (MulAction.stabilizer G x₀)) (a : ℚ) :
    (charRep x₀ χ).ρ s a = (χ s).val * a := rfl

lemma ind_relation (A : Rep ℚ (MulAction.stabilizer G x₀)) (s : (MulAction.stabilizer G x₀)) (g : G) (a : A) :
    IndV.mk (MulAction.stabilizer G x₀).subtype A.ρ (s.val*g) (A.ρ s a) = IndV.mk (MulAction.stabilizer G x₀).subtype A.ρ g a := by
  change Coinvariants.mk _ (MonoidAlgebra.single (s.val*g) (1 : ℚ) ⊗ₜ[ℚ] A.ρ s a) =
    Coinvariants.mk _ (MonoidAlgebra.single g (1 : ℚ) ⊗ₜ[ℚ] a)
  simpa using Coinvariants.mk_self_apply
    (Representation.tprod ((Representation.leftRegular ℚ G).comp (MulAction.stabilizer G x₀).subtype) A.ρ) s
    (MonoidAlgebra.single g (1 : ℚ) ⊗ₜ[ℚ] a)

variable (A : Rep.{0} ℚ G) (b : Basis X ℚ A) (χ : (MulAction.stabilizer G x₀) →* ℚˣ)
variable (hχ : ∀s : (MulAction.stabilizer G x₀), A.ρ s.val (b x₀) = ((χ s).val : ℚ) • b x₀)

def basisSeed (χ : (MulAction.stabilizer G x₀) →* ℚˣ)
    (hχ : ∀s : (MulAction.stabilizer G x₀), A.ρ s.val (b x₀) = ((χ s).val : ℚ) • b x₀) :
    charRep x₀ χ ⟶ Rep.res (MulAction.stabilizer G x₀).subtype A := by
  refine Rep.ofHom { toLinearMap := LinearMap.toSpanSingleton ℚ A (b x₀), isIntertwining' := ?_ }
  intro s
  apply LinearMap.ext
  intro a
  change ((χ s).val*a) • b x₀ = A.ρ s.val (a • b x₀)
  rw [map_smul,hχ,mul_smul,smul_comm]

def induced : Rep.ind (MulAction.stabilizer G x₀).subtype (charRep x₀ χ) ⟶ A :=
  (Rep.indResHomEquiv (MulAction.stabilizer G x₀).subtype _ A).symm (basisSeed x₀ A b χ hχ)

lemma induced_mk (g : G) (a : ℚ) :
    (induced x₀ A b χ hχ).hom (IndV.mk (MulAction.stabilizer G x₀).subtype (charRep x₀ χ).ρ g a) =
      a • A.ρ g⁻¹ (b x₀) := by
  simp [induced,Rep.indResHomEquiv,basisSeed]

variable (ht : ∀x : X, ∃g : G, g • x₀ = x)
variable (hm : ∀(g : G) (x : X), ∃c : ℚˣ, A.ρ g (b x) = c.val • b (g • x))

def transporter (x : X) : G := (ht x).choose
lemma transporter_spec (x : X) : transporter x₀ ht x • x₀ = x := (ht x).choose_spec

def coefficient (x : X) : ℚˣ := (hm (transporter x₀ ht x) x₀).choose

def orbitBasis : Basis X ℚ A := b.unitsSMul (coefficient x₀ A b ht hm)

lemma orbitBasis_eq (x : X) : orbitBasis x₀ A b ht hm x = A.ρ (transporter x₀ ht x) (b x₀) := by
  rw [orbitBasis,Basis.unitsSMul_apply]
  have h := (hm (transporter x₀ ht x) x₀).choose_spec
  change A.ρ (transporter x₀ ht x) (b x₀) = (coefficient x₀ A b ht hm x).val • b (transporter x₀ ht x • x₀) at h
  rw [transporter_spec] at h
  exact h.symm

def inverseLinear : A →ₗ[ℚ] Rep.ind (MulAction.stabilizer G x₀).subtype (charRep x₀ χ) :=
  (orbitBasis x₀ A b ht hm).constr ℚ
    (fun x => IndV.mk (MulAction.stabilizer G x₀).subtype (charRep x₀ χ).ρ (transporter x₀ ht x)⁻¹ 1)

lemma inverseLinear_basis (x : X) :
    inverseLinear x₀ A b χ ht hm (orbitBasis x₀ A b ht hm x) =
      IndV.mk (MulAction.stabilizer G x₀).subtype (charRep x₀ χ).ρ (transporter x₀ ht x)⁻¹ 1 := by
  exact Basis.constr_basis _ _ _ _

lemma induced_inverse :
    (induced x₀ A b χ hχ).hom.toLinearMap.comp (inverseLinear x₀ A b χ ht hm) = LinearMap.id := by
  apply (orbitBasis x₀ A b ht hm).ext
  intro x
  change (induced x₀ A b χ hχ).hom (inverseLinear x₀ A b χ ht hm (orbitBasis x₀ A b ht hm x)) = orbitBasis x₀ A b ht hm x
  rw [inverseLinear_basis,induced_mk,inv_inv,one_smul]
  exact (orbitBasis_eq x₀ A b ht hm x).symm

def residual (g : G) : MulAction.stabilizer G x₀ :=
  ⟨(transporter x₀ ht (g⁻¹ • x₀))⁻¹*g⁻¹,by
    rw [MulAction.mem_stabilizer_iff,mul_smul]
    exact (congrArg ((transporter x₀ ht (g⁻¹ • x₀))⁻¹ • ·) (transporter_spec x₀ ht (g⁻¹ • x₀))).symm.trans (inv_smul_smul _ _)⟩

include hχ in
lemma action_residual (g : G) :
    A.ρ g⁻¹ (b x₀) = ((χ (residual x₀ ht g)).val : ℚ) • orbitBasis x₀ A b ht hm (g⁻¹ • x₀) := by
  rw [orbitBasis_eq]
  have he : g⁻¹ = transporter x₀ ht (g⁻¹ • x₀) * (residual x₀ ht g).val := by
    simp [residual]
  conv_lhs => rw [he]
  rw [map_mul]
  change A.ρ (transporter x₀ ht (g⁻¹ • x₀)) (A.ρ (residual x₀ ht g).val (b x₀)) = _
  rw [hχ,map_smul]

lemma inverse_induced :
    (inverseLinear x₀ A b χ ht hm).comp (induced x₀ A b χ hχ).hom.toLinearMap = LinearMap.id := by
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro a
  change inverseLinear x₀ A b χ ht hm ((induced x₀ A b χ hχ).hom (IndV.mk _ _ g a)) = IndV.mk _ _ g a
  rw [induced_mk,action_residual x₀ A b χ hχ ht hm,map_smul,map_smul,inverseLinear_basis]
  have he := ind_relation x₀ (charRep x₀ χ) (residual x₀ ht g) g 1
  change IndV.mk (MulAction.stabilizer G x₀).subtype (charRep x₀ χ).ρ
    ((residual x₀ ht g).val*g) ((χ (residual x₀ ht g)).val*1) = _ at he
  simp only [mul_one,residual,mul_assoc,inv_mul_cancel,mul_one] at he
  have hs : ((χ (residual x₀ ht g)).val : ℚ) • IndV.mk (MulAction.stabilizer G x₀).subtype
      (charRep x₀ χ).ρ (transporter x₀ ht (g⁻¹ • x₀))⁻¹ 1 =
        IndV.mk (MulAction.stabilizer G x₀).subtype (charRep x₀ χ).ρ g 1 := by
    rw [←map_smul]
    simpa only [residual,smul_eq_mul,mul_one] using he
  rw [hs,←map_smul]
  simp

include ht hm in
lemma induced_isIso : IsIso (induced x₀ A b χ hχ) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have hl : Function.LeftInverse (inverseLinear x₀ A b χ ht hm) (induced x₀ A b χ hχ).hom :=
    fun a => congrArg (fun f : Rep.ind (MulAction.stabilizer G x₀).subtype (charRep x₀ χ) →ₗ[ℚ] _ => f a)
      (inverse_induced x₀ A b χ hχ ht hm)
  have hr : Function.RightInverse (inverseLinear x₀ A b χ ht hm) (induced x₀ A b χ hχ).hom :=
    fun a => congrArg (fun f : A →ₗ[ℚ] A => f a) (induced_inverse x₀ A b χ hχ ht hm)
  exact ⟨hl.injective,hr.surjective⟩

end MonomialInduction
end SourceBurnside.Stability

namespace SourceBurnside.Stability.MonomialInduction
open Classical CategoryTheory Module
variable {G X : Type} [Group G] [MulAction G X]
variable (x₀ : X) (A : Rep.{0} ℚ G) (b : Basis X ℚ A)
variable (hm : ∀(g : G) (x : X), ∃c : ℚˣ, A.ρ g (b x) = c.val • b (g • x))

def scalar (s : MulAction.stabilizer G x₀) : ℚˣ := (hm s.val x₀).choose

lemma scalar_spec (s : MulAction.stabilizer G x₀) :
    A.ρ s.val (b x₀) = (scalar x₀ A b hm s).val • b x₀ := by
  have h := (hm s.val x₀).choose_spec
  change A.ρ s.val (b x₀) = (scalar x₀ A b hm s).val • b (s.val • x₀) at h
  rwa [s.property] at h

omit [MulAction G X] in
lemma smul_basis_injective : Function.Injective (fun c : ℚ => c • b x₀) := by
  intro c d h
  have he := congrArg (fun v : A => b.repr v x₀) h
  simpa using he

def character : MulAction.stabilizer G x₀ →* ℚˣ where
  toFun := scalar x₀ A b hm
  map_one' := by
    apply Units.ext
    apply smul_basis_injective x₀ A b
    dsimp only
    rw [←scalar_spec]
    change A.ρ 1 (b x₀) = (1 : ℚ) • b x₀
    simp
  map_mul' s t := by
    apply Units.ext
    apply smul_basis_injective x₀ A b
    dsimp only
    rw [←scalar_spec]
    change A.ρ (s.val*t.val) (b x₀) = ((scalar x₀ A b hm s).val*(scalar x₀ A b hm t).val) • b x₀
    rw [map_mul]
    change A.ρ s.val (A.ρ t.val (b x₀)) = _
    rw [scalar_spec,map_smul,scalar_spec,mul_smul,smul_comm]

lemma character_spec (s : MulAction.stabilizer G x₀) :
    A.ρ s.val (b x₀) = ((character x₀ A b hm s).val : ℚ) • b x₀ := scalar_spec x₀ A b hm s

lemma character_eq_one (s : MulAction.stabilizer G x₀)
    (hs : A.ρ s.val (b x₀) = b x₀) : character x₀ A b hm s = 1 := by
  apply Units.ext
  apply smul_basis_injective x₀ A b
  dsimp only
  rw [←character_spec,hs,Units.val_one,one_smul]

lemma character_eq_neg_one (s : MulAction.stabilizer G x₀)
    (hs : A.ρ s.val (b x₀) = -b x₀) : character x₀ A b hm s = -1 := by
  apply Units.ext
  apply smul_basis_injective x₀ A b
  dsimp only
  rw [←character_spec,hs]
  simp

end SourceBurnside.Stability.MonomialInduction

namespace SourceBurnside.Stability
open Classical CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace ShapiroMap
variable {G : Type} [Group G] (S : Subgroup G)

def resolution : ProjectiveResolution (Rep.trivial ℚ S ℚ) :=
  (Rep.resFunctor S.subtype).mapProjectiveResolution (Rep.barResolution ℚ G)

lemma comparison_π : (BarMap.chain S.subtype).f 0 ≫ (resolution S).π.f 0 =
    (Rep.barResolution ℚ S).π.f 0 ≫ 𝟙 _ := by
  apply Rep.free_ext
  intro x
  change ((Rep.barResolution ℚ G).π.f 0).hom
    ((BarMap.component S.subtype 0).hom (single x (.single 1 1))) =
    ((Rep.barResolution ℚ S).π.f 0).hom (single x (.single 1 1))
  rw [BarMap.component_single,BarMap.augmentation_single,BarMap.augmentation_single]

def comparisonTensor (A : Rep ℚ S) :
    (Rep.barComplex ℚ S).coinvariantsTensorObj A ⟶ (resolution S).complex.coinvariantsTensorObj A :=
  (((coinvariantsTensor ℚ S).obj A).mapHomologicalComplex (ComplexShape.down ℕ)).map
    (BarMap.chain S.subtype)

lemma comparison_homology_isIso (A : Rep ℚ S) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (comparisonTensor S A) n) := by
  let P := Rep.barResolution ℚ S
  let Q := resolution S
  let F := (Rep.coinvariantsTensor ℚ S).obj A
  have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality (𝟙 _) P Q
    (BarMap.chain S.subtype) (comparison_π S) F n
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  have he : HomologicalComplex.homologyMap (comparisonTensor S A) n =
      (P.isoLeftDerivedObj F n).inv ≫ (Q.isoLeftDerivedObj F n).hom := by
    rw [h]
    simp only [Iso.inv_hom_id_assoc]
    rfl
  rw [he]
  exact inferInstanceAs (IsIso ((P.isoLeftDerivedObj F n).symm ≪≫
    Q.isoLeftDerivedObj F n).hom)

def tensorIso (A : Rep ℚ S) :
    (resolution S).complex.coinvariantsTensorObj A ≅
      (Rep.barComplex ℚ G).coinvariantsTensorObj (Rep.ind S.subtype A) :=
  groupHomology.coinvariantsTensorResProjectiveResolutionIso S A (Rep.barResolution ℚ G)

def unit (A : Rep ℚ S) : A ⟶ Rep.res S.subtype (Rep.ind S.subtype A) :=
  (Rep.indResAdjunction ℚ S.subtype).unit.app A

@[simp] lemma unit_apply (A : Rep ℚ S) (a : A) :
    (unit S A).hom a = IndV.mk S.subtype A.ρ 1 a := rfl

lemma tensorIso_mk (A : Rep ℚ S) (n : ℕ) (a : A) (b : (Rep.barComplex ℚ G).X n) :
    ((tensorIso S A).hom.f n)
      (coinvariantsTensorMk A (Rep.res S.subtype ((Rep.barComplex ℚ G).X n)) a b) =
    coinvariantsTensorMk (Rep.ind S.subtype A) ((Rep.barComplex ℚ G).X n)
      (IndV.mk S.subtype A.ρ 1 a) b :=
  coinvariantsTensorIndInv_mk_tmul_indMk S.subtype a b

lemma chain_compare (A : Rep ℚ S) :
    groupHomology.chainsMap S.subtype (unit S A) ≫
      (groupHomology.inhomogeneousChainsIso (Rep.ind S.subtype A)).hom =
    (groupHomology.inhomogeneousChainsIso A).hom ≫ comparisonTensor S A ≫
      (tensorIso S A).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro x a
  change ((groupHomology.inhomogeneousChainsIso (Rep.ind S.subtype A)).hom.f n)
      ((groupHomology.chainsMap S.subtype (unit S A)).f n (single x a)) =
    ((tensorIso S A).hom.f n)
      ((((coinvariantsTensor ℚ S).obj A).map (BarMap.component S.subtype n))
        (((groupHomology.inhomogeneousChainsIso A).hom.f n) (single x a)))
  rw [groupHomology.chainsMap_f_single,RelativeCoinvariants.chainsIso_single,
    RelativeCoinvariants.chainsIso_single,RelativeCoinvariants.tensor_map_mk,
    BarMap.component_single,tensorIso_mk,unit_apply]
  simp only [map_one]

lemma map_isIso (A : Rep ℚ S) (n : ℕ) :
    IsIso (groupHomology.map S.subtype (unit S A) n) := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n
  have h := congrArg F.map (chain_compare S A)
  simp only [CategoryTheory.Functor.map_comp] at h
  have hComparison : IsIso (F.map (comparisonTensor S A)) := comparison_homology_isIso S A n
  have he : groupHomology.map S.subtype (unit S A) n =
      F.map (groupHomology.inhomogeneousChainsIso A).hom ≫
        F.map (comparisonTensor S A) ≫ F.map (tensorIso S A).hom ≫
        F.map (groupHomology.inhomogeneousChainsIso (Rep.ind S.subtype A)).inv := by
    change F.map (groupHomology.chainsMap S.subtype (unit S A)) = _
    calc
      _ = (F.map (groupHomology.chainsMap S.subtype (unit S A)) ≫
          F.map (groupHomology.inhomogeneousChainsIso (Rep.ind S.subtype A)).hom) ≫
          F.map (groupHomology.inhomogeneousChainsIso (Rep.ind S.subtype A)).inv := by
            simp [←Functor.map_comp]
      _ = _ := by rw [h]; simp only [Category.assoc]

  rw [he]
  exact IsIso.comp_isIso' (F.mapIso (groupHomology.inhomogeneousChainsIso A)).isIso_hom
    (IsIso.comp_isIso' hComparison
      (IsIso.comp_isIso' (F.mapIso (tensorIso S A)).isIso_hom
        (F.mapIso (groupHomology.inhomogeneousChainsIso (Rep.ind S.subtype A))).isIso_inv))
end ShapiroMap
end SourceBurnside.Stability

end

end OAI
