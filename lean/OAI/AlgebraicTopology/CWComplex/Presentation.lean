import OAI.AlgebraicTopology.CWComplex.CoverTopology
import OAI.GroupTheory.Presentation.KernelCycles

namespace OAI

noncomputable section

open Classical Set Metric Topology

namespace EilenbergGanea.CWPresentation
open Set Topology CWCover CWCollar PathTransport CubicalSingular CoverTopology
open scoped ContinuousMap
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
variable [T2Space X] [CWComplex (univ : Set X)] {p : E → X}
variable (cov : IsCoveringMap p) (hd : ∀ k, 2 < k → IsEmpty (Cell (X:=X) k))

abbrev base := baseAttachment hd
abbrev lifted := liftedAttachment cov hd

instance baseOuterConnected [PathConnectedSpace X] : PathConnectedSpace (base hd).outer :=
  (base hd).compression.pathConnected (base hd).outer_open (base hd).inner_open
    (base hd).outer_union_inner (ForestCover.thin_inner (base hd))
instance liftedOuterConnected [PathConnectedSpace E] : PathConnectedSpace (lifted cov hd).outer :=
  (lifted cov hd).compression.pathConnected (lifted cov hd).outer_open (lifted cov hd).inner_open
    (lifted cov hd).outer_union_inner (ForestCover.thin_inner (lifted cov hd))

/-- The actual collar, not an assumed graph presentation, has free π1. -/
theorem outer_isFree [PathConnectedSpace X] (r : (base hd).outer) :
    IsFreeGroup (FundamentalGroup (base hd).outer r) := by
  let a := base hd
  let S := CWComplex.skeletonLT (univ : Set X) (2 : ℕ)
  have hs (k : ℕ) (hk : 1 < k) : IsEmpty (CWSubspace.Cell (S : Set X) k) := by
    refine ⟨fun i => ?_⟩
    have hi : (k : ℕ∞) < 2 := by
      simpa only [S,CWComplex.skeletonLT_I,Set.mem_ofPred_eq,Nat.cast_ofNat] using i.property
    have hki : k < 2 := by exact_mod_cast hi
    omega
  have hr : Function.Surjective a.retractMap := fun x => ⟨a.sectionMap x,a.retract_section x⟩
  let : PathConnectedSpace a.lower := hr.pathConnectedSpace a.retractMap.continuous
  let : PathConnectedSpace (S : Set X) := inferInstanceAs (PathConnectedSpace a.lower)
  let : IsFreeGroup (FundamentalGroup a.lower (a.retractMap r)) :=
    ForestCover.isFree_ordinary_graph (S : Set X) hs (fun y => (PathConnectedSpace.joined _ y).somePath)
  let e : a.outer ≃ₕ a.lower :=
    ⟨a.retractMap,a.sectionMap,⟨a.collarHomotopy.symm⟩,by
      have he : a.retractMap.comp a.sectionMap = ContinuousMap.id a.lower := ContinuousMap.ext a.retract_section
      rw [he]⟩
  exact IsFreeGroup.ofMulEquiv (homotopyFundamentalEquiv e r).symm

variable [ContractibleSpace E]
variable (e : (lifted cov hd).outer)

abbrev root : (base hd).outer := outerProjection cov hd e
abbrev toTotal : (FundamentalGroup (base hd).outer (root cov hd e))ᵐᵒᵖ →*
    (FundamentalGroup X (p e.val))ᵐᵒᵖ :=
  (FundamentalGroup.map (CoverKernel.inclusion (base hd).outer) (root cov hd e)).op
abbrev fromLift : (FundamentalGroup (lifted cov hd).outer e)ᵐᵒᵖ →*
    (FundamentalGroup (base hd).outer (root cov hd e))ᵐᵒᵖ :=
  (FundamentalGroup.map (outerProjection cov hd) e).op

/-- Closed lifting gives the actual kernel, including all (possibly infinitely
many) lifted cells and without a cellular-homology assumption. -/
def liftedKernelEquiv : (FundamentalGroup (lifted cov hd).outer e)ᵐᵒᵖ ≃* (toTotal cov hd e).ker :=
  (homotopyFundamentalEquiv (liftedOuterHomeomorph cov hd).toHomotopyEquiv e).op.trans
    (CoverKernel.fundamentalKernelEquiv cov (base hd).outer (liftedOuterHomeomorph cov hd e))

@[simp] theorem liftedKernelEquiv_val (w : (FundamentalGroup (lifted cov hd).outer e)ᵐᵒᵖ) :
    (liftedKernelEquiv cov hd e w).val = fromLift cov hd e w := by
  obtain ⟨γ,hγ⟩ := Quotient.exists_rep w.unop
  have he : MulOpposite.op (asClass γ) = w := congrArg MulOpposite.op hγ
  rw [← he]
  rfl

variable (q : ∀ y : (lifted cov hd).outer, Path e y) (y₀ : Annulus 2)

def kernelBasis : (LiftedCell (p:=p) 2 →₀ ℤ) ≃ₗ[ℤ]
    Additive (Abelianization (toTotal cov hd e).ker) :=
  ((lifted cov hd).annularBasis y₀).trans ((hurewiczOne q).trans
    (liftedKernelEquiv cov hd e).abelianizationCongr.toAdditive.toIntLinearEquiv)

theorem kernelBasis_single (c : LiftedCell (p:=p) 2) :
    kernelBasis cov hd e q y₀ (Finsupp.single c 1) =
      Additive.ofMul (Abelianization.of (liftedKernelEquiv cov hd e
        ((lifted cov hd).annulusRelator q y₀ c))) := by
  simp only [kernelBasis,LinearEquiv.trans_apply]
  rw [Attachment.annularBasis_single,hurewiczOne_loop]
  rfl

end EilenbergGanea.CWPresentation


namespace EilenbergGanea.CWPresentation
open Set Topology CWCover CWCollar PathTransport CubicalSingular CoverTopology
open scoped ContinuousMap
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
variable [T2Space X] [CWComplex (univ : Set X)] {p : E → X}
variable (cov : IsCoveringMap p) (hd : ∀ k, 2 < k → IsEmpty (Cell (X:=X) k))
variable [ContractibleSpace E] (e : (lifted cov hd).outer)
variable (q : ∀ y : (lifted cov hd).outer, Path e y) (y₀ : Annulus 2)

omit [ContractibleSpace E] in
@[simp] theorem project_annulus (c : LiftedCell (p:=p) 2) (z : Annulus 2) :
    outerProjection cov hd ((lifted cov hd).annulusMap c z) = (base hd).annulusMap c.1 z :=
  Subtype.ext (lifted_annulus cov hd c z)

def projectedAnchor (c : LiftedCell (p:=p) 2) :
    Path (root cov hd e) ((base hd).annulusMap c.1 y₀) :=
  ((q ((lifted cov hd).annulusMap c y₀)).map (outerProjection cov hd).continuous).cast rfl
    (project_annulus cov hd c y₀).symm

def projectedRelator (c : LiftedCell (p:=p) 2) :
    (FundamentalGroup (base hd).outer (root cov hd e))ᵐᵒᵖ :=
  anchored (projectedAnchor cov hd e q y₀ c)
    ((annulusGenerator y₀).map ((base hd).annulusMap c.1).continuous)

omit [ContractibleSpace E] in
theorem projectedRelator_eq (c : LiftedCell (p:=p) 2) :
    fromLift cov hd e ((lifted cov hd).annulusRelator q y₀ c) =
      projectedRelator cov hd e q y₀ c := by
  change (FundamentalGroup.map (outerProjection cov hd) e).op
    (anchored (q ((lifted cov hd).annulusMap c y₀))
      ((annulusGenerator y₀).map ((lifted cov hd).annulusMap c).continuous)) = _
  rw [anchored_map]
  apply anchored_congr
  · intro t; rfl
  · intro t; exact project_annulus cov hd c (annulusGenerator y₀ t)

variable (hs : Function.Surjective p)
def relator (j : Cell (X:=X) 2) := projectedRelator cov hd e q y₀ (chosenCell hs j)

@[simp] theorem relator_mem (j : Cell (X:=X) 2) : toTotal cov hd e (relator cov hd e q y₀ hs j) = 1 := by
  rw [relator,← projectedRelator_eq,← liftedKernelEquiv_val]
  exact (liftedKernelEquiv cov hd e ((lifted cov hd).annulusRelator q y₀ (chosenCell hs j))).property

variable [PathConnectedSpace X]
/-- The selected lifted annuli give an actual presentation of the total π1. -/
theorem relator_normalClosure : (toTotal cov hd e).ker =
    Subgroup.normalClosure (Set.range (relator cov hd e q y₀ hs)) := by
  let bq : ∀ y : (base hd).outer, Path (root cov hd e) y := fun y => (PathConnectedSpace.joined _ y).somePath
  have hn := (base hd).annulus_normalClosure bq y₀ (ForestCover.thin_inner (base hd))
  apply le_antisymm
  · rw [show (toTotal cov hd e).ker = Subgroup.normalClosure (Set.range ((base hd).annulusRelator bq y₀)) from hn]
    apply Subgroup.normalClosure_le_normal
    rintro w ⟨j,rfl⟩
    let s : Path (root cov hd e) ((base hd).annulusMap j y₀) := projectedAnchor cov hd e q y₀ (chosenCell hs j)
    change anchored (bq ((base hd).annulusMap j y₀)) ((annulusGenerator y₀).map ((base hd).annulusMap j).continuous) ∈ _
    rw [anchored_conjugate (bq ((base hd).annulusMap j y₀)) s]
    exact (inferInstance : (Subgroup.normalClosure (Set.range (relator cov hd e q y₀ hs))).Normal).conj_mem _ (Subgroup.subset_normalClosure ⟨j,rfl⟩) _
  · apply Subgroup.normalClosure_le_normal
    rintro w ⟨j,rfl⟩
    exact relator_mem cov hd e q y₀ hs j

end EilenbergGanea.CWPresentation


namespace EilenbergGanea.CWPresentation
open Set Topology CWCover CWCollar PathTransport CubicalSingular CoverTopology
open scoped ContinuousMap
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
variable [T2Space X] [CWComplex (univ : Set X)] {p : E → X}
variable (cov : IsCoveringMap p) (hd : ∀ k, 2 < k → IsEmpty (Cell (X:=X) k))
variable [ContractibleSpace E] (e : (lifted cov hd).outer)
variable (q : ∀ y : (lifted cov hd).outer, Path e y) (y₀ : Annulus 2) (hs : Function.Surjective p)

def deckEquiv : (FundamentalGroup X (p e.val))ᵐᵒᵖ ≃* deckGroup p :=
  CoverMonodromy.traversalEquiv (isQuotientCoveringMap_deck cov hs) e.val

def conjugator (d : deckGroup p) (j : Cell (X:=X) 2) :
    (FundamentalGroup (base hd).outer (root cov hd e))ᵐᵒᵖ :=
  difference (projectedAnchor cov hd e q y₀ (d • chosenCell hs j))
    (projectedAnchor cov hd e q y₀ (chosenCell hs j))

omit [ContractibleSpace E] in
theorem relator_conjugate (d : deckGroup p) (j : Cell (X:=X) 2) :
    projectedRelator cov hd e q y₀ (d • chosenCell hs j) =
      conjugator cov hd e q y₀ hs d j * relator cov hd e q y₀ hs j *
        (conjugator cov hd e q y₀ hs d j)⁻¹ :=
  anchored_conjugate _ _ _

/-- The group-ring coefficient is exactly the deck translate, not its inverse
or an arbitrary permutation. This fixes the traversal/left-action convention. -/
theorem conjugator_value (d : deckGroup p) (j : Cell (X:=X) 2) :
    deckEquiv cov hd e hs (toTotal cov hd e (conjugator cov hd e q y₀ hs d j)) = d := by
  let c := chosenCell hs j
  let z : E := ((lifted cov hd).annulusMap c y₀).val
  have hz : d • z = ((lifted cov hd).annulusMap (d • c) y₀).val := by
    let := CWCover.cwComplex cov
    change d • characteristic (X:=E) c y₀.val.val = characteristic (X:=E) (d • c) y₀.val.val
    rw [lifted_characteristic cov c,lifted_characteristic cov (d • c)]
    exact (cellLift_smul cov d c y₀.val.val).symm
  let s : Path e.val (d • z) :=
    ((q ((lifted cov hd).annulusMap (d • c) y₀)).map continuous_subtype_val).cast rfl hz
  let t : Path e.val z := (q ((lifted cov hd).annulusMap c y₀)).map continuous_subtype_val
  let hp := isQuotientCoveringMap_deck cov hs
  have he : toTotal cov hd e (conjugator cov hd e q y₀ hs d j) =
      MulOpposite.op (Path.Homotopic.Quotient.mk
        (((s.map hp.continuous).cast rfl (hp.map_smul d).symm).trans
          (t.map hp.continuous).symm)) := by
    change MulOpposite.op (Path.Homotopic.Quotient.mk
      (((projectedAnchor cov hd e q y₀ (d • c)).trans
        (projectedAnchor cov hd e q y₀ c).symm).map continuous_subtype_val)) = _
    rw [Path.map_trans,← Path.map_symm]
    rfl
  rw [he]
  exact CoverMonodromy.traversalEquiv_difference hp e.val d s t

/-- Reindexing the genuine lifted-cell basis by monodromy gives the actual
integral basis on G×(base2-cells). -/
def coefficientIndex : (FundamentalGroup X (p e.val))ᵐᵒᵖ × Cell (X:=X) 2 ≃ LiftedCell (p:=p) 2 :=
  ((Equiv.prodCongr (deckEquiv cov hd e hs).toEquiv (Equiv.refl _)).trans
    (Equiv.prodComm _ _)).trans (cellOrbitEquiv cov hs 2).symm

def conjugateBasis : (((FundamentalGroup X (p e.val))ᵐᵒᵖ × Cell (X:=X) 2) →₀ ℤ) ≃ₗ[ℤ]
    Additive (Abelianization (toTotal cov hd e).ker) :=
  (Finsupp.domLCongr (coefficientIndex cov hd e hs)).trans (kernelBasis cov hd e q y₀)

/-- Every basis column is the literal conjugate of a selected annular relation,
with a conjugating word having precisely the specified quotient value. -/
theorem conjugateBasis_single (g : (FundamentalGroup X (p e.val))ᵐᵒᵖ) (j : Cell (X:=X) 2) :
    ∃ k : (FundamentalGroup (base hd).outer (root cov hd e))ᵐᵒᵖ,
      toTotal cov hd e k = g ∧
      conjugateBasis cov hd e q y₀ hs (Finsupp.single (g,j) 1) =
        Additive.ofMul (Abelianization.of (⟨k * relator cov hd e q y₀ hs j * k⁻¹,by
          change toTotal cov hd e (k * relator cov hd e q y₀ hs j * k⁻¹) = 1
          rw [map_mul,map_mul,map_inv,relator_mem,mul_one,mul_inv_cancel]⟩ : (toTotal cov hd e).ker)) := by
  let d := deckEquiv cov hd e hs g
  let k := conjugator cov hd e q y₀ hs d j
  refine ⟨k,?_,?_⟩
  · apply (deckEquiv cov hd e hs).injective
    exact conjugator_value cov hd e q y₀ hs d j
  · simp only [conjugateBasis,LinearEquiv.trans_apply,Finsupp.domLCongr_single]
    rw [kernelBasis_single]
    congr 2
    apply Subtype.ext
    rw [liftedKernelEquiv_val,projectedRelator_eq]
    exact relator_conjugate cov hd e q y₀ hs d j

end EilenbergGanea.CWPresentation


namespace EilenbergGanea.CWPresentation
open Set Topology CWCover CWCollar PathTransport CubicalSingular CoverTopology
open scoped ContinuousMap
universe u v
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
variable [T2Space X] [CWComplex (univ : Set X)] {p : E → X}
variable (cov : IsCoveringMap p) (hd : ∀ k, 2 < k → IsEmpty (Cell (X:=X) k))
variable [PathConnectedSpace X] [ContractibleSpace E] (hs : Function.Surjective p)

include cov hd hs

/-- The arbitrary ordinary2-dimensional CW presentation theorem, including the
full integral boundary basis of its actual contractible cover. There are no
finiteness, countability, local finiteness, or cell-universe restrictions. -/
theorem ordinary_boundary_basis {G : Type v} [Group G] (x : X) (χ₀ : FundamentalGroup X x ≃* G) :
    ∃ (A : Type u) (a : A → G), Function.Surjective (wordValue a) ∧
      ∃ (r : Cell (X:=X) 2 → FreeGroup A), (∀ j, wordValue a (r j) = 1) ∧
        (wordValue a).ker = Subgroup.normalClosure (Set.range r) ∧
        ∃ B : BasedChains G (Cell (X:=X) 2) ≃ₗ[ℤ] cycles a,
          ∀ c, (B c : BasedChains G A) = relatorChainMap a r c := by
  let e : (lifted cov hd).outer := Classical.choice inferInstance
  let q : ∀ y : (lifted cov hd).outer, Path e y := fun y => (PathConnectedSpace.joined _ y).somePath
  let y₀ : Annulus 2 := Classical.choice inferInstance
  let H := FundamentalGroup (base hd).outer (root cov hd e)
  let : IsFreeGroup H := outer_isFree hd (root cov hd e)
  let : IsFreeGroup Hᵐᵒᵖ := IsFreeGroup.ofMulEquiv (MulEquiv.inv' H)
  have hf : Function.Surjective (toTotal cov hd e) := by
    intro g
    obtain ⟨w,hw⟩ := (base hd).compression.fundamental_surjective
      (base hd).outer_open (base hd).inner_open (base hd).outer_union_inner
      (ForestCover.thin_inner (base hd)) (root cov hd e) g.unop
    exact ⟨MulOpposite.op w,congrArg MulOpposite.op hw⟩
  let χ : (FundamentalGroup X (p e.val))ᵐᵒᵖ ≃* G :=
    (MulEquiv.inv' (FundamentalGroup X (p e.val))).symm.trans
      ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (p e.val) x).trans χ₀)
  exact PresentationAlgebra.boundary_basis_of_free_target
    (toTotal cov hd e) hf (relator cov hd e q y₀ hs)
    (relator_mem cov hd e q y₀ hs) (relator_normalClosure cov hd e q y₀ hs)
    (conjugateBasis cov hd e q y₀ hs) (conjugateBasis_single cov hd e q y₀ hs) χ

end EilenbergGanea.CWPresentation




end

end OAI
