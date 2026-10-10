import OAI.Geometry.ComplexBundle.DirectSum
import OAI.Geometry.ComplexBundle.Sections

namespace OAI

noncomputable section

/-! Tensor line bundles, metrics, and finite frames. -/

section
open Bundle Topology
namespace Kaplansky

section

theorem complexLineMap_scalar (L : ℂ →L[ℂ] ℂ) (z : ℂ) : L z = z * L 1 := by
  have h := L.map_smul z (1 : ℂ)
  simpa using h

variable {B J K : Type*} [TopologicalSpace B]
  (C : VectorBundleCore ℂ B ℂ J) (D : VectorBundleCore ℂ B ℂ K)

/-- Tensor product of two actual line cores. Its transition functions
are the products of the two line transition functions. -/
def tensorLineCore : VectorBundleCore ℂ B ℂ (J × K) where
  baseSet i := C.baseSet i.1 ∩ D.baseSet i.2
  isOpen_baseSet i := (C.isOpen_baseSet i.1).inter (D.isOpen_baseSet i.2)
  indexAt x := (C.indexAt x,D.indexAt x)
  mem_baseSet_at x := ⟨C.mem_baseSet_at x,D.mem_baseSet_at x⟩
  coordChange i j x := (C.coordChange i.1 j.1 x 1 * D.coordChange i.2 j.2 x 1) •
    ContinuousLinearMap.id ℂ ℂ
  coordChange_self i x hx z := by
    rw [C.coordChange_self i.1 x hx.1, D.coordChange_self i.2 x hx.2]
    simp
  continuousOn_coordChange i j := by
    have hc := ((C.continuousOn_coordChange i.1 j.1).mono
      (fun x (hx : x ∈ (C.baseSet i.1 ∩ D.baseSet i.2) ∩ (C.baseSet j.1 ∩ D.baseSet j.2)) =>
        ⟨hx.1.1,hx.2.1⟩)).clm_apply (continuousOn_const (c := (1 : ℂ)))
    have hd := ((D.continuousOn_coordChange i.2 j.2).mono
      (fun x (hx : x ∈ (C.baseSet i.1 ∩ D.baseSet i.2) ∩ (C.baseSet j.1 ∩ D.baseSet j.2)) =>
        ⟨hx.1.2,hx.2.2⟩)).clm_apply (continuousOn_const (c := (1 : ℂ)))
    exact (hc.mul hd).smul continuousOn_const
  coordChange_comp i j k x hx z := by
    have hc := C.coordChange_comp i.1 j.1 k.1 x
      ⟨⟨hx.1.1.1,hx.1.2.1⟩,hx.2.1⟩ (1 : ℂ)
    have hd := D.coordChange_comp i.2 j.2 k.2 x
      ⟨⟨hx.1.1.2,hx.1.2.2⟩,hx.2.2⟩ (1 : ℂ)
    rw [complexLineMap_scalar] at hc hd
    change (C.coordChange j.1 k.1 x 1 * D.coordChange j.2 k.2 x 1) *
        ((C.coordChange i.1 j.1 x 1 * D.coordChange i.2 j.2 x 1) * z) =
      (C.coordChange i.1 k.1 x 1 * D.coordChange i.2 k.2 x 1) * z
    rw [← hc, ← hd]
    ring

/-- Multiplication in core fibers is the tensor pairing. This formula
is compatible with every tensor-product chart. -/
def tensorLinePair (x : B) (v : C.Fiber x) (w : D.Fiber x) : (tensorLineCore C D).Fiber x :=
  (show ℂ from v) * (show ℂ from w)

theorem tensorLinePair_chart (i : J × K) (x : B) (v : C.Fiber x) (w : D.Fiber x) :
    ((tensorLineCore C D).localTriv i ⟨x,tensorLinePair C D x v w⟩).2 =
      (C.localTriv i.1 ⟨x,v⟩).2 * (D.localTriv i.2 ⟨x,w⟩).2 := by
  change ℂ at v w
  change (C.coordChange (C.indexAt x) i.1 x 1 * D.coordChange (D.indexAt x) i.2 x 1) *
    ((show ℂ from v) * (show ℂ from w)) =
    C.coordChange (C.indexAt x) i.1 x v * D.coordChange (D.indexAt x) i.2 x w
  rw [complexLineMap_scalar (C.coordChange (C.indexAt x) i.1 x) v,
    complexLineMap_scalar (D.coordChange (D.indexAt x) i.2 x) w]
  ring

/-- Products of continuous sections are continuous in the tensor
bundle topology; the chart compatibility, not fiberwise continuity alone,
establishes the statement. -/
theorem continuous_tensorLinePair_section (s : ∀ x, C.Fiber x) (t : ∀ x, D.Fiber x)
    (hs : Continuous (fun x => TotalSpace.mk' ℂ x (s x)))
    (ht : Continuous (fun x => TotalSpace.mk' ℂ x (t x))) :
    Continuous (fun x => TotalSpace.mk' ℂ x (tensorLinePair C D x (s x) (t x))) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [FiberBundle.continuousAt_section]
  have hc := (FiberBundle.continuousAt_section ℂ x).mp hs.continuousAt
  have hd := (FiberBundle.continuousAt_section ℂ x).mp ht.continuousAt
  apply (hc.mul hd).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun y =>
    tensorLinePair_chart C D ((C.indexAt x),(D.indexAt x)) y (s y) (t y))

theorem tensorLinePair_ne_zero (x : B) (v : C.Fiber x) (w : D.Fiber x)
    (hv : v ≠ 0) (hw : w ≠ 0) : tensorLinePair C D x v w ≠ 0 := by
  change (show ℂ from v) * (show ℂ from w) ≠ 0
  exact mul_ne_zero hv hw

end

variable {B J : Type} [TopologicalSpace B]
  (C : VectorBundleCore ℂ B ℂ J) (u : ∀ b, C.Fiber b)
  (hu : ∀ b, u b ≠ 0)

/-- Coordinates relative to an actual nowhere-zero line section. -/
def lineFrameEquiv (b : B) : C.Fiber b ≃ₗ[ℂ] ℂ where
  toFun z := (show ℂ from z) / (show ℂ from u b)
  invFun z := z * (show ℂ from u b)
  left_inv z := by
    change ((show ℂ from z) / (show ℂ from u b)) * (show ℂ from u b) = (show ℂ from z)
    exact div_mul_cancel₀ _ (hu b)
  right_inv z := by
    change (z * (show ℂ from u b)) / (show ℂ from u b) = z
    exact mul_div_cancel_right₀ _ (hu b)
  map_add' z w := add_div _ _ _
  map_smul' c z := by change (c*(show ℂ from z))/_ = c*((show ℂ from z)/_); ring

theorem lineFrameEquiv_chart (b : B) (z : C.Fiber b) (i : J) (hi : b ∈ C.baseSet i) :
    lineFrameEquiv C u hu b z =
      (C.localTriv i ⟨b,z⟩).2 / (C.localTriv i ⟨b,u b⟩).2 := by
  have hc : C.coordChange (C.indexAt b) i b 1 ≠ 0 := by
    intro hz
    have he := C.coordChange_comp (C.indexAt b) i (C.indexAt b) b
      ⟨⟨C.mem_baseSet_at b,hi⟩,C.mem_baseSet_at b⟩ 1
    rw [hz, map_zero, C.coordChange_self _ _ (C.mem_baseSet_at b)] at he
    exact zero_ne_one he
  change (show ℂ from z) / (show ℂ from u b) =
    C.coordChange (C.indexAt b) i b z / C.coordChange (C.indexAt b) i b (u b)
  rw [complexLineMap_scalar (C.coordChange (C.indexAt b) i b) z,
    complexLineMap_scalar (C.coordChange (C.indexAt b) i b) (u b)]
  exact (mul_div_mul_right _ _ hc).symm

variable (hc : Continuous (fun b => TotalSpace.mk' ℂ b (u b)))

/-- A nonzero continuous frame gives a homeomorphism for the original
line-core topology, with complex-linear fibers. -/
def lineFrameHomeomorph : TotalSpace ℂ C.Fiber ≃ₜ B × ℂ where
  toFun z := (z.proj,lineFrameEquiv C u hu z.proj z.2)
  invFun z := ⟨z.1,(lineFrameEquiv C u hu z.1).symm z.2⟩
  left_inv z := by
    obtain ⟨b,z⟩ := z
    exact congrArg (TotalSpace.mk' ℂ b) ((lineFrameEquiv C u hu b).symm_apply_apply z)
  right_inv z := Prod.ext rfl ((lineFrameEquiv C u hu z.1).apply_symm_apply z.2)
  continuous_toFun := by
    apply (FiberBundle.continuous_proj _ _).prodMk
    apply continuous_iff_continuousAt.mpr
    intro z
    let i := C.indexAt z.proj
    have hp := FiberBundle.continuous_proj ℂ C.Fiber
    have hv := ((C.localTriv i).continuousAt
      ((C.localTriv i).mem_source.mpr (C.mem_baseSet_at z.proj))).snd
    have hw : ContinuousAt (fun w : TotalSpace ℂ C.Fiber =>
        (C.localTriv i ⟨w.proj,u w.proj⟩).2) z :=
      ((FiberBundle.continuousAt_section ℂ z.proj).mp hc.continuousAt).comp hp.continuousAt
    have hn : (C.localTriv i ⟨z.proj,u z.proj⟩).2 ≠ 0 := by
      change C.coordChange (C.indexAt z.proj) i z.proj (u z.proj) ≠ 0
      intro h
      exact hu z.proj ((C.coordChange_self _ _ (C.mem_baseSet_at z.proj) (u z.proj)).symm.trans h)
    apply (hv.div hw hn).congr_of_eventuallyEq
    filter_upwards [hp.continuousAt ((C.isOpen_baseSet i).mem_nhds
      (C.mem_baseSet_at z.proj))] with w hw
    exact lineFrameEquiv_chart C u hu w.proj w.2 i hw
  continuous_invFun := by
    exact continuous_bundle_smul_over Prod.fst continuous_fst Prod.snd continuous_snd
      (fun z : B × ℂ => u z.1) (hc.comp continuous_fst)

variable {S : Type} [Fintype S] {I : S → Type}
  (D : ∀ s, VectorBundleCore ℂ B ℂ (I s))
  (v : ∀ s b, (D s).Fiber b) (hn : ∀ s b, v s b ≠ 0)
  (hv : ∀ s, Continuous (fun b => TotalSpace.mk' ℂ b (v s b)))

def finiteLineFrameEquiv (b : B) :
    (finiteLineSumCore D).Fiber b ≃ₗ[ℂ] (S → ℂ) :=
  (EuclideanSpace.equiv S ℂ).toLinearEquiv.trans
    (LinearEquiv.piCongrRight (fun s => lineFrameEquiv (D s) (v s) (hn s) b))

def finiteLineFrameHomeomorph :
    TotalSpace (EuclideanSpace ℂ S) (finiteLineSumCore D).Fiber ≃ₜ B × (S → ℂ) where
  toFun z := (z.proj,finiteLineFrameEquiv D v hn z.proj z.2)
  invFun z := ⟨z.1,(finiteLineFrameEquiv D v hn z.1).symm z.2⟩
  left_inv z := by
    obtain ⟨b,w⟩ := z
    exact congrArg (TotalSpace.mk' _ b) ((finiteLineFrameEquiv D v hn b).symm_apply_apply w)
  right_inv z := Prod.ext rfl ((finiteLineFrameEquiv D v hn z.1).apply_symm_apply z.2)
  continuous_toFun := by
    apply (FiberBundle.continuous_proj _ _).prodMk
    apply continuous_pi
    intro s
    exact continuous_snd.comp ((lineFrameHomeomorph (D s) (v s) (hn s) (hv s)).continuous.comp
      (continuous_finiteLineSumComponent D s))
  continuous_invFun := by
    apply (continuous_finiteLineSum_iff _ _).mpr
    refine ⟨continuous_fst,fun s => ?_⟩
    exact (lineFrameHomeomorph (D s) (v s) (hn s) (hv s)).symm.continuous.comp
      (continuous_fst.prodMk ((continuous_apply s).comp continuous_snd))

theorem finiteLineFrameHomeomorph_zero_iff
    (z : TotalSpace (EuclideanSpace ℂ S) (finiteLineSumCore D).Fiber) :
    (finiteLineFrameHomeomorph D v hn hv z).2 = 0 ↔ z.2 = 0 :=
  (finiteLineFrameEquiv D v hn z.proj).map_eq_zero_iff

end Kaplansky

end

open Bundle Topology
open scoped InnerProductSpace
namespace Kaplansky
variable {B J K : Type*} [TopologicalSpace B]
  (C : VectorBundleCore ℂ B ℂ J) (D : VectorBundleCore ℂ B ℂ K)

theorem tensorLineCore_coordChange_eq_comp (i j : J × K) (x : B) (z : ℂ) :
    (tensorLineCore C D).coordChange i j x z =
      C.coordChange i.1 j.1 x (D.coordChange i.2 j.2 x z) := by
  change (C.coordChange i.1 j.1 x 1 * D.coordChange i.2 j.2 x 1) * z = _
  rw [complexLineMap_scalar (C.coordChange i.1 j.1 x) (D.coordChange i.2 j.2 x z),
    complexLineMap_scalar (D.coordChange i.2 j.2 x) z]
  ring

/-- Tensoring unitary line transitions preserves the actual Hermitian
metric. No determinant or orientation premise is required. -/
theorem tensorLineCore_unitary
    (hC : ∀ i j x, x ∈ C.baseSet i → x ∈ C.baseSet j → ∀ z w : ℂ,
      inner ℂ (C.coordChange i j x z) (C.coordChange i j x w) = inner ℂ z w)
    (hD : ∀ i j x, x ∈ D.baseSet i → x ∈ D.baseSet j → ∀ z w : ℂ,
      inner ℂ (D.coordChange i j x z) (D.coordChange i j x w) = inner ℂ z w)
    (i j : J × K) (x : B) (hi : x ∈ (tensorLineCore C D).baseSet i)
    (hj : x ∈ (tensorLineCore C D).baseSet j) (z w : ℂ) :
    inner ℂ ((tensorLineCore C D).coordChange i j x z)
      ((tensorLineCore C D).coordChange i j x w) = inner ℂ z w := by
  rw [tensorLineCore_coordChange_eq_comp, tensorLineCore_coordChange_eq_comp,
    hC i.1 j.1 x hi.1 hj.1, hD i.2 j.2 x hi.2 hj.2]

theorem tensorLineSum_unitary {S : Type*} [Fintype S] {J K : S → Type*}
    (C : ∀ s, VectorBundleCore ℂ B ℂ (J s)) (D : ∀ s, VectorBundleCore ℂ B ℂ (K s))
    (hC : LineCoreIsUnitary C) (hD : LineCoreIsUnitary D) :
    LineCoreIsUnitary (fun s => tensorLineCore (C s) (D s)) :=
  fun s => tensorLineCore_unitary (C s) (D s) (hC s) (hD s)

end Kaplansky

end

end OAI
