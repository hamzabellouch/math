import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ActiveGibbs
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.MarginalSupport

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldStageCGibbs

open AllFieldParameters AllFieldHistory AllFieldActiveLaws AllFieldActiveGibbs
open MatrixMultiplication.Foundation JointPopulation JointAmbientDegree
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def distinguishedSide {K : ℕ} (h : PartC K) (phi : Placement) : Fin 3 :=
  phi (stageCDistinguished (cShapeParent h))

def coordinateMass {K : ℕ} (h : PartC K) (k : Fin 17) : ℝ :=
  if k.val = 1 then
    (((1 - binaryParameter (cParameterParent h) (cShapeParent h)) / 2 : ℚ) : ℝ)
  else ((binaryParameter (cParameterParent h) (cShapeParent h) / 2 : ℚ) : ℝ)

def physicalPotential {K : ℕ} (h : PartC K) (phi : Placement)
    (side : Fin 3) (k : Fin 17) : ℝ :=
  if side = distinguishedSide h phi then Real.log (coordinateMass h k) else 0

theorem distinguishedSide_branch {K : ℕ} (h : PartC K) (phi : Placement)
    (b : Fin 4) :
    (shapeSide (distinguishedSide h phi) (branchShape (Work.stageC h, phi) b)).val =
      stageCAtom (cShapeParent h) b (stageCDistinguished (cShapeParent h)) := by
  simp only [distinguishedSide, branchShape, encodePhysicalShape_side,
    Equiv.symm_apply_apply, Work.splitShape, cSplit]

theorem placedLaw_stageC_branch_mass {K : ℕ} (h : PartC K) (phi : Placement)
    (b : Fin 4) :
    (placedLaw (Work.stageC h, phi)).mass (branchShape (Work.stageC h, phi) b) =
      coordinateMass h
        (shapeSide (distinguishedSide h phi) (branchShape (Work.stageC h, phi) b)) := by
  change (Work.stageC h).Branch at b
  rw [placedLaw_mass_branch]
  change (stageCWeight (cParameterParent h) (cShapeParent h) b : ℝ) = _
  simp only [coordinateMass, distinguishedSide_branch h phi b]
  unfold stageCWeight
  have hm := stageCAtom_middle (cShapeParent h) (bShape_size h.1.val) h.1.property b
  by_cases hb : b.val < 2
  · have hn : ¬stageCAtom (cShapeParent h) b (stageCDistinguished (cShapeParent h)) = 1 :=
      fun hmiddle => (hm.mp hmiddle) hb
    simp only [hb, ite_true, hn, ite_false]
  · have hx := hm.mpr hb
    simp only [hb, ite_false, hx, ite_true]

theorem placedLaw_stageC_mass_of_positive {K : ℕ} (h : PartC K) (phi : Placement)
    (u : JointPopulation.Shape) (hu : 0 < (placedLaw (Work.stageC h, phi)).mass u) :
    (placedLaw (Work.stageC h, phi)).mass u =
      coordinateMass h (shapeSide (distinguishedSide h phi) u) := by
  obtain ⟨b, rfl⟩ := placedLaw_positive_has_branch (Work.stageC h, phi) u hu
  exact placedLaw_stageC_branch_mass h phi b

theorem placedLaw_stageC_mass_on_feasible {K : ℕ} (h : PartC K) (phi : Placement)
    (u : JointPopulation.Shape) (ht : u.1.val + u.2.1.val + u.2.2.val = 2)
    (hle : ∀ s, (shapeSide s u).val ≤ physicalShape phi (cShapeParent h) s) :
    (placedLaw (Work.stageC h, phi)).mass u =
      coordinateMass h (shapeSide (distinguishedSide h phi) u) := by
  obtain ⟨b, rfl⟩ := branchShape_exhaustive (Work.stageC h, phi) u ht hle
  exact placedLaw_stageC_branch_mass h phi b

theorem sum_physicalPotential {K : ℕ} (h : PartC K) (phi : Placement)
    (u : JointPopulation.Shape) :
    (∑ s : Fin 3, physicalPotential h phi s (shapeSide s u)) =
      Real.log (coordinateMass h (shapeSide (distinguishedSide h phi) u)) := by
  simp only [physicalPotential, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem placedLaw_stageC_log {K : ℕ} (h : PartC K) (phi : Placement)
    (u : JointPopulation.Shape) (hu : 0 < (placedLaw (Work.stageC h, phi)).mass u) :
    Real.log ((placedLaw (Work.stageC h, phi)).mass u) =
      physicalPotential h phi 0 (shapeSide 0 u) +
        physicalPotential h phi 1 (shapeSide 1 u) +
        physicalPotential h phi 2 (shapeSide 2 u) - 0 := by
  rw [placedLaw_stageC_mass_of_positive h phi u hu, ← sum_physicalPotential h phi u,
    Fin.sum_univ_three, sub_zero]

theorem placedLaw_positive_parent_bounds {K : ℕ} (w : PlacedWork K)
    (u : JointPopulation.Shape) (hu : 0 < (placedLaw w).mass u) :
    ∀ s, (shapeSide s u).val ≤ physicalShape w.2 w.1.parentShape s := by
  obtain ⟨b, rfl⟩ := placedLaw_positive_has_branch w u hu
  intro s
  rw [branchShape, encodePhysicalShape_side]
  exact w.1.splitShape_le b (w.2.symm s)

theorem jointCounts_positive_reference {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (u : JointPopulation.Shape)
    (hu : 0 < jointCounts allocation dilation w u) : 0 < (placedLaw w).mass u := by
  have hc : (0 : ℝ) < (jointCounts allocation dilation w u : ℝ) := by exact_mod_cast hu
  rw [jointCounts_cast] at hc
  rcases mul_pos_iff.mp hc with hpos | hneg
  · exact hpos.2
  · exact False.elim (not_lt_of_ge (Nat.cast_nonneg _) hneg.1)

theorem localAllowed_positive_reference {Hist : Type*} [Fintype Hist] [DecidableEq Hist]
    (counts : Hist → JointPopulation.Shape → ℕ) (total : Hist → ℕ)
    (hist : Hist) (word : Positions counts hist → JointPopulation.Shape)
    (hw : localAllowed counts total hist word)
    {K : ℕ} (h : PartC K) (phi : Placement) (htotal : total hist = 2)
    (hcounts : ∀ u, 0 < counts hist u → 0 < (placedLaw (Work.stageC h, phi)).mass u) :
    ∀ i, 0 < (placedLaw (Work.stageC h, phi)).mass (word i) := by
  intro i
  have hbounds := JointMarginalSupport.localAllowed_parent_bounds counts total hist word hw
    (physicalShape phi (cShapeParent h))
    (fun u hu => placedLaw_positive_parent_bounds (Work.stageC h, phi) u (hcounts u hu))
  obtain ⟨j, hj⟩ := JointMarginalSupport.localAllowed_coordinate_witness
    counts total hist word hw (distinguishedSide h phi) i
  have hp : 0 < (placedLaw (Work.stageC h, phi)).mass ((canonicalTarget counts hist).val j) :=
    hcounts _ (symbol_count_pos counts (canonicalTarget counts) hist j)
  have ht : (word i).1.val + (word i).2.1.val + (word i).2.2.val = 2 :=
    (hw.1 i).trans htotal
  calc
    0 < (placedLaw (Work.stageC h, phi)).mass ((canonicalTarget counts hist).val j) := hp
    _ = coordinateMass h
        (shapeSide (distinguishedSide h phi) ((canonicalTarget counts hist).val j)) :=
      placedLaw_stageC_mass_of_positive h phi _ hp
    _ = coordinateMass h (shapeSide (distinguishedSide h phi) (word i)) := congrArg _ hj
    _ = (placedLaw (Work.stageC h, phi)).mass (word i) :=
      (placedLaw_stageC_mass_on_feasible h phi (word i) ht (hbounds i)).symm

end MatrixMultiplication.AllFieldStageCGibbs

end

end OAI
