import OAI.Probability.DilutedSpin.DepthChildMoment
import OAI.Probability.DilutedSpin.ScheduledCovariance
import OAI.Probability.DilutedSpin.ScheduledMultileafMatrix

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
open PrescribedTree
variable {α I : Type} [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I] {N : ℕ}

/-- Root-averaged genuine old/delayed multileaf induction. The only signed
term is ONE centered root matrix covariance, exactly the term controlled
by physical_matrix_selection. All remaining errors are actual proper
children or the single-copy h_N; the target projection error is eliminated. -/
theorem scheduled_root_multileaf {Z : Type} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (H r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ)) (a : α) (C : Fin k → ReducedTopology)
    (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d)) (ha : (Q a).val=r+1+d)
    (hQ : ∀ j v, (Q a).val+1≤(Q (e j v)).val)
    (K : (z : Z) → KernelTower (Ω z) (H+1+1+r+1+d))
    (f : (z : Z) → FinitePath (Ω z) (H+1+1+r+1+d) → Fin N → ℝ)
    (hf : ∀ z x i, |f z x i|≤1) :
    let L := H+1+1+r+1+d
    let ht := shiftedFrameHeight H r d
    let OldChild := fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val)
    let NewChild := fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
    let OldNode := PrescribedTree.node k OldChild
    let NewNode := PrescribedTree.node k NewChild
    let S := splitFrame OldNode r d
    let RawTarget := splitFrame NewNode (r+1) d
    let Target := heightCast ht RawTarget
    let K' := fun z => kernelHeightCast ht.symm (K z)
    let f' := fun z => vectorHeightCast ht.symm (f z)
    let W := fun z => (k:ℝ)*∑ j, Real.sqrt (descendantEnergyAt (OldChild j) r d (K z) (f z))
    let W' := fun z => (k:ℝ)*∑ j, Real.sqrt (descendantEnergyAt (NewChild j) (r+1) d (K' z) (f' z))
    let h := fun z => projectionShiftError a C e (K z) (f z) Q
    let X := fun z x i => splitProjector OldNode r d (K z) (fun y => f z y i) x
    let A := fun z => spatialProduct (fun _ : I => f z)
    ∀ (b : OldNode.Leaf) (b' : NewNode.Leaf) (q0 : I → RawTarget.Leaf), Function.Bijective q0 →
      ∀ (u v : I), u≠v → q0 u=splitFrameLeaf NewNode (r+1) d 0 b' →
        q0 v=splitFrameLeaf NewNode (r+1) d 1 b' →
    ∀ (B : Finset ℕ), branchingCount S (· ∈ B)=0 →
    ∀ (cs : List I), cs.Nodup → (∀ j ∈ cs, j ∉ insert v ({u}:Finset I)) →
      insert v ({u}:Finset I) ∪ cs.toFinset=Finset.univ →
    let q := fun j => leafHeightCast ht RawTarget (q0 j)
    let x := splitFrameLeaf OldNode r d 0 b
    let y := splitFrameLeaf OldNode r d 1 b
    let m := grid L 0 L
    let J := partialKappa Target m (Finset.univ.image q)/
      partialKappa Target m ((insert v ({u}:Finset I)).image q)
    Integrable (fun z => shapeEnergyAt (stem OldNode r) d (K z) (f z)) μ →
    Integrable (fun z => KernelTower.halfTripleDifferenceAt L (K z) d (X z)) μ →
    Integrable (fun z => matrixObservableHistory Target q (K z) m (v::cs) S x (A z) (treeOverlap S (f z))) μ →
    Integrable (fun z => matrixProjectionError Target q (K z) u v (A z) (X z)) μ →
    Integrable (fun z => oldProjectionError S (K z) x y (treeOverlap S (f z)) (X z)) μ →
    Integrable (fun z => (Target.sampleLaw (K z)).expect (fun w => A z (fun j => Target.pathAt (q j) w))) μ →
    Integrable W μ → Integrable (fun z => Real.sqrt (W z)) μ →
    Integrable (fun z => Real.sqrt (W' z)) μ → Integrable h μ →
    (((d:ℝ)+2)/(L:ℝ))*(∫ z, shapeEnergyAt (stem OldNode r) d (K z) (f z) ∂μ) ≤
      2*(2*(L:ℝ)⁻¹ + |matrixRootCovariance μ Ω Target S q K m (v::cs) x A
          (fun z => treeOverlap S (f z))|/|J|+
        (2*(∫ z, Real.sqrt (W' z) ∂μ)+(∫ z, h z ∂μ))*shiftedCharge B Target S (v::cs).length/|J|+
        pairHistoryMass S m x*(2*(∫ z, Real.sqrt (W z) ∂μ)))+
      (((d:ℝ)+2)/(L:ℝ))*(16*(∫ z, W z ∂μ)) := by
  dsimp only
  intro b b' q0 hq u v huv hu hv B hS cs hcs hdis hfull
    hV hTriple hHistory hTarget hOld hMean hW hSqrtW hSqrtNew hShift
  let ht := shiftedFrameHeight H r d
  let L := H+1+1+r+1+d
  let OldChild := fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val)
  let NewChild := fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
  let RawTarget := splitFrame (.node k NewChild) (r+1) d
  let Target := heightCast ht RawTarget
  let q := fun j => leafHeightCast ht RawTarget (q0 j)
  let S := splitFrame (.node k OldChild) r d
  let X := fun z x i => splitProjector (.node k OldChild) r d (K z) (fun y => f z y i) x
  let A := fun z => spatialProduct (fun _ : I => f z)
  let W' := fun z => (k:ℝ)*∑ j, Real.sqrt (descendantEnergyAt (NewChild j) (r+1) d
    (kernelHeightCast ht.symm (K z)) (vectorHeightCast ht.symm (f z)))
  let h := fun z => projectionShiftError a C e (K z) (f z) Q
  have hq' : Function.Bijective q := (leafHeightCast_bijective ht RawTarget).comp hq
  have hqd : splitDepth Target (q u) (q v)=d := by
    rw [splitDepth_heightCast,hu,hv]
    exact splitFrame_split (.node k NewChild) (r+1) d b'
  have hbase := root_multileaf_matrix μ Ω k OldChild b r d Target q hq' B hS K u v huv
    cs hcs hdis hfull hqd f hf hV hTriple hHistory hTarget hOld hMean hW hSqrtW
  have hproj : (∫ z, matrixProjectionError Target q (K z) u v (A z) (X z) ∂μ) ≤
      2*(∫ z, Real.sqrt (W' z) ∂μ)+(∫ z, h z ∂μ) := by
    have hle := integral_mono hTarget ((hSqrtNew.const_mul 2).add hShift) (fun z =>
      scheduled_frame_target_error_le H r d k hk a C e Q ha hQ (K z) (f z) (hf z) b' q0 hq u v hu hv)
    change (∫ z, matrixProjectionError Target q (K z) u v (A z) (X z) ∂μ) ≤
      (∫ z, 2*Real.sqrt (W' z)+h z ∂μ) at hle
    rw [integral_add (hSqrtNew.const_mul 2) hShift,integral_const_mul] at hle
    exact hle
  have hcharge : 0 ≤ shiftedCharge B Target S (v::cs).length := by
    unfold shiftedCharge
    exact mul_nonneg (chargeBound_nonneg (by positivity) (by positivity) _ _) (by positivity)
  have hproj' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hproj hcharge)
    (abs_nonneg (partialKappa Target (grid L 0 L) (Finset.univ.image q)/
      partialKappa Target (grid L 0 L) ((insert v ({u}:Finset I)).image q)))
  exact hbase.trans (add_le_add (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add le_rfl hproj') le_rfl) (by norm_num)) le_rfl)

end DilutedSpinGlass.ReducedTopology
end

end

section
section
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory _root_.OAI.MeasureTheory DepthAverage
open scoped BigOperators
noncomputable local instance scheduledRootMultileafDecidableEq (type : Type) :
    DecidableEq type := Classical.decEq type
noncomputable local instance scheduledRootMultileafDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

/-- The literal single-copy depth domain: one evaluation coordinate, the
branching coordinates, their strict ancestry and the regular interior cube. -/
def regularShapeDomain (S : ReducedTopology) (L : ℕ) [NeZero L] (η : ℝ)
    (Q : Option S.Vertex → Fin L) : Prop :=
  Regular η Q ∧ Admissible S (fun v => (Q (some v)).val) ((Q none).val+1) L

/-- A proper child retains the first branching coordinate as its evaluation
coordinate, and precisely its own internal branching coordinates. -/
def childCoordinates {k : ℕ+} {hk : 2≤(k:ℕ)} {C : Fin k → ReducedTopology}
    (j : Fin k) : Option (C j).Vertex → Option (ReducedTopology.node k hk C).Vertex
  | none => some none
  | some v => some (some ⟨j,v⟩)

lemma childCoordinates_injective {k : ℕ+} {hk : 2≤(k:ℕ)} {C : Fin k → ReducedTopology}
    (j : Fin k) : Function.Injective (childCoordinates (hk := hk) (C := C) j) := by
  intro x y h
  cases x <;> cases y <;> simp_all [childCoordinates]

lemma admissible_shift_same_upper (S : ReducedTopology) (q : S.Vertex → ℕ)
    {lo L : ℕ} (ha : Admissible S q lo L) (hr : ∀ v, q v+1<L) :
    Admissible S (fun v => q v+1) (lo+1) L := by
  induction S generalizing lo with
  | leaf => trivial
  | node k hk C ih =>
    refine ⟨by change lo+1 ≤ q none+1; have hh := ha.1; omega,hr none,?_⟩
    intro j
    exact ih j _ (ha.2.2 j) (fun v => hr (some ⟨j,v⟩))

/-- Both the old and all-coordinates-delayed proper child lie in the SAME
admissible regular domain. Rotation is genuinely +1 here: no wraparound is
silently admitted at the terminal level. -/
theorem regular_child_projection {L : ℕ} [NeZero L] {η : ℝ}
    (hη : 0<η) (hlarge : 4<η*(L:ℝ))
    {k : ℕ+} {hk : 2≤(k:ℕ)} {C : Fin k → ReducedTopology}
    (j : Fin k) (s : Bool) {Q : Option (ReducedTopology.node k hk C).Vertex → Fin L}
    (hQ : regularShapeDomain (.node k hk C) L η Q) :
    regularShapeDomain (C j) L (η/2)
      (coordinateProjection (childCoordinates (hk := hk) j) (fun _ => shiftPerm s) Q) := by
  refine ⟨regular_shift_restrict hη hlarge _ (childCoordinates_injective j) (fun _ => s) hQ.1,?_⟩
  have ha := hQ.2.2.2 j
  cases s with
  | false => simpa only [coordinateProjection,shiftPerm,Bool.false_eq_true,ite_false,
      Equiv.refl_apply,childCoordinates] using ha
  | true =>
    have hroom : ∀ v : Option (ReducedTopology.node k hk C).Vertex, (Q v).val+1<L :=
      regular_room (by linarith : 1<η*(L:ℝ)) hQ.1
    have hh := admissible_shift_same_upper (C j) _ ha
      (fun v => hroom (some (some ⟨j,v⟩)))
    simpa only [coordinateProjection,shiftPerm,ite_true,childCoordinates,
      rotate_val_of_room _ (hroom _)] using hh

 
theorem regular_scheduled_child_moment {Z : Type} [MeasurableSpace Z]
    (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)] {L N : ℕ} [NeZero L]
    (T : (z : Z) → KernelTower (Ω z) L)
    (f : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ)
    {η : ℝ} (hη : 0<η) (hlarge : 4<η*(L:ℝ))
    (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology) (s : Bool) :
    let F := fun (j : Fin k) (q : Option (C j).Vertex → Fin L) =>
      ∫ z, scheduledShapeEnergy L (q none).val (C j) (fun v => (q (some v)).val) (T z) (f z) ∂μ
    average (regularShapeDomain (.node k hk C) L η)
      (fun Q => Real.sqrt ((k:ℝ)*∑ j, Real.sqrt
        (F j (coordinateProjection (childCoordinates (hk := hk) j) (fun _ => shiftPerm s) Q)))) ≤
      Real.sqrt ((k:ℝ)*∑ j, Real.sqrt (average (regularShapeDomain (C j) L (η/2)) (F j))) := by
  dsimp only
  refine fiber_child_moment_bound (k:ℝ) (by positivity)
    (fun j => childCoordinates (hk := hk) j) (fun j => childCoordinates_injective j)
    (fun _ _ => shiftPerm s) (regularShapeDomain (.node k hk C) L η)
    (fun j => regularShapeDomain (C j) L (η/2)) ?_
    (fun j q => ∫ z, scheduledShapeEnergy L (q none).val (C j)
      (fun v => (q (some v)).val) (T z) (f z) ∂μ) ?_
  · intro j Q hQ
    exact regular_child_projection hη hlarge j s hQ
  · intro j q
    exact integral_nonneg (fun z => scheduledShapeEnergy_nonneg _ _ _ _ _)

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
