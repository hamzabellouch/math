import OAI.Probability.DilutedSpin.RegularNodeEstimates

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology
open scoped NNReal BigOperators
noncomputable local instance (β : Type) : DecidableEq β := Classical.decEq β
variable {p : ℕ}
attribute [local irreducible] projectionShiftError matrixProjectionError oldProjectionError
    matrixObservableHistory KernelTower.halfTripleDifferenceAt splitProjector

/-- On every regular admissible parent assignment there is one literal signed
matrix experiment. Its geometry is fixed before the physical size and probe
parameters are chosen, and its charging constants are independent of the grid.
This is the pointwise producer for the averaged decorrelation induction. -/
theorem regular_node_pointwise (M : Model p) (θB hB : ℝ) (L : ℕ)
    (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    {η : ℝ} (hη : 0<η) (hlarge : 1<η*(L+1:ℕ))
    (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1))
    (hQ : regularShapeDomain (.node k hk C) (L+1) η Q) :
    ∃ (S T : PrescribedTree (L+1)) (a : S.Leaf)
      (q : Option (Fin (2*Fintype.card (ReducedTopology.node k hk C).Leaf-2+1)) → T.Leaf)
      (J : ℝ), ∀ (N : ℕ) (u : Spec L × ℕ → ℝ),
    η*physicalScheduledEnergy M θB hB N L u (.node k hk C) Q ≤
      4*((L+1:ℕ):ℝ)⁻¹ +
      2*(|physicalTreeMatrixCovariance (gridExponents L) S a M θB hB N u T q|/|J|) +
      4*nodeChargeConstant k hk C η*Real.sqrt (physicalChildMass M θB hB N L u k hk C true Q) +
      2*nodeChargeConstant k hk C η*physicalNodeShift M θB hB N L u k hk C Q +
      (4*(nodeHistoryBudget k hk C:ℝ)+16*(k:ℝ))*
        Real.sqrt (physicalChildMass M θB hB N L u k hk C false Q) := by
  obtain ⟨H,r,d,hL,hd,he,had⟩ := regular_node_frame hη hlarge k hk C Q hQ
  have hL' : L=H+1+1+r+1+d := by omega
  subst L
  let L₀ := H+1+1+r+1+d
  let t := 2*Fintype.card (ReducedTopology.node k hk C).Leaf-2
  let OldNode := PrescribedTree.node k (fun j => realize (H+1) (r+1+(d+1)+1) (C j)
    (fun v => (Q (some (some ⟨j,v⟩))).val))
  let NewNode := PrescribedTree.node k (fun j => realize H (r+1+1+(d+1)+1) (C j)
    (fun v => (Q (some (some ⟨j,v⟩))).val+1))
  let BaseNode := PrescribedTree.node k (fun j => realize H (r+1+(d+1)+1) (C j)
    (fun v => (Q (some (some ⟨j,v⟩))).val))
  let S := splitFrame OldNode r (d+1)
  let RawTarget := splitFrame NewNode (r+1) (d+1)
  let ht := shiftedFrameHeight H r (d+1)
  let T := heightCast ht RawTarget
  obtain ⟨b⟩ := leaf_nonempty OldNode
  have hlabel := delayed_node_protected_labeling H (r+1+(d+1)+1) (r+1) (d+1) k hk C
    (fun j v => (Q (some (some ⟨j,v⟩))).val) had
  dsimp only at hlabel
  rw [show r+1+(d+1)+1+1=r+1+1+(d+1)+1 by omega] at hlabel
  obtain ⟨b',q₀,hq₀,hq₁⟩ := hlabel
  let q : Option (Fin (t+1)) → T.Leaf := fun i => leafHeightCast ht RawTarget (q₀ i)
  let a : S.Leaf := splitFrameLeaf OldNode r (d+1) 0 b
  let v : Option (Fin (t+1)) := some (Fin.last t)
  let m : Fin (L₀+2) → ℝ := Fin.cons 0 (gridExponents L₀)
  let J := partialKappa T m (Finset.univ.image q)/partialKappa T m ((insert v ({none}:Finset _)).image q)
  refine ⟨S,T,a,q,J,?_⟩
  intro N u
  have hstep := physical_grid_scheduled_step M θB hB N H r d u k hk (some none) C
    (fun j => childBranchCoordinates (hk := hk) j) Q he had hlarge hQ.1
    b b' q₀ q₀.bijective hq₀ hq₁
  dsimp only at hstep
  have hroom := DepthAverage.regular_room hlarge hQ.1
  have hrot (i : Option (ReducedTopology.node k hk C).Vertex) :
      ((finRotate (L₀+1)) (Q i)).val=(Q i).val+1 :=
    DepthAverage.rotate_val_of_room _ (hroom i)
  have hparent : (fun v => (Q (some v)).val) =
      rootSchedule (hk := hk) (r+1+(d+1)) (fun j v => (Q (some (some ⟨j,v⟩))).val) := by
    funext v
    cases v with
    | none => exact he
    | some v => rfl
  have henergy : physicalScheduledEnergy M θB hB N L₀ u (.node k hk C) Q =
      ∫ z, scheduledShapeEnergy (L₀+1) (d+1) (.node k hk C)
        (rootSchedule (r+1+(d+1)) (fun j v => (Q (some (some ⟨j,v⟩))).val))
        (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L₀)
          (fun i : Labels L₀ (Site N) => prior i.1.1) (gridExponents L₀) (physicalBase M θB hB N)
          (dictionaryFactor (observableAt direction N) (observableAt anchor N) u) z)
        (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L₀ x) v))
          (I := Labels L₀ (Site N)) (A := fun i => Alphabet i.1.1) (X := Bond p N) (Y := ℝ) (M := N) z)
        ∂fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
          (markLaw (weights L₀) N) (M.alpha*N) (scoreRate N) := by
    unfold physicalScheduledEnergy
    rw [hd,hparent]
  have hchild (s : Bool) : physicalChildMass M θB hB N L₀ u k hk C s Q =
      (k:ℝ)*∑ j, Real.sqrt (∫ z, scheduledShapeEnergy (L₀+1)
        (r+1+(d+1)+(if s then 1 else 0)) (C j)
        (fun v => (Q (some (some ⟨j,v⟩))).val+(if s then 1 else 0))
        (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L₀)
          (fun i : Labels L₀ (Site N) => prior i.1.1) (gridExponents L₀) (physicalBase M θB hB N)
          (dictionaryFactor (observableAt direction N) (observableAt anchor N) u) z)
        (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L₀ x) v))
          (I := Labels L₀ (Site N)) (A := fun i => Alphabet i.1.1) (X := Bond p N) (Y := ℝ) (M := N) z)
        ∂fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
          (markLaw (weights L₀) N) (M.alpha*N) (scoreRate N)) := by
    cases s <;> simp only [physicalChildMass,physicalScheduledEnergy,
      DepthAverage.coordinateProjection,childCoordinates,DepthAverage.shiftPerm,
      Bool.false_eq_true,ite_false,ite_true,Equiv.refl_apply,hrot,
      he,Nat.add_zero]
  have hold := hchild false
  have hnew := hchild true
  simp only [Bool.false_eq_true,ite_false,Nat.add_zero] at hold
  simp only [ite_true,show r+1+(d+1)+1=r+1+1+(d+1) by omega] at hnew
  have hg : m = grid (L₀+1) 0 (L₀+1) := gridExponents_cons L₀
  have hbij : Function.Bijective q := (leafHeightCast_bijective ht RawTarget).comp q₀.bijective
  have hfirst : η≤((d+1+r+2:ℕ):ℝ)/((H+1+1+r+1+(d+1):ℕ):ℝ) := by
    have hx := (hQ.1.1 (some none)).1.le
    dsimp only [DepthAverage.normalized] at hx
    rw [he] at hx
    exact hx.trans (div_le_div_of_nonneg_right (by exact_mod_cast (show r+1+(d+1)≤d+1+r+2 by omega)) (by positivity))
  have hcharge := node_frame_charge_uniform H r (d+1) k hk (some none) C
    (fun j => childBranchCoordinates (hk := hk) j) Q had hη hfirst q hbij none v (by simp [v])
  have hpair : pairHistoryMass S m a ≤ (nodeHistoryBudget k hk C:ℝ) := by
    rw [hg,pairHistoryMass_grid (L := L₀+1) (by omega) S a]
    dsimp only [S]
    rw [leaves_splitFrame,node_old_realize_leaves H (r+1+(d+1)+1) k hk C _ had]
    unfold nodeHistoryBudget
    push_cast
    linarith
  have hc : η≤(((d+1:ℕ):ℝ)+2)/((L₀+1:ℕ):ℝ) := by
    have hx := (hQ.1.1 none).1.le
    dsimp only [DepthAverage.normalized] at hx
    rw [hd] at hx
    exact hx.trans (div_le_div_of_nonneg_right (by linarith) (by positivity))
  have hc1 : (((d+1:ℕ):ℝ)+2)/((L₀+1:ℕ):ℝ)≤1 := by
    apply (div_le_one (by positivity)).mpr
    dsimp only [L₀]
    push_cast
    linarith
  change _ ≤ 2*(2*((L₀+1:ℕ):ℝ)⁻¹+
      |physicalTreeMatrixCovariance (gridExponents L₀) S a M θB hB N u T q|/|J|+
      (2*Real.sqrt _ + physicalNodeShift M θB hB N L₀ u k hk C Q)*
        shiftedCharge (shiftedPrefixDepths (stem BaseNode r) (d+1)) T S
          (v::canonicalMatrixTail t).length/|J|+
      pairHistoryMass S m a*(2*Real.sqrt _)) + _ at hstep
  dsimp only [childBranchCoordinates] at hstep
  rw [← henergy,← hold,← hnew] at hstep
  rw [List.length_cons,canonicalMatrixTail_length] at hstep
  have hcharge' : shiftedCharge (shiftedPrefixDepths (stem BaseNode r) (d+1)) T S (t+1)/|J| ≤
      nodeChargeConstant k hk C η := by
    simp only [J,hg]
    convert hcharge using 1
    dsimp only [childBranchCoordinates,BaseNode,T,S,t,RawTarget,NewNode,OldNode,L₀]
    congr 4
  have hs := multileaf_scalar_bound
    (δ := ((L₀+1:ℕ):ℝ)⁻¹)
    (err := |physicalTreeMatrixCovariance (gridExponents L₀) S a M θB hB N u T q|/|J|)
    (w' := physicalChildMass M θB hB N L₀ u k hk C true Q) hc hc1
    (physicalScheduledEnergy_nonneg M θB hB N L₀ u _ Q)
    (physicalChildMass_nonneg M θB hB N L₀ u k hk C false Q)
    (physicalNodeShift_nonneg M θB hB N L₀ u k hk C Q) hcharge' hpair
    (physicalChildMass_le_sqrt M θB hB N L₀ u k hk C false Q) (by
      convert hstep using 1
      ring)
  exact hs

end DilutedSpinGlass.UniversalDictionary

end

end OAI
