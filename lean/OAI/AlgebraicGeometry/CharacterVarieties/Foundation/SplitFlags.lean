import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.VertexFrames

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
variable {R : Type*} [CommRing R]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

@[simp] lemma linearEquiv_congr_apply (e : α ≃ β) (x : α → R) (j : β) :
    (congr (R:=R) e).linearEquiv x j = x (e.symm j) := by
  change ∑ i, ((1 : Matrix β β R) j (e i)) * x i = _
  have he (i : α) : (j=e i) ↔ (i=e.symm j) := by
    constructor
    · intro h; rw [h,e.symm_apply_apply]
    · intro h; rw [h,e.apply_symm_apply]
  simp [Matrix.one_apply,he]

@[simp] lemma linearEquiv_congr_symm_apply (e : α ≃ β) (x : β → R) (j : α) :
    (congr (R:=R) e).linearEquiv.symm x j = x (e j) := by
  change ∑ i, ((1 : Matrix β β R) (e j) i) * x i = _
  simp [Matrix.one_apply]

@[simp] lemma linearEquiv_trans_apply (f : MatrixIso R α β) (g : MatrixIso R β γ)
    (x : α → R) : (f.trans g).linearEquiv x=g.linearEquiv (f.linearEquiv x) := by
  change (g.val*f.val)*ᵥ x=g.val*ᵥ (f.val*ᵥ x)
  exact (Matrix.mulVec_mulVec _ _ _).symm

@[simp] lemma linearEquiv_diagonal_apply (u : α → Rˣ) (x : α → R) (j : α) :
    (diagonal u).linearEquiv x j=(u j : R)*x j := by
  change (Matrix.diagonal (fun i => (u i:R))*ᵥ x) j=_
  simp [Matrix.mulVec,Matrix.diagonal,dotProduct]

@[simp] lemma linearEquiv_trans_symm_apply (f : MatrixIso R α β) (g : MatrixIso R β γ)
    (x : γ → R) :
    (f.trans g).linearEquiv.symm x=f.linearEquiv.symm (g.linearEquiv.symm x) := by
  change (f.inv*g.inv)*ᵥ x=f.inv*ᵥ (g.inv*ᵥ x)
  exact (Matrix.mulVec_mulVec _ _ _).symm

@[simp] lemma linearEquiv_diagonal_symm_apply (u : α → Rˣ) (x : α → R) (j : α) :
    (diagonal u).linearEquiv.symm x j=(((u j)⁻¹ : Rˣ):R)*x j := by
  change (Matrix.diagonal (fun i => (((u i)⁻¹:Rˣ):R))*ᵥ x) j=_
  simp [Matrix.mulVec,Matrix.diagonal,dotProduct]

end IntegralCharacterVarieties.MatrixIso

namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
variable {R : Type*} [CommRing R]
variable {α β α' β' : Type*} [Fintype α] [Fintype β] [Fintype α'] [Fintype β']

@[simp] theorem linearEquiv_reindex (f : MatrixIso R α β) (a : α' ≃ α) (b : β' ≃ β)
    (x : α' → R) (j : β') :
    (f.reindex a b).linearEquiv x j=f.linearEquiv (fun i => x (a.symm i)) (b j) := by
  change (∑ i, f.val (b j) (a i)*x i)=∑ i,f.val (b j) i*x (a.symm i)
  rw [←a.sum_comp]
  simp only [Equiv.symm_apply_apply]

@[simp] theorem linearEquiv_sum_inl (f : MatrixIso R α β) (g : MatrixIso R α' β')
    (x : α ⊕ α' → R) (j : β) :
    (f.sum g).linearEquiv x (.inl j)=f.linearEquiv (fun i => x (.inl i)) j := by
  change ∑ i, (Matrix.fromBlocks f.val 0 0 g.val) (.inl j) i*x i=_
  rw [Fintype.sum_sum_type]
  simp [Matrix.fromBlocks,MatrixIso.linearEquiv,Matrix.toLin'_apply,Matrix.mulVec,dotProduct]

@[simp] theorem linearEquiv_sum_inr (f : MatrixIso R α β) (g : MatrixIso R α' β')
    (x : α ⊕ α' → R) (j : β') :
    (f.sum g).linearEquiv x (.inr j)=g.linearEquiv (fun i => x (.inr i)) j := by
  change ∑ i, (Matrix.fromBlocks f.val 0 0 g.val) (.inr j) i*x i=_
  rw [Fintype.sum_sum_type]
  simp [Matrix.fromBlocks,MatrixIso.linearEquiv,Matrix.toLin'_apply,Matrix.mulVec,dotProduct]
end IntegralCharacterVarieties.MatrixIso

namespace IntegralCharacterVarieties
variable {R V α : Type*} [CommRing R] [AddCommGroup V] [Module R V]
lemma mem_framedPrefix (grade : α → ℕ) (E : (α → R) ≃ₗ[R] V) (k : ℕ) (v : V) :
    v∈framedPrefix grade E k ↔ E.symm v∈coordinatePrefix R grade k := by
  exact Submodule.mem_map_equiv (coordinatePrefix R grade k) (e:=E) (x:=v)
end IntegralCharacterVarieties

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
open scoped Classical Matrix
variable {R : Type*} [CommRing R] {a b c : ℕ}
  (d : LocalRanks (.splitting a b c false))
local instance : Fintype (d.Columns .before) := d.fintypeColumns .before
local instance : Fintype (d.Columns .after) := d.fintypeColumns .after
local instance : Fintype (d.Columns .branch) := d.fintypeColumns .branch

def coarseW (v : d.Columns .before → R) (j : d.Parent .branch) : R :=
  v ⟨.inr (.inl ()),d.splitBranchParent.symm j⟩

def fineW (v : d.Columns .after → R) (j : d.Columns .branch) : R :=
  v ⟨.inr (.inl (d.splitBranchChildren.symm j).1),(d.splitBranchChildren.symm j).2⟩

variable (w : MatrixIso R (d.Columns .branch) (d.Parent .branch))

theorem refinement_coarseW (v : d.Columns .after → R) :
    d.coarseW ((d.splitRefinement w).linearEquiv v)=w.linearEquiv (d.fineW v) := by
  funext j
  simp only [coarseW,splitRefinement,MatrixIso.linearEquiv_reindex,
    splitBefore,Equiv.coe_fn_mk,MatrixIso.linearEquiv_sum_inr,
    MatrixIso.linearEquiv_sum_inl,Equiv.apply_symm_apply]
  rfl

theorem refinement_prefix (v : d.Columns .after → R) (j : d.SplitA false) :
    (d.splitRefinement w).linearEquiv v ⟨.inl j.1,j.2⟩=
      v ⟨.inl (d.splitPrefix.symm j).1,(d.splitPrefix.symm j).2⟩ := by
  simp only [splitRefinement,MatrixIso.linearEquiv_reindex,splitBefore,
    Equiv.coe_fn_mk,MatrixIso.linearEquiv_sum_inl,MatrixIso.linearEquiv_congr_apply]
  rfl

theorem refinement_suffix (v : d.Columns .after → R) (j : d.SplitC false) :
    (d.splitRefinement w).linearEquiv v ⟨.inr (.inr j.1),j.2⟩=
      v ⟨.inr (.inr (d.splitSuffix.symm j).1),(d.splitSuffix.symm j).2⟩ := by
  simp only [splitRefinement,MatrixIso.linearEquiv_reindex,splitBefore,
    Equiv.coe_fn_mk,MatrixIso.linearEquiv_sum_inr,MatrixIso.linearEquiv_congr_apply]
  rfl

/-- Source-order grades, not an arbitrary enumeration. -/
def beforeGrade (z : d.Columns .before) : ℕ :=
  ((Kind.splitting a b c false).childEnumeration .before z.1).val
def afterGrade (z : d.Columns .after) : ℕ :=
  ((Kind.splitting a b c false).childEnumeration .after z.1).val
def branchGrade (z : d.Columns .branch) : ℕ := z.1.val

@[simp] theorem beforeGrade_prefix (z : d.SplitA false) :
    d.beforeGrade ⟨.inl z.1,z.2⟩=z.1.val := rfl
@[simp] theorem beforeGrade_middle (z : d.SplitW) :
    d.beforeGrade ⟨.inr (.inl ()),z⟩=a := by
  change a+((_:Fin 1).val) = a
  omega
@[simp] theorem beforeGrade_suffix (z : d.SplitC false) :
    d.beforeGrade ⟨.inr (.inr z.1),z.2⟩=a+1+z.1.val := by
  change a+(1+z.1.val)=_
  omega
@[simp] theorem afterGrade_prefix (z : d.SplitA true) :
    d.afterGrade ⟨.inl z.1,z.2⟩=z.1.val := rfl
@[simp] theorem afterGrade_middle (z : d.SplitB) :
    d.afterGrade ⟨.inr (.inl z.1),z.2⟩=a+z.1.val := rfl
@[simp] theorem afterGrade_suffix (z : d.SplitC true) :
    d.afterGrade ⟨.inr (.inr z.1),z.2⟩=a+b+z.1.val := by
  change a+(b+z.1.val)=_
  omega


theorem current_iff (v : d.Columns .before → R) :
    v∈coordinatePrefix R d.beforeGrade (a+1) ↔
      ∀ z : d.SplitC false, v ⟨.inr (.inr z.1),z.2⟩=0 := by
  constructor
  · intro hv z
    apply hv
    rw [d.beforeGrade_suffix]
    omega
  · intro hv ⟨z,k⟩ hz
    rcases z with i|u|i
    · have hi := i.isLt
      change a+1 ≤ i.val at hz
      omega
    · cases u
      rw [d.beforeGrade_middle] at hz
      omega
    · exact hv ⟨i,k⟩

theorem afterPrefix_iff (v : d.Columns .after → R) (j : ℕ) (hj : j≤b) :
    v∈coordinatePrefix R d.afterGrade (a+j) ↔
      (∀ z : d.SplitC true, v ⟨.inr (.inr z.1),z.2⟩=0) ∧
      d.fineW v∈coordinatePrefix R d.branchGrade j := by
  constructor
  · intro hv
    constructor
    · intro z
      apply hv
      rw [d.afterGrade_suffix]
      omega
    · intro z hz
      apply hv
      rw [d.afterGrade_middle]
      change j≤z.1.val at hz
      change a+j≤a+z.1.val
      omega
  · rintro ⟨hC,hW⟩ ⟨z,k⟩ hz
    rcases z with i|i|i
    · have hi := i.isLt
      change a+j ≤ i.val at hz
      omega
    · have hh := hW (d.splitBranchChildren ⟨i,k⟩)
      change a+j ≤ a+i.val at hz
      apply hh
      change j ≤ i.val
      omega
    · exact hC ⟨i,k⟩

theorem refinement_current_iff (v : d.Columns .after → R) :
    (d.splitRefinement w).linearEquiv v∈coordinatePrefix R d.beforeGrade (a+1) ↔
      ∀ z : d.SplitC true, v ⟨.inr (.inr z.1),z.2⟩=0 := by
  rw [d.current_iff]
  simp only [d.refinement_suffix]
  constructor
  · intro h z
    specialize h (d.splitSuffix z)
    exact (congrArg (fun z : d.SplitC true => v ⟨.inr (.inr z.1),z.2⟩)
      (d.splitSuffix.symm_apply_apply z)).symm.trans h
  · intro h z
    exact h _

/-- At the split matrix, the refined interval flag is the inverse image of the additional seam flag
INSIDE the old coarse W interval. -/
theorem refinement_flag_iff (v : d.Columns .after → R) (j : ℕ) (hj : j≤b) :
    v∈coordinatePrefix R d.afterGrade (a+j) ↔
      (d.splitRefinement w).linearEquiv v∈coordinatePrefix R d.beforeGrade (a+1) ∧
      d.coarseW ((d.splitRefinement w).linearEquiv v)∈
        framedPrefix d.branchGrade w.linearEquiv j := by
  rw [d.afterPrefix_iff v j hj,d.refinement_current_iff]
  rw [d.refinement_coarseW]
  change _ ↔ _ ∧ w.linearEquiv (d.fineW v)∈
    (coordinatePrefix R d.branchGrade j).map w.linearEquiv.toLinearMap
  rw [Submodule.mem_map_equiv,LinearEquiv.symm_apply_apply]

variable (f : ∀ p,MatrixIso R (d.Columns p) (d.Parent p))

def beforeParentFrame : MatrixIso R (d.Columns .before) (d.Parent .after) :=
  (f .before).reindex (Equiv.refl _) d.splitParent

theorem rightFrame_eq :
    (d.splitComparison f).right=
      (d.splitRefinement (f .branch)).trans (d.beforeParentFrame f) := by
  apply MatrixIso.ext <;> rfl

theorem rightFrame_formula (v : d.Columns .after → R) :
    (d.splitComparison f).right.linearEquiv v=
      (d.beforeParentFrame f).linearEquiv ((d.splitRefinement (f .branch)).linearEquiv v) := by
  rw [d.rightFrame_eq f]
  exact MatrixIso.linearEquiv_trans_apply _ _ _

variable (h : (d.splitComparison f).Holds)

include h in
/-- The equality below is derived from the source comparison itself. -/
theorem old_refined_flag (v : d.Parent .after → R) (j : ℕ) (hj : j≤b) :
    v∈framedPrefix d.afterGrade (f .after).linearEquiv (a+j) ↔
      v∈framedPrefix d.beforeGrade (d.beforeParentFrame f).linearEquiv (a+1) ∧
      d.coarseW ((d.beforeParentFrame f).linearEquiv.symm v)∈
        framedPrefix d.branchGrade (f .branch).linearEquiv j := by
  have he := h.1 (a+j)
  change framedPrefix d.afterGrade (f .after).linearEquiv (a+j)=
    framedPrefix d.afterGrade (d.splitComparison f).right.linearEquiv (a+j) at he
  let x : d.Columns .after → R := (d.splitComparison f).right.linearEquiv.symm v
  have hx : (d.beforeParentFrame f).linearEquiv.symm v=
      (d.splitRefinement (f .branch)).linearEquiv x := by
    apply (d.beforeParentFrame f).linearEquiv.injective
    exact ((d.beforeParentFrame f).linearEquiv.apply_symm_apply v).trans
      (((d.splitComparison f).right.linearEquiv.apply_symm_apply v).symm.trans
        (d.rightFrame_formula f x))
  have hp := mem_framedPrefix d.afterGrade (d.splitComparison f).right.linearEquiv (a+j) v
  have hq := mem_framedPrefix d.beforeGrade (d.beforeParentFrame f).linearEquiv (a+1) v
  constructor
  · intro hv
    have hh := (d.refinement_flag_iff (f .branch) x j hj).mp (hp.mp (he ▸ hv))
    exact ⟨hq.mpr (hx.symm ▸ hh.1),hx.symm ▸ hh.2⟩
  · rintro ⟨hv,hw⟩
    have hh := (d.refinement_flag_iff (f .branch) x j hj).mpr
      ⟨hx ▸ hq.mp hv,hx ▸ hw⟩
    exact he.symm ▸ hp.mpr hh


def branchProjection : (d.Parent .after → R) →ₗ[R] (d.Parent .branch → R) where
  toFun v := d.coarseW ((d.beforeParentFrame f).linearEquiv.symm v)
  map_add' v z := by ext i; simp [coarseW]
  map_smul' t v := by ext i; simp [coarseW]


theorem right_branch_coordinates (v : d.Parent .after → R) :
    d.fineW ((d.splitComparison f).right.linearEquiv.symm v)=
      (f .branch).linearEquiv.symm (d.branchProjection f v) := by
  apply (f .branch).linearEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  let x : d.Columns .after → R := (d.splitComparison f).right.linearEquiv.symm v
  have hx : (d.beforeParentFrame f).linearEquiv.symm v=
      (d.splitRefinement (f .branch)).linearEquiv x := by
    apply (d.beforeParentFrame f).linearEquiv.injective
    exact ((d.beforeParentFrame f).linearEquiv.apply_symm_apply v).trans
      (((d.splitComparison f).right.linearEquiv.apply_symm_apply v).symm.trans
        (d.rightFrame_formula f x))
  exact (d.refinement_coarseW (f .branch) x).symm.trans
    (congrArg d.coarseW hx.symm)

include h in
/-- Every named fine quotient coordinate agrees with the old branch frame. This uses the GRADED
clause of the old vertex equation. -/
theorem old_branch_grade (z : d.Columns .branch) (v : d.Parent .after → R)
    (hv : v∈framedPrefix d.afterGrade (f .after).linearEquiv (a+z.1.val+1)) :
    d.fineW ((f .after).linearEquiv.symm v) z=
      (f .branch).linearEquiv.symm (d.branchProjection f v) z := by
  have hz : d.afterGrade
      ⟨.inr (.inl (d.splitBranchChildren.symm z).1),(d.splitBranchChildren.symm z).2⟩=
      a+z.1.val := rfl
  have hg := congrFun (h.2 (a+z.1.val) v hv)
    ⟨⟨.inr (.inl (d.splitBranchChildren.symm z).1),(d.splitBranchChildren.symm z).2⟩,hz⟩
  exact hg.trans (congrFun (d.right_branch_coordinates f v) z)

def branchSubsystem (U : Submodule R (d.Parent .after → R)) :
    Submodule R (d.Parent .branch → R) :=
  (U ⊓ framedPrefix d.beforeGrade (d.beforeParentFrame f).linearEquiv (a+1)).map
    (d.branchProjection f)

include h in
/-- The branch subsystem's entire fine flag is obtained from the old U intersection flag, in the
named additional-seam module. -/
theorem old_branch_intersections (U : Submodule R (d.Parent .after → R))
    (j : ℕ) (hj : j≤b) :
    (U ⊓ framedPrefix d.afterGrade (f .after).linearEquiv (a+j)).map
        (d.branchProjection f)=
      d.branchSubsystem f U ⊓ framedPrefix d.branchGrade (f .branch).linearEquiv j := by
  ext z
  constructor
  · rintro ⟨v,⟨hU,hv⟩,rfl⟩
    have hh := (d.old_refined_flag f h v j hj).mp hv
    exact ⟨⟨v,⟨hU,hh.1⟩,rfl⟩,hh.2⟩
  · rintro ⟨⟨v,⟨hU,hv⟩,rfl⟩,hz⟩
    exact ⟨v,⟨hU,(d.old_refined_flag f h v j hj).mpr ⟨hv,hz⟩⟩,rfl⟩

/-- The output records the exact source prefix criterion together with all U intersection images,
rather than only relative-position dimensions. -/
def HasOldSplit : Prop :=
  (∀ (v : d.Parent .after → R) (j : ℕ), j≤b →
    (v∈framedPrefix d.afterGrade (f .after).linearEquiv (a+j) ↔
      v∈framedPrefix d.beforeGrade (d.beforeParentFrame f).linearEquiv (a+1) ∧
      d.branchProjection f v∈framedPrefix d.branchGrade (f .branch).linearEquiv j)) ∧
  (∀ (U : Submodule R (d.Parent .after → R)) (j : ℕ), j≤b →
    (U ⊓ framedPrefix d.afterGrade (f .after).linearEquiv (a+j)).map
        (d.branchProjection f)=
      d.branchSubsystem f U ⊓ framedPrefix d.branchGrade (f .branch).linearEquiv j) ∧
  ∀ (z : d.Columns .branch) (v : d.Parent .after → R),
    v∈framedPrefix d.afterGrade (f .after).linearEquiv (a+z.1.val+1) →
    d.fineW ((f .after).linearEquiv.symm v) z=
      (f .branch).linearEquiv.symm (d.branchProjection f v) z

include h in
theorem old_split_flags : d.HasOldSplit f :=
  ⟨d.old_refined_flag f h,d.old_branch_intersections f h,d.old_branch_grade f h⟩

def OldSplitExtracted (R : Type*) [CommRing R] : (k : Kind) → (d : LocalRanks k) →
    (∀ p, MatrixIso R (d.Columns p) (d.Parent p)) → Prop
  | .passage _ _,_,_ => True
  | .splitting _ _ _ false,d,f => d.HasOldSplit f
  | .splitting _ _ _ true,d,f => d.forwardRanks.HasOldSplit f

theorem comparison_oldSplit {k : Kind} (d : LocalRanks k)
    (f : ∀ p,MatrixIso R (d.Columns p) (d.Parent p))
    (h : (comparison k d f).Holds) : OldSplitExtracted R k d f := by
  cases k with
  | passage _ _ => trivial
  | splitting a b c r =>
    cases r with
    | false => exact d.old_split_flags f h
    | true => exact d.forwardRanks.old_split_flags f h

end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open OccurrenceIncidence VertexTable
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A] [Algebra R A]
  (D : Diagram F S V arity) (P : D.Punctures R) (g : D.Solution P A)

/-- The split/merge extraction follows from the entire old solution. -/
theorem oldSplit_extraction (v : V) :
    LocalRanks.OldSplitExtracted A (D.ports.kind v) (D.vertexRanks v)
      (fun p => D.portFrame g.val.val ⟨v,p⟩) :=
  LocalRanks.comparison_oldSplit (D.vertexRanks v)
    (fun p => D.portFrame g.val.val ⟨v,p⟩) (g.property v)
end IntegralCharacterVarieties.SurfacePresentation.Diagram

end

end OAI
