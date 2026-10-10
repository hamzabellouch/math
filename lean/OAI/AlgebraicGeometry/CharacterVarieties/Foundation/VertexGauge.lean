import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.BandCycles

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity)

@[simp] theorem sideCircle_boundary (f : F) (b : Fin (D.boundaryCount f))
    (i : Fin (D.boundaryLength f b)) : D.sideCircle (D.boundarySide ⟨f,b,i⟩)=⟨f,b⟩ := by
  unfold sideCircle
  rw [D.boundarySide.symm_apply_apply]

lemma sideCircle_facet (a : Side S arity) : (D.sideCircle a).1=D.ports.facet a := by
  obtain ⟨⟨f,b,i⟩,rfl⟩ := D.boundarySide.surjective a
  rw [D.sideCircle_boundary]
  exact (D.boundaryFacet f b i).symm

@[simp] lemma sideCircle_next (a : Side S arity) :
    D.sideCircle (D.ports.vertexAssembly.corners.boundaryNext a)=D.sideCircle a := by
  obtain ⟨⟨f,b,i⟩,rfl⟩ := D.boundarySide.surjective a
  rw [D.boundaryNext,D.sideCircle_boundary,D.sideCircle_boundary]

@[simp] lemma sideCircle_prev (a : Side S arity) :
    D.sideCircle (D.ports.vertexAssembly.corners.boundaryNext.symm a)=D.sideCircle a := by
  have h := D.sideCircle_next (D.ports.vertexAssembly.corners.boundaryNext.symm a)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

lemma sideCircle_mate (x : Germ S arity) :
    D.sideCircle (D.ports.vertexAssembly.corners.mate x).1=D.sideCircle x.1 := by
  by_cases h : x.2=positive x.1
  · have hx : x=finish x.1 := Prod.ext rfl h
    conv_lhs => rw [hx]
    exact D.sideCircle_next x.1
  · have hh : x.2= !(positive x.1) := Bool.eq_not_iff.mpr h
    have hx : x=start x.1 := Prod.ext rfl hh
    conv_lhs => rw [hx]
    exact D.sideCircle_prev x.1

lemma portCircle_corner (x : LocalEnd V D.ports.kind) :
    D.sideCircle (D.portSide ⟨(localMate x).1,(localMate x).2.1⟩ (localMate x).2.2)=
      D.sideCircle (D.portSide ⟨x.1,x.2.1⟩ x.2.2) := by
  rw [D.portSide_eq,D.portSide_eq]
  have h := D.sideCircle_mate (D.ports.realize x)
  change D.sideCircle (D.ports.realize (localMate (D.ports.realize.symm
    (D.ports.realize x)))).1 = D.sideCircle (D.ports.realize x).1 at h
  simpa only [Equiv.symm_apply_apply] using h

variable {R : Type*} [CommRing R]

/-- A basis at each old boundary circle; repeated facet labels do not identify these independent
basing paths. -/
abbrev CircleBases := (B : D.BoundaryCircle) →
  MatrixIso R (Fin (D.rank B.1)) (Fin (D.rank B.1))

def sideBasis (G : D.CircleBases (R:=R)) (a : Side S arity) :
    MatrixIso R (Fin (D.rank (D.ports.facet a))) (Fin (D.rank (D.ports.facet a))) :=
  (G (D.sideCircle a)).reindex
    (finCongr (congrArg D.rank (D.sideCircle_facet a).symm))
    (finCongr (congrArg D.rank (D.sideCircle_facet a).symm))

end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
variable {R : Type*} [CommRing R]

lemma finite_basis_transport {I : Type*} (r : I → ℕ)
    (G : (i : I) → MatrixIso R (Fin (r i)) (Fin (r i)))
    (i j : I) (a b : ℕ) (ha : a=r i) (hb : b=r j) (hij : i=j) (hab : a=b) :
    ((G j).reindex (finCongr hb) (finCongr hb)).reindex (finCongr hab) (finCongr hab)=
      (G i).reindex (finCongr ha) (finCongr ha) := by
  subst j
  subst b
  simp only [finCongr_refl,reindex_refl_eq]

end IntegralCharacterVarieties.MatrixIso

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity)
variable {R : Type*} [CommRing R]

lemma sideBasis_corner (G : D.CircleBases (R:=R)) (x : LocalEnd V D.ports.kind) :
    (D.sideBasis G (D.portSide ⟨(localMate x).1,(localMate x).2.1⟩ (localMate x).2.2)).reindex
      (finCongr (congrArg D.rank (D.portFacet_corner x).symm))
      (finCongr (congrArg D.rank (D.portFacet_corner x).symm))=
      D.sideBasis G (D.portSide ⟨x.1,x.2.1⟩ x.2.2) := by
  exact MatrixIso.finite_basis_transport (fun B : D.BoundaryCircle => D.rank B.1)
    G _ _ _ _ _ _ (D.portCircle_corner x).symm _

def portBasis (G : D.CircleBases (R:=R)) (p : LocalPort V D.ports.kind)
    (c : Option ((D.ports.kind p.1).table.Child p.2)) :
    MatrixIso R (Fin ((D.vertexRanks p.1).rank p.2 c))
      (Fin ((D.vertexRanks p.1).rank p.2 c)) := D.sideBasis G (D.portSide p c)

lemma portBasis_corner (G : D.CircleBases (R:=R)) (v : V)
    (x : (p : (D.ports.kind v).table.Port) × Option ((D.ports.kind v).table.Child p)) :
    (D.portBasis G ⟨v,((D.ports.kind v).table.mate x).1⟩
      ((D.ports.kind v).table.mate x).2).reindex
        ((D.vertexRanks v).cornerEquiv x) ((D.vertexRanks v).cornerEquiv x)=
      D.portBasis G ⟨v,x.1⟩ x.2 :=
  D.sideBasis_corner G ⟨v,x⟩

end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
variable {R : Type*} [CommRing R]

lemma reindex_eq_iff {α β α' β' : Type*}
    [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
    (x : MatrixIso R α β) (y : MatrixIso R α' β') (a : α' ≃ α) (b : β' ≃ β) :
    x.reindex a b=y ↔ x=y.reindex a.symm b.symm := by
  constructor
  · intro h
    rw [← h]
    simp only [reindex_reindex_eq,Equiv.symm_trans_self,reindex_refl_eq]
  · intro h
    rw [h]
    simp only [reindex_reindex_eq,Equiv.self_trans_symm,reindex_refl_eq]

lemma block_reindex_sigma {I J : Type*} [Fintype I] [Fintype J]
    {a : I → Type*} {b : J → Type*} [∀ i,Fintype (a i)] [∀ j,Fintype (b j)]
    (e : J ≃ I) (f : ∀ j,b j ≃ a (e j)) (w : ∀ i,MatrixIso R (a i) (a i)) :
    (block w).reindex (Equiv.sigmaCongr e f) (Equiv.sigmaCongr e f)=
      block (fun j => (w (e j)).reindex (f j) (f j)) := by
  apply ext <;> ext ⟨i,x⟩ ⟨j,y⟩
  all_goals
    by_cases h : i=j
    · subst j
      simp [block,reindex,Matrix.blockDiagonal',Equiv.sigmaCongr]
    · have he : e i≠e j := fun hij => h (e.injective hij)
      simp [block,reindex,Matrix.blockDiagonal',Equiv.sigmaCongr,h,he]

lemma block_reindex_sigmaRight {I : Type*} [Fintype I]
    {a b : I → Type*} [∀ i,Fintype (a i)] [∀ i,Fintype (b i)]
    (f : ∀ i,b i ≃ a i) (w : ∀ i,MatrixIso R (a i) (a i)) :
    (block w).reindex (Equiv.sigmaCongrRight f) (Equiv.sigmaCongrRight f)=
      block (fun i => (w i).reindex (f i) (f i)) :=
  block_reindex_sigma (Equiv.refl _) f w
private theorem sum_blocks_unit_reindex {I K : Type*} [Fintype I] [Fintype K]
    [hs : Fintype (I ⊕ (Unit ⊕ K))]
    {a : I ⊕ (Unit ⊕ K) → Type*} [∀ i, Fintype (a i)]
    (g : ∀ i, MatrixIso R (a i) (a i))
    (e : ((i : I ⊕ (Unit ⊕ K)) × a i) ≃
      (((i : I) × a (.inl i)) ⊕ (a (.inr (.inl ())) ⊕ ((i : K) × a (.inr (.inr i))))))
    (hl : ∀ i x, e ⟨.inl i, x⟩ = .inl ⟨i, x⟩)
    (hm : ∀ x, e ⟨.inr (.inl ()), x⟩ = .inr (.inl x))
    (hr : ∀ i x, e ⟨.inr (.inr i), x⟩ = .inr (.inr ⟨i, x⟩)) :
    ((block (fun i => g (.inl i))).sum
      ((g (.inr (.inl ()))).sum (block (fun i => g (.inr (.inr i)))))).reindex e e =
      block g := by
  apply ext <;> ext ⟨i, x⟩ ⟨j, y⟩
  all_goals
    rcases i with i | (⟨⟩ | i) <;> rcases j with j | (⟨⟩ | j) <;>
      simp [reindex, block, sum, Matrix.submatrix_apply, hl, hm, hr,
        Matrix.fromBlocks, Matrix.blockDiagonal']

private theorem sum_three_blocks_reindex {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [hs : Fintype (I ⊕ (J ⊕ K))]
    {a : I ⊕ (J ⊕ K) → Type*} [∀ i, Fintype (a i)]
    (g : ∀ i, MatrixIso R (a i) (a i))
    (e : ((i : I ⊕ (J ⊕ K)) × a i) ≃
      (((i : I) × a (.inl i)) ⊕ (((i : J) × a (.inr (.inl i))) ⊕ ((i : K) × a (.inr (.inr i))))))
    (hl : ∀ i x, e ⟨.inl i, x⟩ = .inl ⟨i, x⟩)
    (hm : ∀ i x, e ⟨.inr (.inl i), x⟩ = .inr (.inl ⟨i, x⟩))
    (hr : ∀ i x, e ⟨.inr (.inr i), x⟩ = .inr (.inr ⟨i, x⟩)) :
    ((block (fun i => g (.inl i))).sum
      ((block (fun i => g (.inr (.inl i)))).sum
        (block (fun i => g (.inr (.inr i)))))).reindex e e = block g := by
  apply ext <;> ext ⟨i, x⟩ ⟨j, y⟩
  all_goals
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
      simp [reindex, block, sum, Matrix.submatrix_apply, hl, hm, hr,
        Matrix.fromBlocks, Matrix.blockDiagonal']

end IntegralCharacterVarieties.MatrixIso

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
open scoped Classical Matrix
variable {R : Type*} [CommRing R] {k : Kind} (d : LocalRanks k)

/-- Fiber bases compatible across every vertex corner. For a Diagram this property is derived from
bases on its boundary circles. -/
structure CoherentBases where
  basis : ∀ p c,MatrixIso R (Fin (d.rank p c)) (Fin (d.rank p c))
  corner : ∀ x : (p : k.table.Port) × Option (k.table.Child p),
    (basis (k.table.mate x).1 (k.table.mate x).2).reindex
      (d.cornerEquiv x) (d.cornerEquiv x)=basis x.1 x.2

namespace CoherentBases
variable {d} (G : d.CoherentBases (R:=R))

def columns (p : k.table.Port) : MatrixIso R (d.Columns p) (d.Columns p) :=
  MatrixIso.block (fun i => G.basis p (some i))

def reframe (f : ∀ p,MatrixIso R (d.Columns p) (d.Parent p)) :
    ∀ p,MatrixIso R (d.Columns p) (d.Parent p) :=
  fun p => ((G.columns p).symm.trans (f p)).trans (G.basis p none)
end CoherentBases
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity)
variable {R : Type*} [CommRing R]

def vertexBases (G : D.CircleBases (R:=R)) (v : V) :
    (D.vertexRanks v).CoherentBases (R:=R) where
  basis p c := D.portBasis G ⟨v,p⟩ c
  corner := D.portBasis_corner G v
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
open scoped Classical Matrix
variable {R : Type*} [CommRing R] {m : ℕ} {t : Passage m}
variable {d : LocalRanks (.passage m t)} (G : d.CoherentBases (R:=R))
local instance : Fintype ((Kind.passage m t).table.Child false) := fintypeChild (.passage m t) false
local instance : Fintype ((Kind.passage m t).table.Child true) := fintypeChild (.passage m t) true
local instance : Fintype (d.Columns false) := d.fintypeColumns false
local instance : Fintype (d.Columns true) := d.fintypeColumns true

lemma CoherentBases.passage_columns :
    (G.columns true).reindex d.passageColumns d.passageColumns=G.columns false := by
  unfold columns passageColumns
  erw [MatrixIso.block_reindex_sigma]
  congr 1
  funext i
  exact G.corner ⟨false,some i⟩

lemma CoherentBases.passage_parent :
    (G.basis true none).reindex d.passageParent d.passageParent=G.basis false none :=
  G.corner ⟨false,none⟩

lemma CoherentBases.passage_reframe
    (f : ∀ p,MatrixIso R (d.Columns p) (d.Parent p)) :
    G.reframe f=d.changePassageBases f (G.columns false) (G.basis false none) := by
  funext p
  cases p
  · rfl
  · have hc := (MatrixIso.reindex_eq_iff _ _ _ _).mp G.passage_columns
    have hp := (MatrixIso.reindex_eq_iff _ _ _ _).mp G.passage_parent
    dsimp only [reframe,changePassageBases]
    rw [hc,hp]

lemma CoherentBases.passage_holds
    (f : ∀ p,MatrixIso R (d.Columns p) (d.Parent p))
    (h : (d.passageComparison f).Holds) :
    (d.passageComparison (G.reframe f)).Holds := by
  rw [G.passage_reframe]
  exact d.changePassageBlockBases_holds f (fun i => G.basis false (some i)) _ h
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
open scoped Classical Matrix
variable {R : Type*} [CommRing R] {a b c : ℕ}
variable {d : LocalRanks (.splitting a b c false)} (G : d.CoherentBases (R:=R))
local instance : Fintype ((Kind.splitting a b c false).table.Child .branch) := fintypeChild (.splitting a b c false) .branch
local instance : Fintype (d.Columns .before) := d.fintypeColumns .before
local instance : Fintype (d.Columns .after) := d.fintypeColumns .after
local instance : Fintype (d.Columns .branch) := d.fintypeColumns .branch

lemma CoherentBases.split_prefix :
    (MatrixIso.block (fun i => G.basis .before (some (.inl i)))).reindex
      d.splitPrefix d.splitPrefix=
      MatrixIso.block (fun i => G.basis .after (some (.inl i))) := by
  unfold splitPrefix
  erw [MatrixIso.block_reindex_sigmaRight]
  congr 1
  funext i
  exact G.corner ⟨.after,some (.inl i)⟩

lemma CoherentBases.split_suffix :
    (MatrixIso.block (fun i => G.basis .before (some (.inr (.inr i))))).reindex
      d.splitSuffix d.splitSuffix=
      MatrixIso.block (fun i => G.basis .after (some (.inr (.inr i)))) := by
  unfold splitSuffix
  erw [MatrixIso.block_reindex_sigmaRight]
  congr 1
  funext i
  exact G.corner ⟨.after,some (.inr (.inr i))⟩

lemma CoherentBases.split_branch_columns :
    (G.columns .branch).reindex d.splitBranchChildren d.splitBranchChildren=
      MatrixIso.block (fun i => G.basis .after (some (.inr (.inl i)))) := by
  exact (MatrixIso.block_reindex_sigmaRight _ _).trans
    (congrArg MatrixIso.block (funext (fun i => G.corner ⟨.after,some (.inr (.inl i))⟩)))

lemma CoherentBases.split_middle :
    (G.basis .branch none).reindex d.splitBranchParent d.splitBranchParent=
      G.basis .before (some (.inr (.inl ()))) := G.corner ⟨.before,some (.inr (.inl ()))⟩

lemma CoherentBases.split_parent :
    (G.basis .before none).reindex d.splitParent d.splitParent=G.basis .after none :=
  G.corner ⟨.after,none⟩

lemma CoherentBases.split_before_columns :
    d.splitBeforeBasis (MatrixIso.block (fun i => G.basis .before (some (.inl i))))
      (G.basis .before (some (.inr (.inl ()))))
      (MatrixIso.block (fun i => G.basis .before (some (.inr (.inr i)))))=G.columns .before := by
  convert!
    (MatrixIso.sum_blocks_unit_reindex
      (hs := fintypeChild (.splitting a b c false) .before)
      (fun i => G.basis .before (some i)) d.splitBefore
      (by intros; rfl) (by intros; rfl) (by intros; rfl)) using 1

lemma CoherentBases.split_after_columns :
    d.splitAfterBasis (MatrixIso.block (fun i => G.basis .before (some (.inl i))))
      (MatrixIso.block (fun i => G.basis .after (some (.inr (.inl i)))))
      (MatrixIso.block (fun i => G.basis .before (some (.inr (.inr i)))))=G.columns .after := by
  unfold splitAfterBasis
  erw [G.split_prefix,G.split_suffix]
  convert!
    (MatrixIso.sum_three_blocks_reindex
      (hs := fintypeChild (.splitting a b c false) .after)
      (fun i => G.basis .after (some i)) d.splitAfter
      (by intros; rfl) (by intros; rfl) (by intros; rfl)) using 1

lemma CoherentBases.split_reframe
    (f : ∀ p,MatrixIso R (d.Columns p) (d.Parent p)) :
    G.reframe f=d.changeSplitBases f
      (MatrixIso.block (fun i => G.basis .before (some (.inl i))))
      (MatrixIso.block (fun i => G.basis .after (some (.inr (.inl i)))))
      (G.basis .before (some (.inr (.inl ()))))
      (MatrixIso.block (fun i => G.basis .before (some (.inr (.inr i)))))
      (G.basis .before none) := by
  funext p
  cases p with
  | before =>
    dsimp only [reframe,changeSplitBases]
    rw [G.split_before_columns]
  | after =>
    dsimp only [reframe,changeSplitBases]
    rw [G.split_after_columns,G.split_parent]
  | branch =>
    dsimp only [reframe,changeSplitBases,splitBranchBasis,splitMiddleBasis]
    have hc := (MatrixIso.reindex_eq_iff _ _ _ _).mp G.split_branch_columns
    have hp := (MatrixIso.reindex_eq_iff _ _ _ _).mp G.split_middle
    rw [← hc,← hp]

lemma CoherentBases.split_holds
    (f : ∀ p,MatrixIso R (d.Columns p) (d.Parent p))
    (h : (d.splitComparison f).Holds) :
    (d.splitComparison (G.reframe f)).Holds := by
  rw [G.split_reframe]
  exact d.changeSplitBlockBases_holds f _ _ _ _ _ h
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
open scoped Classical Matrix
variable {R : Type*} [CommRing R] {k : Kind} {d : LocalRanks k}

/-- Every permitted vertex comparison is invariant under gauges indexed by its corner fibers. This
includes merging, not just forward splitting. -/
theorem CoherentBases.comparison_holds (G : d.CoherentBases (R:=R))
    (f : ∀ p,MatrixIso R (d.Columns p) (d.Parent p))
    (h : (comparison k d f).Holds) : (comparison k d (G.reframe f)).Holds := by
  cases k with
  | passage m t => exact G.passage_holds f h
  | splitting a b c r =>
    cases r with
    | false => exact G.split_holds f h
    | true =>
      let H : d.forwardRanks.CoherentBases (R:=R) := ⟨G.basis,G.corner⟩
      exact H.split_holds f h
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks

end

end OAI
