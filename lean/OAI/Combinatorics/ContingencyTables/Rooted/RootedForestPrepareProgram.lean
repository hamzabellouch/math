import OAI.Combinatorics.ContingencyTables.Rooted.RootedTreeInputProgram

namespace OAI

/-! # Preparing the whole selected-root forest penalty

The program takes the four cell arrays and the graph. It computes the
root discrepancy, both catalogs, every cut coefficient and every affine
offset before invoking the rational penalty evaluator.
-/

namespace ContingencyTables.RootedForestPrepareProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped Classical

abbrev Context := RootedDemandProgram.Input
abbrev TreeInput := ((Context×ℕ)×List ℕ)×(ℕ×ℕ)
abbrev Input := ((ℕ×ℕ)×Context)×List ℕ

def treeFrame (z : TreeInput) : RootedCellDataProgram.Input :=
  RootedTreeInputProgram.treeInput (z.1.1.1,z.2)
def treeFrameRealizer : Realizer treeFrame :=
  composition (f := fun z : TreeInput => (z.1.1.1,z.2))
    (g := RootedTreeInputProgram.treeInput)
    (pair (composition (composition first first) first) second)
    RootedTreeInputProgram.treeInputRealizer
lemma polynomial_treeFrame : PolynomialTime treeFrameRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_first) polynomial_second) RootedTreeInputProgram.polynomial_treeInput

def freeCells (z : TreeInput) : List (ℕ×ℕ) :=
  RootedForestCatalog.catalog (z.1.1.1.1,false)
def freeCellsRealizer : Realizer freeCells :=
  composition (f := fun z : TreeInput => (z.1.1.1.1,false))
    (g := RootedForestCatalog.catalog)
    (pair (composition (composition (composition first first) first) first)
      (constant false)) RootedForestCatalog.catalogRealizer
lemma polynomial_freeCells : PolynomialTime freeCellsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      polynomial_first) (polynomial_constant false)) RootedForestCatalog.polynomial_catalog

def widthCapacity (z : TreeInput) : ℕ×ℕ :=
  (z.1.1.2,matrixEntry (z.1.1.1.1.2,z.2))
def widthCapacityRealizer : Realizer widthCapacity :=
  pair (composition (composition first first) second)
    (composition (f := fun z : TreeInput => (z.1.1.1.1.2,z.2))
      (g := matrixEntry)
      (pair (composition (composition (composition (composition first first) first) first)
        second) second) matrixEntryRealizer)
lemma polynomial_widthCapacity : PolynomialTime widthCapacityRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_second)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_first)
        polynomial_first) polynomial_second) polynomial_second) polynomial_matrixEntry)

def forestInput (z : TreeInput) : RootedForestDataProgram.Input :=
  ((widthCapacity z,RootedCellDataProgram.offsetInput (treeFrame z)),
    RootedTreeInputProgram.terms ((treeFrame z,freeCells z),z.1.2))
def forestInputRealizer : Realizer forestInput :=
  pair (pair widthCapacityRealizer
    (composition (f := treeFrame) (g := RootedCellDataProgram.offsetInput)
      treeFrameRealizer RootedCellDataProgram.offsetInputRealizer))
    (composition (f := fun z : TreeInput => ((treeFrame z,freeCells z),z.1.2))
      (g := RootedTreeInputProgram.terms)
      (pair (pair treeFrameRealizer freeCellsRealizer) (composition first second))
      RootedTreeInputProgram.termsRealizer)
lemma polynomial_forestInput : PolynomialTime forestInputRealizer :=
  polynomial_pair (polynomial_pair polynomial_widthCapacity
    (polynomial_composition polynomial_treeFrame RootedCellDataProgram.polynomial_offsetInput))
    (polynomial_composition (polynomial_pair
      (polynomial_pair polynomial_treeFrame polynomial_freeCells)
      (polynomial_composition polynomial_first polynomial_second))
      RootedTreeInputProgram.polynomial_terms)

def prepareTree (z : TreeInput) : ForestAffineProgram.Input :=
  RootedForestDataProgram.prepare (forestInput z)
def prepareTreeRealizer : Realizer prepareTree :=
  composition (f := forestInput) (g := RootedForestDataProgram.prepare)
    forestInputRealizer RootedForestDataProgram.prepareRealizer
lemma polynomial_prepareTree : PolynomialTime prepareTreeRealizer :=
  polynomial_composition polynomial_forestInput RootedForestDataProgram.polynomial_prepare

def treeBundle (z : Input) : (Context×ℕ)×List ℕ := ((z.1.2,z.1.1.2),z.2)
def treeBundleRealizer : Realizer treeBundle :=
  pair (pair (composition first second) (composition (composition first first) second)) second
lemma polynomial_treeBundle : PolynomialTime treeBundleRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_second)) polynomial_second

def treeCells (z : Input) : List (ℕ×ℕ) :=
  RootedForestCatalog.catalog (z.1.2.1,true)
def treeCellsRealizer : Realizer treeCells :=
  composition (f := fun z : Input => (z.1.2.1,true)) (g := RootedForestCatalog.catalog)
    (pair (composition (composition first second) first) (constant true))
    RootedForestCatalog.catalogRealizer
lemma polynomial_treeCells : PolynomialTime treeCellsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_first) (polynomial_constant true)) RootedForestCatalog.polynomial_catalog

def prepareTrees (z : Input) : List ForestAffineProgram.Input :=
  (treeCells z).map (fun a => prepareTree (treeBundle z,a))
def prepareTreesRealizer : Realizer prepareTrees :=
  composition (f := fun z : Input => (treeBundle z,treeCells z))
    (g := fun z => z.2.map (fun a => prepareTree (z.1,a)))
    (pair treeBundleRealizer treeCellsRealizer) (mapWith prepareTreeRealizer)
lemma polynomial_prepareTrees : PolynomialTime prepareTreesRealizer :=
  polynomial_composition (polynomial_pair polynomial_treeBundle polynomial_treeCells)
    (polynomial_mapWith polynomial_prepareTree)

def prepare (z : Input) : ForestPenaltyProgram.Input :=
  ((z.1.1.1,RootedDemandProgram.rootCount z.1.2),prepareTrees z)
def prepareRealizer : Realizer prepare :=
  pair (pair (composition (composition first first) first)
    (composition (f := fun z : Input => z.1.2) (g := RootedDemandProgram.rootCount)
      (composition first second) RootedDemandProgram.rootCountRealizer)) prepareTreesRealizer
theorem polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_first)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      RootedDemandProgram.polynomial_rootCount)) polynomial_prepareTrees

def penaltyCode (z : Input) : MatchingFPRAS.TreeFraction.Fraction :=
  ForestPenaltyProgram.penaltyCode (prepare z)
def penaltyCodeRealizer : Realizer penaltyCode :=
  composition (f := prepare) (g := ForestPenaltyProgram.penaltyCode)
    prepareRealizer ForestPenaltyProgram.penaltyCodeRealizer
theorem polynomial_penaltyCode : PolynomialTime penaltyCodeRealizer :=
  polynomial_composition polynomial_prepare ForestPenaltyProgram.polynomial_penaltyCode

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit

noncomputable def data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (C B : ℕ)
    (x q : Fin m → Fin n → ℕ) (v : FreeCell A.small A.T → ℕ) : Input :=
  (((C,B),RootedDemandProgram.data A x q),
    List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i)))

theorem forestInput_data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (B : ℕ)
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℕ)
    (v : FreeCell A.small A.T → ℕ) :
    forestInput (((RootedDemandProgram.data A x q,B),
      List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i))),
        (t.val.1.val,t.val.2.val))=
      RootedForestDataProgram.data A B t (fun i j => (x i j:ℤ))
        (fun i j => (q i j:ℤ)) finProdFinEquiv.symm
        (RootedForestCatalog.freeEquiv A) v := by
  unfold forestInput RootedForestDataProgram.data
  apply Prod.ext
  · apply Prod.ext
    · simp only [widthCapacity,RootedDemandProgram.data,
        RootedForestCatalog.data,matrixEntry_code]
    · rw [treeFrame,RootedTreeInputProgram.treeInput_data,
        RootedCellDataProgram.offsetInput_data]
  · exact RootedTreeInputProgram.terms_data A t x q v

theorem prepareTree_data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (B : ℕ)
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℕ)
    (v : FreeCell A.small A.T → ℕ) :
    prepareTree (((RootedDemandProgram.data A x q,B),
      List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i))),
        (t.val.1.val,t.val.2.val))=
      RootedIntegerEvaluation.forestData A (rowColumn A.T) B t
        (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ))
        (RootedForestCatalog.freeEquiv A) v := by
  rw [prepareTree,forestInput_data,RootedForestDataProgram.prepare_data]

lemma treeCatalog_ofFn {m n : ℕ} (A : Instance (Fin m) (Fin n)) :
    RootedForestCatalog.catalog (RootedForestCatalog.data A,true)=
      List.ofFn (fun i => (((RootedForestCatalog.treeEquiv A) i).val.1.val,
        ((RootedForestCatalog.treeEquiv A) i).val.2.val)) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn]
  · intro i hi hj
    simp only [List.getElem_ofFn]
    exact (RootedForestCatalog.catalogCell_coordinates A true ⟨i,hi⟩).symm

theorem prepare_data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (C : ℕ)
    (x q : Fin m → Fin n → ℕ) (v : FreeCell A.small A.T → ℕ) :
    prepare (data A C (CompanionOracleDensity.rationalBinWidth A C) x q v)=
      RootedPenaltyProgram.data A (rowColumn A.T) C
        (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ))
        (RootedForestCatalog.treeEquiv A) (RootedForestCatalog.freeEquiv A) v := by
  have ht : prepareTrees (data A C (CompanionOracleDensity.rationalBinWidth A C) x q v)=
      List.ofFn (fun i => RootedIntegerEvaluation.forestData A (rowColumn A.T)
        (CompanionOracleDensity.rationalBinWidth A C) (RootedForestCatalog.treeEquiv A i)
        (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ))
        (RootedForestCatalog.freeEquiv A) v) := by
    change (RootedForestCatalog.catalog (RootedForestCatalog.data A,true)).map
      (fun a => prepareTree
        (((RootedDemandProgram.data A x q,CompanionOracleDensity.rationalBinWidth A C),
          List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i))),a))=_
    have hc := congrArg (fun cells : List (ℕ×ℕ) => cells.map
      (fun a => prepareTree
        (((RootedDemandProgram.data A x q,CompanionOracleDensity.rationalBinWidth A C),
          List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i))),a)))
      (treeCatalog_ofFn A)
    refine hc.trans ?_
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact prepareTree_data A _ (RootedForestCatalog.treeEquiv A i) x q v
  unfold prepare RootedPenaltyProgram.data
  apply Prod.ext
  · exact congrArg (fun r => (C,r)) (RootedDemandProgram.rootCount_data A x q)
  · exact ht

theorem penaltyCode_data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (C : ℕ)
    (hC : 0<C) (x q : Fin m → Fin n → ℕ) (v : FreeCell A.small A.T → ℕ) :
    MatchingFPRAS.TreeFraction.val
        (penaltyCode (data A C (CompanionOracleDensity.rationalBinWidth A C) x q v))=
      RootedPenaltyProgram.rationalPenalty A (rowColumn A.T) C
        (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ)) (fun f => (v f:ℚ)) := by
  rw [penaltyCode,prepare_data]
  exact RootedPenaltyProgram.penaltyCode_data A (rowColumn A.T) C hC _ _
    (RootedForestCatalog.treeEquiv A) (RootedForestCatalog.freeEquiv A) v

end ContingencyTables.RootedForestPrepareProgram

end OAI
