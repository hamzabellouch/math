import OAI.Combinatorics.ContingencyTables.Rooted.RootedForestPrepareProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedCorrectionArithmetic

namespace OAI

/-! # Executed penalty evaluation at a sampled integer assignment

At an integer point, the coordinate scale in the affine coefficient
cancels its inverse in the coordinate. The program therefore forms the
unscaled signed affine numerator directly from the sampled integers.
-/

namespace ContingencyTables.RootedPointPenaltyProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped RootedForestPrepareProgram
open scoped BigOperators Classical

def term (z : RootedForestDataProgram.TermInput) : ForestAffineProgram.Term :=
  (RootedCoefficientProgram.coefficient z.1,z.2)
def termRealizer : Realizer term :=
  pair (composition (f := fun z : RootedForestDataProgram.TermInput => z.1)
    (g := RootedCoefficientProgram.coefficient) first RootedCoefficientProgram.coefficientRealizer) second
lemma polynomial_term : PolynomialTime termRealizer :=
  polynomial_pair (polynomial_composition polynomial_first
    RootedCoefficientProgram.polynomial_coefficient) polynomial_second

def tree (z : RootedForestDataProgram.Input) : ForestAffineProgram.Input :=
  ((RootedOffsetProgram.offset z.1.2,z.2.map term),z.1.1.2)
def treeRealizer : Realizer tree :=
  pair (pair (composition (f := fun z : RootedForestDataProgram.Input => z.1.2)
      (g := RootedOffsetProgram.offset) (composition first second) RootedOffsetProgram.offsetRealizer)
    (composition second (map termRealizer))) (composition (composition first first) second)
lemma polynomial_tree : PolynomialTime treeRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      RootedOffsetProgram.polynomial_offset)
    (polynomial_composition polynomial_second (polynomial_map polynomial_term)))
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_second)

def prepareTree (z : TreeInput) : ForestAffineProgram.Input := tree (forestInput z)
def prepareTreeRealizer : Realizer prepareTree :=
  composition (f := forestInput) (g := tree) forestInputRealizer treeRealizer
lemma polynomial_prepareTree : PolynomialTime prepareTreeRealizer :=
  polynomial_composition polynomial_forestInput polynomial_tree

def trees (z : Input) : List ForestAffineProgram.Input :=
  (treeCells z).map (fun a => prepareTree (treeBundle z,a))
def treesRealizer : Realizer trees :=
  composition (f := fun z : Input => (treeBundle z,treeCells z))
    (g := fun z => z.2.map (fun a => prepareTree (z.1,a)))
    (pair treeBundleRealizer treeCellsRealizer) (mapWith prepareTreeRealizer)
lemma polynomial_trees : PolynomialTime treesRealizer :=
  polynomial_composition (polynomial_pair polynomial_treeBundle polynomial_treeCells)
    (polynomial_mapWith polynomial_prepareTree)

def prepare (z : Input) : ForestPenaltyProgram.Input :=
  ((z.1.1.1,RootedDemandProgram.rootCount z.1.2),trees z)
def prepareRealizer : Realizer prepare :=
  pair (pair (composition (composition first first) first)
    (composition (f := fun z : Input => z.1.2) (g := RootedDemandProgram.rootCount)
      (composition first second) RootedDemandProgram.rootCountRealizer)) treesRealizer
lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      RootedDemandProgram.polynomial_rootCount)) polynomial_trees

def output (z : Input) : TreeFraction.Fraction := ForestPenaltyProgram.penaltyCode (prepare z)
def outputRealizer : Realizer output := composition prepareRealizer ForestPenaltyProgram.penaltyCodeRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_prepare ForestPenaltyProgram.polynomial_penaltyCode

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit GraphCompletionCounts

noncomputable section
variable {m n nf nc : ℕ}

lemma coefficient_parts (z : RootedCoefficientProgram.Input) :
    RootedCoefficientProgram.coefficient z=ForestAffineProgram.signedParts
      (SignedPairProgram.value (RootedCoefficientProgram.coefficient z)) := by
  unfold RootedCoefficientProgram.coefficient
  split
  · rw [SignedPairProgram.value_normalize]
    exact SignedPairProgram.normalize_eq _
  · rfl

lemma coefficient_parts_input (A : Instance (Fin m) (Fin n)) (t : TreeCell A.T)
    (a : Fin m×Fin n) :
    RootedCoefficientProgram.coefficient (RootedCoefficientProgram.input A t a)=
      ForestAffineProgram.signedParts (RootedIntegerEvaluation.coefficient A (rowColumn A.T) t a) := by
  rw [coefficient_parts,RootedCoefficientProgram.coefficient_input]

lemma tree_data (A : Instance (Fin m) (Fin n)) (B : ℕ) (t : TreeCell A.T)
    (x q : Fin m → Fin n → ℤ) (cells : Fin nc ≃ Fin m×Fin n)
    (free : Fin nf ≃ FreeCell A.small A.T) (v : FreeCell A.small A.T → ℕ) :
    tree (RootedForestDataProgram.data A B t x q cells free v)=
      ForestAffineProgram.data (RootedIntegerEvaluation.offset A (rowColumn A.T) t x q)
        (fun i => RootedIntegerEvaluation.coefficient A (rowColumn A.T) t (free i).val)
        (fun i => v (free i)) (A.b t.val.1 t.val.2) := by
  unfold tree RootedForestDataProgram.data ForestAffineProgram.data
  rw [RootedOffsetProgram.offset_data]
  simp only [List.map_ofFn,Function.comp_def,term,coefficient_parts_input]

lemma rational_tree_integer (A : Instance (Fin m) (Fin n)) (B : ℕ) (hB : 0<B)
    (t : TreeCell A.T) (x q : Fin m → Fin n → ℤ) (v : FreeCell A.small A.T → ℕ) :
    RootedIntegerEvaluation.rationalScaledTree A (rowColumn A.T) B x q
      (fun f => (B:ℚ)*(v f:ℚ)/((A.b f.val.1 f.val.2:ℚ)+1)) t=
      ((RootedIntegerEvaluation.offset A (rowColumn A.T) t x q:ℚ)+
        ∑ f : FreeCell A.small A.T,
          (RootedIntegerEvaluation.coefficient A (rowColumn A.T) t f.val:ℚ)*(v f:ℚ))/
        A.b t.val.1 t.val.2 := by
  have hBQ : (B:ℚ)≠0 := by exact_mod_cast hB.ne'
  unfold RootedIntegerEvaluation.rationalScaledTree
  rw [add_div,Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro f _
  have hN : (A.b f.val.1 f.val.2:ℚ)+1≠0 := by positivity
  have ht : (A.b t.val.1 t.val.2:ℚ)≠0 := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one
      (A.hlarge _ _ (A.hTG t.property)).2).ne'
  field_simp [hBQ,hN,ht]

theorem tree_value (A : Instance (Fin m) (Fin n)) (B : ℕ) (hB : 0<B) (t : TreeCell A.T)
    (x q : Fin m → Fin n → ℤ) (cells : Fin nc ≃ Fin m×Fin n)
    (free : Fin nf ≃ FreeCell A.small A.T) (v : FreeCell A.small A.T → ℕ) :
    TreeFraction.val (ForestAffineProgram.evaluate
      (tree (RootedForestDataProgram.data A B t x q cells free v)))=
      max 0 (max (-RootedIntegerEvaluation.rationalScaledTree A (rowColumn A.T) B x q
        (fun f => (B:ℚ)*(v f:ℚ)/((A.b f.val.1 f.val.2:ℚ)+1)) t)
      (RootedIntegerEvaluation.rationalScaledTree A (rowColumn A.T) B x q
        (fun f => (B:ℚ)*(v f:ℚ)/((A.b f.val.1 f.val.2:ℚ)+1)) t-1)) := by
  have ht : 0<A.b t.val.1 t.val.2 := Nat.lt_of_lt_of_le Nat.zero_lt_one
    (A.hlarge _ _ (A.hTG t.property)).2
  rw [tree_data,ForestAffineProgram.evaluate_data _ _ _ _ ht]
  have he : (∑ i : Fin nf,(RootedIntegerEvaluation.coefficient A (rowColumn A.T) t
      (free i).val:ℚ)*(v (free i):ℚ))=
      ∑ f : FreeCell A.small A.T,
        (RootedIntegerEvaluation.coefficient A (rowColumn A.T) t f.val:ℚ)*(v f:ℚ) :=
    Fintype.sum_equiv free _ _ (fun _ => rfl)
  rw [he,rational_tree_integer A B hB]

lemma trees_data (A : Instance (Fin m) (Fin n)) (C B : ℕ)
    (x q : Fin m → Fin n → ℕ) (v : FreeCell A.small A.T → ℕ) :
    trees (RootedForestPrepareProgram.data A C B x q v)=
      List.ofFn (fun i => tree (RootedForestDataProgram.data A B
        (RootedForestCatalog.treeEquiv A i) (fun i j => (x i j:ℤ))
        (fun i j => (q i j:ℤ)) finProdFinEquiv.symm (RootedForestCatalog.freeEquiv A) v)) := by
  change (RootedForestCatalog.catalog (RootedForestCatalog.data A,true)).map
    (fun a => prepareTree (((RootedDemandProgram.data A x q,B),
      List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i))),a))=_
  have hc := congrArg (fun cells : List (ℕ×ℕ) => cells.map
    (fun a => prepareTree (((RootedDemandProgram.data A x q,B),
      List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i))),a)))
    (RootedForestPrepareProgram.treeCatalog_ofFn A)
  refine hc.trans ?_
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  change tree (forestInput (((RootedDemandProgram.data A x q,B),
    List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i))),
      ((RootedForestCatalog.treeEquiv A i).val.1.val,
        (RootedForestCatalog.treeEquiv A i).val.2.val)))=_
  exact congrArg tree (RootedForestPrepareProgram.forestInput_data A B
    (RootedForestCatalog.treeEquiv A i) x q v)

/-- The executed penalty is exactly the source's rational penalty at
the scaled integer assignment, with no numerical approximation. -/
theorem output_data (A : Instance (Fin m) (Fin n)) (C : ℕ) (hC : 0<C)
    (x q : Fin m → Fin n → ℕ) (v : FreeCell A.small A.T → ℕ) :
    TreeFraction.val (output (RootedForestPrepareProgram.data A C
      (CompanionOracleDensity.rationalBinWidth A C) x q v))=
      RootedPenaltyProgram.rationalPenalty A (rowColumn A.T) C
        (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ))
        (fun f => (CompanionOracleDensity.rationalBinWidth A C:ℚ)*(v f:ℚ)/
          ((A.b f.val.1 f.val.2:ℚ)+1)) := by
  have hB : 0<CompanionOracleDensity.rationalBinWidth A C := by
    unfold CompanionOracleDensity.rationalBinWidth
    exact Nat.mul_pos (Nat.mul_pos (by decide) hC)
      (pow_pos (lt_of_lt_of_le Nat.zero_lt_one A.hd) _)
  rw [output,ForestPenaltyProgram.penaltyCode_value]
  change (C:ℚ)*((RootedDemandProgram.rootCount (RootedDemandProgram.data A x q):ℚ)+
    ((trees (RootedForestPrepareProgram.data A C
      (CompanionOracleDensity.rationalBinWidth A C) x q v)).map
      (fun t => TreeFraction.val (ForestAffineProgram.evaluate t))).sum)=_
  rw [RootedDemandProgram.rootCount_data,trees_data]
  simp only [List.map_ofFn,Function.comp_apply,List.sum_ofFn]
  unfold RootedPenaltyProgram.rationalPenalty
  congr 2
  exact Fintype.sum_equiv (RootedForestCatalog.treeEquiv A) _ _
    (fun i => tree_value A _ hB (RootedForestCatalog.treeEquiv A i) _ _
      finProdFinEquiv.symm (RootedForestCatalog.freeEquiv A) v)

theorem output_integerPoint (A : Instance (Fin m) (Fin n)) (C : ℕ) (hC : 0<C)
    (z : View A → ℕ) (f : FreeIndex A.small A.T A.b) :
    TreeFraction.val (output (RootedForestPrepareProgram.data A C
      (CompanionOracleDensity.rationalBinWidth A C)
      (ForestCountIdentification.smallX A.small z)
      (fun i j => A.b i j-ForestCountIdentification.smallY A.small z i j)
      (fun t => (f t).val)))=
      RootedOracleDensity.rationalD A (rowColumn A.T) C z
        (CompanionOracleDensity.rationalIntegerPoint A C f) := by
  have hpoint : (fun t : FreeCell A.small A.T =>
      CompanionOracleDensity.rationalIntegerPoint A C f
        ((CompanionOracleDensity.index A).symm t))=
      (fun t => (CompanionOracleDensity.rationalBinWidth A C:ℚ)*(f t).val/
        ((A.b t.val.1 t.val.2:ℚ)+1)) := by
    funext t
    change (CompanionOracleDensity.rationalBinWidth A C:ℚ)*
      (f (CompanionOracleDensity.index A ((CompanionOracleDensity.index A).symm t))).val/
      CompanionOracleDensity.freeRange A
        (CompanionOracleDensity.index A ((CompanionOracleDensity.index A).symm t))=_
    rw [Equiv.apply_symm_apply]
    simp only [CompanionOracleDensity.freeRange,Nat.cast_add,Nat.cast_one]
  rw [output_data A C hC]
  unfold RootedOracleDensity.rationalD
  rw [hpoint]
  rfl

theorem output_denominator_pos (z : Input) : 0<(output z).2 :=
  TreeFraction.normalize_den_pos _

end
end ContingencyTables.RootedPointPenaltyProgram

end OAI
