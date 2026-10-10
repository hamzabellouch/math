import OAI.Combinatorics.ContingencyTables.Machines.FlowEntryProgram
import OAI.Combinatorics.ContingencyTables.Transport.EdmondsKarpAlgorithm

namespace OAI

/-! # Materialized binary residual augmentation

The path and bottleneck are computed once, then every matrix entry is
updated from the preceding matrix. Missing paths leave that matrix
unchanged.
-/

namespace ContingencyTables.FlowMatrixProgram

open MatchingFPRAS.TreeTyped DirectedBFSProgram ResidualGraphProgram FlowPathProgram
  FlowEntryProgram

def updateRow (z : UpdateData×ℕ) : List SignedPairProgram.Signed :=
  (List.range z.1.1.1.length).map (fun v=>updateCell (z.1,(z.2,v)))

def updateRowRealizer : Realizer updateRow :=
  composition
    (f := fun z : UpdateData×ℕ=>(z,List.range z.1.1.1.length))
    (g := fun z : (UpdateData×ℕ)×List ℕ=>
      z.2.map (fun v=>updateCell (z.1.1,(z.1.2,v))))
    (pair identity (composition (f := fun z : UpdateData×ℕ=>z.1.1.1)
      (g := matrixIndices) (composition (composition first first) first) matrixIndicesRealizer))
    (mapWith (composition
      (f := fun z : (UpdateData×ℕ)×ℕ=>(z.1.1,(z.1.2,z.2))) (g := updateCell)
      (pair (composition first first) (pair (composition first second) second)) updateCellRealizer))

lemma polynomial_updateRow : PolynomialTime updateRowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_first) polynomial_matrixIndices))
    (polynomial_mapWith (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
        polynomial_second)) polynomial_updateCell))

def updateMatrix (z : UpdateData) : FlowMatrix :=
  (List.range z.1.1.length).map (fun u=>updateRow (z,u))

def updateMatrixRealizer : Realizer updateMatrix :=
  composition
    (f := fun z : UpdateData=>(z,List.range z.1.1.length))
    (g := fun z : UpdateData×List ℕ=>z.2.map (fun u=>updateRow (z.1,u)))
    (pair identity (composition (f := fun z : UpdateData=>z.1.1) (g := matrixIndices)
      (composition first first) matrixIndicesRealizer)) (mapWith updateRowRealizer)

lemma polynomial_updateMatrix : PolynomialTime updateMatrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_matrixIndices)) (polynomial_mapWith polynomial_updateRow)

lemma updateMatrix_code {n : ℕ} (c : PublishedEdmondsKarp.Capacity n)
    (s t : Fin n) (f : PublishedEdmondsKarp.Flow n) (xs : List (Fin n)) (a : ℕ)
    (hnew : PublishedEdmondsKarp.Feasible c s t
      (ResidualAugmentation.listUpdate f xs (a:ℤ))) :
    updateMatrix ((natCode c,flowCode f),
      ((ResidualAugmentation.arcs xs).map (fun uv=>(uv.1.val,uv.2.val)),a))=
      flowCode (ResidualAugmentation.listUpdate f xs (a:ℤ)) := by
  simp only [updateMatrix,updateRow,natCode,List.length_ofFn,DirectedBFSCode.range_eq_map,
    List.map_ofFn,←List.ofFn_eq_map,flowCode]
  apply congrArg List.ofFn
  funext u
  apply congrArg List.ofFn
  funext v
  exact updateCell_code c s t f xs a hnew u v

def prepareAugment (z : Data×List ℕ) : UpdateData :=
  (z.1,(arcPairs z.2,bottleneck z))

def prepareAugmentRealizer : Realizer prepareAugment :=
  pair first (pair (composition second arcPairsRealizer) bottleneckRealizer)

lemma polynomial_prepareAugment : PolynomialTime prepareAugmentRealizer :=
  polynomial_pair polynomial_first (polynomial_pair
    (polynomial_composition polynomial_second polynomial_arcPairs) polynomial_bottleneck)

def augment (z : Data×List ℕ) : FlowMatrix := updateMatrix (prepareAugment z)

def augmentRealizer : Realizer augment :=
  composition prepareAugmentRealizer updateMatrixRealizer

lemma polynomial_augment : PolynomialTime augmentRealizer :=
  polynomial_composition polynomial_prepareAugment polynomial_updateMatrix

def advance (z : Data×(ℕ×ℕ)) : FlowMatrix :=
  match ResidualGraphProgram.search z with
  | none => z.1.2
  | Option.some xs => augment (z.1,xs)

def advanceRealizer : Realizer advance :=
  (composition (pair identity ResidualGraphProgram.searchRealizer)
    (optionCases (composition first second)
      (composition (pair (composition first first) second) augmentRealizer))).congr (by
    intro z
    dsimp only [Function.comp_apply,id_eq,advance]
    cases h : ResidualGraphProgram.search z <;> rfl)

lemma polynomial_advance : PolynomialTime advanceRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_pair polynomial_identity ResidualGraphProgram.polynomial_search)
    (polynomial_optionCases (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_first) polynomial_second)
        polynomial_augment)))

lemma search_residual_nonnegative {n : ℕ} (c : PublishedEdmondsKarp.Capacity n)
    (f : PublishedEdmondsKarp.Flow n) (s t : Fin n) (xs : List (Fin n))
    (h : ResidualSearch.search c f s t=some xs) :
    ∀ uv∈ResidualAugmentation.arcs xs,0≤(c uv.1 uv.2:ℤ)-f uv.1 uv.2 := by
  obtain ⟨k,p,rfl,hp,_⟩ := ResidualSearch.search_shortest c f s t xs h
  intro uv huv
  rw [ResidualAugmentation.arcs_ofFn] at huv
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp huv
  exact (hp.2.2.2 i).le

theorem advance_code {n : ℕ} (c : PublishedEdmondsKarp.Capacity n)
    (s t : Fin n) (hst : s≠t) (f : PublishedEdmondsKarp.Flow n)
    (hf : PublishedEdmondsKarp.Feasible c s t f) :
    advance ((natCode c,flowCode f),(s.val,t.val))=
      flowCode (EdmondsKarpAlgorithm.advance c s t f) := by
  cases hs : ResidualSearch.search c f s t with
  | none =>
    simp only [advance,ResidualGraphProgram.search_code,hs,Option.map_none,
      EdmondsKarpAlgorithm.advance,ResidualAugmentation.step,Option.getD_none]
  | some xs =>
    have hn := search_residual_nonnegative c f s t xs hs
    let a := bottleneck ((natCode c,flowCode f),xs.map Fin.val)
    have ha : (a:ℤ)=ResidualAugmentation.bottleneck c f xs := bottleneck_code c f xs hn
    have hstep : ResidualAugmentation.step c s t f=
        Option.some (ResidualAugmentation.listUpdate f xs (a:ℤ)) := by
      simp only [ResidualAugmentation.step,hs,Option.map_some,ha]
    have hnew := ResidualAugmentation.step_feasible c s t hst f _ hf hstep
    simp only [advance,ResidualGraphProgram.search_code,hs,Option.map_some]
    change updateMatrix ((natCode c,flowCode f),
      (arcPairs (xs.map Fin.val),a))=_
    rw [arcPairs_map,updateMatrix_code c s t f xs a hnew]
    simp only [EdmondsKarpAlgorithm.advance,hstep,Option.getD_some]

end ContingencyTables.FlowMatrixProgram

end OAI
