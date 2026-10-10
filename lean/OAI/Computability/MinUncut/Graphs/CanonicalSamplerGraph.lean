import Mathlib
import OAI.Computability.MinUncut.Estimates.LiteralLocalTemplates
import OAI.Computability.MinUncut.Estimates.ReversePrefixProgram
import OAI.Computability.MinUncut.Encoding.RawGraphEncoding

namespace OAI

section
open scoped BigOperators
namespace MinUncut.PathRealization
open MinUncut.FiniteProof MinUncutGames.Foundations.Hastad.SourceOccurrences

lemma listFailure_map {V W : Type*} (f : V → W) (ds : List (Demand V)) (s : W → Bool) :
    listFailure (ds.map (Demand.map f)) s=listFailure ds (s ∘ f) := by
  simp only [listFailure,List.map_map,Function.comp_def,failure_map]

def listOutput {N : ℕ} (ds : List (Demand (Fin N))) (k : ℕ) (hk : 1≤k) : Output :=
  canonicalOutput (fun i : Fin ds.length => ds[i]) k hk

lemma listOutput_yes {N : ℕ} (ds : List (Demand (Fin N))) (k : ℕ) (hk : 1≤k)
    (s : Fin N → Bool) (hs : listFailure ds s≤k) : (listOutput ds k hk).opt≤k :=
  canonicalOutput_yes _ k hk s (by simpa only [← listFailure_eq] using hs)

lemma listOutput_no {N : ℕ} (ds : List (Demand (Fin N))) (k : ℕ) (hk : 1≤k)
    (K : ℕ) (hs : ∀ s, K*k<listFailure ds s) : K*k<(listOutput ds k hk).opt :=
  canonicalOutput_no _ k hk K (by simpa only [← listFailure_eq] using hs)

lemma listFailure_weight {E V : Type} [Fintype E] (D : ℕ) (w : E → ℚ)
    (hw : ∀e,0≤w e) (hd : ∀e,(w e).den∣D) (d : E → Demand V)
    (enc : Encoding E) (s : V → Bool) :
    (listFailure (demandList D w d enc) s:ℝ)=(D:ℝ)*∑e,(w e:ℝ)*(failure (d e) s:ℝ) := by
  rw [listFailure_demandList,← expanded_failure]
  exact expanded_weight D w hw hd d s

lemma listFailure_extend {V W : Type*} (f : V → W) (hf : Function.Injective f)
    (ds : List (Demand V)) (s : V → Bool) :
    listFailure (ds.map (Demand.map f)) (extendAssignment f s)=listFailure ds s := by
  simp only [listFailure,List.map_map,Function.comp_def,mapDemand_extend f hf]

end MinUncut.PathRealization

noncomputable section
namespace MinUncut.Outer.Parameters
open MinUncut.Inner MinUncut.FiniteProof MinUncut.PathRealization
attribute [local instance] Classical.propDecidable

variable {N s J : ℕ} [Nonempty (Fin s)]

def canonicalDemands (P : Parameters J) (eqs : Fin s → Equation (Fin N)) :
    List (Demand (Fin (paddedVariableEncoding N P.o.t).size)) :=
  (demandList (P.denominator (Fin s)) (P.weight eqs) (P.demand eqs)
    (SampleEnumeration.all eqs P.o.k P.d.m P.d.n P.grid).encoding).map (Demand.map variableCode)

def canonicalGraph (P : Parameters J) (eqs : Fin s → Equation (Fin N)) : Output :=
  listOutput (P.canonicalDemands eqs) (5*P.denominator (Fin s))
    (threshold_positive P.denominator_pos)

lemma canonicalGraph_failure (P : Parameters J) (eqs : Fin s → Equation (Fin N))
    (y : Fin (paddedVariableEncoding N P.o.t).size → Bool) :
    (listFailure (P.canonicalDemands eqs) y:ℝ)=
      (P.denominator (Fin s):ℝ)*∑e,(P.weight eqs e:ℝ)*
        (failure (P.demand eqs e) (y ∘ variableCode):ℝ) := by
  unfold canonicalDemands
  rw [listFailure_map]
  exact listFailure_weight _ _ (P.weight_nonneg eqs) (P.weight_den eqs) _ _ _

lemma canonicalGraph_yes (P : Parameters J) (eqs : Fin s → Equation (Fin N))
    (y : FamilyVariable (Fin N) (Fin P.o.t) → Bool)
    (hy : ∑e,(P.weight eqs e:ℝ)*(failure (P.demand eqs e) y:ℝ)≤9/2) :
    (P.canonicalGraph eqs).opt≤(P.canonicalGraph eqs).threshold := by
  apply listOutput_yes _ _ _ (extendAssignment variableCode y)
  have hh := listFailure_weight (P.denominator (Fin s)) (P.weight eqs)
    (P.weight_nonneg eqs) (P.weight_den eqs) (P.demand eqs)
    (SampleEnumeration.all eqs P.o.k P.d.m P.d.n P.grid).encoding y
  have he : listFailure (P.canonicalDemands eqs) (extendAssignment variableCode y)=
      listFailure (demandList (P.denominator (Fin s)) (P.weight eqs) (P.demand eqs)
        (SampleEnumeration.all eqs P.o.k P.d.m P.d.n P.grid).encoding) y :=
    listFailure_extend variableCode variableCode_injective _ y
  have hD : (0:ℝ)<P.denominator (Fin s) := by exact_mod_cast P.denominator_pos
  have hs : (listFailure (P.canonicalDemands eqs) (extendAssignment variableCode y):ℝ)≤
      5*P.denominator (Fin s) := by
    rw [he,hh]
    calc
      _ ≤ (P.denominator (Fin s):ℝ)*5 :=
        mul_le_mul_of_nonneg_left (hy.trans (by norm_num)) hD.le
      _ = _ := mul_comm _ _
  exact_mod_cast hs

lemma canonicalGraph_no {K : ℕ} (hK : 2≤K) (P : Parameters J)
    (eqs : Fin s → Equation (Fin N))
    (hy : ∀ y, 8*(K:ℝ)-1/2 < ∑e,(P.weight eqs e:ℝ)*(failure (P.demand eqs e) y:ℝ)) :
    K*(P.canonicalGraph eqs).threshold<(P.canonicalGraph eqs).opt := by
  apply listOutput_no
  intro y
  have hh := P.canonicalGraph_failure eqs y
  have hK' : (2:ℝ)≤K := by exact_mod_cast hK
  have hD : (0:ℝ)<P.denominator (Fin s) := by exact_mod_cast P.denominator_pos
  have hg : 5*(K:ℝ)<∑e,(P.weight eqs e:ℝ)*(failure (P.demand eqs e) (y ∘ variableCode):ℝ) :=
    lt_trans (by linarith) (hy (y ∘ variableCode))
  have hs : (K:ℝ)*(5*P.denominator (Fin s))<
      (listFailure (P.canonicalDemands eqs) y:ℝ) := by
    rw [hh]
    have h := mul_lt_mul_of_pos_left hg hD
    simpa only [mul_assoc,mul_comm,mul_left_comm] using h
  exact_mod_cast hs

end MinUncut.Outer.Parameters

end
end
namespace MinUncut.Costed.GraphRegisters
open MinUncut.PathRealization

lemma finRange_vals (V : ℕ) : (List.finRange V).map Fin.val=List.range V := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

def canonicalTable {N : ℕ} (ds : List (Demand (Fin N))) : List Bool :=
  (List.finRange (N+ds.length*3)).flatMap fun u=>
    (List.finRange (N+ds.length*3)).map fun v=>canonicalAdjacent (fun d:Fin ds.length=>ds[d]) u v

lemma rawRow_pack {N : ℕ} (ds : List (Demand (Fin N))) (u : Fin (N+ds.length*3)) :
    rawRow N ds.length (packDemands ds) u.val (N+ds.length*3)=
      ((List.finRange (N+ds.length*3)).map fun v=>
        canonicalAdjacent (fun d:Fin ds.length=>ds[d]) u v).map Bool.toNat := by
  rw [rawRow,←finRange_vals,List.map_map,List.map_map]
  congr 1
  funext v
  exact rawCell_canonical ds u v

lemma rawTable_pack {N : ℕ} (ds : List (Demand (Fin N))) :
    rawTable N ds.length (packDemands ds) (N+ds.length*3) (N+ds.length*3)=
      (canonicalTable ds).map Bool.toNat := by
  rw [rawTable,←finRange_vals,List.flatMap_map,canonicalTable,List.map_flatMap]
  congr 1
  funext u
  exact rawRow_pack ds u

lemma listOutput_bits {N : ℕ} (ds : List (Demand (Fin N))) (k : ℕ) (hk : 1≤k) :
    (listOutput ds k hk).bits=MinUncutGames.BinaryEncoding.nameBits (N+ds.length*3)++
      canonicalTable ds++MinUncutGames.BinaryEncoding.nameBits k := rfl

end MinUncut.Costed.GraphRegisters

noncomputable section
namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncut.PathRealization MinUncutGames.Reduction MinUncut.SourceBridge
open MinUncutGames.Foundations.Hastad.SourceOccurrences

variable {t k m n : ℕ} {g : MinUncut.FiniteGaussian.GridData}

def demandExpressions (σ η : ℚ) (e : Index (Fin t) k m n g) : List AExpr :=
  let T := indexQuery σ η e
  [leftExpr T e.2.2.1,rightExpr T e.2.2.1,signExpr T e.2.2.1]

def localExpressions (E : Enumeration (Index (Fin t) k m n g)) (a : ℚ)
    (b : MinUncut.Outer.Test → ℚ) (σ η : ℚ) : List AExpr :=
  E.values.flatMap (fun e=>(List.replicate (repetitions a b e) (demandExpressions σ η e)).flatten)

def tupleDemands (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (E : Enumeration (Index (Fin t) k m n g)) (a : ℚ) (b : MinUncut.Outer.Test → ℚ)
    (σ η : ℚ) : List (Demand (Fin (paddedVariableEncoding input.«variables» t).size)) :=
  E.values.flatMap (fun e=>List.replicate (repetitions a b e)
    ((allDemand (equations input) g σ η (occurrence (equations input) (u,e))).map variableCode))

lemma demandExpressions_eval (input : SourceEncoding.Input)
    (u : Fin t → Fin input.equations.length) (e : Index (Fin t) k m n g) (σ η : ℚ) (rest : List ℕ) :
    (demandExpressions σ η e).map (fun x=>x.eval (inputTuple input u++rest))=
      GraphRegisters.packDemand ((allDemand (equations input) g σ η
        (occurrence (equations input) (u,e))).map variableCode) := by
  change queryWords (indexQuery σ η e) e.2.2.1 (inputTuple input u++rest)=_
  rw [queryWords_append,queryWords_eq,occurrence_demand]
  rfl

lemma localExpressions_eval (input : SourceEncoding.Input)
    (u : Fin t → Fin input.equations.length) (E : Enumeration (Index (Fin t) k m n g))
    (a : ℚ) (b : MinUncut.Outer.Test → ℚ) (σ η : ℚ) (rest : List ℕ) :
    (localExpressions E a b σ η).map (fun x=>x.eval (inputTuple input u++rest))=
      GraphRegisters.packDemands (tupleDemands input u E a b σ η) := by
  simp only [localExpressions,tupleDemands,GraphRegisters.packDemands,List.map_flatMap,
    List.map_flatten,List.flatMap_assoc]
  apply congrArg (List.flatMap · E.values)
  funext e
  simp only [List.map_replicate, demandExpressions_eval,List.flatMap_replicate]

def tupleList (input : SourceEncoding.Input) (t : ℕ) : List (Fin t → Fin input.equations.length) :=
  (List.finRange (input.equations.length^t)).map finFunctionFinEquiv.symm

def generatedDemands (input : SourceEncoding.Input) (E : Enumeration (Index (Fin t) k m n g))
    (a : ℚ) (b : MinUncut.Outer.Test → ℚ) (σ η : ℚ) :
    List (Demand (Fin (paddedVariableEncoding input.«variables» t).size)) :=
  (tupleList input t).flatMap (fun u=>tupleDemands input u E a b σ η)

lemma emitted_demands (input : SourceEncoding.Input) (E : Enumeration (Index (Fin t) k m n g))
    (a : ℚ) (b : MinUncut.Outer.Test → ℚ) (σ η : ℚ) (rest : List ℕ) :
    Blocks.emitted (localExpressions E a b σ η) (input.equations.length^t)
      (SourceEncoding.inputWords input++rest)=
      GraphRegisters.packDemands (generatedDemands input E a b σ η) := by
  rw [Blocks.emitted,←GraphRegisters.finRange_vals]
  simp only [generatedDemands,tupleList,List.flatMap_map,GraphRegisters.packDemands,
    List.flatMap_assoc]
  apply congrArg (List.flatMap · (List.finRange (input.equations.length^t)))
  funext z
  have h := localExpressions_eval input (finFunctionFinEquiv.symm z) E a b σ η rest
  simpa only [Blocks.block,inputTuple,Equiv.apply_symm_apply,List.cons_append,GraphRegisters.packDemands] using h

end MinUncut.Costed.SourceWords

end

end OAI
