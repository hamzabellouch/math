import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeOptions

namespace OAI

namespace MatchingFPRAS.ExecutableOptions
open TreeTyped TreeFraction

variable {A : Type} [Codec A] [LinearOrder A]

def uniform (s : Finset A) : Options A :=
  (s.sort (·≤·)).map fun a=>(a,TreeFraction.normalize (1,s.card))
def uniformRealizer : Realizer (uniform (A:=A)) :=
  (composition (pair (composition (pair (constant 1) finsetCard) normalizeRealizer) finsetList)
    (mapWith (pair second first))).congr (fun _=>rfl)
lemma polynomial_uniform : PolynomialTime (uniformRealizer (A:=A)) := by
  unfold uniformRealizer
  apply polynomial_congr
  have := polynomial_normalize
  have := polynomial_mapWith (polynomial_pair (polynomial_second (A:=Fraction) (B:=A)) polynomial_first)
  tree_cost
omit [Codec A] in
lemma numbering_ofFn (s : Finset A) :
    List.ofFn (fun i=>(WeightedOptions.numbering s i).val)=s.sort (·≤·) := by
  apply List.ext_getElem
  · simp
  · intro i hi _
    simp only [List.getElem_ofFn]
    change s.orderEmbOfFin rfl ⟨i,by simpa using hi⟩ = (s.sort (·≤·))[i]
    rw [Finset.orderEmbOfFin_apply]
    rfl
omit [Codec A] in
lemma uniform_repr (s : Finset A) (hs : s.Nonempty) :
    uniform s=repr id (WeightedOptions.uniform s hs) := by
  unfold uniform repr
  rw [←numbering_ofFn,List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext i
  simp only [WeightedOptions.uniform,id_eq]
  simp only [Function.comp_def]
  rw [normalize_repr]
  congr 1
  simp only [val,Nat.cast_one,one_div]

def neighbors (x : (A×Finset A)×ℕ) : Options A :=
  ((x.1.2.sort (·≤·)).map fun a=>(a,TreeFraction.normalize (1,x.2)))++
    [(x.1.1,sub ((1,1),TreeFraction.normalize (x.1.2.card,x.2)))]
def neighborsRealizer : Realizer (neighbors (A:=A)) := by
  let headOptions : Realizer (fun x : (A×Finset A)×ℕ=>
      (x.1.2.sort (·≤·)).map fun a=>(a,TreeFraction.normalize (1,x.2))) :=
    (composition (pair (composition (pair (constant 1) second) normalizeRealizer)
      (composition first.snd finsetList)) (mapWith (pair second first))).congr (fun _=>rfl)
  let tailOptions : Realizer (fun x : (A×Finset A)×ℕ=>
      [(x.1.1,sub ((1,1),TreeFraction.normalize (x.1.2.card,x.2)))]) :=
    (composition (pair first.fst (composition (pair (constant (1,1))
      (composition (pair (composition first.snd finsetCard) second) normalizeRealizer)) subRealizer)) listSingleton).congr (fun _=>rfl)
  exact (composition (pair headOptions tailOptions) append).congr (fun _=>rfl)
lemma polynomial_neighbors : PolynomialTime (neighborsRealizer (A:=A)) := by
  unfold neighborsRealizer
  dsimp only [Realizer.fst, Realizer.snd]
  apply polynomial_congr
  have := polynomial_normalize
  have := polynomial_sub
  have := polynomial_listSingleton (A:=A×Fraction)
  have := polynomial_mapWith (polynomial_pair (polynomial_second (A:=Fraction) (B:=A)) polynomial_first)
  tree_cost
omit [Codec A] in
lemma neighbors_repr (a : A) (s : Finset A) (d : ℕ) (hd : s.card≤d) :
    neighbors ((a,s),d)=repr id (WeightedOptions.neighbors a s d hd) := by
  have hsub : (s.card:ℚ)/d≤1 := by
    by_cases hz : d=0
    · simp [hz]
    · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hz)).mpr (by exact_mod_cast hd)
  have hn : TreeFraction.normalize (s.card,d)=TreeFraction.repr ((s.card:ℚ)/d) := normalize_repr _
  have hu : TreeFraction.normalize (1,d)=TreeFraction.repr ((d:ℚ)⁻¹) := by
    simpa only [val,Nat.cast_one,one_div] using normalize_repr (1,d)
  have h1 : (1,1)=TreeFraction.repr 1 := rfl
  simp only [neighbors,repr,hn,hu,h1,sub_repr (by decide) (by positivity) hsub]
  simp only [WeightedOptions.neighbors]
  rw [List.ofFn_succ_last,←numbering_ofFn,List.map_ofFn]
  simp only [Fin.lastCases_castSucc,Fin.lastCases_last,id_eq,Function.comp_def]
end MatchingFPRAS.ExecutableOptions

end OAI
