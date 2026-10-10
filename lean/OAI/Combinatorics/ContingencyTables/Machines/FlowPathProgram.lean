import OAI.Combinatorics.ContingencyTables.Machines.ResidualGraphProgram
import OAI.Combinatorics.ContingencyTables.Transport.ResidualAugmentation
import OAI.Combinatorics.ContingencyTables.Machines.FiniteGraphRootProgram
import OAI.Combinatorics.ContingencyTables.Transport.FlowClamp

namespace OAI

/-! # Binary path bottlenecks and one integral flow-entry update -/

namespace ContingencyTables.FlowPathProgram

open MatchingFPRAS.TreeTyped DirectedBFSProgram ResidualGraphProgram SignedPairProgram

/-- Adjacent path entries, using only indices below the stored path length. -/
def arcPairs (xs : List ℕ) : List (ℕ×ℕ) :=
  (List.range (xs.length-1)).map (fun i=>(xs.getD i 0,xs.getD (i+1) 0))

def pairAt (z : List ℕ×ℕ) : ℕ×ℕ := (z.1.getD z.2 0,z.1.getD (z.2+1) 0)

def pairAtRealizer : Realizer pairAt :=
  pair (getDFast 0) (composition
    (pair first (composition second successor)) (getDFast 0))

lemma polynomial_pairAt : PolynomialTime pairAtRealizer :=
  polynomial_pair (polynomial_getDFast 0) (polynomial_composition
    (polynomial_pair polynomial_first (polynomial_composition polynomial_second
      polynomial_successor)) (polynomial_getDFast 0))

def arcIndices (xs : List ℕ) : List ℕ := List.range (xs.length-1)

def arcIndicesRealizer : Realizer arcIndices :=
  composition (composition listLength predecessor) range

lemma polynomial_arcIndices : PolynomialTime arcIndicesRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition polynomial_listLength polynomial_predecessor) Polynomial.X
  intro xs
  have h := list_length_le_weight xs
  simpa only [Function.comp_apply,Polynomial.eval_X] using (Nat.sub_le xs.length 1).trans h

def arcPairsRealizer : Realizer arcPairs :=
  composition (pair identity arcIndicesRealizer) (mapWith pairAtRealizer)

lemma polynomial_arcPairs : PolynomialTime arcPairsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_arcIndices)
    (polynomial_mapWith polynomial_pairAt)

lemma arcPairs_nil : arcPairs []=[] := rfl
lemma arcPairs_singleton (u : ℕ) : arcPairs [u]=[] := rfl

lemma arcPairs_cons_cons (u v : ℕ) (xs : List ℕ) :
    arcPairs (u::v::xs)=(u,v)::arcPairs (v::xs) := by
  simp [arcPairs,List.range_succ_eq_map,Function.comp_def]

lemma arcPairs_map {n : ℕ} (xs : List (Fin n)) :
    arcPairs (xs.map Fin.val)=
      (ResidualAugmentation.arcs xs).map (fun uv=>(uv.1.val,uv.2.val)) := by
  induction xs with
  | nil => rfl
  | cons u xs ih =>
    cases xs with
    | nil => rfl
    | cons v xs =>
      simpa only [List.map_cons,arcPairs_cons_cons,ResidualAugmentation.arcs] using
        congrArg (List.cons (u.val,v.val)) ih

def minimumScan (xs : List ℕ) : ℕ :=
  match xs with
  | [] => 0
  | a::as => as.foldl (fun b a=>min a b) a

def minimumScanRealizer : Realizer minimumScan :=
  (listCase 0 (composition (pair second first) (fold minimum))).congr (by
    intro xs
    cases xs <;> rfl)

lemma polynomial_minimumScan : PolynomialTime minimumScanRealizer :=
  polynomial_congr _ (polynomial_listCase 0 (polynomial_composition
    (polynomial_pair polynomial_second polynomial_first)
    FiniteGraphRootProgram.polynomial_minimumFold))

lemma minimumScan_eq (xs : List ℕ) : minimumScan xs=xs.min?.getD 0 := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    simp only [minimumScan,List.min?_cons',Option.getD_some]
    have he : (fun b a : ℕ=>min a b)=min := by
      funext b c
      exact min_comm c b
    rw [he]

lemma minimumFold_cast (xs : List ℕ) (a : ℕ) :
    ((xs.foldl (fun b a : ℕ=>min a b) a:ℕ):ℤ)=
      (xs.map (fun a : ℕ=>(a:ℤ))).foldl min (a:ℤ) := by
  induction xs generalizing a with
  | nil => rfl
  | cons b xs ih =>
    simp only [List.foldl_cons,List.map_cons]
    rw [ih,Nat.cast_min,min_comm (b:ℤ) (a:ℤ)]

lemma minimumScan_cast (xs : List ℕ) :
    (minimumScan xs:ℤ)=(xs.map (fun a : ℕ=>(a:ℤ))).min?.getD 0 := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    simp only [minimumScan,List.map_cons,List.min?_cons',Option.getD_some]
    exact minimumFold_cast xs a

def residuals (z : Data×List ℕ) : List ℕ :=
  (arcPairs z.2).map (fun uv=>residualValue (arcData (z.1,uv)))

def residualsRealizer : Realizer residuals :=
  composition (pair first (composition second arcPairsRealizer))
    (mapWith (composition arcDataRealizer residualValueRealizer))

lemma polynomial_residuals : PolynomialTime residualsRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_arcPairs))
    (polynomial_mapWith (polynomial_composition polynomial_arcData polynomial_residualValue))

def bottleneck (z : Data×List ℕ) : ℕ := minimumScan (residuals z)
def bottleneckRealizer : Realizer bottleneck := composition residualsRealizer minimumScanRealizer
lemma polynomial_bottleneck : PolynomialTime bottleneckRealizer :=
  polynomial_composition polynomial_residuals polynomial_minimumScan

lemma bottleneck_code {n : ℕ} (c : PublishedEdmondsKarp.Capacity n)
    (f : PublishedEdmondsKarp.Flow n) (xs : List (Fin n))
    (hres : ∀ uv∈ResidualAugmentation.arcs xs,0≤(c uv.1 uv.2:ℤ)-f uv.1 uv.2) :
    (bottleneck ((natCode c,flowCode f),xs.map Fin.val):ℤ)=
      ResidualAugmentation.bottleneck c f xs := by
  rw [bottleneck,minimumScan_cast]
  apply congrArg (fun zs : List ℤ=>zs.min?.getD 0)
  simp only [residuals,arcPairs_map,List.map_map]
  change (ResidualAugmentation.arcs xs).map (fun uv=>
      (residualValue (arcData ((natCode c,flowCode f),(uv.1.val,uv.2.val))):ℤ))=
    (ResidualAugmentation.arcs xs).map (fun uv=>(c uv.1 uv.2:ℤ)-f uv.1 uv.2)
  apply List.map_congr_left
  intro uv huv
  simp only [arcData,capacityEntry_code,flowEntry_code,
    residualValue_correct,SignedPairProgram.value,ForestAffineProgram.signedParts_sub]
  exact Int.toNat_of_nonneg (hres uv huv)

def pairEqual (z : (ℕ×ℕ)×(ℕ×ℕ)) : Bool :=
  decide (z.1.1=z.2.1) && decide (z.1.2=z.2.2)

def pairEqualRealizer : Realizer pairEqual :=
  composition (pair
    (composition (pair (composition first first) (composition second first)) natEqual)
    (composition (pair (composition first second) (composition second second)) natEqual)) boolAnd

lemma polynomial_pairEqual : PolynomialTime pairEqualRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_composition polynomial_second polynomial_first)) polynomial_natEqual)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition polynomial_second polynomial_second)) polynomial_natEqual))
    polynomial_boolAnd

def arcCount (z : (ℕ×ℕ)×List (ℕ×ℕ)) : ℕ :=
  (z.2.filter (fun uv=>pairEqual (z.1,uv))).length

def arcCountRealizer : Realizer arcCount :=
  composition (filterWith pairEqualRealizer) listLength

lemma polynomial_arcCount : PolynomialTime arcCountRealizer :=
  polynomial_composition (polynomial_filterWith polynomial_pairEqual) polynomial_listLength

lemma arcCount_cast (uv : ℕ×ℕ) (xs : List (ℕ×ℕ)) :
    (arcCount (uv,xs):ℤ)=(xs.map (fun xy=>if xy=uv then (1:ℤ) else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : a=uv
    · subst a
      simpa [arcCount,pairEqual,add_comm] using congrArg (fun z : ℤ=>1+z) ih
    · have he : pairEqual (uv,a)=false := by
        by_cases h1 : uv.1=a.1
        · by_cases h2 : uv.2=a.2
          · exact False.elim (h (Prod.ext h1.symm h2.symm))
          · simp [pairEqual,h1,h2]
        · simp [pairEqual,h1]
      simp only [arcCount,List.filter_cons,he,Bool.false_eq_true,ite_false,
        List.map_cons,h,ite_false,List.sum_cons,zero_add]
      exact ih

end ContingencyTables.FlowPathProgram

end OAI
