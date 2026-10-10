import OAI.Combinatorics.ContingencyTables.Transport.DyadicRootBisection
import OAI.Combinatorics.ContingencyTables.Machines.BinaryPowerProgram
import OAI.Combinatorics.MatchingCount.Machines.TreeFiniteOps
import OAI.Combinatorics.MatchingCount.Complexity.TreePolyTactic

namespace OAI

/-! # Polynomial binary execution of the rational correction bisection

The root degree is the length of a supplied allowance list. One fixed
depth list controls the outer loop. Thus both natural-power evaluation
and the bisection loop have polynomial cost in the supplied binary data
and the two explicit allowances.
-/

namespace ContingencyTables.DyadicRootProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

def powerInput (z : ℕ×List Bool) : ℕ×ℕ := (z.1,z.2.length)
def powerInputRealizer : Realizer powerInput := pair first (composition second listLength)
lemma polynomial_powerInput : PolynomialTime powerInputRealizer := by
  unfold powerInputRealizer
  exact polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_listLength)

def markedPower (z : ℕ×List Bool) : ℕ := BinaryPowerPrograms.power (powerInput z)
def markedPowerRealizer : Realizer markedPower :=
  composition powerInputRealizer BinaryPowerPrograms.powerRealizer

lemma polynomial_markedPower : PolynomialTime markedPowerRealizer := by
  apply work_composition polynomial_powerInput BinaryPowerPrograms.work_power X
  intro z
  have hl:=list_length_le_weight z.2
  simp only [powerInput,eval_X]
  rw [←Prod.eta z,weight_prod]
  dsimp only
  omega

lemma markedPower_eq (a : ℕ) (xs : List Bool) : markedPower (a,xs)=a^xs.length :=
  BinaryPowerPrograms.power_eq a xs.length

abbrev Parameters := TreeFraction.Fraction×List Bool
abbrev State := Parameters×DyadicRootBisection.State

private def lowRealizer : Realizer (fun z : State=>z.2.1.1) :=
  composition (composition second first) first
private def highRealizer : Realizer (fun z : State=>z.2.1.2) :=
  composition (composition second first) second
private def denominatorRealizer : Realizer (fun z : State=>z.2.2) := composition second second
private def numeratorRealizer : Realizer (fun z : State=>z.1.1.1) :=
  composition (composition first first) first
private def targetDenominatorRealizer : Realizer (fun z : State=>z.1.1.2) :=
  composition (composition first first) second
private def allowanceRealizer : Realizer (fun z : State=>z.1.2) := composition first second

private lemma polynomial_low : PolynomialTime lowRealizer := by unfold lowRealizer; tree_poly
private lemma polynomial_high : PolynomialTime highRealizer := by unfold highRealizer; tree_poly
private lemma polynomial_denominator : PolynomialTime denominatorRealizer := by
  unfold denominatorRealizer; tree_poly
private lemma polynomial_numerator : PolynomialTime numeratorRealizer := by
  unfold numeratorRealizer; tree_poly
private lemma polynomial_targetDenominator : PolynomialTime targetDenominatorRealizer := by
  unfold targetDenominatorRealizer; tree_poly
private lemma polynomial_allowance : PolynomialTime allowanceRealizer := by
  unfold allowanceRealizer; tree_poly

def mid (z : State) : ℕ := z.2.1.1+z.2.1.2
def midRealizer : Realizer mid := composition (pair lowRealizer highRealizer) add
lemma polynomial_mid : PolynomialTime midRealizer :=
  polynomial_composition (polynomial_pair polynomial_low polynomial_high) polynomial_add

def twiceDenominator (z : State) : ℕ := 2*z.2.2
def twiceDenominatorRealizer : Realizer twiceDenominator :=
  composition (f:=fun z : State=>(2,z.2.2)) (g:=fun p : ℕ×ℕ=>p.1*p.2)
    (pair (constant 2) denominatorRealizer) multiply
lemma polynomial_twiceDenominator : PolynomialTime twiceDenominatorRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 2) polynomial_denominator)
    polynomial_multiply

def leftProduct (z : State) : ℕ := markedPower (mid z,z.1.2)*z.1.1.2
def leftProductRealizer : Realizer leftProduct :=
  composition (pair
    (composition (pair midRealizer allowanceRealizer) markedPowerRealizer)
    targetDenominatorRealizer) multiply
lemma polynomial_leftProduct : PolynomialTime leftProductRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_mid polynomial_allowance)
      polynomial_markedPower) polynomial_targetDenominator) polynomial_multiply

def rightProduct (z : State) : ℕ := z.1.1.1*markedPower (twiceDenominator z,z.1.2)
def rightProductRealizer : Realizer rightProduct :=
  composition (pair numeratorRealizer
    (composition (pair twiceDenominatorRealizer allowanceRealizer) markedPowerRealizer)) multiply
lemma polynomial_rightProduct : PolynomialTime rightProductRealizer :=
  polynomial_composition (polynomial_pair polynomial_numerator
    (polynomial_composition (polynomial_pair polynomial_twiceDenominator polynomial_allowance)
      polynomial_markedPower)) polynomial_multiply

def test (z : State) : Bool := decide (leftProduct z≤rightProduct z)
def testRealizer : Realizer test := composition (pair leftProductRealizer rightProductRealizer) leNat
lemma polynomial_test : PolynomialTime testRealizer :=
  polynomial_composition (polynomial_pair polynomial_leftProduct polynomial_rightProduct)
    polynomial_leNat

private def lowerBranchRealizer : Realizer (fun z : State=>
    ((mid z,2*z.2.1.2),twiceDenominator z)) :=
  pair (pair midRealizer (composition
    (f:=fun z : State=>(2,z.2.1.2)) (g:=fun p : ℕ×ℕ=>p.1*p.2)
    (pair (constant 2) highRealizer) multiply))
    twiceDenominatorRealizer
private def upperBranchRealizer : Realizer (fun z : State=>
    ((2*z.2.1.1,mid z),twiceDenominator z)) :=
  pair (pair (composition
    (f:=fun z : State=>(2,z.2.1.1)) (g:=fun p : ℕ×ℕ=>p.1*p.2)
    (pair (constant 2) lowRealizer) multiply) midRealizer)
    twiceDenominatorRealizer

def next (z : State) : State :=
  (z.1,if test z then ((mid z,2*z.2.1.2),twiceDenominator z)
    else ((2*z.2.1.1,mid z),twiceDenominator z))
def nextRealizer : Realizer next :=
  pair first (choose testRealizer lowerBranchRealizer upperBranchRealizer)

lemma polynomial_next : PolynomialTime nextRealizer := by
  apply polynomial_pair polynomial_first
  apply polynomial_choose polynomial_test
  · exact polynomial_pair (polynomial_pair polynomial_mid
      (polynomial_composition (polynomial_pair (polynomial_constant 2) polynomial_high)
        polynomial_multiply)) polynomial_twiceDenominator
  · exact polynomial_pair (polynomial_pair
      (polynomial_composition (polynomial_pair (polynomial_constant 2) polynomial_low)
        polynomial_multiply) polynomial_mid) polynomial_twiceDenominator

lemma next_eq (z : State) :
    next z=(z.1,DyadicRootBisection.advance z.1.1 z.1.2.length z.2) := by
  simp only [next,test,leftProduct,rightProduct,markedPower_eq,mid,twiceDenominator,
    DyadicRootBisection.advance,decide_eq_true_eq]

def height (z : DyadicRootBisection.State) : ℕ := max (max z.1.1.size z.1.2.size) z.2.size

private lemma size_double (a : ℕ) : (2*a).size≤a.size+1 := by
  simpa only [two_mul,max_self] using nat_size_add a a

lemma height_advance (c : TreeFraction.Fraction) (s : ℕ) (z : DyadicRootBisection.State) :
    height (DyadicRootBisection.advance c s z)≤height z+1 := by
  have hm:=nat_size_add z.1.1 z.1.2
  have ha:=size_double z.1.1
  have hb:=size_double z.1.2
  have hd:=size_double z.2
  unfold DyadicRootBisection.advance height
  split_ifs <;> dsimp only <;> omega

def advance (z : Bool×State) : State := next z.2
def advanceRealizer : Realizer advance := composition second nextRealizer
lemma polynomial_advance : PolynomialTime advanceRealizer :=
  polynomial_composition polynomial_second polynomial_next

lemma fold_parameters (xs : List Bool) (z : State) :
    (xs.foldl (fun z a=>advance (a,z)) z).1=z.1 := by
  induction xs generalizing z with
  | nil=>rfl
  | cons a xs ih=>exact ih (next z)

lemma fold_height (xs : List Bool) (z : State) :
    height (xs.foldl (fun z a=>advance (a,z)) z).2≤height z.2+xs.length := by
  induction xs generalizing z with
  | nil=>simp only [List.foldl_nil,List.length_nil,Nat.add_zero,le_refl]
  | cons a xs ih=>
    have hh:=height_advance z.1.1 z.1.2.length z.2
    have ht:=ih (next z)
    have hn: height (next z).2≤height z.2+1 := by
      rw [next_eq]
      exact hh
    change height (xs.foldl (fun z a=>advance (a,z)) (next z)).2≤
      height z.2+(xs.length+1)
    omega

lemma height_le_weight (z : DyadicRootBisection.State) : height z≤weight z := by
  have ha: z.1.1.size≤weight z :=
    (size_le_weight _).trans ((weight_fst z.1).trans (weight_fst z))
  have hb: z.1.2.size≤weight z :=
    (size_le_weight _).trans ((weight_snd z.1).trans (weight_fst z))
  have hd: z.2.size≤weight z := (size_le_weight _).trans (weight_snd z)
  exact max_le (max_le ha hb) hd

lemma polynomial_loop : PolynomialTime (fold advanceRealizer) := by
  apply polynomial_fold polynomial_advance (30*(X+1))
  intro xs z pre post he
  let S:=weight (xs,z)
  let out:=pre.foldl (fun z a=>advance (a,z)) z
  have hz: weight z≤S:=weight_snd (xs,z)
  have hp: weight z.1≤S:=(weight_fst z).trans hz
  have hs: height z.2≤S:=(height_le_weight z.2).trans ((weight_snd z).trans hz)
  have hl: pre.length≤S:=(list_length_le_weight pre).trans
    ((weight_prefix he).trans (weight_fst (xs,z)))
  have hh:=fold_height pre z
  change height out.2≤height z.2+pre.length at hh
  have hctx: out.1=z.1:=fold_parameters pre z
  have h1:=weight_nat_le out.2.1.1
  have h2:=weight_nat_le out.2.1.2
  have h3:=weight_nat_le out.2.2
  have hs1: out.2.1.1.size≤height out.2:=
    (le_max_left _ _).trans (le_max_left _ _)
  have hs2: out.2.1.2.size≤height out.2:=
    (le_max_right _ _).trans (le_max_left _ _)
  have hs3: out.2.2.size≤height out.2:=le_max_right _ _
  have hw: weight out=weight out.1+weight out.2.1.1+weight out.2.1.2+weight out.2.2+3 := by
    change weight (out.1,((out.2.1.1,out.2.1.2),out.2.2))=_
    simp only [weight_prod]
    omega
  simp only [eval_mul,eval_ofNat,eval_add,eval_X,eval_one]
  change weight out≤30*(S+1)
  rw [hw,hctx]
  omega

abbrev Input := Parameters×List Bool
def prepare (z : Input) : List Bool×State := (z.2,(z.1,((0,8),1)))
def prepareRealizer : Realizer prepare := pair second (pair first (constant ((0,8),1)))
lemma polynomial_prepare : PolynomialTime prepareRealizer := by
  unfold prepareRealizer
  exact polynomial_pair polynomial_second
    (polynomial_pair polynomial_first (polynomial_constant ((0,8),1)))

def execute (z : Input) : State := z.2.foldl (fun s a=>advance (a,s)) (z.1,((0,8),1))
def executeRealizer : Realizer execute := composition prepareRealizer (fold advanceRealizer)
lemma polynomial_execute : PolynomialTime executeRealizer :=
  polynomial_composition polynomial_prepare polynomial_loop

def finish (z : State) : TreeFraction.Fraction :=
  TreeFraction.normalize (mid z,twiceDenominator z)
def finishRealizer : Realizer finish :=
  composition (pair midRealizer twiceDenominatorRealizer) TreeFraction.normalizeRealizer
lemma polynomial_finish : PolynomialTime finishRealizer :=
  polynomial_composition (polynomial_pair polynomial_mid polynomial_twiceDenominator)
    TreeFraction.polynomial_normalize

def output (z : Input) : TreeFraction.Fraction := finish (execute z)
def outputRealizer : Realizer output := composition executeRealizer finishRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_execute polynomial_finish

lemma fold_eq (xs : List Bool) (p : Parameters) (z : DyadicRootBisection.State) :
    xs.foldl (fun z a=>advance (a,z)) (p,z)=
      (p,(DyadicRootBisection.advance p.1 p.2.length)^[xs.length] z) := by
  induction xs generalizing z with
  | nil=>rfl
  | cons a xs ih=>
    rw [List.foldl_cons]
    change xs.foldl (fun z a=>advance (a,z)) (next (p,z))=_
    rw [next_eq,ih]
    simp only [List.length_cons,Function.iterate_succ_apply]

theorem output_eq (c : TreeFraction.Fraction) (degree depth : List Bool) :
    output ((c,degree),depth)=DyadicRootBisection.output c degree.length depth.length := by
  have hr (k : ℕ) :
      (DyadicRootBisection.advance c degree.length)^[k] ((0,8),1)=
        DyadicRootBisection.run c degree.length k := by
    induction k with
    | zero=>rfl
    | succ k ih=>rw [Function.iterate_succ_apply',ih,DyadicRootBisection.run]
  simp only [output,execute,fold_eq,hr,finish,mid,twiceDenominator,DyadicRootBisection.output]

theorem output_value (c : TreeFraction.Fraction) (hc : 0<c.2) (degree depth : List Bool) :
    TreeFraction.val (output ((c,degree),depth))=
      RationalRootBisection.midpoint (TreeFraction.val c) degree.length depth.length := by
  rw [output_eq]
  exact DyadicRootBisection.output_value c hc _ _

end ContingencyTables.DyadicRootProgram

end OAI
