import OAI.Combinatorics.ContingencyTables.Machines.FractionAcceptanceProgram
import OAI.Combinatorics.ContingencyTables.Transport.FiniteObservableTransport

namespace OAI

/-! # Clipped rational Metropolis acceptance as a binary program -/

namespace ContingencyTables.FractionMetropolisProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev Input := (TreeFraction.Fraction × TreeFraction.Fraction) × List Bool

def ratio (z : Input) : TreeFraction.Fraction := TreeFraction.div (z.1.2,z.1.1)
def ratioRealizer : Realizer ratio :=
  composition (f := fun z : Input => (z.1.2,z.1.1)) (g := TreeFraction.div)
    (pair (composition first second) (composition first first)) TreeFraction.divRealizer
lemma polynomial_ratio : PolynomialTime ratioRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition polynomial_first polynomial_first)) TreeFraction.polynomial_div

def belowOne (z : Input) : Bool := TreeFraction.less (ratio z,(1,1))
def belowOneRealizer : Realizer belowOne :=
  composition (f := fun z : Input => (ratio z,(1,1))) (g := TreeFraction.less)
    (pair ratioRealizer (constant (1,1))) TreeFraction.lessRealizer
lemma polynomial_belowOne : PolynomialTime belowOneRealizer :=
  polynomial_composition (polynomial_pair polynomial_ratio (polynomial_constant _)) TreeFraction.polynomial_less

def probability (z : Input) : TreeFraction.Fraction := if belowOne z then ratio z else (1,1)
def probabilityRealizer : Realizer probability := choose belowOneRealizer ratioRealizer (constant (1,1))
lemma polynomial_probability : PolynomialTime probabilityRealizer :=
  polynomial_choose polynomial_belowOne polynomial_ratio (polynomial_constant _)

attribute [local irreducible] probability

def accept (z : Input) : Bool := FractionAcceptanceProgram.acceptCode (probability z,z.2)
def acceptRealizer : Realizer accept :=
  composition (f := fun z : Input => (probability z,z.2)) (g := FractionAcceptanceProgram.acceptCode)
    (pair probabilityRealizer second) FractionAcceptanceProgram.acceptCodeRealizer
lemma polynomial_accept : PolynomialTime acceptRealizer :=
  polynomial_composition (polynomial_pair polynomial_probability polynomial_second)
    FractionAcceptanceProgram.polynomial_acceptCode

lemma probability_value (x y : TreeFraction.Fraction) (bits : List Bool) :
    TreeFraction.val (probability ((x,y),bits))=min 1 (TreeFraction.val y/TreeFraction.val x) := by
  have hd : 0 < (ratio ((x,y),bits)).2 := TreeFraction.normalize_den_pos _
  have hr : TreeFraction.val (ratio ((x,y),bits))=TreeFraction.val y/TreeFraction.val x :=
    TreeFraction.div_val y x
  unfold probability belowOne
  rw [TreeFraction.less_val _ _ hd (by decide)]
  have hone : TreeFraction.val (1,1)=(1:ℚ) := by norm_num [TreeFraction.val]
  rw [hone]
  by_cases h : TreeFraction.val (ratio ((x,y),bits)) < 1
  · simp only [h,decide_true,ite_true]
    rw [hr]
    exact (min_eq_right (by simpa only [hr] using h.le)).symm
  · simp only [h,decide_false,Bool.false_eq_true,ite_false,hone]
    exact (min_eq_left (by simpa only [hr] using le_of_not_gt h)).symm

lemma accept_ofFn (x y : TreeFraction.Fraction) (B : ℕ) (bits : Fin B → Bool) :
    accept ((x,y),List.ofFn bits)=
      decide (FairBits.rationalThresholdAccept B (min 1 (TreeFraction.val y/TreeFraction.val x)) bits) := by
  rw [accept,FractionAcceptanceProgram.acceptCode_ofFn,probability_value]

noncomputable section
open FiniteObservableTransport
open scoped Classical

/-- Independent exact observable laws suffice for the implemented coin;
no finite type of rational weight values is required. -/
theorem sameLaw_accept {X Y U V : Type*} [Fintype X] [Fintype Y] [Fintype U] [Fintype V]
    (current : X → TreeFraction.Fraction) (target : U → TreeFraction.Fraction)
    (f : Y → ℚ) (g : V → ℚ)
    (hf : SameLaw (fun x => TreeFraction.val (current x)) f)
    (hg : SameLaw (fun u => TreeFraction.val (target u)) g) (B : ℕ) :
    SameLaw (fun z : (X × U) × (Fin B → Bool) =>
      accept ((current z.1.1,target z.1.2),List.ofFn z.2))
      (fun z : (Y × V) × (Fin B → Bool) =>
        decide (FairBits.rationalThresholdAccept B (min 1 (g z.1.2/f z.1.1)) z.2)) := by
  have hid : SameLaw (fun x : Fin B → Bool => x) (fun x : Fin B → Bool => x) := fun _ => rfl
  have hs := (hf.prod hg).prod hid
  intro phi
  simp_rw [accept_ofFn]
  exact hs (fun z => phi (decide (FairBits.rationalThresholdAccept B (min 1 (z.1.2/z.1.1)) z.2)))

end

end ContingencyTables.FractionMetropolisProgram

end OAI
