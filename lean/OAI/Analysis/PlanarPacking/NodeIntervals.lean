import OAI.Analysis.PlanarPacking.Entries
import OAI.Analysis.PlanarPacking.Nodes

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid
namespace Numerical

def qSmall : RBox := ((piBounds.mul piBounds).scale 2 3).mul
  ((RBox.rat 2 1).add (bBounds.scale (-2) 1))
def qLarge : RBox := ((piBounds.mul piBounds).scale 2 3).mul
  ((RBox.rat 2 1).add (bBounds.scale 2 1))
def qBase : RBox := (piBounds.mul piBounds).scale 1 3

def dSmall : RBox := (piBounds.mul ((RBox.rat 3 1).add (bBounds.scale 2 1))).scale 1 18
def dOther : RBox := (piBounds.mul ((RBox.rat 3 1).add (bBounds.scale (-2) 1))).scale 1 18
def dBase : RBox := (piBounds.mul bBounds).scale 7 9

lemma qSmall_contains : qSmall.Contains ((2*Real.pi^2/3)*(2-2*b)) := by
  have hp := RBox.contains_scale (RBox.contains_mul piBounds_contains piBounds_contains) 2 3 (by norm_num)
  have hb := RBox.contains_add (RBox.contains_rat 2 1 (by norm_num))
    (RBox.contains_scale bBounds_contains (-2) 1 (by norm_num))
  convert RBox.contains_mul hp hb using 1 <;> norm_num [qSmall,qLarge,dSmall,dOther,dBase,b]; ring
lemma qLarge_contains : qLarge.Contains ((2*Real.pi^2/3)*(2+2*b)) := by
  have hp := RBox.contains_scale (RBox.contains_mul piBounds_contains piBounds_contains) 2 3 (by norm_num)
  have hb := RBox.contains_add (RBox.contains_rat 2 1 (by norm_num))
    (RBox.contains_scale bBounds_contains 2 1 (by norm_num))
  convert RBox.contains_mul hp hb using 1 <;> norm_num [qSmall,qLarge,dSmall,dOther,dBase,b]; ring_nf; simp
lemma qBase_contains : qBase.Contains (Real.pi^2/3) := by
  convert RBox.contains_scale (RBox.contains_mul piBounds_contains piBounds_contains) 1 3 (by norm_num) using 1 <;> norm_num [qBase]; ring
lemma dSmall_contains : dSmall.Contains (Real.pi*(3+2*b)/18) := by
  have hb := RBox.contains_add (RBox.contains_rat 3 1 (by norm_num))
    (RBox.contains_scale bBounds_contains 2 1 (by norm_num))
  convert RBox.contains_scale (RBox.contains_mul piBounds_contains hb) 1 18 (by norm_num) using 1 <;> norm_num [qSmall,qLarge,dSmall,dOther,dBase,b]; ring
lemma dOther_contains : dOther.Contains (Real.pi*(3-2*b)/18) := by
  have hb := RBox.contains_add (RBox.contains_rat 3 1 (by norm_num))
    (RBox.contains_scale bBounds_contains (-2) 1 (by norm_num))
  convert RBox.contains_scale (RBox.contains_mul piBounds_contains hb) 1 18 (by norm_num) using 1 <;> norm_num [qSmall,qLarge,dSmall,dOther,dBase,b]; ring
lemma dBase_contains : dBase.Contains (7*Real.pi*b/9) := by
  convert RBox.contains_scale (RBox.contains_mul piBounds_contains bBounds_contains) 7 9 (by norm_num) using 1 <;> norm_num [qSmall,qLarge,dSmall,dOther,dBase,b]; ring

def qBox (n : ℕ) : RBox := if n%12=0 ∨ n%12=4 then qBase else if n%12=1 ∨ n%12=3 then qSmall else qLarge
def dBox (n : ℕ) : RBox := match n%12 with
  | 0 => dBase.neg
  | 1 => dSmall
  | 3 => dSmall.neg
  | 4 => dBase
  | 7 => dOther.neg
  | _ => dOther

lemma qBox_contains (n : ℕ) (hn : n%12 ∈ residues) : (qBox n).Contains (Q n) := by
  have hh : Q n = Q (n%12) := by simp [Q]
  rw [hh]
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with hn|hn|hn|hn|hn|hn <;> simp only [hn, qBox] <;>
    norm_num only at *
  · simpa [Q_0,hn,qBox] using qBase_contains
  · simpa [Q_1,hn,qBox] using qSmall_contains
  · simpa [Q_3,hn,qBox] using qSmall_contains
  · simpa [Q_4,hn,qBox] using qBase_contains
  · simpa [Q_7,hn,qBox] using qLarge_contains
  · simpa [Q_9,hn,qBox] using qLarge_contains
lemma dBox_contains (n : ℕ) (hn : n%12 ∈ residues) : (dBox n).Contains (D n) := by
  have hh : D n = D (n%12) := by simp [D]
  rw [hh]
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with hn|hn|hn|hn|hn|hn
  · simpa [D_0,hn,dBox,neg_mul,neg_div] using RBox.neg_contains dBase_contains
  · simpa [D_1,hn,dBox] using dSmall_contains
  · simpa [D_3,hn,dBox,neg_mul,neg_div] using RBox.neg_contains dSmall_contains
  · simpa [D_4,hn,dBox] using dBase_contains
  · simpa [D_7,hn,dBox,neg_mul,neg_div] using RBox.neg_contains dOther_contains
  · simpa [D_9,hn,dBox] using dOther_contains

def invBox (a : RBox) : RBox := ⟨precision^2/a.hi,-((-precision^2)/a.lo)⟩
def qiBox (n : ℕ) : RBox := invBox (qBox n)
lemma qiBox_contains (n : ℕ) (hn : n%12 ∈ residues) : (qiBox n).Contains (Q n)⁻¹ := by
  apply RBox.inv_contains (qBox_contains n hn)
  unfold qiBox qBox
  split <;> (try split) <;> decide +kernel

def inflate (a : RBox) : RBox := ⟨a.lo-10^8,a.hi+10^8⟩
lemma inflate_contains {a : RBox} {x y : ℝ} (hx : a.Contains x) (he : |y-x| < 1/10^22) :
    (inflate a).Contains y := by
  have he' := abs_lt.mp he
  have hp := precision_pos
  have hL := mul_lt_mul_of_pos_left he'.1 hp
  have hU := mul_lt_mul_of_pos_left he'.2 hp
  constructor <;> dsimp [inflate] <;> push_cast <;>
    norm_num [RBox.Contains,precision] at hL hU hx ⊢ <;> linarith only [hx.1,hx.2,hL,hU]

lemma K_column_contains {n : Node} {m : ℕ} (hn : n.val ≤ 100) (hm : m ≤ 100)
    (d e : Bool) {a : CBox}
    (ha : a.Contains (momentRuleValue quadraturePoint fejerWeight n.val m d e)) :
    (inflate a.re).Contains (K (positiveData (columnVector n d)) (if e then 1 else 0) m) :=
  inflate_contains ha.1 (K_column_rule_error hn hm d e)

lemma S_column_value_contains {n m : Node} {d : Bool} {a : RBox}
    (ha : a.Contains (K (positiveData (columnVector n d)) 0 m.val)) :
    (a.neg.mul (qiBox m.val)).Contains (S (columnVector n d) (m,false)) := by
  rw [S_column_value,div_eq_mul_inv]
  exact RBox.contains_mul (RBox.neg_contains ha) (qiBox_contains m.val m.property.2)
lemma S_column_derivative_contains {n m : Node} {d : Bool} {a c : RBox}
    (ha : a.Contains (K (positiveData (columnVector n d)) 0 m.val))
    (hc : c.Contains (K (positiveData (columnVector n d)) 1 m.val)) :
    (((dBox m.val).mul a).add c.neg |>.mul (qiBox m.val)).Contains (S (columnVector n d) (m,true)) := by
  rw [S_column_derivative,div_eq_mul_inv,sub_eq_add_neg]
  exact RBox.contains_mul
    (RBox.contains_add (RBox.contains_mul (dBox_contains m.val m.property.2) ha) (RBox.neg_contains hc))
    (qiBox_contains m.val m.property.2)
end Numerical
end SharpPlanar

end OAI
