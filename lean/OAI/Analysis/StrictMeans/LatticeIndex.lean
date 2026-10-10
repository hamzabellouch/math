import OAI.Analysis.StrictMeans.IndexLocality

namespace OAI

section
open Set Function
namespace StrictInverseFirstPower.Grid
noncomputable section

abbrev Lattice := Lex (ℤ × ℤ)
def ex : Lattice := toLex (1,0)
def ey : Lattice := toLex (0,1)

def latticeHeight (p q : ℤ → ℝ) (v : Lattice) : ℝ := p (ofLex v).1 + q (ofLex v).2

lemma ex_ne_zero : ex ≠ 0 := by decide
lemma ey_ne_zero : ey ≠ 0 := by decide
lemma ex_add_ey_ne_zero : ex+ey ≠ 0 := by decide

lemma bool_congr {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) : decide P = decide Q :=
  decide_eq_decide.mpr h

lemma separable_strict_bits (A B : ℝ) :
    bit (decide (A+B<0)) * (bit (decide (A<0))+bit (decide (B<0))-1) =
      bit (decide (A<0))*bit (decide (B<0)) := by
  by_cases ha : A<0 <;> by_cases hb : B<0 <;> simp [ha,hb,bit]
  · have h : A+B<0 := by linarith
    simp [h]
  · linarith

lemma separable_weak_bits (A B : ℝ) :
    bit (decide (A+B≤0)) * (bit (decide (A≤0))+bit (decide (B≤0))-1) =
      bit (decide (A≤0))*bit (decide (B≤0)) := by
  by_cases ha : A≤0 <;> by_cases hb : B≤0 <;> simp [ha,hb,bit]
  · have h : A+B≤0 := by linarith
    simp [h]
  · linarith

lemma separable_linkIndex (A B C D : ℝ) :
    linkIndex (decide (A<0)) (decide (A+B<0)) (decide (B<0))
      (decide (C≤0)) (decide (C+D≤0)) (decide (D≤0)) =
    (1-bit (decide (A<0))-bit (decide (C≤0))) *
      (1-bit (decide (B<0))-bit (decide (D≤0))) := by
  have h₁ := separable_strict_bits A B
  have h₂ := separable_weak_bits C D
  unfold linkIndex
  nlinarith only [h₁,h₂]

lemma heightRank_pos_x (u : Lattice → ℝ) (v : Lattice) :
    heightRank u (v+ex) < heightRank u v ↔ u (v+ex)<u v := by
  simp only [heightRank,Prod.Lex.toLex_lt_toLex]
  have hn : ¬ v+ex < v := not_lt.mpr (le_of_lt (lt_add_of_pos_right v (by decide : 0 < ex)))
  simp [hn]

lemma heightRank_pos_y (u : Lattice → ℝ) (v : Lattice) :
    heightRank u (v+ey) < heightRank u v ↔ u (v+ey)<u v := by
  simp only [heightRank,Prod.Lex.toLex_lt_toLex]
  have hn : ¬ v+ey < v := not_lt.mpr (le_of_lt (lt_add_of_pos_right v (by decide : 0 < ey)))
  simp [hn]

lemma heightRank_pos_xy (u : Lattice → ℝ) (v : Lattice) :
    heightRank u (v+ex+ey) < heightRank u v ↔ u (v+ex+ey)<u v := by
  simp only [heightRank,Prod.Lex.toLex_lt_toLex]
  have hn : ¬ v+ex+ey < v := by
    rw [add_assoc]
    exact not_lt.mpr (le_of_lt (lt_add_of_pos_right v (by decide : 0 < ex+ey)))
  simp [hn]

lemma heightRank_neg_step (u : Lattice → ℝ) (v s : Lattice) (hs : 0 < s) :
    heightRank u (v-s) < heightRank u v ↔ u (v-s)≤u v := by
  simp only [heightRank,Prod.Lex.toLex_lt_toLex]
  have hneg : v-s < v := sub_lt_self _ hs
  simp only [hneg,and_true]
  exact le_iff_lt_or_eq.symm

lemma latticeHeight_index (p q : ℤ → ℝ) (v : Lattice) :
    heightIndex (latticeHeight p q) ex ey v =
      (1-bit (decide (p ((ofLex v).1+1)<p (ofLex v).1))-
        bit (decide (p ((ofLex v).1-1)≤p (ofLex v).1))) *
      (1-bit (decide (q ((ofLex v).2+1)<q (ofLex v).2))-
        bit (decide (q ((ofLex v).2-1)≤q (ofLex v).2))) := by
  rw [heightIndex,meshIndex_eq_linkIndex]
  have hx := bool_congr (heightRank_pos_x (latticeHeight p q) v)
  have hy := bool_congr (heightRank_pos_y (latticeHeight p q) v)
  have hxy := bool_congr (heightRank_pos_xy (latticeHeight p q) v)
  have hmx := bool_congr (heightRank_neg_step (latticeHeight p q) v ex (by decide))
  have hmy := bool_congr (heightRank_neg_step (latticeHeight p q) v ey (by decide))
  have hmxy := bool_congr (heightRank_neg_step (latticeHeight p q) v (ex+ey) (by decide))
  rw [hx,hy,hxy,hmx,hmy,hmxy]
  simp only [latticeHeight,ofLex_add,ofLex_sub,ex,ey,ofLex_toLex,Prod.fst_add,
    Prod.snd_add,Prod.fst_sub,Prod.snd_sub,add_zero,zero_add,sub_zero]
  have h := separable_linkIndex (p ((ofLex v).1+1)-p (ofLex v).1)
    (q ((ofLex v).2+1)-q (ofLex v).2) (p ((ofLex v).1-1)-p (ofLex v).1)
    (q ((ofLex v).2-1)-q (ofLex v).2)
  simp only [sub_lt_zero,sub_nonpos] at h
  simp only [add_lt_add_iff_left,add_lt_add_iff_right,add_le_add_iff_left,add_le_add_iff_right]
  convert h using 1
  congr 1 <;> apply bool_congr <;> constructor <;> intro ht <;> linarith

end
end StrictInverseFirstPower.Grid

end

end OAI
