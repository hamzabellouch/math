import OAI.Analysis.Triangular.Signs.OrdinaryComparison
import OAI.Analysis.Triangular.Signs.ExceptionalComparison

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma real_function_le_of_deleted {f g : ℝ → ℝ} {m s : ℝ}
    (hv : f m=g m) (hd : deriv f m=deriv g m)
    (hb : deletedSecond f m s ≤ deletedSecond g m s) : f s ≤ g s := by
  by_cases hsm : s=m
  · simpa [hsm] using hv.le
  · simp only [deletedSecond,hsm,ite_false] at hb
    have hh := (div_le_div_iff_of_pos_right (sq_pos_of_ne_zero (sub_ne_zero.mpr hsm))).mp hb
    rw [hv,hd] at hh
    linarith
lemma near_exceptional_deleted {z : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    {τ : ℝ} (hτ : τ∈Icc 0 1) :
    deletedSecond (actualJ 0 z hz hzB) 1 (1+τ) ≤ deletedSecond (gaussianG z) 1 (1+τ) := by
  have he := (abs_lt.mp (deleted_accuracy 0 hz hzB 0 1 hτ)).2
  have hg := gaussian_deleted_right (m:=1) hz hτ.1
  have ht := exceptional_rational_comparison (actualParameter z) (actualParameter_mem hz hzB) hτ hz hzB
  change finiteTaylor 0 1 1 (actualParameter z) τ+3/1000 ≤ _ at ht
  norm_num [nearNode,finiteNode,residue,nearDisplacement,nearDisplacementNum,nearError] at he
  norm_num at hg
  change _ ≤ Q 1*((3*z+τ)/(6*z^2+4*z*τ+τ^2)) at ht
  linarith
lemma near_deleted {z : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Fin 7) (y : Fin 2) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    deletedSecond (actualJ 0 z hz hzB) (nearNode n) (nearNode n+nearDisplacement n y*τ) ≤
      deletedSecond (gaussianG z) (nearNode n) (nearNode n+nearDisplacement n y*τ) := by
  by_cases he : n=0 ∧ y=1
  · rcases he with ⟨rfl,rfl⟩
    simpa [nearNode,finiteNode,residue,nearDisplacement,nearDisplacementNum] using near_exceptional_deleted hz hzB hτ
  · exact near_ordinary_deleted hz hzB n y he hτ
lemma nearCell_signs {z : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Fin 7) (y : Fin 2) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    actualJ 0 z hz hzB (nearNode n+nearDisplacement n y*τ) ≤ gaussianG z (nearNode n+nearDisplacement n y*τ) ∧
      0 ≤ actualJ 1 z hz hzB (nearNode n+nearDisplacement n y*τ) := by
  have hn : 0<nearNode n ∧ nearNode n%36∈residues := finiteNode_node ⟨n.val,by omega⟩
  have hj := actual_interpolation hz hzB ⟨nearNode n,hn⟩
  exact ⟨real_function_le_of_deleted hj.1 hj.2.1 (near_deleted hz hzB n y hτ),
    real_function_nonneg_of_deleted hj.2.2.1 hj.2.2.2 (near_positive_deleted hz hzB n y hτ)⟩
lemma near_cell_cover {s : ℝ} (hs : s∈Icc 0 (29/2)) :
    ∃ (n : Fin 7) (y : Fin 2) (τ : ℝ),τ∈Icc 0 1 ∧ s=nearNode n+nearDisplacement n y*τ := by
  by_cases h0 : s ≤ 1
  · refine ⟨0,0,(s-1)/(-1),?_,?_⟩
    · constructor <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (0:Fin 7)=(1:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (0:Fin 7) (0:Fin 2)=(-2:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h1 : s ≤ 2
  · refine ⟨0,1,(s-1)/1,?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (0:Fin 7)=(1:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (0:Fin 7) (1:Fin 2)=(2:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h2 : s ≤ 3
  · refine ⟨1,0,(s-3)/(-1),?_,?_⟩
    · constructor <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (1:Fin 7)=(3:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (1:Fin 7) (0:Fin 2)=(-2:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h3 : s ≤ (7/2)
  · refine ⟨1,1,(s-3)/(1/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (1:Fin 7)=(3:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (1:Fin 7) (1:Fin 2)=(1:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h4 : s ≤ 4
  · refine ⟨2,0,(s-4)/(-1/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (2:Fin 7)=(4:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (2:Fin 7) (0:Fin 2)=(-1:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h5 : s ≤ (11/2)
  · refine ⟨2,1,(s-4)/(3/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (2:Fin 7)=(4:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (2:Fin 7) (1:Fin 2)=(3:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h6 : s ≤ 7
  · refine ⟨3,0,(s-7)/(-3/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (3:Fin 7)=(7:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (3:Fin 7) (0:Fin 2)=(-3:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h7 : s ≤ 8
  · refine ⟨3,1,(s-7)/1,?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (3:Fin 7)=(7:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (3:Fin 7) (1:Fin 2)=(2:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h8 : s ≤ 9
  · refine ⟨4,0,(s-9)/(-1),?_,?_⟩
    · constructor <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (4:Fin 7)=(9:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (4:Fin 7) (0:Fin 2)=(-2:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h9 : s ≤ (21/2)
  · refine ⟨4,1,(s-9)/(3/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (4:Fin 7)=(9:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (4:Fin 7) (1:Fin 2)=(3:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h10 : s ≤ 12
  · refine ⟨5,0,(s-12)/(-3/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (5:Fin 7)=(12:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (5:Fin 7) (0:Fin 2)=(-3:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h11 : s ≤ (25/2)
  · refine ⟨5,1,(s-12)/(1/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (5:Fin 7)=(12:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (5:Fin 7) (1:Fin 2)=(1:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h12 : s ≤ 13
  · refine ⟨6,0,(s-13)/(-1/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (6:Fin 7)=(13:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (6:Fin 7) (0:Fin 2)=(-1:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  refine ⟨6,1,(s-13)/(3/2),?_,?_⟩
  · constructor <;> norm_num <;> linarith [hs.1,hs.2]
  · norm_num only [show nearNode (6:Fin 7)=(13:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (6:Fin 7) (1:Fin 2)=(3:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
    ring
lemma near_signs {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z) (hs : s∈Icc 0 (29/2)) :
    actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s := by
  obtain ⟨n,y,τ,hτ,rfl⟩ := near_cell_cover hs
  exact nearCell_signs hz hzB n y hτ
end AtomicTriangular.Construction
end

end OAI
