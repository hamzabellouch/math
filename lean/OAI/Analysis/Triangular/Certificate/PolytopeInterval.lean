import OAI.Analysis.Triangular.Certificate.Polytope
import OAI.Analysis.Triangular.Auxiliary.Bernstein

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def ZBox : RI := (RI.point 391).divNat 1000
def WstarBox : RI := (RI.point 61).divNat 10000
def DeltaStarBox : RI := (RI.point 18).divNat 100000
def UstarBox : RI := (RI.point 48).divNat 100000
def PstarBox : RI := (RI.point 3).divNat 10000000
lemma ZBox_mem : ZBox.Mem Z := RI.mem_divNat (RI.mem_point 391) (by norm_num)
lemma WstarBox_mem : WstarBox.Mem Wstar := RI.mem_divNat (RI.mem_point 61) (by norm_num)
lemma DeltaStarBox_mem : DeltaStarBox.Mem DeltaStar := RI.mem_divNat (RI.mem_point 18) (by norm_num)
lemma UstarBox_mem : UstarBox.Mem Ustar := RI.mem_divNat (RI.mem_point 48) (by norm_num)
lemma PstarBox_mem : PstarBox.Mem Pstar := RI.mem_divNat (RI.mem_point 3) (by norm_num)
def rowLowerBox (a : Fin 8 → RI) : RI :=
  (((((a 1).add (ZBox.mul ((RI.point 0).imin (a 0)))).add
  (DeltaStarBox.mul ((RI.point 0).imin (a 2).neg))).add
  (WstarBox.mul ((RI.point 0).imin ((a 3).add (ZBox.mul (a 2)))))).add
  (UstarBox.mul ((RI.point 0).imin ((a 5).imin ((a 5).add (ZBox.mul (a 4))))))).add
  (PstarBox.mul (((RI.point 0).imin (a 6)).add ((RI.point 0).imin (a 7))))
lemma rowLowerBox_mem {a : Fin 8 → RI} {v : Fin 8 → ℝ}
    (hv : ∀ i, (a i).Mem (v i)) : (rowLowerBox a).Mem (rowLower v) := by
  have hz : (RI.point 0).Mem (0:ℝ) := by simpa using RI.mem_point 0
  unfold rowLowerBox rowLower
  apply RI.mem_add
  · apply RI.mem_add
    · apply RI.mem_add
      · apply RI.mem_add
        · exact RI.mem_add (hv 1) (RI.mem_mul ZBox_mem (RI.mem_min hz (hv 0)))
        · exact RI.mem_mul DeltaStarBox_mem (RI.mem_min hz (RI.mem_neg (hv 2)))
      · exact RI.mem_mul WstarBox_mem (RI.mem_min hz (RI.mem_add (hv 3) (RI.mem_mul ZBox_mem (hv 2))))
    · exact RI.mem_mul UstarBox_mem (RI.mem_min hz (RI.mem_min (hv 5) (RI.mem_add (hv 5) (RI.mem_mul ZBox_mem (hv 4)))))
  · exact RI.mem_mul PstarBox_mem (RI.mem_add (RI.mem_min hz (hv 6)) (RI.mem_min hz (hv 7)))
end AtomicTriangular.FiniteCertificate
namespace AtomicTriangular.Construction
open Bernstein

def bernsteinRows (n : ℕ) (a : Fin (n+1) → Fin 8 → ℝ)
    (d : Fin (n+1)) (r : Fin 8) : ℝ :=
  ∑ l : Fin (n+1), ((d.val.choose l.val:ℝ)/(n.choose l.val:ℝ))*a l r
lemma bernsteinRows_dot (n : ℕ) (a : Fin (n+1) → Fin 8 → ℝ)
    (d : Fin (n+1)) (e : Fin 8 → ℝ) :
    (∑ r : Fin 8, bernsteinRows n a d r*e r) =
      ∑ l : Fin (n+1), ((d.val.choose l.val:ℝ)/(n.choose l.val:ℝ))*(∑ r : Fin 8, a l r*e r) := by
  simp only [bernsteinRows,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]
lemma polytope_polynomial_lower (n : ℕ) (a : Fin (n+1) → Fin 8 → ℝ) (m : ℝ)
    (hm : ∀ d, m < rowLower (bernsteinRows n a d))
    (e : Fin 8 → ℝ) (he : ParameterPolytope e) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 1) :
    m < ∑ l : Fin (n+1), (∑ r : Fin 8, a l r*e r)*τ^l.val := by
  let c : ℕ → ℝ := fun l => if hl : l<n+1 then ∑ r : Fin 8, a ⟨l,hl⟩ r*e r else 0
  have hb : ∀ d < n+1, m < bernsteinCoefficient n c d := by
    intro d hd
    have hh := (hm ⟨d,hd⟩).trans_le (rowLower_le (bernsteinRows n a ⟨d,hd⟩) e he)
    rw [bernsteinRows_dot] at hh
    have heq : bernsteinCoefficient n c d =
        ∑ l : Fin (n+1), ((d.choose l.val:ℝ)/(n.choose l.val:ℝ))*(∑ r : Fin 8, a l r*e r) := by
      unfold bernsteinCoefficient
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro l hl
      simp only [c,dite_eq_left l.isLt]
    rwa [heq]
  have hh := strict_bernstein_bound n c m hb hτ
  rw [← Fin.sum_univ_eq_sum_range] at hh
  simpa only [c,Fin.is_lt,dite_eq_left] using hh
end AtomicTriangular.Construction
end

end OAI
