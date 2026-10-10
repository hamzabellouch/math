import OAI.NumberTheory.OrdinaryCorrelations.Elliott.NormThreshold

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology
open MeasureTheory intervalIntegral
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff
open Filter Finset
open scoped BigOperators Matrix.Norms.L2Operator

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem.Sliding
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open OrdinaryCorrelations.Localization
variable {S : PrimeSystem} {B τ C₀ T : ℝ} {h ℓ L D₀ : ℕ}

def dirMatrix (D : S.DivisorFamily B τ C₀) (h L : ℕ) (cut : S.Cutoffs T)
    (a : ℕ → ℂ) (D₀ : ℕ) (n : ℤ) : Matrix (Fin D₀) (Fin D₀) ℂ := fun x y =>
  if VertexAllowed D h L (n+x.val) ∧ VertexAllowed D h L (n+y.val) then
    ∑ d∈D.members, if (y.val:ℤ)=x.val+(h:ℤ)*d then
      a d * ((S.divisorEdgeWeight cut (S.integerResidues n) d x.val y.val /
        Real.sqrt (S.vertexWeight (S.integerResidues n) x.val *
          S.vertexWeight (S.integerResidues n) y.val)):ℝ) else 0
  else 0

lemma dirMatrix_polarization (D : S.DivisorFamily B τ C₀) (hh : 0<h) (L : ℕ)
    (cut : S.Cutoffs T) (a : ℕ→ℂ) (n : ℤ) :
    dirMatrix D h L cut a D₀ n = (2:ℂ)⁻¹ •
      (symMatrix D h L cut a D₀ n - Complex.I •
        symMatrix D h L cut (fun d=>Complex.I*a d) D₀ n) := by
  ext x y
  simp only [dirMatrix,symMatrix,Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul]
  by_cases hy : VertexAllowed D h L (n+x.val) ∧ VertexAllowed D h L (n+y.val)
  · simp only [ite_eq_left hy]
    rw [mul_sum,←sum_sub_distrib,mul_sum]
    apply sum_congr rfl
    intro d hd
    have hh' : (0:ℤ)<h := by exact_mod_cast hh
    have hd' : (0:ℤ)<d := by exact_mod_cast Nat.zero_lt_one.trans (D.greater_one d hd)
    have hpos := mul_pos hh' hd'
    by_cases he : (y.val:ℤ)=x.val+(h:ℤ)*d
    · have hlt : x.val<y.val := by exact_mod_cast (by omega : (x.val:ℤ)<y.val)
      simp only [he, true_or, hlt,ite_true]
      ring_nf
      rw [Complex.I_sq]
      ring
    · by_cases he' : (x.val:ℤ)=y.val+(h:ℤ)*d
      · have hlt : ¬x.val<y.val := by exact_mod_cast (by omega : ¬(x.val:ℤ)<y.val)
        simp only [ite_eq_right he, ite_eq_left (Or.inr he'),ite_eq_right hlt,
          star_mul,Complex.star_def,Complex.conj_I]
        ring_nf
        rw [Complex.I_sq]
        ring
      · simp [he,he']
  · simp only [ite_eq_right hy,mul_zero,sub_zero]

lemma dirMatrix_norm_le (D : S.DivisorFamily B τ C₀) (hh : 0<h) (L : ℕ)
    (cut : S.Cutoffs T) (a : ℕ→ℂ) (n : ℤ) :
    ‖dirMatrix D h L cut a D₀ n‖ ≤
      (‖symMatrix D h L cut a D₀ n‖ +
        ‖symMatrix D h L cut (fun d=>Complex.I*a d) D₀ n‖)/2 := by
  rw [dirMatrix_polarization D hh L cut a n,norm_smul]
  have hb := norm_sub_le (symMatrix D h L cut a D₀ n)
    (Complex.I • symMatrix D h L cut (fun d=>Complex.I*a d) D₀ n)
  simp only [norm_smul,Complex.norm_I,one_mul] at hb
  simp only [norm_inv,Complex.norm_ofNat]
  nlinarith

lemma dirMatrix_denominator_cancel (D : S.DivisorFamily B τ C₀) (h L : ℕ)
    (cut : S.Cutoffs T) (a : ℕ→ℂ) (n : ℤ) (x y : Fin D₀) :
    dirMatrix D h L cut a D₀ n x y *
      (Real.sqrt (S.vertexWeight (S.integerResidues n) x.val):ℂ) *
      (Real.sqrt (S.vertexWeight (S.integerResidues n) y.val):ℂ) =
    if VertexAllowed D h L (n+x.val) ∧ VertexAllowed D h L (n+y.val) then
      ∑ d∈D.members,if (y.val:ℤ)=x.val+(h:ℤ)*d then
        a d*(S.divisorEdgeWeight cut (S.integerResidues n) d x.val y.val:ℝ) else 0
    else 0 := by
  unfold dirMatrix
  split_ifs
  · rw [sum_mul,sum_mul]
    apply sum_congr rfl
    intro d hd
    split_ifs
    · have hx := S.vertexWeight_pos (S.integerResidues n) x.val
      have hy := S.vertexWeight_pos (S.integerResidues n) y.val
      rw [Real.sqrt_mul hx.le,Complex.ofReal_div,Complex.ofReal_mul]
      have hxs : (Real.sqrt (S.vertexWeight (S.integerResidues n) x.val):ℂ)≠0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hx))
      have hys : (Real.sqrt (S.vertexWeight (S.integerResidues n) y.val):ℂ)≠0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hy))
      field_simp
    · simp
  · simp

def retainedEdge (D : S.DivisorFamily B τ C₀) (h L : ℕ) (cut : S.Cutoffs T)
    (F G : ℤ→ℂ) (n : ℤ) (d : ℕ) : ℂ :=
  if VertexAllowed D h L n ∧ VertexAllowed D h L (n+(h:ℤ)*d) then
    F n * G (n+(h:ℤ)*d) * (S.divisorEdgeWeight cut (S.integerResidues n) d 0 ((h:ℤ)*d):ℝ)
  else 0

lemma retainedEdge_shift (D : S.DivisorFamily B τ C₀) (h L : ℕ) (cut : S.Cutoffs T)
    (F G : ℤ→ℂ) (n : ℤ) (d : ℕ) (x : ℤ) :
    retainedEdge D h L cut F G (n+x) d =
    if VertexAllowed D h L (n+x) ∧ VertexAllowed D h L (n+(x+(h:ℤ)*d)) then
      F (n+x)*G (n+(x+(h:ℤ)*d)) *
        (S.divisorEdgeWeight cut (S.integerResidues n) d x (x+(h:ℤ)*d):ℝ) else 0 := by
  rw [integer_edge_shift cut n x d x (x+(h:ℤ)*d)]
  simp only [sub_self,add_sub_cancel_left,retainedEdge,add_assoc]

lemma sum_forward_entries (D₀ k : ℕ) (r : ℕ→ℂ) :
    (∑ x : Fin D₀, ∑ y : Fin D₀,if y.val=x.val+k then r x.val else 0) =
      ∑ x∈range (D₀-k),r x := by
  have he (x : Fin D₀) : (∑ y : Fin D₀,if y.val=x.val+k then r x.val else 0) =
      if x.val+k<D₀ then r x.val else 0 := by
    by_cases hx : x.val+k<D₀
    · rw [sum_eq_single (⟨x.val+k,hx⟩:Fin D₀)]
      · simp [hx]
      · intro y hy hne
        have hn : y.val≠x.val+k := fun he => hne (Fin.ext he)
        simp [hn]
      · simp
    · rw [ite_eq_right hx]
      exact sum_eq_zero (fun y hy => ite_eq_right (by intro he; omega))
  simp_rw [he]
  rw [Fin.sum_univ_eq_sum_range (fun x=>if x+k<D₀ then r x else 0)]
  calc
    _ = ∑ x∈(range D₀).filter (fun x=>x+k<D₀),r x := (sum_filter _ _).symm
    _ = _ := by
      congr 1
      ext x
      simp only [mem_filter,Finset.mem_range]
      omega

lemma dirMatrix_bilinear_eq (D : S.DivisorFamily B τ C₀) (h L : ℕ)
    (cut : S.Cutoffs T) (a : ℕ→ℂ) (F G : ℤ→ℂ) (n : ℤ) :
    (∑ x : Fin D₀,∑ y : Fin D₀,
      F (n+x.val)*dirMatrix D h L cut a D₀ n x y*G (n+y.val)*
        (Real.sqrt (S.vertexWeight (S.integerResidues n) x.val):ℂ)*
        (Real.sqrt (S.vertexWeight (S.integerResidues n) y.val):ℂ)) =
    ∑ d∈D.members,a d*∑ x∈range (D₀-h*d),retainedEdge D h L cut F G (n+x) d := by
  have he (x y : Fin D₀) :
      F (n+x.val)*dirMatrix D h L cut a D₀ n x y*G (n+y.val)*
        (Real.sqrt (S.vertexWeight (S.integerResidues n) x.val):ℂ)*
        (Real.sqrt (S.vertexWeight (S.integerResidues n) y.val):ℂ) =
      ∑ d∈D.members, if y.val=x.val+h*d then
        a d*retainedEdge D h L cut F G (n+x.val) d else 0 := by
    calc
      _ = F (n+x.val)*G (n+y.val)*(dirMatrix D h L cut a D₀ n x y*
          (Real.sqrt (S.vertexWeight (S.integerResidues n) x.val):ℂ)*
          (Real.sqrt (S.vertexWeight (S.integerResidues n) y.val):ℂ)) := by ring
      _ = _ := by
        rw [dirMatrix_denominator_cancel]
        simp only [mul_ite,mul_sum,mul_zero]
        by_cases hy : VertexAllowed D h L (n+x.val) ∧ VertexAllowed D h L (n+y.val)
        · rw [ite_eq_left hy]
          apply sum_congr rfl
          intro d hd
          have heq : (y.val:ℤ)=x.val+(h:ℤ)*d ↔ y.val=x.val+h*d := by exact_mod_cast Iff.rfl
          simp only [heq]
          split_ifs with hxy
          · have hxy' : (y.val:ℤ)=x.val+(h:ℤ)*d := by exact_mod_cast hxy
            rw [retainedEdge_shift,←hxy',ite_eq_left hy]
            ring
          · rfl
        · rw [ite_eq_right hy]
          symm
          apply sum_eq_zero
          intro d hd
          split_ifs with hxy
          · have hxy' : (y.val:ℤ)=x.val+(h:ℤ)*d := by exact_mod_cast hxy
            rw [retainedEdge_shift,←hxy',ite_eq_right hy,mul_zero]
          · rfl
  simp_rw [he]
  simp_rw [sum_comm (s:=univ) (t:=D.members)]
  apply sum_congr rfl
  intro d hd
  rw [sum_forward_entries D₀ (h*d) (fun x=>a d*retainedEdge D h L cut F G (n+(x:ℤ)) d)]
  exact (mul_sum _ _ _).symm

lemma window_bilinear_le (D : S.DivisorFamily B τ C₀) (hh : 0<h) (L : ℕ)
    (cut : S.Cutoffs T) (a : ℕ→ℂ) (F G : ℤ→ℂ)
    (hF : ∀ n,‖F n‖≤1) (hG : ∀ n,‖G n‖≤1) (n : ℤ) :
    ‖∑ d∈D.members,a d*∑ x∈range (D₀-h*d),retainedEdge D h L cut F G (n+x) d‖ ≤
      ((‖symMatrix D h L cut a D₀ n‖+
        ‖symMatrix D h L cut (fun d=>Complex.I*a d) D₀ n‖)/2)*
          windowWeight S D₀ (S.integerResidues n) := by
  rw [←dirMatrix_bilinear_eq]
  exact (weighted_matrix_bilinear (dirMatrix D h L cut a D₀ n)
    (fun x=>S.vertexWeight (S.integerResidues n) x.val)
    (fun x=>(S.vertexWeight_pos _ _).le) (fun x=>F (n+x.val)) (fun x=>G (n+x.val))
    (fun x=>hF _) (fun x=>hG _)).trans
      (mul_le_mul_of_nonneg_right (dirMatrix_norm_le D hh L cut a n) (windowWeight_nonneg _))

end OrdinaryCorrelations.GraphKernel.PrimeSystem.Sliding

end

end OAI
