import Mathlib
import OAI.Probability.SKGap.Matrix.MatrixWordRegularity

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X]

omit [PseudoMetricSpace X] in
lemma word_opNorm_add (M N : Matrix ι ι ℝ) : opNorm (M+N) ≤ opNorm M+opNorm N := by
  unfold opNorm
  rw [map_add,map_add]
  exact norm_add_le _ _

omit [PseudoMetricSpace X] in
lemma real_product_four_point (a b c d e f g h : Matrix ι ι ℝ) :
    ‖(a*e-b*f)-(c*g-d*h)‖ ≤
      ‖(a-b)-(c-d)‖*opNorm e+‖c-d‖*opNorm (e-g)+
      opNorm (b-d)*‖e-f‖+opNorm d*‖(e-f)-(g-h)‖ := by
  have he : (a*e-b*f)-(c*g-d*h)=
      ((a-b)-(c-d))*e+(c-d)*(e-g)+(b-d)*(e-f)+d*((e-f)-(g-h)) := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖((a-b)-(c-d))*e+(c-d)*(e-g)+(b-d)*(e-f)‖+‖d*((e-f)-(g-h))‖ := norm_add_le _ _
    _ ≤ (‖((a-b)-(c-d))*e+(c-d)*(e-g)‖+‖(b-d)*(e-f)‖)+‖d*((e-f)-(g-h))‖ := by gcongr;exact norm_add_le _ _
    _ ≤ ((‖((a-b)-(c-d))*e‖+‖(c-d)*(e-g)‖)+‖(b-d)*(e-f)‖)+‖d*((e-f)-(g-h))‖ := by gcongr;exact norm_add_le _ _
    _ ≤ _ := by
      gcongr
      · exact frobenius_mul_le_opNorm_right _ _
      · exact frobenius_mul_le_opNorm_right _ _
      · exact frobenius_mul_le_opNorm _ _
      · exact frobenius_mul_le_opNorm _ _

structure MatrixFactorPairBounds (B Δ : NNReal) (f g : X→Matrix ι ι ℝ) : Prop where
  leftBound : ∀ x,opNorm (f x)≤B
  rightBound : ∀ x,opNorm (g x)≤B
  leftLip : LipschitzWith B f
  rightLip : LipschitzWith B g
  parameter : ∀ x,opNorm (f x-g x)≤Δ
  increment : LipschitzWith Δ (fun x=>f x-g x)

def wordParameterCoeff (B : NNReal) : ℕ→NNReal
  | 0 => 0
  | r+1 => B^r+B*wordParameterCoeff B r

def wordMixedCoeff (B : NNReal) : ℕ→NNReal
  | 0 => 0
  | r+1 => B^r+B*wordParameterCoeff B r+(r:NNReal)*B^r+B*wordMixedCoeff B r

theorem matrixWord_pair_increments (F : List ((X→Matrix ι ι ℝ)×(X→Matrix ι ι ℝ)))
    {B Δ : NNReal} (hF : ∀ p∈F,MatrixFactorPairBounds B Δ p.1 p.2) :
    (∀ x,opNorm (matrixFactorProduct (F.map Prod.fst) x-matrixFactorProduct (F.map Prod.snd) x)≤
      (wordParameterCoeff B F.length:ℝ)*Δ) ∧
    LipschitzWith (wordMixedCoeff B F.length*Δ)
      (fun x=>matrixFactorProduct (F.map Prod.fst) x-matrixFactorProduct (F.map Prod.snd) x) := by
  induction F with
  | nil =>
    constructor
    · intro x;simp [matrixFactorProduct,wordParameterCoeff,opNorm]
    · simp [matrixFactorProduct,wordMixedCoeff]
  | cons p F ih =>
    have hp := hF p List.mem_cons_self
    have hFt : ∀ q∈F,MatrixFactorPairBounds B Δ q.1 q.2 := fun q hq=>hF q (List.mem_cons_of_mem p hq)
    have ht := ih hFt
    have hbL : ∀ f∈F.map Prod.fst,∀ x,opNorm (f x)≤B := by
      intro f hf;obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hf;exact (hFt q hq).leftBound
    have hlL : ∀ f∈F.map Prod.fst,LipschitzWith B f := by
      intro f hf;obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hf;exact (hFt q hq).leftLip
    have htl := matrixFactorProduct_lipschitz (F.map Prod.fst) hbL hlL
    constructor
    · intro x
      simp only [List.map_cons,matrixFactorProduct_cons,List.length_cons,wordParameterCoeff,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_pow]
      have he : p.1 x*matrixFactorProduct (F.map Prod.fst) x-p.2 x*matrixFactorProduct (F.map Prod.snd) x=
        (p.1 x-p.2 x)*matrixFactorProduct (F.map Prod.fst) x+
        p.2 x*(matrixFactorProduct (F.map Prod.fst) x-matrixFactorProduct (F.map Prod.snd) x) := by noncomm_ring
      rw [he]
      apply (word_opNorm_add _ _).trans
      apply (add_le_add (opNorm_mul _ _) (opNorm_mul _ _)).trans
      have h1 := mul_le_mul (hp.parameter x) (matrixFactorProduct_opNorm (F.map Prod.fst) hbL x)
        (show 0≤opNorm (matrixFactorProduct (F.map Prod.fst) x) from norm_nonneg _) Δ.coe_nonneg
      have h2 := mul_le_mul (hp.rightBound x) (ht.1 x) (show 0≤opNorm
        (matrixFactorProduct (F.map Prod.fst) x-matrixFactorProduct (F.map Prod.snd) x) from norm_nonneg _) B.coe_nonneg
      apply (add_le_add h1 h2).trans_eq
      simp only [List.length_map]
      ring
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [dist_eq_norm,List.map_cons,matrixFactorProduct_cons]
      have he : (p.1 x*matrixFactorProduct (F.map Prod.fst) x-p.2 x*matrixFactorProduct (F.map Prod.snd) x)-
          (p.1 y*matrixFactorProduct (F.map Prod.fst) y-p.2 y*matrixFactorProduct (F.map Prod.snd) y)=
        (p.1 x*matrixFactorProduct (F.map Prod.fst) x-p.1 y*matrixFactorProduct (F.map Prod.fst) y)-
          (p.2 x*matrixFactorProduct (F.map Prod.snd) x-p.2 y*matrixFactorProduct (F.map Prod.snd) y) := by abel
      rw [he]
      apply (real_product_four_point _ _ _ _ _ _ _ _).trans
      have hi : ‖(p.1 x-p.1 y)-(p.2 x-p.2 y)‖≤(Δ:ℝ)*dist x y := by
        have hh := hp.increment.dist_le_mul x y
        rw [dist_eq_norm] at hh
        convert! hh using 1
        congr 1;abel
      have hr : ‖p.2 x-p.2 y‖≤(B:ℝ)*dist x y := by simpa only [dist_eq_norm] using hp.rightLip.dist_le_mul x y
      have hli : ‖matrixFactorProduct (F.map Prod.fst) x-matrixFactorProduct (F.map Prod.fst) y‖≤
          ((F.length:ℝ)*(B:ℝ)^F.length)*dist x y := by
        simpa only [dist_eq_norm,List.length_map,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_pow] using htl.dist_le_mul x y
      have hm : ‖(matrixFactorProduct (F.map Prod.fst) x-matrixFactorProduct (F.map Prod.fst) y)-
          (matrixFactorProduct (F.map Prod.snd) x-matrixFactorProduct (F.map Prod.snd) y)‖≤
          ((wordMixedCoeff B F.length:ℝ)*Δ)*dist x y := by
        have hh := ht.2.dist_le_mul x y
        rw [dist_eq_norm] at hh
        convert! hh using 1
        congr 1;abel
      have h1 := mul_le_mul hi (matrixFactorProduct_opNorm (F.map Prod.fst) hbL x)
        (show 0≤opNorm (matrixFactorProduct (F.map Prod.fst) x) from norm_nonneg _) (mul_nonneg Δ.coe_nonneg dist_nonneg)
      have h2 := mul_le_mul hr (ht.1 x) (show 0≤opNorm
        (matrixFactorProduct (F.map Prod.fst) x-matrixFactorProduct (F.map Prod.snd) x) from norm_nonneg _)
        (mul_nonneg B.coe_nonneg dist_nonneg)
      have h3 := mul_le_mul (hp.parameter y) hli (norm_nonneg _) Δ.coe_nonneg
      have h4 := mul_le_mul (hp.rightBound y) hm (norm_nonneg _) B.coe_nonneg
      apply (add_le_add (add_le_add (add_le_add h1 h2) h3) h4).trans_eq
      simp only [List.length_map,List.length_cons,wordMixedCoeff,NNReal.coe_add,NNReal.coe_mul,
        NNReal.coe_natCast,NNReal.coe_pow]
      ring
end SKGap
end
end

end OAI
