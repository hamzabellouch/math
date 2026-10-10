import OAI.Analysis.Triangular.Construction.CurvatureEnvelope
import OAI.Analysis.Triangular.Construction.CoefficientAddition
import OAI.Analysis.Triangular.Taylor.FiniteTaylorError

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma deletedSecond_add {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (m s : ℝ) :
    deletedSecond (f+g) m s=deletedSecond f m s+deletedSecond g m s := by
  unfold deletedSecond
  split_ifs with hs
  · rw [iteratedDeriv_add hf.contDiffAt hg.contDiffAt]
    ring
  · rw [deriv_add (hf.differentiable (by norm_num) m) (hg.differentiable (by norm_num) m)]
    simp only [Pi.add_apply]
    ring
lemma finiteJ_contDiff (side : Fin 2) (e : Fin 8 → ℝ) : ContDiff ℝ ⊤ (finiteJ side e) := by
  have he : finiteJ side e=pairJ (coefficientInput ((gamma side *ᵥ e) 2) (finiteApprox side e) 0)
      (coefficientInput ((gamma (otherSide side) *ᵥ e) 2) (finiteApprox (otherSide side) e) 0) := by
    funext s; exact congrArg Complex.re (finiteJJet_pair side e 0 s)
  rw [he]
  exact pairJ_contDiff _ _
def nearBase (n : Fin 7) (y : Fin 2) : Fin 5 := if n.val=0 then (if y.val=0 then 0 else 1) else 2
def nearError (n : Fin 7) (y : Fin 2) : ℝ := if n.val=0 then (if y.val=0 then 18/1000 else 3/1000) else 16/100000
lemma nearDisplacement_radius (n : Fin 7) (y : Fin 2) : |nearDisplacement n y| ≤ nearRadius n := by
  fin_cases n <;> fin_cases y <;> norm_num [nearDisplacement,nearDisplacementNum,nearRadius,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
lemma nearDisplacement_mul_radius (n : Fin 7) (y : Fin 2) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    |nearDisplacement n y*τ| ≤ nearRadius n := by
  rw [abs_mul,abs_of_nonneg hτ.1]
  exact (mul_le_of_le_one_right (abs_nonneg _) hτ.2).trans (nearDisplacement_radius n y)
lemma nearBase_le_node (n : Fin 7) (y : Fin 2) : curvaturePoint (nearBase n y) ≤ (nearNode n:ℝ) := by
  fin_cases n <;> fin_cases y <;> norm_num [nearBase,curvaturePoint,nearNode,finiteNode,residue,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
lemma nearBase_le_cell (n : Fin 7) (y : Fin 2) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    curvaturePoint (nearBase n y) ≤ (nearNode n:ℝ)+nearDisplacement n y*τ := by
  obtain ⟨ht0,ht1⟩ := hτ
  fin_cases n <;> fin_cases y <;> norm_num [nearBase,curvaturePoint,nearNode,finiteNode,residue,nearDisplacement,nearDisplacementNum,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail] <;> linarith
lemma near_error_arithmetic (n : Fin 7) (y : Fin 2) :
    (1/100000:ℝ)*finiteCurvatureEnvelope (nearBase n y)+(3/1000000000)*tailCurvatureEnvelope (nearBase n y)+
      (if n.val=0 then (161/100000:ℝ) else 75/10000000)<nearError n y := by
  fin_cases n <;> fin_cases y <;> norm_num [nearBase,nearError,finiteCurvatureEnvelope,tailCurvatureEnvelope,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
lemma deleted_accuracy (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) (n : Fin 7) (y : Fin 2) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    |deletedSecond (actualJ side z hz hzB) (nearNode n) (nearNode n+nearDisplacement n y*τ)-
      finiteTaylor side (nearNode n) (nearDisplacement n y) (actualParameter z) τ|<nearError n y := by
  let corr := pairJ (coefficientInput 0 (extendFiniteError (actualFiniteError side z hz hzB)) (actualTail side z hz hzB))
      (coefficientInput 0 (extendFiniteError (actualFiniteError (otherSide side) z hz hzB)) (actualTail (otherSide side) z hz hzB))
  let K : ℝ := (1/100000)*finiteCurvatureEnvelope (nearBase n y)+(3/1000000000)*tailCurvatureEnvelope (nearBase n y)
  have hb : |deletedSecond corr (nearNode n) (nearNode n+nearDisplacement n y*τ)| ≤ K := by
    have hh := deletedSecond_bound (f:=corr) ((pairJ_contDiff _ _).of_le (by norm_num))
      (m:=(nearNode n:ℝ)) (s:=(nearNode n:ℝ)+nearDisplacement n y*τ) (C:=2*K) ?_
    · linarith
    · intro t ht
      have htB : curvaturePoint (nearBase n y) ≤ t := (le_min (nearBase_le_node n y) (nearBase_le_cell n y hτ)).trans ht.1
      have ha (side : Fin 2) : ‖extendFiniteError (actualFiniteError side z hz hzB)‖ ≤ (1/100000:ℝ) := by
        rw [extendFiniteError_norm]
        simpa only [show (10:ℝ)^5=100000 by norm_num] using (actualFiniteError_norm side hz hzB).le
      have hh := pairJ_curvature _ _ _ _ (nearBase n y) htB (ha side) (ha (otherSide side))
        (actualTail_norm side hz hzB).le (actualTail_norm (otherSide side) hz hzB).le
      norm_num at hh
      change |iteratedDeriv 2 corr t|/2 ≤ K at hh
      linarith
  rw [actualJ_split,deletedSecond_add ((finiteJ_contDiff _ _).of_le (by norm_num)) ((pairJ_contDiff _ _).of_le (by norm_num))]
  have he := finiteTaylor_error side hz hzB n (nearDisplacement_mul_radius n y hτ)
  have hh := abs_add_le (deletedSecond (finiteJ side (actualParameter z)) (nearNode n) (nearNode n+nearDisplacement n y*τ)-finiteTaylor side (nearNode n) (nearDisplacement n y) (actualParameter z) τ)
    (deletedSecond corr (nearNode n) (nearNode n+nearDisplacement n y*τ))
  have htab := near_error_arithmetic n y
  dsimp only [K] at hb
  convert lt_of_le_of_lt hh (by linarith) using 1
  congr 1
  ring
end AtomicTriangular.Construction
end

end OAI
