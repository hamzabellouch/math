import Mathlib
import OAI.Probability.SKGap.Terminal.PairGibbsBound
import OAI.Probability.SKGap.Entropy.SparseWeightedForm
import OAI.Probability.SKGap.Terminal.SmallFieldCount

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

lemma one_sub_tanh_sq (x : ℝ) : 1-tanh x^2=1/cosh x^2 := by
  rw [tanh_eq_sinh_div_cosh]
  have hc := (cosh_pos x).ne'
  have he := cosh_sq_sub_sinh_sq x
  field_simp
  nlinarith only [he]

lemma variance_tanh_le_cosh {t x : ℝ} (ht : 0 ≤ t) (hx : t ≤ |x|) :
    1-tanh x^2 ≤ 1/cosh t^2 := by
  rw [one_sub_tanh_sq]
  have hcosh : cosh t ≤ cosh x := cosh_le_cosh.mpr (by simpa only [abs_of_nonneg ht] using hx)
  have hs := (sq_le_sq₀ (cosh_pos t).le (cosh_pos x).le).mpr hcosh
  exact one_div_le_one_div_of_le (sq_pos_of_pos (cosh_pos t)) hs

def terminalU (g : Disorder n) : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j=>tanh (coupling g i j))
def terminalQ (g : Disorder n) : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j=>tanh (coupling g i j)^2)

theorem terminal_deterministic (g : Disorder n) (h : Fin n→ℝ) {M t α ε R : ℝ}
    (hM : 0 ≤ M) (ht : 0 < t) (hε : 0 ≤ ε)
    (hJ : ‖Matrix.of (coupling g)‖ ≤ M)
    (hU : ‖terminalU g‖ ≤ M) (hQ : ‖terminalQ g‖ ≤ M)
    (hc : ∀ i j,|tanh (coupling g i j)| ≤ 1/1000)
    (hR : ∀ i,∑ j,tanh (coupling g i j)^4 ≤ R)
    (hsparse : ∀ S : Finset (Fin n),(S.card:ℝ) ≤ α*(n:ℝ) →
      ∀ w : EuclideanSpace ℝ (Fin n),(∀ i,i ∉ S → w i=0) →
      |⟪w,Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (terminalU g) w⟫| ≤ ε*‖w‖^2 ∧
      |⟪w,Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (terminalQ g) w⟫| ≤ ε*‖w‖^2)
    (hB : ((Finset.univ.filter (fun i=>|h i| < 2*t)).card:ℝ) ≤ α*(n:ℝ)/2)
    (hsmall : M^2 ≤ t^2*α/2)
    (hnum : 800000*R+400001*(ε+M*(2*sqrt (1/cosh t^2)+1/cosh t^2)) ≤ 1/2) :
    ∀ f : Spin n→ℝ,variance g h f ≤ 2*dirichlet g h f := by
  have hη : (0:ℝ) ≤ 1/cosh t^2 := by positivity
  have hS := all_configurations_small_fields g h hM ht hJ hB hsmall
  let k := ε+M*(2*sqrt (1/cosh t^2)+1/cosh t^2)
  have hcurv (f : Spin n→ℝ) : (1/2:ℝ)*dirichlet g h f ≤
      expectation g h (fun x=>heatBathGenerator g h f x^2) := by
    let q := fun x=>∑ i,siteVariance g h i x*spinGradient i f x^2
    have hq : expectation g h q=dirichlet g h f := by
      dsimp [q]
      rw [expectation_sum,dirichlet_weighted]
    have hform (x : Spin n) :
        (∑ i,∑ j,tanh (coupling g i j)*weightedGradient g h i f x*weightedGradient g h j f x) ≤ k*q x ∧
        (∑ i,∑ j,tanh (coupling g i j)^2*|weightedGradient g h i f x*weightedGradient g h j f x|) ≤ k*q x := by
      let S := Finset.univ.filter (fun i=>|localField g h i x| < t)
      have hv (i : Fin n) : 0 ≤ siteVariance g h i x := (siteVariance_pos g h i x).le
      have hvsmall (i : Fin n) (hi : i ∉ S) : siteVariance g h i x ≤ 1/cosh t^2 := by
        apply variance_tanh_le_cosh ht.le
        have hi' : ¬|localField g h i x| < t := by simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using hi
        exact le_of_not_gt hi'
      have hboundU := weighted_sparse_form (terminalU g) S (fun i=>siteVariance g h i x)
        (fun i=>spinGradient i f x) hη hε hM hv (fun i=>siteVariance_le_one g h i x) hvsmall hU
        (fun w hw=>(hsparse S (hS x) w hw).1)
      have hboundQ := weighted_sparse_form (terminalQ g) S (fun i=>siteVariance g h i x)
        (fun i=>|spinGradient i f x|) hη hε hM hv (fun i=>siteVariance_le_one g h i x) hvsmall hQ
        (fun w hw=>(hsparse S (hS x) w hw).2)
      constructor
      · exact (le_abs_self _).trans hboundU
      · simp only [sq_abs] at hboundQ
        have he : (∑ i,∑ j,tanh (coupling g i j)^2*|weightedGradient g h i f x*weightedGradient g h j f x|)=
            ∑ i,∑ j,terminalQ g i j*(siteVariance g h i x*|spinGradient i f x|)*
              (siteVariance g h j x*|spinGradient j f x|) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          simp only [terminalQ,Matrix.of_apply,weightedGradient,abs_mul,abs_of_nonneg (hv i),abs_of_nonneg (hv j)]
          ring
        rw [he]
        exact (le_abs_self _).trans hboundQ
    have hu := expectation_mono g h (fun x=>(hform x).1)
    have hq' := expectation_mono g h (fun x=>(hform x).2)
    rw [expectation_const_mul,hq] at hu hq'
    have hl := gibbs_signed_curvature g h f hc hR
    have hd := dirichlet_nonneg g h f
    have hn : 800000*R+400001*k ≤ 1/2 := hnum
    have hh := mul_le_mul_of_nonneg_right hn hd
    nlinarith only [hu,hq',hl,hh]
  intro f
  have hp := heatBath_curvature_poincare g h (by norm_num : (0:ℝ) < 1/2) hcurv f
  linarith only [hp]
end SKGap

end
end

end OAI
