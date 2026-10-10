import OAI.Combinatorics.PolynomialVacuum.Algebra.PolynomialScaling

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem exchangeNumerator_scale (c x y : ℂ) (a b : Pair) :
    exchangeNumerator (c*x) (c*y) a b=c^2*exchangeNumerator x y a b := by
  simp only [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

theorem exchangeDenominator_scale (c x y : ℂ) :
    exchangeDenominator (c*x) (c*y)=c^2*exchangeDenominator x y := by
  unfold exchangeDenominator; ring

theorem siteR_scale (j : ℕ) (c x y : ℂ) (W : SpinTensor ℕ ℂ) :
    siteR j (c*x) (c*y) W=c^2 • siteR j x y W := by
  funext s
  change pairAction j (j+1) (exchangeNumerator (c*x) (c*y)) W s=c^2*pairAction j (j+1) (exchangeNumerator x y) W s
  simp only [pairAction,exchangeNumerator_scale,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab hab; ring

theorem LowerExchange.scale {Ψ : NatSpectralTensor} {n : ℕ}
    (h : LowerExchange Ψ n) {c : ℂ} (hc : c≠0) :
    LowerExchange (fun X => Ψ (fun j => c*X j)) n := by
  intro j hj X
  have he := h j hj (fun k => c*X k)
  rw [siteR_scale,exchangeDenominator_scale,← smul_smul] at he
  have hsw : swapSite j (fun k => c*X k)=fun k => c*swapSite j X k := by rfl
  rw [hsw] at he
  funext s
  exact mul_left_cancel₀ (pow_ne_zero 2 hc) (congrFun he s)

theorem liftState_homogeneous_scale {n d : ℕ} (ψ : State n)
    (h : ∀ s, (ψ s).IsHomogeneous d) (c : ℂ) (X : ℕ → ℂ) (s : ℕ → Spin) :
    liftState ψ (fun j => c*X j) s=c^d*liftState ψ X s := by
  have he := congrArg (eval (fun j : Fin n => X j.val)) (homogeneous_scale (h (fun j : Fin n => s j.val)) c)
  simpa only [eval_scalePolynomial,map_mul,eval_C,liftState,liftPolyTensor] using he

theorem fusionPair_scale (c a x : ℂ) : fusionPair (c*a) (c*x)=c^2*fusionPair a x := by
  unfold fusionPair; ring

theorem naturalFusion_scale (n i : ℕ) (c : ℂ) (X : ℕ → ℂ) :
    naturalFusion n i (fun j => c*X j)=c^(2*n+1)*naturalFusion n i X := by
  simp only [naturalFusion,fusionProduct,skipTwo,fusionPair_scale,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_range]
  rw [← pow_mul,pow_succ]
  ring

noncomputable def scalingDiscrepancy {N : ℕ} (ψ : State N) (d : ℕ) : NatPolyTensor :=
  fun s => scalePolynomial 2 (coordinatePolynomial ψ s)-C ((2:ℂ)^d)*coordinatePolynomial ψ s

theorem eval_scalingDiscrepancy {N : ℕ} (ψ : State N) (d : ℕ) (X : ℕ → ℂ) :
    evalNatPolyTensor (scalingDiscrepancy ψ d) X=
      liftState ψ (fun j => 2*X j)-(2:ℂ)^d • liftState ψ X := by
  funext s
  simp only [evalNatPolyTensor,scalingDiscrepancy,map_sub,eval_scalePolynomial,map_mul,eval_C,
    eval_coordinatePolynomial,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]

theorem scalingDiscrepancy_exchange {N m d : ℕ} (ψ : State N)
    (hex : LowerExchange (liftState ψ) m) :
    LowerExchange (evalNatPolyTensor (scalingDiscrepancy ψ d)) m := by
  intro j hj X
  simp only [eval_scalingDiscrepancy,map_sub,map_smul,hex.scale (by norm_num : (2:ℂ)≠0) j hj,
    hex j hj,smul_sub]
  rw [smul_comm ((2:ℂ)^d)]

end PolynomialVacuumAlgebra

end OAI
