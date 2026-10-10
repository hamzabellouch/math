import OAI.Combinatorics.PolynomialVacuum.Algebra.SpectralAnalytic

namespace OAI

namespace PolynomialVacuumAlgebra
namespace AnalyticVacuum
open Classical Filter
open scoped Topology
theorem four_ne_zero {x : ℂ} (h : x^4= -1) : x-1≠0 ∧ x+1≠0 := by
  constructor
  · intro hz
    have hx : x=1 := sub_eq_zero.mp hz
    rw [hx] at h
    norm_num at h
  · intro hz
    have hx : x= -1 := eq_neg_of_add_eq_zero_left hz
    rw [hx] at h
    norm_num at h

theorem physical_auxiliary : T*(-zeta)=t := by
  dsimp [T,zeta,t]; vacuum_ring_finish

theorem physical_fusion (N : ℕ) : homogeneousFusion N (-zeta)≠0 := by
  have hT : T^4= -1 := by dsimp [T,t]; vacuum_ring_finish
  have ha : -zeta≠0 := neg_ne_zero.mpr (pow_ne_zero _ t_ne_zero)
  have h1 : (t^5*(-zeta))^4= -1 := by dsimp [zeta,t]; vacuum_ring_finish
  have h2 : (1-t^6*(-zeta))=(2 : ℂ) := by dsimp [zeta,t]; vacuum_ring_finish
  apply mul_ne_zero (mul_ne_zero (by simpa [add_comm] using (four_ne_zero hT).2) ha)
  apply pow_ne_zero
  change (1-t^5*(-zeta))*(1-t^6*(-zeta))≠0
  rw [h2]
  exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp (four_ne_zero h1).1))) (by norm_num)

theorem physical_cup_denominator : exchangeDenominator (T*(-zeta)) (-zeta)≠0 := by
  have h1 : (t^2*T)^4= -1 := by dsimp [T,t]; vacuum_ring_finish
  have h2 : (T^2)^2= -1 := by dsimp [T,t]; vacuum_ring_finish
  have hn1 : t^2*T-1≠0 := (four_ne_zero h1).1
  have hn2 : T^2-1≠0 := by
    intro hz
    rw [sub_eq_zero.mp hz] at h2
    norm_num at h2
  have ha : -zeta≠0 := neg_ne_zero.mpr (pow_ne_zero _ t_ne_zero)
  have he : exchangeDenominator (T*(-zeta)) (-zeta)=(-zeta)^2*(t^2*T-1)*(T^2-1) := by
    unfold exchangeDenominator; ring
  rw [he]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ ha) hn1) hn2

noncomputable def spectralMatrix (N : ℕ) (X : Fin N → ℂ) : Matrix (Fin N → Spin) (Fin N → Spin) ℂ :=
  transferMatrix N zeta t (extendData N X)
noncomputable def rowDenominator (N : ℕ) (X : Fin N → ℂ) : ℂ :=
  trainDenominator t (extendData N X) 0 N
noncomputable def spectralPolynomial (N : ℕ) (X : Fin N → ℂ) : (Fin N → Spin) → ℂ :=
  fun s=>MvPolynomial.eval X (polynomialVacuum N s)

@[simp] theorem rowDenominator_one (N : ℕ) : rowDenominator N (fun _=>1)=exchangeDenominator t 1^N := by
  simp [rowDenominator,trainDenominator_constant]
@[simp] theorem spectralMatrix_one (N : ℕ) : spectralMatrix N (fun _=>1)=exchangeDenominator t 1^N • physicalTransfer N zeta := by
  simp only [spectralMatrix,extendData_one,transferMatrix_physical]

theorem spectral_fusion_one (N : ℕ) : Inhomogeneous.spectralFusion N (extendData N (fun _=>1)) (-zeta)≠0 := by
  simpa [Inhomogeneous.spectralFusion,homogeneousFusion,fusionProduct] using physical_fusion N

theorem analytic_spectral_fusion (N : ℕ) (X : Fin N → ℂ) :
    AnalyticAt ℂ (fun Y=>Inhomogeneous.spectralFusion N (extendData N Y) (-zeta)) X := by
  unfold Inhomogeneous.spectralFusion fusionProduct
  apply analyticAt_const.mul
  apply analytic_finite_product
  intro j _
  unfold fusionPair
  have h:=analytic_extendData N j X
  fun_prop

theorem fusion_eventually_ne_zero (N : ℕ) :
    ∀ᶠ X in nhds (fun _ : Fin N => (1:ℂ)),Inhomogeneous.spectralFusion N (extendData N X) (-zeta)≠0 :=
  (analytic_spectral_fusion N _).continuousAt.eventually_ne (spectral_fusion_one N)

theorem spectralPolynomial_eigen (N : ℕ) (X : Fin N → ℂ)
    (hs : Inhomogeneous.spectralFusion N (extendData N X) (-zeta)≠0) :
    (spectralMatrix N X).mulVec (spectralPolynomial N X)=rowDenominator N X • spectralPolynomial N X := by
  let Y:=extendData N X
  have he:=Inhomogeneous.polynomialVacuum_tracedRow N Y (-zeta) hs physical_cup_denominator
  rw [physical_auxiliary] at he
  have hf : Inhomogeneous.spectralVector N Y=finiteTensor N (spectralPolynomial N X) := by
    funext s
    unfold Inhomogeneous.spectralVector liftState liftPolyTensor finiteTensor spectralPolynomial
    have hy : (fun j : Fin N=>Y j.val)=X := by
      funext j
      exact extendData_fin N X j
    rw [hy]
  rw [hf] at he
  funext s
  let sn : ℕ → Spin:=fun j=>if h : j<N then s ⟨j,h⟩ else .zero
  have hh:=congrFun he sn
  rw [tracedTrain_matrix] at hh
  simp only [Pi.smul_apply,smul_eq_mul,finiteTensor] at hh
  have hr : (fun j : Fin N=>sn j.val)=s := by funext j; simp [sn,j.isLt]
  rw [hr] at hh
  exact hh

end AnalyticVacuum
end PolynomialVacuumAlgebra

end OAI
