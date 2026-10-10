import OAI.Combinatorics.PolynomialVacuum.Algebra.NaturalRotation

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

theorem finRotate_symm_val (n : ℕ) (j : Fin (n+1)) :
    ((finRotate (n+1)).symm j).val=rotationIndex n j.val := by
  by_cases hj : j=0
  · subst j
    have h := (finRotate (n+1)).symm_apply_eq.mpr (finRotate_last (n:=n)).symm
    rw [h]
    simp [rotationIndex]
  · rw [coe_finRotate_symm_of_ne_zero hj]
    simp [rotationIndex,show j.val≠0 from Fin.val_ne_zero_iff.mpr hj]

theorem fusionProduct_rotate (n : ℕ) (a : ℂ) (X : ℕ → ℂ) :
    fusionProduct a (natRotate n X) (n+1)=fusionProduct a X (n+1) := by
  simp only [fusionProduct,← Fin.prod_univ_eq_prod_range,natRotate,Function.comp_apply,← finRotate_symm_val]
  exact Equiv.prod_comp (finRotate (n+1)).symm (fun j : Fin (n+1) => fusionPair a (X j.val))

theorem naturalFusion_rotate {n j : ℕ} (hj : j<n+1) (X : ℕ → ℂ) :
    naturalFusion (n+1) (j+1) (natRotate (n+2) X)=naturalFusion (n+1) j X := by
  simp only [naturalFusion,natRotate_succ,natRotate_skipTwo hj,fusionProduct_rotate]

theorem cyclicTransform_cup {n j : ℕ} (hj : j<n+1) (Ψ ψ : NatSpectralTensor)
    (hc : CupAt Ψ ψ (n+1) (j+1)) (hcy : NaturalCyclic n ψ) :
    CupAt (cyclicTransform (n+2) Ψ) ψ (n+1) j := by
  intro X hX
  have hRX : natRotate (n+2) X (j+1+1)=T*natRotate (n+2) X (j+1) := by
    simpa only [natRotate_succ] using hX
  have he := hc (natRotate (n+2) X) hRX
  funext s
  have hlo := congrFun (hcy (skipTwo j X)) (skipTwo j s)
  have hlast : skipTwo j s n=s (n+2) := by simp [skipTwo,show ¬n<j by omega]
  simp only [cyclicTransform,rotateTensor,hlast] at hlo
  simp only [cyclicTransform,rotateTensor,he,Pi.smul_apply,smul_eq_mul,
    cupLinear,LinearMap.coe_mk,AddHom.coe_mk,natRotate_succ,natRotate_skipTwo hj,
    naturalFusion_rotate hj]
  calc
    _ = naturalFusion (n+1) j X * cup (s j,s (j+1)) *
      (zeta ^ (-charge (s (n+2))) * ψ (natRotate n (skipTwo j X)) (natRotate n (skipTwo j s))) := by ring
    _ = _ := by rw [hlo]; ring

theorem cyclicDiscrepancy_cup {n : ℕ} (Ψ : State (n+3)) (ψ : State (n+1))
    (hc : ∀ i≤n+1, CupAt (liftState Ψ) (liftState ψ) (n+1) i)
    (hcy : NaturalCyclic n (liftState ψ)) (j : ℕ) (hj : j+1<n+2)
    (X : ℕ → ℂ) (hX : X (j+1)=T*X j) : evalNatPolyTensor (cyclicDiscrepancy Ψ) X=0 := by
  rw [eval_cyclicDiscrepancy,cyclicTransform_cup (by omega : j<n+1) _ _ (hc (j+1) (by omega)) hcy X hX,
    hc j (by omega) X hX,sub_self]

end PolynomialVacuumAlgebra

end OAI
