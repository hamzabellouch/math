import OAI.Combinatorics.PolynomialVacuum.Algebra.FirstCupNodeAssembly

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

def CupAt (Ψ ψ : NatSpectralTensor) (n i : ℕ) : Prop :=
  ∀ X, X (i+1)=T*X i → Ψ X=naturalFusion n i X • cupLinear i (ψ (skipTwo i X))

theorem swapSite_twice {α : Type*} (i : ℕ) (X : ℕ → α) : swapSite i (swapSite i X)=X := by
  funext k
  simp only [swapSite,Function.comp_apply]
  rw [Equiv.swap_apply_self]

theorem skipTwo_cup_slide {α : Type*} (i : ℕ) (X : ℕ → α) :
    skipTwo i (swapSite (i+1) (swapSite i X))=skipTwo (i+1) X := by
  funext k
  simp only [skipTwo,swapSite,Function.comp_apply,Equiv.swap_apply_def]
  split_ifs <;> congr 1 <;> omega

theorem cupAt_step_generic {Ψ ψ : NatSpectralTensor} {n i : ℕ}
    (hΨ : LowerExchange Ψ (n+1)) (hi : i+2 < n+1) (hc : CupAt Ψ ψ n i)
    (Y : ℕ → ℂ) (hY : Y (i+2)=T*Y (i+1))
    (hD : exchangeDenominator (Y (i+1)) (Y i)*exchangeDenominator (T*Y (i+1)) (Y i)≠0) :
    Ψ Y=naturalFusion n (i+1) Y • cupLinear (i+1) (ψ (skipTwo (i+1) Y)) := by
  let X := swapSite (i+1) (swapSite i Y)
  have hx0 : X i=Y (i+1) := by simp [X,swapSite_other (by omega : i≠i+1) (by omega : i≠i+1+1),swapSite_left]
  have hx1 : X (i+1)=T*Y (i+1) := by
    simp only [X,swapSite_left,swapSite_other (by omega : i+1+1≠i) (by omega : i+1+1≠i+1)]
    simpa only [show i+1+1=i+2 by omega] using hY
  have hx2 : X (i+2)=Y i := by
    simp only [X,show i+2=i+1+1 by omega,swapSite_right]
  have hskip : skipTwo i X=skipTwo (i+1) Y := skipTwo_cup_slide i Y
  have hf : naturalFusion n i X=naturalFusion n (i+1) Y := by
    simp only [naturalFusion,hx0,hskip]
  have he1 := hΨ (i+1) (by omega) X
  have he2 := hΨ i (by omega) (swapSite (i+1) X)
  have hback : swapSite i (swapSite (i+1) X)=Y := by simp only [X,swapSite_twice]
  rw [hback] at he2
  have hd0 : swapSite (i+1) X i=Y (i+1) := by simpa only [swapSite_other (by omega : i≠i+1) (by omega : i≠i+1+1)] using hx0
  have hd1 : swapSite (i+1) X (i+1)=Y i := by simpa only [swapSite_left,show i+1+1=i+2 by omega] using hx2
  rw [hd0,hd1] at he2
  simp only [show i+1+1=i+2 by omega,hx1,hx2] at he1
  have he := congrArg (siteR i (Y (i+1)) (Y i)) he1
  rw [map_smul,he2,smul_smul] at he
  rw [hc X (hx1.trans (congrArg (T*·) hx0.symm)),map_smul,map_smul,← Module.End.mul_apply,
    ← Module.End.mul_apply,siteR_cup_slide] at he
  simp only [LinearMap.smul_apply,hf,hskip,smul_smul] at he
  have hs : (exchangeDenominator (Y (i+1)) (Y i)*exchangeDenominator (T*Y (i+1)) (Y i)) • Ψ Y=
      (exchangeDenominator (Y (i+1)) (Y i)*exchangeDenominator (T*Y (i+1)) (Y i)) •
        (naturalFusion n (i+1) Y • cupLinear (i+1) (ψ (skipTwo (i+1) Y))) := by
    rw [smul_smul]
    simpa only [mul_comm,mul_left_comm,mul_assoc] using he.symm
  exact (smul_right_injective _ hD) hs

end PolynomialVacuumAlgebra

end OAI
