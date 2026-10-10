import OAI.Combinatorics.PolynomialVacuum.Algebra.ThreeSiteRestriction
import OAI.Combinatorics.PolynomialVacuum.Algebra.AllFinalCupZeros

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem eval_of_killSite_zero (p : MvPolynomial ℕ ℂ) (j : ℕ) (h : killSite j p=0)
    (X : ℕ → ℂ) (hX : X j=0) : eval X p=0 := by
  have he := congrArg (eval X) h
  simp only [eval_killSite,map_zero,update_nat_decidable] at he
  have hu : Function.update X j 0=X := by
    funext k
    by_cases hk : k=j <;> simp_all
  rw [hu] at he
  exact he

theorem quotient_three_site_zero (r : NatPolyTensor)
    (hd : ∀ s j, j < 3 → (r s).degreeOf j ≤ 1)
    (hp : ∀ s j, j < 3 → s j=Spin.plus → (r s).degreeOf j ≤ 0)
    (hm : ∀ s j, j < 3 → s j=Spin.minus → killSite j (r s)=0)
    (hex : ∀ j, j < 2 → ∀ Y, siteR j (Y j) (Y (j+1)) (evalNatPolyTensor r Y)=
      eigenOne (Y j) (Y (j+1)) • evalNatPolyTensor r (swapSite j Y)) : ∀ s, r s=0 := by
  intro s
  apply MvPolynomial.funext
  intro Y
  have he : ∀ x y z a b c, restrictThree r Y s x y z a b c=0 := by
    apply trilinear_rigidity
    · intro y z a b c
      have ht := eval_update_affine (r (setFirstThree s a b c)) 0 (setFirstThree Y 0 y z) (hd _ 0 (by omega))
      simpa only [update_nat_decidable,setFirstThree_update0,restrictThree] using ht
    · intro x z a b c
      have ht := eval_update_affine (r (setFirstThree s a b c)) 1 (setFirstThree Y x 0 z) (hd _ 1 (by omega))
      simpa only [update_nat_decidable,setFirstThree_update1,restrictThree] using ht
    · intro x y a b c
      have ht := eval_update_affine (r (setFirstThree s a b c)) 2 (setFirstThree Y x y 0) (hd _ 2 (by omega))
      simpa only [update_nat_decidable,setFirstThree_update2,restrictThree] using ht
    · intro a b c ha x y z
      have ht := eval_update_constant (r (setFirstThree s a b c)) 0 (setFirstThree Y 0 y z)
        (hp _ 0 (by omega) (by simpa using ha)) x
      simpa only [update_nat_decidable,setFirstThree_update0,restrictThree] using ht
    · intro a b c hb x y z
      have ht := eval_update_constant (r (setFirstThree s a b c)) 1 (setFirstThree Y x 0 z)
        (hp _ 1 (by omega) (by simpa using hb)) y
      simpa only [update_nat_decidable,setFirstThree_update1,restrictThree] using ht
    · intro a b c hc x y z
      have ht := eval_update_constant (r (setFirstThree s a b c)) 2 (setFirstThree Y x y 0)
        (hp _ 2 (by omega) (by simpa using hc)) z
      simpa only [update_nat_decidable,setFirstThree_update2,restrictThree] using ht
    · intro a b c ha y z
      exact eval_of_killSite_zero _ 0 (hm _ 0 (by omega) (by simpa using ha)) _ (by simp)
    · intro a b c hb x z
      exact eval_of_killSite_zero _ 1 (hm _ 1 (by omega) (by simpa using hb)) _ (by simp)
    · intro a b c hc x y
      exact eval_of_killSite_zero _ 2 (hm _ 2 (by omega) (by simpa using hc)) _ (by simp)
    · exact restrictThree_exchange1 r Y s (hex 0 (by omega))
    · exact restrictThree_exchange2 r Y s (hex 1 (by omega))
  simpa only [restrictThree,setFirstThree_restore,map_zero] using he (Y 0) (Y 1) (Y 2) (s 0) (s 1) (s 2)

theorem polynomial_cup_zero_all {m : ℕ} (p : NatPolyTensor)
    (hex : LowerExchange (evalNatPolyTensor p) m)
    (hc : ∀ i, i+1 < m → ∀ X, X (i+1)=T*X i → evalNatPolyTensor p X=0)
    (i k : ℕ) (hik : i < k) (hk : k < m) (s : ℕ → Spin) : cupSpecialize i k (p s)=0 := by
  have he : cupSpecialize i k (p s)=cupSpecialize i k 0 := by
    apply cupSurface_eq_of_generic i k (by omega) _ _ (partialTrainGuard k i) (partialTrainGuard_surface hik)
    intro Y hY hG
    have hz := cupZero_transport_generic hex hik hk (hc i (by omega)) Y hY (by simpa using hG)
    simpa only [evalNatPolyTensor,Pi.zero_apply,map_zero] using congrFun hz s
  simpa only [map_zero] using he

 

theorem cup_vanishing_rigidity {m : ℕ} (hm : 3 ≤ m) (p : NatPolyTensor)
    (hex : LowerExchange (evalNatPolyTensor p) m)
    (hc : ∀ i, i+1 < m → ∀ X, X (i+1)=T*X i → evalNatPolyTensor p X=0)
    (hd : ∀ s j, j < m → (p s).degreeOf j ≤ m)
    (hp : ∀ s j, j < m → s j=Spin.plus → (p s).degreeOf j ≤ m-1)
    (hz : ∀ s j, j < m → s j=Spin.minus → killSite j (p s)=0) : ∀ s, p s=0 := by
  have hdiv (s : ℕ → Spin) : cupVandermonde m ∣ p s :=
    cupVandermonde_dvd m (p s) (fun i k hik hk => polynomial_cup_zero_all p hex hc i k hik hk s)
  choose r hr using hdiv
  have he (j : ℕ) (hj : j+1 < m) := cupQuotient_exchange hj p r hr (hex j hj)
  have hzero : ∀ s, r s=0 := by
    apply quotient_three_site_zero
    · intro s j hj
      apply cupQuotient_degree m j 1 (by omega) (p s) (r s) (hr s)
      have hd' := hd s j (by omega)
      omega
    · intro s j hj hs
      apply cupQuotient_degree m j 0 (by omega) (p s) (r s) (hr s)
      simpa only [Nat.add_zero] using hp s j (by omega) hs
    · intro s j hj hs
      exact cupQuotient_minus_zero m j (p s) (r s) (hr s) (hz s j (by omega) hs)
    · intro j hj
      exact he j (by omega)
  intro s
  rw [hr s,hzero s,mul_zero]

end PolynomialVacuumAlgebra

end OAI
