import OAI.NumberTheory.Ostmann.QuadraticCenter.CommonCenterBiasJacobi
import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelCharacterTransferBasic

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def affineKernelAverage (P : Finset ℕ) (ε : ℕ → ℤ) (m : ℕ) (h x : ℤ) : ℝ :=
  signedJacobiAverage P ε ((m:ℤ)*x-h)

theorem affineKernelAverage_eq_oriented (P : Finset ℕ) (ε t : ℕ → ℤ)
    (m : ℕ) (h : ℤ) (hcop : ∀p∈P,Nat.Coprime m p)
    (hcenter : ∀p∈P,(p:ℤ)∣h-(m:ℤ)*t p) (x : ℤ) :
    affineKernelAverage P (commonCenterOrientation ε m) m h x =
      orientedQuadraticAverage P ε t x := by
  unfold affineKernelAverage signedJacobiAverage orientedQuadraticAverage
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  exact_mod_cast commonCenter_oriented_jacobi (hcop p hp) (hcenter p hp) x

theorem affineKernelAverage_eq_oriented_of_lt (P : Finset ℕ) (ε t : ℕ → ℤ)
    (m : ℕ) (h : ℤ) (hm : 0 < m) (hP : ∀p∈P,p.Prime ∧ m < p)
    (hcenter : ∀p∈P,(p:ℤ)∣h-(m:ℤ)*t p) (x : ℤ) :
    affineKernelAverage P (commonCenterOrientation ε m) m h x =
      orientedQuadraticAverage P ε t x :=
  affineKernelAverage_eq_oriented P ε t m h
    (fun p hp => commonCenter_multiplier_coprime (hP p hp).1 hm (hP p hp).2) hcenter x

theorem affineKernelAverage_eq_oriented_sub_bad (P : Finset ℕ) (ε t : ℕ → ℤ)
    (m : ℕ) (h : ℤ) (hP : ∀p∈P,p.Prime)
    (hcenter : ∀p∈P,(p:ℤ)∣h-(m:ℤ)*t p) (x : ℤ) :
    affineKernelAverage P (commonCenterOrientation ε m) m h x =
      orientedQuadraticAverage P ε t x-
        (∑p∈P.filter (fun p => p∣m),((ε p*jacobiSym (x-t p) p:ℤ):ℝ))/P.card := by
  classical
  unfold affineKernelAverage signedJacobiAverage orientedQuadraticAverage
  rw [← sub_div,Finset.sum_filter,← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpm : p∣m
  · rw [ite_eq_left hpm,sub_self,commonCenter_oriented_jacobi_of_dvd (hP p hp) hpm]
    simp only [Int.cast_zero]
  · rw [ite_eq_right hpm,sub_zero,
      commonCenter_oriented_jacobi ((hP p hp).coprime_iff_not_dvd.mpr hpm).symm (hcenter p hp)]

theorem affineKernelAverage_abs_le_one (P : Finset ℕ) (hP : 0 < P.card)
    (ε : ℕ → ℤ) (hε : ∀p∈P,ε p=1 ∨ ε p=-1)
    (m : ℕ) (h : ℤ) (hcop : ∀p∈P,Nat.Coprime m p) (x : ℤ) :
    |affineKernelAverage P (commonCenterOrientation ε m) m h x|≤1 := by
  apply abs_signedJacobiAverage_le_one P hP
  intro p hp
  exact (commonCenterOrientation_sign (hε p hp) (hcop p hp)).symm

theorem affineKernelAverage_eq_zero (P : Finset ℕ) (hP : ∀p∈P,p.Prime)
    (ε : ℕ → ℤ) (m : ℕ) (h x : ℤ) (hx : (m:ℤ)*x-h=0) :
    affineKernelAverage P ε m h x=0 := by
  unfold affineKernelAverage signedJacobiAverage
  rw [hx]
  have hs : (∑p∈P,((ε p*jacobiSym 0 p:ℤ):ℝ))=0 := by
    apply Finset.sum_eq_zero
    intro p hp
    simp only [jacobiSym.zero_left (hP p hp).one_lt,mul_zero,Int.cast_zero]
  rw [hs,zero_div]

end Ostmann.QuadraticCenter

end

end OAI
