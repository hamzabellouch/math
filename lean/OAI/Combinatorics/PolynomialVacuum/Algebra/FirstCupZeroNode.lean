import OAI.Combinatorics.PolynomialVacuum.Algebra.FirstCupNodes

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

noncomputable def prefixProduct (n : ℕ) (X : ℕ → ℂ) : ℂ := ∏ k ∈ Finset.range n, X k

def LastZeroReduction (Ψ ψ : NatSpectralTensor) (n : ℕ) : Prop :=
  ∀ X s, X n=0 → s n≠Spin.plus → Ψ X s=
    if s n=Spin.zero then prefixProduct n X*ψ X s else 0

theorem fusionPair_zero (a : ℂ) : fusionPair a 0=T*a^2 := by
  simp only [fusionPair,T,t]
  vacuum_ring_finish

theorem prefixProduct_dropTwo (n : ℕ) (X : ℕ → ℂ) :
    prefixProduct (n+2) X=X 0*X 1*prefixProduct n (skipTwo 0 X) := by
  simp only [prefixProduct,skipTwo_zero_apply]
  rw [show n+2=2+n by omega,Finset.prod_range_add]
  simp only [Finset.prod_range_succ,Finset.range_zero,Finset.prod_empty,one_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Nat.add_comm 2 k]

theorem firstCup_zero_scalar (n : ℕ) (X : ℕ → ℂ) (hX : X 1=T*X 0) (h0 : X (n+2)=0) :
    prefixProduct (n+2) X*naturalFusion n 0 X=
      naturalFusion (n+1) 0 X*prefixProduct n (skipTwo 0 X) := by
  simp only [prefixProduct_dropTwo,naturalFusion,fusionProduct,Finset.prod_range_succ,
    skipTwo_zero_apply,h0,fusionPair_zero,hX]
  ring

 

theorem firstCup_zeroNode {Ψ ψ χ φ : NatSpectralTensor} {n : ℕ}
    (hΨ : LastZeroReduction Ψ χ (n+2)) (hψ : LastZeroReduction ψ φ n)
    (hχ : FirstCupReduction χ φ n)
    (X : ℕ → ℂ) (s : ℕ → Spin) (hX : X 1=T*X 0) (h0 : X (n+2)=0)
    (hs : s (n+2)≠Spin.plus) :
    Ψ X s=(naturalFusion (n+1) 0 X • cupLinear 0 (ψ (skipTwo 0 X))) s := by
  rw [hΨ X s h0 hs,hχ X hX]
  have hz := hψ (skipTwo 0 X) (skipTwo 0 s) (by simpa using h0) (by simpa using hs)
  simp only [Pi.smul_apply,smul_eq_mul,cupLinear,LinearMap.coe_mk,AddHom.coe_mk]
  rw [hz]
  simp only [skipTwo_zero_apply]
  split_ifs
  · have he := firstCup_zero_scalar n X hX h0
    linear_combination he * cup (s 0,s 1) * φ (skipTwo 0 X) (skipTwo 0 s)
  · simp

end PolynomialVacuumAlgebra

end OAI
