import OAI.Algebra.AffineCancellation.RelativeClearing
import OAI.Algebra.AffineCancellation.PolynomialSlice
import OAI.Algebra.AffineCancellation.TorsorInverse

namespace OAI

noncomputable section

namespace ComplexCancellation.Torsor
open LaurentPolynomial
variable {P : Type*} [CommRing P] [IsDomain P] [Algebra ℂ P]
variable (ρ : Degeneration.G →ₐ[ℂ] P) (Q : Frame ρ) (D : Derivation ℂ Degeneration.G Degeneration.G)
variable (hρ : Function.Injective ρ)
variable (hc : ∀ p, p ∈ InvariantClearing.subalgebra ρ D)
include hρ hc
lemma clear_C (p : P) : C p ∈ RelativeClearing.subalgebra Bundle.pullback (forward ρ Q) D := by
  obtain ⟨c,r,hc,hcn,hcr⟩ := hc p
  refine ⟨c,Bundle.pullback r,hc,hcn,?_⟩
  have h := DFunLike.congr_fun (forward_pullback ρ Q hρ) c
  have h' := DFunLike.congr_fun (forward_pullback ρ Q hρ) r
  change forward ρ Q (Bundle.pullback c)=C (ρ c) at h
  change forward ρ Q (Bundle.pullback r)=C (ρ r) at h'
  rw [h,h',← map_mul,hcr]
lemma clear_T_one : T 1 ∈ RelativeClearing.subalgebra Bundle.pullback (forward ρ Q) D := by
  have he : T 1=C Q.c₀*forward ρ Q (Bundle.j Determinant.a)-C Q.b₀*forward ρ Q (Bundle.j Determinant.d) := by
    rw [forward_j,forward_j,frameMap_a,frameMap_d]
    calc _ = C (Q.a₀*Q.c₀-Q.d₀*Q.b₀)*T 1 := by rw [Q.det,map_one,one_mul]
      _ = _ := by rw [map_sub,map_mul,map_mul]; ring
  rw [he]
  apply sub_mem
  · exact mul_mem (clear_C ρ Q D hρ hc _) (RelativeClearing.image_mem _ _ _ _)
  · exact mul_mem (clear_C ρ Q D hρ hc _) (RelativeClearing.image_mem _ _ _ _)
lemma clear_T_neg_one : T (-1) ∈ RelativeClearing.subalgebra Bundle.pullback (forward ρ Q) D := by
  have he : T (-1)=C Q.a₀*forward ρ Q (Bundle.j Determinant.c)-C Q.d₀*forward ρ Q (Bundle.j Determinant.b) := by
    rw [forward_j,forward_j,frameMap_c,frameMap_b]
    calc _ = C (Q.a₀*Q.c₀-Q.d₀*Q.b₀)*T (-1) := by rw [Q.det,map_one,one_mul]
      _ = _ := by rw [map_sub,map_mul,map_mul]; ring
  rw [he]
  apply sub_mem
  · exact mul_mem (clear_C ρ Q D hρ hc _) (RelativeClearing.image_mem _ _ _ _)
  · exact mul_mem (clear_C ρ Q D hρ hc _) (RelativeClearing.image_mem _ _ _ _)
lemma clear_T (n : ℤ) : T n ∈ RelativeClearing.subalgebra Bundle.pullback (forward ρ Q) D := by
  by_cases hn : 0 ≤ n
  · have he : T n=(T 1 : L (P := P))^n.toNat := by rw [T_pow,Int.toNat_of_nonneg hn,mul_one]
    rw [he]
    exact pow_mem (clear_T_one ρ Q D hρ hc) _
  · have he : T n=(T (-1) : L (P := P))^(-n).toNat := by rw [T_pow,Int.toNat_of_nonneg (by omega : 0 ≤ -n)]; congr 1; omega
    rw [he]
    exact pow_mem (clear_T_neg_one ρ Q D hρ hc) _
lemma clear_laurent (r : L (P := P)) : r ∈ RelativeClearing.subalgebra Bundle.pullback (forward ρ Q) D := by
  induction r using LaurentPolynomial.induction_on' with
  | add r s hr hs => exact add_mem hr hs
  | C_mul_T n p => exact mul_mem (clear_C ρ Q D hρ hc p) (clear_T ρ Q D hρ hc n)
end ComplexCancellation.Torsor

end

end OAI
