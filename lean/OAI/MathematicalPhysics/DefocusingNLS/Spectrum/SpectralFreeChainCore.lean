import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeChainDifference
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeRobinPropagation

namespace OAI

/-! A forced free solution differs from its outgoing parameter correction by
an ordinary homogeneous solution. -/

open Set
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralFreeChain_core_coefficients (β lam η : ℂ) (L R : ℝ)
    (hL : 0 < L) (hR : L < R) (a b : ℂ)
    (U₀ U₁ P N DP DN : ℝ → E₄) (C : E₄ →L[ℂ] (Fin 2 → ℂ))
    (hU₀ : ∀ r ∈ Icc L R, U₀ r = a • P r + b • N r)
    (hC₀ : C (U₀ L)=0) (hC₁ : C (U₁ L)=0)
    (hcont : ContinuousOn U₁ (Icc L R))
    (hD : ∀ r ∈ Ioo L R, HasDerivAt U₁
      (spectralFreePhysicalPairField β lam η r (U₁ r)+spectralFreeChainSource (U₀ r)) r)
    (hP : ∀ r ∈ Icc L R, HasDerivAt P (spectralFreePhysicalPairField β lam η r (P r)) r)
    (hN : ∀ r ∈ Icc L R, HasDerivAt N (spectralFreePhysicalPairField β lam η r (N r)) r)
    (hDP : ∀ r ∈ Icc L R, HasDerivAt DP
      (spectralFreePhysicalPairField β lam η r (DP r)+spectralFreeChainSource (P r)) r)
    (hDN : ∀ r ∈ Icc L R, HasDerivAt DN
      (spectralFreePhysicalPairField β lam η r (DN r)+spectralFreeChainSource (N r)) r)
    (c : ℂ × ℂ) (hc : U₁ R = a • DP R+b • DN R+(c.1 • P R+c.2 • N R)) :
    a • C (P L)+b • C (N L)=0 ∧
      c.1 • C (P L)+c.2 • C (N L)+a • C (DP L)+b • C (DN L)=0 := by
  have hPc : ContinuousOn P (Icc L R) := fun r hr => (hP r hr).continuousAt.continuousWithinAt
  have hNc : ContinuousOn N (Icc L R) := fun r hr => (hN r hr).continuousAt.continuousWithinAt
  have hDPc : ContinuousOn DP (Icc L R) := fun r hr => (hDP r hr).continuousAt.continuousWithinAt
  have hDNc : ContinuousOn DN (Icc L R) := fun r hr => (hDN r hr).continuousAt.continuousWithinAt
  let Z := fun r => U₁ r - (a • DP r + b • DN r)
  let W := fun r => c.1 • P r + c.2 • N r
  have hZc : ContinuousOn Z (Icc L R) := hcont.sub
    ((hDPc.const_smul a).add (hDNc.const_smul b))
  have hWc : ContinuousOn W (Icc L R) :=
    (hPc.const_smul c.1).add (hNc.const_smul c.2)
  have hZd (r : ℝ) (hr : r ∈ Ioo L R) : HasDerivAt Z
      (spectralFreePhysicalPairField β lam η r (Z r)) r :=
    spectralFreeChain_difference β lam _ a b U₀ U₁ P N DP DN r
      (hU₀ r (Ioo_subset_Icc_self hr)) (hD r hr) (hDP r (Ioo_subset_Icc_self hr)) (hDN r (Ioo_subset_Icc_self hr))
  have hWd (r : ℝ) (hr : r ∈ Ioo L R) : HasDerivAt W
      (spectralFreePhysicalPairField β lam η r (W r)) r :=
    spectralFreeCombination_hasDerivAt β lam η P N c.1 c.2 r
      (hP r (Ioo_subset_Icc_self hr)) (hN r (Ioo_subset_Icc_self hr))
  have hZR : Z R = W R := by
    change U₁ R - (a • DP R + b • DN R) = W R
    change U₁ R = a • DP R + b • DN R + W R at hc
    rw [hc]
    abel
  have he := spectralFree_eq_on_annulus β lam η Z W L R hL hR
    hZc hWc hZd hWd hZR
  have hLL : L ∈ Icc L R := ⟨le_rfl,hR.le⟩
  have hC₀' := hC₀
  have hC₁' := hC₁
  have hbase : a • C (P L) + b • C (N L)=0 := by
    rw [hU₀ L hLL,map_add,map_smul,map_smul] at hC₀'
    exact hC₀'
  have hchain := congrArg C (he hLL)
  change C (U₁ L - (a • DP L + b • DN L)) = C (c.1 • P L + c.2 • N L) at hchain
  simp only [map_sub,map_add,map_smul,hC₁'] at hchain
  have hzero : c.1 • C (P L) + c.2 • C (N L) + a • C (DP L) + b • C (DN L)=0 := by
    ext j
    have hj := congrFun hchain j
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hj ⊢
    linear_combination -hj
  exact ⟨hbase,hzero⟩

end DefocusingNLS

end OAI
