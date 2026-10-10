import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerAssignedPair

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerMass
open InverseMoment InverseInitialArithmetic InverseInitialQuotientGeometry
open InverseInitialEnergyCallerAssigned
local notation "Eis"=>ActualEisensteinCubic.O

theorem assigned_quotient_subset {ι σ:Type*}[DecidableEq ι][DecidableEq σ]
    (p:ι→Eis)(S:Finset (Source (ι:=ι) 0))(J₁ J₂:Finset σ)(L₁ L₂:σ→Finset ι) :
    quotientSet p (assignedSource S J₁ J₂ L₁ L₂)⊆quotientSet p S := by
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨⟨y,q⟩,hy,rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨y,(Finset.mem_product.mp (Finset.mem_filter.mp hy).1).1,rfl⟩

theorem divisor_weight_mono {t:Ideal Eis}(ht:t≠0){J K:ℕ}(hJK:J≤K) :
    ((idealDivisors t).card:ℝ)^J≤((idealDivisors t).card:ℝ)^K := by
  have hc : (1:ℝ)≤(idealDivisors t).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1,(mem_idealDivisors ht).mpr (one_dvd t)⟩
  exact pow_le_pow_right₀ hc hJK

theorem assigned_quotient_mass (K:ℕ)(U π:ℝ)(hU:0≤U)(hπ:0<π) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (S:Finset (Source (ι:=ι) 0))(J₁ J₂:Finset σ)(L₁ L₂:σ→Finset ι)
      (_hJ:J₁.card+J₂.card≤K)(Z R:ℝ)(_hZ:1≤Z)(_hR:R≤U)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R),
      (∑t∈quotientSet p (assignedSource S J₁ J₂ L₁ L₂),
        ((idealDivisors t).card:ℝ)^(J₁.card+J₂.card))≤C*Z^(R+π) := by
  have hε : 0<π/(U+1) := div_pos hπ (by linarith)
  obtain ⟨C,hC,hb⟩ := normalized_mass_bound K (π/(U+1)) hε
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ S J₁ J₂ L₁ L₂ hJ Z R hZ hR hn
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  let T := quotientSet p (assignedSource S J₁ J₂ L₁ L₂)
  have ht : ∀t∈T,t≠0 := quotientSet_nonzero p hp _
  have hnorm : ∀t∈T,(t.absNorm:ℝ)≤Z^R :=
    fun t hh=>hn t (assigned_quotient_subset p S J₁ J₂ L₁ L₂ hh)
  have hm := hb T (Z^R) (Real.rpow_pos_of_pos hZp _) ht hnorm
  have hpow : (Z^R)^(π/(U+1))≤Z^π := by
    rw [←Real.rpow_mul hZp.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    apply (mul_le_mul_of_nonneg_right hR hε.le).trans
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0<U+1)).mpr
    nlinarith
  have hm' := hm.trans (mul_le_mul_of_nonneg_left hpow hC.le)
  have hs := mul_le_mul_of_nonneg_left hm' (Real.rpow_nonneg hZp.le R)
  simp only [normalizedMass,←mul_assoc,mul_inv_cancel₀ (Real.rpow_pos_of_pos hZp R).ne',one_mul] at hs
  calc
    _≤∑t∈T,((idealDivisors t).card:ℝ)^K :=
      Finset.sum_le_sum fun t hmem=>divisor_weight_mono (ht t hmem) hJ
    _≤Z^R*(C*Z^π) := by simpa only [mul_assoc] using hs
    _=C*Z^(R+π) := by rw [Real.rpow_add hZp];ring

end SevenEighths.InverseInitialEnergyCallerMass

end

end OAI
