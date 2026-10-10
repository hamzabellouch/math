import OAI.Combinatorics.PolynomialVacuum.Separator.Normalization

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra

 

noncomputable def separatorComplexExponent (s : ℂ) : ℂ :=
  1/6+2*s^2/(3*(Real.pi : ℂ)^2)

noncomputable def normalizedSeparatorFamily (n : ℕ) (s : ℂ) : ℂ :=
  separatorPolynomial n (2*Complex.cosh s) *
    Complex.exp (-separatorComplexExponent s * Real.log (n : ℝ))

noncomputable def separatorNormalizationPoint : ℂ := (Real.pi/2 : ℝ)*Complex.I

theorem separatorComplexExponent_re (s : ℂ) :
    (separatorComplexExponent s).re=separatorExponent s := by
  unfold separatorComplexExponent separatorExponent
  have hr : (3*(Real.pi : ℂ)^2)=((3*Real.pi^2 : ℝ) : ℂ) := by push_cast; rfl
  rw [Complex.add_re,hr,Complex.div_ofReal_re]
  norm_num

theorem normalizationPoint_cosh : Complex.cosh separatorNormalizationPoint=0 := by
  rw [separatorNormalizationPoint,Complex.cosh_mul_I]
  simp

theorem normalizationPoint_exponent : separatorComplexExponent separatorNormalizationPoint=0 := by
  have hp : (Real.pi : ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  unfold separatorComplexExponent separatorNormalizationPoint
  push_cast
  field_simp
  norm_num [Complex.I_sq]

theorem normalizedSeparatorFamily_normalized (n : ℕ) :
    normalizedSeparatorFamily n separatorNormalizationPoint=1 := by
  simp [normalizedSeparatorFamily,normalizationPoint_cosh,normalizationPoint_exponent,separator_zero]

theorem normalizedSeparatorFamily_analyticAt (n : ℕ) (hn : 1≤n) (s : ℂ) :
    AnalyticAt ℂ (normalizedSeparatorFamily n) s := by
  have hc : AnalyticAt ℂ (fun s : ℂ=>2*Complex.cosh s) s := by fun_prop
  have hf := (separator_analyticAt n hn (2*Complex.cosh s)).comp (f:=fun z : ℂ=>2*Complex.cosh z) hc
  have he : AnalyticAt ℂ (fun s : ℂ=>
      Complex.exp (-separatorComplexExponent s * Real.log (n : ℝ))) s := by
    unfold separatorComplexExponent
    fun_prop
  exact hf.mul he

theorem normalizedSeparatorFamily_norm (n : ℕ) (hn : 1≤n) (s : ℂ) :
    ‖normalizedSeparatorFamily n s‖=
      ‖separatorPolynomial n (2*Complex.cosh s)‖/(n : ℝ)^separatorExponent s := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast hn
  rw [normalizedSeparatorFamily,norm_mul,Complex.norm_exp]
  have hr : (-separatorComplexExponent s*(Real.log (n : ℝ) : ℂ)).re=
      -(separatorExponent s*Real.log (n : ℝ)) := by
    simp only [Complex.mul_re,Complex.neg_re,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
      separatorComplexExponent_re,neg_mul]
  rw [hr,Real.exp_neg,Real.rpow_def_of_pos hn0]
  simp [div_eq_mul_inv,mul_comm]

 

def SeparatorNormalFamilyBound : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ {s : ℂ | |s.im|<Real.pi} →
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, 1≤n → ∀ s∈K, ‖normalizedSeparatorFamily n s‖≤C

 

theorem normal_family_bound_iff : SeparatorNormalFamilyBound ↔
    (∀ K : Set ℂ, IsCompact K → K ⊆ {s : ℂ | |s.im|<Real.pi} →
      ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, 1≤n → ∀ s∈K,
        ‖separatorPolynomial n (2*Complex.cosh s)‖≤C*(n : ℝ)^separatorExponent s) := by
  constructor
  · intro h K hK hsK
    obtain ⟨C,hC,hbound⟩:=h K hK hsK
    refine ⟨C,hC,?_⟩
    intro n hn s hs
    have hb:=hbound n hn s hs
    rw [normalizedSeparatorFamily_norm n hn] at hb
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast hn : (0 : ℝ)<n) _)).mp hb
  · intro h K hK hsK
    obtain ⟨C,hC,hbound⟩:=h K hK hsK
    refine ⟨C,hC,?_⟩
    intro n hn s hs
    rw [normalizedSeparatorFamily_norm n hn]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast hn : (0 : ℝ)<n) _)).mpr
      (hbound n hn s hs)

end PolynomialVacuumCylinder

end OAI
