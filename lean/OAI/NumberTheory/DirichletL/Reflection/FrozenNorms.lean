import OAI.NumberTheory.DirichletL.Reflection.BoundedTemplates

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} {p : ι → Eis} {N a c : Eis} {mode : Bool}

lemma frozenCofactorCharacter_cross_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i k : ι) (hik : i ≠ k) (j : ℕ) :
    ‖frozenCofactorCharacter (Ideal.span {p i}) (hg i) j (p k)‖ = 1 := by
  have hn := crossSymbol_norm hg hcop i k hik
  unfold frozenCofactorCharacter
  split_ifs
  · simp only [MonoidHom.comp_apply,RingHom.toMonoidHom_eq_coe,MulChar.coe_toMonoidHom,
      MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0),MulChar.inv_apply_eq_inv',norm_pow,norm_inv]
    change ‖MixedCrossSeparation.crossSymbol p hg i k‖⁻¹^2 = 1
    rw [hn]; norm_num
  · simp only [MonoidHom.comp_apply,RingHom.toMonoidHom_eq_coe,MulChar.coe_toMonoidHom,
      MulChar.pow_apply' _ (by omega : 2*j+2 ≠ 0),norm_pow]
    change ‖MixedCrossSeparation.crossSymbol p hg i k‖^(2*j+2) = 1
    rw [hn,one_pow]

lemma frozenCofactorCharacter_product_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i : ι) (S : Finset ι) (hi : i ∉ S) (j : ℕ) :
    ‖frozenCofactorCharacter (Ideal.span {p i}) (hg i) j (∏ k ∈ S, p k)‖ = 1 := by
  rw [map_prod,norm_prod]
  apply Finset.prod_eq_one
  intro k hk
  exact frozenCofactorCharacter_cross_norm hg hcop i k (fun h => hi (h ▸ hk)) j

variable [Fintype ι]

lemma frozenPrimeScalar_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i : ι) (j : ℕ) (hj : j < 6) : ‖frozenPrimeScalar (p i) c (hp i) (hg i) j‖ = 1 := by
  have hh := local_phase_norm D hp hg hchar i j hj
  rw [controlled_frozen_phase,norm_mul] at hh
  have hn : ‖frozenCofactorCharacter (Ideal.span {p i}) (hg i) j (cofactor p i)‖ = 1 := by
    exact frozenCofactorCharacter_product_norm hg hcop i (Finset.univ.erase i) (by simp) j
  simpa only [hn,mul_one] using hh

lemma frozenCore_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (j : ι → ℕ) (F : Finset ι) (hj : ∀ i ∈ F, j i < 6) : ‖frozenCore hp hg c j F‖ = 1 := by
  rw [frozenCore,norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  rw [norm_mul,frozenPrimeScalar_norm D hp hg hchar hcop i (j i) (hj i hi),one_mul]
  exact frozenCofactorCharacter_product_norm hg hcop i (F.erase i) (by simp) (j i)

lemma sourceFrozenPhase_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hN : (9:Eis)*c ∣ N) (hr : λ₀^2 ∣ (∏ i, p i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (j : ι → ℕ) (F : Finset ι) (hj : ∀ i ∈ F, j i < 6) (u : Eisˣ) (m : ℕ) :
    ‖sourceFrozenPhase D s hp hg j F u m‖ = 1 := by
  rw [sourceFrozenPhase,norm_mul,norm_mul,norm_star,D.fixedFactor_norm hN hr hbase,
    frozenCore_norm D hp hg hchar hcop j F hj,ramifiedBlock_norm]
  norm_num

end
end SevenEighths.InverseReflectedPhase

end OAI
