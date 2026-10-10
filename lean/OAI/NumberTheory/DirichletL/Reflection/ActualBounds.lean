import OAI.NumberTheory.DirichletL.Reflection.NormalizedColumns

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma two_block_phase_bounds (F : PrimeFamily φ) (S : PrimeFamily σ) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hcop : Pairwise (Function.onFun IsCoprime (F.sum S).ideal))
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) ((F.sum S).ideal i))
    (hchar : ∀ i, ringChar (Eis ⧸ (F.sum S).ideal i) ≠ 2) (u : Eisˣ) (m : ℕ) :
    ‖sourceRowPhase s (F.sum S).generator_ne_zero (F.sum S).generator_good
      (Sum.elim jF (fun _ => 1)) (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m‖ ≤ 1 ∧
    ‖actualSlotPhase F S jF s u m‖ ≤ 1 := by
  classical
  obtain ⟨D⟩ := (F.sum S).exists_controlled N a c mode hc hN hbase hac hcop hNp
  have hcp : Pairwise (Function.onFun IsCoprime
      (fun i => Ideal.span {(F.sum S).generator i})) := by
    simpa only [PrimeFamily.generator_span] using hcop
  have hch : ∀ i, ringChar (Eis ⧸ Ideal.span {(F.sum S).generator i}) ≠ 2 := by
    intro i
    have he := congrArg (fun I : Ideal Eis => ringChar (Eis ⧸ I)) ((F.sum S).generator_span i)
    exact he.symm ▸ hchar i
  have hd : Disjoint (Finset.univ.image (Sum.inr : σ → φ ⊕ σ)) (Finset.univ.image Sum.inl) := by
    simp only [Finset.disjoint_left,Finset.mem_image,Finset.mem_univ,true_and]
    rintro i ⟨k,rfl⟩ ⟨f,h⟩
    cases h
  exact ⟨sourceRowPhase_norm_le_one D s _ _ hch hcp _ _ _ hd u m,
    sourceSlotPhase_norm_le_one D s _ _ hch hcp _ _ _ hd u m⟩

lemma actualRowPhase_norm_le_one (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (jF : φ → ℕ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hFK : ∀ f, IsCoprime (F.ideal f) K)
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hNK : IsCoprime (Ideal.span {N}) K)
    (hcharF : ∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) (u : Eisˣ) (m : ℕ) :
    ‖actualRowPhase F K hK jF s u m‖ ≤ 1 := by
  have hcp := PrimeFamily.sum_pairwise F (PrimeFamily.residual K hK) hF
    (PrimeFamily.residual_pairwise K hK) (fun f P =>
      (hFK f).of_isCoprime_of_dvd_right (PrimeFamily.residual_dvd K hK P))
  have hNp : ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (PrimeFamily.residual K hK)).ideal i) := by
    intro i
    cases i with
    | inl f => exact hNF f
    | inr P => exact hNK.of_isCoprime_of_dvd_right (PrimeFamily.residual_dvd K hK P)
  have hchar : ∀ i, ringChar (Eis ⧸ (F.sum (PrimeFamily.residual K hK)).ideal i) ≠ 2 := by
    intro i
    cases i with
    | inl f => exact hcharF f
    | inr P => exact (hK.2.2 P.val (Multiset.mem_toFinset.mp P.property)).2
  have hh := (two_block_phase_bounds F (PrimeFamily.residual K hK) jF s hc hN hbase hac hcp hNp hchar u m).1
  unfold actualRowPhase
  convert hh using 1 ; congr 2 <;> ext i <;> simp

lemma actualFrozenPhase_norm_le_one (F : PrimeFamily φ) (jF : φ → ℕ) (κ : ℂ) (hκ : ‖κ‖ ≤ 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hcharF : ∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) (hj : ∀ f, jF f < 6) (u : Eisˣ) (m : ℕ) :
    ‖actualFrozenPhase F jF κ s u m‖ ≤ 1 := by
  obtain ⟨D⟩ := F.exists_controlled N a c mode hc hN hbase hac hF hNF
  have hcp : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {F.generator i})) := by
    simpa only [PrimeFamily.generator_span] using hF
  have hch : ∀ i, ringChar (Eis ⧸ Ideal.span {F.generator i}) ≠ 2 := by
    intro i
    have he := congrArg (fun I : Ideal Eis => ringChar (Eis ⧸ I)) (F.generator_span i)
    exact he.symm ▸ hcharF i
  rw [actualFrozenPhase,norm_mul,norm_mul,norm_star,
    frozenCore_norm D _ _ hch hcp _ _ (fun i _ => hj i),ramifiedBlock_norm,mul_one,mul_one]
  exact hκ

end
end SevenEighths.InverseReflectedPhase

end OAI
