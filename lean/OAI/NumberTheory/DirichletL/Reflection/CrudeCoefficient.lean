import OAI.NumberTheory.DirichletL.Reflection.KernelBaseline
import OAI.NumberTheory.DirichletL.Descent.MarkedPhase

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve LocalReflectionBrackets InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma norm_bracket_le_card {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (j : ℕ) (x : F) : ‖bracket χ j x‖≤(Fintype.card F:ℝ) := by
  have hq : (1:ℝ)≤Fintype.card F := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0:F)⟩
  have hr : 1≤rootCard F := by
    unfold rootCard
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hq)
  have hi : (rootCard F)⁻¹≤1 := (inv_le_one₀ rootCard_pos).mpr hr
  by_cases hj4 : j=4
  · subst j
    by_cases hx : x=0
    · subst x
      rw [norm_bracket_four_zero]
      apply (div_le_iff₀ rootCard_pos).mpr
      nlinarith
    · rw [norm_bracket_four_nonzero χ x hx]
      exact hi.trans hq
  · by_cases hj0 : j=0
    · subst j
      exact (norm_bracket_zero_le χ x).trans (hi.trans hq)
    · exact (norm_bracket_nonexceptional_le_one χ j hj4 hj0 x).trans hq

variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

lemma mixedActiveBracket_crude_norm (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (i : ι) (x : Eis) :
    ‖mixedActiveBracket G.generator_ne_zero G.generator_good j S D i x‖≤(Ideal.absNorm (G.ideal i):ℝ) := by
  rw [mixedActiveBracket_eq_signed]
  have hn : ‖(if i∈S then (-1:ℂ) else 1)‖=1 := by split_ifs <;> simp
  have hjm : markedActiveExponent S j i<6 := by
    unfold markedActiveExponent
    split_ifs
    · norm_num
    · exact hj i
  have hc : ∀ i, ringChar (Eis⧸Ideal.span {G.generator i})≠2 := by
    intro i
    rw [G.generator_span]
    exact hchar i
  rw [norm_mul,hn,one_mul,norm_mul,local_phase_norm D G.generator_ne_zero G.generator_good hc i _ hjm,one_mul]
  apply (norm_bracket_le_card _ _ _).trans_eq
  have he : Fintype.card (Eis⧸Ideal.span {G.generator i})=Ideal.absNorm (Ideal.span {G.generator i}) := by
    rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
  rw [he,G.generator_span]

lemma literal_mixed_coefficient_crude (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) :
    ‖s.amplitude u m n b *
      (star D.fixedFactor*ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U (s.modelDualNumerator u m n b))*
      ∏ i, mixedActiveBracket G.generator_ne_zero G.generator_good j S D i (s.modelDualNumerator u m n b)‖≤
      (Ideal.absNorm (∏ i,G.ideal i):ℝ) := by
  rw [norm_mul,norm_mul,norm_mul,norm_star,D.fixedFactor_norm hN G.generator_product_primary hbase,
    ShortDraftCusp.A4BadPhase_norm,one_mul,mul_one]
  apply (mul_le_of_le_one_left (norm_nonneg _) (s.amplitude_norm u m n b)).trans
  rw [norm_prod,map_prod,Nat.cast_prod]
  exact Finset.prod_le_prod₀ (fun i hi => norm_nonneg _) (fun i hi => mixedActiveBracket_crude_norm G D hchar j hj S i _)

end
end SevenEighths.InverseReflectedPhase

end OAI
