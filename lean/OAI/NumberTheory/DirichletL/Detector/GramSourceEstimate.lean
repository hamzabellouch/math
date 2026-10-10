import OAI.NumberTheory.DirichletL.Detector.GramTruncation

namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem original_source_truncation_bound (δ ε : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (hε : 0<ε) (hε1 : ε<1/6) (a b M₀ : ℝ) (ha : 0<a) (hab : a<b) (hM₀ : 0≤M₀)
    (W : ℝ→ℂ) (hcompact : HasCompactSupport W) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (hWM : ∀x,‖W x‖≤M₀) :
    ∃(J : ℕ)(H₁ H₂ : Finset (ℕ×ℕ))(K₁ K₂ : ℝ),0<K₁ ∧ 0<K₂ ∧
      ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal),fixedBadPrimes⊆S→∀(σ : RayRing)
      (F : Finset SupportedIdeal)(E : Finset GramFrequency)(U : SchwartzMap ℝ ℂ)
      (v Y Q : ℝ)(hY : 0<Y),0<Q→
      ‖sourceTruncation S hS σ F E W hcompact Y Q hY U v‖≤
        K₁*H₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y)*(Y^2/Q)*
          (Y/((Ideal.absNorm (jointFixedModulus S hS):ℝ)*(Y^2/Q)))^(-1+δ)+
        K₂*H₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Q/Y)*
          (Ideal.absNorm (jointFixedModulus S hS):ℝ)^ε*(Y^2/Q)^(1/6:ℝ) := by
  obtain ⟨J,H₁,hgood⟩ := canonical_nonexceptional_ideal_sum δ hδ hδ1 3 (by norm_num) a b ha hab
  obtain ⟨K₁,hK₁,hgood⟩ := hgood W hs hW
  obtain ⟨H₂,K₂,hK₂,hbadbound⟩ := canonical_exceptional_ideal_sum ε hε hε1 a b M₀ ha (by linarith) hM₀
  refine ⟨J,H₁,H₂,K₁,K₂,hK₁,hK₂,?_⟩
  intro S hS hbad σ F E U v Y Q hY hQ
  let G:=sourceDivisorUnion F W hcompact Y hY
  have hα := fun (C : SupportedIdeal) (_ : C∈F) (D : SupportedIdeal) (_ : D∈G)=>sourceMobiusWeight_norm W hcompact Y hY C D
  have hg := hgood S hS σ F G (fun C _=>nonexceptionalFrequencies S hS E C)
    (sourceMobiusWeight W hcompact Y hY) hα
    (by intro C hC D hD k hk;exact (Finset.mem_filter.mp hk).2)
    U v (Y^2/Q) Y Q (by positivity) hY hQ.le
  have hb := hbadbound W hcompact hs hWM S hS σ F G (fun C _=>exceptionalFrequencies S hS E C)
    (sourceMobiusWeight W hcompact Y hY) hα
    (by intro C hC D hD k hk;exact (Finset.mem_filter.mp hk).2)
    U v (Y^2/Q) Y Q (by positivity) hY hQ.le
  rw [sourceTruncation_eq_canonical S hS hbad σ F E W hcompact Y Q hY hQ U v,sourceCanonicalSum_split]
  exact (norm_add_le _ _).trans ((add_le_add hb hg).trans_eq (add_comm _ _))

end SevenEighths.ProbeGramCommon
end

end OAI
