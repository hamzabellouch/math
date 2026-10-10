import OAI.NumberTheory.DirichletL.Detector.GramCanonicalBlock

namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma min_product_amplification (L T : ℝ) (hL : 0≤L) (hT : 0≤T) (A : ℕ) :
    min 1 ((L*T)^A)≤(1+T)^A*min 1 (L^A) := by
  by_cases h : L^A≤1
  · rw [min_eq_right h]
    apply (min_le_right _ _).trans
    rw [mul_pow,mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hT (by linarith) _) (pow_nonneg hL _)
  · rw [min_eq_left (le_of_not_ge h),mul_one]
    exact (min_le_left _ _).trans (one_le_pow₀ (by linarith))

lemma frequencyScale_ratio (C : SupportedIdeal) (k : GramFrequency) (Y Q : ℝ) :
    frequencyScale C k.val Y Q=(Ideal.absNorm (Ideal.span {k.val}):ℝ)/((Y^2/Q)/Ideal.absNorm C.val) := by
  rw [frequencyScale,ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,div_div_eq_mul_div]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

theorem canonical_nonexceptional_weighted (A : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃(J : ℕ)(H₀ : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧ ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(k : GramFrequency),¬ExceptionalFrequency S hS C k→
      ∀(d : O)(U : SchwartzMap ℝ ℂ)(v H N : ℝ),0<H→0<N→
        ‖canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*
          (Ideal.absNorm C.val:ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*H/N)^A)*
          (1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ) := by
  obtain ⟨J,H₀,hblock⟩ := canonical_nonexceptional_block A (A+2) hA a₀ b₀ ha₀ hab
  refine ⟨J,H₀,?_⟩
  intro W hs hW
  obtain ⟨K,hK,hblock⟩ := hblock W hs hW
  refine ⟨K,hK,?_⟩
  intro S hS σ C k hk d U v H N hH hN
  let t : ℝ := (Ideal.absNorm (Ideal.span {k.val}):ℝ)/H
  let L : ℝ := (Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*H/N
  have ht : 0≤t := by dsimp [t];positivity
  have hL : 0≤L := by dsimp [L];positivity
  have htp : 0<1+t := by linarith
  have he : (Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*Ideal.absNorm (Ideal.span {k.val})/N=L*t := by
    dsimp [L,t]
    field_simp
  have hb := hblock S hS σ C k hk d U v t N ht hN
  rw [he] at hb
  apply hb.trans
  calc
    _≤K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J/(1+t)^(A+2)*
        (Ideal.absNorm C.val:ℝ)*N^2*((1+t)^A*min 1 (L^A)) :=
      mul_le_mul_of_nonneg_left (min_product_amplification L t hL ht A) (by positivity)
    _=K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Ideal.absNorm C.val:ℝ)*N^2*
        min 1 (L^A)*(1+t)^(-2:ℝ) := by
      rw [Real.rpow_neg htp.le,Real.rpow_two,pow_add]
      field_simp
    _=_ := rfl

end SevenEighths.ProbeGramCommon
end

end OAI
