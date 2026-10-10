import OAI.NumberTheory.DirichletL.Detector.GramFrequencyMass
import OAI.NumberTheory.DirichletL.Detector.GramPrefactor

namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma normalized_double_sum_bound (F G : Finset SupportedIdeal) (α V : SupportedIdeal→SupportedIdeal→ℂ)
    (hα : ∀C∈F,∀D∈G,‖α C D‖≤1) (p : ℝ) (hp : 0≤p) :
    ‖(p:ℂ)*(∑C∈F,∑D∈G,α C D*V C D)‖≤∑C∈F,∑D∈G,p*‖V C D‖ := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp]
  calc
    _≤p*(∑C∈F,∑D∈G,‖α C D*V C D‖) := mul_le_mul_of_nonneg_left
      ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _=>norm_sum_le _ _))) hp
    _≤p*(∑C∈F,∑D∈G,‖V C D‖) := by
      apply mul_le_mul_of_nonneg_left _ hp
      apply Finset.sum_le_sum
      intro C hC
      apply Finset.sum_le_sum
      intro D hD
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hα C hC D hD) (norm_nonneg _)).trans_eq (one_mul _)
    _=_ := by simp only [Finset.mul_sum]

theorem canonical_nonexceptional_ideal_sum (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (A : ℕ) (hA : 2<A) (a b : ℝ) (ha : 0<a) (hab : a<b) :
    ∃(J : ℕ)(H₀ : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a b)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧ ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (F G : Finset SupportedIdeal)(E : SupportedIdeal→SupportedIdeal→Finset GramFrequency)
      (α : SupportedIdeal→SupportedIdeal→ℂ),
      (∀C∈F,∀D∈G,‖α C D‖≤1)→(∀C∈F,∀D∈G,∀k∈E C D,¬ExceptionalFrequency S hS C k)→
      ∀(U : SchwartzMap ℝ ℂ)(v P Y Q : ℝ),0<P→0<Y→0≤Q→
        ‖((Q/Y^3:ℝ):ℂ)*(∑C∈F,∑D∈G,α C D*∑k∈E C D,
          canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
            ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/(P/gramIdealNorm C))
            (Y/(gramIdealNorm C*gramIdealNorm D)))‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y)*P*
          (Y/((Ideal.absNorm (jointFixedModulus S hS):ℝ)*P))^(-1+δ) := by
  obtain ⟨J,H₀,hfreq⟩ := canonical_nonexceptional_frequency_sum A hA a b ha hab
  obtain ⟨L,hL,hideal⟩ := gram_supported_double_sum δ hδ hδ1
  refine ⟨J,H₀,?_⟩
  intro W hs hW
  obtain ⟨K,hK,hfreq⟩ := hfreq W hs hW
  refine ⟨K*L,mul_pos hK hL,?_⟩
  intro S hS σ F G E α hα hE U v P Y Q hP hY hQ
  let M : ℝ := Ideal.absNorm (jointFixedModulus S hS)
  have hM : 0<M := by dsimp [M];exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (jointFixedModulus_nonzero S hS))
  let V := fun C D : SupportedIdeal=>∑k∈E C D,
    canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
      ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/(P/gramIdealNorm C)) (Y/(gramIdealNorm C*gramIdealNorm D))
  let B := K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y)*P
  have hB : 0≤B := by dsimp [B];positivity
  have ht (C D : SupportedIdeal) (hC : C∈F) (hD : D∈G) :
      (Q/Y^3)*‖V C D‖≤B*(gramIdealNorm C^(-2:ℝ)*gramIdealNorm D^(-2:ℝ)*
        min 1 ((gramIdealNorm C*gramIdealNorm D/(Y/(M*P)))^A)) := by
    have hc := gramIdealNorm_pos C
    have hd := gramIdealNorm_pos D
    have hh := hfreq S hS σ C (E C D) (hE C hC D hD) (primaryGenerator D.val) U v
      (P/gramIdealNorm C) (Y/(gramIdealNorm C*gramIdealNorm D)) (by positivity) (by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (show 0≤Q/Y^3 by positivity)
    apply hh'.trans_eq
    change (Q/Y^3)*(K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*
      gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*(P/gramIdealNorm C)*
      min 1 ((M*gramIdealNorm C*(P/gramIdealNorm C)/(Y/(gramIdealNorm C*gramIdealNorm D)))^A))=_
    calc
      _=(K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J)*
        ((Q/Y^3)*gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*(P/gramIdealNorm C)*
        min 1 ((M*gramIdealNorm C*(P/gramIdealNorm C)/(Y/(gramIdealNorm C*gramIdealNorm D)))^A)) := by ring
      _=_ := by rw [supported_nonexceptional_prefactor C D M P Y Q hM hP hY A];dsimp [B];ring
  calc
    _≤∑C∈F,∑D∈G,(Q/Y^3)*‖V C D‖ := normalized_double_sum_bound F G α V hα _ (by positivity)
    _≤∑C∈F,∑D∈G,B*(gramIdealNorm C^(-2:ℝ)*gramIdealNorm D^(-2:ℝ)*
        min 1 ((gramIdealNorm C*gramIdealNorm D/(Y/(M*P)))^A)) := Finset.sum_le_sum (fun C hC=>Finset.sum_le_sum (fun D hD=>ht C D hC hD))
    _=B*(∑C∈F,∑D∈G,gramIdealNorm C^(-2:ℝ)*gramIdealNorm D^(-2:ℝ)*
        min 1 ((gramIdealNorm C*gramIdealNorm D/(Y/(M*P)))^A)) := by simp only [Finset.mul_sum]
    _≤B*(L*(Y/(M*P))^(-1+δ)) := mul_le_mul_of_nonneg_left (hideal A (by omega) _ (by positivity) F G) hB
    _=_ := by dsimp [B,M];ring

theorem canonical_exceptional_ideal_sum (ε : ℝ) (hε : 0<ε) (hε1 : ε<1/6)
    (a b M₀ : ℝ) (ha : 0<a) (hb : 0≤b) (hM₀ : 0≤M₀) :
    ∃H₀ : Finset (ℕ×ℕ),∃K : ℝ,0<K ∧
      ∀(W : ℝ→ℂ)(_hcompact : HasCompactSupport W),
      (Function.support W⊆Set.Icc a b)→(∀x,‖W x‖≤M₀)→
      ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (F G : Finset SupportedIdeal)(E : SupportedIdeal→SupportedIdeal→Finset GramFrequency)
      (α : SupportedIdeal→SupportedIdeal→ℂ),
      (∀C∈F,∀D∈G,‖α C D‖≤1)→(∀C∈F,∀D∈G,∀k∈E C D,ExceptionalFrequency S hS C k)→
      ∀(U : SchwartzMap ℝ ℂ)(v P Y Q : ℝ),0<P→0<Y→0≤Q→
        ‖((Q/Y^3:ℝ):ℂ)*(∑C∈F,∑D∈G,α C D*∑k∈E C D,
          canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
            ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/(P/gramIdealNorm C))
            (Y/(gramIdealNorm C*gramIdealNorm D)))‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Q/Y)*
          (Ideal.absNorm (jointFixedModulus S hS):ℝ)^ε*P^(1/6:ℝ) := by
  obtain ⟨H₀,K,hK,hfreq⟩ := canonical_exceptional_frequency_sum a b M₀ ε ha hb hM₀ hε
  obtain ⟨L,hL,hideal⟩ := gram_supported_exceptional_sum ε hε.le hε1
  refine ⟨H₀,K*L,mul_pos hK hL,?_⟩
  intro W hcompact hs hW S hS σ F G E α hα hE U v P Y Q hP hY hQ
  let M : ℝ := Ideal.absNorm (jointFixedModulus S hS)
  have hM : 0<M := by dsimp [M];exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (jointFixedModulus_nonzero S hS))
  let V := fun C D : SupportedIdeal=>∑k∈E C D,
    canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
      ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/(P/gramIdealNorm C)) (Y/(gramIdealNorm C*gramIdealNorm D))
  let B := K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Q/Y)*M^ε*P^(1/6:ℝ)
  have hB : 0≤B := by dsimp [B];positivity
  have ht (C D : SupportedIdeal) (hC : C∈F) (hD : D∈G) :
      (Q/Y^3)*‖V C D‖≤B*(gramIdealNorm C^(-7/6+ε:ℝ)*gramIdealNorm D^(-2:ℝ)) := by
    have hc := gramIdealNorm_pos C
    have hd := gramIdealNorm_pos D
    have hh := hfreq W hcompact hs hW U S hS σ C (E C D) (hE C hC D hD) (primaryGenerator D.val) v
      (P/gramIdealNorm C) (Y/(gramIdealNorm C*gramIdealNorm D)) (by positivity) (by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (show 0≤Q/Y^3 by positivity)
    apply hh'.trans_eq
    change (Q/Y^3)*(K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*
      gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*(M*gramIdealNorm C)^ε*(P/gramIdealNorm C)^(1/6:ℝ))=_
    calc
      _=(K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)*
        ((Q/Y^3)*gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*(M*gramIdealNorm C)^ε*(P/gramIdealNorm C)^(1/6:ℝ)) := by ring
      _=_ := by rw [supported_exceptional_prefactor C D M P Y Q ε hM hP hY];dsimp [B];ring
  calc
    _≤∑C∈F,∑D∈G,(Q/Y^3)*‖V C D‖ := normalized_double_sum_bound F G α V hα _ (by positivity)
    _≤∑C∈F,∑D∈G,B*(gramIdealNorm C^(-7/6+ε:ℝ)*gramIdealNorm D^(-2:ℝ)) :=
      Finset.sum_le_sum (fun C hC=>Finset.sum_le_sum (fun D hD=>ht C D hC hD))
    _=B*(∑C∈F,∑D∈G,gramIdealNorm C^(-7/6+ε:ℝ)*gramIdealNorm D^(-2:ℝ)) := by simp only [Finset.mul_sum]
    _≤B*L := mul_le_mul_of_nonneg_left (hideal F G) hB
    _=_ := by dsimp [B,M];ring

end SevenEighths.ProbeGramCommon
end

end OAI
