import OAI.NumberTheory.DirichletL.Detector.GramWeightedFrequency
import OAI.NumberTheory.DirichletL.Detector.GramCanonicalTrivial
import OAI.NumberTheory.DirichletL.Detector.GramFrequencySummation

namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma gramFrequency_image_sum (E : Finset GramFrequency) (f : O→ℝ) :
    (∑k∈E.image Subtype.val,f k)=∑k∈E,f k.val :=
  Finset.sum_image (fun _ _ _ _ h=>Subtype.val_injective h)

theorem canonical_nonexceptional_frequency_sum (A : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃(J : ℕ)(H₀ : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧ ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(E : Finset GramFrequency),
      (∀k∈E,¬ExceptionalFrequency S hS C k)→
      ∀(d : O)(U : SchwartzMap ℝ ℂ)(v H N : ℝ),0<H→0<N→
        ‖∑k∈E,canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*
          (Ideal.absNorm C.val:ℝ)*N^2*H*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*H/N)^A) := by
  obtain ⟨J,H₀,hblock⟩ := canonical_nonexceptional_weighted A hA a₀ b₀ ha₀ hab
  obtain ⟨L,hL,hcount⟩ := ProbeGramFrequencySummation.frequency_weighted_sum
  refine ⟨J,H₀,?_⟩
  intro W hs hW
  obtain ⟨K,hK,hblock⟩ := hblock W hs hW
  refine ⟨K*L,mul_pos hK hL,?_⟩
  intro S hS σ C E hE d U v H N hH hN
  have hc := hcount (E.image Subtype.val) H hH (by
    intro k hk;obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk;exact j.property)
  rw [gramFrequency_image_sum] at hc
  let V := K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Ideal.absNorm C.val:ℝ)*N^2*
    min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*H/N)^A)
  have hV : 0≤V := by dsimp [V];positivity
  calc
    _≤∑k∈E,‖canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖ := norm_sum_le _ _
    _≤∑k∈E,V*(1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ) :=
      Finset.sum_le_sum (fun k hk=>hblock S hS σ C k (hE k hk) d U v H N hH hN)
    _=V*(∑k∈E,(1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ)) := (Finset.mul_sum ..).symm
    _≤V*(L*H) := mul_le_mul_of_nonneg_left hc hV
    _=_ := by dsimp [V];ring

theorem canonical_exceptional_frequency_sum (a b M ε : ℝ) (ha : 0<a) (hb : 0≤b)
    (hM : 0≤M) (hε : 0<ε) :
    ∃H₀ : Finset (ℕ×ℕ),∃K : ℝ,0<K ∧
      ∀(W : ℝ→ℂ)(_hcompact : HasCompactSupport W),
      (Function.support W⊆Set.Icc a b)→(∀x,‖W x‖≤M)→
      ∀(U : SchwartzMap ℝ ℂ)(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(E : Finset GramFrequency),
      (∀k∈E,ExceptionalFrequency S hS C k)→
      ∀(d : O)(v H N : ℝ),0<H→0<N→
        ‖∑k∈E,canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Ideal.absNorm C.val:ℝ)*N^2*
          ((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val)^ε*H^(1/6:ℝ) := by
  obtain ⟨H₀,K,hK,hblock⟩ := canonical_trivial_block a b M ha hb hM 2
  obtain ⟨L,hL,hcount⟩ := ProbeGramFrequencySummation.exceptional_frequency_weighted_sum ε hε
  refine ⟨H₀,K*L,mul_pos hK hL,?_⟩
  intro W hcompact hs hW U S hS σ C E hE d v H N hH hN
  have hc := hcount (exceptionalModulus S hS C) (exceptionalModulus_nonzero S hS C)
    (E.image Subtype.val) H hH
    (by intro k hk;obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk;exact j.property)
    (by intro k hk;obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk;exact hE j hj)
  rw [gramFrequency_image_sum,exceptionalModulus_norm,Nat.cast_mul] at hc
  let V := K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Ideal.absNorm C.val:ℝ)*N^2
  have hV : 0≤V := by dsimp [V];positivity
  have hp (k : GramFrequency) :
      ‖canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖≤
        V*(1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ) := by
    have ht : 0≤(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H := by positivity
    have hb := hblock W hcompact hs hW U S hS σ C k d N _ v hN ht
    have hpos : 0<1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H := by positivity
    rw [Real.rpow_neg hpos.le,Real.rpow_two,←div_eq_mul_inv]
    apply (le_div_iff₀ (sq_pos_of_pos hpos)).mpr
    convert hb using 1 ; dsimp [V] ; ring
  calc
    _≤∑k∈E,‖canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖ := norm_sum_le _ _
    _≤∑k∈E,V*(1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ) := Finset.sum_le_sum (fun k _=>hp k)
    _=V*(∑k∈E,(1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ)) := (Finset.mul_sum ..).symm
    _≤V*(L*((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val)^ε*H^(1/6:ℝ)) := mul_le_mul_of_nonneg_left hc hV
    _=_ := by dsimp [V];ring

end SevenEighths.ProbeGramCommon
end

end OAI
