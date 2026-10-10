import OAI.RepresentationTheory.RestrictedTilting.Basic
import OAI.RepresentationTheory.RestrictedTilting.LowDegreeTrace
import OAI.RepresentationTheory.RestrictedTilting.SmallGroupTrace
import OAI.RepresentationTheory.RestrictedTilting.TorusWeightProjection
import OAI.RepresentationTheory.RestrictedTilting.RationalHomWeights

namespace OAI

namespace FiberFunctorProof
open scoped BigOperators
open CategoryTheory Representation
universe u v
variable {k : Type u} [Field k] [Infinite k]
variable {E : Type v} [AddGroup E] [Fintype E] [DecidableEq E]
variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]

 

theorem bounded_rational_norm_zero (ρ : Representation k (SL2 k) V)
    (hρ : IsRational k ρ) (N : ℕ) (hN : HasWeightsBetween ρ (-(N : ℤ)) N)
    (l : E →+ k) (hl : Function.Injective l) (hE : N < Fintype.card E - 1) (v : V) :
    ∑ e : E, ρ (unipotent k (l e)) v = 0 := by
  classical
  have heigen (n : ℤ) (w : V)
      (hw : ∀ a, ρ (diagonalTorus k a) w = integerCharacter k n a • w) :
      ∑ e : E, ρ (unipotent k (l e)) w = 0 := by
    by_cases hz : w = 0
    · simp [hz]
    have hn : -(N : ℤ) ≤ n := by
      by_contra h
      exact hz (hN n w (Or.inl (by omega)) hw)
    obtain ⟨c, hc⟩ := rational_unipotent_expansion k ρ hρ w
    have hcz (i : ℕ) (hi : N < i) : c i = 0 :=
      hN (n + 2 * i) (c i) (Or.inr (by omega))
        (unipotent_coefficient_weight k ρ w n hw c hc i)
    simp_rw [hc, Finsupp.sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hiN : i ≤ N
    · rw [← Finset.sum_smul, finite_additive_power_sum_zero l hl i (lt_of_le_of_lt hiN hE),
        zero_smul]
    · simp [hcz i (by omega)]
  obtain ⟨c, hc⟩ := rational_torus_integerExpansions k ρ hρ v
  have hs : v = ∑ n ∈ c.support, c n := by
    simpa [Finsupp.sum, integerCharacter] using hc 1
  rw [hs]
  simp_rw [map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro n hn
  exact heigen n (c n) (integer_coefficient_eigen k ρ v c hc n)

 

theorem bounded_norm_zero_weight (ρ : Representation k (SL2 k) V)
    (hρ : IsRational k ρ) (N : ℕ) (hN : HasWeightsBetween ρ (-(N : ℤ)) N)
    (l : E →+ k) (hl : Function.Injective l)
    (hE : N < 2 * (Fintype.card E - 1)) (v : V) :
    torusWeightProjection ρ hρ 0 (∑ e : E, ρ (unipotent k (l e)) v) = 0 := by
  classical
  have heigen (n : ℤ) (w : V)
      (hw : ∀ a, ρ (diagonalTorus k a) w = integerCharacter k n a • w) :
      torusWeightProjection ρ hρ 0 (∑ e : E, ρ (unipotent k (l e)) w) = 0 := by
    by_cases hz : w = 0
    · simp [hz]
    have hn : -(N : ℤ) ≤ n := by
      by_contra h
      exact hz (hN n w (Or.inl (by omega)) hw)
    obtain ⟨c, hc⟩ := rational_unipotent_expansion k ρ hρ w
    simp_rw [hc, Finsupp.sum, map_sum, map_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hiE : i < Fintype.card E - 1
    · rw [← Finset.sum_smul, finite_additive_power_sum_zero l hl i hiE, zero_smul]
    · have hni : n + 2 * (i : ℤ) ≠ 0 := by omega
      rw [torusWeightProjection_eigen ρ hρ 0 (n+2*i) (c i)
        (unipotent_coefficient_weight k ρ w n hw c hc i), ite_eq_right hni]
      simp
  obtain ⟨c, hc⟩ := rational_torus_integerExpansions k ρ hρ v
  have hs : v = ∑ n ∈ c.support, c n := by
    simpa [Finsupp.sum, integerCharacter] using hc 1
  rw [hs]
  simp_rw [map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro n hn
  have h := heigen n (c n) (integer_coefficient_eigen k ρ v c hc n)
  simpa only [map_sum] using h

 
theorem bounded_fixed_norm_zero (ρ : Representation k (SL2 k) V)
    (hρ : IsRational k ρ) (N : ℕ) (hN : HasWeightsBetween ρ (-(N : ℤ)) N)
    (l : E →+ k) (hl : Function.Injective l)
    (hE : N < 2 * (Fintype.card E - 1)) (v : V)
    (hv : ∀ a, ρ (diagonalTorus k a) (∑ e : E, ρ (unipotent k (l e)) v) =
      ∑ e : E, ρ (unipotent k (l e)) v) :
    ∑ e : E, ρ (unipotent k (l e)) v = 0 := by
  rw [← torusWeightProjection_zero_fixed ρ hρ _ hv]
  exact bounded_norm_zero_weight ρ hρ N hN l hl hE v

 

theorem low_weight_projective_factor_zero (p r : ℕ) [NeZero p]
    (l : (Fin r → ZMod p) →+ k) (hl : Function.Injective l)
    (A B : FDRep k (SL2 k)) (hA : IsRational k A.ρ) (hB : IsRational k B.ρ)
    (a b : ℕ) (ha : HasWeightsBetween A.ρ (-(a : ℤ)) a)
    (hb : HasWeightsBetween B.ρ (-(b : ℤ)) b) (hab : a+b < 2*(p^r-1))
    (f : A ⟶ B) (hf : FactorsThroughProjective ((restrictElementary k p r l).map f)) :
    f = 0 := by
  classical
  let R := restrictElementary k p r l
  obtain ⟨t, ht⟩ := SmallGroupTrace.relativeTrace_of_factors (R.obj A) (R.obj B) (R.map f) hf
  let ρ := Representation.linHom A.ρ B.ρ
  have he : (∑ e : Fin r → ZMod p, ρ (unipotent k (l e)) t) = f.hom.hom.hom := by
    change relativeTrace (R.obj A).ρ (R.obj B).ρ t = f.hom.hom.hom at ht
    rw [← ht]
    simp only [relativeTrace, Representation.norm, LinearMap.sum_apply]
    change _ = ∑ e : Multiplicative (Fin r → ZMod p),
      (Representation.linHom (R.obj A).ρ (R.obj B).ρ) e t
    rw [← Equiv.sum_comp Multiplicative.ofAdd]
    apply Finset.sum_congr rfl
    intro e he
    change B.ρ (unipotent k (l e)) ∘ₗ t ∘ₗ A.ρ (unipotent k (l e))⁻¹ =
      B.ρ (unipotent k (l e)) ∘ₗ t ∘ₗ A.ρ (unipotent k (l (-e)))
    congr 2
    have h := map_inv (elementaryEmbedding k p r l) (Multiplicative.ofAdd e)
    exact congrArg A.ρ h.symm
  have hr : IsRational k ρ := IsRational.linHom A.ρ B.ρ hA hB
  have hw : HasWeightsBetween ρ (-((a+b : ℕ) : ℤ)) (a+b) := by
    simpa only [Nat.cast_add] using hasWeightsBetween_linHom A.ρ B.ρ hA a b ha hb
  have hz := bounded_fixed_norm_zero ρ hr (a+b) hw l hl
    (by simpa [Fintype.card_fun, ZMod.card] using hab) t (fun u => by
      rw [he]
      change B.ρ (diagonalTorus k u) ∘ₗ f.hom.hom.hom ∘ₗ A.ρ (diagonalTorus k u)⁻¹ =
        f.hom.hom.hom
      ext x
      change B.ρ (diagonalTorus k u) (f.hom.hom.hom (A.ρ (diagonalTorus k u)⁻¹ x)) = _
      rw [← fdrepLinear_comm k f]
      simp)
  rw [he] at hz
  apply Action.Hom.ext
  apply InducedCategory.hom_ext
  apply ModuleCat.hom_ext
  exact hz
end FiberFunctorProof

end OAI
