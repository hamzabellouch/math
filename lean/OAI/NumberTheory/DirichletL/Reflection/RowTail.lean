import OAI.NumberTheory.DirichletL.Reflection.WholeRow
import OAI.NumberTheory.DirichletL.Reflection.FamilyTail

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v
variable {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma finite_weighted_truncation {α β : Type*} [Fintype α]
    (f : α→β→ℂ) (w : α→ℂ) (J : Finset β)
    (hf : ∀ p, Summable (f p)) :
    (∑' i,∑ p,w p*f p i)-(∑ i∈J,∑ p,w p*f p i)=
      ∑ p,w p*((∑' i,f p i)-∑ i∈J,f p i) := by
  rw [Summable.tsum_finsetSum (fun p _ => (hf p).mul_left (w p)),Finset.sum_comm]
  simp only [tsum_mul_left,←Finset.mul_sum,mul_sub,Finset.sum_sub_distrib]

lemma finite_weighted_truncation_norm {α β : Type*} [Fintype α]
    (f : α→β→ℂ) (w : α→ℂ) (J : Finset β) (E : ℝ)
    (hf : ∀ p, Summable (f p)) (hw : ∀ p,‖w p‖≤1)
    (he : ∀ p, ‖(∑' i,f p i)-∑ i∈J,f p i‖≤E) :
    ‖(∑' i,∑ p,w p*f p i)-(∑ i∈J,∑ p,w p*f p i)‖≤Fintype.card α*E := by
  rw [finite_weighted_truncation f w J hf]
  calc
    _ ≤ ∑ p,‖w p*((∑' i,f p i)-∑ i∈J,f p i)‖ := norm_sum_le _ _
    _ ≤ ∑ _p : α,E := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hw p) (norm_nonneg _)).trans (by simpa using he p)
    _ = _ := by simp

theorem original_family_row_tail (lo hi : ℝ) (hlo : 0<lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0<C ∧
    ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ]
      (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
      (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
      (D : ∀ P : Pset, IsCoprime K P.val →
        ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ P∈Pset, ∀ i, ringChar (Eis⧸(F.reflected K hK (S P)).ideal i)≠2) →
      (∀ i,jF i<6) → (∀ P∈Pset,(∏ j,(S P).ideal j)=P) →
    ∀ (u : Eisˣ) (θ X T QK QP : ℝ) (r aw : Ideal Eis→ℂ),
      0<X → 0<T → 0<QK → 0<QP →
      (Ideal.absNorm K:ℝ)≤QK → (∀ P∈Pset,(Ideal.absNorm P:ℝ)≤QP) →
      ‖r K‖≤1 → (∀ P∈Pset,‖aw P‖≤1) →
      ‖(∑' i : ℕ×ℕ×ℕ,literalDyadicRow F K hK S jF Pset D s hc u i W θ X r aw)-
        ∑ i∈retainedDyads (familyRawScale F s X QK QP) (16*T),
          literalDyadicRow F K hK S jF Pset D s hc u i W θ X r aw‖≤
        Pset.card*(C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
          T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹) := by
  obtain ⟨degree,C,hC,hbound⟩ := original_family_dyadic_tail
    (N:=N) (a:=a) (c:=c) (mode:=mode) lo hi hlo A W hWs hW
  refine ⟨degree,C,hC,?_⟩
  intro φ σ _ _ F K hK S jF Pset D s hc hN hbase hchar hj hprod u θ X T QK QP r aw hX hT hQK hQP hKr hPr hr haw
  let L := {P : Pset // IsCoprime K P.val}
  let block := fun (P : L) i => literalDyadicBlock (F.reflected K hK (S P.val.val))
    (D P.val P.property) s hc (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ)
    (CompletedHeight.normTwistedSource W θ) X u i
  let J := retainedDyads (familyRawScale F s X QK QP) (16*T)
  have htw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) := by
    have he : (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ:ℝ→ℂ)=
        CompletedHeight.normTwistedSource W θ := by
      funext x
      exact CompletedHeight.uniformTwistedSchwartz_apply W lo hi hlo hWs hW θ x
    rw [←he]
    exact (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ).smooth ⊤
  have hj' : ∀ i : φ ⊕ (PrimeIndex K ⊕ σ), reflectedExponent jF i<6 := by
    intro i
    rcases i with f | k | p
    · exact hj f
    · norm_num [reflectedExponent]
    · norm_num [reflectedExponent]
  have hs (P : L) : Summable (block P) :=
    literalDyadicBlock_summable (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) (reflectedExponent jF) hj' (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) lo hi hlo
      ((CompletedHeight.normTwistedSource_support W θ).trans hWs) htw X hX u
  have he (P : L) : ‖(∑' i,block P i)-∑ i∈J,block P i‖≤
      C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
        T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹ := by
    rw [tsum_sub_finset_eq_tail (block P) (hs P) J]
    have hh := hbound F K hK (S P.val.val) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) jF hj u θ X T QK QP hX hT hQK hQP hKr
      (by rw [hprod P.val.val P.val.property]; exact hPr P.val.val P.val.property)
    apply le_trans ?_ hh
    apply le_of_eq
    congr 1
    apply tsum_congr
    intro i
    by_cases hi : i∈J <;> simp [J] at hi ⊢ <;> simp [hi,block]
  have hw (P : L) : ‖r K*aw P.val.val‖≤1 := by
    rw [norm_mul]
    exact (mul_le_mul hr (haw P.val.val P.val.property) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hh := finite_weighted_truncation_norm block (fun P : L => r K*aw P.val.val) J _ hs hw he
  change ‖(∑' i,∑ P : L,r K*aw P.val.val*block P i)-∑ i∈J,∑ P : L,r K*aw P.val.val*block P i‖≤_
  apply hh.trans
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast (Fintype.card_subtype_le (fun P : Pset => IsCoprime K P.val)).trans_eq (Fintype.card_coe Pset)
  · positivity
end
end SevenEighths.InverseReflectedPhase

end OAI
