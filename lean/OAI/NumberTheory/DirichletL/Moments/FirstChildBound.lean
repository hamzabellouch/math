import OAI.NumberTheory.DirichletL.Moments.FirstWholeAssembly
import OAI.NumberTheory.DirichletL.Moments.ReflectedChild

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstChildBound
open CanonicalQuadraticSieve CenteredMomentSupportedCorrelation CenteredMomentFirstAssembly
open CenteredMomentFirstColumns CenteredMomentGaussEnergy CenteredMomentReflectedChild
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentSmooth RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

private theorem weighted_norm_sum {α : Type*} (S : Finset α) (a f : α → ℂ)
    (r : ℝ) (hr : 0 ≤ r) (B : α → ℝ)
    (hB : ∀ i ∈ S, r*‖f i‖ ≤ B i) :
    r*‖∑ i ∈ S, a i*f i‖ ≤ ∑ i ∈ S, ‖a i‖*B i := by
  calc
    _ ≤ r*∑ i ∈ S, ‖a i*f i‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hr
    _ = ∑ i ∈ S, ‖a i‖*(r*‖f i‖) := by simp only [Finset.mul_sum,norm_mul]; congr 1; funext i; ring
    _ ≤ _ := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hB i hi) (norm_nonneg _))

theorem finite_first_ray_divisor_bound (L : Finset (Ideal O))
    (F : Ideal O → RayCharacter → RayCharacter → ℂ)
    (r C : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C) (B₁ B₂ : Ideal O → ℝ)
    (hB₁ : ∀ I ∈ L, 0 ≤ B₁ I) (hB₂ : ∀ I ∈ L, 0 ≤ B₂ I)
    (hF : ∀ I ∈ L, ∀ χ ξ, r*‖F I χ ξ‖ ≤ C*(B₁ I*B₂ I)) :
    r*‖∑ I ∈ L, (UniqueFactorizationMonoid.moebius I : ℂ)*
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (firstPhaseTable) χ ξ * F I χ ξ‖ ≤
      (256*C)*∑ I ∈ L, ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖*(B₁ I*B₂ I) := by
  have he (I : Ideal O) (hI : I ∈ L) :
      r*‖∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff (firstPhaseTable) χ ξ*F I χ ξ‖ ≤ (256*C)*(B₁ I*B₂ I) := by
    calc
      _ ≤ ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          ‖pairCoeff (firstPhaseTable) χ ξ‖*(C*(B₁ I*B₂ I)) := by
        have h := weighted_norm_sum Finset.univ (fun _ : RayCharacter => (1 : ℂ))
          (fun χ => ∑ ξ : RayCharacter, pairCoeff (firstPhaseTable) χ ξ*F I χ ξ) r hr
          (fun χ => ∑ ξ : RayCharacter, ‖pairCoeff (firstPhaseTable) χ ξ‖*(C*(B₁ I*B₂ I)))
          (fun χ _ => weighted_norm_sum Finset.univ _ _ r hr _ (fun ξ _ => hF I hI χ ξ))
        simpa only [one_mul,norm_one] using h
      _ = (∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff (firstPhaseTable) χ ξ‖)*
          (C*(B₁ I*B₂ I)) := by simp only [Finset.sum_mul]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right (firstPhaseTable_mass)
          (mul_nonneg hC (mul_nonneg (hB₁ I hI) (hB₂ I hI)))
        convert h using 1 ; ring
  have h := weighted_norm_sum L (fun I => (UniqueFactorizationMonoid.moebius I : ℂ))
    (fun I => ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (firstPhaseTable) χ ξ*F I χ ξ)
    r hr (fun I => (256*C)*(B₁ I*B₂ I)) he
  convert h using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  ring

theorem first_row_children {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
    (a : α → O) (b : β → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (hb : ∀ j,Supported (Ideal.span {b j}))
    (hpa : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣a i-1)
    (hpb : ∀ j,ConcretePrimeRowBridge.goodLambda^2∣b j-1)
    (c : α → ℂ) (d : β → ℂ) (e r : O) (ρ : O → ℂ)
    (hρ : ∀ x y,ρ (x*y)=ρ x*ρ y) (q : O → ℂ) (K : O → α → β → ℂ) :
    (∑ z∈rows,q z*∑ i∈S,∑ j∈T,
      ((if IsCoprime (a i) (b j) then originalPhase e r ρ (a i) (b j) else 0)*(c i*star (d j)))*
        (gaussRow (a i) (ha i) z*star (gaussRow (b j) (hb j) (-z)))*K z i j)=
      ∑ L∈divisorPool T (fun j => Ideal.span {b j}),
        (UniqueFactorizationMonoid.moebius L:ℂ)*
          ∑ χ : RayCharacter,∑ ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
            ∑ z∈rows,(q z*ρ e)*∑ i∈S,∑ j∈T,
              ((divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*gaussRow (a i) (ha i) z)*
                star (divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) (ξ⁻¹) j*
                  gaussRow (b j) (hb j) (-z)))*K z i j := by
  simp_rw [finite_first_children S T a b ha hb hpa hpb c d e r ρ hρ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s:=rows)]
  apply Finset.sum_congr rfl
  intro L hL
  rw [Finset.sum_comm (s:=rows)]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.sum_comm (s:=rows)]
  apply Finset.sum_congr rfl
  intro ξ hξ
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem whole_kernel_first_child_bound (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i,0≤M i)
    (hV : ∀ i y,V i y≠0 → |y|≤M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ R : ℝ,0<R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (a : α → O) (b : β → O)
        (ha : ∀ i,Supported (Ideal.span {a i})) (hb : ∀ j,Supported (Ideal.span {b j})),
      (∀ i,ConcretePrimeRowBridge.goodLambda^2∣a i-1) →
      (∀ j,ConcretePrimeRowBridge.goodLambda^2∣b j-1) →
      ∀ (c : α → ℂ) (d : β → ℂ) (e r : O) (ρ : O → ℂ),
      (∀ x y,ρ (x*y)=ρ x*ρ y) → ‖ρ e‖≤1 →
      ∀ (q : O → ℂ) (u : α → ℝ) (v : β → ℝ) (ρ₀ x : O → ℝ),
      (∀ z∈rows,‖q z‖≤1) →
      (∀ z∈rows,‖V 0 (ρ₀ z)‖≤1) → (∀ z∈rows,‖V 1 (x z)‖≤1) →
      ∀ (U : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (∀ z∈rows,1≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      ∀ (B₁ B₂ : Ideal O → ℝ),
      (∀ L∈divisorPool T (fun j => Ideal.span {b j}),0≤B₁ L) →
      (∀ L∈divisorPool T (fun j => Ideal.span {b j}),0≤B₂ L) →
      (∀ L∈divisorPool T (fun j => Ideal.span {b j}),∀ χ : RayCharacter,∀ t : ℝ,
        (gaussEnergy S a ha (fun i =>
          divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*
            columnPhase (V 2) (u i) t) U K).re≤(B₁ L*(1+‖t‖)^J₁)^2) →
      (∀ L∈divisorPool T (fun j => Ideal.span {b j}),∀ ξ : RayCharacter,∀ t : ℝ,
        (gaussEnergy T b hb (fun j =>
          divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) ξ j*
            star (columnPhase (V 3) (v j) t)) U K).re≤(B₂ L*(1+‖t‖)^J₂)^2) →
      (1+R)^A*‖∑ z∈rows,q z*∑ i∈S,∑ j∈T,
        ((if IsCoprime (a i) (b j) then originalPhase e r ρ (a i) (b j) else 0)*(c i*star (d j)))*
          (gaussRow (a i) (ha i) z*star (gaussRow (b j) (hb j) (-z)))*
            wholeKernel W V R (ρ₀ z) (x z) (u i) (v j)‖≤
        C*∑ L∈divisorPool T (fun j => Ideal.span {b j}),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*(B₁ L*B₂ L) := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_reflected_gauss_child_bound W V M hM hV A J₁ J₂
  refine ⟨256*C,mul_nonneg (by norm_num) hC,?_⟩
  intro R hR α β rows S T a b ha hb hpa hpb c d e r ρ hρ hρe q u v ρ₀ x hq hV₀ hV₁ U K hK hU hmajor
    B₁ B₂ hB₁ hB₂ hleft hright
  rw [first_row_children rows S T a b ha hb hpa hpb c d e r ρ hρ]
  apply finite_first_ray_divisor_bound _ _ ((1+R)^A) C (by positivity) hC B₁ B₂ hB₁ hB₂
  intro L hL χ ξ
  exact hbound R hR rows S T a b ha hb
    (divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ)
    (divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) (ξ⁻¹))
    u v ρ₀ x (fun z => q z*ρ e)
    (fun z hz => by rw [norm_mul];exact (mul_le_of_le_one_left (norm_nonneg _) (hq z hz)).trans hρe)
    hV₀ hV₁ U K hK hU hmajor (B₁ L) (B₂ L) (hB₁ L hL) (hB₂ L hL)
    (hleft L hL χ) (hright L hL (ξ⁻¹))

end SevenEighths.CenteredMomentFirstChildBound

end

end OAI
