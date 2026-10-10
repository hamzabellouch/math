import OAI.NumberTheory.DirichletL.Moments.TerminalEnergy
import OAI.NumberTheory.DirichletL.Moments.AbsoluteEnergy

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentUncenteredTerminal
open HeckeFamily CenteredMomentAbsoluteEnergy CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

def uncenteredProfileCoefficient {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) : ℂ :=
  (∏ j,ν j (v (Sum.inl j))*Wslot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/P j))*
    (if IsCoprime (finiteTupleProduct v) R then 1 else 0)*
    (W₁ ((Ideal.absNorm (B₁*v (Sum.inr 0)):ℝ)/X₁)*
      W₂ ((Ideal.absNorm (B₂*v (Sum.inr 1)):ℝ)/X₂))*
    (if s∣finiteTupleProduct v then 1 else 0)

def comparisonScale (b : ℝ) : ℝ := 1/(2*max 1 b)

lemma comparisonScale_pos (b : ℝ) : 0<comparisonScale b := by
  have hb : 0<max 1 b := zero_lt_one.trans_le (le_max_left _ _)
  unfold comparisonScale
  positivity

lemma comparison_product (b T : ℝ) : comparisonScale b*(T/comparisonScale b)=T := by
  have hy := (comparisonScale_pos b).ne'
  field_simp

theorem comparison_first_zero (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (B I : Ideal O) (hB : B≠0) :
    W ((Ideal.absNorm (B*I):ℝ)/comparisonScale b)=0 := by
  by_contra h
  have ht := hs h
  by_cases hI : I=0
  · simp only [hI,mul_zero,map_zero,Nat.cast_zero,zero_div,Set.mem_Icc] at ht
    linarith [ht.1]
  have hn : 1≤(Ideal.absNorm (B*I):ℝ) :=
    QuadraticMainBoundary.norm_one_le (mul_ne_zero hB hI)
  have hmax : 1≤max 1 b := le_max_left _ _
  have hb : b≤max 1 b := le_max_right _ _
  have harg : (Ideal.absNorm (B*I):ℝ)/comparisonScale b=
      (Ideal.absNorm (B*I):ℝ)*(2*max 1 b) := by
    simp [comparisonScale,div_eq_mul_inv]
  rw [harg] at ht
  have hupper := ht.2
  nlinarith

theorem profileCoefficient_eq_uncentered {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ : ℝ) (ha₁ : 0<a₁)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁)
    (X₁ X₂ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (hB₁ : B₁≠0) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ (comparisonScale b₁) Y₂ B₁ B₂ s=
      uncenteredProfileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ B₁ B₂ s := by
  funext v
  simp only [profileCoefficient,idealRectangle,
    comparison_first_zero W₁ a₁ b₁ ha₁ hs₁ B₁ (v (Sum.inr 0)) hB₁,
    zero_mul,sub_zero,uncenteredProfileCoefficient]

theorem smooth_subset_uncentered_absolute_energy {α : Type*} (F : Finset α)
    (Wslot : α → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (a b : α → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈F,0<a j) (hb : ∀ j∈F,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈F,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ,0<C ∧ ∀ J : Finset α,J⊆F →
      ∀ (η : Character) (m A : O) (t : ℝ) (R : Ideal O) (ν : α → Ideal O → ℂ),
      (∀ j∈J,∀ I,‖ν j I‖≤1) →
      ∀ (P : α → ℝ) (X₁ X₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J,0<P j) → 0<X₁ → 0<X₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → ∀ (S : Finset (Tuple J)) (K : ℝ),0<K →
      let H := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j)
      let E := finiteHeckeEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (uncenteredProfileCoefficient R (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ B₁ B₂ s)) Φ K
      ‖E‖≤C*max 1 K*H^2 ∧ ‖E‖/H≤C*max 1 K*H := by
  obtain ⟨C,hC,hbound⟩ := smooth_subset_source_absolute_energy F Wslot W₁ W₂ Φ a b a₁ b₁ a₂ b₂
    ha hb ha₁ hb₁ ha₂ hb₂ hsSlot hs₁ hs₂ hWslot hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro J hJ η m A t R ν hν P X₁ X₂ T B₁ B₂ s hP hX₁ hX₂ hB₁ hB₂ hX S K hK
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have he := hbound J hJ η m A t R ν hν P X₁ X₂
    (comparisonScale b₁) (T/comparisonScale b₁) T B₁ B₂ s
    hP hX₁ hX₂ (comparisonScale_pos b₁) (div_pos hT (comparisonScale_pos b₁))
    hB₁ hB₂ hX (comparison_product b₁ T) S K hK
  rw [profileCoefficient_eq_uncentered R (fun j : J => ν j.val)
    (fun j : J => Wslot j.val) (fun j : J => P j.val) W₁ W₂ a₁ b₁ ha₁ hs₁
    X₁ X₂ (T/comparisonScale b₁) B₁ B₂ s hB₁] at he
  exact he

theorem actual_small_width_uncentered_energy {α : Type*} (F : Finset α)
    (Wslot : α → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (a b : α → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈F,0<a j) (hb : ∀ j∈F,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈F,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ,0<C ∧ ∀ J : Finset α,J⊆F →
      ∀ (η : Character) (m A : O) (t : ℝ) (R : Ideal O) (ν : α → Ideal O → ℂ),
      (∀ j∈J,∀ I,‖ν j I‖≤1) →
      ∀ (P : α → ℝ) (X₁ X₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J,0<P j) → 0<X₁ → 0<X₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → ∀ (S : Finset (Tuple J)) (Z mExp q M AExp ρ δ : ℝ),1≤Z →
      0≤mExp → 0≤q → mExp+q=M → M≤ρ → AExp≤M+δ →
      let H := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j)
      H=Z^AExp →
      ‖finiteHeckeEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (uncenteredProfileCoefficient R (fun j : J=>ν j.val)
          (fun j : J=>Wslot j.val) (fun j : J=>P j.val)
          W₁ W₂ X₁ X₂ B₁ B₂ s)) Φ (Z^mExp)‖/H≤C*Z^(M+ρ+δ) := by
  obtain ⟨C,hC,hbound⟩ := CenteredMomentTerminalEnergy.actual_small_width_source_energy
    F Wslot W₁ W₂ Φ a b a₁ b₁ a₂ b₂
    ha hb ha₁ hb₁ ha₂ hb₂ hsSlot hs₁ hs₂ hWslot hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro J hJ η m A t R ν hν P X₁ X₂ T B₁ B₂ s
    hP hX₁ hX₂ hB₁ hB₂ hX S Z mExp q M AExp ρ δ hZ hm hq hM hsmall hA H hscale
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have he := hbound J hJ η m A t R ν hν P X₁ X₂
    (comparisonScale b₁) (T/comparisonScale b₁) T B₁ B₂ s
    hP hX₁ hX₂ (comparisonScale_pos b₁) (div_pos hT (comparisonScale_pos b₁))
    hB₁ hB₂ hX (comparison_product b₁ T) S Z mExp q M AExp ρ δ
    hZ hm hq hM hsmall hA hscale
  rw [profileCoefficient_eq_uncentered R (fun j : J => ν j.val)
    (fun j : J => Wslot j.val) (fun j : J => P j.val) W₁ W₂ a₁ b₁ ha₁ hs₁
    X₁ X₂ (T/comparisonScale b₁) B₁ B₂ s hB₁] at he
  exact he

end SevenEighths.CenteredMomentUncenteredTerminal

end

end OAI
