import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCapped

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
theorem capped_slots_source_control
    (a b ε B : ℝ) (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ, ∃ R : Finset (ℕ×ℕ), (0,0)∈R ∧
      ∀Q : Ideal O,Q≠0 → ∃C : ℝ,0<C ∧
      ∀W₁ W₂ : 𝓢(ℝ,ℂ), Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀(ι : Type*) [Fintype ι],∀Z : ℝ,1≤Z →
      ∀(η : Character)(m A z : O),m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ)≤Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
      ∀(S : ι→Finset (Ideal O))(β : ι→Ideal O→ℂ)(P b M : ι→ℝ),
      (∀i,0<P i) → (∀i,0≤b i) → (∀i,0≤M i) →
      (∀i,∀I∈S i,‖β i I‖≤M i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) →
      ∀t X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      ‖centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖≤
        C*(sourceControl R W₁*sourceControl R W₂)*Z^ε*(1+‖t‖)^J*(∏i,128*b i*M i)*(Real.sqrt (T*∏i,P i)/max 1 L) := by
  obtain ⟨J,R,hR,hJ⟩ := capped_rectangle_source_control a b ε B ha hb hε hB
  refine ⟨J,R,hR,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩ := hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ ι _ Z hZ η m A z hm hA hz hml hm2 hc he S β P b M hP hb hM hβ hN
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hR₁ := sourceControl_nonneg R W₁
  have hR₂ := sourceControl_nonneg R W₂
  have hT : 0<T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hslots (i : ι) : ‖rowSlot η m A z (S i) (β i) t‖≤(128*b i*M i)*P i := by
    convert rowSlot_bound η m A z (S i) (β i) t (b i*P i) (M i)
      (mul_nonneg (hb i) (hP i).le) (hM i) (hβ i) (hN i) using 1; ring
  exact whole_product_normalization _ (fun i=>rowSlot η m A z (S i) (β i) t)
    (fun i=>128*b i*M i) P (C*(sourceControl R W₁*sourceControl R W₂)*Z^ε*(1+‖t‖)^J) T (max 1 L) (by positivity) hT
    (zero_lt_one.trans_le (le_max_left _ _))
    (fun i=>mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hM i)) hP hslots
    (hbound W₁ W₂ hs₁ hs₂ Z hZ η m A z hm hA hz hml hm2 hc he t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY)

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
