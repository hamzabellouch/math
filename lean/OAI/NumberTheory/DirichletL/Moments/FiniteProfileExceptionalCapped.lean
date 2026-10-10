import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalRow

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeVolume
open CenteredMomentHeckeTwist CenteredMomentExceptionalCappedAmplitude
local notation "O" => HeckeFamily.O
theorem capped_rectangle_source_control
    (a b ε B : ℝ) (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hB : 0≤B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), (0,0)∈S ∧
      ∀ Q : Ideal O, Q≠0 → ∃ C : ℝ, 0<C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀ Z : ℝ, 1≤Z → ∀ (η : Character) (m A₀ z : O),
      m ≠ 0 → A₀ ≠ 0 → z ≠ 0 →
      (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (HeckeRowClosure.rowConductorBound η m 1 (A₀*z):ℝ) ≤ Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A₀ z →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹ *
        (rowTwistedSum η m A₀ z W₁ t X₁*rowTwistedSum η m A₀ z W₂ t X₂-
         rowTwistedSum η m A₀ z W₁ t Y₁*rowTwistedSum η m A₀ z W₂ t Y₂)‖ ≤
        C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*(Real.sqrt T/max 1 L) := by
  obtain ⟨J,S,hS,hJ⟩ := row_rectangle_source_control a b ε B ha hb hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hcancel⟩ := hJ Q hQ
  let D : ℝ := 2*(128*b)*(128*b)
  have hD : 0≤D := by dsimp [D]; positivity
  refine ⟨C+D,by positivity,?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ η m A z hm hA hz hml hm2 hcond hex
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  let P₁ := sourceControl S W₁
  let P₂ := sourceControl S W₂
  have hP₁ : 0≤P₁ := sourceControl_nonneg S W₁
  have hP₂ : 0≤P₂ := sourceControl_nonneg S W₂
  have hw₁ (x:ℝ) : ‖W₁ x‖≤P₁ :=
    (SchwartzMap.norm_le_seminorm ℝ W₁ x).trans
      (Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ)
        (s := S) (x := W₁) (i := (0, 0)) hS)
  have hw₂ (x:ℝ) : ‖W₂ x‖≤P₂ :=
    (SchwartzMap.norm_le_seminorm ℝ W₂ x).trans
      (Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ)
        (s := S) (x := W₂) (i := (0, 0)) hS)
  by_cases hlarge : 1≤L
  · rw [max_eq_right hlarge]
    apply (hcancel W₁ W₂ hs₁ hs₂ Z hZ η m A z hm hA hz hml hm2 hcond hex
      t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY).trans
    gcongr
    exact le_add_of_nonneg_right hD
  · rw [max_eq_left (le_of_not_ge hlarge),div_one]
    have habs := normalized_rectangle_absolute η m A z W₁ W₂ b b P₁ P₂ hb hb hP₁ hP₂
      (fun _ hx=>(hs₁ hx).2) (fun _ hx=>(hs₂ hx).2) hw₁ hw₂
      t X₁ X₂ Y₁ Y₂ T (hL.trans_le hX₁) (hL.trans_le hX₂)
      (hL.trans_le hY₁) (hL.trans_le hY₂) hpX hpY
    have hc : D ≤ (C+D)*Z^ε*(1+‖t‖)^J := by
      calc
        _ ≤ C+D := le_add_of_nonneg_left hC.le
        _ ≤ (C+D)*Z^ε := le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hZ hε.le)
        _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith [norm_nonneg t]))
    apply habs.trans
    calc
      _ = D*(P₁*P₂)*Real.sqrt T := by dsimp [D]; ring
      _ ≤ ((C+D)*Z^ε*(1+‖t‖)^J)*(P₁*P₂)*Real.sqrt T := by
        gcongr
      _ = _ := by dsimp [P₁,P₂]; ring
end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
