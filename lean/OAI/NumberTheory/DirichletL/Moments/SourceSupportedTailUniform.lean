import OAI.NumberTheory.DirichletL.Moments.SourceProfileMassUniform
import OAI.NumberTheory.DirichletL.Moments.SupportedTailAggregate
import OAI.NumberTheory.DirichletL.Moments.SourceZeroEnergy

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSourceSupportedTailUniform
open ActualEisensteinCubic HeckeFamily CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentFirstTailAggregate CenteredMomentFirstScale
open CenteredMomentSupportedTailAggregate CenteredMomentSourceZeroEnergy CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceRow CenteredMomentFirstDiscardedEnergy CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

theorem source_first_discarded_energy_bound {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ)
    (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j,0<a j) (hb : ∀ j,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hWslot : ∀ j,ContDiff ℝ ∞ (Wslot j))
    (Adec : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (sΦ : Finset (ℕ × ℕ)) (C : ℝ),0<C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁ : ℝ→ℂ)⊆Set.Icc a₁ b₁ →
      Function.support (W₂ : ℝ→ℂ)⊆Set.Icc a₂ b₂ →
      ∀ (η : Character) (m A : O) (t : ℝ) (R : Ideal O) (ν : ι → Ideal O → ℂ),
      (∀ j I,‖ν j I‖≤1) → ∀ (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple ι)) (Φ : 𝓢(ℝ,ℂ)) (K X HN Tsec Z Csec ξ : ℝ),
      0<K → 0<X → 1<Z → 1≤Csec →
      ((∏ j,b j)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)≤Real.exp HN*X) →
      (∀ I : supportedColumns (finiteColumns S),∀ J : supportedColumns (finiteColumns S),
        finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I≠0 →
        finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) J≠0 →
        ∀ E∈inactiveSubsets I J,firstNominalScale I J (∏ P∈E,P.val) K X≤Tsec) →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖discardedEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s))
        Φ K Tsec Z ξ‖ ≤
      ((T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j))^2*
        (Real.exp HN*X)^ε*K*(C*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*
          sΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨D,hD,hmass⟩ := CenteredMomentSourceProfileMassUniform.profile_mass_uniform
    Wslot a b a₁ b₁ a₂ b₂ ha hb ha₁ hb₁ ha₂ hb₂ hsSlot hWslot
  obtain ⟨sΦ,C,hC,htail⟩ := first_discarded_energy_bound Adec ε hε
  refine ⟨sΦ,D^2*C,mul_pos (sq_pos_of_pos hD) hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY
    S Φ K X HN Tsec Z Csec ξ hK hXX hZ hCs hN hsec hthreshold
  let Dprofile := D*SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂
  let β := profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hm := (finiteColumnCoefficient_mass S β).trans
    (hmass W₁ W₂ hs₁ hs₂ R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S)
  have hz (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
      (hs : Function.support W⊆Set.Icc a b) : W 0=0 := by
    by_contra hn
    exact (not_le_of_gt ha) (hs hn).1
  have hNN (I : Ideal O) (_hI : I∈finiteColumns S)
      (hn : finiteColumnCoefficient S β I≠0) : (Ideal.absNorm I:ℝ)≤Real.exp HN*X := by
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    have hh := profileCoefficient_product_bound R ν Wslot P b W₁ W₂ b₁ b₂
      X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY
      (fun j=>hz (Wslot j) (a j) (b j) (ha j) (hsSlot j))
      (hz W₁ a₁ b₁ ha₁ hs₁) (hz W₂ a₂ b₂ ha₂ hs₂)
      (fun j x hx=>(hsSlot j hx).2) (fun x hx=>(hs₁ hx).2)
      (fun x hx=>(hs₂ hx).2) v hv0
    rw [←he]
    exact hh.2.trans hN
  have ht := htail η m A t (finiteColumns S) (finiteColumnCoefficient S β) Φ K X HN Tsec Z Csec ξ
    hK hXX hZ hCs hNN hsec hthreshold
  apply ht.trans
  have hsq := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hm 2
  calc
    _ ≤ (Dprofile*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j))^2*
        (Real.exp HN*X)^ε*K*(C*sΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hK.le
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg (by positivity) _)
    _ = _ := by dsimp [Dprofile]; ring

theorem source_second_discarded_energy_bound {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ)
    (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j,0<a j) (hb : ∀ j,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hWslot : ∀ j,ContDiff ℝ ∞ (Wslot j))
    (Adec : ℕ) :
    ∃ (sΦ : Finset (ℕ × ℕ)) (C : ℝ),0<C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁ : ℝ→ℂ)⊆Set.Icc a₁ b₁ →
      Function.support (W₂ : ℝ→ℂ)⊆Set.Icc a₂ b₂ →
      ∀ (η : Character) (t : ℝ) (R : Ideal O) (ν : ι → Ideal O → ℂ),
      (∀ j I,‖ν j I‖≤1) → ∀ (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple ι)) (Φ : 𝓢(ℝ,ℂ)) (K X HN Tsec Z Csec ξ : ℝ),
      0<K → 0<X → 1<Z → 1≤Csec →
      ((∏ j,b j)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)≤Real.exp HN*X) →
      X^2/K≤Tsec →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖secondDiscardedEnergy η t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s))
        Φ K Tsec Z ξ‖ ≤
      ((T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j))^2*
        K*(Real.exp HN*X)^2*(C*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*
          sΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨D,hD,hmass⟩ := CenteredMomentSourceProfileMassUniform.profile_mass_uniform
    Wslot a b a₁ b₁ a₂ b₂ ha hb ha₁ hb₁ ha₂ hb₂ hsSlot hWslot
  obtain ⟨sΦ,C,hC,htail⟩ := second_discarded_energy_bound Adec
  refine ⟨sΦ,D^2*C,mul_pos (sq_pos_of_pos hD) hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ η t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY
    S Φ K X HN Tsec Z Csec ξ hK hXX hZ hCs hN hsec hthreshold
  let Dprofile := D*SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂
  let β := profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hm := (finiteColumnCoefficient_mass S β).trans
    (hmass W₁ W₂ hs₁ hs₂ R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S)
  have hz (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
      (hs : Function.support W⊆Set.Icc a b) : W 0=0 := by
    by_contra hn
    exact (not_le_of_gt ha) (hs hn).1
  have hNN (I : Ideal O) (_hI : I∈finiteColumns S)
      (hn : finiteColumnCoefficient S β I≠0) : (Ideal.absNorm I:ℝ)≤Real.exp HN*X := by
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    have hh := profileCoefficient_product_bound R ν Wslot P b W₁ W₂ b₁ b₂
      X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY
      (fun j=>hz (Wslot j) (a j) (b j) (ha j) (hsSlot j))
      (hz W₁ a₁ b₁ ha₁ hs₁) (hz W₂ a₂ b₂ ha₂ hs₂)
      (fun j x hx=>(hsSlot j hx).2) (fun x hx=>(hs₁ hx).2)
      (fun x hx=>(hs₂ hx).2) v hv0
    rw [←he]
    exact hh.2.trans hN
  have ht := htail η t (finiteColumns S) (finiteColumnCoefficient S β) Φ K X HN Tsec Z Csec ξ
    hK hXX hZ hCs hNN hsec hthreshold
  apply ht.trans
  have hsq := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hm 2
  calc
    _ ≤ (Dprofile*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j))^2*
        K*(Real.exp HN*X)^2*(C*sΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right hsq hK.le
    _ = _ := by dsimp [Dprofile]; ring

end SevenEighths.CenteredMomentSourceSupportedTailUniform

end

end OAI
