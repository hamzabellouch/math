import OAI.NumberTheory.DirichletL.Moments.SourceProfileMass

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap

namespace SevenEighths.CenteredMomentSourceProfileMassUniform
open ActualEisensteinCubic CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass
local notation "O" => ActualEisensteinCubic.O

theorem profile_mass_explicit {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (b D : ι → ℝ) (b₁ b₂ D₁ D₂ : ℝ)
    (hb : ∀ j,0≤b j) (hb₁ : 0≤b₁) (hb₂ : 0≤b₂)
    (hD : ∀ j,0≤D j) (hD₁ : 0≤D₁) (hD₂ : 0≤D₂)
    (hzSlot : ∀ j,Wslot j 0=0) (hz₁ : W₁ 0=0) (hz₂ : W₂ 0=0)
    (hsSlot : ∀ j x,Wslot j x≠0→x≤b j)
    (hs₁ : ∀ x,W₁ x≠0→x≤b₁) (hs₂ : ∀ x,W₂ x≠0→x≤b₂)
    (hbound : ∀ j x,‖Wslot j x‖≤D j)
    (hbound₁ : ∀ x,‖W₁ x‖≤D₁) (hbound₂ : ∀ x,‖W₂ x‖≤D₂)
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (hν : ∀ j I,‖ν j I‖≤1)
    (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O)
    (hP : ∀ j,0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (S : Finset (Tuple ι)) :
    (∑v∈S,‖profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖)≤
      (2*128^(Fintype.card ι+2)*(∏j,D j)*D₁*D₂*(∏j,b j)*b₁*b₂)*
        (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏j,P j) := by
  let e := Fintype.equivFin ι
  have hzero : ∀ i,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i 0=0 := by
    simpa only [Fin.forall_fin_add,sourceProfiles,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hzSlot (e.symm j)) (And.intro hz₁ hz₂)
  have hs : ∀ i x,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i x≠0→
      x≤sourceBounds (fun j => b (e.symm j)) b₁ b₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hsSlot (e.symm j)) (And.intro hs₁ hs₂)
  have hbound' : ∀ i x,‖sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i x‖≤
      sourceBounds (fun j => D (e.symm j)) D₁ D₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hbound (e.symm j)) (And.intro hbound₁ hbound₂)
  have hm := originalCoefficient_mass (Fintype.card ι) 1 one_ne_zero
    (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0 (fun j => ν (e.symm j))
    (fun j I => hν _ I) (fun j => Wslot (e.symm j)) (fun j => P (e.symm j))
    (fun j => b (e.symm j)) (fun j => D (e.symm j)) W₁ W₂
    b₁ b₂ D₁ D₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s
    (fun j => hb _) hb₁ hb₂ (fun j => hD _) hD₁ hD₂
    (fun j => hP _) hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hzero hs hbound'
    (S.image (tupleEquiv e))
  rw [finite_original_mass_reindex] at hm
  simp_rw [profileCoefficient_eq_original]
  simpa only [sourceMassConstant,e.symm.prod_comp D,e.symm.prod_comp b,e.symm.prod_comp P] using hm

theorem profile_mass_uniform {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j,0<a j) (hb : ∀ j,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hWslot : ∀ j,ContDiff ℝ ∞ (Wslot j)) :
    ∃ C : ℝ,0<C ∧ ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁ : ℝ→ℂ)⊆Set.Icc a₁ b₁ →
      Function.support (W₂ : ℝ→ℂ)⊆Set.Icc a₂ b₂ →
      ∀ (R : Ideal O) (ν : ι→Ideal O→ℂ),(∀ j I,‖ν j I‖≤1)→
      ∀ (P : ι→ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j)→0<X₁→0<X₂→0<Y₁→0<Y₂→B₁≠0→B₂≠0→
      X₁*X₂=T→Y₁*Y₂=T→∀ S : Finset (Tuple ι),
      (∑v∈S,‖profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖)≤
        (C*SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)*
          (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏j,P j) := by
  choose D hD hbound hz hs using fun j =>
    smooth_annular_bound (Wslot j) (a j) (b j) (ha j) (hsSlot j) (hWslot j)
  let C₀ := 2*128^(Fintype.card ι+2)*(∏j,D j)*(∏j,b j)*b₁*b₂
  have hprodD : 0≤∏j,D j := Finset.prod_nonneg (fun j _ => hD j)
  have hprodb : 0≤∏j,b j := Finset.prod_nonneg (fun j _ => hb j)
  have hC₀ : 0≤C₀ := by dsimp [C₀]; positivity
  refine ⟨1+C₀,by positivity,?_⟩
  intro W₁ W₂ hs₁ hs₂ R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have hzW (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
      (hs : Function.support (W : ℝ→ℂ)⊆Set.Icc a b) : W 0=0 := by
    by_contra hn
    exact (not_le_of_gt ha) (hs hn).1
  have hm := profile_mass_explicit Wslot W₁ W₂ b D b₁ b₂
    (SchwartzMap.seminorm ℝ 0 0 W₁) (SchwartzMap.seminorm ℝ 0 0 W₂)
    hb hb₁ hb₂ hD (apply_nonneg _ _) (apply_nonneg _ _) hz
    (hzW W₁ a₁ b₁ ha₁ hs₁) (hzW W₂ a₂ b₂ ha₂ hs₂) hs
    (fun x hx => (hs₁ hx).2) (fun x hx => (hs₂ hx).2) hbound
    (SchwartzMap.norm_le_seminorm ℝ W₁) (SchwartzMap.norm_le_seminorm ℝ W₂)
    R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hprodP : 0≤∏j,P j := Finset.prod_nonneg (fun j _ => (hP j).le)
  have hpos : 0≤SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂*
      (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏j,P j) := by positivity
  apply hm.trans
  have hh := mul_le_mul_of_nonneg_right (show C₀≤1+C₀ by linarith) hpos
  dsimp only [C₀] at hh
  nlinarith only [hh]
end SevenEighths.CenteredMomentSourceProfileMassUniform

end

end OAI
