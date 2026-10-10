import OAI.NumberTheory.DirichletL.Moments.SourceProfileMass
import OAI.NumberTheory.DirichletL.Moments.SupportedZeroEnergy

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSourceZeroEnergy
open ActualEisensteinCubic HeckeFamily CenteredMomentRectangle
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentSupportedZeroEnergy
open CenteredMomentFirstLocalization CenteredMomentSourceRow
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

theorem profileCoefficient_norm_le {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (hν : ∀ j I,‖ν j I‖≤1)
    (Wslot : ι → ℝ → ℂ) (P D : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (D₁ D₂ : ℝ)
    (hD : ∀ j,0≤D j) (hD₁ : 0≤D₁) (hD₂ : 0≤D₂)
    (hslot : ∀ j x,‖Wslot j x‖≤D j)
    (h₁ : ∀ x,‖W₁ x‖≤D₁) (h₂ : ∀ x,‖W₂ x‖≤D₂)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    ‖profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖≤
      2*D₁*D₂*(∏ j,D j) := by
  have hp : ‖∏ j,ν j (v (Sum.inl j))*Wslot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/P j)‖≤∏ j,D j := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro j _
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (hν j _) (hslot j _)
      (norm_nonneg _) zero_le_one
  have hr (I J : Ideal O) : ‖idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J‖≤2*D₁*D₂ := by
    unfold idealRectangle
    apply (norm_sub_le _ _).trans
    rw [norm_mul,norm_mul]
    have hx := mul_le_mul (h₁ ((Ideal.absNorm I:ℝ)/X₁))
      (h₂ ((Ideal.absNorm J:ℝ)/X₂)) (norm_nonneg _) hD₁
    have hy := mul_le_mul (h₁ ((Ideal.absNorm I:ℝ)/Y₁))
      (h₂ ((Ideal.absNorm J:ℝ)/Y₂)) (norm_nonneg _) hD₁
    linarith
  have hm (p : Prop) [Decidable p] : ‖(if p then 1 else 0 : ℂ)‖≤1 := by
    split_ifs <;> norm_num
  have hDp : 0≤∏ j,D j := Finset.prod_nonneg (fun j _ => hD j)
  unfold profileCoefficient
  rw [norm_mul,norm_mul,norm_mul]
  have h := mul_le_mul
    (mul_le_mul (mul_le_mul hp (hm (IsCoprime (finiteTupleProduct v) R)) (norm_nonneg _) (Finset.prod_nonneg (fun j _ => hD j)))
      (hr (B₁*v (Sum.inr 0)) (B₂*v (Sum.inr 1))) (norm_nonneg _) (by positivity))
    (hm (s∣finiteTupleProduct v)) (norm_nonneg _) (by positivity)
  simpa only [mul_one] using h.trans_eq (by ring)

theorem profileCoefficient_product_bound {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ)
    (P b : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ)
    (B₁ B₂ s : Ideal O)
    (hP : ∀ j,0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hz : ∀ j,Wslot j 0=0) (hz₁ : W₁ 0=0) (hz₂ : W₂ 0=0)
    (hs : ∀ j x,Wslot j x≠0 → x≤b j)
    (hs₁ : ∀ x,W₁ x≠0 → x≤b₁) (hs₂ : ∀ x,W₂ x≠0 → x≤b₂)
    (v : Tuple ι)
    (hv : profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    finiteTupleProduct v≠0 ∧ (Ideal.absNorm (finiteTupleProduct v):ℝ)≤
      (∏ j,b j)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  let e := Fintype.equivFin ι
  have hzero : ∀ i,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i 0=0 := by
    simpa only [Fin.forall_fin_add,sourceProfiles,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hz (e.symm j)) (And.intro hz₁ hz₂)
  have hsup : ∀ i x,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i x≠0 →
      x≤sourceBounds (fun j => b (e.symm j)) b₁ b₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hs (e.symm j)) (And.intro hs₁ hs₂)
  have hn : CenteredMomentAddedZero.originalCoefficient (Fintype.card ι) 1
      (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0
      (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j)) (fun j => P (e.symm j))
      W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (tupleEquiv e v)≠0 := by
    rw [originalCoefficient_reindex,←profileCoefficient_eq_original]
    exact hv
  have hh := originalCoefficient_product_bound (Fintype.card ι) 1
    (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0 (fun j => ν (e.symm j))
    (fun j => Wslot (e.symm j)) (fun j => P (e.symm j)) (fun j => b (e.symm j))
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j => hP (e.symm j))
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hzero hsup (tupleEquiv e v) hn
  simpa only [tupleProduct_reindex,sourceRadius,e.symm.prod_comp] using hh

theorem zeroEnergy_eq_zero_of_subunit {ι : Type*} [Fintype ι]
    (η : Character) (m A : O) (t : ℝ) (S : Finset (Tuple ι)) (β : Tuple ι → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K Y : ℝ) (hY : Y<1)
    (hN : ∀ v∈S,β v≠0 → finiteTupleProduct v≠0 ∧
      (Ideal.absNorm (finiteTupleProduct v):ℝ)≤Y) :
    zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) W K=0 := by
  have hb (v : Tuple ι) (hv : v∈S) : β v=0 := by
    by_contra hn
    have hh := hN v hv hn
    have hnorm : (1:ℝ)≤Ideal.absNorm (finiteTupleProduct v) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hh.1)
    linarith
  have hc (I : Ideal O) : finiteColumnCoefficient S β I=0 := by
    unfold finiteColumnCoefficient
    exact Finset.sum_eq_zero (fun v hv => hb v (Finset.mem_filter.mp hv).1)
  simp only [zeroEnergy,hc,zero_mul,star_zero,mul_zero,Finset.sum_const_zero]

theorem smooth_source_zero_energy {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j,0<a j) (hb : ∀ j,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (R : Ideal O) (ν : ι → Ideal O → ℂ), (∀ j I,‖ν j I‖≤1) →
      ∀ (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple ι)) (Φ : 𝓢(ℝ,ℂ)) (X K : ℝ),
      0<X → 0≤K → (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)≤X →
      ‖((X⁻¹:ℝ):ℂ)*zeroEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) Φ K‖≤
        C*K*‖paperRadialFourier Φ 0‖*X^ε := by
  choose D hD hDb hz hs using fun j => smooth_annular_bound (Wslot j) (a j) (b j) (ha j) (hsSlot j) (hWslot j)
  obtain ⟨D₁,hD₁,hDb₁,hz₁,hsb₁⟩ := smooth_annular_bound W₁ a₁ b₁ ha₁ hs₁ hW₁
  obtain ⟨D₂,hD₂,hDb₂,hz₂,hsb₂⟩ := smooth_annular_bound W₂ a₂ b₂ ha₂ hs₂ hW₂
  let B := 2*D₁*D₂*(∏ j,D j)
  have hB : 0≤B := mul_nonneg (by positivity) (Finset.prod_nonneg (fun j _ => hD j))
  have hend : 0≤(∏ j,b j)*b₁*b₂ := mul_nonneg
    (mul_nonneg (Finset.prod_nonneg (fun j _ => hb j)) hb₁) hb₂
  let L := 1+(∏ j,b j)*b₁*b₂
  have hL : 0<L := by dsimp only [L]; linarith
  have hendL : (∏ j,b j)*b₁*b₂≤L := by dsimp only [L]; linarith
  obtain ⟨C₀,hC₀,hbound⟩ := active_tuple_zero_energy_bound (Fintype.card ι) ε hε
  let C := C₀*(1+B^2)*L^(1+ε)
  have hC : 0<C := mul_pos (mul_pos hC₀ (by positivity)) (Real.rpow_pos_of_pos hL _)
  refine ⟨C,hC,?_⟩
  intro η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S Φ X K hXX hK hscale
  let β := profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hβ (v : Tuple ι) : ‖β v‖≤B :=
    profileCoefficient_norm_le R ν hν Wslot P D W₁ W₂ D₁ D₂ hD hD₁ hD₂ hDb hDb₁ hDb₂
      X₁ X₂ Y₁ Y₂ B₁ B₂ s v
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hraw : 0≤(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) :=
    mul_nonneg (div_nonneg hT.le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (Finset.prod_nonneg (fun j _ => (hP j).le))
  have hN (v : Tuple ι) (hv : β v≠0) :
      finiteTupleProduct v≠0 ∧ (Ideal.absNorm (finiteTupleProduct v):ℝ)≤L*X := by
    have hh := profileCoefficient_product_bound R ν Wslot P b W₁ W₂ b₁ b₂
      X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY
      hz hz₁ hz₂ hs hsb₁ hsb₂ v hv
    refine ⟨hh.1,hh.2.trans ?_⟩
    calc
      _ = ((∏ j,b j)*b₁*b₂)*((T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)) := by ring
      _ ≤ L*X := mul_le_mul hendL hscale hraw hL.le
  by_cases hsmall : L*X<1
  · have he := zeroEnergy_eq_zero_of_subunit η m A t S β Φ K (L*X) hsmall
      (fun v _ hv => hN v hv)
    change ‖((X⁻¹:ℝ):ℂ)*zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) Φ K‖≤_
    rw [he,mul_zero,norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC.le hK) (norm_nonneg _)) (Real.rpow_nonneg hXX.le _)
  have hradius : 1≤L*X := le_of_not_gt hsmall
  have he := hbound (le_refl (Fintype.card ι)) η m A t S β Φ (L*X) K B hradius hK hB
    (fun v _ _ => hβ v) (fun I _ hI => by
      obtain ⟨v,hv,hne,hprod⟩ := finiteColumnCoefficient_witness S β I hI
      rw [←hprod]
      exact (hN v hne).2)
  have hpower : X⁻¹*(L*X)^(1+ε)=L^(1+ε)*X^ε := by
    rw [Real.mul_rpow hL.le hXX.le,Real.rpow_add hXX,Real.rpow_one]
    field_simp
  change ‖((X⁻¹:ℝ):ℂ)*zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) Φ K‖≤_
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hXX)]
  apply (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hXX.le)).trans
  calc
    _ = C₀*B^2*L^(1+ε)*K*‖paperRadialFourier Φ 0‖*X^ε := by
      calc
        _ = C₀*B^2*K*‖paperRadialFourier Φ 0‖*(X⁻¹*(L*X)^(1+ε)) := by ring
        _ = _ := by rw [hpower];ring
    _ ≤ C*K*‖paperRadialFourier Φ 0‖*X^ε := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hXX.le _)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_right _ hK
      dsimp only [C]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : B^2≤1+B^2) hC₀.le)
        (Real.rpow_nonneg hL.le _)

theorem smooth_source_zero_energy_at_radius {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j,0<a j) (hb : ∀ j,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (R : Ideal O) (ν : ι → Ideal O → ℂ), (∀ j I,‖ν j I‖≤1) →
      ∀ (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple ι)) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ), 0≤K →
      let X := (∏ j,b j)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)
      let E := zeroEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) Φ K
      (X<1 → E=0) ∧ ‖((X⁻¹:ℝ):ℂ)*E‖≤C*K*‖paperRadialFourier Φ 0‖*X^ε := by
  choose D hD hDb hz hs using fun j => smooth_annular_bound (Wslot j) (a j) (b j) (ha j) (hsSlot j) (hWslot j)
  obtain ⟨D₁,hD₁,hDb₁,hz₁,hsb₁⟩ := smooth_annular_bound W₁ a₁ b₁ ha₁ hs₁ hW₁
  obtain ⟨D₂,hD₂,hDb₂,hz₂,hsb₂⟩ := smooth_annular_bound W₂ a₂ b₂ ha₂ hs₂ hW₂
  let B := 2*D₁*D₂*(∏ j,D j)
  have hB : 0≤B := mul_nonneg (by positivity) (Finset.prod_nonneg (fun j _ => hD j))
  obtain ⟨C₀,hC₀,hbound⟩ := normalized_supported_tuple_zero_energy_bound (Fintype.card ι) ε hε
  refine ⟨C₀*(1+B^2),mul_pos hC₀ (by positivity),?_⟩
  intro η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S Φ K hK X E
  let β := profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hβ (v : Tuple ι) : ‖β v‖≤B :=
    profileCoefficient_norm_le R ν hν Wslot P D W₁ W₂ D₁ D₂ hD hD₁ hD₂ hDb hDb₁ hDb₂
      X₁ X₂ Y₁ Y₂ B₁ B₂ s v
  have hN (v : Tuple ι) (hv : β v≠0) :
      finiteTupleProduct v≠0 ∧ (Ideal.absNorm (finiteTupleProduct v):ℝ)≤X :=
    profileCoefficient_product_bound R ν Wslot P b W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s
      hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hz hz₁ hz₂ hs hsb₁ hsb₂ v hv
  have hzero (hx : X<1) : E=0 :=
    zeroEnergy_eq_zero_of_subunit η m A t S β Φ K X hx (fun v _ hv => hN v hv)
  refine ⟨hzero,?_⟩
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hXX : 0≤X := by
    dsimp only [X]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (Finset.prod_nonneg (fun j _ => hb j)) hb₁) hb₂)
      (div_nonneg hT.le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))))
      (Finset.prod_nonneg (fun j _ => (hP j).le))
  by_cases hx : X<1
  · rw [hzero hx,mul_zero,norm_zero]
    positivity
  have he := hbound (le_refl (Fintype.card ι)) η m A t S β Φ X K B
    (le_of_not_gt hx) hK hB (fun v _ => hβ v) (fun v _ hv => (hN v hv).2)
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hXX _)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    C₀*K*B^2 = C₀*B^2*K := by ring
    _ ≤ C₀*(1+B^2)*K := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : B^2≤1+B^2) hC₀.le) hK

theorem smooth_subset_source_zero_energy {α : Type*} (F : Finset α)
    (Wslot : α → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : α → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈F,0<a j) (hb : ∀ j∈F,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈F,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ J : Finset α,J⊆F →
      ∀ (η : Character) (m A : O) (t : ℝ) (R : Ideal O) (ν : α → Ideal O → ℂ),
      (∀ j∈J,∀ I,‖ν j I‖≤1) →
      ∀ (P : α → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple J)) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ),0≤K →
      let H := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j)
      let ρ := (∏ j∈J,b j)*b₁*b₂*H
      let E := zeroEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) Φ K
      (ρ<1 → E=0) ∧
      ‖((ρ⁻¹:ℝ):ℂ)*E‖≤C*K*‖paperRadialFourier Φ 0‖*ρ^ε ∧
      ∀ X : ℝ,0<X → H≤X → ‖((X⁻¹:ℝ):ℂ)*E‖≤C*K*‖paperRadialFourier Φ 0‖*X^ε := by
  have hraw (J : Finset α) (hJ : J⊆F) := smooth_source_zero_energy
    (fun j : J => Wslot j.val) W₁ W₂ (fun j : J => a j.val) (fun j : J => b j.val)
    a₁ b₁ a₂ b₂ (fun j => ha j.val (hJ j.property)) (fun j => hb j.val (hJ j.property))
    ha₁ hb₁ ha₂ hb₂ (fun j => hsSlot j.val (hJ j.property)) hs₁ hs₂
    (fun j => hWslot j.val (hJ j.property)) hW₁ hW₂ ε hε
  have hrad (J : Finset α) (hJ : J⊆F) := smooth_source_zero_energy_at_radius
    (fun j : J => Wslot j.val) W₁ W₂ (fun j : J => a j.val) (fun j : J => b j.val)
    a₁ b₁ a₂ b₂ (fun j => ha j.val (hJ j.property)) (fun j => hb j.val (hJ j.property))
    ha₁ hb₁ ha₂ hb₂ (fun j => hsSlot j.val (hJ j.property)) hs₁ hs₂
    (fun j => hWslot j.val (hJ j.property)) hW₁ hW₂ ε hε
  let D (J : Finset α) : ℝ := if hJ : J⊆F then (hraw J hJ).choose+(hrad J hJ).choose else 1
  have hD (J : Finset α) : 0<D J := by
    dsimp only [D]
    split_ifs with hJ
    · exact add_pos (hraw J hJ).choose_spec.1 (hrad J hJ).choose_spec.1
    · norm_num
  let C := 1+∑ J∈F.powerset,D J
  have hC : 0<C := by
    have hsum := Finset.sum_nonneg (fun J (_ : J∈F.powerset) => (hD J).le)
    dsimp only [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro J hJ η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S Φ K hK H ρ E
  have hDC : D J≤C := by
    have hle := Finset.single_le_sum (fun L (_ : L∈F.powerset) => (hD L).le) (Finset.mem_powerset.mpr hJ)
    dsimp only [C]
    linarith
  have hde : D J=(hraw J hJ).choose+(hrad J hJ).choose := by simp only [D,dite_eq_left hJ]
  have hrawC : (hraw J hJ).choose≤C := by
    rw [hde] at hDC
    linarith [(hrad J hJ).choose_spec.1]
  have hradC : (hrad J hJ).choose≤C := by
    rw [hde] at hDC
    linarith [(hraw J hJ).choose_spec.1]
  have hr := (hrad J hJ).choose_spec.2 η m A t R (fun j : J => ν j.val)
    (fun j I => hν j.val j.property I) (fun j : J => P j.val)
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j => hP j.val j.property)
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S Φ K hK
  have heq : (∏ j : J,b j.val)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j : J,P j.val)=ρ := by
    rw [Finset.prod_coe_sort,Finset.prod_coe_sort]
    dsimp only [ρ,H]
    ring
  dsimp only at hr
  rw [heq] at hr
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hprodB : 0≤∏ j∈J,b j := Finset.prod_nonneg (fun j hj => hb j (hJ hj))
  have hprodP : 0≤∏ j∈J,P j := Finset.prod_nonneg (fun j hj => (hP j hj).le)
  have hρ : 0≤ρ := by dsimp only [ρ,H]; positivity
  refine ⟨hr.1,hr.2.trans ?_,?_⟩
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hradC hK) (norm_nonneg _))
      (Real.rpow_nonneg hρ _)
  · intro X hXX hscale
    have hx := (hraw J hJ).choose_spec.2 η m A t R (fun j : J => ν j.val)
      (fun j I => hν j.val j.property I) (fun j : J => P j.val)
      X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j => hP j.val j.property)
      hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S Φ X K hXX hK
      (by simpa only [Finset.prod_coe_sort] using hscale)
    exact hx.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrawC hK) (norm_nonneg _))
      (Real.rpow_nonneg hXX.le _))

end SevenEighths.CenteredMomentSourceZeroEnergy

end

end OAI
