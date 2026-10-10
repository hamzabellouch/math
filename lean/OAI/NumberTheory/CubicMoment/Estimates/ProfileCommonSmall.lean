import OAI.NumberTheory.CubicMoment.Estimates.ProfilePoissonTotal
import OAI.NumberTheory.CubicMoment.Estimates.SmallBCommonSum

namespace OAI
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment.ProfileControl

theorem smallB_coprime_dispersion_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (A T u : ℝ), 4 ≤ (Z:ℝ) → 16 ≤ (Z:ℝ)^(3/4:ℝ) →
      (Z:ℝ)^(1/50:ℝ) ≤ T → (Z:ℝ)^(3/2:ℝ) ≤ A →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ (Z:ℝ)/2 ≤ norm b ∧ norm b ≤ (Z:ℝ)) →
      dyadicHeightMean (fun t => ‖coprimeDispersionGram S β (u+t) P.V A‖) T ≤
        (K*P.cost)*A^(2/3:ℝ)*(Z:ℝ)^(2/3-1/40000:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K₀,hK₀,hbound₀⟩ := smallB_poisson_total_height_power hMV hC hHuxley
  refine ⟨K₀,hK₀,?_⟩
  intro P S β Z A T u hZ hlarge hT hAlo hS
  let K := K₀*P.cost
  have hK : 0 < K := mul_pos hK₀ P.cost_pos
  have hbound := hbound₀ P
  have hA : 0 < A := (Real.rpow_pos_of_pos (by linarith : 0 < (Z:ℝ)) _).trans_le hAlo
  have hp : ∀ b ∈ S, primary b ∧ Squarefree b ∧ b ≠ 1 := by
    intro b hb
    refine ⟨(hS b hb).1,(hS b hb).2.1,?_⟩
    intro he
    have hn := (hS b hb).2.2.1
    rw [he,norm_one_eq] at hn
    linarith
  have he (t : ℝ) := coprimeDispersionGram_eq_poisson_series S hp β (u+t) P.V P.compact P.smooth hA
  simp_rw [he]
  exact hbound S frequencyDyad β Z A T u hZ hlarge hT hAlo hS (fun _ => Finset.Subset.refl _)


theorem smallB_coprime_height_real
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (v : Eisenstein → ℂ)
      (Z A T u : ℝ), 4 ≤ (⌊Z⌋₊:ℝ) → 16 ≤ (⌊Z⌋₊:ℝ)^(3/4:ℝ) →
      Z^(1/50:ℝ) ≤ T → Z^(3/2:ℝ) ≤ A →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t =>
        ‖coprimeGramForm S (fun b => v b*star (normTwist (u+t) b)) P.V A‖) T ≤
        (K*P.cost)*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ)*∑ b ∈ S, ‖v b‖^2 := by
  obtain ⟨K₀,hK₀,hbound₀⟩ := smallB_coprime_dispersion_height_power hMV hC hHuxley
  refine ⟨K₀,hK₀,?_⟩
  intro P S v Z A T u hZ hlarge hT hA hS
  let K := K₀*P.cost
  have hK : 0 < K := mul_pos hK₀ P.cost_pos
  have hbound := hbound₀ P
  have hZ₀ : 0 ≤ Z := by
    by_contra h
    have hf : ⌊Z⌋₊ = 0 := Nat.floor_of_nonpos (le_of_not_ge h)
    simp only [hf,Nat.cast_zero] at hZ
    linarith
  have hf : (⌊Z⌋₊:ℝ) ≤ Z := Nat.floor_le hZ₀
  have hA₀ : 0 ≤ A := (Real.rpow_nonneg hZ₀ _).trans hA
  have hS' : ∀ b ∈ S, primary b ∧ Squarefree b ∧
      (⌊Z⌋₊:ℝ)/2 ≤ norm b ∧ norm b ≤ (⌊Z⌋₊:ℝ) := by
    intro b hb
    refine ⟨(hS b hb).1,(hS b hb).2.1,?_,?_⟩
    · linarith [(hS b hb).2.2.1]
    · have hh : normNat b ≤ ⌊Z⌋₊ := Nat.le_floor (by
        rw [normNat_cast]
        exact (hS b hb).2.2.2)
      have hr : (normNat b : ℝ) ≤ (⌊Z⌋₊:ℝ) := by exact_mod_cast hh
      rwa [normNat_cast] at hr
  have hh := hbound S (gramUntwist v) ⌊Z⌋₊ A T u hZ hlarge
    ((Real.rpow_le_rpow (by positivity) hf (by norm_num)).trans hT)
    ((Real.rpow_le_rpow (by positivity) hf (by norm_num)).trans hA) hS'
  have he (t : ℝ) := coprimeGramForm_height_eq S
    (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩) v (u+t) P.V A
  simp_rw [← he] at hh
  have henergy : (∑ b ∈ S, ‖gramUntwist v b‖^2) = ∑ b ∈ S, ‖v b‖^2 := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [gramUntwist_norm (hS b hb).1 (hS b hb).2.1]
  rw [henergy] at hh
  exact hh.trans (by
    gcongr)


theorem smallB_common_row_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A T u : ℝ) (k m : Eisenstein), 0 ≤ Z → Z^(3/2:ℝ) ≤ A →
      Z^(1/50:ℝ) ≤ T → primary k → primary m → m ∣ k →
      4 ≤ (⌊Z/norm k⌋₊:ℝ) → 16 ≤ (⌊Z/norm k⌋₊:ℝ)^(3/4:ℝ) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t => ‖coprimeGramForm (residualRows S k)
        (commonBlockCoefficient (fun b => star (dispersionAmplitude β (u+t) b)) k m)
        P.V (A/norm m)‖) T ≤
      (K*P.cost)*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ)*commonBlockEnergy S β k := by
  obtain ⟨K₀,hK₀,hbound₀⟩ := smallB_coprime_height_real hMV hC hHuxley
  refine ⟨K₀,hK₀,?_⟩
  intro P S β Z A T u k m hZ hA hT hk hm hmk hfloor hlarge hS
  let K := K₀*P.cost
  have hK : 0 < K := mul_pos hK₀ P.cost_pos
  have hbound := hbound₀ P
  have hk₀ := primary_ne_zero hk
  have hk₁ := one_le_norm hk₀
  have hm₀ := primary_ne_zero hm
  have hm₁ := one_le_norm hm₀
  have hmkN := norm_le_of_dvd hk₀ hmk
  have hS₀ : ∀ b ∈ S, primary b ∧ Squarefree b := fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩
  have hr := residualRows_primary hk hS₀
  let v := commonBlockCoefficient (fun b => star (β b*gauss b)) k m
  have hrows : ∀ b ∈ residualRows S k,
      primary b ∧ Squarefree b ∧ (Z/norm k)/2 ≤ norm b ∧ norm b ≤ Z/norm k := by
    intro b hb
    have hkb := hS (k*b) ((mem_residualRows hk₀).mp hb)
    refine ⟨(hr b hb).1,(hr b hb).2,?_,?_⟩
    · rw [div_right_comm]
      apply (div_le_iff₀ (norm_pos_of_ne_zero hk₀)).mpr
      rw [norm_mul_eq] at hkb
      nlinarith [hkb.2.2.1]
    · apply (le_div_iff₀ (norm_pos_of_ne_zero hk₀)).mpr
      simpa only [norm_mul_eq,mul_comm] using hkb.2.2.2
  have hrow := hbound (residualRows S k) v (Z/norm k) (A/norm m) T u hfloor hlarge
    (smallB_common_height_scale hZ hk₁ hT)
    (smallB_common_outer_scale hZ hk₁ (norm_pos_of_ne_zero hm₀) hmkN hA) hrows
  have he (t : ℝ) : coprimeGramForm (residualRows S k)
      (commonBlockCoefficient (fun b => star (dispersionAmplitude β (u+t) b)) k m) P.V (A/norm m) =
      coprimeGramForm (residualRows S k) (fun b => v b*star (normTwist (u+t) b)) P.V (A/norm m) := by
    rw [common_coprime_height_eq S β k m hk hS₀,
      ← coprimeGramForm_height_eq _ hr]
  simp_rw [he]
  have henergy : (∑ b ∈ residualRows S k, ‖v b‖^2) ≤ commonBlockEnergy S β k := by
    apply (commonBlockCoefficient_unweighted_energy_le S hS₀
      (fun b => star (β b*gauss b)) hk m).trans
    unfold commonBlockEnergy
    apply Finset.sum_le_sum
    intro b hb
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hkb := (hS (k*b) ((mem_residualRows hk₀).mp hb)).1
    apply pow_le_pow_left₀ (by positivity)
    simp only [norm_star,norm_mul]
    exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_gauss_le_one hkb)
  have hA₀ : 0 ≤ A := (Real.rpow_nonneg hZ _).trans hA
  exact hrow.trans (by
    have hs := smallB_common_bound_scale hZ hA₀ hk₁ hm₁
    calc
      _ ≤ K*(A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ))*(∑ b ∈ residualRows S k, ‖v b‖^2) := by
        simpa only [K,mul_assoc] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs hK.le) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      _ ≤ _ := by
        have hsc : 0 ≤ K*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ) := by positivity
        simpa only [K,mul_assoc] using mul_le_mul_of_nonneg_left henergy hsc)


theorem smallB_common_block_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A T u : ℝ) (k : Eisenstein), 0 < Z → Z^(3/2:ℝ) ≤ A →
      Z^(1/50:ℝ) ≤ T → primary k → Squarefree k →
      4 ≤ (⌊Z/norm k⌋₊:ℝ) → 16 ≤ (⌊Z/norm k⌋₊:ℝ)^(3/4:ℝ) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t => ‖commonGramBlock S
        (fun b => star (dispersionAmplitude β (u+t) b)) P.V A k‖) T ≤
      (K*P.cost)*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ)*
        ((2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S β k) := by
  obtain ⟨K₀,hK₀,hrow₀⟩ := smallB_common_row_height_power hMV hC hHuxley
  refine ⟨K₀,hK₀,?_⟩
  intro P S β Z A T u k hZ hA hT hk hsk hfloor hlarge hS
  let K := K₀*P.cost
  have hK : 0 < K := mul_pos hK₀ P.cost_pos
  have hrow := hrow₀ P
  have hA₀ : 0 < A := (Real.rpow_pos_of_pos hZ _).trans_le hA
  have hT₀ : 0 < T := (Real.rpow_pos_of_pos hZ _).trans_le hT
  have hS₀ : ∀ b ∈ S, primary b ∧ Squarefree b := fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩
  let Fset := (primaryPrimeFactors k).powerset
  let F (s : Finset Eisenstein) (t : ℝ) :=
    coprimeGramForm (residualRows S k)
      (commonBlockCoefficient (fun b => star (dispersionAmplitude β (u+t) b)) k (∏ p ∈ s,p))
      P.V (A/norm (∏ p ∈ s,p))
  have hfc (s : Finset Eisenstein) : Continuous (F s) := by
    have he (t : ℝ) := common_coprime_height_eq S β k (∏ p ∈ s,p) hk hS₀ (u+t) P.V
      (A/norm (∏ p ∈ s,p))
    simp_rw [F,he]
    exact (continuous_coprimeDispersionGram _ _ P.V _).comp
      (show Continuous (fun t : ℝ => u+t) from continuous_const.add continuous_id)
  have he (t : ℝ) : commonGramBlock S
      (fun b => star (dispersionAmplitude β (u+t) b)) P.V A k =
      ∑ s ∈ Fset, (idealMoebius (∏ p ∈ s,p):ℂ)*F s t :=
    commonGramBlock_moebius S hS₀ _ P.V P.compact P.smooth hA₀ hk hsk
  simp_rw [he]
  apply (dyadicHeightMean_norm_sum_le Fset
    (fun s t => (idealMoebius (∏ p ∈ s,p):ℂ)*F s t)
    (fun s _ => continuous_const.mul (hfc s)) hT₀).trans
  have hb (s : Finset Eisenstein) (hs : s ∈ Fset) :
      dyadicHeightMean (fun t => ‖(idealMoebius (∏ p ∈ s,p):ℂ)*F s t‖) T ≤
        K*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ)*commonBlockEnergy S β k := by
    have hsub : s ⊆ primaryPrimeFactors k := Finset.mem_powerset.mp hs
    have hm : primary (∏ p ∈ s,p) := primary_finset_prod _ _
      (fun p hp => (primaryPrimeFactor_spec hk (hsub hp)).1.1)
    have hmk : (∏ p ∈ s,p) ∣ k := (primary_subsets_prod_dvd hk hsub k).mpr
      (fun p hp => (primaryPrimeFactor_spec hk (hsub hp)).2)
    have hmc : Continuous (fun t => (idealMoebius (∏ p ∈ s,p):ℂ)*F s t) :=
      continuous_const.mul (hfc s)
    have havg := dyadicHeightMean_mono
      (f := fun t => ‖(idealMoebius (∏ p ∈ s,p):ℂ)*F s t‖)
      (g := fun t => ‖F s t‖) hmc.norm (hfc s).norm hT₀ (fun t _ => by
        rw [norm_mul]
        exact mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one _))
    exact havg.trans (hrow S β Z A T u k _ hZ.le hA hT hk
      hm
      hmk hfloor hlarge hS)
  exact (Finset.sum_le_sum hb).trans_eq (by
    simp only [Fset,Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    ring)


theorem smallB_common_sum_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : PoissonProfileBudget) (S I : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A T u : ℝ), 0 < Z → Z^(3/2:ℝ) ≤ A → Z^(1/50:ℝ) ≤ T →
      I ⊆ commonRowFactors S →
      (∀ k ∈ I, 4 ≤ (⌊Z/norm k⌋₊:ℝ) ∧ 16 ≤ (⌊Z/norm k⌋₊:ℝ)^(3/4:ℝ)) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t => ‖∑ k ∈ I, commonGramBlock S
        (fun b => star (dispersionAmplitude β (u+t) b)) P.V A k‖) T ≤
      (K*P.cost)*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K₀,hK₀,hblock₀⟩ := smallB_common_block_height_power hMV hC hHuxley
  obtain ⟨E,hE,henergy⟩ := common_energy_small_power (1/80000) (by norm_num)
  refine ⟨K₀*E,by positivity,?_⟩
  intro P S I β Z A T u hZ hA hT hI hfloor hS
  let K := K₀*P.cost
  have hK : 0 < K := mul_pos hK₀ P.cost_pos
  have hblock := hblock₀ P
  have hS₀ : ∀ b ∈ S, primary b ∧ Squarefree b := fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩
  have hA₀ : 0 < A := (Real.rpow_pos_of_pos hZ _).trans_le hA
  have hT₀ : 0 < T := (Real.rpow_pos_of_pos hZ _).trans_le hT
  have hsum := dyadicHeightMean_norm_sum_le I
    (fun k t => commonGramBlock S (fun b => star (dispersionAmplitude β (u+t) b)) P.V A k)
    (fun k _ => continuous_commonGramBlock_height S β k P.V A u) hT₀
  have hb (k : Eisenstein) (hk : k ∈ I) := hblock S β Z A T u k hZ hA hT
    (commonRowFactors_spec hS₀ (hI hk)).1 (commonRowFactors_spec hS₀ (hI hk)).2
    (hfloor k hk).1 (hfloor k hk).2 hS
  have hbound : (∑ k ∈ I, (2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S β k) ≤
      E*Z^(1/80000:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
    apply le_trans _ (henergy S β Z (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1,(hS b hb).2.2.2⟩))
    exact Finset.sum_le_sum_of_subset_of_nonneg hI (fun k hk _ => by
      exact mul_nonneg (by positivity) (commonBlockEnergy_nonneg S β k))
  calc
    _ ≤ ∑ k ∈ I, K*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ)*
        ((2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S β k) :=
      hsum.trans (Finset.sum_le_sum hb)
    _ = (K*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ))*
        (∑ k ∈ I, (2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S β k) := by
      rw [Finset.mul_sum]
    _ ≤ (K*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ))*(E*Z^(1/80000:ℝ)*∑ b ∈ S, ‖β b‖^2) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by
      have he : Z^(2/3-1/40000:ℝ)*Z^(1/80000:ℝ) = Z^(2/3-1/80000:ℝ) := by
        rw [← Real.rpow_add hZ]
        congr 1
        norm_num
      calc
        _ = (K*E)*A^(2/3:ℝ)*(Z^(2/3-1/40000:ℝ)*Z^(1/80000:ℝ))*∑ b ∈ S, ‖β b‖^2 := by dsimp [K]; ring
        _ = _ := by rw [he]; dsimp [K]; ring


end CubicFirstMoment.ProfileControl

end

end OAI
