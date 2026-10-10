import OAI.NumberTheory.DirichletL.Moments.GaussEnergy
import OAI.NumberTheory.DirichletL.IdealCharacter

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondDiagonal
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem full_zero_off_diagonal (u v : O)
    [Fintype (Residue u)] [Fintype (Residue v)]
    (χ : MulChar (Residue u) ℂ) (ψ : MulChar (Residue v) ℂ)
    (hne : (Ideal.span {u} : Ideal O) ≠ Ideal.span {v}) :
    fullModulusCorrelation u v χ ψ 0 = 0 := by
  unfold fullModulusCorrelation fullCorrelation
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_congruence]
  split_ifs with hc
  · by_cases hx0 : χ (Ideal.Quotient.mk _ x) = 0
    · rw [hx0,zero_mul]
    by_cases hy0 : ψ (Ideal.Quotient.mk _ y) = 0
    · rw [hy0,star_zero,mul_zero]
    have hux : IsCoprime u x := ((Ideal.isCoprime_span_singleton_iff x u).mp
      ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp hx0))).symm
    have hvy : IsCoprime v y := ((Ideal.isCoprime_span_singleton_iff y v).mp
      ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp hy0))).symm
    simp only [sub_zero] at hc
    have hu : u ∣ v*x := by
      have he := dvd_add ((dvd_mul_right u v).trans hc) (dvd_mul_right u y)
      convert he using 1 ; ring
    have hv : v ∣ u*y := by
      have he := dvd_sub (dvd_mul_right v x) ((dvd_mul_left v u).trans hc)
      convert he using 1 ; ring
    have huv := hux.dvd_of_dvd_mul_right hu
    have hvu := hvy.dvd_of_dvd_mul_right hv
    exact False.elim (hne (le_antisymm (Ideal.span_singleton_le_span_singleton.mpr hvu)
      (Ideal.span_singleton_le_span_singleton.mpr huv)))
  · rfl

theorem full_same_zero (u : O) (hu : u ≠ 0) [Fintype (Residue u)]
    (χ : MulChar (Residue u) ℂ) :
    fullModulusCorrelation u u χ χ 0 = ∑ x : Residue u, χ x*star (χ x) := by
  have hcong (x y : Residue u) :
      scaledResidue u u (u*u) rfl x - scaledResidue u u (u*u) (mul_comm u u) y =
        Ideal.Quotient.mk (Ideal.span {u*u}) 0 ↔ x=y := by
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [scaledResidue_congruence,sub_zero,← mul_sub,mul_dvd_mul_iff_left hu]
    exact Ideal.mem_span_singleton.symm.trans Ideal.Quotient.eq.symm
  simp only [fullModulusCorrelation,fullCorrelation,hcong,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem full_same_zero_norm_le (u : O) (hu : u ≠ 0) [Fintype (Residue u)]
    (χ : MulChar (Residue u) ℂ) :
    ‖fullModulusCorrelation u u χ χ 0‖ ≤ (Fintype.card (Residue u) : ℝ) := by
  rw [full_same_zero u hu χ]
  calc
    _ ≤ ∑ x : Residue u, ‖χ x*star (χ x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue u, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hn : χ x = 0
      · simp only [hn,zero_mul,norm_zero,zero_le_one]
      · rw [MulChar.star_apply',MulChar.inv_apply_eq_inv',mul_inv_cancel₀ hn,norm_one]
    _ = _ := by simp

theorem actual_zero_off_diagonal (u v : O) (hu : Supported (Ideal.span {u}))
    (hv : Supported (Ideal.span {v}))
    (hpu : ConcretePrimeRowBridge.goodLambda^2 ∣ u-1)
    (hpv : ConcretePrimeRowBridge.goodLambda^2 ∣ v-1) (hne : u ≠ v) :
    actualCorrelation u v hu hv 0 = 0 := by
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero u hu)
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero v hv)
  let : Fintype (Residue u) := Fintype.ofFinite _
  let : Fintype (Residue v) := Fintype.ofFinite _
  apply full_zero_off_diagonal u v
  intro he
  apply hne
  rw [← primaryGenerator_span u (supported_element_ne_zero u hu) hpu,
    ← primaryGenerator_span v (supported_element_ne_zero v hv) hpv,he]

theorem actual_same_zero_norm_le (u : O) (hu : Supported (Ideal.span {u})) :
    ‖actualCorrelation u u hu hu 0‖ ≤ (Ideal.absNorm (Ideal.span {u}) : ℝ) := by
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero u hu)
  let : Fintype (Residue u) := Fintype.ofFinite _
  have hb := full_same_zero_norm_le u (supported_element_ne_zero u hu) (supportedModulusCharacter u hu)
  simpa only [actualCorrelation,supportedCorrelation,Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card] using hb

theorem divisible_ideal_card (S : Finset (Ideal O)) (s : Ideal O) (hs : s ≠ 0)
    (hS : ∀ I ∈ S, I ≠ 0) (hdiv : ∀ I ∈ S, s ∣ I)
    (Y : ℝ) (hY : 0 ≤ Y) (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y) :
    (S.card : ℝ) ≤ 128*Y/(Ideal.absNorm s : ℝ) := by
  by_cases hempty : S.Nonempty
  · have hquot (I : Ideal O) (hI : I ∈ S) : idealQuotient s I ≠ 0 :=
      ne_zero_of_dvd_ne_zero (hS I hI) (idealQuotient_dvd (hdiv I hI))
    have hbound (I : Ideal O) (hI : I ∈ S) := idealQuotient_norm_le hs (hdiv I hI) Y (hN I hI)
    obtain ⟨I,hI⟩ := hempty
    have hscale : 1 ≤ Y/(Ideal.absNorm s : ℝ) := by
      have hn : (1:ℝ) ≤ Ideal.absNorm (idealQuotient s I) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hquot I hI))
      exact hn.trans (hbound I hI)
    have hc := DescentFiberCost.finite_ideal_count_real (S.image (idealQuotient s)) _ hscale
      (by intro J hJ; obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ; exact hquot I hI)
      (by intro J hJ; obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ; exact hbound I hI)
    rw [Finset.card_image_of_injOn (fun I hI J hJ he => idealQuotient_injective_on s
      (hdiv I hI) (hdiv J hJ) he)] at hc
    convert hc using 1 ; ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hempty,Finset.card_empty,Nat.cast_zero]
    positivity

def secondZeroEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) : ℂ :=
  ∑ i ∈ S, ∑ j ∈ S, (c i*star (c j)) *
    (actualCorrelation (a i) (a j) (ha i) (ha j) 0 /
      ((Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ) : ℂ)*
       (Real.sqrt (Ideal.absNorm (Ideal.span {a j}) : ℝ) : ℂ)))

theorem secondZeroEnergy_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hp : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hinj : Set.InjOn a S) (c : α → ℂ) :
    ‖secondZeroEnergy S a ha c‖ ≤ ∑ i ∈ S, ‖c i‖^2 := by
  have hroot (i : α) :
      ((Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ) : ℂ)*
       (Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ) : ℂ)) =
        (Ideal.absNorm (Ideal.span {a i}) : ℂ) := by
    rw [← Complex.ofReal_mul,Real.mul_self_sqrt (Nat.cast_nonneg _),Complex.ofReal_natCast]
  have he : secondZeroEnergy S a ha c =
      ∑ i ∈ S, (c i*star (c i)) *
        (actualCorrelation (a i) (a i) (ha i) (ha i) 0 /(Ideal.absNorm (Ideal.span {a i}) : ℂ)) := by
    unfold secondZeroEnergy
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · rw [hroot]
    · intro j hj hji
      have hne : a i ≠ a j := fun he => hji (hinj hi hj he).symm
      rw [actual_zero_off_diagonal _ _ (ha i) (ha j) (hp i) (hp j) hne,zero_div,mul_zero]
    · exact fun hnot => False.elim (hnot hi)
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul,norm_mul,norm_star,norm_div,Complex.norm_natCast,← pow_two]
  have hN : 0 < (Ideal.absNorm (Ideal.span {a i}) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (ha i).1)
  exact mul_le_of_le_one_right (sq_nonneg _) ((div_le_one hN).mpr (actual_same_zero_norm_le _ (ha i)))

theorem primary_column_card {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hp : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hinj : Set.InjOn a S) (s : Ideal O) (hs : s ≠ 0)
    (hdiv : ∀ i ∈ S, s ∣ Ideal.span {a i}) (Y : ℝ) (hY : 0 ≤ Y)
    (hN : ∀ i ∈ S, (Ideal.absNorm (Ideal.span {a i}) : ℝ) ≤ Y) :
    (S.card : ℝ) ≤ 128*Y/(Ideal.absNorm s : ℝ) := by
  have hspan : Set.InjOn (fun i => (Ideal.span {a i} : Ideal O)) S := by
    intro i hi j hj he
    dsimp only at he
    apply hinj hi hj
    rw [← primaryGenerator_span (a i) (supported_element_ne_zero _ (ha i)) (hp i),
      ← primaryGenerator_span (a j) (supported_element_ne_zero _ (ha j)) (hp j),he]
  have hb := divisible_ideal_card (S.image (fun i => Ideal.span {a i})) s hs
    (by intro I hI; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI; exact (ha i).1)
    (by intro I hI; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI; exact hdiv i hi)
    Y hY (by intro I hI; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI; exact hN i hi)
  rwa [Finset.card_image_of_injOn hspan] at hb

theorem secondZeroEnergy_divisor_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hp : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hinj : Set.InjOn a S) (c : α → ℂ) (B : ℝ) (_hB : 0 ≤ B)
    (hc : ∀ i ∈ S, ‖c i‖ ≤ B) (s : Ideal O) (hs : s ≠ 0)
    (hdiv : ∀ i ∈ S, s ∣ Ideal.span {a i}) (Y : ℝ) (hY : 0 ≤ Y)
    (hN : ∀ i ∈ S, (Ideal.absNorm (Ideal.span {a i}) : ℝ) ≤ Y) :
    ‖secondZeroEnergy S a ha c‖ ≤ 128*B^2*Y/(Ideal.absNorm s : ℝ) := by
  calc
    _ ≤ ∑ i ∈ S, ‖c i‖^2 := secondZeroEnergy_bound S a ha hp hinj c
    _ ≤ ∑ _i ∈ S, B^2 := Finset.sum_le_sum (fun i hi =>
      pow_le_pow_left₀ (norm_nonneg _) (hc i hi) 2)
    _ = B^2*(S.card : ℝ) := by simp [mul_comm]
    _ ≤ B^2*(128*Y/(Ideal.absNorm s : ℝ)) :=
      mul_le_mul_of_nonneg_left (primary_column_card S a ha hp hinj s hs hdiv Y hY hN) (sq_nonneg _)
    _ = _ := by ring

theorem normalized_secondZeroEnergy_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hp : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hinj : Set.InjOn a S) (c : α → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hc : ∀ i ∈ S, ‖c i‖ ≤ B) (s : Ideal O) (hs : s ≠ 0)
    (hdiv : ∀ i ∈ S, s ∣ Ideal.span {a i}) (Y : ℝ) (hY : 0 ≤ Y)
    (hN : ∀ i ∈ S, (Ideal.absNorm (Ideal.span {a i}) : ℝ) ≤ Y)
    (κ : ℂ) (T : ℝ) (hT : 0 < T) :
    ‖(κ/(T:ℂ))*secondZeroEnergy S a ha c‖ ≤
      128*‖κ‖*B^2*Y/(T*(Ideal.absNorm s : ℝ)) := by
  rw [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hT]
  calc
    _ ≤ (‖κ‖/T)*(128*B^2*Y/(Ideal.absNorm s : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (secondZeroEnergy_divisor_bound S a ha hp hinj c B hB hc s hs hdiv Y hY hN)
        (div_nonneg (norm_nonneg _) hT.le)
    _ = _ := by ring

end SevenEighths.CenteredMomentSecondDiagonal

end

end OAI
