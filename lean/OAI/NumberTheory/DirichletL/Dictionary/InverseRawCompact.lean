import OAI.NumberTheory.DirichletL.Dictionary.InverseRawEnergy
import OAI.NumberTheory.DirichletL.Moments.OriginalReflectionErrorMass

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.DetectorDictionaryInverseRawCompact
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment FourierBridge HeckePrimeAnnular
open CenteredMomentOriginalReflectionErrorMass CenteredMomentCounting
open ActualEisensteinCubic ConcreteTraceCRT

local notation "O" => HeckeFamily.O

lemma inverse_polynomial_all_ideals (χ : Character) (W : ℝ→ℂ) (D freq : ℝ) :
    polynomial χ true W D 0 freq =
      (D:ℂ)^(-(1/2:ℂ))*∑'I:Ideal O,coefficient χ true I*annularWeight W D 0 freq I := by
  unfold polynomial
  congr 1
  have he : (∑'I:HeckeDyadic.NonzeroIdeal,coefficient χ true I.val*annularWeight W D 0 freq I.val)=
      ∑'I:Ideal O,coefficient χ true I*annularWeight W D 0 freq I := by
    apply tsum_subtype_eq_of_support_subset (s:={I:Ideal O|I≠0})
      (f:=fun I:Ideal O=>coefficient χ true I*annularWeight W D 0 freq I)
    intro I hI hz
    subst I
    exact hI (by simp only [coefficient_zero,zero_mul])
  simpa only [summand,HeckeDyadic.norm,annularWeight,mul_assoc] using he

theorem inverse_polynomial_bound (χ : Character) (W : ℝ→ℂ) (b B D freq : ℝ)
    (hB : 0≤B) (hD : 0<D) (hW : ∀x,‖W x‖≤B)
    (hs : Function.support W⊆Set.Iic b) :
    ‖polynomial χ true W D 0 freq‖≤(128*max 1 b*B)*Real.sqrt D := by
  rw [inverse_polynomial_all_ideals]
  apply normalized_linear_bound D _ hD
  have hh:=norm_tsum_ideal_ball (fun I:Ideal O=>coefficient χ true I*annularWeight W D 0 freq I)
    (max 1 b*D) B (by positivity) hB (by
      change coefficient χ true (0:Ideal O)*_ = 0
      rw [coefficient_zero,zero_mul])
    (by
      intro I
      by_cases hI:I=0
      · subst I
        simpa only [coefficient_zero,zero_mul,norm_zero] using hB
      rw [norm_mul,annularWeight_zero_norm W D freq hD I hI]
      exact (mul_le_mul (coefficient_norm_le χ true I) (hW _) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul B))
    (by
      intro I hne
      have hw : W ((I.absNorm:ℝ)/D)≠0 := by
        intro hz
        exact hne (by simp only [annularWeight,hz,zero_mul,mul_zero])
      exact ((div_le_iff₀ hD).mp (hs hw)).trans
        (mul_le_mul_of_nonneg_right (le_max_right 1 b) hD.le))
  convert hh using 1; ring

lemma childLogTest_norm (W : ℝ→ℂ) (s x : ℝ) :
    ‖childLogTest W s x‖=‖W x‖ := by
  simp only [childLogTest,norm_mul,logPhase_norm,mul_one]

theorem inverse_reference_bound (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) :
    ∃A:ℝ,0<A ∧ ∀(χ:Character) (s D:ℝ),0<D →
      ‖polynomial χ true (childLogTest W s) D 0 0‖≤A*Real.sqrt D := by
  obtain ⟨B,hB,hbound⟩:=compact_norm_bound W a b ha hs W.continuous
  refine ⟨128*max 1 b*B,by positivity,?_⟩
  intro χ s D hD
  apply inverse_polynomial_bound χ (childLogTest W s) b B D 0 hB.le hD
  · intro x
    simpa only [childLogTest_norm] using hbound x
  · intro x hx
    have hw : W x≠0 := by
      intro hz
      exact hx (by simp only [childLogTest,hz,zero_mul])
    exact (hs hw).2

theorem nonzero_element_rows_card (rows : Finset NonzeroElement) (H : ℝ) (hH : 1≤H)
    (hrows : ∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) :
    (rows.card:ℝ)≤128*H := by
  have hh:=DescentFiberCost.finite_element_count_real (rows.image Subtype.val) H hH (by
    intro z hz
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact hrows v hv)
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
  exact hh

theorem reference_energy_linear (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) :
    ∃K:ℝ,0<K ∧ ∀(χ:NonzeroElement→Character) (rows:Finset NonzeroElement)
      (s H D:ℝ),1≤H → 0<D →
      (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) →
      (∑v∈rows,‖polynomial (χ v) true (childLogTest W s) D 0 0‖^2)≤K*H*D := by
  obtain ⟨A,hA,hbound⟩:=inverse_reference_bound W a b ha hs
  refine ⟨128*A^2,by positivity,?_⟩
  intro χ rows s H D hH hD hrows
  calc
    _≤∑v∈rows,A^2*D := by
      apply Finset.sum_le_sum
      intro v _
      have hh:=pow_le_pow_left₀ (norm_nonneg _) (hbound (χ v) s D hD) 2
      simpa only [mul_pow,Real.sq_sqrt hD.le] using hh
    _=(rows.card:ℝ)*(A^2*D) := by simp
    _≤(128*H)*(A^2*D) := mul_le_mul_of_nonneg_right
      (nonzero_element_rows_card rows H hH hrows) (by positivity)
    _=(128*A^2)*H*D := by ring

theorem subunit_rows_reference_energy (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) :
    ∃C0:ℝ,0<C0 ∧ ∀(χ:NonzeroElement→Character) (rows:Finset NonzeroElement)
      (s H D:ℝ),1≤H → 0<D → D≤1 →
      (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) →
      (∑v∈rows,‖polynomial (χ v) true (childLogTest W s) D 0 0‖^2)≤C0*H := by
  obtain ⟨K,hK,hbound⟩:=reference_energy_linear W a b ha hs
  refine ⟨K,hK,?_⟩
  intro χ rows s H D hH hD hD1 hrows
  exact (hbound χ rows s H D hH hD hrows).trans
    (mul_le_of_le_one_right (by positivity) hD1)

lemma scale_le_rows (c H D : ℝ) (hc : 0≤c) (hH : 1≤H)
    (_hD : 0<D) (hDH : D^(1+c)≤H) : D≤H := by
  by_cases hD1:D≤1
  · exact hD1.trans hH
  · have hd : 1≤D := le_of_not_ge hD1
    calc
      D=D^(1:ℝ) := (Real.rpow_one D).symm
      _≤D^(1+c) := Real.rpow_le_rpow_of_exponent_le hd (by linarith)
      _≤H := hDH

theorem small_rows_reference_energy (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (H0 : ℝ) (hH0 : 1≤H0) :
    ∃C0:ℝ,0<C0 ∧ ∀(χ:NonzeroElement→Character) (rows:Finset NonzeroElement)
      (s H D c:ℝ),1≤H → H≤H0 → 0≤c → 0<D → D^(1+c)≤H →
      (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) →
      (∑v∈rows,‖polynomial (χ v) true (childLogTest W s) D 0 0‖^2)≤C0*H := by
  obtain ⟨K,hK,hbound⟩:=reference_energy_linear W a b ha hs
  refine ⟨K*H0,by positivity,?_⟩
  intro χ rows s H D c hH hHH0 hc hD hDH hrows
  calc
    _≤K*H*D := hbound χ rows s H D hH hD hrows
    _≤K*H*H0 := mul_le_mul_of_nonneg_left ((scale_le_rows c H D hc hH hD hDH).trans hHH0)
      (by positivity)
    _=(K*H0)*H := by ring

lemma raw_majorant_ge_linear (C C0 H D κ s : ℝ) (J : ℕ)
    (hC : 0≤C) (hC0 : 0≤C0) (hH : 1≤H) (hκ : 0≤κ) :
    C0*H≤((C+C0)*(1+‖s‖)^(2*J))*H*(H*max 1 D)^κ := by
  have ht : 1≤(1+‖s‖)^(2*J) := one_le_pow₀ (by linarith [norm_nonneg s])
  have hb : 1≤H*max 1 D := hH.trans
    (le_mul_of_one_le_right (by positivity) (le_max_left _ _))
  have hp : 1≤(H*max 1 D)^κ := Real.one_le_rpow hb hκ
  calc
    C0*H≤(C+C0)*H := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _≤((C+C0)*(1+‖s‖)^(2*J))*H := mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (by positivity) ht) (by positivity)
    _≤_ := le_mul_of_one_le_right (by positivity) hp

theorem rawMoment_of_large_rows_ge_one (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (H0 : ℝ) (hH0 : 1≤H0) :
    ∃C0:ℝ,0<C0 ∧ ∀(data:RowData) (c κ C:ℝ) (J:ℕ),
      0≤c → 0≤κ → 0≤C →
      (∀(s H D:ℝ),H0≤H → 1≤D → D^(1+c)≤H →
        ∀rows:Finset NonzeroElement,
          (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) →
          (∑v∈rows,‖polynomial (data.character v) true (childLogTest W s) D 0 0‖^2)≤
            (C*(1+‖s‖)^(2*J))*H*(H*max 1 D)^κ) →
      ∀s:ℝ,RawMoment data (childLogTest W s) c κ ((C+C0)*(1+‖s‖)^(2*J)) := by
  obtain ⟨K,hK,hbound⟩:=reference_energy_linear W a b ha hs
  refine ⟨K*H0,by positivity,?_⟩
  intro data c κ C J hc hκ hC hlarge s H D hH hD hDH rows hrows
  have hsmall (hDH0:D≤H0) :
      (∑v∈rows,‖polynomial (data.character v) true (childLogTest W s) D 0 0‖^2)≤
        ((C+K*H0)*(1+‖s‖)^(2*J))*H*(H*max 1 D)^κ := by
    calc
      _≤K*H*D := hbound data.character rows s H D hH hD hrows
      _≤K*H*H0 := mul_le_mul_of_nonneg_left hDH0 (by positivity)
      _=(K*H0)*H := by ring
      _≤_ := raw_majorant_ge_linear C (K*H0) H D κ s J hC (by positivity) hH hκ
  by_cases hHH0:H≤H0
  · exact hsmall ((scale_le_rows c H D hc hH hD hDH).trans hHH0)
  by_cases hD1:D≤1
  · exact hsmall (hD1.trans hH0)
  · apply (hlarge s H D (le_of_not_ge hHH0) (le_of_not_ge hD1) hDH rows hrows).trans
    gcongr
    exact le_add_of_nonneg_right (by positivity)

theorem rawMoment_of_large_rows (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (H0 : ℝ) (hH0 : 1≤H0) :
    ∃C0:ℝ,0<C0 ∧ ∀(data:RowData) (c κ C:ℝ) (J:ℕ),
      0≤c → 0≤κ → 0≤C →
      (∀(s H D:ℝ),H0≤H → 0<D → D^(1+c)≤H →
        ∀rows:Finset NonzeroElement,
          (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) →
          (∑v∈rows,‖polynomial (data.character v) true (childLogTest W s) D 0 0‖^2)≤
            (C*(1+‖s‖)^(2*J))*H*(H*max 1 D)^κ) →
      ∀s:ℝ,RawMoment data (childLogTest W s) c κ ((C+C0)*(1+‖s‖)^(2*J)) := by
  obtain ⟨C0,hC0,hcomplete⟩:=rawMoment_of_large_rows_ge_one W a b ha hs H0 hH0
  refine ⟨C0,hC0,?_⟩
  intro data c κ C J hc hκ hC hlarge
  apply hcomplete data c κ C J hc hκ hC
  intro s H D hH hD hDH rows hrows
  exact hlarge s H D hH (zero_lt_one.trans_le hD) hDH rows hrows

end SevenEighths.DetectorDictionaryInverseRawCompact

end

end OAI
