import OAI.NumberTheory.DirichletL.Moments.DivisorSlots

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorBoundary
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def frozenSlots (D : Ideal O) (s slots : Finset ι) (a : Allocation D s) : Finset ι :=
  slots.filter (fun i => (selectedPrimes D s a i).Nonempty)

def extractedProduct (D : Ideal O) (s plain slots : Finset ι) (a : Allocation D s)
    (v : ι → Ideal O) : Ideal O :=
  (∏ i ∈ plain,selectedDivisor D s a i)*(∏ i ∈ frozenSlots D s slots a,v i)

theorem divisor_dvd_extractedProduct (D : Ideal O) (hD : Squarefree D)
    (s plain slots : Finset ι) (hs : s ⊆ plain ∪ slots)
    (a : Allocation D s) (v : ι → Ideal O) (hn : allocationTerm D s v a ≠ 0) :
    D∣extractedProduct D s plain slots a v := by
  apply (squarefree_dvd_iff _ _ hD).mpr
  intro P hP
  let PP : primeSupport D := ⟨P,hP⟩
  have hne : (a PP).val.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (Finset.mem_erase.mp (a PP).property).1
  obtain ⟨i,hi⟩ := hne
  have his : i ∈ s := (Finset.mem_powerset.mp (Finset.mem_of_mem_erase (a PP).property)) hi
  have hip : PP ∈ selectedPrimes D s a i := Finset.mem_filter.mpr ⟨Finset.mem_univ PP,hi⟩
  rcases Finset.mem_union.mp (hs his) with hp | hslot
  · apply dvd_mul_of_dvd_left
    exact (Finset.dvd_prod_of_mem (fun Q : primeSupport D => (Q:Ideal O)) hip).trans
      (Finset.dvd_prod_of_mem (fun i => selectedDivisor D s a i) hp)
  · apply dvd_mul_of_dvd_right
    exact (selected_divides_factor D s v a hn PP i hi).trans
      (Finset.dvd_prod_of_mem v (Finset.mem_filter.mpr ⟨hslot,⟨PP,hip⟩⟩))

theorem extractedProduct_ne_zero (D : Ideal O) (s plain slots : Finset ι)
    (a : Allocation D s) (v : ι → Ideal O) (hv : ∀ i ∈ slots,v i ≠ 0) :
    extractedProduct D s plain slots a v ≠ 0 :=
  mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _ => selectedDivisor_ne_zero D s a i))
    (Finset.prod_ne_zero_iff.mpr (fun i hi => hv i (Finset.mem_filter.mp hi).1))

theorem actual_divisor_norm_boundary (D : Ideal O) (hD : Squarefree D)
    (s plain slots : Finset ι) (hs : s ⊆ plain ∪ slots)
    (a : Allocation D s) (v : ι → Ideal O) (hn : allocationTerm D s v a ≠ 0)
    (hv : ∀ i ∈ slots,v i ≠ 0) :
    Ideal.absNorm D ≤ (∏ i ∈ plain,Ideal.absNorm (selectedDivisor D s a i))*
      (∏ i ∈ frozenSlots D s slots a,Ideal.absNorm (v i)) := by
  have hd := divisor_dvd_extractedProduct D hD s plain slots hs a v hn
  have hnorm := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (extractedProduct_ne_zero D s plain slots a v hv))) (map_dvd Ideal.absNorm hd)
  simpa only [extractedProduct,map_mul,map_prod] using hnorm

theorem actual_divisor_log_boundary (D : Ideal O) (hD : Squarefree D)
    (s plain slots : Finset ι) (hs : s ⊆ plain ∪ slots)
    (a : Allocation D s) (v : ι → Ideal O) (hn : allocationTerm D s v a ≠ 0)
    (hv : ∀ i ∈ slots,v i ≠ 0) (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤
      (∑ i ∈ plain,Real.logb Z (Ideal.absNorm (selectedDivisor D s a i):ℝ))+
      (∑ i ∈ frozenSlots D s slots a,Real.logb Z (Ideal.absNorm (v i):ℝ)) := by
  have hnorm : (Ideal.absNorm D:ℝ) ≤
      (∏ i ∈ plain,(Ideal.absNorm (selectedDivisor D s a i):ℝ))*
      (∏ i ∈ frozenSlots D s slots a,(Ideal.absNorm (v i):ℝ)) := by
    exact_mod_cast actual_divisor_norm_boundary D hD s plain slots hs a v hn hv
  have hp (i : ι) : (Ideal.absNorm (selectedDivisor D s a i):ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (selectedDivisor_ne_zero D s a i))
  have hq (i : ι) (hi : i ∈ frozenSlots D s slots a) : (Ideal.absNorm (v i):ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hv i (Finset.mem_filter.mp hi).1))
  have hh := Real.logb_le_logb_of_le hZ (show (0:ℝ)<Ideal.absNorm D by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)) hnorm
  rw [Real.logb_mul (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
    (Finset.prod_ne_zero_iff.mpr hq), Real.logb_prod _ _ (fun i _ => hp i),
    Real.logb_prod _ _ hq] at hh
  exact hh

def formalReduction (D : Ideal O) (s plain slots : Finset ι) (a : Allocation D s)
    (P : ι → ℝ) (Z : ℝ) : ℝ :=
  (∑ i ∈ plain,Real.logb Z (Ideal.absNorm (selectedDivisor D s a i):ℝ))+
    ∑ i ∈ frozenSlots D s slots a,Real.logb Z (P i)

def frozenRatio (D : Ideal O) (s slots : Finset ι) (a : Allocation D s)
    (v : ι → Ideal O) (P : ι → ℝ) (Z : ℝ) : ℝ :=
  ∑ i ∈ frozenSlots D s slots a,Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i)

theorem formal_reduction_add_ratio (D : Ideal O) (s plain slots : Finset ι)
    (a : Allocation D s) (v : ι → Ideal O) (hv : ∀ i ∈ slots,v i ≠ 0)
    (P : ι → ℝ) (hP : ∀ i ∈ slots,0 < P i) (Z : ℝ) :
    formalReduction D s plain slots a P Z+frozenRatio D s slots a v P Z =
      (∑ i ∈ plain,Real.logb Z (Ideal.absNorm (selectedDivisor D s a i):ℝ))+
      (∑ i ∈ frozenSlots D s slots a,Real.logb Z (Ideal.absNorm (v i):ℝ)) := by
  unfold formalReduction frozenRatio
  rw [add_assoc,← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have his := (Finset.mem_filter.mp hi).1
  rw [Real.logb_div (Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hv i his))) (hP i his).ne']
  ring

theorem actual_formal_boundary (D : Ideal O) (hD : Squarefree D)
    (s plain slots : Finset ι) (hs : s ⊆ plain ∪ slots)
    (a : Allocation D s) (v : ι → Ideal O) (hn : allocationTerm D s v a ≠ 0)
    (hv : ∀ i ∈ slots,v i ≠ 0) (P : ι → ℝ) (hP : ∀ i ∈ slots,0 < P i)
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤
      formalReduction D s plain slots a P Z+frozenRatio D s slots a v P Z := by
  rw [formal_reduction_add_ratio D s plain slots a v hv P hP Z]
  exact actual_divisor_log_boundary D hD s plain slots hs a v hn hv Z hZ

theorem divisor_dyad_card (Ds : Finset (Ideal O)) (T : ℝ) (hT : 1 ≤ T)
    (hD : ∀ D ∈ Ds,D ≠ 0) (hN : ∀ D ∈ Ds,(Ideal.absNorm D:ℝ) < 2*T) :
    (Ds.card:ℝ) ≤ 256*T := by
  have h := DescentFiberCost.finite_ideal_count_real Ds (2*T) (by linarith) hD
    (fun D hD => (hN D hD).le)
  linarith

theorem paired_raw_divisor_bound (Ds : Finset (Ideal O)) (T Z θ : ℝ)
    (hT : 1 ≤ T) (hZ : 1 < Z) (r₁ r₂ w₁ w₂ : Ideal O → ℝ)
    (hD : ∀ D ∈ Ds,D ≠ 0)
    (hlo : ∀ D ∈ Ds,T ≤ (Ideal.absNorm D:ℝ))
    (hhi : ∀ D ∈ Ds,(Ideal.absNorm D:ℝ) < 2*T)
    (hleft : ∀ D ∈ Ds,Real.logb Z (Ideal.absNorm D:ℝ) ≤ r₁ D+w₁ D)
    (hright : ∀ D ∈ Ds,Real.logb Z (Ideal.absNorm D:ℝ) ≤ r₂ D+w₂ D)
    (hw : ∀ D ∈ Ds,w₁ D+w₂ D ≤ 2*θ) :
    (∑ D ∈ Ds,Z^(-(r₁ D+r₂ D)/2)) ≤ 256*Z^θ := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have he (D : Ideal O) (hmem : D ∈ Ds) : Z^(-(r₁ D+r₂ D)/2) ≤ Z^θ/T := by
    have hn := Real.logb_le_logb_of_le hZ hT0 (hlo D hmem)
    have h₁ := hleft D hmem
    have h₂ := hright D hmem
    have hω := hw D hmem
    have hh : -(r₁ D+r₂ D)/2 ≤ θ-Real.logb Z T := by linarith
    have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le hh
    rw [Real.rpow_sub hZ0,Real.rpow_logb hZ0 hZ.ne' hT0] at hpow
    exact hpow
  calc
    _ ≤ ∑ _D ∈ Ds,Z^θ/T := Finset.sum_le_sum (fun D hD => he D hD)
    _ = (Ds.card:ℝ)*(Z^θ/T) := by simp
    _ ≤ (256*T)*(Z^θ/T) := mul_le_mul_of_nonneg_right (divisor_dyad_card Ds T hT hD hhi) (by positivity)
    _ = _ := by field_simp

end SevenEighths.CenteredMomentDivisorBoundary

end

end OAI
