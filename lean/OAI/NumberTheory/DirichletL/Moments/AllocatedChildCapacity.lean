import OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalSource
import OAI.NumberTheory.DirichletL.Moments.CommonMaskChildCapacity
import OAI.NumberTheory.DirichletL.Moments.CommonRawScale
import OAI.NumberTheory.DirichletL.Moments.LiveCapacity

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentAllocatedChildCapacity
open HeckeFamily CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRaw CenteredMomentDivisorRetained CenteredMomentEligibleEnergy
open CenteredMomentCommonRadialData
local notation "O" => HeckeFamily.O

def clippingLoss (Z U₁ U₂ : ℝ) : ℝ :=
  max (-Real.logb Z U₁) 0+max (-Real.logb Z U₂) 0

lemma clipped_log (Z U : ℝ) (hZ : 1<Z) (hU : 0<U) :
    Real.logb Z (clippedScale U)=Real.logb Z U+max (-Real.logb Z U) 0 := by
  by_cases h : 1≤U
  · rw [clippedScale,max_eq_right h,max_eq_right (neg_nonpos.mpr (Real.logb_nonneg hZ h))]
    ring
  · have hu : U≤1 := (lt_of_not_ge h).le
    have hl : Real.logb Z U≤0 := Real.logb_nonpos hZ hU.le hu
    rw [clippedScale,max_eq_left hu,max_eq_left (neg_nonneg.mpr hl),Real.logb_one]
    ring

lemma clipped_pair_log (Z U₁ U₂ : ℝ) (hZ : 1<Z) (h₁ : 0<U₁) (h₂ : 0<U₂) :
    Real.logb Z (clippedScale U₁)+Real.logb Z (clippedScale U₂)=
      Real.logb Z U₁+Real.logb Z U₂+clippingLoss Z U₁ U₂ := by
  rw [clipped_log Z U₁ hZ h₁,clipped_log Z U₂ hZ h₂]
  unfold clippingLoss
  ring

lemma clipping_loss_bound (Z U₁ U₂ b₁ b₂ : ℝ) (hZ : 1<Z)
    (h₁ : 0<U₁) (h₂ : 0<U₂) (hs₁ : 1≤U₁*b₁) (hs₂ : 1≤U₂*b₂) :
    0≤clippingLoss Z U₁ U₂ ∧
      clippingLoss Z U₁ U₂≤Real.logb Z (max 1 b₁*max 1 b₂) := by
  have one (U b : ℝ) (hU : 0<U) (hs : 1≤U*b) :
      max (-Real.logb Z U) 0≤Real.logb Z (max 1 b) := by
    have hb : 0<max 1 b := zero_lt_one.trans_le (le_max_left _ _)
    have hc : clippedScale U≤max 1 b*U := by
      apply max_le
      · exact hs.trans (by nlinarith [le_max_right (1:ℝ) b])
      · nlinarith [le_max_left (1:ℝ) b]
    have hl := Real.logb_le_logb_of_le hZ
      (zero_lt_one.trans_le (clippedScale_ge_one U)) hc
    rw [clipped_log Z U hZ hU,Real.logb_mul hb.ne' hU.ne'] at hl
    linarith
  refine ⟨add_nonneg (le_max_right _ _) (le_max_right _ _),?_⟩
  rw [Real.logb_mul (ne_of_gt (zero_lt_one.trans_le (le_max_left (1:ℝ) b₁)))
    (ne_of_gt (zero_lt_one.trans_le (le_max_left (1:ℝ) b₂)))]
  exact add_le_add (one U₁ b₁ h₁ hs₁) (one U₂ b₂ h₂ hs₂)

lemma profile_polynomial_survives (χ : Character) (V : Plain) (U : ℝ) (hU : 0<U)
    (t X σ v : ℝ) (hn : HeckeDyadic.polynomial χ false (V.profile U hU t) X σ v≠0) :
    1≤U*V.b := by
  by_contra hs
  rw [V.profile_zero U hU t (lt_of_not_ge hs)] at hn
  exact hn (by simp [HeckeDyadic.polynomial,HeckeDyadic.summand])

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def plainLogs (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ : ℝ) : ℝ :=
  Real.logb Z (clippedScale (rawScale D a X₁ 0))+
    Real.logb Z (clippedScale (rawScale D a X₂ 1))

def remainingLogs (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z : ℝ) (P : ι→ℝ) : ℝ := ∑i∈liveIndices D a,Real.logb Z (P i)

def preVolume (s : Data ι) : ℝ := s.X₁*s.X₂*∏i,s.P i

omit [DecidableEq ι] in
lemma preVolume_pos (s : Data ι) : 0<preVolume s :=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

lemma selectedNorm_ge_one (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) :
    1≤selectedNorm D a := by
  have hn (j : Fin 2) : (1:ℝ)≤Ideal.absNorm (selectedPlain D a j) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  exact one_le_mul_of_one_le_of_one_le (hn 0) (hn 1)

lemma formalReduction_ge_one (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (P : ι→ℝ) (hP : ∀i,1≤P i) : 1≤formalReductionFactor D a P :=
  one_le_mul_of_one_le_of_one_le (selectedNorm_ge_one D a)
    (Finset.one_le_prod₀ (fun i _=>hP i))

lemma remainingLogs_le (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z : ℝ) (hZ : 1<Z) (P : ι→ℝ) (hP : ∀i,1≤P i) :
    remainingLogs D a Z P≤∑i,Real.logb Z (P i) :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _=>Real.logb_nonneg hZ (hP i))

lemma raw_volume (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (X₁ X₂ : ℝ) (P : ι→ℝ) (hP : ∀i,0<P i) :
    rawScale D a X₁ 0*rawScale D a X₂ 1*(∏i∈liveIndices D a,P i)=
      (X₁*X₂*∏i,P i)/formalReductionFactor D a P := by
  have hr : 0<formalReductionFactor D a P :=
    mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>hP i))
  apply (eq_div_iff hr.ne').mpr
  simpa only [rawScale,div_mul_div_comm,rawRemaining,selectedNorm] using
    CenteredMomentDivisorRaw.raw_scale_identity D a (X₁*X₂) P

lemma raw_log_volume (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ : ℝ) (h₁ : 0<X₁) (h₂ : 0<X₂) (P : ι→ℝ) (hP : ∀i,0<P i) :
    Real.logb Z (rawScale D a X₁ 0)+Real.logb Z (rawScale D a X₂ 1)+remainingLogs D a Z P=
      Real.logb Z (X₁*X₂*∏i,P i)-Real.logb Z (formalReductionFactor D a P) := by
  have hr : 0<formalReductionFactor D a P :=
    mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>hP i))
  have hh := congrArg (Real.logb Z) (raw_volume D a X₁ X₂ P hP)
  rw [Real.logb_div (mul_pos (mul_pos h₁ h₂) (Finset.prod_pos (fun i _=>hP i))).ne' hr.ne',
    Real.logb_mul (mul_pos (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1)).ne'
      (Finset.prod_pos (fun i _=>hP i)).ne',
    Real.logb_mul (rawScale_pos D a X₁ h₁ 0).ne' (rawScale_pos D a X₂ h₂ 1).ne',
    Real.logb_prod _ _ (fun i _=>(hP i).ne')] at hh
  exact hh

theorem affine_exact (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ M : ℝ) (hZ : 1<Z) (h₁ : 0<X₁) (h₂ : 0<X₂)
    (P : ι→ℝ) (hP : ∀i,0<P i) :
    plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M=
      Real.logb Z (X₁*X₂*∏i,P i)-Real.logb Z (formalReductionFactor D a P)-M+
        (6*κ-1)*remainingLogs D a Z P+
        clippingLoss Z (rawScale D a X₁ 0) (rawScale D a X₂ 1) := by
  have hv := raw_log_volume D a Z X₁ X₂ h₁ h₂ P hP
  rw [plainLogs,clipped_pair_log Z _ _ hZ (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1)]
  nlinarith

theorem excess_le (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ b₁ b₂ κ M : ℝ) (hZ : 1<Z) (h₁ : 0<X₁) (h₂ : 0<X₂)
    (P : ι→ℝ) (hP : ∀i,1≤P i) (hκ : (1/6:ℝ)≤κ)
    (hs₁ : 1≤rawScale D a X₁ 0*b₁) (hs₂ : 1≤rawScale D a X₂ 1*b₂) :
    max (plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M) 0≤
      max (Real.logb Z (X₁*X₂*∏i,P i)-Real.logb Z (formalReductionFactor D a P)-M+
        (6*κ-1)*(∑i,Real.logb Z (P i))+Real.logb Z (max 1 b₁*max 1 b₂)) 0 := by
  rw [affine_exact D a Z X₁ X₂ κ M hZ h₁ h₂ P (fun i=>zero_lt_one.trans_le (hP i))]
  have hc := (clipping_loss_bound Z _ _ b₁ b₂ hZ
    (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1) hs₁ hs₂).2
  have hp := mul_le_mul_of_nonneg_left (remainingLogs_le D a Z hZ P hP)
    (by linarith : 0≤6*κ-1)
  exact max_le_max (by linarith) le_rfl

theorem allocated_survives (s : Data ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (z : O)
    (X₁ X₂ : ℝ) (h₁ : 0<X₁) (h₂ : 0<X₂)
    (hne : allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0) :
    1≤rawScale D a X₁ 0*s.b₁ ∧ 1≤rawScale D a X₂ 1*s.b₂ := by
  have hz (hs : rawScale D a X₁ 0*s.b₁<1 ∨ rawScale D a X₂ 1*s.b₂<1) : False := by
    apply hne
    exact CenteredMomentCommonMaskEnergy.original_retained_zero s.η s.m s.A z _ _ _ _
      s.support₁ s.support₂ (fun i : liveIndices D a=>s.slots i)
      (fun i : liveIndices D a=>s.coefficient i) (fun i : liveIndices D a=>s.P i)
      s.t _ _ (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1) hs
  constructor
  · exact le_of_not_gt (fun hh=>hz (Or.inl hh))
  · exact le_of_not_gt (fun hh=>hz (Or.inr hh))

theorem paired_capacity (s : Data ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z κ M : ℝ) (hZ : 1<Z) (hκ : (1/6:ℝ)≤κ) (hP : ∀i,1≤s.P i) :
    let bound := max (Real.logb Z (preVolume s)-Real.logb Z (formalReductionFactor D a s.P)-M+
      (6*κ-1)*(∑i,Real.logb Z (s.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂)) 0
    (∀z,allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ s.X₁ s.X₂≠0 →
      max (plainLogs D a Z s.X₁ s.X₂+6*κ*remainingLogs D a Z s.P-M) 0≤bound) ∧
    (∀z,allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ s.Y₁ s.Y₂≠0 →
      max (plainLogs D a Z s.Y₁ s.Y₂+6*κ*remainingLogs D a Z s.P-M) 0≤bound) := by
  constructor
  · intro z hn
    obtain ⟨h₁,h₂⟩ := allocated_survives s D a z s.X₁ s.X₂ s.X₁_pos s.X₂_pos hn
    exact excess_le D a Z _ _ _ _ κ M hZ s.X₁_pos s.X₂_pos s.P hP hκ h₁ h₂
  · intro z hn
    obtain ⟨h₁,h₂⟩ := allocated_survives s D a z s.Y₁ s.Y₂ s.Y₁_pos s.Y₂_pos hn
    have hb := excess_le D a Z _ _ _ _ κ M hZ s.Y₁_pos s.Y₂_pos s.P hP hκ h₁ h₂
    simpa only [s.same_product,preVolume] using hb

omit [DecidableEq ι] in
theorem common_preVolume (s : Input ι) (C R : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C) :
    preVolume (commonData s C R B)=preVolume s.toData/
      CenteredMomentCommonRawScale.rawReduction B.val s.P := by
  have hr := CenteredMomentCommonRawScale.rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  apply (eq_div_iff hr.ne').mpr
  simpa only [preVolume,commonData,div_mul_div_comm,
    CenteredMomentCommonRawScale.remainingRaw,CenteredMomentCommonRawScale.plainNorm] using
      CenteredMomentCommonRawScale.raw_scale_identity B.val (alloc_ne s C B) (s.X₁*s.X₂) s.P

omit [DecidableEq ι] in
lemma common_reduction_ge_one (s : Input ι) (C : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C) (hP : ∀i,1≤s.P i) :
    1≤CenteredMomentCommonRawScale.rawReduction B.val s.P := by
  have hn (j : ι⊕Fin 2) : (1:ℝ)≤Ideal.absNorm (B.val j) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (alloc_ne s C B j))
  apply one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (hn (Sum.inr 0)) (hn (Sum.inr 1)))
  apply Finset.one_le_prod₀
  intro i _
  unfold CenteredMomentCommonRawScale.frozenScale
  split_ifs
  · exact le_rfl
  · exact hP i

omit [DecidableEq ι] in
lemma common_slot_logs_le (s : Input ι) (C : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C)
    (Z : ℝ) (hZ : 1<Z) (hP : ∀i,1≤s.P i) :
    (∑i : CenteredMomentCommonProfile.liveIndices B.val,Real.logb Z (s.P i))≤
      ∑i,Real.logb Z (s.P i) := by
  rw [Finset.sum_coe_sort (CenteredMomentCommonProfile.liveIndices B.val) (fun i : ι=>Real.logb Z (s.P i))]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _=>Real.logb_nonneg hZ (hP i))

theorem common_allocated_raw_volume (s : Input ι) (C R : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C)
    (D : Ideal O) (a : Allocation D
      (Finset.univ : Finset ((CenteredMomentCommonProfile.liveIndices B.val)⊕Fin 2))) :
    let v := commonData s C R B
    let result := preVolume s.toData/(CenteredMomentCommonRawScale.rawReduction B.val s.P*
      formalReductionFactor D a v.P)
    rawScale D a v.X₁ 0*rawScale D a v.X₂ 1*(∏i∈liveIndices D a,v.P i)=result ∧
      rawScale D a v.Y₁ 0*rawScale D a v.Y₂ 1*(∏i∈liveIndices D a,v.P i)=result := by
  dsimp only
  have hx := raw_volume D a (commonData s C R B).X₁ (commonData s C R B).X₂
    (commonData s C R B).P (commonData s C R B).P_pos
  have hy := raw_volume D a (commonData s C R B).Y₁ (commonData s C R B).Y₂
    (commonData s C R B).P (commonData s C R B).P_pos
  change _=preVolume (commonData s C R B)/_ at hx
  rw [common_preVolume s C R B,div_div] at hx
  rw [(commonData s C R B).same_product] at hy
  change _=preVolume (commonData s C R B)/_ at hy
  rw [common_preVolume s C R B,div_div] at hy
  exact ⟨hx,hy⟩

theorem common_paired_capacity (s : Input ι) (C R : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C)
    (D : Ideal O) (a : Allocation D
      (Finset.univ : Finset ((CenteredMomentCommonProfile.liveIndices B.val)⊕Fin 2)))
    (Z κ M : ℝ) (hZ : 1<Z) (hκ : (1/6:ℝ)≤κ) (hP : ∀i,1≤s.P i) :
    let v := commonData s C R B
    let bound := max (Real.logb Z (preVolume s.toData)-
      Real.logb Z (CenteredMomentCommonRawScale.rawReduction B.val s.P)-
      Real.logb Z (formalReductionFactor D a v.P)-M+
      (6*κ-1)*(∑i,Real.logb Z (s.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂)) 0
    (∀z,allocatedPositiveRow v.η v.m v.A z v.t v.slots v.coefficient v.P D a
      v.W₁ v.W₂ v.X₁ v.X₂≠0 →
      max (plainLogs D a Z v.X₁ v.X₂+6*κ*remainingLogs D a Z v.P-M) 0≤bound) ∧
    (∀z,allocatedPositiveRow v.η v.m v.A z v.t v.slots v.coefficient v.P D a
      v.W₁ v.W₂ v.Y₁ v.Y₂≠0 →
      max (plainLogs D a Z v.Y₁ v.Y₂+6*κ*remainingLogs D a Z v.P-M) 0≤bound) := by
  dsimp only
  obtain ⟨hx,hy⟩ := paired_capacity (commonData s C R B) D a Z κ M hZ hκ (fun i=>hP i)
  have hv : Real.logb Z (preVolume (commonData s C R B))=
      Real.logb Z (preVolume s.toData)-Real.logb Z (CenteredMomentCommonRawScale.rawReduction B.val s.P) := by
    rw [common_preVolume s C R B,Real.logb_div (preVolume_pos s.toData).ne'
      (CenteredMomentCommonRawScale.rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos).ne']
  have hl := mul_le_mul_of_nonneg_left (common_slot_logs_le s C B Z hZ hP)
    (by linarith : 0≤6*κ-1)
  have hb : max (Real.logb Z (preVolume (commonData s C R B))-
      Real.logb Z (formalReductionFactor D a (commonData s C R B).P)-M+
      (6*κ-1)*(∑i,Real.logb Z ((commonData s C R B).P i))+
      Real.logb Z (max 1 (commonData s C R B).b₁*max 1 (commonData s C R B).b₂)) 0≤
      max (Real.logb Z (preVolume s.toData)-
        Real.logb Z (CenteredMomentCommonRawScale.rawReduction B.val s.P)-
        Real.logb Z (formalReductionFactor D a (commonData s C R B).P)-M+
        (6*κ-1)*(∑i,Real.logb Z (s.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂)) 0 := by
    rw [hv]
    apply max_le_max _ le_rfl
    change _≤Real.logb Z (preVolume s.toData)-
      Real.logb Z (CenteredMomentCommonRawScale.rawReduction B.val s.P)-
      Real.logb Z (formalReductionFactor D a (commonData s C R B).P)-M+
      (6*κ-1)*(∑i,Real.logb Z (s.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂)
    dsimp only [commonData]
    linarith
  exact ⟨fun z hz=>(hx z hz).trans hb,fun z hz=>(hy z hz).trans hb⟩

theorem excess_le_remaining (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ b₁ b₂ κ M : ℝ) (hZ : 1<Z) (h₁ : 0<X₁) (h₂ : 0<X₂)
    (P : ι→ℝ) (hP : ∀i,0<P i)
    (hs₁ : 1≤rawScale D a X₁ 0*b₁) (hs₂ : 1≤rawScale D a X₂ 1*b₂) :
    max (plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M) 0≤
      max (Real.logb Z (X₁*X₂*∏i,P i)-Real.logb Z (formalReductionFactor D a P)-M+
        (6*κ-1)*remainingLogs D a Z P+Real.logb Z (max 1 b₁*max 1 b₂)) 0 := by
  rw [affine_exact D a Z X₁ X₂ κ M hZ h₁ h₂ P hP]
  have hc := (clipping_loss_bound Z _ _ b₁ b₂ hZ
    (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1) hs₁ hs₂).2
  exact max_le_max (by linarith) le_rfl

theorem allocated_clipping (s : Data ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (z : O)
    (Z X₁ X₂ : ℝ) (hZ : 1<Z) (h₁ : 0<X₁) (h₂ : 0<X₂)
    (hne : allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0) :
    plainLogs D a Z X₁ X₂=Real.logb Z (rawScale D a X₁ 0)+Real.logb Z (rawScale D a X₂ 1)+
      clippingLoss Z (rawScale D a X₁ 0) (rawScale D a X₂ 1) ∧
    0≤clippingLoss Z (rawScale D a X₁ 0) (rawScale D a X₂ 1) ∧
    clippingLoss Z (rawScale D a X₁ 0) (rawScale D a X₂ 1)≤Real.logb Z (max 1 s.b₁*max 1 s.b₂) := by
  obtain ⟨hs₁,hs₂⟩ := allocated_survives s D a z X₁ X₂ h₁ h₂ hne
  exact ⟨clipped_pair_log Z _ _ hZ (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1),
    clipping_loss_bound Z _ _ _ _ hZ (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1) hs₁ hs₂⟩

lemma native_excess (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ M : ℝ) (P : ι→ℝ) :
    CenteredMomentLiveCapacity.excess (liveIndices D a) (fun i=>Real.logb Z (P i))
      (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
      (Real.logb Z (clippedScale (rawScale D a X₂ 1))) M κ=
      max (plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M) 0 := rfl

end SevenEighths.CenteredMomentAllocatedChildCapacity

end

end OAI
