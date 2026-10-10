import OAI.NumberTheory.DirichletL.Moments.AllocatedChildCapacity
import OAI.NumberTheory.DirichletL.Energy.InputParentCapacity
import OAI.NumberTheory.DirichletL.Moments.FirstSecondCapacityDefect

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyDeletedChildCapacity
open HeckeFamily CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedChildCapacity
open CenteredMomentRetainedProfile CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentDivisorRaw CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity
open CenteredMomentFirstSecondCapacityLedger CenteredMomentLiveCapacity
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma deletion_norm (F : Finset (Ideal O)) (hF : ∀I∈F,I≠0) :
    (1:ℝ) ≤ (∏I∈F,I).absNorm := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Finset.prod_ne_zero_iff.mpr hF))

lemma prime_deletion_norm (F : Finset (Ideal O)) (hF : ∀I∈F,Prime I) :
    (1:ℝ) ≤ (∏I∈F,I).absNorm :=
  deletion_norm F (fun I hI=>(hF I hI).ne_zero)

def postmaskLength (Z U : ℝ) (F : Finset (Ideal O)) : ℝ :=
  length Z (clippedScale U/((∏I∈F,I).absNorm:ℝ))

lemma postmaskLength_eq (Z U : ℝ) (F : Finset (Ideal O))
    (hZ : 1<Z) (hF : ∀I∈F,I≠0) :
    postmaskLength Z U F=Real.logb Z (clippedScale U)-
      min (Real.logb Z ((∏I∈F,I).absNorm:ℝ)) (Real.logb Z (clippedScale U)) :=
  postmask_length Z U _ hZ (deletion_norm F hF)

lemma postmaskLength_le (Z U : ℝ) (F : Finset (Ideal O))
    (hZ : 1<Z) (hF : ∀I∈F,I≠0) :
    postmaskLength Z U F≤Real.logb Z (clippedScale U) :=
  postmask_length_le Z U _ hZ (deletion_norm F hF)

lemma postmaskLength_nonneg (Z U : ℝ) (F : Finset (Ideal O)) (hZ : 1<Z) :
    0≤postmaskLength Z U F := length_nonneg Z _ hZ

theorem child_survives (χ : Character) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (t X₁ X₂ : ℝ) (h₁ : 0<X₁) (h₂ : 0<X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hne : child χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0) :
    1≤rawScale D a X₁ 0*V₁.b ∧ 1≤rawScale D a X₂ 1*V₂.b := by
  unfold child at hne
  have hp:=left_ne_zero_of_mul hne
  exact ⟨profile_polynomial_survives χ V₁ _ (rawScale_pos D a X₁ h₁ 0) t _ 0 0
    (left_ne_zero_of_mul hp),
    profile_polynomial_survives χ V₂ _ (rawScale_pos D a X₂ h₂ 1) t _ 0 0
      (right_ne_zero_of_mul hp)⟩

def deletedExcess (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ M : ℝ) (P : ι→ℝ) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι) : ℝ :=
  excess (liveIndices D a\J) (fun i=>Real.logb Z (P i))
    (postmaskLength Z (rawScale D a X₁ 0) F₁)
    (postmaskLength Z (rawScale D a X₂ 1) F₂) M κ

lemma deletedExcess_le (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ M : ℝ) (P : ι→ℝ) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0) :
    deletedExcess D a Z X₁ X₂ κ M P F₁ F₂ J≤
      max (plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M) 0 := by
  have h₁:=postmaskLength_le Z (rawScale D a X₁ 0) F₁ hZ hF₁
  have h₂:=postmaskLength_le Z (rawScale D a X₂ 1) F₂ hZ hF₂
  have hsum:(∑i∈liveIndices D a\J,Real.logb Z (P i))≤remainingLogs D a Z P :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun i _ _=>Real.logb_nonneg hZ (hP i))
  have hh:=mul_le_mul_of_nonneg_left hsum (by positivity : 0≤6*κ)
  unfold deletedExcess excess plainLogs
  exact max_le_max (by linarith) le_rfl

theorem child_excess_from_parent (χ : Character) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (t Z X₁ X₂ κ A M Mnom Mactual w ell δ θ : ℝ)
    (h₁ : 0<X₁) (h₂ : 0<X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hne : child χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0)
    (hparent : A+(6*κ-1)*(∑i,Real.logb Z (P i))≤M)
    (hshift : Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤A-M+6*(w+ell)+δ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ) :
    deletedExcess D a Z X₁ X₂ κ Mactual P F₁ F₂ J≤
      max (6*(w+ell)+δ+2*θ+Mnom-Mactual) 0 := by
  obtain ⟨hs₁,hs₂⟩:=child_survives χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J hne
  apply (deletedExcess_le D a Z X₁ X₂ κ Mactual P F₁ F₂ J hZ hκ hP hF₁ hF₂).trans
  apply (excess_le_remaining D a Z X₁ X₂ V₁.b V₂.b κ Mactual hZ h₁ h₂ P
    (fun i=>zero_lt_one.trans_le (hP i)) hs₁ hs₂).trans
  apply max_le_max _ le_rfl
  have hr:=affine_reduction_le_parent D a Z κ hZ hκ P hP
  linarith

theorem child_paid_width (χ : Character) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (t Z X₁ X₂ κ A M Mnom Mactual w ell δ₁ δ₂ θ : ℝ)
    (h₁ : 0<X₁) (h₂ : 0<X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hne : child χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0)
    (hparent : A+(6*κ-1)*(∑i,Real.logb Z (P i))≤M)
    (hshift : Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤A-M+6*(w+ell)+δ₁)
    (hwidth : Mactual-Mnom≤δ₂) (hw : 0≤w) (hell : 0≤ell)
    (hδ₁ : 0≤δ₁) (hδ₂ : 0≤δ₂) (hθ : 0≤θ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ) :
    Mactual+deletedExcess D a Z X₁ X₂ κ Mactual P F₁ F₂ J/6≤
      Mnom+δ₂+w+ell+δ₁/6+θ/3 := by
  have he:=child_excess_from_parent χ D a V₁ V₂ pool β P t Z X₁ X₂ κ A M Mnom Mactual
    w ell δ₁ θ h₁ h₂ F₁ F₂ J hZ hκ hP hF₁ hF₂ hne hparent hshift hclip
  have hh:=width_defect_cost (Mactual-Mnom) (6*(w+ell)+δ₁+2*θ) δ₂
    (by positivity) hδ₂ hwidth
  rw [show 6*(w+ell)+δ₁+2*θ-(Mactual-Mnom)=6*(w+ell)+δ₁+2*θ+Mnom-Mactual by ring] at hh
  linarith

lemma eventually_endpoint_cost (b₁ b₂ θ : ℝ) (hθ : 0<θ) :
    ∀ᶠ Z : ℝ in Filter.atTop,1<Z ∧ Real.logb Z (max 1 b₁*max 1 b₂)≤2*θ :=
  CenteredMomentCommonMaskChildCapacity.eventually_fixed_clipping_cost b₁ b₂ (2*θ) (by positivity)

theorem paired_child_excess (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (Z X₁ X₂ Y₁ Y₂ κ A M Mnom Mactual w ell δ θ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hsame : Y₁*Y₂=X₁*X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hparent : A+(6*κ-1)*(∑i,Real.logb Z (P i))≤M)
    (hshift : Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤A-M+6*(w+ell)+δ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ) :
    (∀χ t,child χ D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J≠0 →
      deletedExcess D a Z X₁ X₂ κ Mactual P F₁ F₂ J≤
        max (6*(w+ell)+δ+2*θ+Mnom-Mactual) 0) ∧
    (∀χ t,child χ D a V₁ V₂ pool β P t Y₁ Y₂ hY₁ hY₂ F₁ F₂ J≠0 →
      deletedExcess D a Z Y₁ Y₂ κ Mactual P F₁ F₂ J≤
        max (6*(w+ell)+δ+2*θ+Mnom-Mactual) 0) := by
  constructor
  · intro χ t hn
    exact child_excess_from_parent χ D a V₁ V₂ pool β P t Z X₁ X₂ κ A M Mnom Mactual
      w ell δ θ hX₁ hX₂ F₁ F₂ J hZ hκ hP hF₁ hF₂ hn hparent hshift hclip
  · intro χ t hn
    apply child_excess_from_parent χ D a V₁ V₂ pool β P t Z Y₁ Y₂ κ A M Mnom Mactual
      w ell δ θ hY₁ hY₂ F₁ F₂ J hZ hκ hP hF₁ hF₂ hn hparent _ hclip
    simpa only [hsame] using hshift

theorem source_removal_width_cost (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (Z X₁ X₂ κ A M Mnom Mactual w ell δ₁ δ₂ θ mesh : ℝ)
    (h₁ : 0<X₁) (h₂ : 0<X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hparent : A+(6*κ-1)*(∑i,Real.logb Z (P i))≤M)
    (hshift : Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤A-M+6*(w+ell)+δ₁)
    (hwidth : Mactual-Mnom≤δ₂) (hw : 0≤w) (hell : 0≤ell)
    (hδ₁ : 0≤δ₁) (hδ₂ : 0≤δ₂) (hθ : 0≤θ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ)
    (hm : 0≤mesh) (hmesh : ∀i∈liveIndices D a\J,Real.logb Z (P i)≤mesh) :
    ∃removed : Finset ι,removed⊆liveIndices D a\J ∧
      (removed=liveIndices D a\J ∨
        postmaskLength Z (rawScale D a X₁ 0) F₁+
        postmaskLength Z (rawScale D a X₂ 1) F₂+
        6*κ*(∑i∈(liveIndices D a\J)\removed,Real.logb Z (P i))≤Mactual) ∧
      ∀χ t,child χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0 →
        Mactual-Mnom+κ*(∑i∈removed,Real.logb Z (P i))≤
          δ₂+w+ell+δ₁/6+θ/3+κ*mesh := by
  by_cases hk : κ=0
  · refine ⟨liveIndices D a\J,Finset.Subset.refl _,Or.inl rfl,?_⟩
    intro χ t _
    simp only [hk,zero_mul,add_zero]
    linarith
  have hkpos : 0<κ := lt_of_le_of_ne hκ (Ne.symm hk)
  obtain ⟨removed,hr,hcap,hcost⟩:=removal_excess_cost (liveIndices D a\J)
    (fun i=>Real.logb Z (P i))
    (postmaskLength Z (rawScale D a X₁ 0) F₁)
    (postmaskLength Z (rawScale D a X₂ 1) F₂) Mactual κ mesh hkpos hm
    (fun i _=>Real.logb_nonneg hZ (hP i)) hmesh
  refine ⟨removed,hr,hcap,?_⟩
  intro χ t hn
  have hp:=child_paid_width χ D a V₁ V₂ pool β P t Z X₁ X₂ κ A M Mnom Mactual
    w ell δ₁ δ₂ θ h₁ h₂ F₁ F₂ J hZ hκ hP hF₁ hF₂ hn hparent hshift
    hwidth hw hell hδ₁ hδ₂ hθ hclip
  change κ*(∑i∈removed,Real.logb Z (P i))≤
    deletedExcess D a Z X₁ X₂ κ Mactual P F₁ F₂ J/6+κ*mesh at hcost
  linarith

lemma postmask_scale_pos (U : ℝ) (F : Finset (Ideal O)) (hF : ∀I∈F,I≠0) :
    0<clippedScale U/((∏I∈F,I).absNorm:ℝ) :=
  div_pos (zero_lt_one.trans_le (clippedScale_ge_one U))
    (zero_lt_one.trans_le (deletion_norm F hF))

theorem input_parent_child_excess (s : CenteredMomentCommonRadialData.Input ι)
    (χ : Character) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (V₁ V₂ : Plain)
    (t Z X₁ X₂ κ M Mnom Mactual w ell δ θ : ℝ)
    (h₁ : 0<X₁) (h₂ : 0<X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤s.P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hne : child χ D a V₁ V₂ s.slots s.coefficient s.P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0)
    (hparent : length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M)
    (hshift : Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤
      Real.logb Z (CenteredMomentAmplificationChildInput.volume s)-M+6*(w+ell)+δ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ) :
    deletedExcess D a Z X₁ X₂ κ Mactual s.P F₁ F₂ J≤
      max (6*(w+ell)+δ+2*θ+Mnom-Mactual) 0 :=
  child_excess_from_parent χ D a V₁ V₂ s.slots s.coefficient s.P t Z X₁ X₂ κ
    (Real.logb Z (CenteredMomentAmplificationChildInput.volume s)) M Mnom Mactual w ell δ θ
    h₁ h₂ F₁ F₂ J hZ hκ hP hF₁ hF₂ hne
    (input_affine_capacity s Z κ M hZ hparent) hshift hclip

end SevenEighths.CenteredMomentEnergyDeletedChildCapacity

end

end OAI
