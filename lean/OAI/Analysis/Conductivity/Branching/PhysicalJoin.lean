import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalBlockEnergy
import OAI.Analysis.Conductivity.Branching.PhysicalChildAttachedCorrection

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma physical_localized_jet_zero
    {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)
    (f : Fin 4 → Lp ℝ 2 (volume : Measure (Fin 3 → ℝ))) :
    let g : Fin 4 → Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
      Fin.cases (compactMultiplierCLM hχ.continuous hc (f 0))
        (fun i => compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
          (hc.fderiv_apply ℝ (Pi.single i 1)) (f 0) +
          compactMultiplierCLM hχ.continuous hc (f i.succ))
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∉tsupport χ → physicalFourJetCLM g x=0 := by
  intro g
  have h₀ := compactMultiplierCLM_ae hχ.continuous hc (f 0)
  have hᵢ (i : Fin 3) : g i.succ=ᵐ[volume] fun y =>
      fderiv ℝ χ y (Pi.single i 1)*f 0 y+χ y*f i.succ y := by
    apply (Lp.coeFn_add _ _).trans
    filter_upwards [compactMultiplierCLM_ae
      ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ (Pi.single i 1)) (f 0),
      compactMultiplierCLM_ae hχ.continuous hc (f i.succ)] with y h₁ h₂
    exact congrArg₂ (·+·) h₁ h₂
  have h₀' := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp h₀)
  have hᵢ' := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae (ae_all_iff.mpr hᵢ))
  filter_upwards [physicalFourJetCLM_ae g,h₀',hᵢ'] with x hx h₀x hᵢx hn
  rw [hx]
  dsimp only [Function.comp_apply] at h₀x
  have hχ0 := image_eq_zero_of_notMem_tsupport hn
  have hdχ0 := fderiv_of_notMem_tsupport ℝ hn
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change compactMultiplierCLM hχ.continuous hc (f 0) (WithLp.ofLp x)=0
    rw [h₀x,hχ0,zero_mul]
  · change g j.succ (WithLp.ofLp x)=0
    rw [hᵢx j]
    simp [hχ0,hdχ0]

lemma weak_jet_zero_of_val_zero (u : H1) {x : R3} (h : u.val x=0) :
    weakValue u x=0 ∧ ∀ i,weakGradient u x i=0 := by
  constructor
  · change (u.val x) 0=0
    rw [h]; rfl
  · intro i
    change (u.val x) i.succ=0
    rw [h]; rfl

lemma parentCompletionJoin_zero_off_support (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : a<0) {χ : (Fin 3 → ℝ) → ℝ}
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)
    (hχb : ∀ y,|χ y|≤1) (hχs : tsupport χ⊆sourceClosedCollarBand 0 (2*centralThickness))
    (p : centralEnergySpace s) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∉tsupport χ →
      weakValue (parentCompletionJoin s hs ha hχ hc hχb hχs p) x=0 ∧
      ∀ i,weakGradient (parentCompletionJoin s hs ha hχ hc hχb hχs p) x i=0 := by
  have hh := physical_localized_jet_zero hχ hc (fun i => parentJoinedComponentCLM s hs ha i p.val)
  filter_upwards [hh] with x hx hn
  exact weak_jet_zero_of_val_zero _ (hx hn)

lemma childCompletionJoin_zero_off_support (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : 0<a) (k : Fin 2) {χ : (Fin 3 → ℝ) → ℝ}
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)
    (hχb : ∀ y,|χ y|≤1) (hχs : tsupport χ⊆sourceClosedCollarBand (-2*centralThickness) 0)
    (p : centralEnergySpace s) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∉tsupport χ →
      weakValue (childCompletionJoin s hs ha k hχ hc hχb hχs p) x=0 ∧
      ∀ i,weakGradient (childCompletionJoin s hs ha k hχ hc hχb hχs p) x i=0 := by
  have hh := physical_localized_jet_zero hχ hc (fun i => childJoinedComponentCLM s hs ha k i p.val)
  filter_upwards [hh] with x hx hn
  exact weak_jet_zero_of_val_zero _ (hx hn)

lemma centralInteriorCompletion_zero_off_support (s : Fin 3 → ℝ)
    {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)
    (hχs : tsupport χ⊆centralPhysical) (hχB : ∀ y∈tsupport χ,WithLp.toLp 2 y∈ball)
    (p : centralEnergySpace s) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∉tsupport χ →
      weakValue (centralInteriorCompletion s hχ hc hχs hχB p) x=0 ∧
      ∀ i,weakGradient (centralInteriorCompletion s hχ hc hχs hχB p) x i=0 := by
  have hh := physical_localized_jet_zero hχ hc
    (fun i => centralPhysicalWholeCLM (centralAmbientComponent s i p.val))
  filter_upwards [hh] with x hx hn
  exact weak_jet_zero_of_val_zero _ (hx hn)

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceJoin_children_separate (k l : Fin 2) (hkl : k≠l) {y : Fin 3 → ℝ}
    (hk : -2*centralThickness ≤ sourceCollarTime
      ((sourceChildHomeomorph (actualChildSign k)).symm y))
    (hl : -2*centralThickness ≤ sourceCollarTime
      ((sourceChildHomeomorph (actualChildSign l)).symm y)) : False := by
  have h₁ := (sourceJoinInner_bounds hk).2.1
  have h₂ := (sourceJoinInner_bounds hl).2.1
  change |(y 0-actualChildSign k*sourceOffset)/sourceScale|≤1002/1000 at h₁
  change |(y 0-actualChildSign l*sourceOffset)/sourceScale|≤1002/1000 at h₂
  rw [abs_div,abs_of_pos (show 0<sourceScale by norm_num [sourceScale])] at h₁ h₂
  have h₁' := abs_le.mp ((div_le_iff₀ (show 0<sourceScale by norm_num [sourceScale])).mp h₁)
  have h₂' := abs_le.mp ((div_le_iff₀ (show 0<sourceScale by norm_num [sourceScale])).mp h₂)
  fin_cases k <;> fin_cases l
  · exact hkl rfl
  · norm_num [actualChildSign,sourceScale,sourceOffset] at h₁' h₂'
    linarith [h₁'.1,h₂'.2]
  · norm_num [actualChildSign,sourceScale,sourceOffset] at h₁' h₂'
    linarith [h₂'.1,h₁'.2]
  · exact hkl rfl

lemma physicalOtherEnd_child_time (k : Fin 2) (i : Fin 3) (hik : i≠k.succ)
    {y : Fin 3 → ℝ} (hy : y∈physicalEndRegion i) :
    sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)< -2*centralThickness := by
  by_contra hn
  have ht := le_of_not_gt hn
  revert hy hik
  refine Fin.cases ?_ (fun l => ?_) i
  · intro _ hy
    have hh := sourceJoinChild_far_parent k ht
    have he : sourceChildCoordinates (actualChildSign k)
        ((sourceChildHomeomorph (actualChildSign k)).symm y)=y :=
      (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y
    rw [he] at hh
    change sourceCollarTime y∈Icc 0 centralThickness at hy
    norm_num [centralThickness] at hh hy
    linarith [hy.2]
  · intro hik hy
    have hl : -2*centralThickness ≤ sourceCollarTime
        ((sourceChildHomeomorph (actualChildSign l)).symm y) := by
      change sourceCollarTime ((sourceChildHomeomorph (actualChildSign l)).symm y)
        ∈Icc (-centralThickness) 0 at hy
      have := hy.1
      dsimp [centralThickness] at *
      linarith
    exact sourceJoin_children_separate k l (fun he => hik (congrArg Fin.succ he.symm)) ht hl

lemma physicalChildEnd_parent_time (k : Fin 2) {y : Fin 3 → ℝ}
    (hy : y∈physicalEndRegion k.succ) : 2*centralThickness ≤ sourceCollarTime y := by
  have hh := physicalChildEnd_far_parent k hy
  have he : sourceChildCoordinates (actualChildSign k)
      ((sourceChildHomeomorph (actualChildSign k)).symm y)=y :=
    (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y
  rwa [he] at hh

lemma parent_join_zero_on_children (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : a<0) (p : centralEnergySpace s) (k : Fin 2) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈physicalEndRegion k.succ →
      weakValue (parentCompletionJoin s hs ha (centralJoinPartition_smooth 1)
        centralJoinPartition_parent_compact (centralJoinPartition_bound 1)
        centralJoinPartition_parent_support p) x=0 ∧
      ∀ i,weakGradient (parentCompletionJoin s hs ha (centralJoinPartition_smooth 1)
        centralJoinPartition_parent_compact (centralJoinPartition_bound 1)
        centralJoinPartition_parent_support p) x i=0 := by
  have hh := parentCompletionJoin_zero_off_support s hs ha (centralJoinPartition_smooth 1)
    centralJoinPartition_parent_compact (centralJoinPartition_bound 1)
    centralJoinPartition_parent_support p
  filter_upwards [hh] with x hx hy
  apply hx
  intro hm
  have ht := centralJoinPartition_subordinate 1 hm
  change sourceCollarTime (WithLp.ofLp x)∈Ioo 0 (2*centralThickness) at ht
  exact (not_le.mpr ht.2) (physicalChildEnd_parent_time k hy)

lemma physical_child_join_zero_on_other_ends (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : 0<a) (p : centralEnergySpace s) (k : Fin 2)
    (i : Fin 3) (hik : i≠k.succ) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈physicalEndRegion i →
      weakValue (physicalChildCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
        (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
        (centralJoinChildCutoff_support k) p) x=0 ∧
      ∀ j,weakGradient (physicalChildCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
        (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
        (centralJoinChildCutoff_support k) p) x j=0 := by
  let u := childCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
    (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
    (centralJoinChildCutoff_support k) p
  have hu : u∈H10 := childCompletionJoin_mem_H10 s hs ha k _ _ _ _ p
  have he := childCompletionJoin_zero_off_support s hs ha k (centralJoinChildCutoff_smooth k)
    (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
    (centralJoinChildCutoff_support k) p
  have hz : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈{y | sourceCollarTime y< -2*centralThickness} →
      weakValue u x=0 ∧ ∀ j,weakGradient u x j=0 := by
    filter_upwards [he] with x hx hy
    exact hx (fun hm => (not_le.mpr hy) ((centralJoinChildCutoff_support k hm).1))
  have hh := childH10Transport_zero_on k ⟨u,hu⟩ _ hz
  filter_upwards [hh] with x hx hy
  exact hx (physicalOtherEnd_child_time k i hik hy)

lemma central_interior_join_zero_on_ends (s : Fin 3 → ℝ) (p : centralEnergySpace s)
    (i : Fin 3) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈physicalEndRegion i →
      weakValue (centralInteriorCompletion s (centralJoinPartition_smooth 0)
        centralJoinPartition_interior_compact centralJoinPartition_interior_support
        (fun _ hy => centralPhysical_subset_ball (centralJoinPartition_interior_support hy)) p) x=0 ∧
      ∀ j,weakGradient (centralInteriorCompletion s (centralJoinPartition_smooth 0)
        centralJoinPartition_interior_compact centralJoinPartition_interior_support
        (fun _ hy => centralPhysical_subset_ball (centralJoinPartition_interior_support hy)) p) x j=0 := by
  have hh := centralInteriorCompletion_zero_off_support s (centralJoinPartition_smooth 0)
    centralJoinPartition_interior_compact centralJoinPartition_interior_support
    (fun _ hy => centralPhysical_subset_ball (centralJoinPartition_interior_support hy)) p
  have he := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
      physicalBlockRegion_central_end_exclusive_ae)
  filter_upwards [hh,he] with x hx he hy
  exact hx (fun hm => he (centralJoinPartition_interior_support hm) i hy)

end ScalarConductivity
end

end OAI
