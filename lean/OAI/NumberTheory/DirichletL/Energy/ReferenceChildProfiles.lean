import OAI.NumberTheory.DirichletL.Energy.ReferenceChild

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceChildProfiles
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyProfiles
open CenteredMomentAllocatedNaturalRadial CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentFiniteProfileExceptional
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentLattice CenteredMomentRetainedProfile
local notation "O"=>HeckeFamily.O

def reflectionProfiles {a b:ℝ}(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
    (j k:Fin 2)(v t:ℝ):Profiles a b:=
  independentProfiles ha (derivativeChoice (annulusSeed a b hlo hhi).profile j)
    (derivativeChoice W k)
    (derivativeChoice_support _ _ _ (annulusSeed a b hlo hhi).support j)
    (derivativeChoice_support _ _ _ hs k) (-2*Real.pi*v) t

theorem reflected_child_ray_energy {α:Type*}[Fintype α][DecidableEq α]
    {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
    (F:Finset α)(pool:α→Finset (Ideal O))(ν:α→Character)(Wslot:α→ℝ→ℂ)(P σ freq:α→ℝ)
    (hp:∀i∈F,∀I∈pool i,Prime I)(hP:∀i∈F,0<P i)
    (j k:Fin 2)(v t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v) *
      polynomial (naturalCharacter s.character z) false (scaleTest W k) X₂ 0 t *
      ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i)
        (heightCoefficient (fun I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (Wslot i) (P i) (σ i) (freq i) I) t) (P i))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale=
    energy (unpuncturedState s).character (unpuncturedState s).mask 1 0
      ((reflectionProfiles ha hlo hhi W hs j k v t).profile 0)
      ((reflectionProfiles ha hlo hhi W hs j k v t).profile 1)
      (fun i:F=>pool i)
      (fun (i:F) I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (Wslot i) (P i) (σ i) (t+freq i) I)
      (fun i:F=>P i) X₁ X₂
      (unpuncturedState s).radial.keep (unpuncturedState s).radial.profile (unpuncturedState s).radial.scale:=by
  have hh:=independent_child_ray_energy s ha
    (derivativeChoice (annulusSeed a b hlo hhi).profile j) (derivativeChoice W k)
    (derivativeChoice_support _ _ _ (annulusSeed a b hlo hhi).support j)
    (derivativeChoice_support _ _ _ hs k) F pool ν Wslot P σ freq hp hP
    t (-2*Real.pi*v) t X₁ X₂ hX₁ hX₂
  have he:((annulusSeed a b hlo hhi).profile:ℝ→ℂ)=(fun y:ℝ=>(annulus y:ℂ)):=
    funext annulusTemplate_apply
  simpa only [derivativeChoice_apply,he,reflectionProfiles] using hh

theorem independent_profile_control (a b:ℝ)(ha:0<a)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,∀t₁ t₂:ℝ,
      (independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control S≤
        C*(sourceControl T W₁*sourceControl T W₂)*(1+‖t₁‖+‖t₂‖)^(2*n):=by
  obtain ⟨n,T,C,hC,hc⟩:=normPowerProfile_source_control a b ha S
  refine ⟨n,T,C^2,sq_pos_of_pos hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ t₁ t₂
  have h₁:=hc W₁ hs₁ t₁
  have h₂:=hc W₂ hs₂ t₂
  have hp₁:(1+‖t₁‖)^n≤(1+‖t₁‖+‖t₂‖)^n:=pow_le_pow_left₀ (by positivity) (by linarith [norm_nonneg t₂]) n
  have hp₂:(1+‖t₂‖)^n≤(1+‖t₁‖+‖t₂‖)^n:=pow_le_pow_left₀ (by positivity) (by linarith [norm_nonneg t₁]) n
  have h₁':S.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)≤C*sourceControl T W₁*(1+‖t₁‖+‖t₂‖)^n:=
    h₁.trans (mul_le_mul_of_nonneg_left hp₁ (mul_nonneg hC.le (sourceControl_nonneg _ _)))
  have h₂':S.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂)≤C*sourceControl T W₂*(1+‖t₁‖+‖t₂‖)^n:=
    h₂.trans (mul_le_mul_of_nonneg_left hp₂ (mul_nonneg hC.le (sourceControl_nonneg _ _)))
  simp only [Profiles.control,independentProfiles,show (1:Fin 2)≠0 by decide,ite_true,ite_false]
  apply (mul_le_mul h₁' h₂' (apply_nonneg _ _)
    (mul_nonneg (mul_nonneg hC.le (sourceControl_nonneg _ _)) (by positivity))).trans_eq
  rw [show (1+‖t₁‖+‖t₂‖)^(2*n)=((1+‖t₁‖+‖t₂‖)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul]]
  ring

lemma derivative_choice_control (S:Finset (ℕ×ℕ)):
    ∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),∀j:Fin 2,
      sourceControl S (derivativeChoice W j)≤C*sourceControl T W:=by
  obtain ⟨T,C,hC,hc⟩:=scale_source_control S
  refine ⟨S∪T,1+C,by positivity,?_⟩
  intro W j
  have h₁:sourceControl S W≤sourceControl (S∪T) W:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left:S⊆S∪T)) W
  have h₂:sourceControl T W≤sourceControl (S∪T) W:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_right:T⊆S∪T)) W
  by_cases hj:j=0
  · simp only [derivativeChoice,ite_eq_left hj]
    exact h₁.trans (le_mul_of_one_le_left (sourceControl_nonneg _ _) (by linarith))
  · simp only [derivativeChoice,ite_eq_right hj]
    exact (hc W).trans (mul_le_mul (by linarith) h₂ (sourceControl_nonneg _ _) (by positivity))

theorem reflected_profile_control (a b:ℝ)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀W:𝓢(ℝ,ℂ),∀hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b,
      ∀j k:Fin 2,∀v t:ℝ,
      (reflectionProfiles ha hlo hhi W hs j k v t).control S≤
        C*sourceControl T W*(1+‖v‖+‖t‖)^n:=by
  obtain ⟨n,T,C,hC,hc⟩:=independent_profile_control a b ha S
  obtain ⟨U,D,hD,hd⟩:=derivative_choice_control T
  let A:ℝ:=1+∑j:Fin 2,sourceControl T (derivativeChoice (annulusSeed a b hlo hhi).profile j)
  have hA:0<A:=by
    have hh:=Finset.sum_nonneg (fun (j:Fin 2) (_:j∈Finset.univ)=>
      sourceControl_nonneg T (derivativeChoice (annulusSeed a b hlo hhi).profile j))
    dsimp [A];linarith
  refine ⟨2*n,U,C*A*D*(1+2*Real.pi)^(2*n),by positivity,?_⟩
  intro W hs j k v t
  have haSeed:sourceControl T (derivativeChoice (annulusSeed a b hlo hhi).profile j)≤A:=by
    have hh:=Finset.single_le_sum (fun (j:Fin 2) (_:j∈Finset.univ)=>
      sourceControl_nonneg T (derivativeChoice (annulusSeed a b hlo hhi).profile j)) (Finset.mem_univ j)
    dsimp [A];linarith
  have hheight:1+‖-2*Real.pi*v‖+‖t‖≤(1+2*Real.pi)*(1+‖v‖+‖t‖):=by
    rw [norm_mul,norm_mul,Real.norm_of_nonneg Real.pi_pos.le]
    norm_num only [norm_neg,Real.norm_of_nonneg (by norm_num:0≤(2:ℝ))]
    nlinarith [Real.pi_pos,norm_nonneg v,norm_nonneg t]
  have hh:=hc (derivativeChoice (annulusSeed a b hlo hhi).profile j) (derivativeChoice W k)
    (derivativeChoice_support _ _ _ (annulusSeed a b hlo hhi).support j)
    (derivativeChoice_support _ _ _ hs k) (-2*Real.pi*v) t
  apply hh.trans
  calc
    _≤C*(A*(D*sourceControl U W))*((1+2*Real.pi)*(1+‖v‖+‖t‖))^(2*n):=by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (mul_le_mul haSeed (hd W k) (sourceControl_nonneg _ _) hA.le) hC.le
      · exact pow_le_pow_left₀ (by positivity) hheight _
      · positivity
      · exact mul_nonneg hC.le (mul_nonneg hA.le (mul_nonneg hD.le (sourceControl_nonneg _ _)))
    _=_:=by rw [mul_pow];ring

end SevenEighths.CenteredMomentEnergyReferenceChildProfiles

end

end OAI
