import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
import OAI.NumberTheory.DirichletL.Moments.SecondDyadicRowSupport
import OAI.NumberTheory.DirichletL.Moments.SecondWidthDrop

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondChildRadialWidth
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondLiveBlock
open CenteredMomentSecondDyadicRowSupport CenteredMomentSectorLocalization
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRadicalBudget
open CenteredMomentSecondActualWidth CenteredMomentSecondWidthDrop
local notation "O" => HeckeFamily.O

theorem physicalBlock_live_dyadic_witness (η:Character)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z:O,z∈liveRows C D U R rows ∧ z∈dyadicRows rows n ∧
      z≠0 ∧ dyadicScale (n 1)<4*normValue z := by
  rw [physicalBlock_live_dyadic_rows η t S β C D hC hD U R rows W K n] at hne
  unfold physicalBlock at hne
  obtain ⟨z,hz,_⟩:=Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hl,hd⟩:=(mem_dyadicRows _ n z).mp hz
  have hz':z∈dyadicRows rows n:=(mem_dyadicRows rows n z).mpr
    ⟨(Finset.mem_filter.mp hl).1,hd⟩
  exact ⟨z,hl,hz',dyadicRows_nonzero rows n z hz',by
    have hh:=(dyadicRows_norm rows n z hz').1
    linarith⟩

section Family
variable {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
  {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
  (h:Family η C D hC hD U τ)
  (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
  (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
  (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)

include h hK hne

theorem dyadic_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter) :
    Real.logb Z (dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*(fixedFactor:ℝ)) := by
  obtain ⟨z,hzl,_,hz0,hscale⟩:=physicalBlock_live_dyadic_witness η t S β C D hC hD U R rows W K n hne
  have hw:=(h.physical_budget t S β R rows W K hK n hne χ).2 Z hZ z hzl
  have hh:=Real.logb_le_logb_of_le hZ (dyadicScale_pos (n 1)) hscale.le
  rw [Real.logb_mul (by norm_num : (4:ℝ)≠0) (normValue_pos z hz0).ne'] at hh
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*(fixedFactor:ℝ))=
      Real.logb Z (4:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul (by norm_num : (4:ℝ)≠0) (by positivity : 4*(fixedFactor:ℝ)≠0)]
    congr 1
    ring
  rw [hf]
  linarith

omit h hK hne in

theorem radial_support_bound (Φ:ℝ→ℂ)(b:ℝ)
    (hs:Function.support Φ⊆Set.Iic b)(y:O)
    (hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y≤b*dyadicScale (n 1) :=
  (div_le_iff₀ (dyadicScale_pos (n 1))).mp (hs hy)

theorem radial_radius_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter)(b:ℝ)(hb:0<b) :
    Real.logb Z (b*dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
  have hh:=dyadic_log_budget h t S β R rows W K hK n hne Z hZ χ
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*b*(fixedFactor:ℝ))=
      Real.logb Z b+Real.logb Z (16*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul hb.ne' (by positivity : 16*(fixedFactor:ℝ)≠0)]
    congr 1
    ring
  rw [Real.logb_mul hb.ne' (dyadicScale_pos (n 1)).ne',hf]
  linarith

theorem radial_point_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter)
    (Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (normValue y)+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
  have hl:=Real.logb_le_logb_of_le hZ (normValue_pos y hy0)
    (radial_support_bound n Φ b hs y hy)
  have hh:=radial_radius_log_budget h t S β R rows W K hK n hne Z hZ χ b hb
  linarith

theorem declared_radial_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter)
    (Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
  have hbH:1≤b*dyadicScale (n 1):=(normValue_ge_one y hy0).trans
    (radial_support_bound n Φ b hs y hy)
  rw [max_eq_right hbH]
  exact radial_radius_log_budget h t S β R rows W K hK n hne Z hZ χ b hb

theorem whole_radial_norm_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter)
    (Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y*((τ χ).modulus.absNorm:ℝ)≤
      Z^(Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*b*(fixedFactor:ℝ))) := by
  have hτ:(0:ℝ)<(τ χ).modulus.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (τ χ).modulus_ne_bot)
  have hh:=radial_radius_log_budget h t S β R rows W K hK n hne Z hZ χ b hb
  rw [←Real.logb_mul (mul_pos hb (dyadicScale_pos (n 1))).ne' hτ.ne'] at hh
  exact (mul_le_mul_of_nonneg_right (radial_support_bound n Φ b hs y hy) hτ.le).trans
    ((Real.logb_le_iff_le_rpow hZ (mul_pos (mul_pos hb (dyadicScale_pos (n 1))) hτ)).mp hh)

end Family

theorem fixed_radial_cost_eventually (b ε:ℝ)(hb:0<b)(hε:0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→Real.logb Z (16*b*(fixedFactor:ℝ))≤ε := by
  have he:=(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (16*b*(fixedFactor:ℝ))
  obtain ⟨Z₀,hZ₀⟩:=Filter.eventually_atTop.1 (he.and (Filter.eventually_gt_atTop (1:ℝ)))
  refine ⟨max 2 Z₀,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro Z hZ
  obtain ⟨hc,hZ1⟩:=hZ₀ Z ((le_max_right _ _).trans hZ)
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  exact (Real.logb_le_iff_le_rpow hZ1 (by positivity)).mpr hc

theorem eventually_whole_radial_width (b ε:ℝ)(hb:0<b)(hε:0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→
    ∀(η:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
      (U:Finset (CommonIndex C D))(τ:RayCharacter→Character),Family η C D hC hD U τ→
    ∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U R rows W K n≠0→
    ∀(χ:RayCharacter)(Φ:ℝ→ℂ),Function.support Φ⊆Set.Iic b→
    Real.logb Z (b*dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+ε ∧
    ∀y:O,Φ (normValue y/dyadicScale (n 1))≠0→
      normValue y*((τ χ).modulus.absNorm:ℝ)≤
        Z^(Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
          Real.logb Z (normValue (commonFrequencyGenerator C D))+
          Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+ε) := by
  obtain ⟨Z₀,hZ₀,hcost⟩:=fixed_radial_cost_eventually b ε hb hε
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ η C D hC hD U τ h t S β R rows W K hK n hne χ Φ hs
  have hZ1:=hZ₀.trans_le hZ
  have hc:=hcost Z hZ
  constructor
  · have hh:=radial_radius_log_budget h t S β R rows W K hK n hne Z hZ1 χ b hb
    linarith
  · intro y hy
    exact (whole_radial_norm_budget h t S β R rows W K hK n hne Z hZ1 χ Φ b hb hs y hy).trans
      (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))

theorem physical_declared_radial_width_drop {η:Character}{C D:Ideal O}
    {hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Z H K Tsec Csec ξ M σ g:ℝ)(hZ:1<Z)(hH:0<H)(hK:0<K)
    (hT:0<Tsec)(hCs:0<Csec)
    (hg:amplificationIncrement η Z H K M σ≤g)
    (hscale:Tsec≤Csec*(H^2/(K*Z^g))) (n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U (frequencyRadius Tsec Z ξ)
      rows W (K*Z^g) n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      M-σ+ξ/2+Real.logb Z (16*b*Csec*(fixedFactor:ℝ)) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hKg:0<K*Z^g:=mul_pos hK (Real.rpow_pos_of_pos hz _)
  have hw:=declared_radial_log_budget h t S β (frequencyRadius Tsec Z ξ) rows W
    (K*Z^g) hKg n hne Z hZ χ Φ b hb hs y hy0 hy
  have hc:=actual_common_log_ge_unit C D hC U Z hZ
  have hn:nominalLength Z H K g+Real.logb Z (η.modulus.absNorm:ℝ)≤M-σ := by
    have hnom:=actual_nominal_drop η Z H K M σ
    unfold nominalLength at hnom ⊢
    linarith
  rw [physical_frequency_scale Z H K g hZ hH hK] at hscale
  have hl:=Real.logb_le_logb_of_le hZ hT hscale
  rw [Real.logb_mul hCs.ne' (Real.rpow_pos_of_pos hz _).ne',
    Real.logb_rpow hz hZ.ne'] at hl
  have hr:Real.logb Z (frequencyRadius Tsec Z ξ)≤
      nominalLength Z H K g+ξ/2+Real.logb Z Csec := by
    rw [frequencyRadius,Real.logb_mul hT.ne' (Real.rpow_pos_of_pos hz _).ne',
      Real.logb_rpow hz hZ.ne']
    linarith
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*b*Csec*(fixedFactor:ℝ))=
      Real.logb Z Csec+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul hCs.ne' (by positivity : 16*b*(fixedFactor:ℝ)≠0)]
    congr 1
    ring
  rw [hf]
  linarith

end SevenEighths.CenteredMomentSecondChildRadialWidth

end

end OAI
