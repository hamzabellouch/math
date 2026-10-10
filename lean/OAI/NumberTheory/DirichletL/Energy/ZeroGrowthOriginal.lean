import OAI.NumberTheory.DirichletL.Energy.ZeroGrowthBounded
import OAI.NumberTheory.DirichletL.Energy.ZeroRetainedError
import OAI.NumberTheory.DirichletL.Energy.ReferenceDeletionEnergy
import OAI.NumberTheory.DirichletL.Energy.ReferenceProfileBudget
import OAI.NumberTheory.DirichletL.Energy.LiveClippingDefect

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthOriginal
open HeckeFamily HeckeDyadic QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyZeroGrowth
open CenteredMomentEnergyZeroGrowthBounded CenteredMomentEnergyZeroRetainedError
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceDeletionEnergy CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentInductionEnergy CenteredMomentEnergyLiveClippingDefect CenteredMomentRetainedEnergy
local notation "O"=>HeckeFamily.O

def swapProfiles {a b:ℝ}(p:Profiles a b):Profiles a b where
  profile := ![p.profile 1,p.profile 0]
  support := by
    intro i
    fin_cases i
    · simpa using p.support 1
    · simpa using p.support 0

lemma swapProfiles_control {a b:ℝ}(p:Profiles a b)(U:Finset (ℕ×ℕ)):
    (swapProfiles p).control U=p.control U:=by
  simp [swapProfiles,Profiles.control,mul_comm]

lemma plainEnergy_swap {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)
    (p:Profiles a b)(t X₁ X₂:ℝ):
    s.plainEnergy (swapProfiles p) t X₂ X₁=s.plainEnergy p t X₁ X₂:=by
  unfold NaturalState.plainEnergy energy
  apply tsum_congr
  intro z
  have hh:positiveSlotRow s.character s.mask 1 z ((swapProfiles p).profile 0)
      ((swapProfiles p).profile 1) (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1)
      t X₂ X₁=positiveSlotRow s.character s.mask 1 z (p.profile 0) (p.profile 1)
      (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1) t X₁ X₂:=by
    simp only [swapProfiles,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    unfold positiveSlotRow
    rw [mul_comm X₂ X₁]
    ring
  rw [hh]

theorem original_from_growth (a b bΦ epsilon xi defect saving Lreflect:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hepsilon:0<epsilon)(hxi:0<xi)(hdefect:0<defect)(S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(Bmask L Mcap loss:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K→
      ZeroGrowthAt Q a b bΦ Bmask L Mcap loss Z degree S K→0≤Bmask→
      Mcap+Bmask+defect+xi≤L→Mcap+Bmask+defect≤Lreflect→
      ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤Mcap→
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁→0<X₂→X₁≤Z^L→X₂≤Z^L→
      s.plainEnergy p t X₁ X₂≤
        C*(K+1)*diagonalControl s.radial.profile*(p.control U)^2*(1+|t|)^J*
          (s.puncture.radical.absNorm:ℝ)^epsilon*
          ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon*
            (1+2*(L*Real.log Z))*Z^(s.width+loss+defect+xi)+
           (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
            Z^(-2*saving)*max 1 s.radial.scale*Z^L):=by
  obtain ⟨n,T,Dchild,hDc,nlive,Slive,Clive,Dlive,hCl,hDl,hlive⟩:=
    live_deleted_bounded a b bΦ epsilon xi defect saving Lreflect
      ha hlo hhi hbΦ hepsilon hxi hdefect 2 (by norm_num) S
  obtain ⟨ndead,Sdead,Cdead,hCd,hdead⟩:=natural_original_error_mass
    a b bΦ epsilon xi saving ha (by linarith only [hlo, hhi]) hbΦ hepsilon hxi
  obtain ⟨Cweight,hCw,hweight⟩:=original_energy_weighted_deletion (α:=Fin 0)
    (fun _=>0) (fun _=>0) (fun _=>le_refl 0) epsilon hepsilon
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T (Slive∪Sdead)
    0 n (nlive+ndead) Clive Dchild (Dlive+Cdead) hCl hDc (by positivity)
  refine ⟨J,U,Cweight*Cprofile,by positivity,?_⟩
  filter_upwards [hlive,hdead] with Z hZ hZd
  refine ⟨hZ.1,?_⟩
  intro Bmask L Mcap loss Q degree K hK hgrowth hBmask hL hLreflect s hQ hs
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hL0:0≤L:=by linarith only [s.width_nonneg, hs, hBmask, hdefect, hxi, hL]
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hd:=diagonalControl_nonneg s.radial.profile
  let Rcap:=max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width)
  let Pmain:=Rcap^epsilon*(1+2*(L*Real.log Z))*Z^(s.width+loss+defect+xi)
  let Perror:=Rcap^(2*epsilon)*Z^(-2*saving)*max 1 s.radial.scale*Z^L
  have hPm:0≤Pmain:=by dsimp only [Pmain,Rcap];positivity
  have hPe:0≤Perror:=by dsimp only [Perror,Rcap];positivity
  have hordered (p:Profiles a b)(t Xshort Xlong:ℝ)(hXs:0<Xshort)(horder:Xshort≤Xlong)
      (hcap:Xshort≤Z^L)(hsupport:1≤b*Xlong):
      s.plainEnergy p t Xshort Xlong≤
        Cweight*Cprofile*(K+1)*diagonalControl s.radial.profile*(p.control U)^2*(1+|t|)^J*
          (s.puncture.radical.absNorm:ℝ)^epsilon*(Pmain+Perror):=by
    have hXl:0<Xlong:=hXs.trans_le horder
    have hp:=hprofile (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t 0 (le_refl 0)
    simp only [add_zero,zero_add,pow_zero,mul_one] at hp
    let A:=Cprofile*(p.control U)^2*(1+|t|)^J
    let E:=(K+1)*diagonalControl s.radial.profile*A
    have hA:0≤A:=by dsimp only [A];positivity
    have hE:0≤E:=by dsimp only [E];positivity
    have hSl:sourceControl Slive (p.profile 1)≤sourceControl (Slive∪Sdead) (p.profile 1):=
      control_mono Finset.subset_union_left _
    have hSd:sourceControl Sdead (p.profile 1)≤sourceControl (Slive∪Sdead) (p.profile 1):=
      control_mono Finset.subset_union_right _
    have hSl0:=sourceControl_nonneg Slive (p.profile 1)
    have hSd0:=sourceControl_nonneg Sdead (p.profile 1)
    have hheight:1≤1+‖t‖:=le_add_of_nonneg_right (norm_nonneg _)
    have hnL:(1+‖t‖)^(2*nlive)≤(1+‖t‖)^(2*(nlive+ndead)):=
      pow_le_pow_right₀ hheight (by omega)
    have hnD:(1+‖t‖)^(2*ndead)≤(1+‖t‖)^(2*(nlive+ndead)):=
      pow_le_pow_right₀ hheight (by omega)
    have hmain:Clive*(sourceControl Slive (p.profile 1))^2*(1+‖t‖)^(2*nlive)*
        (K*diagonalControl s.radial.profile*Dchild*(sourceControl T (p.profile 0))^2*(1+|t|)^(2*n))≤E:=by
      have hh:Clive*Dchild*(sourceControl Slive (p.profile 1))^2*(sourceControl T (p.profile 0))^2*
          (1+‖t‖)^(2*nlive)*(1+|t|)^(2*n)≤A:=by
        apply le_trans _ hp.2.1
        gcongr
      have hh':=mul_le_mul_of_nonneg_left hh (mul_nonneg hK hd)
      have he:K*diagonalControl s.radial.profile*A≤E:=by
        dsimp only [E]
        nlinarith only [mul_nonneg hd hA]
      apply le_trans _ he
      convert hh' using 1; ring
    have herrLive:Dlive*(sourceControl Slive (p.profile 1))^2*(1+‖t‖)^(2*nlive)*
        ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*diagonalControl s.radial.profile≤E:=by
      have hh:Dlive*(sourceControl Slive (p.profile 1))^2*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*(1+‖t‖)^(2*nlive)≤A:=by
        apply le_trans _ hp.2.2
        gcongr
        exact le_add_of_nonneg_right hCd.le
      have hh':=mul_le_mul_of_nonneg_left hh hd
      have he:diagonalControl s.radial.profile*A≤E:=by
        dsimp only [E]
        nlinarith only [mul_nonneg hK (mul_nonneg hd hA)]
      apply le_trans _ he
      convert hh' using 1; ring
    have herrDead:Cdead*(sourceControl Sdead (p.profile 1))^2*
        ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*(1+‖t‖)^(2*ndead)*
        diagonalControl s.radial.profile≤E:=by
      have hh:Cdead*(sourceControl Sdead (p.profile 1))^2*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*(1+‖t‖)^(2*ndead)≤A:=by
        apply le_trans _ hp.2.2
        gcongr
        exact le_add_of_nonneg_left hDl.le
      have hh':=mul_le_mul_of_nonneg_left hh hd
      have he:diagonalControl s.radial.profile*A≤E:=by
        dsimp only [E]
        nlinarith only [mul_nonneg hK (mul_nonneg hd hA)]
      apply le_trans _ he
      convert hh' using 1; ring
    have hw:=hweight Z Bmask bΦ a b s (p.profile 0) (p.profile 1) ha (by linarith only [hlo, hhi])
      (p.support 0) (p.support 1) (fun _=>∅) (fun _ _=>0) (fun _=>1)
      t Xshort Xlong (E*(Pmain+Perror)) 1
    have hresult:s.plainEnergy p t Xshort Xlong≤
        Cweight*(s.puncture.radical.absNorm:ℝ)^epsilon*(E*(Pmain+Perror)):=by
      apply hw
      · simp
      · simp
      · simp
      · simp
      · exact hXs
      · exact hXl
      · exact mul_nonneg hE (add_nonneg hPm hPe)
      · norm_num
      · intro Ds hDs Dl hDl' I hI
        obtain ⟨hNs,_⟩:=divisor_norm s Ds hDs
        obtain ⟨hNl,_⟩:=divisor_norm s Dl hDl'
        have hpS:0<((∏P∈Ds,P).absNorm:ℝ):=zero_lt_one.trans_le hNs
        have hpL:0<((∏P∈Dl,P).absNorm:ℝ):=zero_lt_one.trans_le hNl
        have heffective (f:O→ℂ):radialEnergy f (effectiveState s).radial.keep
            s.radial.profile s.radial.scale=radialEnergy f s.radial.keep s.radial.profile s.radial.scale:=
          radialEnergy_effective s.radial f
        simp only [Finset.univ_eq_empty,Finset.empty_sdiff,Finset.prod_empty,mul_one,Real.rpow_one]
        rw [show (fun z:O=>polynomial (naturalCharacter s.character z) false (p.profile 0)
              (Xshort/((∏P∈Ds,P).absNorm:ℝ)) 0 t*
            polynomial (naturalCharacter s.character z) false (p.profile 1)
              (Xlong/((∏P∈Dl,P).absNorm:ℝ)) 0 t)=
            (fun z:O=>polynomial (naturalCharacter s.character z) false (p.profile 1)
              (Xlong/((∏P∈Dl,P).absNorm:ℝ)) 0 t*
            polynomial (naturalCharacter s.character z) false (p.profile 0)
              (Xshort/((∏P∈Ds,P).absNorm:ℝ)) 0 t) by funext z;exact mul_comm _ _]
        by_cases hl:0≤s.width-Real.logb Z (Xlong/((∏P∈Dl,P).absNorm:ℝ))+xi
        · have hh:=hZ.2 Bmask L Mcap loss Q degree K hK hgrowth hBmask hL hLreflect
            s hQ hs (p.profile 1) (p.profile 0) (p.support 1) (p.support 0)
            t Xshort Xlong hXs horder hcap hsupport Ds Dl hDs hDl' hl
          have hb:=add_le_add
            (mul_le_mul_of_nonneg_right hmain (mul_nonneg hPm hpL.le))
            (mul_le_mul_of_nonneg_right herrLive hPe)
          have hc:E*Pmain*((∏P∈Dl,P).absNorm:ℝ)+E*Perror≤
              E*(Pmain+Perror)*((∏P∈Dl,P).absNorm:ℝ):=by
            calc
              _ ≤ E*Pmain*((∏P∈Dl,P).absNorm:ℝ)+(E*Perror)*((∏P∈Dl,P).absNorm:ℝ) :=
                add_le_add le_rfl (le_mul_of_one_le_right (mul_nonneg hE hPe) hNl)
              _ = _ := by ring
          apply hh.trans
          calc
            _ ≤ E*Pmain*((∏P∈Dl,P).absNorm:ℝ)+E*Perror := by
              convert hb using 1 <;> dsimp only [Pmain,Perror,Rcap] <;> ring
            _ ≤ _ := hc
        · have hfar:s.width+xi<Real.logb Z (Xlong/((∏P∈Dl,P).absNorm:ℝ)):=by linarith only [hl]
          have hh:=hZd.2 Bmask s (p.profile 1) (p.profile 0) (p.support 1) (p.support 0)
            t t (Real.logb Z (Xlong/((∏P∈Dl,P).absNorm:ℝ)))
            (Xshort/((∏P∈Ds,P).absNorm:ℝ)) (div_pos hXs hpS) hfar
          rw [Real.rpow_logb hz hZ.1.ne' (div_pos hXl hpL)] at hh
          rw [heffective]
          have hshortcap:Xshort/((∏P∈Ds,P).absNorm:ℝ)≤Z^L:=
            (div_le_self hXs.le hNs).trans hcap
          have hb:=mul_le_mul_of_nonneg_right herrDead
            (show 0≤Rcap^(2*epsilon)*Z^(-2*saving)*max 1 s.radial.scale*
              (Xshort/((∏P∈Ds,P).absNorm:ℝ)) by positivity)
          have hc:E*(Rcap^(2*epsilon)*Z^(-2*saving)*max 1 s.radial.scale*
              (Xshort/((∏P∈Ds,P).absNorm:ℝ)))≤E*Perror:=by
            dsimp only [Perror]
            gcongr
          have hf:E*Perror≤E*(Pmain+Perror)*((∏P∈Dl,P).absNorm:ℝ):=by
            exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hPm) hE).trans
              (le_mul_of_one_le_right (mul_nonneg hE (add_nonneg hPm hPe)) hNl)
          apply hh.trans
          calc
            _ ≤ E*(Rcap^(2*epsilon)*Z^(-2*saving)*max 1 s.radial.scale*
                (Xshort/((∏P∈Ds,P).absNorm:ℝ))) := by
              convert hb using 1; dsimp only [Rcap,sourceControl]; ring
            _ ≤ E*Perror := hc
            _ ≤ _ := hf
    apply hresult.trans_eq
    dsimp only [E,A]
    ring
  intro p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  by_cases hzero:s.plainEnergy p t X₁ X₂=0
  · rw [hzero]
    positivity
  · obtain ⟨z,hz,hrow⟩:=energy_support_witness s.character s.mask 1 t
      (p.profile 0) (p.profile 1) (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1)
      X₁ X₂ s.radial.keep s.radial.profile s.radial.scale hzero
    obtain ⟨hs₁,hs₂⟩:=positiveSlotRow_profiles_scales s.character s.mask 1 z p
      (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1) t X₁ X₂ hX₁ hX₂ hrow
    by_cases horder:X₁≤X₂
    · exact hordered p t X₁ X₂ hX₁ horder hc₁ hs₂
    · have hh:=hordered (swapProfiles p) t X₂ X₁ hX₂ (le_of_not_ge horder) hc₂ hs₁
      simpa only [plainEnergy_swap,swapProfiles_control] using hh

end SevenEighths.CenteredMomentEnergyZeroGrowthOriginal

end

end OAI
