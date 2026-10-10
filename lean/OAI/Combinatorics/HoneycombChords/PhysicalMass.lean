import OAI.Combinatorics.HoneycombChords.ObliqueBounds
import OAI.Combinatorics.HoneycombChords.PhysicalFunctional

namespace OAI

/-!
# Physical residual identities and strict bridge mass bounds

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

section

/-! Derivation of the manuscript's exact uneliminated and eliminated oblique
residual formulas from the actual infinite bridge mass. -/
namespace CriticalHoneycomb.FiniteFunctional
open Finset

lemma F0_density_integrable {N : ℕ} {H F : ℝ → ℂ}
    (hH : H ∈ M N ⊔ Submodule.span ℂ {C (angle/2)}) (hF : F ∈ admissibleDensity N) :
    PairingIntegrable H F := by
  rw [←fBasis_span] at hH
  apply PairingIntegrable.span_left (S:=Set.range (fBasis N)) _ hH
  rintro _ ⟨i,rfl⟩
  exact fBasis_density_integrable hF i

lemma value_annihilates_F0 {N : ℕ} {F : ℝ → ℂ} {ρ : ℂ}
    (hF : F ∈ admissibleDensity N) (hM : ∀ H ∈ M N,value ρ F H=0)
    (hc : value ρ F (C (angle/2))=0) {H : ℝ → ℂ}
    (hH : H ∈ M N ⊔ Submodule.span ℂ {C (angle/2)}) : value ρ F H=0 := by
  obtain ⟨H₀,h₀,H₁,h₁,rfl⟩ := Submodule.mem_sup.mp hH
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp h₁
  rw [value_add (F0_density_integrable (Submodule.mem_sup_left h₀) hF)
    (F0_density_integrable (Submodule.mem_sup_right (Submodule.smul_mem _ a
      (Submodule.subset_span (Set.mem_singleton (C (angle/2)))))) hF),hM _ h₀,value_smul,hc,mul_zero,add_zero]

lemma value_eq_residual {N : ℕ} {F H : ℝ → ℂ} {ρ : ℂ}
    (hF : F ∈ admissibleDensity N) (hM : ∀ H ∈ M N,value ρ F H=0)
    (hc : value ρ F (C (angle/2))=0) (hH : InPairingDomain N H) :
    value ρ F H=4*aStar*obliqueResidual N H (-4)+ρ*obliqueResidual N H 0 := by
  have he : value ρ F (obliqueResidual N H)=value ρ F H := by
    rw [obliqueResidual,value_sub (domain_density_integrable hH hF) (projection_density_integrable H hF),
      value_annihilates_F0 hF hM hc (projection_mem N H),sub_zero]
  rw [←he,value,residual_density_pairing_zero hH hF,add_zero]

/-- The physical bridge mass satisfies two residual equations before elimination of the scalar coefficient. -/
theorem source_physical_uneliminated_residual (N : ℕ) (hN : 1≤N) :
    ∃ (B : ℝ) (s : ℂ),0≤B ∧ bridgeMass N=ENNReal.ofReal B ∧
      2*(B:ℂ)=4*aStar*(obliqueResidual N hZero (-4)+s*obliqueResidual N hZero 0) ∧
      obliqueResidual N cThreeCorrection (-4)+s*obliqueResidual N cThreeCorrection 0=0 := by
  obtain ⟨B,ρ,F,hB,hMass,hF,hM,hc,hcorr,hval⟩ := source_physical_finite_functional N hN
  have he₀ := value_eq_residual hF hM hc (hZero_in_pairingDomain N)
  have he₁ := value_eq_residual hF hM hc (cThreeCorrection_in_pairingDomain N)
  change 2*(B:ℂ)=value ρ F hZero at hval
  change value ρ F cThreeCorrection=0 at hcorr
  have ha : 4*aStar ≠ 0 := mul_ne_zero (by norm_num) aStar_ne_zero
  refine ⟨B,ρ/(4*aStar),hB,hMass,?_,?_⟩
  · rw [hval,he₀]
    field_simp [aStar_ne_zero]
  · have hh : 4*aStar*obliqueResidual N cThreeCorrection (-4)+ρ*obliqueResidual N cThreeCorrection 0=0 := by
      rw [←he₁,hcorr]
    apply (mul_left_cancel₀ ha)
    rw [mul_zero]
    calc
      _=4*aStar*obliqueResidual N cThreeCorrection (-4)+ρ*obliqueResidual N cThreeCorrection 0 := by field_simp [aStar_ne_zero]
      _=0 := hh

/-- The physical bridge mass equals the eliminated oblique residual expression when its denominator is nonzero. -/
theorem source_physical_residual_formula (N : ℕ) (hN : 1≤N)
    (hd : obliqueResidual N cThreeCorrection 0 ≠ 0) :
    ∃ B : ℝ,0≤B ∧ bridgeMass N=ENNReal.ofReal B ∧
      (B:ℂ)=2*aStar*(obliqueResidual N hZero (-4)-
        obliqueResidual N cThreeCorrection (-4)*obliqueResidual N hZero 0/
          obliqueResidual N cThreeCorrection 0) := by
  obtain ⟨B,s,hB,hMass,hm,hs⟩ := source_physical_uneliminated_residual N hN
  have he : s= -obliqueResidual N cThreeCorrection (-4)/obliqueResidual N cThreeCorrection 0 := by
    apply (eq_div_iff hd).mpr
    linear_combination hs
  refine ⟨B,hB,hMass,?_⟩
  rw [he] at hm
  linear_combination (1/2:ℂ)*hm

end CriticalHoneycomb.FiniteFunctional

end


section

namespace CriticalHoneycomb.FiniteFunctional

/-- The physical bridge mass equals an oblique residual expression. -/
theorem physical_residual_formula (N : ℕ) (hN : 1≤N) :
    ∃ B : ℝ,0≤B ∧ bridgeMass N=ENNReal.ofReal B ∧
      (B:ℂ)=2*aStar*(obliqueResidual N hZero (-4)-
        obliqueResidual N cThreeCorrection (-4)*obliqueResidual N hZero 0/
          obliqueResidual N cThreeCorrection 0) :=
  source_physical_residual_formula N hN (source_residual_denominator_ne_zero hN)

end CriticalHoneycomb.FiniteFunctional

end


section

namespace CriticalHoneycomb.FiniteFunctional
open StripAsymptotic Matrix MeasureTheory Filter Topology

lemma physical_real_residual_formula (N : ℕ) (hN : 1≤N) :
    ∃ B : ℝ,0≤B ∧ bridgeMass N=ENNReal.ofReal B ∧
      B=2*aStar.re*((obliqueResidual N hZero (-4)).re-
        (obliqueResidual N cThreeCorrection (-4)).re*(obliqueResidual N hZero 0).re/
          (obliqueResidual N cThreeCorrection 0).re) := by
  obtain ⟨B,hB,hM,he⟩:=physical_residual_formula N hN
  refine ⟨B,hB,hM,?_⟩
  rw [←aStar_ofReal_re,←residual_ofReal_re N hZero_ofReal_re (-4),
    ←residual_ofReal_re N correction_ofReal_re (-4),←residual_ofReal_re N hZero_ofReal_re 0,
    ←residual_ofReal_re N correction_ofReal_re 0] at he
  exact_mod_cast he

/-- An upper bound for the infinite strict bridge path sum. -/
theorem physical_bridge_mass_upper :
    ∃ A : ℝ,0<A ∧ ∀ᶠ N : ℕ in atTop,
      bridgeMass N≤ENNReal.ofReal (A*((N:ℝ)+1)^(-1/4:ℝ)) := by
  obtain ⟨a,A,ha,hA,hR⟩:=source_h_residuals_at_minus_four
  refine ⟨2*aStar.re*A,mul_pos (mul_pos (by norm_num) aStar_re_pos) hA,?_⟩
  filter_upwards [hR,eventually_ge_atTop (1:ℕ)] with N hR hN
  dsimp only at hR
  obtain ⟨B,hB,hM,he⟩:=physical_real_residual_formula N hN
  rw [hM]
  apply ENNReal.ofReal_le_ofReal
  have hP : 0<((N:ℝ)+1)^(-1/4:ℝ) := by positivity
  have hd:=source_residual_denominator_neg hN
  have hnc:=cThree_residual_minus_four_nonpos N
  have hnh : 0<(obliqueResidual N hOne (-4)).re := lt_of_lt_of_le (mul_pos ha hP) hR.2.2.1
  have hnum : (obliqueResidual N cThreeCorrection (-4)).re≤0 := by
    rw [cThreeCorrection,obliqueResidual_sub (cThree_in_pairingDomain N) (hOne_in_pairingDomain N),
      Pi.sub_apply,Complex.sub_re]
    linarith
  have hquot : 0≤(obliqueResidual N cThreeCorrection (-4)).re*(obliqueResidual N hZero 0).re /
      (obliqueResidual N cThreeCorrection 0).re :=
    div_nonneg_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hnum (hZero_residual_zero_pos hN).le) hd.le
  have hapos : 0≤2*aStar.re := by linarith [aStar_re_pos]
  rw [he]
  calc
    _≤2*aStar.re*(obliqueResidual N hZero (-4)).re := mul_le_mul_of_nonneg_left (sub_le_self _ hquot) hapos
    _≤2*aStar.re*(A*((N:ℝ)+1)^(-1/4:ℝ)) := mul_le_mul_of_nonneg_left hR.2.1 hapos
    _=_ := by ring

end CriticalHoneycomb.FiniteFunctional

end


section

namespace CriticalHoneycomb.FiniteFunctional
open StripAsymptotic Filter Topology Real

lemma corrected_bracket_lower {Z A H z c d : ℝ} (hA : A ≤ 0) (hH : 0 ≤ H)
    (hz : 0 ≤ z) (hc : c<0) (hd : 0 ≤ d) :
    Z-A*z/c-H*z/(-c) ≤ Z-(A-H)*z/(c-d) := by
  have hb : 0< -c := neg_pos.mpr hc
  have hbd : 0< -c+d := by linarith
  have hnum : 0 ≤ (-A+H)*z := mul_nonneg (by linarith) hz
  have hdiv := div_le_div_of_nonneg_left hnum hb (show -c ≤ -c+d by linarith)
  have he₁ : (A-H)*z/(c-d)=(-A+H)*z/(-c+d) := by
    field_simp [hc.ne,(show c-d≠0 by linarith),hb.ne',hbd.ne']
    ring
  have he₂ : A*z/c+H*z/(-c)=(-A+H)*z/(-c) := by
    field_simp [hc.ne,hb.ne']
    ring
  rw [he₁]
  linarith

/-- Matching lower estimate for the actual infinite strict-bridge path sum. -/
theorem physical_bridge_mass_lower :
    ∃ a : ℝ,0<a ∧ ∀ᶠ N : ℕ in atTop,
      ENNReal.ofReal (a*((N:ℝ)+1)^(-1/4:ℝ))≤bridgeMass N := by
  obtain ⟨a,ha,hQc⟩:=pinned_source_residual_lower
  obtain ⟨a₀,A,ha₀,hA,hR⟩:=source_h_residuals_at_minus_four
  obtain ⟨D,hD,hzero⟩:=source_h_residuals_at_zero_upper
  let ε:=a/(2*A)
  have hε : 0<ε := by dsimp [ε]; positivity
  have ht : Tendsto (fun N : ℕ ↦ (N:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ ↦ (68*Real.pi*D)*((N:ℝ)+1)^(-1/8:ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_apply,neg_div] using ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/8)).comp ht).const_mul (68*Real.pi*D)
  have hsmall : ∀ᶠ N : ℕ in atTop,(68*Real.pi*D)*((N:ℝ)+1)^(-1/8:ℝ) ≤ ε :=
    (hlim.eventually (gt_mem_nhds hε)).mono (fun _ h ↦ h.le)
  refine ⟨aStar.re*a,mul_pos aStar_re_pos ha,?_⟩
  filter_upwards [hQc,hR,hzero,hsmall,eventually_ge_atTop (1:ℕ)] with N hQc hR hzero hsmall hN
  dsimp only at hR hzero
  let X:ℝ:=(N:ℝ)+1
  let P:ℝ:=X^(-1/4:ℝ)
  let b:ℝ:=-(obliqueResidual N (C (3*angle/2)) 0).re
  let M:ℝ:=68*Real.pi*Real.sqrt X
  have hX : 0<X := by dsimp [X]; positivity
  have hP : 0<P := Real.rpow_pos_of_pos hX _
  have hb : 0<b := neg_pos.mpr (cThree_residual_zero_neg N)
  have hM : 0<M := by dsimp [M]; positivity
  have hc : 1 ≤ b*M := (div_le_iff₀ hM).mp (source_coefficient_inverse_sqrt N)
  have hzM : (obliqueResidual N hZero 0).re*M ≤ ε := by
    calc
      _ ≤ (D*X^(-5/8:ℝ))*M := mul_le_mul_of_nonneg_right hzero.1.2 hM.le
      _ = (68*Real.pi*D)*X^(-1/8:ℝ) := by
        dsimp [M]
        rw [Real.sqrt_eq_rpow]
        calc
          _=(68*Real.pi*D)*(X^(-5/8:ℝ)*X^(1/2:ℝ)) := by ring
          _=_ := by rw [←Real.rpow_add hX]; norm_num
      _ ≤ ε := hsmall
  have hzb : (obliqueResidual N hZero 0).re ≤ ε*b := by
    apply le_of_mul_le_mul_right (a := M) ?_ hM
    calc
      _ ≤ ε := hzM
      _ ≤ ε*(b*M) := le_mul_of_one_le_right hε.le hc
      _ = _ := by ring
  have herror : (obliqueResidual N hOne (-4)).re*(obliqueResidual N hZero 0).re/b ≤ (a/2)*P := by
    calc
      _ ≤ (A*P)*(ε*b)/b := div_le_div_of_nonneg_right
        (mul_le_mul hR.2.2.2 hzb hzero.1.1 (mul_nonneg hA.le hP.le)) hb.le
      _ = _ := by dsimp [ε]; field_simp [hb.ne',hA.ne']
  have hH : 0 ≤ (obliqueResidual N hOne (-4)).re :=
    (mul_nonneg ha₀.le hP.le).trans hR.2.2.1
  have hbracket:=corrected_bracket_lower (Z:=(obliqueResidual N hZero (-4)).re)
    (cThree_residual_minus_four_nonpos N) hH hzero.1.1
    (cThree_residual_zero_neg N) hzero.2.1
  have hlo : (a/2)*P ≤ (obliqueResidual N hZero (-4)).re-
      ((obliqueResidual N (C (3*angle/2)) (-4)).re-(obliqueResidual N hOne (-4)).re)*
        (obliqueResidual N hZero 0).re/
          ((obliqueResidual N (C (3*angle/2)) 0).re-(obliqueResidual N hOne 0).re) := by
    change a*P ≤ _ at hQc
    dsimp [b] at herror
    linarith
  obtain ⟨B,hB,hBM,hBE⟩:=physical_real_residual_formula N hN
  rw [hBM]
  apply ENNReal.ofReal_le_ofReal
  have he : (obliqueResidual N cThreeCorrection)=
      obliqueResidual N (C (3*angle/2))-obliqueResidual N hOne :=
    obliqueResidual_sub (cThree_in_pairingDomain N) (hOne_in_pairingDomain N)
  rw [he,Pi.sub_apply,Pi.sub_apply,Complex.sub_re,Complex.sub_re] at hBE
  have h:=mul_le_mul_of_nonneg_left hlo (show 0 ≤ 2*aStar.re by linarith [aStar_re_pos])
  calc
    _ = 2*aStar.re*((a/2)*P) := by dsimp [P,X]; ring
    _ ≤ B := by rw [hBE]; exact h

end CriticalHoneycomb.FiniteFunctional

end

end OAI
