import OAI.NumberTheory.DirichletL.Moments.AmplificationRadicalChoice
import OAI.NumberTheory.DirichletL.Moments.SecondChildRadialWidth
import OAI.NumberTheory.DirichletL.Moments.CommonRadiusSaving
import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalLedger

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentAmplifiedChildWidth
open ActualEisensteinCubic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentChildRows CenteredMomentSecondRadicalBudget
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondChildRadialWidth
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondLiveBlock
open CenteredMomentSecondActualWidth CenteredMomentSecondWidthDrop
open CenteredMomentSecondCanonical CenteredMomentSecondHeightFamily
open CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

theorem modulus_pos (η:Character) : 0<(η.modulus.absNorm:ℝ) :=
  norm_pos _ η.modulus_ne_bot
theorem span_pos (m:O)(hm:m≠0) : 0<((Ideal.span {m}).absNorm:ℝ) :=
  norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr hm)

theorem canonical_modulus_log (η ρ:Character)(m:O)(hm:m≠0)
    (I J:Ideal O)(A:Finset (CommonIndex I J))(Z:ℝ)
    (hmod:ρ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A*activeConductor I J}) :
    Real.logb Z (ρ.modulus.absNorm:ℝ)=
      Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z ((Ideal.span {m}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)+
      Real.logb Z ((∏P∈A,P.val).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ) := by
  have he:0<((∏P∈A,P.val).absNorm:ℝ) := by
    apply norm_pos
    exact Finset.prod_ne_zero_iff.mpr (fun P _=>(IdealMobiusDivisorSum.support_prime (Finset.mem_inter.mp P.property).1).ne_zero)
  rw [hmod,first_displayed_norm]
  push_cast
  rw [Real.logb_mul (mul_pos (mul_pos (modulus_pos η) (span_pos m hm))
      (span_pos 72 (by norm_num))).ne' (mul_pos he (active_norm_pos I J)).ne',
    Real.logb_mul (mul_pos (modulus_pos η) (span_pos m hm)).ne'
      (span_pos 72 (by norm_num)).ne',
    Real.logb_mul (modulus_pos η).ne' (span_pos m hm).ne',
    Real.logb_mul he.ne' (active_norm_pos I J).ne']
  ring

theorem radical_error_log_bound (ρ η:Character)(χ:RayCharacter)(m p:O)
    (hm:m≠0)(hp:p≠0)(Z:ℝ)(hZ:1<Z)(n:ℕ)(hn:n=0∨n=5∨n=6)
    (hN:η.modulus.absNorm≤radicalBound (childCharacter ρ χ) m p (errorMovingExponent n)) :
    Real.logb Z (η.modulus.absNorm:ℝ)≤
      Real.logb Z (ρ.modulus.absNorm:ℝ)+Real.logb Z ((Ideal.span {m}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(12:O)}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)+errorMoving p Z (n+1) := by
  have hmpos:=span_pos m hm
  have h12:=span_pos 12 (by norm_num)
  have h72:=span_pos 72 (by norm_num)
  have hρ:=modulus_pos ρ
  have hray:( (childCharacter ρ χ).modulus.absNorm:ℝ)≤
      (ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm := by
    exact_mod_cast child_modulus_bound ρ χ
  have hb:(η.modulus.absNorm:ℝ)≤
      ((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
      (Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm*Z^(errorMoving p Z (n+1)) := by
    have hh:(η.modulus.absNorm:ℝ)≤(radicalBound (childCharacter ρ χ) m p (errorMovingExponent n):ℝ):=by exact_mod_cast hN
    rw [radicalBound_error_power _ m p hp Z hZ n hn] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hray (by positivity))
        (by positivity)) (by positivity))
  have hh:=Real.logb_le_logb_of_le hZ (modulus_pos η) hb
  rw [Real.logb_mul (by positivity : (0:ℝ)<
      ((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
      (Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm).ne'
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).ne',
    Real.logb_mul (by positivity : (0:ℝ)<
      ((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*(Ideal.span {m}).absNorm).ne'
      (span_pos 72 (by norm_num)).ne',
    Real.logb_mul (mul_pos (modulus_pos ρ) (span_pos 12 (by norm_num))).ne' (span_pos m hm).ne',
    Real.logb_mul (modulus_pos ρ).ne' (span_pos 12 (by norm_num)).ne',
    Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  linarith

theorem common_nominal_identity (A c d R E m q w wo σ δ reserve branch:ℝ) :
    2*(A-c-w)-(2*A-c-d+R+E-m+
      max (d-c-2*w+wo) 0+branch*σ+δ+reserve)+(q+R+E+wo)=
    m+q+(d-c-2*w+wo-max (d-c-2*w+wo) 0)-branch*σ-δ-reserve := by ring

theorem common_nominal_le (A c d R E m q w wo σ δ reserve branch:ℝ) :
    2*(A-c-w)-(2*A-c-d+R+E-m+
      max (d-c-2*w+wo) 0+branch*σ+δ+reserve)+(q+R+E+wo)≤
    m+q-branch*σ-δ-reserve := by
  rw [common_nominal_identity]
  linarith [le_max_left (d-c-2*w+wo) (0:ℝ)]

theorem shortened_log (I J:Ideal O)(X Z:ℝ)(hX:0<X)(p:O)(hp:p≠0)(k:ℕ) :
    Real.logb Z (X/((commonPart I J).absNorm*(normValue p)^k))=
      Real.logb Z X-Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)-errorRemoval p Z k := by
  rw [Real.logb_div hX.ne' (mul_pos (norm_pos _ (commonPart_ne_zero I J))
    (pow_pos (normValue_pos p hp) k)).ne',
    Real.logb_mul (norm_pos _ (commonPart_ne_zero I J)).ne' (pow_pos (normValue_pos p hp) k).ne',
    Real.logb_pow]
  unfold errorRemoval
  ring

theorem main_nominal_bound (η ρ:Character)(m:O)(hm:m≠0)(I J:Ideal O)
    (A:Finset (CommonIndex I J))(K X Z σ δ reserve:ℝ)
    (hK:0<K)(hX:0<X)(hZ:1<Z)
    (hmod:ρ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A*activeConductor I J}) :
    2*Real.logb Z (X/(commonPart I J).absNorm)-
      Real.logb Z (mainCommonRadius Z (Real.logb Z (Ideal.absNorm (commonPart J I):ℝ))
        (nominalLog I J (∏P∈A,P.val) K X Z) (Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)) σ δ reserve)+
      Real.logb Z (ρ.modulus.absNorm:ℝ)≤
      Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z ((Ideal.span {m}).absNorm:ℝ)+Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)-
      2*σ-δ-reserve := by
  have he:(∏P∈A,P.val)≠0 := Finset.prod_ne_zero_iff.mpr (fun P _=>(IdealMobiusDivisorSum.support_prime (Finset.mem_inter.mp P.property).1).ne_zero)
  rw [Real.logb_div hX.ne' (norm_pos _ (commonPart_ne_zero I J)).ne',
    mainCommonRadius,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne',
    nominalLog,CenteredMomentFirstPhysicalLedger.nominal_log I J _ he Z K X hK hX,
    canonical_modulus_log η ρ m hm I J A Z hmod]
  linarith [le_max_left (Real.logb Z (Ideal.absNorm (commonPart J I):ℝ)-
    Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)) (0:ℝ)]

theorem error_nominal_bound (η ρ θ:Character)(χ:RayCharacter)(m₀ m₁ p:O)
    (hm₀:m₀≠0)(hm₁:m₁≠0)(hp:p≠0)(I J:Ideal O)(A:Finset (CommonIndex I J))
    (K X Z σ δ reserve:ℝ)(hK:0<K)(hX:0<X)(hZ:1<Z)
    (hmod:ρ.modulus=η.modulus*Ideal.span {m₀}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A*activeConductor I J})
    (n:ℕ)(hn:n=0∨n=5∨n=6)
    (hN:θ.modulus.absNorm≤radicalBound (childCharacter ρ χ) m₁ p (errorMovingExponent n)) :
    2*Real.logb Z (X/((commonPart I J).absNorm*(normValue p)^(n+1)))-
      Real.logb Z (errorCommonRadius Z (Real.logb Z (Ideal.absNorm (commonPart J I):ℝ))
        (nominalLog I J (∏P∈A,P.val) K X Z) (Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)) σ δ reserve p (n+1))+
      Real.logb Z (θ.modulus.absNorm:ℝ)≤
      Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z ((Ideal.span {m₀}).absNorm:ℝ)+Real.logb Z ((Ideal.span {m₁}).absNorm:ℝ)+
      2*Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(12:O)}).absNorm:ℝ)-σ-δ-reserve := by
  have he:(∏P∈A,P.val)≠0 := Finset.prod_ne_zero_iff.mpr (fun P _=>(IdealMobiusDivisorSum.support_prime (Finset.mem_inter.mp P.property).1).ne_zero)
  have hq:=radical_error_log_bound ρ θ χ m₁ p hm₁ hp Z hZ n hn hN
  rw [canonical_modulus_log η ρ m₀ hm₀ I J A Z hmod] at hq
  rw [shortened_log I J X Z hX p hp (n+1),errorCommonRadius,
    Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne',nominalLog,
    CenteredMomentFirstPhysicalLedger.nominal_log I J _ he Z K X hK hX]
  linarith [le_max_left (Real.logb Z (Ideal.absNorm (commonPart J I):ℝ)-
    Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)-2*errorRemoval p Z (n+1)+errorMoving p Z (n+1)) (0:ℝ)]

theorem physical_radial_budget {η:Character}{C D:Ideal O}
    {hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Z H L Tsec Csec ξ:ℝ)(hZ:1<Z)(hH:0<H)(hL:0<L)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*(H^2/L))(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W L n≠0)
    (χ:RayCharacter)(b:ℝ)(hb:0<b) :
    Real.logb Z (b*dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      2*Real.logb Z H-Real.logb Z L+Real.logb Z (η.modulus.absNorm:ℝ)-
      Real.logb Z (normValue (commonFrequencyGenerator C D))+
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)) := by
  have hw:=radial_radius_log_budget h t S β (frequencyRadius Tsec Z ξ) rows W L hL n hne Z hZ χ b hb
  have hl:=Real.logb_le_logb_of_le hZ hT hscale
  rw [Real.logb_mul hCs.ne' (div_pos (sq_pos_of_pos hH) hL).ne',
    Real.logb_div (sq_pos_of_pos hH).ne' hL.ne',Real.logb_pow] at hl
  have hr:Real.logb Z (frequencyRadius Tsec Z ξ)≤
      2*Real.logb Z H-Real.logb Z L+ξ/2+Real.logb Z Csec := by
    rw [frequencyRadius,Real.logb_mul hT.ne'
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).ne',
      Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
    push_cast at hl
    linarith
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*b*Csec*(fixedFactor:ℝ))=
      Real.logb Z Csec+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul hCs.ne' (by positivity : (16:ℝ)*b*fixedFactor≠0)]
    congr 1
    ring
  rw [hf]
  linarith

theorem physical_declared_budget {η:Character}{C D:Ideal O}
    {hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Z H L Tsec Csec ξ:ℝ)(hZ:1<Z)(hH:0<H)(hL:0<L)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*(H^2/L))(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W L n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      2*Real.logb Z H-Real.logb Z L+Real.logb Z (η.modulus.absNorm:ℝ)+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)) := by
  have hh:=physical_radial_budget h t S β rows W Z H L Tsec Csec ξ hZ hH hL hT hCs hscale n hne χ b hb
  have hc:=actual_common_log_ge_unit C D hC U Z hZ
  have hbH:1≤b*dyadicScale (n 1):=(normValue_ge_one y hy0).trans
    (radial_support_bound n Φ b hs y hy)
  rw [max_eq_right hbH]
  linarith

theorem physical_whole_budget {η:Character}{C D:Ideal O}
    {hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Z H L Tsec Csec ξ:ℝ)(hZ:1<Z)(hH:0<H)(hL:0<L)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*(H^2/L))(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W L n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y*((τ χ).modulus.absNorm:ℝ)≤
      Z^(2*Real.logb Z H-Real.logb Z L+Real.logb Z (η.modulus.absNorm:ℝ)+ξ/2+
        Real.logb Z (16*b*Csec*(fixedFactor:ℝ))) := by
  have hh:=physical_radial_budget h t S β rows W Z H L Tsec Csec ξ hZ hH hL hT hCs hscale n hne χ b hb
  have hc:=actual_common_log_ge_unit C D hC U Z hZ
  have hb':Real.logb Z (b*dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      2*Real.logb Z H-Real.logb Z L+Real.logb Z (η.modulus.absNorm:ℝ)+ξ/2+
        Real.logb Z (16*b*Csec*(fixedFactor:ℝ)) := by linarith
  rw [←Real.logb_mul (mul_pos hb (dyadicScale_pos (n 1))).ne' (modulus_pos (τ χ)).ne'] at hb'
  exact (mul_le_mul_of_nonneg_right (radial_support_bound n Φ b hs y hy)
    (modulus_pos (τ χ)).le).trans
    ((Real.logb_le_iff_le_rpow hZ (mul_pos (mul_pos hb (dyadicScale_pos (n 1)))
      (modulus_pos (τ χ)))).mp hb')

theorem original_coefficient_fixed_mask {ι:Type*}[Fintype ι]
    (D:OriginalData ι)(ρ:Character)(t T:ℝ) :
    D.coefficient ρ fixedBadMask t T=
      fun I:supportedColumns D.columns => (Real.sqrt T:ℂ)⁻¹*(D.beta I*heightCoeff ρ t I) := by
  funext I
  rw [OriginalData.coefficient,←heightCoeff_eq_fixed_rowWeight ρ t I
    (Finset.mem_filter.mp I.property).2]

def presentationFactor : ℝ :=
  ((Ideal.span {(72:O)}).absNorm:ℝ)*(fixedFactor:ℝ)

theorem presentationFactor_pos : 0<presentationFactor :=
  mul_pos (span_pos 72 (by norm_num)) (by exact_mod_cast fixedFactor_pos)

theorem presentationFactor_log (Z:ℝ) : Real.logb Z presentationFactor=
    2*Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(12:O)}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {fixedBadMask}).absNorm:ℝ) := by
  unfold presentationFactor fixedFactor
  push_cast
  rw [Real.logb_mul (span_pos 72 (by norm_num)).ne'
      (mul_pos (mul_pos (span_pos 12 (by norm_num)) (span_pos fixedBadMask fixedBadMask_ne_zero))
        (span_pos 72 (by norm_num))).ne',
    Real.logb_mul (mul_pos (span_pos 12 (by norm_num)) (span_pos fixedBadMask fixedBadMask_ne_zero)).ne'
      (span_pos 72 (by norm_num)).ne',
    Real.logb_mul (span_pos 12 (by norm_num)).ne' (span_pos fixedBadMask fixedBadMask_ne_zero).ne']
  ring

theorem first_fixed_log_le (Z:ℝ)(hZ:1<Z) :
    Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)≤Real.logb Z presentationFactor := by
  apply Real.logb_le_logb_of_le hZ (span_pos 72 (by norm_num))
  have hf:(1:ℝ)≤fixedFactor:=by exact_mod_cast fixedFactor_pos
  exact le_mul_of_one_le_right (span_pos 72 (by norm_num)).le hf

theorem exists_fixed_width_threshold (b Csec σ:ℝ)(hb:0<b)(hCs:0<Csec)(hσ:0<σ) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→∀ξ:ℝ,ξ≤σ/4→
      Real.logb Z ((Ideal.span {fixedBadMask}).absNorm:ℝ)+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor)<σ/2 := by
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  let C:ℝ:=((Ideal.span {fixedBadMask}).absNorm:ℝ)*(16*b*Csec*(fixedFactor:ℝ)*presentationFactor)
  have hCp:0<C:=mul_pos (span_pos fixedBadMask fixedBadMask_ne_zero)
    (mul_pos (by positivity : (0:ℝ)<16*b*Csec*fixedFactor) presentationFactor_pos)
  have he:=(Filter.tendsto_atTop.1 (tendsto_rpow_atTop (show 0<σ/4 by linarith))) C
  obtain ⟨Z₀,hZ₀⟩:=Filter.eventually_atTop.1 (he.and (Filter.eventually_gt_atTop (1:ℝ)))
  refine ⟨max 2 Z₀,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro Z hZ ξ hξ
  obtain ⟨hCZ,hZ1⟩:=hZ₀ Z ((le_max_right _ _).trans hZ)
  have hh:Real.logb Z C≤σ/4:=(Real.logb_le_iff_le_rpow hZ1 hCp).mpr hCZ
  dsimp [C] at hh
  rw [Real.logb_mul (span_pos fixedBadMask fixedBadMask_ne_zero).ne'
    (mul_pos (by positivity : (0:ℝ)<16*b*Csec*fixedFactor) presentationFactor_pos).ne'] at hh
  linarith

def fixedWidthThreshold (b Csec σ:ℝ)(hb:0<b)(hCs:0<Csec)(hσ:0<σ) : ℝ :=
  (exists_fixed_width_threshold b Csec σ hb hCs hσ).choose

theorem fixedWidthThreshold_spec (b Csec σ:ℝ)(hb:0<b)(hCs:0<Csec)(hσ:0<σ) :
    1<fixedWidthThreshold b Csec σ hb hCs hσ ∧
    ∀Z:ℝ,fixedWidthThreshold b Csec σ hb hCs hσ≤Z→∀ξ:ℝ,ξ≤σ/4→
      Real.logb Z ((Ideal.span {fixedBadMask}).absNorm:ℝ)+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor)<σ/2 :=
  (exists_fixed_width_threshold b Csec σ hb hCs hσ).choose_spec

section ActualSource
variable (η ρ:Character)(m:O)(hm:m≠0)(I J:Ideal O)(A:Finset (CommonIndex I J))
  (K X Z σ δ reserve:ℝ)(hK:0<K)(hX:0<X)(hZ:1<Z)
  (hmod:ρ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A*activeConductor I J})

local notation "cc" => Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)
local notation "dd" => Real.logb Z (Ideal.absNorm (commonPart J I):ℝ)
local notation "kk" => nominalLog I J (∏P∈A,Subtype.val P) K X Z
local notation "Lm" => mainCommonRadius Z dd kk cc σ δ reserve
local notation "Hx" => X/Ideal.absNorm (commonPart I J)
local notation "parentWidth" => Real.logb Z K+Real.logb Z (Ideal.absNorm (Character.modulus η):ℝ)+Real.logb Z (Ideal.absNorm (Ideal.span (Singleton.singleton m)):ℝ)
include σ δ reserve hm hK hX hZ hmod

theorem main_nominal_fixed :
    2*Real.logb Z Hx-Real.logb Z Lm+Real.logb Z (ρ.modulus.absNorm:ℝ)≤
      parentWidth+Real.logb Z presentationFactor-2*σ-δ-reserve := by
  have hh:=main_nominal_bound η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod
  linarith [first_fixed_log_le Z hZ]

theorem error_nominal_fixed (θ:Character)(χ:RayCharacter)(p:O)(hp:p≠0)
    (n:ℕ)(hn:n=0∨n=5∨n=6)
    (hN:θ.modulus.absNorm≤radicalBound (childCharacter ρ χ) fixedBadMask p (errorMovingExponent n)) :
    2*Real.logb Z (X/((commonPart I J).absNorm*(normValue p)^(n+1)))-
      Real.logb Z (errorCommonRadius Z dd kk cc σ δ reserve p (n+1))+
      Real.logb Z (θ.modulus.absNorm:ℝ)≤
      parentWidth+Real.logb Z presentationFactor-σ-δ-reserve := by
  have hh:=error_nominal_bound η ρ θ χ m fixedBadMask p hm fixedBadMask_ne_zero hp
    I J A K X Z σ δ reserve hK hX hZ hmod n hn hN
  rw [presentationFactor_log]
  linarith

theorem main_declared_width {C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}(h:Family ρ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)(hscale:Tsec≤Csec*(Hx^2/Lm))
    (n:Fin 4→ℤ)
    (hne:physicalBlock ρ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W Lm n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      parentWidth-2*σ-δ-reserve+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor) := by
  have hHx:0<Hx:=div_pos hX (norm_pos _ (commonPart_ne_zero I J))
  have hL:0<Lm:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hw:=physical_declared_budget h t S β rows W Z Hx Lm Tsec Csec ξ hZ hHx hL hT hCs hscale n hne χ Φ b hb hs y hy0 hy
  have hnom:=main_nominal_fixed η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  rw [Real.logb_mul (by positivity : (0:ℝ)<16*b*Csec*fixedFactor).ne' presentationFactor_pos.ne']
  linarith

theorem error_declared_width (θ:Character)(χ₀:RayCharacter)(p:O)(hp:p≠0)
    (k:ℕ)(hk:k=0∨k=5∨k=6)
    (hN:θ.modulus.absNorm≤radicalBound (childCharacter ρ χ₀) fixedBadMask p (errorMovingExponent k))
    {C D:Ideal O}{hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family θ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*((X/((commonPart I J).absNorm*(normValue p)^(k+1)))^2/
      errorCommonRadius Z dd kk cc σ δ reserve p (k+1)))
    (n:Fin 4→ℤ)
    (hne:physicalBlock θ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W
      (errorCommonRadius Z dd kk cc σ δ reserve p (k+1)) n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      parentWidth-σ-δ-reserve+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor) := by
  have hHx:0<X/((commonPart I J).absNorm*(normValue p)^(k+1)):=
    div_pos hX (mul_pos (norm_pos _ (commonPart_ne_zero I J)) (pow_pos (normValue_pos p hp) _))
  have hL:0<errorCommonRadius Z dd kk cc σ δ reserve p (k+1):=
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hw:=physical_declared_budget h t S β rows W Z _ _ Tsec Csec ξ hZ hHx hL hT hCs hscale n hne χ Φ b hb hs y hy0 hy
  have hnom:=error_nominal_fixed η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod θ χ₀ p hp k hk hN
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  rw [Real.logb_mul (by positivity : (0:ℝ)<16*b*Csec*fixedFactor).ne' presentationFactor_pos.ne']
  linarith

theorem main_whole_width {C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}(h:Family ρ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)(hscale:Tsec≤Csec*(Hx^2/Lm))
    (n:Fin 4→ℤ)
    (hne:physicalBlock ρ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W Lm n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y*((τ χ).modulus.absNorm:ℝ)≤
      Z^(parentWidth-2*σ-δ-reserve+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor)) := by
  have hHx:0<Hx:=div_pos hX (norm_pos _ (commonPart_ne_zero I J))
  have hL:0<Lm:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hw:=physical_whole_budget h t S β rows W Z Hx Lm Tsec Csec ξ hZ hHx hL hT hCs hscale n hne χ Φ b hb hs y hy
  have hnom:=main_nominal_fixed η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  apply hw.trans
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  rw [Real.logb_mul (by positivity : (0:ℝ)<16*b*Csec*fixedFactor).ne' presentationFactor_pos.ne']
  linarith

theorem error_whole_width (θ:Character)(χ₀:RayCharacter)(p:O)(hp:p≠0)
    (k:ℕ)(hk:k=0∨k=5∨k=6)
    (hN:θ.modulus.absNorm≤radicalBound (childCharacter ρ χ₀) fixedBadMask p (errorMovingExponent k))
    {C D:Ideal O}{hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family θ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*((X/((commonPart I J).absNorm*(normValue p)^(k+1)))^2/
      errorCommonRadius Z dd kk cc σ δ reserve p (k+1)))
    (n:Fin 4→ℤ)
    (hne:physicalBlock θ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W
      (errorCommonRadius Z dd kk cc σ δ reserve p (k+1)) n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y*((τ χ).modulus.absNorm:ℝ)≤
      Z^(parentWidth-σ-δ-reserve+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor)) := by
  have hHx:0<X/((commonPart I J).absNorm*(normValue p)^(k+1)):=
    div_pos hX (mul_pos (norm_pos _ (commonPart_ne_zero I J)) (pow_pos (normValue_pos p hp) _))
  have hL:0<errorCommonRadius Z dd kk cc σ δ reserve p (k+1):=
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hw:=physical_whole_budget h t S β rows W Z _ _ Tsec Csec ξ hZ hHx hL hT hCs hscale n hne χ Φ b hb hs y hy
  have hnom:=error_nominal_fixed η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod θ χ₀ p hp k hk hN
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  apply hw.trans
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  rw [Real.logb_mul (by positivity : (0:ℝ)<16*b*Csec*fixedFactor).ne' presentationFactor_pos.ne']
  linarith

theorem main_declared_width_drop {C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}(h:Family ρ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)(hscale:Tsec≤Csec*(Hx^2/Lm))
    (n:Fin 4→ℤ)
    (hne:physicalBlock ρ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W Lm n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0)
    (hmask:m=fixedBadMask)(q:ℝ)(hcap:(η.modulus.absNorm:ℝ)≤Z^q)
    (hσ:0<σ)(hδ:0≤δ)(hr:0≤reserve)(hξ:ξ≤σ/4)
    (hlarge:fixedWidthThreshold b Csec σ hb hCs hσ≤Z) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)<
      Real.logb Z K+q-σ/2 := by
  have hw:=main_declared_width η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod h t S β rows W Tsec Csec ξ hT hCs hscale n hne χ Φ b hb hs y hy0 hy
  have hq:Real.logb Z (η.modulus.absNorm:ℝ)≤q:=
    (Real.logb_le_iff_le_rpow hZ (modulus_pos η)).mpr hcap
  have hc:=(fixedWidthThreshold_spec b Csec σ hb hCs hσ).2 Z hlarge ξ hξ
  rw [hmask] at hw
  linarith

theorem error_declared_width_drop (θ:Character)(χ₀:RayCharacter)(p:O)(hp:p≠0)
    (k:ℕ)(hk:k=0∨k=5∨k=6)
    (hN:θ.modulus.absNorm≤radicalBound (childCharacter ρ χ₀) fixedBadMask p (errorMovingExponent k))
    {C D:Ideal O}{hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family θ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*((X/((commonPart I J).absNorm*(normValue p)^(k+1)))^2/
      errorCommonRadius Z dd kk cc σ δ reserve p (k+1)))
    (n:Fin 4→ℤ)
    (hne:physicalBlock θ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W
      (errorCommonRadius Z dd kk cc σ δ reserve p (k+1)) n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0)
    (hmask:m=fixedBadMask)(q:ℝ)(hcap:(η.modulus.absNorm:ℝ)≤Z^q)
    (hσ:0<σ)(hδ:0≤δ)(hr:0≤reserve)(hξ:ξ≤σ/4)
    (hlarge:fixedWidthThreshold b Csec σ hb hCs hσ≤Z) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)<
      Real.logb Z K+q-σ/2 := by
  have hw:=error_declared_width η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod θ χ₀ p hp k hk hN h t S β rows W Tsec Csec ξ hT hCs hscale n hne χ Φ b hb hs y hy0 hy
  have hq:Real.logb Z (η.modulus.absNorm:ℝ)≤q:=
    (Real.logb_le_iff_le_rpow hZ (modulus_pos η)).mpr hcap
  have hc:=(fixedWidthThreshold_spec b Csec σ hb hCs hσ).2 Z hlarge ξ hξ
  rw [hmask] at hw
  linarith

end ActualSource
end SevenEighths.CenteredMomentAmplifiedChildWidth

end

end OAI
