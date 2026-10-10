import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology

namespace SevenEighths.CenteredMomentSecondExceptionalFamilyUniform
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondHeightFamily
open CenteredMomentSecondRadicalBudget CenteredMomentSecondLiveBlock
open CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentReflectedSource CenteredMomentSecondExceptionalFamily
local notation "O" => HeckeFamily.O

def fixedExpandedCost : ℝ :=
  1296*(fixedFactor:ℝ)*(Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm

theorem fixedExpandedCost_pos : 0<fixedExpandedCost := by
  have hb : (0:ℝ)<(Ideal.span {fixedBadMask}).absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
  have h72 : (0:ℝ)<(Ideal.span {(72:O)}).absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (show (72:O)≠0 by norm_num)))
  have hf : (0:ℝ)<fixedFactor := by exact_mod_cast fixedFactor_pos
  unfold fixedExpandedCost
  positivity

theorem expandedFactor_real (η:Character) :
    (expandedFactor η:ℝ)=fixedExpandedCost*(η.modulus.absNorm:ℝ) := by
  unfold expandedFactor fixedExpandedCost
  push_cast
  ring

theorem expanded_real_bounds {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
    (h:Family η C D hC hD U τ)(hCD:primeSupport C=primeSupport D)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U radius rows W K n≠0)
    (χ ξ:RayCharacter)(R:Ideal O)(z:O) :
    (expandedConductor (τ χ) R C z:ℝ)≤
      fixedExpandedCost*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*normValue z ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤
      fixedExpandedCost*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*normValue z := by
  obtain ⟨hl,hr⟩ := expanded_conductor_bounds h hCD t S β radius rows W K hK n hne χ ξ R z
  have hl' : (expandedConductor (τ χ) R C z:ℝ)≤
      (expandedFactor η:ℝ)*R.absNorm*C.absNorm*D.absNorm*normValue z := by
    dsimp only [normValue]
    exact_mod_cast hl
  have hr' : (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤
      (expandedFactor η:ℝ)*R.absNorm*C.absNorm*D.absNorm*normValue z := by
    dsimp only [normValue]
    exact_mod_cast hr
  rw [expandedFactor_real] at hl' hr'
  exact ⟨hl',hr'⟩

theorem live_expanded_real_bounds {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
    (h:Family η C D hC hD U τ)(hCD:primeSupport C=primeSupport D)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U radius rows W K n≠0)
    (χ ξ:RayCharacter)(R:Ideal O)(z:O)(hz:z∈liveRows C D U radius rows) :
    0<radius ∧ z≠0 ∧ 1≤normValue z ∧
    (expandedConductor (τ χ) R C z:ℝ)≤
      (4*fixedExpandedCost)*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*radius ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤
      (4*fixedExpandedCost)*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*radius := by
  obtain ⟨hR,hz0,hz1,_⟩ := liveRows_geometry C D U radius rows z hz
  obtain ⟨hl,hr⟩ := expanded_real_bounds h hCD t S β radius rows W K hK n hne χ ξ R z
  have hf := fixedExpandedCost_pos
  have hbound : fixedExpandedCost*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*normValue z≤
      (4*fixedExpandedCost)*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*radius := by
    calc
      _≤fixedExpandedCost*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*(4*radius) :=
        mul_le_mul_of_nonneg_left (live_norm_le_four_radius C D U radius rows z hz)
          (by positivity)
      _=_ := by ring
  exact ⟨hR,hz0,hz1,hl.trans hbound,hr.trans hbound⟩

theorem eventually_uniform_live_caps (ε:ℝ)(hε:0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→∀η:Character,
    ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀(U:Finset (CommonIndex C D))(τ:RayCharacter→Character),Family η C D hC hD U τ→
    ∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U radius rows W K n≠0→
    ∀(χ ξ:RayCharacter)(R:Ideal O)(c d r m q:ℝ),
    (η.modulus.absNorm:ℝ)≤Z^q→(C.absNorm:ℝ)≤Z^c→(D.absNorm:ℝ)≤Z^d→
    (R.absNorm:ℝ)≤Z^r→ radius≤Z^m→∀z∈liveRows C D U radius rows,
    0<radius ∧ z≠0 ∧ 1≤normValue z ∧
    (expandedConductor (τ χ) R C z:ℝ)≤Z^(c+d+r+m+q+ε) ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤Z^(c+d+r+m+q+ε) := by
  have he := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (4*fixedExpandedCost)
  obtain ⟨Z₁,hZ₁⟩ := Filter.eventually_atTop.1 he
  refine ⟨max 2 Z₁,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro Z hZ η C D hC hD hCD U τ h t S β radius rows W K hK n hne χ ξ R c d r m q hη hCN hDN hRN hrad z hz
  have hZpos : 0<Z := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hZ)
  have hconstant := hZ₁ Z ((le_max_right _ _).trans hZ)
  obtain ⟨hR,hz0,hz1,hl,hr⟩ := live_expanded_real_bounds h hCD t S β radius rows W K hK n hne χ ξ R z hz
  have hbound : (4*fixedExpandedCost)*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*radius≤
      Z^(c+d+r+m+q+ε) := by
    calc
      _≤Z^ε*Z^q*Z^r*Z^c*Z^d*Z^m := by gcongr
      _=Z^(c+d+r+m+q+ε) := by
        rw [←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos,
          ←Real.rpow_add hZpos,←Real.rpow_add hZpos]
        congr 1
        ring
  exact ⟨hR,hz0,hz1,hl.trans hbound,hr.trans hbound⟩

theorem exists_uniform_exceptional_family (ε:ℝ)(hε:0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀(η:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D),
    primeSupport C=primeSupport D→∀U:Finset (CommonIndex C D),
    ∃τ:RayCharacter→Character,Family η C D hC hD U τ ∧
    ∀Z:ℝ,Z₀≤Z→∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U radius rows W K n≠0→
    ∀(χ ξ:RayCharacter)(R:Ideal O)(c d r m q:ℝ),
    (η.modulus.absNorm:ℝ)≤Z^q→(C.absNorm:ℝ)≤Z^c→(D.absNorm:ℝ)≤Z^d→
    (R.absNorm:ℝ)≤Z^r→ radius≤Z^m→∀z∈liveRows C D U radius rows,
    0<radius ∧ z≠0 ∧ 1≤normValue z ∧
    (expandedConductor (τ χ) R C z:ℝ)≤Z^(c+d+r+m+q+ε) ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤Z^(c+d+r+m+q+ε) := by
  obtain ⟨Z₀,hZ₀,hcaps⟩ := eventually_uniform_live_caps ε hε
  refine ⟨Z₀,hZ₀,?_⟩
  intro η C D hC hD hCD U
  obtain ⟨τ,hτ⟩ := exists_exceptional_family η C D hC hD hCD U
  refine ⟨τ,hτ,?_⟩
  intro Z hZ
  exact hcaps Z hZ η C D hC hD hCD U τ hτ

end SevenEighths.CenteredMomentSecondExceptionalFamilyUniform

end

end OAI
