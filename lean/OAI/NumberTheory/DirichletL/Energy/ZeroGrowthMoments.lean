import OAI.NumberTheory.DirichletL.Energy.ZeroGrowthChild
import OAI.NumberTheory.DirichletL.Energy.ZeroReflectionSupport
import OAI.NumberTheory.DirichletL.Energy.ReferenceLowControl

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroGrowthMoments
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyZeroGrowth CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentEnergyZeroGrowthChild CenteredMomentEnergyReferenceLowControl
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentScaleSupremum
open CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

theorem reflected_uniform (a b:ℝ)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃D:ℝ,0<D ∧
    ∀(bΦ Bmask L Mcap ε Z:ℝ)(Q:Ideal O)(degree:ℕ)(C:ℝ),0≤C →
    ZeroGrowthAt Q a b bΦ Bmask L Mcap ε Z degree S C → 0≤Bmask →
    ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → s.width≤Mcap →
    ∀(Wshort:𝓢(ℝ,ℂ))(_hsW:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b)
      (j k:Fin 2)(v t X₁ X₂:ℝ),0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      (C*diagonalControl s.radial.profile*D*(sourceControl T Wshort)^2*
        (1+|t|)^(2*n)*Z^(max s.width (length Z X₁+length Z X₂)+ε))*(1+‖v‖)^(2*n):=by
  obtain ⟨n,T,D,hD,hd⟩:=reflected_child_control a b ha hlo hhi S 0
  refine ⟨n,T,D,hD,?_⟩
  intro bΦ Bmask L Mcap ε Z Q degree C hC hlow hB s hQ hs
    Wshort hsW j k v t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hh:=reflected_from_growth a b bΦ Bmask L Mcap ε Z Q degree S C hlow hB ha hlo hhi
    s hQ hs Wshort hsW j k v t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hb:=hd Wshort hsW j k v t 0 (le_refl 0)
  simp only [add_zero,zero_add,pow_zero,mul_one] at hb
  have hp:0≤C*diagonalControl s.radial.profile:=mul_nonneg hC (by
    unfold diagonalControl
    positivity)
  have hz:0≤Z^(max s.width (length Z X₁+length Z X₂)+ε):=(Real.rpow_pos_of_pos (zero_lt_one.trans_le s.base_ge_one) _).le
  have hmul:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hp) hz
  apply hh.trans
  convert hmul using 1 ; ring

lemma actual_growth_power (Z b M xi epsilon loss Xshort Xlong Nshort Nlong x:ℝ)
    (hZ:1<Z)(hb:0<b)(hM:0≤M)(he:0≤epsilon)(hxi:0≤xi)
    (hshort:0<Xshort)(hlong:Xshort≤Xlong)(hNs:1≤Nshort)(hNl:1≤Nlong)
    (hsupport:1≤b*Xlong)(hdef:Real.logb Z (max 1 b)≤epsilon)
    (hlive:0≤M-Real.logb Z (Xlong/Nlong)+xi)
    (hx:x∈Set.Icc 0 (max 0 (M-Real.logb Z (Xlong/Nlong)+xi)*Real.log Z)):
    Z^(max M (length Z (Real.exp x)+length Z (Xshort/Nshort))+loss)≤
      Nlong*Z^(M+loss+epsilon+xi):=by
  have hg:=live_deleted_growth Z b M xi Xshort Xlong Nshort Nlong
    hZ hb hM hshort hlong hNs hNl hsupport hlive x hx
  have hN:=Real.logb_nonneg hZ hNl
  have hemax:max M (length Z (Real.exp x)+length Z (Xshort/Nshort))≤
      M+Real.logb Z Nlong+epsilon+xi:=max_le (by linarith) (by linarith)
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ.le (show max M (length Z (Real.exp x)+length Z (Xshort/Nshort))+loss≤M+Real.logb Z Nlong+epsilon+xi+loss by linarith)
  apply hp.trans_eq
  rw [show M+Real.logb Z Nlong+epsilon+xi+loss=
    Real.logb Z Nlong+(M+loss+epsilon+xi) by ring,
    Real.rpow_add (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (zero_lt_one.trans_le hNl)]

end SevenEighths.CenteredMomentEnergyZeroGrowthMoments

end

end OAI
