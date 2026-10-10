import OAI.NumberTheory.DirichletL.Energy.ZeroGrowthMoments

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroGrowthWindow
open CenteredMomentFiniteProfileExceptional
open HeckeFamily HeckeDyadic QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyZeroGrowth
open CenteredMomentEnergyZeroGrowthMoments CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceLowWindow CenteredMomentEnergyReferenceLowBranchGeometry
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

theorem actual_reflected_window (a b:ℝ)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃D:ℝ,0<D ∧
    ∀(bΦ Bmask L Mcap loss Z:ℝ)(Q:Ideal O)(degree:ℕ)(C:ℝ),0≤C→
    ZeroGrowthAt Q a b bΦ Bmask L Mcap loss Z degree S C→0≤Bmask→
    ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤Mcap→
    ∀(Wshort:𝓢(ℝ,ℂ)),Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b→
    ∀xi epsilon Xshort Xlong:ℝ,0≤xi→0≤epsilon→1<Z→
    Real.logb Z (max 1 b)≤epsilon→Mcap+Bmask+epsilon+xi≤L→
    0<Xshort→Xshort≤Xlong→Xshort≤Z^L→1≤b*Xlong→
    ∀Dshort Dlong:Finset (Ideal O),
    Dshort∈(CompletedGauss.primeSupport s.puncture).powerset→
    Dlong∈(CompletedGauss.primeSupport s.puncture).powerset→
    let Nshort:ℝ:=(∏P∈Dshort,P).absNorm;
    let Nlong:ℝ:=(∏P∈Dlong,P).absNorm;
    0≤s.width-Real.logb Z (Xlong/Nlong)+xi→
    ∀(j k:Fin 2)(v t x:ℝ),
    x∈Set.Icc 0 (max 0 (s.width-Real.logb Z (Xlong/Nlong)+xi)*Real.log Z)→
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) (Xshort/Nshort) 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      (C*diagonalControl s.radial.profile*D*(sourceControl T Wshort)^2*
        (1+|t|)^(2*n)*Z^(s.width+loss+epsilon+xi)*Nlong)*(1+‖v‖)^(2*n):=by
  obtain ⟨n,T,D,hD,hu⟩:=reflected_uniform a b ha hlo hhi S
  refine ⟨n,T,D,hD,?_⟩
  intro bΦ Bmask L Mcap loss Z Q degree C hC hgrowth hB s hQ hs Wshort hsW
    xi epsilon Xshort Xlong hxi he hZ hdef hL hshort hlong hshortcap hsupport Dshort Dlong hDs hDl
  dsimp only
  intro hlive j k v t x hx
  obtain ⟨hNs,hNscap⟩:=divisor_norm s Dshort hDs
  obtain ⟨hNl,hNlcap⟩:=divisor_norm s Dlong hDl
  have hpS:0<((∏P∈Dshort,P).absNorm:ℝ):=zero_lt_one.trans_le hNs
  have hpL:0<((∏P∈Dlong,P).absNorm:ℝ):=zero_lt_one.trans_le hNl
  have hlogN:Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)≤Bmask:=
    (Real.logb_le_iff_le_rpow hZ hpL).mpr hNlcap
  have hlen:=live_deleted_growth Z b s.width xi Xshort Xlong _ _ hZ (by linarith)
    s.width_nonneg hshort hlong hNs hNl hsupport hlive x hx
  have hn:=length_nonneg Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ)) hZ
  have hlenx:length Z (Real.exp x)≤L:=by linarith
  have hlogx:Real.logb Z (Real.exp x)≤length Z (Real.exp x):=by
    rw [length_eq_max_log Z _ hZ (Real.exp_pos _)]
    exact le_max_right _ _
  have hxc:Real.exp x≤Z^L:=(Real.logb_le_iff_le_rpow hZ (Real.exp_pos _)).mp (hlogx.trans hlenx)
  have hsc:Xshort/((∏P∈Dshort,P).absNorm:ℝ)≤Z^L:=
    (div_le_self hshort.le hNs).trans hshortcap
  have hh:=hu bΦ Bmask L Mcap loss Z Q degree C hC hgrowth hB s hQ hs Wshort hsW
    j k v t (Real.exp x) (Xshort/((∏P∈Dshort,P).absNorm:ℝ))
    (Real.exp_pos _) (div_pos hshort hpS) hxc hsc
  have hp:=actual_growth_power Z b s.width xi epsilon loss Xshort Xlong _ _ x
    hZ (by linarith) s.width_nonneg he hxi hshort hlong hNs hNl hsupport hdef hlive hx
  have hcoef:0≤C*diagonalControl s.radial.profile*D*(sourceControl T Wshort)^2*(1+|t|)^(2*n):=by
    have hd:=diagonalControl_nonneg s.radial.profile
    positivity
  apply hh.trans
  have hbnd:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hcoef)
    (show 0≤(1+‖v‖)^(2*n) by positivity)
  convert hbnd using 1 ; ring
end SevenEighths.CenteredMomentEnergyZeroGrowthWindow

end

end OAI
