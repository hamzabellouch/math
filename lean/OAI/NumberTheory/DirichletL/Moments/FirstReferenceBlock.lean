import OAI.NumberTheory.DirichletL.Moments.FirstDivisorCommonBound
import OAI.NumberTheory.DirichletL.Moments.FirstMixedWindow

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstReferenceBlock
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentGaussEnergy
open CenteredMomentFirstDivisorSupport CenteredMomentChildAssembly
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport RayFourExpansion
open CenteredMomentHeckeColumnWindow CenteredMomentSecondWindowBudget
open CenteredMomentSectorLocalization CenteredMomentLogDyadic CenteredMomentMobiusRegroup
open CenteredMomentSecondHeightFamily CenteredMomentFirstPhysicalAnnularCommonBound
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstMixedAllowance
open CenteredMomentFirstMixedWindow CenteredMomentFirstWindowBudgets
open CenteredMomentFirstCanonicalFamily CenteredMomentRankinRadical
local notation "O"=>HeckeFamily.O

theorem actual_reference_block (W:𝓢(ℝ,ℂ)) (decay J₁ J₂:ℕ)
    (B δ:ℝ)(hB:0≤B)(hδ:0<δ):
    ∃Cb:ℝ,0<Cb ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀{ι:Type*}[Fintype ι][DecidableEq ι],∀s:Input ι,∀R seed:Ideal O,
    ∀a₁ a₂:ℝ,0<a₁→0<a₂→
    (∀x,s.W₁ x≠0→a₁≤x)→(∀x,s.W₂ x≠0→a₂≤x)→
    ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀E:Finset (CommonIndex C D),∀ξ₁ ξ₂:RayCharacter,
    ∀F:FixedPair s.η C D hC E ξ₁ ξ₂,∀rows:Finset O,∀K:ℝ,0<K→∀n:Fin 4→ℤ,
    sourceRadius s/(D.absNorm:ℝ)≤Z^B→∀EL ER:Fin 4→ℝ,(∀i,0≤EL i)→(∀i,0≤ER i)→
    let V:=volume s;
    let refL:=(F.left.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z);
    let refR:=(F.right.modulus.absNorm:ℝ)*(V/(D.absNorm:ℝ))^2*Z^(allowance D C Z);
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 (original s R seed).columns))
      (fun b=>Ideal.span {element C D hD.1 (original s R seed).columns b}),
      (L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ)→Squarefree L→∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy (original s R seed) C hC (fixedPair s.η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
        ((∑i,refL*EL i)/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₁))→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 (original s R seed).columns))
      (fun b=>Ideal.span {element C D hD.1 (original s R seed).columns b}),
      (L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ)→Squarefree L→∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy (original s R seed) D hD (fixedPair s.η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
        ((∑i,refR*ER i)/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₂))→
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay*
      ‖block s.η (fixedBadMask*idealGenerator R) 1 s.t (original s R seed).columns
        (original s R seed).beta C D hC hD E rows W (fun _=>logAnnulus)
        K (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))‖/V≤
      Cb*Z^δ*(‖inactiveWeight C D E‖*(Real.exp (Real.log 4)/((∏i,s.lo i)*a₁*a₂))*
        fixedPresentationCost*K*(s.η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm)*
      (∑i:Fin 4,∑j:Fin 4,windowBudget J₁ s.t (EL i)*windowBudget J₂ s.t (ER j)):=by
  obtain ⟨Cb,hCb,hev⟩:=CenteredMomentFirstDivisorCommonBound.actual_supported_annular_harmonic
    W decay J₁ J₂ B δ hB hδ
  refine ⟨Cb,hCb,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ _ s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂ C D hC hD hCD E ξ₁ ξ₂ F rows K hK n hcap EL ER hEL hER
    V refL refR hleft hright
  have hz:0≤Z:=zero_le_one.trans hZ.1.le
  have hcb:0≤Cb:=hCb.le
  have hf:0≤fixedPresentationCost:=fixedPresentationCost_pos.le
  have hprodlo:0≤∏i,s.lo i:=Finset.prod_nonneg (fun i _=>(s.lo_pos i).le)
  have hV:0<V:=volume_pos s
  have hRL:0≤refL:=by dsimp [refL]; positivity
  have hRR:0≤refR:=by dsimp [refR]; positivity
  have hLE:∀i:Fin 4,0≤refL*EL i:=fun i=>mul_nonneg hRL (hEL i)
  have hRE:∀i:Fin 4,0≤refR*ER i:=fun i=>mul_nonneg hRR (hER i)
  have hz₁:s.W₁ 0=0:=by by_contra hn;have hh:=hs₁ 0 hn;linarith
  have hz₂:s.W₂ 0=0:=by by_contra hn;have hh:=hs₂ 0 hn;linarith
  have hb:=hZ.2 s.η (original s R seed) s.t C D hC hD hCD E rows K hK n
    (sourceRadius s) (fun I hI=>(original_column_norm s R seed I hz₁ hz₂ hI).2)
    hcap (∑i,refL*EL i) (∑i,refR*ER i)
    (Finset.sum_nonneg (fun i _=>hLE i)) (Finset.sum_nonneg (fun i _=>hRE i)) hleft hright
  have hw:=windowBudget_pair_sum Finset.univ Finset.univ (fun i=>refL*EL i) (fun i=>refR*ER i)
    (fun i _=>hLE i) (fun i _=>hRE i) J₁ J₂ s.t
  have hb':=hb.trans (mul_le_mul_of_nonneg_left hw (by positivity))
  by_cases hn:block s.η (fixedBadMask*idealGenerator R) 1 s.t (original s R seed).columns
      (original s R seed).beta C D hC hD E rows W (fun _=>logAnnulus)
      K (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))=0
  · simp only [hn,norm_zero,mul_zero,zero_div]
    have he:0≤∑i:Fin 4,∑j:Fin 4,windowBudget J₁ s.t (EL i)*windowBudget J₂ s.t (ER j):=
      Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun j _=>mul_nonneg
        (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _)))
    positivity
  · have href:=original_four_budget_reference s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂
      (fixedBadMask*idealGenerator R) 1 s.t (original s R seed).columns C D hC hD hCD E
      ξ₁ ξ₂ F rows W (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
      (dyadicScale (n 2)) (dyadicScale (n 3)) (Real.log 4) Z EL ER J₁ J₂ s.t hK
      (dyadicScale_pos _) (dyadicScale_pos _) hZ.1 hEL hER
      (fun _ x hx=>by
        have hh:=logAnnulus_support hx
        exact abs_le.mpr ⟨hh.1,hh.2.trans (Real.log_nonneg (by norm_num))⟩) hn
    have hh:=div_le_div_of_nonneg_right hb' hV.le
    have hscale:0≤Cb*Z^δ:=by positivity
    have hmul:=mul_le_mul_of_nonneg_left href hscale
    calc
      _ ≤ _ := hh
      _ = Cb*Z^δ*(‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖/V*
          (∑i:Fin 4,∑j:Fin 4,windowBudget J₁ s.t (refL*EL i)*windowBudget J₂ s.t (refR*ER j))) := by ring
      _ ≤ _ := by convert hmul using 1 <;> (try dsimp [refL,refR,V,volume,CenteredMomentExceptionalAmplitudePair.volume]) ; ring

end SevenEighths.CenteredMomentFirstReferenceBlock

end

end OAI
