import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedEnergy
import OAI.NumberTheory.DirichletL.Moments.SecondDivisorSupport
import OAI.NumberTheory.DirichletL.Moments.MobiusHarmonicMass
import OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput
import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstDivisorSupport
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentGaussEnergy
open CenteredMomentSecondDivisorSupport CenteredMomentChildAssembly
open CenteredMomentHeckeColumnWindow
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport RayFourExpansion
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

lemma common_coefficient_zero (s : OriginalData ι) (D : Ideal O) (hD : Supported D)
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)<L.absNorm)
    (τ : Character) (t : ℝ) (I : supportedColumns (residualPool D hD.1 s.columns)) :
    (if IsCoprime D (I:Ideal O) ∧ L∣(I:Ideal O) then s.beta (D*I) else 0)*heightCoeff τ t I=0 := by
  split_ifs with hi
  · have hz : s.beta (D*I)=0 := by
      by_contra hn
      exact (not_le_of_gt hL) (live_right_divisor_norm D I L hD.1
        (Finset.mem_filter.mp I.property).2.1 s.beta H hβ hn hi.2)
    rw [hz,zero_mul]
  · rw [zero_mul]

theorem commonEnergy_zero (s : OriginalData ι) (D : Ideal O) (hD : Supported D)
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)<L.absNorm)
    (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    commonEnergy s D hD τ t L W K=0 := by
  unfold commonEnergy gaussEnergy gaussPolynomial
  simp only [common_coefficient_zero s D hD H hβ L hL τ t,zero_mul,
    Finset.sum_const_zero,norm_zero,zero_pow (by decide : 2≠0),Complex.ofReal_zero,tsum_zero]

lemma right_coefficient_zero (s : OriginalData ι) (C D : Ideal O) (hD : Supported D)
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)<L.absNorm)
    (η : Character) (m : O) (t : ℝ) (χ : RayCharacter)
    (a : columns C D hD.1 s.columns→ℂ) (I : columns C D hD.1 s.columns) :
    divisorCoefficient L (element C D hD.1 s.columns)
      (fun I=>coefficient η m 1 t s.beta D I*a I) χ I=0 := by
  unfold divisorCoefficient
  rw [element_span]
  split_ifs with hd
  · have hz : s.beta (D*I)=0 := by
      by_contra hn
      exact (not_le_of_gt hL) (live_right_divisor_norm D I L hD.1
        (column_supported C D hD.1 s.columns I).1 s.beta H hβ hn hd)
    simp only [coefficient,hz,zero_mul]
  · rfl

theorem rightWindowChild_zero (s : OriginalData ι) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)<L.absNorm)
    (η : Character) (m : O) (t : ℝ) (χ : RayCharacter)
    (θ X : ℝ) (V : ℝ→ℂ) (z : O) :
    rightWindowChild s η m t C D hC hD E χ L θ X V z=0 := by
  unfold rightWindowChild gaussPolynomial
  dsimp only
  simp only [right_coefficient_zero s C D hD H hβ L hL η m t χ,
    zero_mul,Finset.sum_const_zero]

theorem signed_right_window_filter (s : OriginalData ι) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (η : Character) (m : O) (t : ℝ) (χ : RayCharacter)
    (θ X : ℝ) (V : ℝ→ℂ) (Ds : Finset (Ideal O)) (rows : Finset O)
    (F : Ideal O→O→ℂ) :
    (∑L∈Ds,∑z∈rows,F L z*star (rightWindowChild s η m t C D hC hD E χ L θ X V (-z)))=
      ∑L∈Ds.filter (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)),
        ∑z∈rows,F L z*star (rightWindowChild s η m t C D hC hD E χ L θ X V (-z)) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro L hLD
  by_cases hl : (L.absNorm:ℝ)≤H/(D.absNorm:ℝ)
  · rw [ite_eq_left hl]
  · rw [ite_eq_right hl]
    simp only [rightWindowChild_zero s C D hC hD E H hβ L (lt_of_not_ge hl),star_zero,
      mul_zero,Finset.sum_const_zero]

theorem supported_harmonic_mass (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(Ds : Finset (Ideal O))(D : Ideal O)(H : ℝ),H/(D.absNorm:ℝ)≤Z^B →
      (∑L∈Ds.filter (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)),
        ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖/(L.absNorm:ℝ))≤C*Z^δ := by
  obtain ⟨C,hC,hbound⟩:=CenteredMomentMobiusHarmonicMass.full_mass_subpower B δ hB hδ
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro Ds D H hcap
  exact hz.2 _ (fun L hL _=>(Finset.mem_filter.mp hL).2.trans hcap)

open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput

theorem input_commonEnergy_zero (s : Input ι) (R seed D : Ideal O) (hD : Supported D)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (L : Ideal O)
    (hL : CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)<L.absNorm)
    (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    commonEnergy (original s R seed) D hD τ t L W K=0 :=
  commonEnergy_zero (original s R seed) D hD _
    (fun I hi=>(CenteredMomentOriginalCommonHarmonic.original_column_norm s R seed I hz₁ hz₂ hi).2)
    L hL τ t W K

theorem input_rightWindowChild_zero (s : Input ι) (R seed C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (L : Ideal O)
    (hL : CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)<L.absNorm)
    (η : Character) (m : O) (t : ℝ) (χ : RayCharacter)
    (θ X : ℝ) (V : ℝ→ℂ) (z : O) :
    rightWindowChild (original s R seed) η m t C D hC hD E χ L θ X V z=0 :=
  rightWindowChild_zero (original s R seed) C D hC hD E _
    (fun I hi=>(CenteredMomentOriginalCommonHarmonic.original_column_norm s R seed I hz₁ hz₂ hi).2)
    L hL η m t χ θ X V z

end SevenEighths.CenteredMomentFirstDivisorSupport

end

end OAI
