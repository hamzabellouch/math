import OAI.NumberTheory.DirichletL.Moments.FirstAnnularActiveInput
import OAI.NumberTheory.DirichletL.Moments.AmplificationRadicalChoice

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentFirstAnnularInput
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve ConcreteTraceCRT
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplifiedRetainedRadius CenteredMomentAmplificationActiveFactor
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow CenteredMomentGaussNormalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationGlobal
open CenteredMomentSectorLocalization CenteredMomentOriginalChildEnergy
open CenteredMomentFirstScale
open CenteredMomentChildRows CenteredMomentHeckeExpansion
local notation "O"=>ActualEisensteinCubic.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentSecondHeightFamily

theorem eventually_input_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6)
    (hC : 1≤Csec) (hxi : 0≤xi) (hreserve : 0<reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ η : Character,
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ s : Input ι,s.η=η →
          (∀ i,Function.support (s.W i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,s.P i=Z^(z i)) →
          ∀ (R seed : Ideal O),R≠0 → seed≠0 → (R.absNorm:ℝ)≤Z^BR → (seed.absNorm:ℝ)≤Z^Bs →
          ∀ (d cLog : ℝ),∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0<K → 0<X →
          Tsec≤Csec*firstNominalScale I J E K X →
          ∀ (H0 : ℝ),0<H0 → H0≤4*frequencyRadius Tsec Z xi → 8*H0≤Z^Mmax →
          normalizedGaussSource s R seed CenteredMomentFirstAnnularMajorant.profile H0≤
            (56/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                normalizedGaussSource s R seed ballProfile
                  (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z (32*Csec) xi) reserve)+
                ∑p : elementPool P,∑i : Fin 3,
                  (16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*
                    ∑χ:RayCharacter,∑B:actualAllocations (activeInput s).pools
                        ((Ideal.span {p.val})^(errorIndex i+1)),
                      childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
                        R seed B (τ p i χ) s.t ballProfile
                        (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                          (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))) := by
  filter_upwards [CenteredMomentFirstAnnularAmplification.eventually_annular_amplification_common
    (ι:=ι) M H hH Sbad hbad sigma loss BR Bs Mmax b eta Csec xi reserve
    hsigma hloss hM hb hgap hC hxi hreserve,
    eventually_dyadic_amplification.{0} M H hH Sbad hbad sigma loss BR Bs Mmax b eta
      hsigma hloss hM hgap] with Z hz hpz
  obtain ⟨hZ,hP,hcard,hfam⟩:=hz
  obtain ⟨_,_,_,hsep,hdata,_⟩:=hpz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η
  obtain ⟨τ,hN,henergy⟩:=hfam η fixedBadMask fixedBadMask_ne_zero
    (dvd_mul_right _ _) (dvd_mul_left _ _)
  refine ⟨τ,hN,?_⟩
  intro s hsη hsupp z hz hlen R seed hR0 hs0 hR hs d cLog I J E hE K X Tsec hK hX hsec H0 hH0 houter hcap
  have he:=henergy (original s R seed) s.pools_ne s.prime hsupp z hz hlen hR0 hs0 hR hs
    s.t (volume s) d cLog (volume_pos s) I J E hE K X Tsec hK hX hsec H0 hH0 houter hcap
  rw [←hsη,normalized_input_coefficient,normalized_input_coefficient] at he
  convert he using 1
  congr 2
  apply Finset.sum_congr rfl
  intro p _
  have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
    (fun Q hQ=>(hdata Q hQ).2.1) p.val p.property
  have hcop:∀i,∀Q∈(activeInput s).slots i,IsCoprime (Ideal.span {p.val}) Q:=by
    exact original_slot_coprime (original s R seed).active Z sigma b eta hZ.le hb hsep z hz hlen
      hsupp (original s R seed).active_slot
      (fun i Q hQ=>s.prime i Q ((original s R seed).active_subset _ hQ))
      (Ideal.span {p.val}) (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
  apply Finset.sum_congr rfl
  intro i _
  rw [←original_active]
  exact (original_childEnergy_eq_inputs (activeInput s) R seed (τ p i) p.val hd.1.ne_zero hcop
    (errorIndex i) s.t _).symm

end SevenEighths.CenteredMomentFirstAnnularInput

end

end OAI
