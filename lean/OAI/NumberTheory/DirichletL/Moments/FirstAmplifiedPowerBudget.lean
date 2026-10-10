import OAI.NumberTheory.DirichletL.Moments.FirstAnnularActiveInput
import OAI.NumberTheory.DirichletL.Moments.AmplificationRadicalChoice
import OAI.NumberTheory.DirichletL.Moments.FirstErrorAllocationPower
import OAI.NumberTheory.DirichletL.Moments.FirstAnnularInputAmplification

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentFirstAmplifiedPowerBudget
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

open CenteredMomentFirstAnnularInput CenteredMomentFirstErrorAllocationPower
theorem eventually_input_power_amplification {ι : Type*} [Fintype ι]
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
          ∀ (amain:Fin 4→ℝ) (aerror:elementPool P→Fin 3→RayCharacter→Fin 4→ℝ)
            (α:Fin 4→ℝ), (∀p i χ j,0≤aerror p i χ j)→
          (normalizedGaussSource s R seed ballProfile
            (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
              (frequencyLoss Z (32*Csec) xi) reserve)≤
                (∑j,amain j*(volume s)^(α j))*CenteredMomentFirstChildProfileControl.mass s^2)→
          (∀p:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
            ∀B:actualAllocations (activeInput s).pools ((Ideal.span {p.val})^(errorIndex i+1)),
              childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
                R seed B (τ p i χ) s.t ballProfile
                (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                  (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))≤
                (∑j,aerror p i χ j*(volume (child (activeInput s)
                  ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ p i χ) s.t))^(α j))*
                  CenteredMomentFirstChildProfileControl.mass (child (activeInput s)
                    ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ p i χ) s.t)^2)→
          normalizedGaussSource s R seed CenteredMomentFirstAnnularMajorant.profile H0≤
            (56/(P.card:ℝ))*CenteredMomentFirstChildProfileControl.mass s^2*
              (((Mmax+2*sigma)/(sigma/6))*(∑j,amain j*(volume s)^(α j))+
                ∑p:elementPool P,∑i:Fin 3,
                  (16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*(errorIndex i+2:ℝ)*
                    ∑χ:RayCharacter,∑j,aerror p i χ j*
                      (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j)) := by
  filter_upwards [eventually_input_amplification (ι:=ι) M H hH Sbad hbad
    sigma loss BR Bs Mmax b eta Csec xi reserve hsigma hloss hM hb hgap hC hxi hreserve,
    eventually_dyadic_amplification.{0} M H hH Sbad hbad sigma loss BR Bs Mmax b eta
      hsigma hloss hM hgap] with Z hz hpz
  obtain ⟨hZ,hP,hcard,hfam⟩:=hz
  obtain ⟨_,_,_,hsep,hdata,_⟩:=hpz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η
  obtain ⟨τ,hN,henergy⟩:=hfam η
  refine ⟨τ,hN,?_⟩
  intro s hsη hsupp z hz hlen R seed hR0 hs0 hR hs d cLog I J E hE K X Tsec hK hX hsec
    H0 hH0 houter hcap amain aerror α haerr hmain herr
  have he:=henergy s hsη hsupp z hz hlen R seed hR0 hs0 hR hs d cLog I J E hE K X Tsec
    hK hX hsec H0 hH0 houter hcap
  apply he.trans
  have hpweight:0≤56/((primePool M H Sbad (1/2) 1 (Z^(sigma/3))).card:ℝ):=by positivity
  have hmweight:0≤(Mmax+2*sigma)/(sigma/6):=by positivity
  have herror: ∀p:elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))),∀i:Fin 3,
      (∑χ:RayCharacter,∑B:actualAllocations (activeInput s).pools ((Ideal.span {p.val})^(errorIndex i+1)),
        childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
          R seed B (τ p i χ) s.t ballProfile
          (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
            (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1)))≤
      (errorIndex i+2:ℝ)*(∑χ:RayCharacter,∑j,aerror p i χ j*
        (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j))*
          CenteredMomentFirstChildProfileControl.mass s^2:=by
    intro p i
    have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
      (fun Q hQ=>(hdata Q hQ).2.1) p.val p.property
    have hcop:∀j,∀Q∈(activeInput s).slots j,IsCoprime (Ideal.span {p.val}) Q:=by
      exact original_slot_coprime (original s R seed).active Z sigma b eta hZ.le hb hsep z hz hlen
        hsupp (original s R seed).active_slot
        (fun j Q hQ=>s.prime j Q ((original s R seed).active_subset _ hQ))
        (Ideal.span {p.val}) (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
    have hq:Prime (Ideal.span {p.val}):=(hdata _ hd.2.1).1
    calc
      _≤∑χ:RayCharacter,((errorIndex i+1+1:ℕ):ℝ)*
          (∑j,aerror p i χ j*(volume (activeInput s)/
            ((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j))*
              CenteredMomentFirstChildProfileControl.mass (activeInput s)^2:=by
        apply Finset.sum_le_sum
        intro χ hχ
        apply le_trans (Finset.sum_le_sum (fun B _=>herr p i χ B))
        exact budget_sum_le (activeInput s) (Ideal.span {p.val}) hq (errorIndex i+1) hcop R
          (fun _=>τ p i χ) (fun _=>s.t) 4 (aerror p i χ) α (haerr p i χ)
      _=_:=by
        simp only [CenteredMomentFirstChildProfileControl.mass,activeInput]
        push_cast
        rw [←Finset.sum_mul,←Finset.mul_sum]
        congr 2
        ring
  calc
    _≤(56/((primePool M H Sbad (1/2) 1 (Z^(sigma/3))).card:ℝ))*
        (((Mmax+2*sigma)/(sigma/6))*
          ((∑j,amain j*(volume s)^(α j))*CenteredMomentFirstChildProfileControl.mass s^2)+
          ∑p:elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))),∑i:Fin 3,(16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*
            ((errorIndex i+2:ℝ)*(∑χ:RayCharacter,∑j,aerror p i χ j*
              (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j))*
                CenteredMomentFirstChildProfileControl.mass s^2)):=by
      apply mul_le_mul_of_nonneg_left _ hpweight
      apply add_le_add (mul_le_mul_of_nonneg_left hmain hmweight)
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (herror p i)
        (mul_nonneg (by positivity) (localErrorCost_nonneg p (errorIndex i)))
    _=_:=by
      simp only [←mul_assoc,←Finset.sum_mul]
      ring

theorem eventually_original_subsets_power_amplification {Ω : Type*} [Fintype Ω]
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
      ∃ τ : (A:Finset Ω) → (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (A:Finset Ω) (p : elementPool P) i χ,(τ A p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ A:Finset Ω,∀ s : Input A,s.η=η →
          (∀ i,Function.support (s.W i)⊆Set.Iic b) →
          ∀ (z : A→ℝ),(∀i,z i≤eta) → (∀i,s.P i=Z^(z i)) →
          ∀ (R seed : Ideal O),R≠0 → seed≠0 → (R.absNorm:ℝ)≤Z^BR → (seed.absNorm:ℝ)≤Z^Bs →
          ∀ (d cLog : ℝ),∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0<K → 0<X →
          Tsec≤Csec*firstNominalScale I J E K X →
          ∀ (H0 : ℝ),0<H0 → H0≤4*frequencyRadius Tsec Z xi → 8*H0≤Z^Mmax →
          ∀ (amain:Fin 4→ℝ) (aerror:elementPool P→Fin 3→RayCharacter→Fin 4→ℝ)
            (α:Fin 4→ℝ), (∀p i χ j,0≤aerror p i χ j)→
          (normalizedGaussSource s R seed ballProfile
            (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
              (frequencyLoss Z (32*Csec) xi) reserve)≤
                (∑j,amain j*(volume s)^(α j))*CenteredMomentFirstChildProfileControl.mass s^2)→
          (∀p:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
            ∀B:actualAllocations (activeInput s).pools ((Ideal.span {p.val})^(errorIndex i+1)),
              childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
                R seed B (τ A p i χ) s.t ballProfile
                (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                  (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))≤
                (∑j,aerror p i χ j*(volume (child (activeInput s)
                  ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ A p i χ) s.t))^(α j))*
                  CenteredMomentFirstChildProfileControl.mass (child (activeInput s)
                    ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ A p i χ) s.t)^2)→
          normalizedGaussSource s R seed CenteredMomentFirstAnnularMajorant.profile H0≤
            (56/(P.card:ℝ))*CenteredMomentFirstChildProfileControl.mass s^2*
              (((Mmax+2*sigma)/(sigma/6))*(∑j,amain j*(volume s)^(α j))+
                ∑p:elementPool P,∑i:Fin 3,
                  (16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*(errorIndex i+2:ℝ)*
                    ∑χ:RayCharacter,∑j,aerror p i χ j*
                      (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j)) := by
  have hall:=Filter.eventually_all.mpr (fun A:Finset Ω=>
    eventually_input_power_amplification (ι:=A) M H hH Sbad hbad sigma loss BR Bs Mmax b eta Csec xi reserve
      hsigma hloss hM hb hgap hC hxi hreserve)
  filter_upwards [hall] with Z hz
  have hbase:=hz (∅:Finset Ω)
  refine ⟨hbase.1,hbase.2.1,hbase.2.2.1,?_⟩
  intro η
  have hf (A:Finset Ω):=(hz A).2.2.2 η
  choose τ hN he using hf
  exact ⟨τ,hN,he⟩

end SevenEighths.CenteredMomentFirstAmplifiedPowerBudget

end

end OAI
