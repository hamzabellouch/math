import OAI.NumberTheory.DirichletL.Moments.FirstChildBound
import OAI.NumberTheory.DirichletL.Moments.FirstSectorTransform
import OAI.NumberTheory.DirichletL.Moments.FirstChildProfile

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentFirstSectors CenteredMomentFirstSectorEnergy CenteredMomentFirstSectorTransform
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentActive
open CenteredMomentFirstReduced CenteredMomentFirstFrequency CenteredMomentFirstWholeKernel
open CenteredMomentFirstColumns CenteredMomentFirstAssembly CenteredMomentGaussEnergy
open CenteredMomentSmooth CenteredMomentScale CenteredMomentPrimitive IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

def columns (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O)):Finset (Ideal O):=
  (residualPool D hD (supportedColumns S)).filter (fun I=>IsCoprime C I)

lemma column_supported (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))
    (a:columns C D hD S):Supported (a:Ideal O):=
  residualPool_supported D hD S ⟨a.val,(Finset.mem_filter.mp a.property).1⟩

def element (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):O:=
  CompletedGauss.primaryGenerator a

lemma element_span (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):
    Ideal.span {element C D hD S a}=a:=primary_span_supported a (column_supported C D hD S a)

lemma element_supported (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):
    Supported (Ideal.span {element C D hD S a}):=by
  rw [element_span];exact column_supported C D hD S a

lemma element_primary (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):
    goodLambda^2∣element C D hD S a-1:=
  (CompletedGauss.primaryGenerator_spec a (supported_primaryGenerator_ne_zero a
    (column_supported C D hD S a))).2

lemma active_span_dvd (C D:Ideal O)(hC:C≠0)(hD:D≠0)
    (hCD:primeSupport C=primeSupport D):Ideal.span {activeConductor C D}∣C:=by
  have hh:=activeConductor_span_dvd C D
  rw [(fixed_common_parts C D hC hD hCD).1] at hh
  exact hh

lemma element_coprime_active (C D B:Ideal O)(hC:C≠0)(hD:D≠0)(hB:B≠0)
    (hCD:primeSupport C=primeSupport D)(S:Finset (Ideal O))(a:columns C B hB S):
    IsCoprime (element C B hB S a) (activeConductor C D):=by
  rw [←Ideal.isCoprime_span_singleton_iff,element_span]
  exact (Finset.mem_filter.mp a.property).2.symm.of_isCoprime_of_dvd_right (active_span_dvd C D hC hD hCD)

def coefficient (η:Character)(m A:O)(t:ℝ)(c:Ideal O→ℂ)(D:Ideal O)
    (I:Ideal O):ℂ:=c (D*I)*CenteredMomentHeckeExpansion.rowWeight η m A 1 t I

def inactiveWeight (C D:Ideal O)(E:Finset (CommonIndex C D)):ℂ:=
  (UniqueFactorizationMonoid.moebius (∏P∈E,P.val):ℂ)

def block (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀:ℝ):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let k:=K/‖eisEmbedding e‖^2
  let r:=activeConductor C D
  inactiveWeight C D E * ∑h∈rows,
    ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      let na:=element C C hC.1 S a
      let nb:=element C D hD.1 S b
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (tripleRow na nb r (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) e *
        ((k/‖eisEmbedding (na*(nb*r))‖^2:ℝ):ℂ)*
        tripleFourier na nb r
          (supported_element_ne_zero _ (element_supported C C hC.1 S a))
          (supported_element_ne_zero _ (element_supported C D hD.1 S b))
          (finitePrimeModulus_ne_zero _) (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) h)*
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
        windows V (k/‖eisEmbedding r‖^2) (‖eisEmbedding h‖^2)
          (‖eisEmbedding na‖^2) (‖eisEmbedding nb‖^2) K₀ H₀ A₀ B₀*
        EisensteinSchwartzPoisson.paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (na*(nb*r))‖^2)
      else 0

def scalar (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))(K A₀ B₀:ℝ):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let k:=K/‖eisEmbedding e‖^2
  inactiveWeight C D E * ((k:ℂ)*canonicalNormalizedGauss (activePrime C D)
    (activeCoprime C D) (activeGood C D hC) (activeExponent C D)/
      ((‖eisEmbedding (activeConductor C D)‖:ℂ)*(Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))

theorem block_eq_whole (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(rows:Finset O)(hrows:∀h∈rows,h≠0)
    (W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀:ℝ)
    (hK:0<K)(hK₀:0<K₀)(hH₀:0<H₀)(hA₀:0<A₀)(hB₀:0<B₀):
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
    let k:=K/‖eisEmbedding e‖^2
    let r:=activeConductor C D
    let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    block η m A t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀=
      scalar C D hC E K A₀ B₀ * ∑h∈rows,star (ρ h)*
        ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
          ((if IsCoprime (element C C hC.1 S a) (element C D hD.1 S b) then
            originalPhase e r ρ (element C C hC.1 S a) (element C D hD.1 S b) else 0)*
            (coefficient η m A t c C a*star (coefficient η m A t c D b)))*
          (gaussRow _ (element_supported C C hC.1 S a) h*
            star (gaussRow _ (element_supported C D hD.1 S b) (-h)))*
          wholeKernel W V (K₀*H₀/(A₀*B₀))
            (Real.log ((k/‖eisEmbedding r‖^2)/K₀)) (Real.log (‖eisEmbedding h‖^2/H₀))
            (Real.log (‖eisEmbedding (element C C hC.1 S a)‖^2/A₀))
            (Real.log (‖eisEmbedding (element C D hD.1 S b)‖^2/B₀)):=by
  dsimp only
  have he:primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E≠0:=
    supported_element_ne_zero _ (subsetGenerator_supported C D hC E)
  have hk:0<K/‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2:=
    div_pos hK (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero he)))
  unfold block scalar
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hcop:IsCoprime (element C C hC.1 S a) (element C D hD.1 S b)↔
      IsCoprime (a:Ideal O) (b:Ideal O):=by
    rw [←Ideal.isCoprime_span_singleton_iff,element_span,element_span]
  by_cases hab:IsCoprime (a:Ideal O) (b:Ideal O)
  · simp only [hab,ite_true,hcop]
    have hh:=dilated_frequency_whole_kernel (activePrime C D) (activeCoprime C D)
      (activeGood C D hC) (fun P=>common_odd C D hC P.val) (activeExponent C D)
      (netExponent_ne_zero _ _ _) (fun P=>netExponent_lt_six _ _)
      (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
      (element C C hC.1 S a) (element C D hD.1 S b)
      (element_supported C C hC.1 S a) (element_supported C D hD.1 S b)
      ((hcop.mpr hab).mul_right (element_coprime_active C D C hC.1 hD.1 hC.1 hCD S a))
      (element_coprime_active C D D hC.1 hD.1 hD.1 hCD S b)
      _ hk h (hrows h hh) W V K₀ H₀ A₀ B₀ hK₀ hH₀ hA₀ hB₀
    dsimp only at hh
    change inactiveWeight C D E * (_*_*_*_)=_
    calc
      _=inactiveWeight C D E*(coefficient η m A t c C a*star (coefficient η m A t c D b))*
        (dilatedFrequency (activePrime C D) (activeCoprime C D) (activeGood C D hC)
          (activeExponent C D) (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
          (element C C hC.1 S a) (element C D hD.1 S b)
          (element_supported C C hC.1 S a) (element_supported C D hD.1 S b)
          (K/‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2) h *
        windows V _ _ _ _ K₀ H₀ A₀ B₀ * EisensteinSchwartzPoisson.paperRadialFourier W _):=by
          dsimp [dilatedFrequency,activeFunction,activeConductor];ring
      _=_:=by rw [hh];dsimp only [activeConductor];ring
  · simp [hab,hcop]

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
