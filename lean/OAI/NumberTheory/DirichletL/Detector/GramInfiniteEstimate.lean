import OAI.NumberTheory.DirichletL.Detector.GramSourceEstimate

namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff Topology
namespace SevenEighths.ProbeGramCommon
open Filter ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma sourceTruncation_tendsto (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (F : Finset SupportedIdeal) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q) (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    Tendsto (fun E : Finset GramFrequency=>sourceTruncation S hS σ F E W hW Y Q hY U v) atTop
      (𝓝 (((Q/Y^3:ℝ):ℂ)*∑C∈F,∑'k : GramFrequency,originalCommonBlock S hS σ C k W hW Y Q hY U v)) := by
  have hs (C : SupportedIdeal) : Summable (fun k : GramFrequency=>originalCommonBlock S hS σ C k W hW Y Q hY U v) :=
    originalCommonBlock_summable S hS σ C W hW Y Q hY hQ U v
  have hh := (summable_sum (s:=F) (fun C hC=>hs C)).hasSum.mul_left ((Q/Y^3:ℝ):ℂ)
  rw [Summable.tsum_finsetSum (fun C hC=>hs C)] at hh
  change Tendsto _ atTop (𝓝 _) at hh
  convert hh using 1
  funext E
  unfold sourceTruncation
  rw [←Finset.mul_sum,Finset.sum_comm]

theorem original_energy_nonzero_bound (δ ε : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (hε : 0<ε) (hε1 : ε<1/6) (a b M₀ : ℝ) (ha : 0<a) (hab : a<b) (hM₀ : 0≤M₀)
    (W : ℝ→ℂ) (hcompact : HasCompactSupport W) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (hWM : ∀x,‖W x‖≤M₀) :
    ∃(J : ℕ)(H₁ H₂ : Finset (ℕ×ℕ))(K₁ K₂ : ℝ),0<K₁ ∧ 0<K₂ ∧
      ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal),fixedBadPrimes⊆S→∀(σ : RayRing)
      (U : SchwartzMap ℝ ℂ)(v Y Q : ℝ)(hY : 0<Y),0<Q→
      ‖gaussEnergy (lowGaussColumns W hcompact Y hY) (fun I=>primaryGenerator I.val)
        (fun I=>(supported_span_primaryGenerator_iff _).mpr I.property)
        (lowGaussColumn (calibrationForSet S hS) W Y σ v) U Q-
        lowGramZeroMode (calibrationForSet S hS) W hcompact Y hY σ v U Q‖≤
        K₁*H₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y)*(Y^2/Q)*
          (Y/((Ideal.absNorm (jointFixedModulus S hS):ℝ)*(Y^2/Q)))^(-1+δ)+
        K₂*H₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Q/Y)*
          (Ideal.absNorm (jointFixedModulus S hS):ℝ)^ε*(Y^2/Q)^(1/6:ℝ) := by
  obtain ⟨J,H₁,H₂,K₁,K₂,hK₁,hK₂,hbound⟩ := original_source_truncation_bound δ ε hδ hδ1 hε hε1 a b M₀ ha hab hM₀ W hcompact hs hW hWM
  refine ⟨J,H₁,H₂,K₁,K₂,hK₁,hK₂,?_⟩
  intro S hS hbad σ U v Y Q hY hQ
  rw [original_energy_common_blocks S hS σ W hcompact Y Q hY hQ U v,add_sub_cancel_left]
  exact le_of_tendsto (sourceTruncation_tendsto S hS σ _ W hcompact Y Q hY hQ U v).norm
    (Eventually.of_forall (fun E=>hbound S hS hbad σ _ E U v Y Q hY hQ))

end SevenEighths.ProbeGramCommon
end

end OAI
