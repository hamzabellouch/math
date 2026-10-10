import Mathlib
import OAI.Probability.SKRatio.Gaussian.PlantedEmpirical
import OAI.Probability.SKRatio.Quantization.QuantizerExistence
import OAI.Probability.SKRatio.Quantization.BinPullback
import OAI.Probability.SKRatio.Quantization.CompactTolerance

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression

lemma l2Norm_field (β : ℝ) : l2Norm (fieldLaw β) id=sqrt (β^2+β^4) := by
  unfold l2Norm
  exact congrArg sqrt (fieldLaw_secondMoment β)

lemma quantizer_l2Norm_le {β R : ℝ} (hR : 0<R) {N : ℕ} (hN : 0<N)
    {a : ℝ} (ha : 0≤a) (herr : (∫ x, (x-gridQuant R N x)^2 ∂fieldLaw β)≤a^2) :
    l2Norm (fieldLaw β) (gridQuant R N)≤ sqrt (β^2+β^4)+a := by
  have hs := measurable_intervalBin (Nat.succ_pos N) (gridCut_strictMono hR hN)
  have hH := memLp_finite_comp (μ := fieldLaw β) hs (gridRep R N)
  have he : l2Norm (fieldLaw β) (fun x => gridQuant R N x-x)≤a := by
    unfold l2Norm
    apply (sqrt_le_iff).mpr ⟨ha,?_⟩
    simpa only [sub_sq_comm] using herr
  have ht := l2Norm_add (memLp_field β) (hH.sub (memLp_field β))
  change l2Norm (fieldLaw β) (fun x => x+(gridQuant R N x-x))≤
    l2Norm (fieldLaw β) id+l2Norm (fieldLaw β) (fun x => gridQuant R N x-x) at ht
  have heq : (fun x => x+(gridQuant R N x-x))=gridQuant R N := by ext x; ring
  rw [heq] at ht
  rw [l2Norm_field] at ht
  linarith only [ht,he]

lemma finiteV_le_of_quantizer {β C a : ℝ} (hβ : 0≤β) (ha : 0≤a)
    (hscalar : ∀ b r : ℝ → ℝ, MemLp b 2 (fieldLaw β) → MemLp r 2 (fieldLaw β) →
      (∫ x, b x^2+r x^2 ∂fieldLaw β)=1 → variational β b r≤C)
    {R : ℝ} (hR : 0<R) {N : ℕ} (hN : 0<N) (hβne : β≠0)
    (herr : (∫ x, (x-gridQuant R N x)^2 ∂fieldLaw β)≤a^2)
    {T : ℝ} (hT : 0≤T) (hsize : sqrt (β^2+β^4)+a≤T)
    (hv : ∀ x, |v x-v (gridQuant R N x)|≤a)
    (hmv : ∀ x, |m x*v x-m (gridQuant R N x)*v (gridQuant R N x)|≤a)
    (hf : ∀ x y, |v y^2/(w x+w y)-v (gridQuant R N y)^2/
      (w (gridQuant R N x)+w (gridQuant R N y))|≤a)
    (hk : ∀ x y, |kernel x y-kernel (gridQuant R N x) (gridQuant R N y)|≤a)
    (z : Parameters (Fin (N+2))) :
    finiteV β (massRoot (fieldLaw β) (intervalBin (gridCut R N))) (gridRep R N) z ≤
      C+(2*a+2*T*a+5*β^2*a+4*β*sqrt a) := by
  let σ := intervalBin (gridCut R N)
  have hs : Measurable σ := measurable_intervalBin (Nat.succ_pos N) (gridCut_strictMono hR hN)
  have hm : ∀ d, 0<binMass (fieldLaw β) σ d :=
    intervalBin_mass_pos (Nat.succ_pos N) (gridCut_strictMono hR hN) β hβne
  let b := pullback (fieldLaw β) σ (paramB z)
  let r := pullback (fieldLaw β) σ (paramR z)
  have hb : MemLp b 2 (fieldLaw β) := memLp_pullback hs _
  have hr : MemLp r 2 (fieldLaw β) := memLp_pullback hs _
  have he := pullback_normalized (μ := fieldLaw β) hs hm z
  have hH : MemLp (gridQuant R N) 2 (fieldLaw β) := memLp_finite_comp hs (gridRep R N)
  have herr' : l2Norm (fieldLaw β) (fun x => x-gridQuant R N x)≤a :=
    (sqrt_le_iff).mpr ⟨ha,herr⟩
  have hbnd := fieldForm_error (μ := fieldLaw β) β hβ hb hr
    (measurable_pullback hs _) (measurable_pullback hs _) measurable_id
    (measurable_gridQuant hR hN) (memLp_field β) hH he ha hT herr'
    ((quantizer_l2Norm_le hR hN ha herr).trans hsize) hv hmv hf hk
  have hp := fieldForm_pullback (μ := fieldLaw β) hs hm β (gridRep R N) z
  change fieldForm (fieldLaw β) β (gridQuant R N) b r = _ at hp
  rw [fieldForm_id,hp] at hbnd
  have hu := hscalar b r hb hr he
  have hle := neg_le_abs (variational β b r-finiteV β (massRoot (fieldLaw β) σ) (gridRep R N) z)
  change finiteV β (massRoot (fieldLaw β) σ) (gridRep R N) z≤_
  linarith only [hle,hbnd,hu]

theorem scalar_quantizer_exists
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {ρ : ∀ n, Measure (Ω n)} {X : ∀ n, Ω n → Fin n → ℝ}
    (hX : ExponentialSquareTails ρ X)
    {β K C e : ℝ} (hβ : 0<β) (hK : 0≤K) (he : 0<e)
    (hscalar : ∀ b r : ℝ → ℝ, MemLp b 2 (fieldLaw β) → MemLp r 2 (fieldLaw β) →
      (∫ x, b x^2+r x^2 ∂fieldLaw β)=1 → variational β b r≤C) :
    ∃ a R : ℝ, ∃ N : ℕ, 0<a ∧ a<1 ∧ 0<R ∧ 0<N ∧
      (2*a+2*(sqrt (β^2+β^4)+2)*a+5*β^2*a+K*a+4*β*sqrt a<e) ∧
      (∀ x, |v x-v (gridQuant R N x)|≤a) ∧
      (∀ x, |m x*v x-m (gridQuant R N x)*v (gridQuant R N x)|≤a) ∧
      (∀ x y, |v y^2/(w x+w y)-v (gridQuant R N y)^2/
        (w (gridQuant R N x)+w (gridQuant R N y))|≤a) ∧
      (∀ x y, |kernel x y-kernel (gridQuant R N x) (gridQuant R N y)|≤a) ∧
      (∀ z, finiteV β (massRoot (fieldLaw β) (intervalBin (gridCut R N))) (gridRep R N) z<C+e) ∧
      ExponentiallyRare ρ (fun n => {ω | a≤ siteNorm (fun i => X n ω i-gridQuant R N (X n ω i))}) := by
  let T := sqrt (β^2+β^4)+2
  have hT : 0≤T := by dsimp [T]; positivity
  obtain ⟨a,ha,ha1,hea⟩ := field_error_tolerance β (T+K/2) he
  have htotal : 2*a+2*T*a+5*β^2*a+K*a+4*β*sqrt a<e := by linarith only [hea]
  obtain ⟨δ,hδ,ht⟩ := compact_coefficients_tolerance ha
  obtain ⟨R,N,hR,hN,hcomp,hl2,hemp⟩ := quantizer_exists hX (μ := fieldLaw β)
    (memLp_field β).integrable_sq hδ ha
  obtain ⟨hv,hmv,hf,hk⟩ := ht (gridQuant R N) hcomp
  refine ⟨a,R,N,ha,ha1,hR,hN,htotal,hv,hmv,hf,hk,?_,hemp⟩
  intro z
  have hp := finiteV_le_of_quantizer hβ.le ha.le hscalar hR hN hβ.ne'
    hl2.le hT (by dsimp [T]; linarith only [ha1]) hv hmv hf hk z
  have hKa := mul_nonneg hK ha.le
  exact hp.trans_lt (by linarith only [htotal,hKa])

end SKRatio.Bins

end

end OAI
