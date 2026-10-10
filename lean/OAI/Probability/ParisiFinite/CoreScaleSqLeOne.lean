import Mathlib
import OAI.Probability.ParisiFinite.SelectedBlock

namespace OAI

/-! Core Scale Sq Le One. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Filter ContinuousLinearMap
open ContinuousLinearMap
open scoped InnerProductSpace BigOperators Topology
open ContinuousLinearMap InnerProductSpace
open ContinuousLinearMap Filter
open Filter MeasureTheory
open scoped Topology ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology RealInnerProductSpace
open scoped BigOperators TensorProduct
open scoped Topology InnerProductSpace
open MeasureTheory Filter
open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
open scoped BigOperators Topology NNReal
open scoped BigOperators NNReal Topology
open scoped BigOperators NNReal
open scoped NNReal Topology
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

lemma coreScale_sq_le_one (n : ℕ) : coreScale n^2 ≤ 1 := by
  rw [coreScale_sq]
  apply (div_le_one (by positivity : (0:ℝ)<n+1)).mpr
  linarith

lemma coreFluctuation_window_bound {N m : ℕ} (hN : 0<N) (β : ℝ) (j : Fin N) :
    coreFluctuationBound (N+j) m β (eighthRootScale N^3) ≤
      (|β|+3*(m+1:ℕ))*eighthRootScale N^4 := by
  let r := eighthRootScale N
  let L : ℝ := (m+1:ℕ)
  have hr : 1 ≤ r := one_le_eighthRootScale hN
  have hr0 : 0 ≤ r := by linarith
  have hL : 1 ≤ L := by dsimp [L]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  have hn : (N+j.val:ℕ) ≤ (2:ℝ)*N := by exact_mod_cast (show N+j.val ≤ 2*N by omega)
  have hN' : (N:ℝ)=r^8 := (eighthRootScale_pow_eight N).symm
  have hc : (β*coreScale (N+j))^2 ≤ β^2 := by
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_left (coreScale_sq_le_one _) (sq_nonneg β)).trans_eq (mul_one _)
  have hbn : (β*coreScale (N+j))^2*(N+j.val:ℕ)/2 ≤ β^2*N := by
    have h1 := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (N+j.val))
    have h2 := mul_le_mul_of_nonneg_left hn (sq_nonneg β)
    nlinarith only [h1,h2]
  have hp : (r^3)^2 ≤ r^8 := by
    have h := pow_le_pow_right₀ hr (by norm_num : 6 ≤ 8)
    nlinarith only [h]
  have hcoef : β^2+9*L ≤ (|β|+3*L)^2 := by
    nlinarith [sq_abs β,abs_nonneg β,mul_nonneg (sub_nonneg.mpr hL) (show 0 ≤ L by linarith),
      mul_nonneg (abs_nonneg β) (show 0 ≤ L by linarith)]
  unfold coreFluctuationBound
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · change (β*coreScale (N+j))^2*(N+j.val:ℕ)/2+9*L*(r^3)^2 ≤ ((|β|+3*L)*r^4)^2
    rw [hN'] at hbn
    have hp' := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ) ≤ 9*L)
    have hh := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hr0 8)
    nlinarith only [hbn,hp',hh]

def windowSlope (β : ℝ) (N : ℕ) : ℝ := (pressure β (N+N)-pressure β N)/(N:ℝ)

lemma tendsto_windowSlope {β : ℝ} (hβ : 0<β) :
    Tendsto (windowSlope β) atTop (𝓝 (β*limitingFreeEnergy β)) := by
  have hN : Tendsto (fun N : ℕ => N+N) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_add_right N N) tendsto_id
  have h := (((tendsto_pressure_perSpin hβ).comp hN).const_mul 2).sub (tendsto_pressure_perSpin hβ)
  have he : ∀ᶠ N in atTop, windowSlope β N=
      2*(pressure β (N+N)/(N+N:ℕ))-pressure β N/(N:ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
    dsimp [windowSlope]
    push_cast
    field_simp
    ring
  apply Tendsto.congr' (he.mono fun _ h => h.symm)
  simpa only [Function.comp_def, show 2*(β*limitingFreeEnergy β)-β*limitingFreeEnergy β=β*limitingFreeEnergy β by ring] using h

lemma cavityWindowBudget_root_bound {N m : ℕ} (hN : 0<N) (d : Fin (m+1) → ℕ)
    (β : ℝ) {ell : ℝ} (hell : 0 ≤ ell) :
    cavityWindowBudget N d β (eighthRootScale N^3) (eighthRootScale N^2) ell
      ((|β|+3*(m+1:ℕ))*eighthRootScale N^4) ≤ windowSlope β N+
      (Real.pi*(8*(m+1:ℕ)+4*(∑ k,(d k:ℝ))))/(eighthRootScale N^2)+
      (ell*(m+1:ℕ)*(17+4*|β|+12*(m+1:ℕ)))/eighthRootScale N := by
  let r := eighthRootScale N
  let L : ℝ := (m+1:ℕ)
  have hr : 1 ≤ r := one_le_eighthRootScale hN
  have hrp : 0<r := by linarith
  have hN' : (N:ℝ)=r^8 := (eighthRootScale_pow_eight N).symm
  have hsmall : 5+4*((|β|+3*L)*r^4)/r^2+12*r^2 ≤ (17+4*|β|+12*L)*r^2 := by
    have he : 4*((|β|+3*L)*r^4)/r^2=4*(|β|+3*L)*r^2 := by field_simp
    rw [he]
    nlinarith [sq_nonneg (r-1)]
  have hm := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ ell/r^3*L by positivity)
  dsimp [cavityWindowBudget,windowSlope]
  change _ ≤ (pressure β (N+N)-pressure β N)/(N:ℝ)+
    (Real.pi*(8*L+4*(∑ k,(d k:ℝ))))/r^2+(ell*L*(17+4*|β|+12*L))/r
  rw [hN']
  have he : (pressure β (N+N)-pressure β N+Real.pi*(8*L+4*(∑ k,(d k:ℝ)))*(r^3)^2)/r^8=
      (pressure β (N+N)-pressure β N)/r^8+(Real.pi*(8*L+4*(∑ k,(d k:ℝ))))/r^2 := by
    field_simp
  change (pressure β (N+N)-pressure β N+Real.pi*(8*L+4*(∑ k,(d k:ℝ)))*(r^3)^2)/r^8+
    (ell/r^3)*L*(5+4*((|β|+3*L)*r^4)/r^2+12*r^2) ≤ _
  rw [he]
  have he' : (ell/r^3*L)*((17+4*|β|+12*L)*r^2)=(ell*L*(17+4*|β|+12*L))/r := by
    field_simp
  rw [he'] at hm
  linarith

lemma tendsto_root_window_bound {m : ℕ} (d : Fin (m+1) → ℕ) {β : ℝ} (hβ : 0<β) (ell : ℝ) :
    Tendsto (fun N => windowSlope β N+
      (Real.pi*(8*(m+1:ℕ)+4*(∑ k,(d k:ℝ))))/(eighthRootScale N^2)+
      (ell*(m+1:ℕ)*(17+4*|β|+12*(m+1:ℕ)))/eighthRootScale N) atTop (𝓝 (β*limitingFreeEnergy β)) := by
  have hi : Tendsto (fun N => (eighthRootScale N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_eighthRootScale
  have h1 := (hi.pow 2).const_mul (Real.pi*(8*(m+1:ℕ)+4*(∑ k,(d k:ℝ))))
  have h2 := hi.const_mul (ell*(m+1:ℕ)*(17+4*|β|+12*(m+1:ℕ)))
  have h := ((tendsto_windowSlope hβ).add h1).add h2
  simpa only [div_eq_mul_inv,inv_pow,zero_pow (by decide : 2≠0),mul_zero,add_zero] using h

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

 

theorem exists_cavity_compatible {m : ℕ} (d : Fin (m+1) → ℕ) {β : ℝ} (hβ : 0<β)
    (M : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ (n : ℕ) (x : Fin (m+1) → ℝ), M ≤ n ∧ 0<n ∧
      (∑ k, (x k)^2)/(n:ℝ) ≤ ε ∧
      mixedIncrement n d β x ≤ β*limitingFreeEnergy β+ε ∧
      ∀ (k : Fin (m+1)) (r : ℕ) (i : Fin r) (f : (Fin r → Configuration n) → ℝ),
      (∀ σ, |f σ| ≤ 1) → |mixedGGDefect d (β*coreScale n) x k i f| ≤ ε := by
  let τ := min ε 1
  have hτ : 0<τ := lt_min hε (by norm_num)
  have hτε : τ ≤ ε := min_le_left _ _
  have hτ1 : τ ≤ 1 := min_le_right _ _
  let P := β*limitingFreeEnergy β
  let a := Real.log 2-Real.pi*β^2/2
  let ell := (|P-a|+2)/τ
  have hell : 0<ell := by dsimp [ell]; positivity
  let B (N : ℕ) := windowSlope β N+
      (Real.pi*(8*(m+1:ℕ)+4*(∑ k,(d k:ℝ))))/(eighthRootScale N^2)+
      (ell*(m+1:ℕ)*(17+4*|β|+12*(m+1:ℕ)))/eighthRootScale N
  have hB : ∀ᶠ N in atTop, B N<P+τ :=
    (tendsto_root_window_bound d hβ ell).eventually (eventually_lt_nhds (by dsimp [P]; linarith))
  have hi : Tendsto (fun N => (eighthRootScale N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_eighthRootScale
  have hv : Tendsto (fun N => 4*(m+1:ℕ)/(eighthRootScale N^2)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,inv_pow,zero_pow (by decide : 2≠0),mul_zero] using
      (hi.pow 2).const_mul ((4:ℝ)*(m+1:ℕ))
  have hv' : ∀ᶠ N in atTop, 4*(m+1:ℕ)/(eighthRootScale N^2)<ε :=
    hv.eventually (eventually_lt_nhds hε)
  obtain ⟨N,hN,hMN,hBN,hVN⟩ := (eventually_gt_atTop 0 |>.and ((eventually_ge_atTop M).and (hB.and hv'))).exists
  have hr := one_le_eighthRootScale hN
  have hrp : 0<eighthRootScale N := by linarith
  have hδ : eighthRootScale N^2 ≤ eighthRootScale N^3 := pow_le_pow_right₀ hr (by norm_num)
  obtain ⟨j,x,hx,hc,hg⟩ := exists_cavity_GG_choice hN d β (pow_pos hrp 3) (pow_pos hrp 2) hδ hell
    (coreFluctuation_window_bound hN β)
  have hb := cavityWindowBudget_root_bound hN d β hell.le
  change _ ≤ B N at hb
  have hbudget := hb.trans hBN.le
  have hn : 0<N+j.val := by omega
  refine ⟨N+j,x,by omega,hn,?_,?_,fun k r i f hf => ?_⟩
  · have hs := Finset.sum_le_sum (fun k (_ : k∈Finset.univ) => eighthRoot_amplitude_pressure_bound hN (hx k))
    rw [← Finset.sum_div] at hs
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
    have hn' : (0:ℝ)<N := Nat.cast_pos.mpr hN
    have hle : (N:ℝ) ≤ (N+j.val:ℕ) := by exact_mod_cast (Nat.le_add_right N j.val)
    have hd := div_le_div_of_nonneg_left (Finset.sum_nonneg (s:=Finset.univ) fun (k : Fin (m+1)) _ => sq_nonneg (x k)) hn' hle
    apply hd.trans (hs.trans _)
    have he : (m+1:ℕ)*(4/(eighthRootScale N^2))=4*(m+1:ℕ)/(eighthRootScale N^2) := by ring
    rw [he]
    exact hVN.le
  · exact hc.trans (hbudget.trans (add_le_add_right hτε P))
  · apply (hg k r i f hf).trans
    apply (div_le_iff₀ hell).mpr
    have habs : P-a ≤ |P-a| := le_abs_self _
    have he : τ*ell=|P-a|+2 := by dsimp [ell]; field_simp
    have hmul := mul_le_mul_of_nonneg_right hτε hell.le
    change _-a ≤ ε*ell
    nlinarith only [hbudget,habs,hτ1,he,hmul]

end SKCavity

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def compatibleSize {β : ℝ} (hβ : 0<β) (m : ℕ) : ℕ :=
  (exists_cavity_compatible (show Fin (m+1) → ℕ from Fin.val) hβ (m+1)
    (by positivity : (0:ℝ)<1/(m+1:ℕ))).choose

def compatibleAmplitude {β : ℝ} (hβ : 0<β) (m : ℕ) : Fin (m+1) → ℝ :=
  (exists_cavity_compatible (show Fin (m+1) → ℕ from Fin.val) hβ (m+1)
    (by positivity : (0:ℝ)<1/(m+1:ℕ))).choose_spec.choose

lemma compatible_spec {β : ℝ} (hβ : 0<β) (m : ℕ) :
    m+1 ≤ compatibleSize hβ m ∧ 0<compatibleSize hβ m ∧
    (∑ k, (compatibleAmplitude hβ m k)^2)/(compatibleSize hβ m:ℝ) ≤ 1/(m+1:ℕ) ∧
    mixedIncrement (compatibleSize hβ m) Fin.val β (compatibleAmplitude hβ m) ≤ β*limitingFreeEnergy β+1/(m+1:ℕ) ∧
    ∀ (k : Fin (m+1)) (r : ℕ) (i : Fin r) (f : (Fin r → Configuration (compatibleSize hβ m)) → ℝ),
      (∀ σ, |f σ| ≤ 1) → |mixedGGDefect Fin.val (β*coreScale (compatibleSize hβ m))
        (compatibleAmplitude hβ m) k i f| ≤ 1/(m+1:ℕ) :=
  (exists_cavity_compatible (show Fin (m+1) → ℕ from Fin.val) hβ (m+1)
    (by positivity : (0:ℝ)<1/(m+1:ℕ))).choose_spec.choose_spec

def compatibleCoeff {β : ℝ} (hβ : 0<β) (m : ℕ) :=
  mixedCoeff (compatibleSize hβ m) Fin.val (β*coreScale (compatibleSize hβ m)) (compatibleAmplitude hβ m)

def compatibleLaw {β : ℝ} (hβ : 0<β) (m : ℕ) : ProbabilityMeasure OverlapArray :=
  fieldOverlapLaw (t:=m) (compatibleCoeff hβ m)

def compatibleValue {β : ℝ} (hβ : 0<β) (m : ℕ) : ℝ :=
  mixedIncrement (compatibleSize hβ m) Fin.val β (compatibleAmplitude hβ m)

lemma compatibleValue_le {β : ℝ} (hβ : 0<β) (m : ℕ) :
    compatibleValue hβ m ≤ β*limitingFreeEnergy β+1/(m+1:ℕ) := (compatible_spec hβ m).2.2.2.1

lemma compatibleGG_le {β : ℝ} (hβ : 0<β) {m p r : ℕ} (hp : p ≤ m) (i : Fin r)
    (f : (Fin r → Configuration (compatibleSize hβ m)) → ℝ) (hf : ∀ σ, |f σ| ≤ 1) :
    |overlapGGDefect (compatibleCoeff hβ m) p i f| ≤ 1/(m+1:ℕ) :=
  (compatible_spec hβ m).2.2.2.2 ⟨p,Nat.lt_succ_of_le hp⟩ r i f hf

lemma tendsto_succ_reciprocal : Tendsto (fun m : ℕ => (1:ℝ)/(m+1:ℕ)) atTop (𝓝 0) := by
  have h : Tendsto (fun m : ℕ => ((m+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun m => Nat.le_succ m) tendsto_id)
  simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp h

lemma tendsto_compatibleGG {β : ℝ} (hβ : 0<β) (p r : ℕ) (i : Fin r)
    (f : ∀ m, (Fin r → Configuration (compatibleSize hβ m)) → ℝ) (hf : ∀ m σ, |f m σ| ≤ 1) :
    Tendsto (fun m => overlapGGDefect (compatibleCoeff hβ m) p i (f m)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  exact squeeze_zero' (Eventually.of_forall fun m => abs_nonneg _) ((eventually_ge_atTop p).mono
    fun m hm => compatibleGG_le hβ hm i (f m) (hf m)) tendsto_succ_reciprocal

lemma compatible_limit_Gram {β : ℝ} (hβ : 0<β) {μ : ProbabilityMeasure OverlapArray} {φ : ℕ → ℕ}
    (hμ : Tendsto (fun k => compatibleLaw hβ (φ k)) atTop (𝓝 μ)) :
    (μ : Measure _) GramArrays=1 := by
  have h := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ isClosed_GramArrays
  have he : ∀ k, (compatibleLaw hβ (φ k) : Measure _) GramArrays=(1:ℝ≥0∞) := fun k =>
    finiteProbability_set_of_forall _ (fieldReplicaMass_nonneg _) (sum_fieldReplicaMass (φ k+1) _) _
      (configurationOverlap_mem_Gram (compatible_spec hβ (φ k)).2.1)
  simp_rw [he] at h
  rw [limsup_const] at h
  exact le_antisymm prob_le_one h

lemma compatible_limit_GG {β : ℝ} (hβ : 0<β) {μ : ProbabilityMeasure OverlapArray} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (hμ : Tendsto (fun k => compatibleLaw hβ (φ k)) atTop (𝓝 μ))
    (r p : ℕ) (i : Fin r) (f : C(OverlapBlock r,ℝ)) (hf : ∀ R, |f R| ≤ 1) :
    arrayGGDefect μ r p i f=0 := by
  have hz := (tendsto_compatibleGG hβ p r i
    (fun _ σ => f (blockOfReplicas σ)) (fun _ σ => hf _)).comp hφ.tendsto_atTop
  have he : ∀ᶠ k in atTop,
      overlapGGDefect (compatibleCoeff hβ (φ k)) p i (fun σ => f (blockOfReplicas σ))=
        arrayGGDefect (compatibleLaw hβ (φ k)) r p i f := by
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop (max r 1))] with k hk
    exact (arrayGGDefect_fieldOverlapLaw (by omega) (by omega) _ p i f).symm
  exact tendsto_nhds_unique ((continuous_arrayGGDefect r p i f).tendsto μ |>.comp hμ) (hz.congr' he)

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

lemma compatible_limit_GG_unbounded {β : ℝ} (hβ : 0<β) {μ : ProbabilityMeasure OverlapArray} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (hμ : Tendsto (fun k => compatibleLaw hβ (φ k)) atTop (𝓝 μ))
    (r p : ℕ) (i : Fin r) (f : C(OverlapBlock r,ℝ)) : arrayGGDefect μ r p i f=0 := by
  let M : ℝ := ‖f‖+1
  have hm : 0<M := by dsimp [M]; positivity
  have hf : ∀ R, |((M⁻¹) • f) R| ≤ 1 := by
    intro R
    change |M⁻¹*f R| ≤ 1
    rw [abs_mul, abs_of_pos (inv_pos.mpr hm), ← div_eq_inv_mul]
    apply (div_le_one hm).mpr
    have := f.norm_coe_le_norm R
    simpa only [Real.norm_eq_abs] using this.trans (le_add_of_nonneg_right (by norm_num : (0:ℝ)≤1))
  have h := compatible_limit_GG hβ hφ hμ r p i (M⁻¹ • f) hf
  change arrayGGDefect μ r p i (fun R => M⁻¹*f R)=0 at h
  rw [arrayGGDefect_const_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero hm.ne')

 
theorem compatible_limit_continuousGG {β : ℝ} (hβ : 0<β) {μ : ProbabilityMeasure OverlapArray} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (hμ : Tendsto (fun k => compatibleLaw hβ (φ k)) atTop (𝓝 μ))
    (r : ℕ) (i : Fin r) (f : C(OverlapBlock r,ℝ)) (ψ : C(OverlapEntry,ℝ)) :
    continuousGG μ r i f ψ=0 := by
  let L := continuousGG μ r i f
  have hp (p : ℕ) : L (overlapPower p)=0 := by
    rw [continuousGG_power]
    exact compatible_limit_GG_unbounded hβ hφ hμ r p i f
  have hpoly (p : Polynomial ℝ) : L (p.toContinuousMapOn (Set.Icc (-1:ℝ) 1))=0 := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      have he : (p+q).toContinuousMapOn (Set.Icc (-1:ℝ) 1)=p.toContinuousMapOn _+q.toContinuousMapOn _ := by
        ext x; simp [Polynomial.toContinuousMapOn]
      rw [he, map_add, hp, hq, add_zero]
    | monomial p a =>
      have he : (Polynomial.monomial p a).toContinuousMapOn (Set.Icc (-1:ℝ) 1)=a • overlapPower p := by
        ext x; simp [Polynomial.toContinuousMapOn, overlapPower]
      rw [he, map_smul, hp, smul_zero]
  have hs : (polynomialFunctions (Set.Icc (-1:ℝ) 1) : Set C(OverlapEntry,ℝ)) ⊆ {g | L g=0} := by
    intro g hg
    rw [polynomialFunctions_coe] at hg
    rcases hg with ⟨p,rfl⟩
    exact hpoly p
  have hc := closure_minimal hs (isClosed_eq L.continuous continuous_const)
  exact hc (continuousMap_mem_polynomialFunctions_closure (-1) 1 ψ)

lemma compatible_limit_exchangeable_integral {β : ℝ} (hβ : 0<β) {μ : ProbabilityMeasure OverlapArray} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (hμ : Tendsto (fun k => compatibleLaw hβ (φ k)) atTop (𝓝 μ))
    (r : ℕ) (e : Fin r → ℕ) (he : Function.Injective e) (f : C(OverlapBlock r,ℝ)) :
    (∫ R, f (selectedBlock e R) ∂(μ : Measure OverlapArray))=
      ∫ R, f (blockOfArray r R) ∂(μ : Measure OverlapArray) := by
  let F : C(OverlapArray,ℝ) := f.comp ⟨selectedBlock e,continuous_selectedBlock e⟩
  let G : C(OverlapArray,ℝ) := f.comp ⟨blockOfArray r,continuous_blockOfArray r⟩
  have hF := (ProbabilityMeasure.continuous_integral_continuousMap F).tendsto μ |>.comp hμ
  have hG := (ProbabilityMeasure.continuous_integral_continuousMap G).tendsto μ |>.comp hμ
  have ha : ∀ᶠ k in atTop,
      (∫ R, F R ∂(compatibleLaw hβ (φ k) : Measure OverlapArray))=
        ∫ R, G R ∂(compatibleLaw hβ (φ k) : Measure OverlapArray) := by
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop (max r (∑ i,e i)))] with k hk
    have hr : r ≤ φ k+1 := by omega
    have ht (i : Fin r) : e i<φ k+1 := by
      have h := Finset.single_le_sum (fun j _ => Nat.zero_le (e j)) (Finset.mem_univ i)
      omega
    change (∫ R, f (selectedBlock e R) ∂(fieldOverlapLaw (t:=φ k) (compatibleCoeff hβ (φ k)) : Measure _))=_
    rw [integral_fieldOverlapLaw_selected hr e he ht]
    exact (integral_fieldOverlapLaw_block hr _ f).symm
  exact tendsto_nhds_unique (hF.congr' ha) hG

 
theorem compatible_limit_exchangeable {β : ℝ} (hβ : 0<β) {μ : ProbabilityMeasure OverlapArray} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (hμ : Tendsto (fun k => compatibleLaw hβ (φ k)) atTop (𝓝 μ))
    (r : ℕ) (e : Fin r → ℕ) (he : Function.Injective e) :
    (μ : Measure OverlapArray).map (selectedBlock e)=blockLaw μ r := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map (continuous_selectedBlock e).measurable.aemeasurable f.continuous.aestronglyMeasurable,
    blockLaw, integral_map (continuous_blockOfArray r).measurable.aemeasurable f.continuous.aestronglyMeasurable]
  exact compatible_limit_exchangeable_integral hβ hφ hμ r e he f.toContinuousMap

 

theorem exists_compatible_ultrametric_limit {β : ℝ} (hβ : 0<β) :
    ∃ (μ : ProbabilityMeasure OverlapArray) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k => compatibleLaw hβ (φ k)) atTop (𝓝 μ) ∧
      (μ : Measure OverlapArray) GramArrays=1 ∧ GGIdentities μ ∧ FiniteExchangeable μ ∧
      (μ : Measure OverlapArray) UltrametricArrays=1 ∧
      ∀ k, compatibleValue hβ (φ k) ≤ β*limitingFreeEnergy β+1/(φ k+1:ℕ) := by
  obtain ⟨μ,φ,hφ,hμ⟩ := CompactSpace.tendsto_subseq (compatibleLaw hβ)
  have hG := compatible_limit_Gram hβ hμ
  have hgg : GGIdentities μ := fun r i =>
    GG_measure_identity μ r i (compatible_limit_continuousGG hβ hφ hμ r i)
  have hex : FiniteExchangeable μ := compatible_limit_exchangeable hβ hφ hμ
  exact ⟨μ,φ,hφ,hμ,hG,hgg,hex,GG_ultrametric hG hgg hex,fun k => compatibleValue_le hβ (φ k)⟩

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

 
def partitionBlock {r : ℕ} (c : Fin r → ℕ) (q : ℝ) : Set (OverlapBlock r) :=
  {T | ∀ i j, q<(T i j:ℝ) ↔ c i=c j}

def partitionEvent {r : ℕ} (c : Fin r → ℕ) (q : ℝ) : Set OverlapArray :=
  (blockOfArray r) ⁻¹' partitionBlock c q

lemma measurableSet_partitionBlock {r : ℕ} (c : Fin r → ℕ) (q : ℝ) :
    MeasurableSet (partitionBlock c q) := by
  unfold partitionBlock
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases h : c i=c j
  · simp only [h,iff_true]
    exact measurableSet_lt measurable_const (by fun_prop)
  · simp only [h,iff_false,not_lt]
    exact measurableSet_le (by fun_prop) measurable_const

lemma measurableSet_partitionEvent {r : ℕ} (c : Fin r → ℕ) (q : ℝ) :
    MeasurableSet (partitionEvent c q) :=
  (measurableSet_partitionBlock c q).preimage (continuous_blockOfArray r).measurable

def clusterCount {r : ℕ} (c : Fin r → ℕ) (i : Fin r) : ℕ :=
  (Finset.univ.filter (fun j => c j=c i)).card

lemma clusterCount_pos {r : ℕ} (c : Fin r → ℕ) (i : Fin r) : 0<clusterCount c i := by
  apply Finset.card_pos.mpr
  exact ⟨i,by simp⟩

lemma partition_pair_event {r : ℕ} (c : Fin r → ℕ) (q : ℝ) (i j : Fin r) :
    {R | R∈partitionEvent c q ∧ q<(R i j:ℝ)}=
      if c i=c j then partitionEvent c q else ∅ := by
  split_ifs with h
  · ext R
    exact ⟨fun hR => hR.1,fun hR => ⟨hR,(hR i j).mpr h⟩⟩
  · ext R
    simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
    exact fun hR => h ((hR.1 i j).mp hR.2)

 

theorem GG_partition_join {μ : ProbabilityMeasure OverlapArray} (hgg : GGIdentities μ)
    {r : ℕ} (c : Fin r → ℕ) (q : ℝ) (i : Fin r) :
    (r:ℝ)*(μ:Measure OverlapArray).real {R | R∈partitionEvent c q ∧ q<(R i r:ℝ)}=
      (μ:Measure OverlapArray).real (partitionEvent c q)*
        ((clusterCount c i:ℝ)-1+(entryLaw μ 0 1).real {x | q<(x:ℝ)}) := by
  have h := GG_event_identity hgg r i (partitionBlock c q) {x | q<(x:ℝ)}
    (measurableSet_partitionBlock c q) (measurableSet_lt measurable_const (by fun_prop))
  change (r:ℝ)*(μ:Measure OverlapArray).real {R | R∈partitionEvent c q ∧ q<(R i r:ℝ)}=
    (μ:Measure OverlapArray).real (partitionEvent c q)*(entryLaw μ 0 1).real {x | q<(x:ℝ)}+
      ∑ l∈Finset.univ.erase i,(μ:Measure OverlapArray).real {R | R∈partitionEvent c q ∧ q<(R i l:ℝ)} at h
  simp_rw [partition_pair_event] at h
  simp only [apply_ite,measureReal_empty] at h
  have hs : (∑ l∈Finset.univ.erase i,if c i=c l then (μ:Measure OverlapArray).real (partitionEvent c q) else 0)=
    ((clusterCount c i:ℝ)-1)*(μ:Measure OverlapArray).real (partitionEvent c q) := by
    have hj : (∑ l : Fin r,if c i=c l then (μ:Measure OverlapArray).real (partitionEvent c q) else 0)=
        (clusterCount c i:ℝ)*(μ:Measure OverlapArray).real (partitionEvent c q) := by
      simp only [← Finset.sum_filter]
      simp only [Finset.sum_const,nsmul_eq_mul]
      congr 2
      apply congrArg Finset.card
      ext l
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,eq_comm]
    have hh := Finset.sum_erase_add (s:=Finset.univ)
      (f:=fun l => if c i=c l then (μ:Measure OverlapArray).real (partitionEvent c q) else 0) (Finset.mem_univ i)
    simp only [ite_true] at hh
    rw [hj] at hh
    linarith
  rw [hs] at h
  nlinarith only [h]

lemma ultrametric_partition_join_disjoint {r : ℕ} (c : Fin r → ℕ) (q : ℝ) (i j : Fin r)
    (hij : c i≠c j) :
    Disjoint {R | R∈UltrametricArrays ∧ R∈partitionEvent c q ∧ q<(R i r:ℝ)}
      {R | R∈UltrametricArrays ∧ R∈partitionEvent c q ∧ q<(R j r:ℝ)} := by
  apply Set.disjoint_left.mpr
  intro R hi hj
  have hu := hi.1 i j r
  exact hij ((hi.2.1 i j).mp ((lt_min hi.2.2 hj.2.2).trans_le hu))

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def overlapDiscount (μ : ProbabilityMeasure OverlapArray) (q : ℝ) : ℝ :=
  (entryLaw μ 0 1).real {x | (x:ℝ) ≤ q}

lemma entry_upper_mass (μ : ProbabilityMeasure OverlapArray) (q : ℝ) :
    (entryLaw μ 0 1).real {x | q<(x:ℝ)}=1-overlapDiscount μ q := by
  let := entryLaw_probability μ 0 1
  have h : {x : OverlapEntry | q<(x:ℝ)}={x : OverlapEntry | (x:ℝ) ≤ q}ᶜ := by ext x; simp
  rw [h,probReal_compl_eq_one_sub (measurableSet_le (by fun_prop) measurable_const)]
  rfl

lemma GG_cluster_join {μ : ProbabilityMeasure OverlapArray} (hgg : GGIdentities μ)
    {r : ℕ} (c : Fin r → ℕ) (q : ℝ) (i : Fin r) :
    (r:ℝ)*(μ:Measure OverlapArray).real {R | R∈partitionEvent c q ∧ q<(R i r:ℝ)}=
      ((clusterCount c i:ℝ)-overlapDiscount μ q)*(μ:Measure OverlapArray).real (partitionEvent c q) := by
  rw [GG_partition_join hgg,entry_upper_mass]
  ring

def ClusterReps {r : ℕ} (c : Fin r → ℕ) (S : Finset (Fin r)) : Prop :=
  Set.InjOn c S ∧ ∀ i, ∃ j∈S, c j=c i

lemma exists_clusterReps {r : ℕ} (c : Fin r → ℕ) : ∃ S, ClusterReps c S := by
  have h : Set.SurjOn c Set.univ (Finset.univ.image c) := by
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact ⟨j,Set.mem_univ _,rfl⟩
  obtain ⟨S,_,hinj,hS⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn Set.univ (Finset.univ.image c) h
  refine ⟨S,hinj,fun i => ?_⟩
  have hi : c i∈S.image c := by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  exact Finset.mem_image.mp hi

lemma sum_clusterCount {r : ℕ} {c : Fin r → ℕ} {S : Finset (Fin r)} (hS : ClusterReps c S) :
    (∑ i∈S, clusterCount c i)=r := by
  have hc (i) : clusterCount c i=∑ j : Fin r,if c j=c i then 1 else 0 := by
    simp [clusterCount]
  simp_rw [hc]
  rw [Finset.sum_comm]
  have h1 (j : Fin r) : (∑ i∈S,if c j=c i then 1 else 0)=1 := by
    obtain ⟨i,hi,hij⟩ := hS.2 j
    rw [Finset.sum_eq_single i]
    · simp [hij]
    · intro k hk hki
      have hne : c j≠c k := fun hh => hki (hS.1 hk hi (hh.symm.trans hij.symm))
      simp [hne]
    · exact fun h => (h hi).elim
  simp_rw [h1]
  simp

lemma ae_full_probability {X : Type*} [MeasurableSpace X] (μ : ProbabilityMeasure X)
    {S : Set X} (hS : MeasurableSet S) (h : (μ:Measure X) S=1) : ∀ᵐ x ∂(μ:Measure X), x∈S := by
  apply ae_iff.mpr
  change (μ:Measure X) Sᶜ=0
  rw [measure_compl hS (measure_ne_top _ _),h]
  simp

 

theorem GG_cluster_innovation {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {r : ℕ} {c : Fin r → ℕ} {S : Finset (Fin r)} (hS : ClusterReps c S) (q : ℝ) :
    (r:ℝ)*(μ:Measure OverlapArray).real {R | R∈partitionEvent c q ∧ ∀ i : Fin r, (R i r:ℝ) ≤ q}=
      (S.card:ℝ)*overlapDiscount μ q*(μ:Measure OverlapArray).real (partitionEvent c q) := by
  let U := GramArrays∩UltrametricArrays
  have hUa : ∀ᵐ R ∂(μ:Measure OverlapArray), R∈U :=
    (ae_full_probability μ isClosed_GramArrays.measurableSet hG).and
      (ae_full_probability μ isClosed_UltrametricArrays.measurableSet hu)
  have hUr (T : Set OverlapArray) : (μ:Measure OverlapArray).real (U∩T)=(μ:Measure OverlapArray).real T :=
    congrArg ENNReal.toReal (Measure.measure_inter_eq_of_ae hUa)
  let E := partitionEvent c q
  let J (i : Fin r) : Set OverlapArray := {R | R∈E ∧ q<(R i r:ℝ)}
  let A : Set OverlapArray := ⋃ i∈S, J i
  have hJ (i : Fin r) : MeasurableSet (J i) := by
    change MeasurableSet (partitionEvent c q ∩ {R : OverlapArray | q<(R i r:ℝ)})
    exact (measurableSet_partitionEvent c q).inter (measurableSet_lt measurable_const (by fun_prop))
  have hA : MeasurableSet A := MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hJ i
  have hdis : Set.PairwiseDisjoint (S:Set (Fin r)) (fun i => U∩J i) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro R hRi hRj
    have hne : c i≠c j := fun hh => hij (hS.1 hi hj hh)
    have h := hRi.1.2 i j r
    exact hne ((hRi.2.1 i j).mp ((lt_min hRi.2.2 hRj.2.2).trans_le h))
  have hsum : (μ:Measure OverlapArray).real A=∑ i∈S,(μ:Measure OverlapArray).real (J i) := by
    rw [← hUr A]
    have he : U∩A=⋃ i∈S,U∩J i := by ext R; simp only [A,Set.mem_inter_iff,Set.mem_iUnion]; aesop
    rw [he,measureReal_biUnion_finset hdis (fun i _ =>
      (isClosed_GramArrays.measurableSet.inter isClosed_UltrametricArrays.measurableSet).inter (hJ i))]
    exact Finset.sum_congr rfl fun i _ => hUr (J i)
  have hcompl : (μ:Measure OverlapArray).real {R | R∈E ∧ ∀ i : Fin r, (R i r:ℝ) ≤ q}=
      (μ:Measure OverlapArray).real (E\A) := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hUa] with R hR
    apply propext
    constructor
    · rintro ⟨hE,hnew⟩
      refine ⟨hE,?_⟩
      simp only [A,Set.mem_iUnion]
      rintro ⟨i,hi,hj⟩
      exact (not_lt_of_ge (hnew i)) hj.2
    · rintro ⟨hE,hnot⟩
      refine ⟨hE,fun i => ?_⟩
      by_contra hi
      have hi' : q<(R i r:ℝ) := lt_of_not_ge hi
      obtain ⟨j,hj,hij⟩ := hS.2 i
      have ho : q<(R j i:ℝ) := (hE j i).mpr hij
      have hu' := hR.2 j r i
      rw [hR.1.1 r i] at hu'
      have hj' : q<(R j r:ℝ) := (lt_min ho hi').trans_le hu'
      exact hnot (Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hj,⟨hE,hj'⟩⟩⟩)
  rw [hcompl,measureReal_sdiff (by
    intro R hR
    obtain ⟨i,hR⟩ := Set.mem_iUnion.mp hR
    obtain ⟨_,hR⟩ := Set.mem_iUnion.mp hR
    exact hR.1) hA,hsum]
  have hi := Finset.sum_congr (s₁:=S) (s₂:=S) rfl (fun i _ => GG_cluster_join hgg c q i)
  rw [← Finset.mul_sum] at hi
  have hc := sum_clusterCount hS
  have hc' : (∑ i∈S,(clusterCount c i:ℝ))=(r:ℝ) := by exact_mod_cast hc
  simp_rw [sub_mul] at hi
  rw [Finset.sum_sub_distrib,← Finset.sum_mul,hc',Finset.sum_const,nsmul_eq_mul] at hi
  change (r:ℝ)*(∑ i∈S,(μ:Measure OverlapArray).real (J i))=_ at hi
  nlinarith only [hi]

end SKCavity

end

end OAI
