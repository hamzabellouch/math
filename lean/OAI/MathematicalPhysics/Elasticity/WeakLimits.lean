import OAI.MathematicalPhysics.Elasticity.PhysicalCGO

namespace OAI

noncomputable section

namespace ElasticityDistribution

section
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open ElasticityAugmented TemperedDistribution TrivSqZeroExt

lemma complex_inr_smul (c : ℂ) (u : Dist) : (c • (inr u : Ext))=inr (c • u) := by
  exact (TrivSqZeroExt.inr_smul Coeff c u).symm

def directiond (θ : Fin 3 → ℂ) (u : Dist) : Dist := ∑ i, θ i • dd i u
def normald (θ : Fin 3 → ℂ) (u : Fin 3 → Dist) : Dist := ∑ i, θ i • u i
def leadingRd (θ : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (b : Dist) (i : Fin 3) : Dist :=
  (2*m) • directiond θ (u i)+direction dc θ m • u i+
    θ i • ((lam+m) • b+∑ j, dc j m • u j)
def leadingSd (θ : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (b : Dist) : Dist :=
  (2*(lam+m+m)) • directiond θ b+(2*direction dc θ (lam+m)) • b+
    (4 : Coeff) • (∑ i, dc i m • directiond θ (u i))+
    (2 : Coeff) • (∑ i, direction dc θ (dc i m) • u i)

lemma direction_inr (θ : Fin 3 → ℂ) (u : Dist) :
    direction (A := Ext) de θ (inr u)=inr (directiond θ u) := by
  simp only [direction,directiond,de_inr,inr_smul,inr_sum]
lemma direction_inl (θ : Fin 3 → ℂ) (a : Coeff) :
    direction (A := Ext) de θ (inl a)=inl (direction dc θ a) := by
  simp only [direction,de_inl,inl_smul,inl_sum]
lemma leadingR_inr (θ : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (b : Dist) (i : Fin 3) :
    leadingR de θ (inl lam) (inl m) (fun j => inr (u j)) (inr b) i =
      inr (leadingRd θ lam m u b i) := by
  simp only [leadingR,leadingRd,direction_inr,direction_inl,← inl_two,
    coff_inl_mul,coff_inl_add,inl_mul_inr,de_inl,← inr_sum,← inr_add,complex_inr_smul]
lemma leadingS_inr (θ : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (b : Dist) :
    leadingS de θ (inl lam) (inl m) (fun j => inr (u j)) (inr b) =
      inr (leadingSd θ lam m u b) := by
  have hf : (4 : Ext)=inl (4 : Coeff) := (inl_natCast 4).symm
  simp only [leadingS,leadingSd,direction_inr,direction_inl,← inl_two,hf,
    coff_inl_mul,coff_inl_add,inl_mul_inr,de_inl,← inr_sum,← inr_add]

/-- Exact null-phase polynomial decomposition for the physical distributions. -/
theorem rd_null_expansion (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0)
    (τ : ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (b : Dist) (i : Fin 3) :
    rd (τ • θ) lam m u b i=rd 0 lam m u b i+τ • leadingRd θ lam m u b i := by
  have he := RT_null_expansion de θ hθ τ (inl lam) (inl m) (fun j => inr (u j)) (inr b) i
  have h0 := RT_inr 0 lam m u b i
  have ht : shifted (A := Ext) de 0=fun i => (de i).toLinearMap := by
    funext i
    apply LinearMap.ext
    intro a
    change de i a+(0 : ℂ) • a=de i a
    rw [zero_smul ℂ a,add_zero]
  rw [ht] at h0
  change R de (inl lam) (inl m) (fun j => inr (u j)) (inr b) i=_ at h0
  rw [RT_inr,h0,leadingR_inr,← inr_smul,← inr_add] at he
  exact congrArg TrivSqZeroExt.snd he

theorem scd_null_expansion (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0)
    (τ : ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (b : Dist) :
    scd (τ • θ) lam m u b=scd 0 lam m u b+τ • leadingSd θ lam m u b := by
  have he := ST_null_expansion de θ hθ τ (inl lam) (inl m) (fun j => inr (u j)) (inr b) de_commute
  have h0 := ST_inr 0 lam m u b
  have ht : shifted (A := Ext) de 0=fun i => (de i).toLinearMap := by
    funext i
    apply LinearMap.ext
    intro a
    change de i a+(0 : ℂ) • a=de i a
    rw [zero_smul ℂ a,add_zero]
  rw [ht] at h0
  change ElasticityAugmented.S de (inl lam) (inl m) (fun j => inr (u j)) (inr b)=_ at h0
  rw [ST_inr,h0,leadingS_inr,← inr_smul,← inr_add] at he
  exact congrArg TrivSqZeroExt.snd he

lemma divergence_phase (θ : Fin 3 → ℂ) (τ : ℂ) (u : Fin 3 → Dist) :
    divd (τ • θ) u=divd 0 u+τ • normald θ u := by
  have hz (i : Fin 3) : sd 0 i (u i)=dd i (u i) := by
    change dd i (u i)+(0 : ℂ) • u i=dd i (u i)
    rw [zero_smul ℂ (u i),add_zero]
  simp only [divd,hz,sd_apply,Pi.smul_apply,smul_eq_mul,normald,
    Finset.sum_add_distrib,Finset.smul_sum,smul_smul]
end
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators
open ElasticityAugmented
abbrev AugHilbert := WithLp 2 (Fin 4 → Lp ℂ 2 (volume : Measure X))
def augEntry (i : Fin 4) : AugHilbert →L[ℂ] Dist :=
  (Lp.toTemperedDistributionCLM ℂ (volume : Measure X) 2).comp
    ((ContinuousLinearMap.proj i).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 4 => Lp ℂ 2 (volume : Measure X))).toContinuousLinearMap)
lemma augEntry_apply (i : Fin 4) (U : AugHilbert) : augEntry i U=(U i : Dist) := rfl

def coeffCLM (a : Coeff) : Dist →L[ℂ] Dist := smulLeftCLM ℂ (eval a)
def ddCLM (i : Fin 3) : Dist →L[ℂ] Dist := LineDeriv.lineDerivOpCLM ℂ Dist (e i)
def sdCLM (z : Fin 3 → ℂ) (i : Fin 3) : Dist →L[ℂ] Dist :=
  ddCLM i+z i • ContinuousLinearMap.id ℂ Dist
def lapdCLM (z : Fin 3 → ℂ) : Dist →L[ℂ] Dist := ∑ i, (sdCLM z i).comp (sdCLM z i)
def directionCLM (θ : Fin 3 → ℂ) : Dist →L[ℂ] Dist := ∑ i, θ i • ddCLM i
lemma coeffCLM_apply (a : Coeff) (u : Dist) : coeffCLM a u=a • u := rfl
lemma ddCLM_apply (i : Fin 3) (u : Dist) : ddCLM i u=dd i u := rfl
lemma sdCLM_apply (z : Fin 3 → ℂ) (i : Fin 3) (u : Dist) : sdCLM z i u=sd z i u := rfl
lemma lapdCLM_apply (z : Fin 3 → ℂ) (u : Dist) : lapdCLM z u=lapd z u := by
  simp only [lapdCLM,lapd,sum_apply,ContinuousLinearMap.comp_apply,sdCLM_apply]
lemma directionCLM_apply (θ : Fin 3 → ℂ) (u : Dist) : directionCLM θ u=directiond θ u := by
  simp only [directionCLM,directiond,sum_apply,smul_apply,ddCLM_apply]

def rdCLM (z : Fin 3 → ℂ) (lam m : Coeff) (i : Fin 3) : AugHilbert →L[ℂ] Dist :=
  (coeffCLM m).comp ((lapdCLM z).comp (augEntry i.succ))+
  (coeffCLM (lam+m)).comp ((sdCLM z i).comp (augEntry 0))+
  (∑ j, (coeffCLM (dc j m)).comp ((sdCLM z j).comp (augEntry i.succ)+(sdCLM z i).comp (augEntry j.succ)))+
  (coeffCLM (dc i lam)).comp (augEntry 0)
def scdCLM (z : Fin 3 → ℂ) (lam m : Coeff) : AugHilbert →L[ℂ] Dist :=
  (coeffCLM (lam+m+m)).comp ((lapdCLM z).comp (augEntry 0))+
  (2 : ℂ) • (∑ i, (coeffCLM (dc i (lam+m))).comp ((sdCLM z i).comp (augEntry 0)))+
  (2 : ℂ) • (∑ i, (coeffCLM (dc i m)).comp ((lapdCLM z).comp (augEntry i.succ)))+
  (2 : ℂ) • (∑ i, ∑ j, (coeffCLM (dc i (dc j m))).comp ((sdCLM z i).comp (augEntry j.succ)))+
  (coeffCLM (∑ i, dc i (dc i lam))).comp (augEntry 0)
def leadingRCLM (θ : Fin 3 → ℂ) (lam m : Coeff) (i : Fin 3) : AugHilbert →L[ℂ] Dist :=
  (coeffCLM (2*m)).comp ((directionCLM θ).comp (augEntry i.succ))+
  (coeffCLM (direction dc θ m)).comp (augEntry i.succ)+
  θ i • ((coeffCLM (lam+m)).comp (augEntry 0)+∑ j, (coeffCLM (dc j m)).comp (augEntry j.succ))
def leadingSCLM (θ : Fin 3 → ℂ) (lam m : Coeff) : AugHilbert →L[ℂ] Dist :=
  (coeffCLM (2*(lam+m+m))).comp ((directionCLM θ).comp (augEntry 0))+
  (coeffCLM (2*direction dc θ (lam+m))).comp (augEntry 0)+
  (coeffCLM 4).comp (∑ i, (coeffCLM (dc i m)).comp ((directionCLM θ).comp (augEntry i.succ)))+
  (coeffCLM 2).comp (∑ i, (coeffCLM (direction dc θ (dc i m))).comp (augEntry i.succ))
def normalCLM (θ : Fin 3 → ℂ) : AugHilbert →L[ℂ] Dist := ∑ i, θ i • augEntry i.succ
def divergenceCLM (z : Fin 3 → ℂ) : AugHilbert →L[ℂ] Dist := ∑ i, (sdCLM z i).comp (augEntry i.succ)
lemma rdCLM_apply (z : Fin 3 → ℂ) (lam m : Coeff) (i : Fin 3) (U : AugHilbert) :
    rdCLM z lam m i U=rd z lam m (fun j => (U j.succ : Dist)) (U 0 : Dist) i := by
  simp only [rdCLM,rd,add_apply,sum_apply,ContinuousLinearMap.comp_apply,
    coeffCLM_apply,lapdCLM_apply,sdCLM_apply,augEntry_apply]
lemma scdCLM_apply (z : Fin 3 → ℂ) (lam m : Coeff) (U : AugHilbert) :
    scdCLM z lam m U=scd z lam m (fun j => (U j.succ : Dist)) (U 0 : Dist) := by
  simp only [scdCLM,scd,add_apply,sum_apply,smul_apply,ContinuousLinearMap.comp_apply,
    coeffCLM_apply,lapdCLM_apply,sdCLM_apply,augEntry_apply]
lemma leadingRCLM_apply (θ : Fin 3 → ℂ) (lam m : Coeff) (i : Fin 3) (U : AugHilbert) :
    leadingRCLM θ lam m i U=leadingRd θ lam m (fun j => (U j.succ : Dist)) (U 0 : Dist) i := by
  simp only [leadingRCLM,leadingRd,add_apply,sum_apply,smul_apply,ContinuousLinearMap.comp_apply,
    coeffCLM_apply,directionCLM_apply,augEntry_apply]
lemma leadingSCLM_apply (θ : Fin 3 → ℂ) (lam m : Coeff) (U : AugHilbert) :
    leadingSCLM θ lam m U=leadingSd θ lam m (fun j => (U j.succ : Dist)) (U 0 : Dist) := by
  simp only [leadingSCLM,leadingSd,add_apply,sum_apply,ContinuousLinearMap.comp_apply,
    coeffCLM_apply,directionCLM_apply,augEntry_apply]
lemma normalCLM_apply (θ : Fin 3 → ℂ) (U : AugHilbert) :
    normalCLM θ U=normald θ (fun j => (U j.succ : Dist)) := by
  simp only [normalCLM,normald,sum_apply,smul_apply,augEntry_apply]
lemma divergenceCLM_apply (z : Fin 3 → ℂ) (U : AugHilbert) :
    divergenceCLM z U=divd z (fun j => (U j.succ : Dist)) := by
  simp only [divergenceCLM,divd,sum_apply,ContinuousLinearMap.comp_apply,sdCLM_apply,augEntry_apply]
end ElasticityDistribution
namespace ElasticityCGO

section
open Set Filter MeasureTheory
open scoped SchwartzMap Topology BigOperators ENNReal
open ElasticityAugmented
open ElasticityBessel (L2 norm2 J)
open ElasticityNegativeOrder (mult sobNorm)
open ElasticityPhysicalAlgebra (divShift)
open ElasticityPhysicalEstimate (physicalAug)
open ElasticityDistribution (AugHilbert)

def augEmbed : (Fin 4 → S) →ₗ[ℂ] AugHilbert where
  toFun u := WithLp.toLp 2 (fun i => L2 (u i))
  map_add' u v := by apply PiLp.ext; intro i; exact map_add L2 _ _
  map_smul' c u := by apply PiLp.ext; intro i; exact map_smul L2 _ _
lemma augEmbed_apply (u : Fin 4 → S) (i : Fin 4) : augEmbed u i=L2 (u i) := rfl
lemma norm_augEmbed (h : ℝ) (u : Fin 4 → S) : ‖augEmbed u‖=sobNorm h 0 u := by
  rw [PiLp.norm_eq_of_L2]
  simp only [augEmbed_apply,sobNorm,ElasticityBessel.J_zero,norm2]
lemma norm_augEmbed_le (h : ℝ) (u : Fin 4 → S) : ‖augEmbed u‖≤ sobNorm h 1 u := by
  rw [norm_augEmbed h]
  simpa only [one_mul] using ElasticityNegativeOrder.sobNorm_component_bound h h 0 1 1
    (by norm_num) u u (fun i => by
      simpa only [ElasticityBessel.J_zero,one_mul] using ElasticityNegativeOrder.norm2_J_one_ge h (u i))
lemma norm2_le_sobNorm {n : ℕ} (h : ℝ) (u : Fin n → S) (i : Fin n) :
    norm2 (u i)≤ sobNorm h 1 u := by
  apply (ElasticityNegativeOrder.norm2_J_one_ge h (u i)).trans
  exact Real.le_sqrt_of_sq_le (Finset.single_le_sum (fun j _ => sq_nonneg (norm2 (J h 1 (u j))))
    (Finset.mem_univ i))

lemma truncation_at_zero (N : ℕ) (f : ℕ → S) : truncation 0 N f=f 0 := by
  induction N with
  | zero => exact truncation_zero 0 f
  | succ N ih => simp only [truncation_succ,ih,zero_pow (Nat.succ_ne_zero N),zero_smul,add_zero]
lemma truncation_continuous (N : ℕ) (f : ℕ → S) : Continuous (fun h : ℂ => truncation h N f) := by
  unfold truncation
  exact continuous_finsetSum _ (fun j _ => (continuous_id.pow j).smul continuous_const)
lemma truncation_tendsto {h : ℕ → ℂ} (hh : Tendsto h atTop (𝓝 0)) (N : ℕ) (f : ℕ → S) :
    Tendsto (fun n => truncation (h n) N f) atTop (𝓝 (f 0)) := by
  simpa only [truncation_at_zero,Function.comp_def] using (truncation_continuous N f).continuousAt.tendsto.comp hh

/-- Exact polynomial formula for the actual localized formal scalar amplitude.
The derivative of the localization is retained; it disappears only where g=1. -/
lemma formal_scalar_polynomial {U : Set X} (hU : IsOpen U)
    (θ : Fin 3 → ℂ) (N : ℕ) (a : ℕ → Amplitude Smooth)
    (h₀ : normal θ (a 0).1=0)
    (hrec : ∀ j<N,EqOn (fun x => ((normal θ (a (j+1)).1 : Smooth) : X → ℂ) x)
      (fun x => ((-(div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) U)
    (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ)) (hχ : EqOn (χ : X → ℂ) 1 U)
    {g : X → ℂ} (hg : g.HasTemperateGrowth) (hs : tsupport g⊆U)
    (h : ℂ) (hh : h≠0) :
    divShift (h⁻¹ • θ) (fun i => mult g (cut χ hc ((truncation h N a).1 i)))=
      truncation h N (fun j => mult g (cut χ hc (a j).2))+
      h^N • mult g (cut χ hc (div coord (a N).1-(a N).2))+
      ∑ i, truncation h N (fun j => mult (fun x => fderiv ℝ g x (e i)) (cut χ hc ((a j).1 i))) := by
  rw [divShift_mult _ g hg]
  have he := cut_truncation_divergence hU θ h hh N a h₀ hrec χ hc hχ
  rw [mult_eq_of_local hg hs he,truncation_scalar]
  simp only [map_add,map_smul,cut_truncation]
  congr 1
  · simp only [truncation,map_sum,map_smul]
  · exact Finset.sum_congr rfl (fun i _ => mult_cut_truncation_vector _ χ hc N a h i)

/-- Strong Schwartz convergence of the formal augmented amplitudes, including
its physical scalar component and the cutoff derivative. -/
theorem formal_augmented_tendsto {U : Set X} (hU : IsOpen U)
    (θ : Fin 3 → ℂ) (N : ℕ) (hN : 0<N) (a : ℕ → Amplitude Smooth)
    (h₀ : normal θ (a 0).1=0)
    (hrec : ∀ j<N,EqOn (fun x => ((normal θ (a (j+1)).1 : Smooth) : X → ℂ) x)
      (fun x => ((-(div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) U)
    (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ)) (hχ : EqOn (χ : X → ℂ) 1 U)
    {g : X → ℂ} (hg : g.HasTemperateGrowth) (hs : tsupport g⊆U)
    {h : ℕ → ℂ} (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n,h n≠0) :
    ∀ i : Fin 4, Tendsto (fun n => physicalAug ((h n)⁻¹ • θ)
      (fun j => mult g (cut χ hc ((truncation (h n) N a).1 j))) i) atTop
      (𝓝 ((Fin.cons (mult g (cut χ hc (a 0).2)+
        ∑ j, mult (fun x => fderiv ℝ g x (e j)) (cut χ hc ((a 0).1 j)))
        (fun j => mult g (cut χ hc ((a 0).1 j))) : Fin 4 → S) i)) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [physicalAug,Fin.cons_zero]
    have he : (fun n => divShift ((h n)⁻¹ • θ)
        (fun j => mult g (cut χ hc ((truncation (h n) N a).1 j))))=
        (fun n => truncation (h n) N (fun j => mult g (cut χ hc (a j).2))+
          h n^N • mult g (cut χ hc (div coord (a N).1-(a N).2))+
          ∑ j, truncation (h n) N (fun k => mult (fun x => fderiv ℝ g x (e j))
            (cut χ hc ((a k).1 j)))) := by
      funext n
      exact formal_scalar_polynomial hU θ N a h₀ hrec χ hc hχ hg hs _ (hne n)
    rw [he]
    have hm := (hh.pow N).smul (tendsto_const_nhds (x := mult g (cut χ hc (div coord (a N).1-(a N).2))))
    simp only [zero_pow hN.ne',zero_smul] at hm
    have hv := tendsto_finsetSum Finset.univ (fun j _ => truncation_tendsto hh N
      (fun k => mult (fun x => fderiv ℝ g x (e j)) (cut χ hc ((a k).1 j))))
    simpa only [add_zero] using ((truncation_tendsto hh N
      (fun k => mult g (cut χ hc (a k).2))).add hm).add hv
  · simp only [physicalAug,Fin.cons_succ]
    simp_rw [mult_cut_truncation_vector]
    exact truncation_tendsto hh N _

/-- A localized actual physical correction with O(h) augmented H_h^1 norm
has every literal augmented L2 component converging strongly to zero. -/
lemma augmented_correction_tendsto {h : ℕ → ℝ} (hh : Tendsto h atTop (𝓝 0))
    (C : ℝ) (u : ℕ → Fin 4 → S) (hu : ∀ n,sobNorm (h n) 1 (u n)≤C*h n) (i : Fin 4) :
    Tendsto (fun n => L2 (u n i)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (norm2_le_sobNorm (h n) (u n) i).trans (hu n))
    (by simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul hh)

end
open Set MeasureTheory Filter
open scoped SchwartzMap Topology BigOperators
open ElasticityAugmented
open ElasticityCoeffBounds (ExteriorConstant)
open ElasticityBessel (L2 norm2)
open ElasticityNegativeOrder (mult sobNorm)
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityPhysicalEstimate (physicalAug)

def localizedFormal (R : ℝ) (hR : 1≤R) (h : ℂ) (a : ℕ → Amplitude Smooth)
    (g : X → ℂ) : Fin 3 → S := fun i => mult g
  (cut ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩ (fiveCutoff_compact R hR 0)
    ((truncation h 8 a).1 i))

def localizedLeading (R : ℝ) (hR : 1≤R) (a : ℕ → Amplitude Smooth)
    (g : X → ℂ) : Fin 4 → S := Fin.cons
  (mult g (cut ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩ (fiveCutoff_compact R hR 0) (a 0).2)+
    ∑ j,mult (fun x => fderiv ℝ g x (e j))
      (cut ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩ (fiveCutoff_compact R hR 0) ((a 0).1 j)))
  (fun j => mult g (cut ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩
    (fiveCutoff_compact R hR 0) ((a 0).1 j)))

/-- Actual shifted physical solutions, bounded in the literal augmented H1
norm, whose augmented L2 error from the formal series is O(h). -/
theorem localized_actual_strong_bound (R : ℝ) (hR : 1≤R) (α β : X)
    (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (a : ℕ → Amplitude Smooth) (ha : PhysicalColumn R hR α β lam m a)
    (h₀ : normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (a 0).1=0)
    (hrec : ∀ j<8,EqOn (fun x => ((normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ))
      (a (j+1)).1 : Smooth) : X → ℂ) x)
      (fun x => ((-(div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) (Metric.ball 0 R))
    {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g⊆Metric.ball 0 R) {B : Set X} (hB : IsOpen B)
    (hBR : B⊆Metric.ball 0 R) (hg1 : EqOn g 1 B) :
    ∃ C D h₁ : ℝ,0<C ∧ 0<D ∧ 0<h₁ ∧ ∀ h : ℝ,0<h → h≤h₁ → ∃ u : Fin 3 → S,
      (∀ i,EqOn (physical (phase h α β) lam m u i : X → ℂ) 0 B) ∧
      sobNorm h 1 (physicalAug (phase h α β) u)≤C ∧
      ∀ i,‖L2 (physicalAug (phase h α β) u i-
        physicalAug (phase h α β) (localizedFormal R hR (h : ℂ) a g) i)‖≤D*h := by
  let χ : Smooth := ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩
  have hcχ : HasCompactSupport (χ : X → ℂ) := fiveCutoff_compact R hR 0
  obtain ⟨A,hA,hformal⟩ := localized_formal_augmented_H1_bound Metric.isOpen_ball
    (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) 8 a h₀ hrec χ hcχ
    (fiveCutoff_initial R hR) (hc.hasTemperateGrowth hg) hs
  obtain ⟨D,h₁,hD,hh₁,hh₁1,hsol⟩ := physical_column_shifted_realization
    R hR α β lam m a ha hg hc hs
  refine ⟨2*(A+D),D,h₁,by linarith only [hA,hD],hD,hh₁,fun h hh hsmall => ?_⟩
  obtain ⟨w,q,v,_hv,hp,_hq,_hw,_hn,hbound⟩ := hsol h hh hsmall
  let F := localizedFormal R hR (h : ℂ) a g
  let V : Fin 3 → S := fun i => mult g (v i)
  let u := F-V
  have hlocal : ∀ j,EqOn (u j : X → ℂ)
      (((fun k => cut χ hcχ ((truncation (h : ℂ) 8 a).1 k))-v) j) B := by
    intro j x hx
    change mult g (cut χ hcχ ((truncation (h : ℂ) 8 a).1 j)) x-mult g (v j) x=_
    simp only [ElasticityNegativeOrder.mult_apply g (hc.hasTemperateGrowth hg),hg1 hx,
      Pi.one_apply,one_mul,Pi.sub_apply,sub_apply]
  refine ⟨u,fun i x hx => (ElasticityPhysicalAlgebra.physical_eqOn_of_eqOn hB _ lam m
    hl.growth hm.growth u _ hlocal i hx).trans (hp i (hBR hx)),?_,fun i => ?_⟩
  · have hh1 : h≤1 := hsmall.trans hh₁1
    have hf := hformal h hh hh1
    rw [← phase_eq] at hf
    change sobNorm h 1 (physicalAug (phase h α β) F)≤A at hf
    change sobNorm h 1 (physicalAug (phase h α β) V)≤D*h at hbound
    change sobNorm h 1 (physicalAug (phase h α β) (F-V))≤_
    rw [ElasticityPhysicalEstimate.physicalAug_sub]
    have hn := sobNorm_sub_four h 1 (physicalAug (phase h α β) F) (physicalAug (phase h α β) V)
    have hDh : D*h≤D := by nlinarith only [hD,hh1]
    linarith only [hn,hf,hbound,hDh]
  · have ht : physicalAug (phase h α β) u i-physicalAug (phase h α β) F i=
        -physicalAug (phase h α β) V i := by
      change physicalAug (phase h α β) (F-V) i-physicalAug (phase h α β) F i=_
      rw [ElasticityPhysicalEstimate.physicalAug_sub]
      simp only [Pi.sub_apply,sub_sub_cancel_left]
    rw [ht,map_neg,norm_neg]
    exact (norm2_le_sobNorm h (physicalAug (phase h α β) V) i).trans hbound

lemma localized_formal_L2_tendsto (R : ℝ) (hR : 1≤R) (α β : X)
    (a : ℕ → Amplitude Smooth)
    (h₀ : normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (a 0).1=0)
    (hrec : ∀ j<8,EqOn (fun x => ((normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ))
      (a (j+1)).1 : Smooth) : X → ℂ) x)
      (fun x => ((-(div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) (Metric.ball 0 R))
    {g : X → ℂ} (hg : g.HasTemperateGrowth) (hs : tsupport g⊆Metric.ball 0 R)
    {h : ℕ → ℝ} (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n,h n≠0) (i : Fin 4) :
    Tendsto (fun n => L2 (physicalAug (phase (h n) α β)
      (localizedFormal R hR (h n : ℂ) a g) i)) atTop
      (𝓝 (L2 (localizedLeading R hR a g i))) := by
  have hh' : Tendsto (fun n => (h n : ℂ)) atTop (𝓝 0) := by
    simpa only [Complex.ofReal_zero,Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp hh
  have ht := formal_augmented_tendsto Metric.isOpen_ball
    (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) 8 (by norm_num) a h₀ hrec
    ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩ (fiveCutoff_compact R hR 0)
    (fiveCutoff_initial R hR) hg hs hh' (fun n => Complex.ofReal_ne_zero.mpr (hne n)) i
  simp_rw [← phase_eq] at ht
  exact L2.continuous.continuousAt.tendsto.comp ht

end ElasticityCGO
namespace ElasticityWeakLimit
open Filter Topology
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Bounded physical amplitudes admit a common weak subsequence in the genuine
Hilbert space. For several columns, take their finite Hilbert product. -/
theorem bounded_weak_subsequence [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (u : ℕ → H) (C : ℝ) (hC : ∀ n, ‖u n‖ ≤ C) :
    ∃ w : H, ‖w‖ ≤ C ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ v : H, Tendsto (fun n => inner ℂ (u (σ n)) v) atTop (𝓝 (inner ℂ w v)) := by
  let f : ℕ → WeakDual ℂ H := fun n => StrongDual.toWeakDual (InnerProductSpace.toDual ℂ H (u n))
  have hf : ∀ n, f n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ H) C := by
    intro n
    simpa only [Set.mem_preimage,Metric.mem_closedBall,dist_zero_right,
      f,StrongDual.toStrongDual_toWeakDual,LinearIsometryEquiv.norm_map] using hC n
  obtain ⟨w,hw,σ,hσ,hlim⟩ := (WeakDual.isSeqCompact_closedBall (𝕜 := ℂ) (E := H) 0 C) hf
  refine ⟨(InnerProductSpace.toDual ℂ H).symm w.toStrongDual,?_,σ,hσ,fun v => ?_⟩
  · simpa only [Set.mem_preimage,Metric.mem_closedBall,dist_zero_right,
      LinearIsometryEquiv.norm_map] using hw
  · have he := (WeakDual.eval_continuous v).tendsto w |>.comp hlim
    rw [InnerProductSpace.toDual_symm_apply]
    exact he

/-- Weak convergence preserves any exact testing identity, including exterior
agreement of the transferred amplitudes. -/
lemma testing_identity {u : ℕ → H} {w : H}
    (hu : ∀ v, Tendsto (fun n => inner ℂ (u n) v) atTop (𝓝 (inner ℂ w v)))
    (v : H) (c : ℂ) (hc : ∀ n, inner ℂ (u n) v=c) : inner ℂ w v=c := by
  have hconst : Tendsto (fun n => inner ℂ (u n) v) atTop (𝓝 c) := by
    simpa only [hc] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c))
  exact tendsto_nhds_unique (hu v) hconst

/-- The lower-order conjugated terms vanish under weak convergence. No
bound on derivatives of the sequence is required: both operators have already
been transposed onto fixed test vectors. -/
lemma asymptotic_testing_identity {u : ℕ → H} {w : H}
    (hu : ∀ v, Tendsto (fun n => inner ℂ (u n) v) atTop (𝓝 (inner ℂ w v)))
    (eps : ℕ → ℂ) (heps : Tendsto eps atTop (𝓝 0)) (v₁ v₂ : H)
    (heq : ∀ n, inner ℂ (u n) v₁+eps n*inner ℂ (u n) v₂=0) :
    inner ℂ w v₁=0 := by
  have hl := (hu v₁).add (heps.mul (hu v₂))
  simp only [zero_mul,add_zero] at hl
  have hz : Tendsto (fun n => inner ℂ (u n) v₁+eps n*inner ℂ (u n) v₂) atTop (𝓝 (0 : ℂ)) := by
    simpa only [heq] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hl hz
end ElasticityWeakLimit
namespace ElasticityWeakLimit
open MeasureTheory TemperedDistribution Filter Topology
open scoped SchwartzMap InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma weak_scalar {u : ℕ → H} {w : H}
    (hu : ∀ v, Tendsto (fun n => inner ℂ (u n) v) atTop (𝓝 (inner ℂ w v)))
    (L : H →L[ℂ] ℂ) : Tendsto (fun n => L (u n)) atTop (𝓝 (L w)) := by
  let v := (InnerProductSpace.toDual ℂ H).symm L
  have he (x : H) : L x=inner ℂ v x := (InnerProductSpace.toDual_symm_apply (y := L) (x := x)).symm
  simp only [he]
  have hh := (continuous_star.tendsto (inner ℂ w v)).comp (hu v)
  change Tendsto (fun n => star (inner ℂ (u n) v)) atTop (𝓝 (star (inner ℂ w v))) at hh
  have hs (a b : H) : star (inner ℂ a b)=inner ℂ b a := inner_conj_symm (𝕜 := ℂ) b a
  simpa only [hs] using hh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma weak_distribution {u : ℕ → H} {w : H}
    (hu : ∀ v, Tendsto (fun n => inner ℂ (u n) v) atTop (𝓝 (inner ℂ w v)))
    (A : H →L[ℂ] 𝓢'(E,ℂ)) (φ : 𝓢(E,ℂ)) :
    Tendsto (fun n => A (u n) φ) atTop (𝓝 (A w φ)) := by
  let L : H →L[ℂ] ℂ := (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp A
  exact weak_scalar hu L

/-- The actual distributional lower-order terms disappear after transposing to
fixed tests. This is the passage used for physical transferred amplitudes. -/
theorem weak_local_equation {u : ℕ → H} {w : H}
    (hu : ∀ v, Tendsto (fun n => inner ℂ (u n) v) atTop (𝓝 (inner ℂ w v)))
    (A B : H →L[ℂ] 𝓢'(E,ℂ)) (Ω : Set E) (eps : ℕ → ℂ)
    (heps : Tendsto eps atTop (𝓝 0))
    (heq : ∀ n, ElasticityRegularity.LocalEqual Ω (A (u n)+eps n • B (u n)) 0) :
    ElasticityRegularity.LocalEqual Ω (A w) 0 := by
  intro φ hc hs
  have hh := (weak_distribution hu A φ).add (heps.mul (weak_distribution hu B φ))
  simp only [zero_mul,add_zero] at hh
  have hz : Tendsto (fun n => A (u n) φ+eps n*B (u n) φ) atTop (𝓝 (0 : ℂ)) := by
    have he (n : ℕ) : A (u n) φ+eps n*B (u n) φ=0 := heq n φ hc hs
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hh hz

lemma weak_local_agreement {u : ℕ → H} {w : H}
    (hu : ∀ v, Tendsto (fun n => inner ℂ (u n) v) atTop (𝓝 (inner ℂ w v)))
    (A : H →L[ℂ] 𝓢'(E,ℂ)) (Ω : Set E) (f : 𝓢'(E,ℂ))
    (heq : ∀ n, ElasticityRegularity.LocalEqual Ω (A (u n)) f) :
    ElasticityRegularity.LocalEqual Ω (A w) f := by
  intro φ hc hs
  have hz : Tendsto (fun n => A (u n) φ) atTop (𝓝 (f φ)) := by
    simpa only [fun n => heq n φ hc hs] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => f φ) atTop (𝓝 (f φ)))
  exact tendsto_nhds_unique (weak_distribution hu A φ) hz
end ElasticityWeakLimit
namespace ElasticityDistribution
open MeasureTheory TemperedDistribution Filter Topology
open scoped SchwartzMap InnerProductSpace
open ElasticityAugmented ElasticityWeakLimit

lemma scaled_null_sum (ε : ℂ) (hε : ε ≠ 0) (a b : Dist) :
    ε • (a+ε⁻¹ • b)=b+ε • a := by
  rw [smul_add,smul_smul,mul_inv_cancel₀ hε,one_smul]
  exact add_comm _ _
lemma complex_smul_zero (ε : ℂ) : ε • (0 : Dist)=0 := by
  exact @smul_zero ℂ Dist _ _ ε

/-- Weak physical transferred amplitudes satisfy the actual constrained leading
system, not an unconstrained augmented transport. -/
theorem weak_physical_leading {U : ℕ → AugHilbert} {W : AugHilbert}
    (hU : ∀ v, Tendsto (fun n => inner ℂ (U n) v) atTop (𝓝 (inner ℂ W v)))
    (Ω : Set X) (eps : ℕ → ℂ) (heps : Tendsto eps atTop (𝓝 0))
    (hne : ∀ n, eps n ≠ 0) (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0)
    (lam m : Coeff)
    (hR : ∀ n i, LocalEq Ω (rd ((eps n)⁻¹ • θ) lam m
      (fun j => (U n j.succ : Dist)) (U n 0 : Dist) i) 0)
    (hS : ∀ n, LocalEq Ω (scd ((eps n)⁻¹ • θ) lam m
      (fun j => (U n j.succ : Dist)) (U n 0 : Dist)) 0)
    (hdiv : ∀ n, LocalEq Ω (divd ((eps n)⁻¹ • θ) (fun j => (U n j.succ : Dist)))
      (U n 0 : Dist)) :
    (∀ i, LocalEq Ω (leadingRd θ lam m (fun j => (W j.succ : Dist)) (W 0 : Dist) i) 0) ∧
    LocalEq Ω (leadingSd θ lam m (fun j => (W j.succ : Dist)) (W 0 : Dist)) 0 ∧
    LocalEq Ω (normald θ (fun j => (W j.succ : Dist))) 0 := by
  refine ⟨fun i => ?_,?_,?_⟩
  · have hh := weak_local_equation hU (leadingRCLM θ lam m i) (rdCLM 0 lam m i) Ω eps heps
    simp only [leadingRCLM_apply,rdCLM_apply] at hh
    apply hh
    intro n
    have h := (hR n i).smul (eps n)
    rw [rd_null_expansion θ hθ] at h
    rw [scaled_null_sum _ (hne n),complex_smul_zero] at h
    exact h
  · have hh := weak_local_equation hU (leadingSCLM θ lam m) (scdCLM 0 lam m) Ω eps heps
    simp only [leadingSCLM_apply,scdCLM_apply] at hh
    apply hh
    intro n
    have h := (hS n).smul (eps n)
    rw [scd_null_expansion θ hθ] at h
    rw [scaled_null_sum _ (hne n),complex_smul_zero] at h
    exact h
  · have hh := weak_local_equation hU (normalCLM θ) (divergenceCLM 0-augEntry 0) Ω eps heps
    simp only [normalCLM_apply,sub_apply,divergenceCLM_apply,augEntry_apply] at hh
    apply hh
    intro n
    have h := ((hdiv n).sub (LocalEq.refl (U n 0 : Dist))).smul (eps n)
    rw [divergence_phase] at h
    have he (a b c : Dist) : eps n • (a+(eps n)⁻¹ • b-c)=b+eps n • (a-c) := by
      rw [smul_sub,smul_add,smul_smul,mul_inv_cancel₀ (hne n),one_smul,smul_sub]
      abel
    rw [he,sub_self,complex_smul_zero] at h
    exact h
end ElasticityDistribution
section
open MeasureTheory TemperedDistribution Filter Topology
open scoped SchwartzMap InnerProductSpace ENNReal
namespace ElasticityWeakLimit
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exterior data need only converge in distributions. In particular, this
retains the finite-amplitude and correction terms of the physical CGO sequence
until after the weak limit, rather than replacing them by their leading value. -/
theorem weak_moving_local_agreement {u : ℕ → H} {w : H}
    (hu : ∀ v, Tendsto (fun n => inner ℂ (u n) v) atTop (𝓝 (inner ℂ w v)))
    (A : H →L[ℂ] 𝓢'(E,ℂ)) (Ω : Set E) (f : ℕ → 𝓢'(E,ℂ)) (g : 𝓢'(E,ℂ))
    (hf : ∀ φ, Tendsto (fun n => f n φ) atTop (𝓝 (g φ)))
    (heq : ∀ n, ElasticityRegularity.LocalEqual Ω (A (u n)) (f n)) :
    ElasticityRegularity.LocalEqual Ω (A w) g := by
  intro φ hc hs
  have htest (n : ℕ) : A (u n) φ=f n φ := heq n φ hc hs
  have ht : Tendsto (fun n => A (u n) φ) atTop (𝓝 (g φ)) := by
    simpa only [htest] using hf φ
  exact tendsto_nhds_unique (weak_distribution hu A φ) ht
end ElasticityWeakLimit

namespace ElasticityDistribution
open ElasticityAugmented ElasticityWeakLimit

/-- Actual coefficientwise physical equations survive bounded weak extraction,
including the divergence constraint and the varying physical exterior data.
The bound is a premise here: deriving it from the DN transfer and its compact
Carleman estimate remains separate and is not identified with the main theorem. -/
theorem bounded_physical_limit
    (U : ℕ → AugHilbert) (C : ℝ) (hbound : ∀ n, ‖U n‖≤C)
    (Ω E : Set X) (eps : ℕ → ℂ) (heps : Tendsto eps atTop (𝓝 0))
    (hne : ∀ n,eps n≠0) (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0)
    (lam m : Coeff)
    (hR : ∀ n i,LocalEq Ω (rd ((eps n)⁻¹ • θ) lam m
      (fun j => (U n j.succ : Dist)) (U n 0 : Dist) i) 0)
    (hS : ∀ n,LocalEq Ω (scd ((eps n)⁻¹ • θ) lam m
      (fun j => (U n j.succ : Dist)) (U n 0 : Dist)) 0)
    (hdiv : ∀ n,LocalEq Ω (divd ((eps n)⁻¹ • θ) (fun j => (U n j.succ : Dist)))
      (U n 0 : Dist))
    (F : ℕ → Fin 4 → Dist) (a : Fin 4 → Dist)
    (hF : ∀ i φ,Tendsto (fun n => F n i φ) atTop (𝓝 (a i φ)))
    (hext : ∀ n i,LocalEq E (U n i : Dist) (F n i)) :
    ∃ W : AugHilbert,‖W‖≤C ∧
      (∀ i,LocalEq Ω (leadingRd θ lam m (fun j => (W j.succ : Dist)) (W 0 : Dist) i) 0) ∧
      LocalEq Ω (leadingSd θ lam m (fun j => (W j.succ : Dist)) (W 0 : Dist)) 0 ∧
      LocalEq Ω (normald θ (fun j => (W j.succ : Dist))) 0 ∧
      (∀ i,LocalEq E (W i : Dist) (a i)) ∧
      ∃ σ : ℕ → ℕ,StrictMono σ ∧
        ∀ v,Tendsto (fun n => inner ℂ (U (σ n)) v) atTop (𝓝 (inner ℂ W v)) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have : TopologicalSpace.SeparableSpace (Lp ℂ 2 (volume : Measure X)) := inferInstance
  have : TopologicalSpace.SeparableSpace AugHilbert := inferInstance
  obtain ⟨W,hW,σ,hσ,hw⟩ := bounded_weak_subsequence U C hbound
  have ht := hσ.tendsto_atTop
  obtain ⟨hr,hs,hd⟩ := weak_physical_leading hw Ω (fun n => eps (σ n))
    (heps.comp ht) (fun n => hne (σ n)) θ hθ lam m
    (fun n => hR (σ n)) (fun n => hS (σ n)) (fun n => hdiv (σ n))
  refine ⟨W,hW,hr,hs,hd,fun i => ?_,σ,hσ,hw⟩
  have he := weak_moving_local_agreement hw (augEntry i) E (fun n => F (σ n) i) (a i)
    (fun φ => (hF i φ).comp ht) (fun n => hext (σ n) i)
  exact he
end ElasticityDistribution

end
namespace ElasticityDistribution

section
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap BigOperators
open ElasticityAugmented
open ElasticityCGO (augEmbed)
open ElasticityPhysicalEstimate (physicalAug)

lemma augEmbed_distribution (u : Fin 4 → SchwartzMap X ℂ) (i : Fin 4) :
    (augEmbed u i : Dist)=(u i : Dist) :=
  Lp.toTemperedDistribution_toLp_eq (u i)

/-- The scalar entry of the actual augmented amplitude is its actual physical
shifted divergence. Both physical equations, including the scalar consequence,
are thereby inherited by the same L2 object used in weak extraction. -/
theorem actual_augmented_equations {B : Set X} (z : Fin 3 → ℂ) (lam m : Coeff)
    (u : Fin 3 → SchwartzMap X ℂ)
    (hu : ∀ i,EqOn (ElasticityPhysicalAlgebra.physical z (eval lam) (eval m) u i : X → ℂ) 0 B) :
    let U := augEmbed (physicalAug z u)
    (∀ i,LocalEq B (rd z lam m (fun j => (U j.succ : Dist)) (U 0 : Dist) i) 0) ∧
    LocalEq B (scd z lam m (fun j => (U j.succ : Dist)) (U 0 : Dist)) 0 ∧
    LocalEq B (divd z (fun j => (U j.succ : Dist))) (U 0 : Dist) := by
  intro U
  have he (i : Fin 3) : (U i.succ : Dist)=(u i : Dist) := augEmbed_distribution _ _
  have hd : (U 0 : Dist)=divd z (fun i => (u i : Dist)) := by
    rw [augEmbed_distribution,divd_schwartz]
    rfl
  simp only [he,hd]
  have hp (i) : LocalEq B (phys z lam m (fun j => (u j : Dist)) i) 0 := by
    rw [phys_schwartz]
    have hh := Elasticity.localEq_of_schwartz_eqOn (F := ElasticityPhysicalAlgebra.physical z
      (eval lam) (eval m) u i) (G := 0) (hu i)
    simpa only [map_zero] using hh
  refine ⟨fun i => ?_,?_,LocalEq.refl _⟩
  · rw [← physical_expansion]
    exact hp i
  · rw [← physical_divergence]
    have hh := LocalEq.divergence hp z
    simpa only [divd,map_zero,Finset.sum_const_zero] using hh

lemma actual_augmented_exterior {K : Set X} (z : Fin 3 → ℂ)
    (u v : Fin 3 → SchwartzMap X ℂ)
    (hs : ∀ i,tsupport (v i-u i : SchwartzMap X ℂ)⊆K) :
    ∀ i,LocalEq Kᶜ (augEmbed (physicalAug z v) i : Dist) (augEmbed (physicalAug z u) i : Dist) := by
  have hh (j : Fin 3) : LocalEq Kᶜ (v j : Dist) (u j : Dist) := by
    apply Elasticity.localEq_of_schwartz_eqOn
    intro x hx
    have hz : (v j-u j) x=0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (hs j hh))
    exact sub_eq_zero.mp hz
  intro i
  simp only [augEmbed_distribution]
  refine Fin.cases ?_ (fun j => hh j) i
  change LocalEq Kᶜ (ElasticityPhysicalAlgebra.divShift z v : Dist)
    (ElasticityPhysicalAlgebra.divShift z u : Dist)
  have hd := LocalEq.divergence hh z
  simpa only [divd_schwartz,ElasticityPhysicalAlgebra.divShift] using hd

end
open Set Filter MeasureTheory TemperedDistribution
open scoped SchwartzMap Topology BigOperators
open ElasticityAugmented
open ElasticityCGO (augEmbed)
open ElasticityBessel (L2)
open ElasticityPhysicalEstimate (physicalAug)
open ElasticityPhysicalAlgebra (phase physical)

/-- Weak transport extraction for the literal transferred physical sequence.
The exterior leading value follows from strong convergence of the actual
source augmented amplitudes, not from dropping CGO remainders by definition. -/
theorem actual_transferred_limit (B K : Set X) (α β : X)
    (hθ : ∑ i,((α i : ℂ)+Complex.I*(β i : ℂ))*((α i : ℂ)+Complex.I*(β i : ℂ))=0)
    (lam m : Coeff) (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n,h n≠0)
    (u v : ℕ → Fin 3 → SchwartzMap X ℂ) (a : Fin 4 → SchwartzMap X ℂ)
    (hv : ∀ n i,EqOn (physical (phase (h n) α β) (eval lam) (eval m) (v n) i : X → ℂ) 0 B)
    (hs : ∀ n i,tsupport (v n i-u n i : SchwartzMap X ℂ)⊆K)
    (C : ℝ) (hC : ∀ n,‖augEmbed (physicalAug (phase (h n) α β) (v n))‖≤C)
    (ha : ∀ i,Tendsto (fun n => L2 (physicalAug (phase (h n) α β) (u n) i)) atTop (𝓝 (L2 (a i)))) :
    ∃ W : AugHilbert,
      (∀ i,LocalEq B (leadingRd (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) lam m
        (fun j => (W j.succ : Dist)) (W 0 : Dist) i) 0) ∧
      LocalEq B (leadingSd (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) lam m
        (fun j => (W j.succ : Dist)) (W 0 : Dist)) 0 ∧
      LocalEq B (normald (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (fun j => (W j.succ : Dist))) 0 ∧
      ∀ i,LocalEq Kᶜ (W i : Dist) (a i : Dist) := by
  let U := fun n => augEmbed (physicalAug (phase (h n) α β) (v n))
  have hh' : Tendsto (fun n => (h n : ℂ)) atTop (𝓝 0) := by
    simpa only [Complex.ofReal_zero,Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hh
  have heq (n) := actual_augmented_equations (phase (h n) α β) lam m (v n) (hv n)
  have hF (i : Fin 4) (φ : 𝓢(X,ℂ)) :
      Tendsto (fun n => (augEmbed (physicalAug (phase (h n) α β) (u n)) i : Dist) φ)
        atTop (𝓝 ((a i : Dist) φ)) := by
    let A : Lp ℂ 2 (volume : Measure X) →L[ℂ] ℂ :=
      (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp
        (Lp.toTemperedDistributionCLM ℂ (volume : Measure X) 2)
    have ht := A.continuous.continuousAt.tendsto.comp (ha i)
    simp only [A,Function.comp_def,ContinuousLinearMap.comp_apply,
      PointwiseConvergenceCLM.evalCLM_apply,Lp.toTemperedDistributionCLM_apply,
      ElasticityCGO.augEmbed_apply,ElasticityBessel.L2,SchwartzMap.toLpCLM_apply,
      Lp.toTemperedDistribution_toLp_eq] at ht ⊢
    exact ht
  obtain ⟨W,_hW,hr,hs',hn,hext,_hseq⟩ := bounded_physical_limit U C hC B Kᶜ
    (fun n => (h n : ℂ)) hh' (fun n => Complex.ofReal_ne_zero.mpr (hne n)) _ hθ lam m
    (fun n i => by simpa only [← ElasticityCGO.phase_eq] using (heq n).1 i)
    (fun n => by simpa only [← ElasticityCGO.phase_eq] using (heq n).2.1)
    (fun n => by simpa only [← ElasticityCGO.phase_eq] using (heq n).2.2)
    (fun n i => (augEmbed (physicalAug (phase (h n) α β) (u n)) i : Dist))
    (fun i => (a i : Dist)) hF (fun n => actual_augmented_exterior _ (u n) (v n) (hs n))
  exact ⟨W,hr,hs',hn,hext⟩

end ElasticityDistribution
namespace ElasticitySequences
open Filter
open scoped Topology
lemma small_sequence {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    ∃ h : ℕ → ℝ,Tendsto h atTop (𝓝 0) ∧ (∀ n,0<h n) ∧
      (∀ n,h n≤a) ∧ (∀ n,h n≤b) := by
  let c := min a b
  have hc : 0<c := lt_min ha hb
  let h := fun n : ℕ => c*((n+1 : ℝ)⁻¹)
  have hh : Tendsto h atTop (𝓝 0) := by
    simpa only [h,one_div,mul_zero] using
      tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) atTop (𝓝 0))
  have hpos (n) : 0<h n := mul_pos hc (inv_pos.mpr (by positivity))
  have hle (n) : h n≤c := by
    change c*((n+1 : ℝ)⁻¹)≤c
    apply mul_le_of_le_one_right hc.le
    exact inv_le_one_of_one_le₀ (by have hn : (0 : ℝ)≤(n : ℝ) := Nat.cast_nonneg n; linarith)
  exact ⟨h,hh,hpos,fun n => (hle n).trans (min_le_left a b),
    fun n => (hle n).trans (min_le_right a b)⟩
lemma tendsto_of_error {E : Type*} [NormedAddCommGroup E]
    {u f : ℕ → E} {a : E} {h : ℕ → ℝ} {C : ℝ}
    (hf : Tendsto f atTop (𝓝 a)) (hh : Tendsto h atTop (𝓝 0))
    (he : ∀ n,‖u n-f n‖≤C*h n) : Tendsto u atTop (𝓝 a) := by
  have hn : Tendsto (fun n => ‖u n-f n‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) he (by simpa using tendsto_const_nhds.mul hh)
  have hz : Tendsto (fun n => u n-f n) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hn
  simpa only [sub_add_cancel,zero_add] using hz.add hf
end ElasticitySequences
namespace Elasticity
open Set MeasureTheory Filter TemperedDistribution
open scoped BigOperators SchwartzMap Topology
open ElasticityAugmented
open ElasticityCoeffBounds (ExteriorConstant)
open ElasticityDistribution (Coeff Dist LocalEq AugHilbert leadingRd leadingSd normald)
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityPhysicalEstimate (physicalAug)
open ElasticityNegativeOrder (sobNorm)
open ElasticityCGO

/-- A genuine physical DN transfer yields a bounded weak leading transport
column with the actual exterior leading value. Every bound and equation is
derived from the physical CGO construction and the compact comparison. -/
theorem dn_weak_transport_column {Ω B B' : Set X}
    (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω) (hB : IsOpen B)
    (hBB : Bornology.IsBounded B) (hB' : IsOpen B') (hsub : B'⊆B) (hcl : closure Ω⊆B')
    (R : ℝ) (hR : 1≤R) (hKR : closure Ω⊆Metric.closedBall 0 R)
    (hBR : B⊆Metric.ball 0 R) (α β : X) (hα : α≠0)
    (hθ : ∑ i,((α i : ℂ)+Complex.I*(β i : ℂ))*((α i : ℂ)+Complex.I*(β i : ℂ))=0)
    (lam m : Fin 2 → X → ℝ)
    (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
    (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
    (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
    (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
    (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
    (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1))
    (χ g η : Smooth) (hcχ : HasCompactSupport (χ : X → ℂ))
    (hc : HasCompactSupport (g : X → ℂ)) (hs : tsupport (g : X → ℂ)⊆B)
    (hχ : EqOn (χ : X → ℂ) 1 B) (hg : EqOn (g : X → ℂ) 1 B')
    (hcη : HasCompactSupport (η : X → ℂ)) (hsη : tsupport (η : X → ℂ)⊆Metric.ball 0 R)
    (hη : EqOn (η : X → ℂ) 1 B)
    (a : ℕ → Amplitude Smooth)
    (ha : PhysicalColumn R hR α β (smoothOfReal (lam 0) (hl 0)) (smoothOfReal (m 0) (hm 0)) a)
    (h₀ : normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (a 0).1=0)
    (hrec : ∀ j<8,EqOn (fun x => ((normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ))
      (a (j+1)).1 : Smooth) : X → ℂ) x)
      (fun x => ((-(ElasticityAugmented.div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) (Metric.ball 0 R)) :
    let L : Coeff := ⟨smoothOfReal (lam 1) (hl 1),(hcll 1).growth⟩
    let M : Coeff := ⟨smoothOfReal (m 1) (hm 1),(hclm 1).growth⟩
    let θ := fun i => (α i : ℂ)+Complex.I*(β i : ℂ)
    ∃ W : AugHilbert,
      (∀ i,LocalEq B' (leadingRd θ L M (fun j => (W j.succ : Dist)) (W 0 : Dist) i) 0) ∧
      LocalEq B' (leadingSd θ L M (fun j => (W j.succ : Dist)) (W 0 : Dist)) 0 ∧
      LocalEq B' (normald θ (fun j => (W j.succ : Dist))) 0 ∧
      ∀ i,LocalEq (closure Ω)ᶜ (W i : Dist) (localizedLeading R hR a η i : Dist) := by
  intro L M θ
  obtain ⟨C,D,h₀',hC,hD,hh₀,hsource⟩ := localized_actual_strong_bound R hR α β
    (smoothOfReal (lam 0) (hl 0)) (smoothOfReal (m 0) (hm 0)) (hcll 0) (hclm 0)
    a ha h₀ hrec (smooth_coe η) hcη hsη hB hBR hη
  obtain ⟨A,h₁,hA,hh₁,htransfer⟩ := extended_dn_compact_comparison hΩ hOB hB hBB hB' hsub hcl
    R hR hKR α β hα lam m hl hm hp hcll hclm he hDN χ g hcχ hc hs hχ hg
  obtain ⟨h,hh,hpos,hle₀,hle₁⟩ := ElasticitySequences.small_sequence hh₀ hh₁
  choose u hu hub hue using fun n => hsource (h n) (hpos n) (hle₀ n)
  choose v hvs hv hvb using fun n => htransfer (h n) (hpos n) (hle₁ n) (u n) (hu n)
  have bound (n) : ‖augEmbed (physicalAug (phase (h n) α β) (v n))‖≤(A+1)*C := by
    have hd : augEmbed (physicalAug (phase (h n) α β) (v n-u n))=
        augEmbed (physicalAug (phase (h n) α β) (v n))-
          augEmbed (physicalAug (phase (h n) α β) (u n)) := by
      rw [ElasticityPhysicalEstimate.physicalAug_sub,map_sub]
    have hhU := (norm_augEmbed_le (h n) (physicalAug (phase (h n) α β) (u n))).trans (hub n)
    have hhV := (norm_augEmbed_le (h n) (physicalAug (phase (h n) α β) (v n-u n))).trans (hvb n)
    rw [hd] at hhV
    have hAC := mul_le_mul_of_nonneg_left (hub n) hA.le
    have hn := norm_sub_norm_le (augEmbed (physicalAug (phase (h n) α β) (v n)))
      (augEmbed (physicalAug (phase (h n) α β) (u n)))
    nlinarith only [hhU,hhV,hAC,hn]
  have strong (i : Fin 4) : Tendsto
      (fun n => ElasticityBessel.L2 (physicalAug (phase (h n) α β) (u n) i)) atTop
      (𝓝 (ElasticityBessel.L2 (localizedLeading R hR a η i))) := by
    apply ElasticitySequences.tendsto_of_error
      (localized_formal_L2_tendsto R hR α β a h₀ hrec (hcη.hasTemperateGrowth (smooth_coe η))
        hsη hh (fun n => (hpos n).ne') i) hh
    intro n
    simpa only [map_sub] using hue n i
  exact ElasticityDistribution.actual_transferred_limit B' (closure Ω) α β hθ L M h hh
    (fun n => (hpos n).ne') u v (localizedLeading R hR a η) hv hvs ((A+1)*C) bound strong
end Elasticity
namespace ElasticitySlicing
/-! Measure-theoretic core of transverse slicing: a single exceptional null
set for all planar tests, obtained using the separable L2 value/derivative graph,
not an invalid interchange of an uncountable intersection with almost-everywhere. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {T E F : Type*} [MeasurableSpace T] {μ : Measure T}
    [TopologicalSpace E] [SecondCountableTopology E]
    [TopologicalSpace F] [T2Space F] [Zero F]

lemma ae_all_on_of_continuous (s : Set E) (f : T → E → F)
    (hc : ∀ᵐ t ∂μ, Continuous (f t))
    (hz : ∀ x∈s, ∀ᵐ t ∂μ, f t x=0) :
    ∀ᵐ t ∂μ, ∀ x∈s, f t x=0 := by
  obtain ⟨d,hd,hdd⟩ := TopologicalSpace.exists_countable_dense s
  have hz' : ∀ᵐ t ∂μ, ∀ x∈d, f t (x:E)=0 := by
    rw [ae_ball_iff hd]
    exact fun x _ => hz x x.property
  filter_upwards [hc,hz'] with t hct hzt
  have hs : closure d ⊆ {x : s | f t x=0} :=
    closure_minimal hzt (isClosed_eq (hct.comp continuous_subtype_val) continuous_const)
  intro x hx
  exact hs (hdd ⟨x,hx⟩)

variable {A B G : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup G]
    {ν : Measure A} {κ : Measure B} [SFinite ν] [SFinite κ]

/-- An honest L2 function on the cylinder has L2 planar slices a.e. -/
lemma memLp_two_slices {u : A × B → G} (hu : MemLp u 2 (ν.prod κ)) :
    ∀ᵐ t ∂ν, MemLp (fun z => u (t,z)) 2 κ := by
  have hn := hu.integrable_norm_rpow (by norm_num) (by norm_num)
  filter_upwards [hu.aestronglyMeasurable.prodMk_left,hn.prod_right_ae] with t ht hnt
  exact (integrable_norm_rpow_iff ht (by norm_num : (2:ℝ≥0∞)≠0)
    (by norm_num : (2:ℝ≥0∞)≠⊤)).mp hnt

end ElasticitySlicing
namespace ElasticityGeneralSlicing
/-! Actual transverse slicing of weak planar equations. All planar tests share
one exceptional null set. No uncountable a.e. intersection is used. -/
open Set MeasureTheory Filter
open scoped SchwartzMap ENNReal InnerProductSpace
open ElasticitySlicing
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
    [Measure.IsAddHaarMeasure (volume : Measure P)]
open ElasticityPlanar

abbrev PL2 := Lp ℂ 2 (volume : Measure ℂ)
def sliceLp (u : P × ℂ → ℂ) (t : P) : PL2 :=
  by classical exact if h : MemLp (fun z => u (t,z)) 2 volume then h.toLp _ else 0
omit [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)] in
lemma sliceLp_coe {u : P × ℂ → ℂ} {t : P}
    (h : MemLp (fun z => u (t,z)) 2 volume) :
    (sliceLp u t : ℂ → ℂ)=ᵐ[volume] fun z => u (t,z) := by
  simp only [sliceLp,dite_eq_left h]
  exact h.coeFn_toLp

def testDbar (φ : Test) : Test := d (1:ℂ) φ+Complex.I • d Complex.I φ

def testGraph (φ : Test) : PL2 × PL2 := (L2 (cj φ),L2 (cj (testDbar φ)))

def slicePair (u w : P × ℂ → ℂ) (t : P) (q : PL2 × PL2) : ℂ :=
  inner ℂ q.1 (sliceLp w t)-inner ℂ q.2 (sliceLp u t)

omit [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)] in
lemma slicePair_continuous (u w : P × ℂ → ℂ) (t : P) :
    Continuous (slicePair u w t) := by
  exact (continuous_fst.inner continuous_const).sub (continuous_snd.inner continuous_const)

lemma L2_test_integral {w : ℂ → ℂ} (hw : MemLp w 2 volume) (φ : Test) :
    inner ℂ (L2 (cj φ)) (hw.toLp w)=∫ z, φ z*w z := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(toSchwartz (cj φ)).coeFn_toLp 2 volume,hw.coeFn_toLp] with z hz hwz
  change (L2 (cj φ) : ℂ → ℂ) z=cj φ z at hz
  rw [hz,hwz]
  simp only [cj_apply,RCLike.inner_apply',starRingEnd_apply,star_star,mul_comm]

omit [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)] in
lemma slicePair_graph {u w : P × ℂ → ℂ} {t : P}
    (hu : MemLp (fun z => u (t,z)) 2 volume)
    (hw : MemLp (fun z => w (t,z)) 2 volume) (φ : Test) :
    slicePair u w t (testGraph φ)=
      (∫ z, φ z*w (t,z))-(∫ z, testDbar φ z*u (t,z)) := by
  simp only [slicePair,testGraph,sliceLp,dite_eq_left hu,dite_eq_left hw,L2_test_integral]

omit [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [Measure.IsAddHaarMeasure (volume : Measure P)] in
lemma test_mul_integrable {w : P × ℂ → ℂ} (hw : Integrable w) (φ : Test) :
    Integrable (fun q : P × ℂ => φ q.2*w q) := by
  apply hw.bdd_mul ((toSchwartz φ).continuous.comp continuous_snd).aestronglyMeasurable
  exact Eventually.of_forall (fun q => (toSchwartz φ).norm_le_seminorm ℝ q.2)

/-- Fubini plus the fundamental lemma first gives a null set for one test. -/
lemma single_test_slice {u w : P × ℂ → ℂ}
    (hu : Integrable u) (hw : Integrable w) (φ : Test)
    (he : ∀ (η : P → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∫ q : P × ℂ, η q.1 • (φ q.2*w q-testDbar φ q.2*u q))=0) :
    ∀ᵐ t : P, ∫ z : ℂ, φ z*w (t,z)-testDbar φ z*u (t,z)=0 := by
  have hi := (test_mul_integrable hw φ).sub (test_mul_integrable hu (testDbar φ))
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hi.integral_prod_left.locallyIntegrable
  intro η hη hcη
  obtain ⟨C,hC⟩ := (hcη.isCompact_range hη.continuous).isBounded.exists_norm_le
  have hηi : Integrable (fun q : P × ℂ => η q.1 •
      (φ q.2*w q-testDbar φ q.2*u q)) :=
    hi.bdd_smul C (hη.continuous.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall (fun q => hC (η q.1) (mem_range_self q.1)))
  have hh := he η hη hcη
  change (∫ q : P × ℂ, η q.1 • (φ q.2*w q-testDbar φ q.2*u q)
    ∂(volume : Measure P).prod (volume : Measure ℂ))=0 at hh
  rw [integral_prod _ hηi] at hh
  simpa only [integral_smul,Pi.sub_apply] using hh

/-- The weak cylinder equation genuinely determines the planar weak equation
on a single full-measure subset of transverse parameters. -/
theorem weak_slice_from_product_tests {u w : P × ℂ → ℂ}
    (hu : Integrable u) (hw : Integrable w)
    (hu2 : MemLp u 2 volume) (hw2 : MemLp w 2 volume)
    (he : ∀ (η : P → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      ∀ φ : Test, (∫ q : P × ℂ,
        η q.1 • (φ q.2*w q-testDbar φ q.2*u q))=0) :
    ∀ᵐ t : P, MemLp (fun z => u (t,z)) 2 volume ∧
      MemLp (fun z => w (t,z)) 2 volume ∧
      ∀ φ : Test, (∫ z, φ z*w (t,z))=(∫ z, testDbar φ z*u (t,z)) := by
  have : Fact ((2 : ℝ≥0∞)≠⊤) := ⟨by norm_num⟩
  have hu' := memLp_two_slices (ν := (volume : Measure P)) (κ := (volume : Measure ℂ)) hu2
  have hw' := memLp_two_slices (ν := (volume : Measure P)) (κ := (volume : Measure ℂ)) hw2
  have hg : ∀ q∈range testGraph, ∀ᵐ t : P, slicePair u w t q=0 := by
    rintro q ⟨φ,rfl⟩
    have hzero := single_test_slice hu hw φ (fun η hη hcη => he η hη hcη φ)
    filter_upwards [hu',hw',hzero,(test_mul_integrable hw φ).prod_right_ae,
      (test_mul_integrable hu (testDbar φ)).prod_right_ae] with t hut hwt hzt h1 h2
    rw [slicePair_graph hut hwt,← integral_sub h1 h2]
    exact hzt
  have hcount := ae_all_on_of_continuous (range testGraph) (slicePair u w)
    (Eventually.of_forall (slicePair_continuous u w)) hg
  filter_upwards [hu',hw',hcount] with t hut hwt ht
  refine ⟨hut,hwt,fun φ => ?_⟩
  exact sub_eq_zero.mp ((slicePair_graph hut hwt φ).symm.trans (ht _ (mem_range_self φ)))

end ElasticityGeneralSlicing
namespace ElasticityGeneralSlicing
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv
open ElasticitySlicing
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
    [Measure.IsAddHaarMeasure (volume : Measure P)]
open ElasticityPlanar

instance cylinder_temperate : (volume : Measure (P × ℂ)).HasTemperateGrowth := by
  change ((volume : Measure P).prod (volume : Measure ℂ)).HasTemperateGrowth
  infer_instance

omit [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)] in
lemma compact_product_test (η : P → ℝ) (hcη : HasCompactSupport η) (φ : Test) :
    HasCompactSupport (fun q : P × ℂ => (η q.1 : ℂ)*φ q.2) := by
  apply HasCompactSupport.intro (hcη.prod (compact φ))
  intro q hq
  by_cases ht : q.1∈tsupport η
  · have hz : q.2∉tsupport (φ : ℂ → ℂ) := fun hz => hq ⟨ht,hz⟩
    rw [image_eq_zero_of_notMem_tsupport hz,mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport ht,Complex.ofReal_zero,zero_mul]

def productTest (η : P → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hcη : HasCompactSupport η) (φ : Test) : 𝓢(P × ℂ,ℂ) :=
  (compact_product_test η hcη φ).toSchwartzMap
    ((Complex.ofRealCLM.contDiff.comp (hη.comp contDiff_fst)).mul
      ((smooth φ).comp contDiff_snd))

omit [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
  [Measure.IsAddHaarMeasure (volume : Measure P)] in
lemma productTest_apply (η : P → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hcη : HasCompactSupport η) (φ : Test) (q : P × ℂ) :
    productTest η hη hcη φ q=(η q.1 : ℂ)*φ q.2 := rfl

omit [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
  [Measure.IsAddHaarMeasure (volume : Measure P)] in
lemma productTest_deriv (η : P → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hcη : HasCompactSupport η) (φ : Test) (v : ℂ) :
    ∂_{((0:P),v)} (productTest η hη hcη φ)=productTest η hη hcη (d v φ) := by
  ext q
  change fderiv ℝ (fun q : P × ℂ => (η q.1 : ℂ)*φ q.2) q (0,v)=
    (η q.1 : ℂ)*fderiv ℝ (φ : ℂ → ℂ) q.2 v
  have hηd := (Complex.ofRealCLM.contDiff.comp hη).differentiable (by simp)
  have hφd := (smooth φ).differentiable (by simp)
  have ha : DifferentiableAt ℝ (fun q : P × ℂ => (η q.1 : ℂ)) q :=
    (hηd.comp differentiable_fst) q
  have hb : DifferentiableAt ℝ (fun q : P × ℂ => φ q.2) q :=
    (hφd.comp differentiable_snd) q
  rw [fderiv_fun_mul ha hb]
  have hfa := fderiv_comp q (hηd q.1) (differentiableAt_fst (p := q))
  have hfb := fderiv_comp q (hφd q.2) (differentiableAt_snd (p := q))
  change fderiv ℝ (fun q : P × ℂ => (η q.1 : ℂ)) q = _ at hfa
  change fderiv ℝ (fun q : P × ℂ => φ q.2) q = _ at hfb
  rw [hfa,hfb]
  simp [fderiv_fst,fderiv_snd,smul_eq_mul]

omit [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
  [Measure.IsAddHaarMeasure (volume : Measure P)] in
lemma productTest_add (η : P → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hcη : HasCompactSupport η) (φ ψ : Test) :
    productTest η hη hcη (φ+ψ)=productTest η hη hcη φ+productTest η hη hcη ψ := by
  ext q
  change (η q.1 : ℂ)*(φ q.2+ψ q.2)=_
  exact mul_add _ _ _
omit [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
  [Measure.IsAddHaarMeasure (volume : Measure P)] in
lemma productTest_smul (η : P → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hcη : HasCompactSupport η) (c : ℂ) (φ : Test) :
    productTest η hη hcη (c • φ)=c • productTest η hη hcη φ := by
  ext q
  change (η q.1 : ℂ)*(c*φ q.2)=c*((η q.1 : ℂ)*φ q.2)
  ring
omit [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
  [Measure.IsAddHaarMeasure (volume : Measure P)] in
lemma productTest_dbar (η : P → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hcη : HasCompactSupport η) (φ : Test) :
    ∂_{((0:P),(1:ℂ))} (productTest η hη hcη φ)+
      Complex.I • ∂_{((0:P),Complex.I)} (productTest η hη hcη φ)=
      productTest η hη hcη (testDbar φ) := by
  simp only [testDbar,productTest_add,productTest_smul,productTest_deriv]

/-- The product-test premise of slicing is not an axiom: it follows from the
actual distributional cylinder equation by an exact directional derivative. -/
theorem cylinder_product_tests (u w : Lp ℂ 2 (volume : Measure (P × ℂ)))
    (hu : Integrable (u : P × ℂ → ℂ)) (hw : Integrable (w : P × ℂ → ℂ))
    (he : ∂_{((0:P),(1:ℂ))} (u : 𝓢'(P × ℂ,ℂ))+
      Complex.I • ∂_{((0:P),Complex.I)} (u : 𝓢'(P × ℂ,ℂ))+(w : 𝓢'(P × ℂ,ℂ))=0)
    (η : P → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η) (φ : Test) :
    (∫ q : P × ℂ, η q.1 • (φ q.2*w q-testDbar φ q.2*u q))=0 := by
  have hh := congrArg (fun D : 𝓢'(P × ℂ,ℂ) => D (productTest η hη hcη φ)) he
  have htest : (w : 𝓢'(P × ℂ,ℂ)) (productTest η hη hcη φ)=
      (u : 𝓢'(P × ℂ,ℂ)) (productTest η hη hcη (testDbar φ)) := by
    rw [← productTest_dbar]
    simp only [add_apply,smul_apply,TemperedDistribution.lineDerivOp_apply_apply,
      map_neg,zero_apply,smul_eq_mul] at hh
    simp only [map_add,map_smul,smul_eq_mul]
    linear_combination hh
  simp only [Lp.toTemperedDistribution_apply,productTest_apply,smul_eq_mul] at htest
  obtain ⟨C,hC⟩ := (hcη.isCompact_range hη.continuous).isBounded.exists_norm_le
  have hi (f : P × ℂ → ℂ) (hf : Integrable f) (ψ : Test) :
      Integrable (fun q : P × ℂ => (η q.1 : ℂ)*(ψ q.2*f q)) := by
    apply (test_mul_integrable hf ψ).bdd_mul (c := C)
      (Complex.continuous_ofReal.comp (hη.continuous.comp continuous_fst)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun q => by simpa only [Function.comp_apply,Complex.norm_real] using hC (η q.1) (mem_range_self q.1))
  have hrew : (fun q : P × ℂ => η q.1 • (φ q.2*w q-testDbar φ q.2*u q))=
      (fun q => (η q.1 : ℂ)*(φ q.2*w q))-(fun q => (η q.1 : ℂ)*(testDbar φ q.2*u q)) := by
    funext q
    simp only [Pi.sub_apply,Complex.real_smul,mul_sub]
  rw [hrew]
  change (∫ q : P × ℂ, (η q.1 : ℂ)*(φ q.2*w q)-(η q.1 : ℂ)*(testDbar φ q.2*u q))=0
  rw [integral_sub (hi w hw φ) (hi u hu (testDbar φ)),sub_eq_zero]
  simpa only [mul_assoc] using htest

/-- Actual weak distribution solutions on the cylinder slice to planar
solutions for every compact smooth test on one full-measure parameter set. -/
theorem cylinder_weak_slices (u w : Lp ℂ 2 (volume : Measure (P × ℂ)))
    (hu : Integrable (u : P × ℂ → ℂ)) (hw : Integrable (w : P × ℂ → ℂ))
    (he : ∂_{((0:P),(1:ℂ))} (u : 𝓢'(P × ℂ,ℂ))+
      Complex.I • ∂_{((0:P),Complex.I)} (u : 𝓢'(P × ℂ,ℂ))+(w : 𝓢'(P × ℂ,ℂ))=0) :
    ∀ᵐ t : P, MemLp (fun z => u (t,z)) 2 volume ∧
      MemLp (fun z => w (t,z)) 2 volume ∧
      ∀ φ : Test, (∫ z, φ z*w (t,z))=(∫ z, testDbar φ z*u (t,z)) :=
  weak_slice_from_product_tests hu hw (Lp.memLp u) (Lp.memLp w)
    (cylinder_product_tests u w hu hw he)

end ElasticityGeneralSlicing

end

end OAI
