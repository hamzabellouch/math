import Mathlib
import OAI.Geometry.CubicTorus.Estimates.BVBallCalibration

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma chainPullback_contDiff (l : VariationChain) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : ContDiff ℝ (⊤ : ℕ∞) (chainPullback l F) := by
  induction l with
  | nil => exact hF
  | cons p l ih => rcases p with ⟨a,t⟩; exact coordinatePullback_contDiff a.coordinate a.smooth t ih

lemma chainPullback_periodic (l : VariationChain) {F : Cover → Cover}
    (hF : ∀ n x,F (x+latticeVector n)=F x) :
    ∀ n x,chainPullback l F (x+latticeVector n)=chainPullback l F x := by
  induction l with
  | nil => exact hF
  | cons p l ih => rcases p with ⟨a,t⟩; exact coordinatePullback_periodic a.coordinate a.periodic t ih

lemma chainPullback_norm (l : VariationChain) {F : Cover → Cover} (hF : ∀ x,‖F x‖≤1) :
    ∀ x,‖chainPullback l F x‖≤chainBound l := by
  induction l with
  | nil => exact hF
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    exact coordinatePullback_norm_le_mul a.coordinate a.bound.coe_nonneg
      (fun x ↦ by exact_mod_cast a.derivative_bound x) t (chainBound_pos l) ih

lemma chainPullback_divergence (l : VariationChain) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (chainPullback l F) x = chainJacobian l x * divergence F (chainMove l x) := by
  induction l generalizing x with
  | nil => simp [chainPullback,chainJacobian,chainMove]
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    rw [chainPullback,coordinatePullback_divergence a.coordinate a.smooth t (chainPullback_contDiff l hF),ih]
    simp only [chainJacobian,chainMove,mul_assoc]

lemma chain_inner_pullback (l : VariationChain) (F : Cover → Cover) (x n : Cover) :
    ⟪n,chainPullback l F x⟫=⟪chainCofactor l x n,F (chainMove l x)⟫ := by
  induction l generalizing x n with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    rw [chainPullback,inner_coordinatePullback,ih]
    rfl

lemma chainRegion_measurable {l : VariationChain} (hl : ChainValid l)
    {E : Set Torus} (hE : MeasurableSet E) : MeasurableSet (chainRegion l E) := by
  induction l generalizing E with
  | nil => exact hE
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    exact ih (fun p hp ↦ hl p (by simp [hp]))
      (measurableSet_coordinateRegion a.coordinate (a.smooth.differentiable (by simp))
        a.derivative_bound (hl (a,t) (by simp)) hE)

lemma chainRegion_finite {l : VariationChain} (hl : ChainValid l)
    {E : Set Torus} (hE : MeasurableSet E) (hfin : perimeter E<⊤) : FinitePerimeter (chainRegion l E) := by
  induction l generalizing E with
  | nil => exact ⟨hE.nullMeasurableSet,hfin⟩
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    have ht := hl (a,t) (by simp)
    exact ih (fun p hp ↦ hl p (by simp [hp]))
      (measurableSet_coordinateRegion a.coordinate (a.smooth.differentiable (by simp)) a.derivative_bound ht hE)
      (finitePerimeter_coordinateRegion a.coordinate a.smooth a.periodic a.derivative_bound a.faces ht hE hfin.ne).2

lemma integral_chainRegion {l : VariationChain} (hl : ChainValid l)
    {E : Set Torus} (hE : MeasurableSet E) (g : Cover → ℝ) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' chainRegion l E,g x)=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,chainJacobian l x*g (chainMove l x) := by
  induction l generalizing E with
  | nil => simp [chainRegion,chainJacobian,chainMove]
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    have ht := hl (a,t) (by simp)
    rw [chainRegion,ih (fun p hp ↦ hl p (by simp [hp]))
      (measurableSet_coordinateRegion a.coordinate (a.smooth.differentiable (by simp)) a.derivative_bound ht hE),
      integral_coordinateRegion a.coordinate (a.smooth.differentiable (by simp)) a.derivative_bound a.faces ht hE]
    simp only [chainJacobian,chainMove,mul_assoc]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma wallVelocity_contDiff (a : WallVariation) : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : Cover×Cover ↦ coordinateNormalVelocity a.coordinate a.function p.1 p.2) := by
  unfold coordinateNormalVelocity
  exact (((a.smooth.fderiv_right (by simp)).comp contDiff_fst).clm_apply contDiff_const).smul contDiff_snd |>.sub
    ((contDiff_snd.inner ℝ contDiff_const).smul ((gradient_contDiff a.smooth).comp contDiff_fst))

lemma chainCofactor_contDiff (l : VariationChain) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Cover×Cover ↦ chainCofactor l p.1 p.2) := by
  induction l with
  | nil => exact contDiff_snd
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun p : Cover×Cover ↦
        coordinateCofactor a.coordinate a.function t p.1 p.2) := by
      simp only [coordinateCofactor_eq]
      exact contDiff_snd.add (contDiff_const.fun_smul (wallVelocity_contDiff a))
    exact ih.comp (((coordinateMove_contDiff a.coordinate a.smooth t).comp contDiff_fst).prodMk hc)

lemma chainCofactor_continuous_normal (l : VariationChain) :
    Continuous (fun z : NormalBundle ↦ chainCofactor l z.1 z.2) :=
  (chainCofactor_contDiff l).continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))

theorem perimeter_chainRegion_le_normalArea {l : VariationChain} (hl : ChainValid l)
    {E : Set Torus} (hE : MeasurableSet E) {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) : perimeter (chainRegion l E)≤ENNReal.ofReal
      (∫ z,‖chainCofactor l z.1 z.2‖ ∂(μ : Measure NormalBundle)) := by
  unfold perimeter
  refine iSup_le fun F ↦ iSup_le fun hF ↦ ?_
  have hΓ := chainPullback_contDiff l hF.1
  have hflux := normalMeasure_flux hμ hΓ (chainPullback_periodic l hF.2.1)
    (chainBound_pos l) (chainPullback_norm l hF.2.2)
  rw [integral_chainRegion hl hE]
  simp_rw [← chainPullback_divergence l hF.1]
  rw [← hflux]
  apply ENNReal.ofReal_le_ofReal
  apply integral_mono
  · exact (normalTest _ hΓ.continuous).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (chainCofactor_continuous_normal l).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · intro z
    change ⟪(z.2 : Cover),chainPullback l F z.1⟫≤_
    rw [chain_inner_pullback]
    exact (real_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hF.2.2 _))

lemma chainMove_append (l k : VariationChain) (x : Cover) :
    chainMove (l++k) x=chainMove k (chainMove l x) := by
  induction l generalizing x with
  | nil => rfl
  | cons p l ih => rcases p with ⟨a,t⟩; exact ih _

lemma chainJacobian_append (l k : VariationChain) (x : Cover) :
    chainJacobian (l++k) x=chainJacobian l x*chainJacobian k (chainMove l x) := by
  induction l generalizing x with
  | nil => simp [chainJacobian,chainMove]
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    simp only [List.cons_append,chainJacobian,chainMove,ih,mul_assoc]

lemma chainCofactor_append (l k : VariationChain) (x n : Cover) :
    chainCofactor (l++k) x n=chainCofactor k (chainMove l x) (chainCofactor l x n) := by
  induction l generalizing x n with
  | nil => rfl
  | cons p l ih => rcases p with ⟨a,t⟩; exact ih _ _

lemma chainRegion_append (l k : VariationChain) (E : Set Torus) :
    chainRegion (l++k) E=chainRegion k (chainRegion l E) := by
  induction l generalizing E with
  | nil => rfl
  | cons p l ih => rcases p with ⟨a,t⟩; exact ih _

lemma ChainValid.append {l k : VariationChain} (hl : ChainValid l) (hk : ChainValid k) :
    ChainValid (l++k) := by
  intro p hp
  rcases List.mem_append.mp hp with hp|hp
  · exact hl p hp
  · exact hk p hp

def chainMass (l : VariationChain) (E : Set Torus) : ℝ :=
  ∫ x in fundamentalCube∩quotientMap ⁻¹' E,chainJacobian l x

lemma volume_chainRegion {l : VariationChain} (hl : ChainValid l)
    {E : Set Torus} (hE : MeasurableSet E) : torusVolume.real (chainRegion l E)=chainMass l E := by
  rw [realVolume_lift (chainRegion_measurable hl hE)]
  rw [← setIntegral_one_eq_measureReal]
  change (∫ x in fundamentalCube∩quotientMap ⁻¹' chainRegion l E,(1 : ℝ))=_
  rw [integral_chainRegion hl hE]
  simp only [mul_one,chainMass]

def chainTransportedFlux (l : VariationChain) (b : WallVariation) (E : Set Torus) : ℝ :=
  ∫ x in fundamentalCube∩quotientMap ⁻¹' E,
    chainJacobian l x*fderiv ℝ b.function (chainMove l x) (EuclideanSpace.single b.coordinate 1)

lemma integrableOn_fundamentalCube_of_continuous {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Cover → F} (hf : Continuous f) : IntegrableOn f fundamentalCube :=
  (hf.continuousOn.integrableOn_compact isCompact_closedFundamentalCube).mono_set
    (fun x hx ↦ ⟨WithLp.ofLp x,⟨fun i ↦ (hx i).1,fun i ↦ (hx i).2.le⟩,rfl⟩)

lemma chainMass_append (l : VariationChain) (b : WallVariation) (s : ℝ) (E : Set Torus) :
    chainMass (l++[(b,s)]) E=chainMass l E+s*chainTransportedFlux l b E := by
  have hJ := integrableOn_fundamentalCube_of_continuous (chainJacobian_contDiff l).continuous
  have hB : IntegrableOn (fun x ↦ chainJacobian l x*
      fderiv ℝ b.function (chainMove l x) (EuclideanSpace.single b.coordinate 1)) fundamentalCube :=
    integrableOn_fundamentalCube_of_continuous
    ((chainJacobian_contDiff l).continuous.mul
      ((((b.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).comp (chainMove_contDiff l).continuous)))
  unfold chainMass chainTransportedFlux
  simp only [chainJacobian_append,chainJacobian,coordinateJacobian,mul_one]
  simp_rw [mul_add,mul_one,show ∀ x : Cover,chainJacobian l x*(s*
      fderiv ℝ b.function (chainMove l x) (EuclideanSpace.single b.coordinate 1))=
      s*(chainJacobian l x*fderiv ℝ b.function (chainMove l x) (EuclideanSpace.single b.coordinate 1)) from fun x ↦ by ring]
  rw [integral_add (hJ.mono_set inter_subset_left) ((hB.mono_set inter_subset_left).const_mul s),integral_const_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

lemma wallVelocity_contDiff (a : Variation) : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : Cover×Cover ↦ coordinateNormalVelocity a.coordinate a.function p.1 p.2) := by
  unfold coordinateNormalVelocity
  exact (((a.smooth.fderiv_right (by simp)).comp contDiff_fst).clm_apply contDiff_const).smul contDiff_snd |>.sub
    ((contDiff_snd.inner ℝ contDiff_const).smul ((gradient_contDiff a.smooth).comp contDiff_fst))

lemma chainCofactor_contDiff (l : VariationChain) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Cover×Cover ↦ chainCofactor l p.1 p.2) := by
  induction l with
  | nil => exact contDiff_snd
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun p : Cover×Cover ↦
        coordinateCofactor a.coordinate a.function t p.1 p.2) := by
      simp only [coordinateCofactor_eq]
      exact contDiff_snd.add (contDiff_const.fun_smul (wallVelocity_contDiff a))
    exact ih.comp (((coordinateMove_contDiff a.coordinate a.smooth t).comp contDiff_fst).prodMk hc)

lemma chainCofactor_continuous_normal (l : VariationChain) :
    Continuous (fun z : NormalBundle ↦ chainCofactor l z.1 z.2) :=
  (chainCofactor_contDiff l).continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))

theorem perimeter_chainRegion_le_normalArea {l : VariationChain} (hl : ChainValid l)
    {E : Set Torus} (hE : MeasurableSet E) {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) : perimeter (chainRegion l E)≤ENNReal.ofReal
      (∫ z,‖chainCofactor l z.1 z.2‖ ∂(μ : Measure NormalBundle)) := by
  unfold perimeter
  refine iSup_le fun F ↦ iSup_le fun hF ↦ ?_
  have hΓ := chainPullback_contDiff l hF.1
  have hflux := normalMeasure_flux hμ hΓ (chainPullback_periodic l hF.2.1)
    (chainBound_pos l) (chainPullback_norm l hF.2.2)
  rw [integral_chainRegion hl hE (divergence_periodic hF.2.1)]
  simp_rw [← chainPullback_divergence l hF.1]
  rw [← hflux]
  apply ENNReal.ofReal_le_ofReal
  apply integral_mono
  · exact (normalTest _ hΓ.continuous).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (chainCofactor_continuous_normal l).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · intro z
    change ⟪(z.2 : Cover),chainPullback l F z.1⟫≤_
    rw [chain_inner_pullback]
    exact (real_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hF.2.2 _))

lemma chainMove_append (l k : VariationChain) (x : Cover) :
    chainMove (l++k) x=chainMove k (chainMove l x) := by
  induction l generalizing x with
  | nil => rfl
  | cons p l ih => rcases p with ⟨a,t⟩; exact ih _

lemma chainJacobian_append (l k : VariationChain) (x : Cover) :
    chainJacobian (l++k) x=chainJacobian l x*chainJacobian k (chainMove l x) := by
  induction l generalizing x with
  | nil => simp [chainJacobian,chainMove]
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    simp only [List.cons_append,chainJacobian,chainMove,ih,mul_assoc]

lemma chainCofactor_append (l k : VariationChain) (x n : Cover) :
    chainCofactor (l++k) x n=chainCofactor k (chainMove l x) (chainCofactor l x n) := by
  induction l generalizing x n with
  | nil => rfl
  | cons p l ih => rcases p with ⟨a,t⟩; exact ih _ _

lemma chainRegion_append (l k : VariationChain) (E : Set Torus) :
    chainRegion (l++k) E=chainRegion k (chainRegion l E) := by
  induction l generalizing E with
  | nil => rfl
  | cons p l ih => rcases p with ⟨a,t⟩; exact ih _

lemma ChainValid.append {l k : VariationChain} (hl : ChainValid l) (hk : ChainValid k) :
    ChainValid (l++k) := by
  intro p hp
  rcases List.mem_append.mp hp with hp|hp
  · exact hl p hp
  · exact hk p hp

def chainMass (l : VariationChain) (E : Set Torus) : ℝ :=
  ∫ x in fundamentalCube∩quotientMap ⁻¹' E,chainJacobian l x

lemma volume_chainRegion {l : VariationChain} (hl : ChainValid l)
    {E : Set Torus} (hE : MeasurableSet E) : torusVolume.real (chainRegion l E)=chainMass l E := by
  rw [realVolume_lift (chainRegion_measurable hl hE)]
  rw [← setIntegral_one_eq_measureReal]
  change (∫ x in fundamentalCube∩quotientMap ⁻¹' chainRegion l E,(1 : ℝ))=_
  rw [integral_chainRegion hl hE (fun _ _ ↦ rfl)]
  simp only [mul_one,chainMass]

def chainTransportedFlux (l : VariationChain) (b : Variation) (E : Set Torus) : ℝ :=
  ∫ x in fundamentalCube∩quotientMap ⁻¹' E,
    chainJacobian l x*fderiv ℝ b.function (chainMove l x) (EuclideanSpace.single b.coordinate 1)

lemma chainMass_append (l : VariationChain) (b : Variation) (s : ℝ) (E : Set Torus) :
    chainMass (l++[(b,s)]) E=chainMass l E+s*chainTransportedFlux l b E := by
  have hJ := integrableOn_fundamentalCube_of_continuous (chainJacobian_contDiff l).continuous
  have hB : IntegrableOn (fun x ↦ chainJacobian l x*
      fderiv ℝ b.function (chainMove l x) (EuclideanSpace.single b.coordinate 1)) fundamentalCube :=
    integrableOn_fundamentalCube_of_continuous
    ((chainJacobian_contDiff l).continuous.mul
      ((((b.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).comp (chainMove_contDiff l).continuous)))
  unfold chainMass chainTransportedFlux
  simp only [chainJacobian_append,chainJacobian,coordinateJacobian,mul_one]
  simp_rw [mul_add,mul_one,show ∀ x : Cover,chainJacobian l x*(s*
      fderiv ℝ b.function (chainMove l x) (EuclideanSpace.single b.coordinate 1))=
      s*(chainJacobian l x*fderiv ℝ b.function (chainMove l x) (EuclideanSpace.single b.coordinate 1)) from fun x ↦ by ring]
  rw [integral_add (hJ.mono_set inter_subset_left) ((hB.mono_set inter_subset_left).const_mul s),integral_const_mul]

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

def simultaneousChain (l : List Variation) (t : ℝ) : VariationChain := l.map (fun a ↦ (a,t))

lemma simultaneousMove_smooth (l : List Variation) : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : ℝ×Cover ↦ chainMove (simultaneousChain l p.1) p.2) := by
  induction l with
  | nil => exact contDiff_snd
  | cons a l ih =>
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×Cover ↦ coordinateMove a.coordinate a.function p.1 p.2) := by
      unfold coordinateMove
      exact contDiff_snd.add ((contDiff_fst.mul (a.smooth.comp contDiff_snd)).smul contDiff_const)
    exact ih.comp (contDiff_fst.prodMk hm)

lemma simultaneousJacobian_smooth (l : List Variation) : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : ℝ×Cover ↦ chainJacobian (simultaneousChain l p.1) p.2) := by
  induction l with
  | nil => exact contDiff_const
  | cons a l ih =>
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×Cover ↦ coordinateMove a.coordinate a.function p.1 p.2) := by
      unfold coordinateMove
      exact contDiff_snd.add ((contDiff_fst.mul (a.smooth.comp contDiff_snd)).smul contDiff_const)
    have hJ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×Cover ↦ coordinateJacobian a.coordinate a.function p.1 p.2) := by
      unfold coordinateJacobian
      exact contDiff_const.add (contDiff_fst.mul (((a.smooth.fderiv_right (by simp)).comp contDiff_snd).clm_apply contDiff_const))
    exact hJ.mul (ih.comp (contDiff_fst.prodMk hm))

lemma simultaneousCofactor_smooth (l : List Variation) : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : ℝ×(Cover×Cover) ↦ chainCofactor (simultaneousChain l p.1) p.2.1 p.2.2) := by
  induction l with
  | nil => exact contDiff_snd.snd
  | cons a l ih =>
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×(Cover×Cover) ↦ coordinateMove a.coordinate a.function p.1 p.2.1) := by
      unfold coordinateMove
      exact contDiff_snd.fst.add ((contDiff_fst.mul (a.smooth.comp contDiff_snd.fst)).smul contDiff_const)
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×(Cover×Cover) ↦ coordinateCofactor a.coordinate a.function p.1 p.2.1 p.2.2) := by
      simp only [coordinateCofactor_eq]
      exact contDiff_snd.snd.add (contDiff_fst.fun_smul ((wallVelocity_contDiff a).comp contDiff_snd))
    exact ih.comp (contDiff_fst.prodMk (hm.prodMk hc))

@[simp] lemma simultaneousMove_zero (l : List Variation) (x : Cover) :
    chainMove (simultaneousChain l 0) x=x := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih => simpa [simultaneousChain,chainMove,coordinateMove] using ih x

@[simp] lemma simultaneousJacobian_zero (l : List Variation) (x : Cover) :
    chainJacobian (simultaneousChain l 0) x=1 := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih => simpa [simultaneousChain,chainJacobian,coordinateJacobian,coordinateMove] using ih x

@[simp] lemma simultaneousCofactor_zero (l : List Variation) (x n : Cover) :
    chainCofactor (simultaneousChain l 0) x n=n := by
  induction l generalizing x n with
  | nil => rfl
  | cons a l ih => simpa [simultaneousChain,chainCofactor,coordinateCofactor_eq,coordinateMove] using ih x n

lemma simultaneousChain_eventually_valid (l : List Variation) :
    ∀ᶠ t in 𝓝 (0 : ℝ),ChainValid (simultaneousChain l t) := by
  induction l with
  | nil => exact Eventually.of_forall fun _ p hp ↦ by simp [simultaneousChain] at hp
  | cons a l ih =>
    have ha : ∀ᶠ t in 𝓝 (0 : ℝ),|t| *(a.bound : ℝ)<1 :=
      (continuous_abs.mul continuous_const).continuousAt.eventually (eventually_lt_nhds (by simp))
    filter_upwards [ih,ha] with t ht hat
    intro p hp
    simp only [simultaneousChain,List.map_cons,List.mem_cons] at hp
    rcases hp with rfl|hp
    · exact hat
    · exact ht p hp

@[simp] lemma simultaneousMass_zero (l : List Variation) {E : Set Torus} (hE : MeasurableSet E) :
    chainMass (simultaneousChain l 0) E=torusVolume.real E := by
  simp only [chainMass,simultaneousJacobian_zero,setIntegral_one_eq_measureReal]
  exact (realVolume_lift hE).symm

@[simp] lemma simultaneousFlux_zero (l : List Variation) (b : Variation) (E : Set Torus) :
    chainTransportedFlux (simultaneousChain l 0) b E=directionalFlux E b.coordinate b.function := by
  simp [chainTransportedFlux,directionalFlux]

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def simultaneousChain (l : List WallVariation) (t : ℝ) : VariationChain := l.map (fun a ↦ (a,t))

lemma simultaneousMove_smooth (l : List WallVariation) : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : ℝ×Cover ↦ chainMove (simultaneousChain l p.1) p.2) := by
  induction l with
  | nil => exact contDiff_snd
  | cons a l ih =>
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×Cover ↦ coordinateMove a.coordinate a.function p.1 p.2) := by
      unfold coordinateMove
      exact contDiff_snd.add ((contDiff_fst.mul (a.smooth.comp contDiff_snd)).smul contDiff_const)
    exact ih.comp (contDiff_fst.prodMk hm)

lemma simultaneousJacobian_smooth (l : List WallVariation) : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : ℝ×Cover ↦ chainJacobian (simultaneousChain l p.1) p.2) := by
  induction l with
  | nil => exact contDiff_const
  | cons a l ih =>
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×Cover ↦ coordinateMove a.coordinate a.function p.1 p.2) := by
      unfold coordinateMove
      exact contDiff_snd.add ((contDiff_fst.mul (a.smooth.comp contDiff_snd)).smul contDiff_const)
    have hJ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×Cover ↦ coordinateJacobian a.coordinate a.function p.1 p.2) := by
      unfold coordinateJacobian
      exact contDiff_const.add (contDiff_fst.mul (((a.smooth.fderiv_right (by simp)).comp contDiff_snd).clm_apply contDiff_const))
    exact hJ.mul (ih.comp (contDiff_fst.prodMk hm))

lemma simultaneousCofactor_smooth (l : List WallVariation) : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : ℝ×(Cover×Cover) ↦ chainCofactor (simultaneousChain l p.1) p.2.1 p.2.2) := by
  induction l with
  | nil => exact contDiff_snd.snd
  | cons a l ih =>
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×(Cover×Cover) ↦ coordinateMove a.coordinate a.function p.1 p.2.1) := by
      unfold coordinateMove
      exact contDiff_snd.fst.add ((contDiff_fst.mul (a.smooth.comp contDiff_snd.fst)).smul contDiff_const)
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×(Cover×Cover) ↦ coordinateCofactor a.coordinate a.function p.1 p.2.1 p.2.2) := by
      simp only [coordinateCofactor_eq]
      exact contDiff_snd.snd.add (contDiff_fst.fun_smul ((wallVelocity_contDiff a).comp contDiff_snd))
    exact ih.comp (contDiff_fst.prodMk (hm.prodMk hc))

@[simp] lemma simultaneousMove_zero (l : List WallVariation) (x : Cover) :
    chainMove (simultaneousChain l 0) x=x := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih => simpa [simultaneousChain,chainMove,coordinateMove] using ih x

@[simp] lemma simultaneousJacobian_zero (l : List WallVariation) (x : Cover) :
    chainJacobian (simultaneousChain l 0) x=1 := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih => simpa [simultaneousChain,chainJacobian,coordinateJacobian,coordinateMove] using ih x

@[simp] lemma simultaneousCofactor_zero (l : List WallVariation) (x n : Cover) :
    chainCofactor (simultaneousChain l 0) x n=n := by
  induction l generalizing x n with
  | nil => rfl
  | cons a l ih => simpa [simultaneousChain,chainCofactor,coordinateCofactor_eq,coordinateMove] using ih x n

lemma simultaneousChain_eventually_valid (l : List WallVariation) :
    ∀ᶠ t in 𝓝 (0 : ℝ),ChainValid (simultaneousChain l t) := by
  induction l with
  | nil => exact Eventually.of_forall fun _ p hp ↦ by simp [simultaneousChain] at hp
  | cons a l ih =>
    have ha : ∀ᶠ t in 𝓝 (0 : ℝ),|t| *(a.bound : ℝ)<1 :=
      (continuous_abs.mul continuous_const).continuousAt.eventually (eventually_lt_nhds (by simp))
    filter_upwards [ih,ha] with t ht hat
    intro p hp
    simp only [simultaneousChain,List.map_cons,List.mem_cons] at hp
    rcases hp with rfl|hp
    · exact hat
    · exact ht p hp

@[simp] lemma simultaneousMass_zero (l : List WallVariation) {E : Set Torus} (hE : MeasurableSet E) :
    chainMass (simultaneousChain l 0) E=torusVolume.real E := by
  simp only [chainMass,simultaneousJacobian_zero,setIntegral_one_eq_measureReal]
  exact (realVolume_lift hE).symm

@[simp] lemma simultaneousFlux_zero (l : List WallVariation) (b : WallVariation) (E : Set Torus) :
    chainTransportedFlux (simultaneousChain l 0) b E=directionalFlux E b.coordinate b.function := by
  simp [chainTransportedFlux,directionalFlux]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicTorus

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {μ : Measure X} [IsFiniteMeasure μ]

omit [NormedSpace ℝ X] [SecondCountableTopology X] [NormedSpace ℝ E] [CompleteSpace E] in
lemma integrable_of_continuous_compact_carrier
    [NormedSpace ℝ X] [SecondCountableTopology X] [NormedSpace ℝ E] [CompleteSpace E]
    {K : Set X} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ,x∈K) {f : X → E} (hf : Continuous f) : Integrable f μ := by
  have h := hf.continuousOn.integrableOn_compact hK (μ := μ)
  rwa [IntegrableOn,Measure.restrict_eq_self_of_ae_mem hμ] at h

lemma hasDerivAt_compact_parameter_integral {K : Set X} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ,x∈K) {F : ℝ×X → E} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (t : ℝ) :
    HasDerivAt (fun t ↦ ∫ x,F (t,x) ∂μ)
      (∫ x,fderiv ℝ F (t,x) (1,0) ∂μ) t := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×X ↦ fderiv ℝ F p (1,0)) :=
    (hF.fderiv_right (by simp)).clm_apply contDiff_const
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (f := fun p : ℝ×X ↦ fderiv ℝ F p (1,0)) hd.continuous.continuousOn
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Icc (t-1) (t+1)) (bound := fun _ : X ↦ M)
    (Icc_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun s ↦ (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (integrable_of_continuous_compact_carrier hK hμ (hF.continuous.comp (continuous_const.prodMk continuous_id)))
    ((hd.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (hμ.mono fun x hx s hs ↦ hM (s,x) ⟨hs,hx⟩)
    (integrable_const M) ?_).2
  exact Eventually.of_forall fun x s _ ↦
    (hF.differentiable (by simp) (s,x)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))

theorem contDiff_compact_parameter_integral {K : Set X} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ,x∈K) {F : ℝ×X → E} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ ∫ x,F (t,x) ∂μ) := by
  have hfinite : ∀ n : ℕ,∀ F : ℝ×X → E,ContDiff ℝ (⊤ : ℕ∞) F →
      ContDiff ℝ n (fun t ↦ ∫ x,F (t,x) ∂μ) := by
    intro n
    induction n with
    | zero =>
      intro F hF
      exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun t ↦
        (hasDerivAt_compact_parameter_integral hK hμ hF t).continuousAt)
    | succ n ih =>
      intro F hF
      have hd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×X ↦ fderiv ℝ F p (1,0)) :=
        (hF.fderiv_right (by simp)).clm_apply contDiff_const
      rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_deriv]
      refine ⟨fun t ↦ (hasDerivAt_compact_parameter_integral hK hμ hF t).differentiableAt,by simp,?_⟩
      have heq : deriv (fun t ↦ ∫ x,F (t,x) ∂μ)=(fun t ↦ ∫ x,fderiv ℝ F (t,x) (1,0) ∂μ) :=
        funext fun t ↦ (hasDerivAt_compact_parameter_integral hK hμ hF t).deriv
      rw [heq]
      exact ih _ hd
  exact contDiff_infty.mpr fun n ↦ hfinite n F hF

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cubeIntersection_compact_carrier (E : Set Torus) :
    ∀ᵐ x ∂(volume.restrict (fundamentalCube∩quotientMap ⁻¹' E)),x∈closedFundamentalCube := by
  have hh := ae_restrict_mem measurableSet_fundamentalCube (μ := (volume : Measure Cover))
  have hh' := ae_restrict_of_ae_restrict_of_subset (t := fundamentalCube)
    (s := fundamentalCube∩quotientMap ⁻¹' E) inter_subset_left hh
  exact hh'.mono fun x hx ↦ ⟨WithLp.ofLp x,⟨fun i ↦ (hx i).1,fun i ↦ (hx i).2.le⟩,rfl⟩

lemma simultaneousMass_smooth (l : List WallVariation) (E : Set Torus) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ chainMass (simultaneousChain l t) E) :=
  contDiff_compact_parameter_integral isCompact_closedFundamentalCube
    (cubeIntersection_compact_carrier E) (simultaneousJacobian_smooth l)

lemma simultaneousFlux_smooth (l : List WallVariation) (b : WallVariation) (E : Set Torus) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ chainTransportedFlux (simultaneousChain l t) b E) := by
  exact contDiff_compact_parameter_integral isCompact_closedFundamentalCube (cubeIntersection_compact_carrier E)
    (F := fun p : ℝ×Cover ↦ chainJacobian (simultaneousChain l p.1) p.2 *
      fderiv ℝ b.function (chainMove (simultaneousChain l p.1) p.2) (EuclideanSpace.single b.coordinate 1))
    ((simultaneousJacobian_smooth l).mul
    (((b.smooth.fderiv_right (by simp)).clm_apply contDiff_const).comp (simultaneousMove_smooth l)))

lemma smooth_quotient_extension {f g : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (h0 : g 0≠0) :
    ∃ q : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) q ∧ q =ᶠ[𝓝 0] (fun t ↦ f t/g t) := by
  let S : Set ℝ := {t | g t≠0}
  have hS : IsOpen S := isOpen_ne.preimage hg.continuous
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds h0)
  let η : ContDiffBump (0 : ℝ) := ⟨r/4,r/2,by positivity,by linarith⟩
  have hsupp : tsupport η⊆S := by
    rw [η.tsupport_eq]
    intro t ht
    exact hsub (show dist t 0<r from lt_of_le_of_lt ht (by change r/2<r; linarith))
  refine ⟨fun t ↦ η t*(f t/g t),?_,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : t∈tsupport η
    · exact η.contDiff.contDiffAt.mul (hf.contDiffAt.div hg.contDiffAt (hsupp ht))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ht] with s hs
      simp [hs]
  · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) η.rIn_pos] with t ht
    rw [η.one_of_mem_closedBall (Metric.ball_subset_closedBall ht),one_mul]

def chainCorrection (l : List WallVariation) (b : WallVariation) (E : Set Torus) (t : ℝ) : ℝ :=
  (torusVolume.real E-chainMass (simultaneousChain l t) E)/chainTransportedFlux (simultaneousChain l t) b E

lemma chainCorrection_zero (l : List WallVariation) (b : WallVariation)
    {E : Set Torus} (hE : MeasurableSet E) : chainCorrection l b E 0=0 := by
  simp [chainCorrection,simultaneousMass_zero l hE]

lemma chainCorrection_eventually_exact (l : List WallVariation) (b : WallVariation)
    {E : Set Torus} (hE : MeasurableSet E) (hB : directionalFlux E b.coordinate b.function≠0) :
    ∀ᶠ t in 𝓝 (0 : ℝ),ChainValid (simultaneousChain l t++[(b,chainCorrection l b E t)]) ∧
      torusVolume (chainRegion (simultaneousChain l t++[(b,chainCorrection l b E t)]) E)=torusVolume E := by
  have hden : chainTransportedFlux (simultaneousChain l 0) b E≠0 := by simpa
  have hc : ContinuousAt (chainCorrection l b E) 0 :=
    (continuousAt_const.sub (simultaneousMass_smooth l E).continuous.continuousAt).div
      (simultaneousFlux_smooth l b E).continuous.continuousAt hden
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ),|chainCorrection l b E t| *(b.bound : ℝ)<1 :=
    (hc.abs.mul_const _).eventually (eventually_lt_nhds (by simp [chainCorrection_zero l b hE]))
  have hne : ∀ᶠ t in 𝓝 (0 : ℝ),chainTransportedFlux (simultaneousChain l t) b E≠0 :=
    (simultaneousFlux_smooth l b E).continuous.continuousAt.eventually_ne hden
  filter_upwards [simultaneousChain_eventually_valid l,hsmall,hne] with t ht hbt hnt
  have hv : ChainValid (simultaneousChain l t++[(b,chainCorrection l b E t)]) :=
    ht.append (by intro p hp; obtain rfl := List.mem_singleton.mp hp; exact hbt)
  refine ⟨hv,?_⟩
  apply ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _) |>.mp
  rw [show (torusVolume (chainRegion _ E)).toReal=torusVolume.real (chainRegion _ E) from rfl,
    volume_chainRegion hv hE,chainMass_append]
  unfold chainCorrection
  rw [div_mul_cancel₀ _ hnt]
  dsimp only [Measure.real]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

lemma simultaneousMass_smooth (l : List Variation) (E : Set Torus) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ chainMass (simultaneousChain l t) E) :=
  contDiff_compact_parameter_integral isCompact_closedFundamentalCube
    (cubeIntersection_compact_carrier E) (simultaneousJacobian_smooth l)

lemma simultaneousFlux_smooth (l : List Variation) (b : Variation) (E : Set Torus) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ chainTransportedFlux (simultaneousChain l t) b E) := by
  exact contDiff_compact_parameter_integral isCompact_closedFundamentalCube (cubeIntersection_compact_carrier E)
    (F := fun p : ℝ×Cover ↦ chainJacobian (simultaneousChain l p.1) p.2 *
      fderiv ℝ b.function (chainMove (simultaneousChain l p.1) p.2) (EuclideanSpace.single b.coordinate 1))
    ((simultaneousJacobian_smooth l).mul
    (((b.smooth.fderiv_right (by simp)).clm_apply contDiff_const).comp (simultaneousMove_smooth l)))

def chainCorrection (l : List Variation) (b : Variation) (E : Set Torus) (t : ℝ) : ℝ :=
  (torusVolume.real E-chainMass (simultaneousChain l t) E)/chainTransportedFlux (simultaneousChain l t) b E

lemma chainCorrection_zero (l : List Variation) (b : Variation)
    {E : Set Torus} (hE : MeasurableSet E) : chainCorrection l b E 0=0 := by
  simp [chainCorrection,simultaneousMass_zero l hE]

lemma chainCorrection_eventually_exact (l : List Variation) (b : Variation)
    {E : Set Torus} (hE : MeasurableSet E) (hB : directionalFlux E b.coordinate b.function≠0) :
    ∀ᶠ t in 𝓝 (0 : ℝ),ChainValid (simultaneousChain l t++[(b,chainCorrection l b E t)]) ∧
      torusVolume (chainRegion (simultaneousChain l t++[(b,chainCorrection l b E t)]) E)=torusVolume E := by
  have hden : chainTransportedFlux (simultaneousChain l 0) b E≠0 := by simpa
  have hc : ContinuousAt (chainCorrection l b E) 0 :=
    (continuousAt_const.sub (simultaneousMass_smooth l E).continuous.continuousAt).div
      (simultaneousFlux_smooth l b E).continuous.continuousAt hden
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ),|chainCorrection l b E t| *(b.bound : ℝ)<1 :=
    (hc.abs.mul_const _).eventually (eventually_lt_nhds (by simp [chainCorrection_zero l b hE]))
  have hne : ∀ᶠ t in 𝓝 (0 : ℝ),chainTransportedFlux (simultaneousChain l t) b E≠0 :=
    (simultaneousFlux_smooth l b E).continuous.continuousAt.eventually_ne hden
  filter_upwards [simultaneousChain_eventually_valid l,hsmall,hne] with t ht hbt hnt
  have hv : ChainValid (simultaneousChain l t++[(b,chainCorrection l b E t)]) :=
    ht.append (by intro p hp; obtain rfl := List.mem_singleton.mp hp; exact hbt)
  refine ⟨hv,?_⟩
  apply ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _) |>.mp
  rw [show (torusVolume (chainRegion _ E)).toReal=torusVolume.real (chainRegion _ E) from rfl,
    volume_chainRegion hv hE,chainMass_append]
  unfold chainCorrection
  rw [div_mul_cancel₀ _ hnt]
  dsimp only [Measure.real]
  ring

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def normSmoothingBump : ContDiffBump (0 : ℝ) := ⟨1/8,1/4,by norm_num,by norm_num⟩

def smoothNormalLength (v : Cover) : ℝ :=
  Real.sqrt (‖v‖^2+normSmoothingBump (‖v‖^2))

lemma smoothNormalLength_smooth : ContDiff ℝ (⊤ : ℕ∞) smoothNormalLength := by
  apply ((contDiff_norm_sq ℝ).add (normSmoothingBump.contDiff.comp (contDiff_norm_sq ℝ))).sqrt
  intro v
  apply ne_of_gt
  by_cases hv : v=0
  · subst v
    simp only [Function.comp_apply,norm_zero,zero_pow (by decide : 2≠0),zero_add]
    rw [normSmoothingBump.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num [normSmoothingBump]))]
    norm_num
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr hv)) normSmoothingBump.nonneg

lemma smoothNormalLength_eq {v : Cover} (hv : 1/2≤‖v‖) : smoothNormalLength v=‖v‖ := by
  unfold smoothNormalLength
  rw [normSmoothingBump.zero_of_le_dist,add_zero,Real.sqrt_sq (norm_nonneg _)]
  simp only [Real.dist_eq,sub_zero,abs_of_nonneg (sq_nonneg ‖v‖)]
  change (1/4 : ℝ)≤‖v‖^2
  nlinarith

def normalEmbedding (z : NormalBundle) : Cover×Cover := (z.1,z.2)

lemma normalEmbedding_continuous : Continuous normalEmbedding :=
  (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)

def normalCarrier : Set (Cover×Cover) := closedFundamentalCube×ˢ Metric.sphere 0 1

lemma normalCarrier_compact : IsCompact normalCarrier :=
  isCompact_closedFundamentalCube.prod (isCompact_sphere 0 1)

lemma normalEmbedding_mem (z : NormalBundle) : normalEmbedding z∈normalCarrier := by
  exact ⟨z.1.property,by simpa [Metric.mem_sphere,dist_zero_right,normalEmbedding] using z.2.property⟩

lemma normalMap_ae_carrier (μ : FiniteMeasure NormalBundle) :
    ∀ᵐ p ∂Measure.map normalEmbedding (μ : Measure NormalBundle),p∈normalCarrier := by
  exact (ae_map_iff normalEmbedding_continuous.measurable.aemeasurable
    (show MeasurableSet normalCarrier from normalCarrier_compact.measurableSet)).2
    (Eventually.of_forall normalEmbedding_mem)

theorem normalArea_smoothAt {C : ℝ×(Cover×Cover) → Cover}
    (hC : ContDiff ℝ (⊤ : ℕ∞) C) (h0 : ∀ p∈normalCarrier,C (0,p)=p.2)
    (μ : FiniteMeasure NormalBundle) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun t ↦ ∫ z,‖C (t,normalEmbedding z)‖ ∂(μ : Measure NormalBundle)) 0 := by
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ),∀ p∈normalCarrier,1/2≤‖C (t,p)‖ := by
    apply normalCarrier_compact.eventually_forall_of_forall_eventually
    intro p hp
    apply ((hC.continuous.norm).continuousAt.eventually (eventually_gt_nhds ?_)).mono
    · intro q hq; exact hq.le
    · change 1/2<‖C (0,p)‖
      rw [h0 p hp]
      have hn : ‖p.2‖=1 := by simpa [Metric.mem_sphere,dist_zero_right] using hp.2
      rw [hn]
      norm_num
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ ∫ p,smoothNormalLength (C (t,p))
      ∂Measure.map normalEmbedding (μ : Measure NormalBundle)) :=
    contDiff_compact_parameter_integral normalCarrier_compact (normalMap_ae_carrier μ)
      (smoothNormalLength_smooth.comp hC)
  apply hs.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hsmall] with t ht
  rw [integral_map normalEmbedding_continuous.measurable.aemeasurable]
  · apply integral_congr_ae
    exact Eventually.of_forall fun z ↦ (smoothNormalLength_eq (ht _ (normalEmbedding_mem z))).symm
  · exact ((smoothNormalLength_smooth.comp hC).continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma second_derivative_nonneg_of_local_min {f : ℝ → ℝ} {t : ℝ}
    (hmin : IsLocalMin f t) (hc : ContinuousAt f t) : 0≤deriv (deriv f) t := by
  by_contra hn
  have hn' : deriv (deriv f) t<0 := lt_of_not_ge hn
  have hmax := isLocalMax_of_deriv_deriv_neg hn' hmin.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 t] (fun _ ↦ f t) := by
    filter_upwards [hmin,hmax] with s hs hs'
    exact le_antisymm hs' hs
  have hz := heq.deriv.deriv_eq
  simp only [deriv_const'] at hz
  linarith

def correctedChain (l : List WallVariation) (b : WallVariation) (γ : ℝ → ℝ) (t : ℝ) : VariationChain :=
  simultaneousChain l t++[(b,γ t)]

def correctedChainArea (l : List WallVariation) (b : WallVariation) (γ : ℝ → ℝ)
    (μ : FiniteMeasure NormalBundle) (t : ℝ) : ℝ :=
  ∫ z,‖chainCofactor (correctedChain l b γ t) z.1 z.2‖ ∂(μ : Measure NormalBundle)

lemma correctedChainCofactor_smooth (l : List WallVariation) (b : WallVariation)
    {γ : ℝ → ℝ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ×(Cover×Cover) ↦ chainCofactor (correctedChain l b γ p.1) p.2.1 p.2.2) := by
  simp only [correctedChain,chainCofactor_append,chainCofactor,coordinateCofactor_eq]
  exact (simultaneousCofactor_smooth l).add ((hγ.comp contDiff_fst).fun_smul
    ((wallVelocity_contDiff b).comp
      (((simultaneousMove_smooth l).comp (contDiff_fst.prodMk contDiff_snd.fst)).prodMk
        (simultaneousCofactor_smooth l))))

lemma correctedChainArea_smoothAt (l : List WallVariation) (b : WallVariation)
    {γ : ℝ → ℝ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγ0 : γ 0=0)
    (μ : FiniteMeasure NormalBundle) : ContDiffAt ℝ (⊤ : ℕ∞) (correctedChainArea l b γ μ) 0 := by
  apply normalArea_smoothAt (correctedChainCofactor_smooth l b hγ) ?_ μ
  intro p _
  simp [correctedChain,chainCofactor_append,chainCofactor,coordinateCofactor_eq,hγ0]

lemma correctedChainArea_zero (l : List WallVariation) (b : WallVariation)
    {γ : ℝ → ℝ} (hγ0 : γ 0=0) (μ : FiniteMeasure NormalBundle) :
    correctedChainArea l b γ μ 0=(μ.mass : ℝ) := by
  unfold correctedChainArea
  simp_rw [correctedChain,chainCofactor_append,chainCofactor,coordinateCofactor_eq,hγ0,
    zero_smul,add_zero,simultaneousCofactor_zero,fun z : NormalBundle ↦ z.2.property]
  simp only [integral_const,smul_eq_mul,mul_one]
  rfl

end CubicTorus
end
end
end

end OAI
