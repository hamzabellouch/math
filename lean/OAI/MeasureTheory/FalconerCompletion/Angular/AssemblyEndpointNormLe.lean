import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Estimates.AssemblyEndpointSmooth
import OAI.MeasureTheory.FalconerCompletion.Recursion.RecursiveUnit
import OAI.MeasureTheory.FalconerCompletion.Recursion.TensorCapCompact

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Classical Topology ComplexConjugate
variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin (n+1))

lemma assemblyEndpoint_norm_le (e : RecursiveEnvironmentND n) (x w : V)
    (b : PolicyDescriptor) (hw : ‖w‖=1) : ‖(assemblyEndpointSmooth e x b).1 w‖ ≤ 1 := by
  have h := actualEndpointMask_bounds e.ρ e.mass e.N e.sig e.C e.J 0 b x hw.le
  simpa only [assemblyEndpointSmooth,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h.1] using h.2

lemma uniform_assemblyEndpoint_derivatives (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (e : RecursiveEnvironmentND n) (x : V)
      (b : PolicyDescriptor) (j : ℕ), j ≤ m → ∀ w,
      ‖iteratedFDeriv ℝ j (assemblyEndpointSmooth e x b).1 w‖ ≤
        D*(sourceMaskScaleND (descriptorLength b) ((2:ℝ)^e.N) e.sig)^j := by
  obtain ⟨D,hD,h⟩ := actualEndpointMask_derivatives (n+1) m
  refine ⟨D,hD,?_⟩
  intro e x b j hj w
  change ‖iteratedFDeriv ℝ j (actualEndpointSmooth e.ρ e.mass e.N e.sig e.C e.J 0 b x).1 w‖ ≤ _
  rw [actualEndpointSmooth_derivative_norm]
  exact h e.ρ e.mass e.N e.sig e.C e.J 0 b j hj x w

lemma assemblyEndpoint_word_exact (e : RecursiveEnvironmentND n) (x : V)
    (b : PolicyDescriptor)
    (L : List (Attempt4PrefixShell.SphereAmbientND n →L[ℝ] Attempt4PrefixShell.SphereAmbientND n)) (w : V) :
    (Attempt4PrefixShell.euclideanAngularWordND
      (sourceMaskScaleND (descriptorLength b) ((2:ℝ)^e.N) e.sig) L (assemblyEndpointSmooth e x b)).1 w =
      (actualEndpointAngular
        (L.map (transportedAngularField (Attempt4PrefixShell.sphereEuclideanIsoND n)))
        e.ρ e.mass e.N e.sig e.C e.J 0 b x).1 w := by
  change (Attempt4PrefixShell.normalizedAngularWordND _ L
    (Attempt4PrefixShell.smoothPullND (Attempt4PrefixShell.sphereEuclideanIsoND n)
      (assemblyEndpointSmooth e x b))).1 ((Attempt4PrefixShell.sphereEuclideanIsoND n).symm w)=_
  simpa only [LinearIsometryEquiv.apply_symm_apply,actualEndpointAngular,
    actualEndpointSmooth,assemblyEndpointSmooth,CurrentFalconer.smoothFunctionSpaceND,
    Attempt4PrefixShell.smoothFunctionSpaceND] using
    normalizedAngularWord_pull_exact (Attempt4PrefixShell.sphereEuclideanIsoND n)
      (sourceMaskScaleND (descriptorLength b) ((2:ℝ)^e.N) e.sig) L
      (actualEndpointSmooth e.ρ e.mass e.N e.sig e.C e.J 0 b x)
      ((Attempt4PrefixShell.sphereEuclideanIsoND n).symm w)

noncomputable def assemblyInverseLeft (e : RecursiveEnvironmentND n) (c : ℕ) (f : V → ℂ)
    (p : PrefixAssignment n) : V → V → ℂ :=
  Attempt4PrefixShell.inverseLeftEndpointND (assemblyDescriptorList e.profile e.N e.q c)
    (fun b => sourceMaskScaleND (descriptorLength b) ((2:ℝ)^e.N) e.sig)
    (assemblyEndpointSmooth e) f p
noncomputable def assemblyInverseRight (e : RecursiveEnvironmentND n) (c : ℕ) (g : V → ℂ)
    (p : PrefixAssignment n) : V → V → ℂ :=
  Attempt4PrefixShell.inverseRightEndpointND (assemblyDescriptorList e.profile e.N e.q c)
    (fun b => sourceMaskScaleND (descriptorLength b) ((2:ℝ)^e.N) e.sig)
    (assemblyEndpointSmooth e) g p

lemma assemblyInverseLeft_eq (e : RecursiveEnvironmentND n) (c : ℕ) (f : V → ℂ)
    (p : PrefixAssignment n) (x w : V) :
    assemblyInverseLeft e c f p x w = f x *
      (actualAngularProduct (assemblyDescriptorList e.profile e.N e.q c) id (prefixLeftWords p)
        e.ρ e.mass e.N e.sig e.C e.J 0 x).1 w := by
  simp only [assemblyInverseLeft,Attempt4PrefixShell.inverseLeftEndpointND,
    actualAngularProduct,smoothFinsetProductND]
  congr 1
  apply Finset.prod_congr rfl
  intro b hb
  exact assemblyEndpoint_word_exact e x b (p.2 (Sum.inl b)) w

lemma assemblyInverseRight_eq (e : RecursiveEnvironmentND n) (c : ℕ) (g : V → ℂ)
    (p : PrefixAssignment n) (x w : V) :
    assemblyInverseRight e c g p x w = g x *
      (actualAngularProduct (assemblyDescriptorList e.profile e.N e.q c) id (prefixRightWords p)
        e.ρ e.mass e.N e.sig e.C e.J 0 x).1 w := by
  simp only [assemblyInverseRight,Attempt4PrefixShell.inverseRightEndpointND,
    actualAngularProduct,smoothFinsetProductND]
  congr 1
  apply Finset.prod_congr rfl
  intro b hb
  exact assemblyEndpoint_word_exact e x b (p.2 (Sum.inr b)) w

lemma assemblyInverseLeft_measurable (e : RecursiveEnvironmentND n) (c : ℕ) {f : V → ℂ}
    (hf : Measurable f) (p : PrefixAssignment n) :
    Measurable (Function.uncurry (assemblyInverseLeft e c f p)) := by
  have hm := (hf.comp measurable_fst).mul
    (actualAngularProduct_measurable (assemblyDescriptorList e.profile e.N e.q c) id (prefixLeftWords p)
      e.ρ e.mass e.N e.sig e.C e.J 0)
  convert hm using 1
  funext z
  exact assemblyInverseLeft_eq e c f p z.1 z.2
lemma assemblyInverseRight_measurable (e : RecursiveEnvironmentND n) (c : ℕ) {f : V → ℂ}
    (hf : Measurable f) (p : PrefixAssignment n) :
    Measurable (Function.uncurry (assemblyInverseRight e c f p)) := by
  have hm := (hf.comp measurable_fst).mul
    (actualAngularProduct_measurable (assemblyDescriptorList e.profile e.N e.q c) id (prefixRightWords p)
      e.ρ e.mass e.N e.sig e.C e.J 0)
  convert hm using 1
  funext z
  exact assemblyInverseRight_eq e c f p z.1 z.2

lemma assemblyInverse_bounds (e₁ e₂ : RecursiveEnvironmentND n) (c : ℕ) {f g : V → ℂ}
    (hf : ∀ x,‖f x‖ ≤ 1) (hg : ∀ x,‖g x‖ ≤ 1) (p : PrefixAssignment n) :
    ∃ B C : ℝ, (∀ x w,‖assemblyInverseLeft e₁ c f p x w‖ ≤ B) ∧
      (∀ x w,‖assemblyInverseRight e₂ c g p x w‖ ≤ C) := by
  obtain ⟨B,hB,hleft⟩ := actualAngularProduct_global_bound
    (assemblyDescriptorList e₁.profile e₁.N e₁.q c) id (prefixLeftWords p)
    e₁.ρ e₁.mass e₁.N e₁.sig e₁.C e₁.J 0
  obtain ⟨C,hC,hright⟩ := actualAngularProduct_global_bound
    (assemblyDescriptorList e₂.profile e₂.N e₂.q c) id (prefixRightWords p)
    e₂.ρ e₂.mass e₂.N e₂.sig e₂.C e₂.J 0
  refine ⟨B,C,?_,?_⟩
  · intro x w
    rw [assemblyInverseLeft_eq,norm_mul]
    exact (mul_le_mul (hf x) (hleft x w) (norm_nonneg _) (by norm_num)).trans_eq (one_mul B)
  · intro x w
    rw [assemblyInverseRight_eq,norm_mul]
    exact (mul_le_mul (hg x) (hright x w) (norm_nonneg _) (by norm_num)).trans_eq (one_mul C)

lemma assemblyInverse_total (S T : Finset PolicyDescriptor) (j : ℕ) {p : PrefixAssignment n}
    (hp : p ∈ Attempt4PrefixShell.inverseAngularTermsND j (S.disjSum T)) :
    (∑ b∈S,(prefixLeftWords p b).length)+(∑ b∈T,(prefixRightWords p b).length) ≤ 2*j := by
  have h := Attempt4PrefixShell.inverseAngularTermsND_budget j _ hp
  simpa only [Finset.sum_disjSum,prefixLeftWords,prefixRightWords,List.length_map] using h
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Classical Topology ComplexConjugate
variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin (n+1))

noncomputable def assemblySpatialFactor (X : Set V) (f : V → ℂ) (ξ : V) : V → ℂ :=
  X.indicator (fun x => Attempt4PrefixShell.SpatialFourierND.spatialFourierPhase (n+1) 1 ξ x*f x)

lemma assemblySpatialFactor_measurable {X : Set V} (hX : MeasurableSet X) {f : V → ℂ}
    (hf : Measurable f) (ξ : V) : Measurable (assemblySpatialFactor X f ξ) := by
  apply Measurable.indicator _ hX
  exact ((Attempt4PrefixShell.SpatialFourierND.spatialFourierPhase_continuous (n+1) 1).measurable.comp
    (measurable_const.prodMk measurable_id)).mul hf

lemma assemblySpatialFactor_norm {X : Set V} {f : V → ℂ} (hf : ∀ x, ‖f x‖ ≤ 1) (ξ x : V) :
    ‖assemblySpatialFactor X f ξ x‖ ≤ 1 := by
  by_cases hx : x∈X
  · simpa only [assemblySpatialFactor,Set.indicator_of_mem hx,norm_mul,
      Attempt4PrefixShell.SpatialFourierND.spatialFourierPhase_norm,one_mul] using hf x
  · simp only [assemblySpatialFactor,Set.indicator_of_notMem hx,norm_zero,zero_le_one]

lemma assembly_left_transform (e : RecursiveEnvironmentND n) (c : ℕ)
    {X : Set V} (hX : MeasurableSet X) (hXroot : X ⊆ treeCell []) (f : V → ℂ)
    (p : PrefixAssignment n) (ξ : V) (r : ℝ) (w : V) :
    Attempt4PrefixShell.spatialEndpointTransformND 1 e.ρ X (((2:ℝ)^e.N)^(-e.mass 0))
      (assemblyInverseLeft e c f p) (ξ,(r,w)) =
    _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ (treeCell []) (((2:ℝ)^e.N)^(-e.mass 0))
      (assemblySymbol e c (prefixLeftWords p) (assemblySpatialFactor X f ξ) recursiveUnit) r w := by
  unfold Attempt4PrefixShell.spatialEndpointTransformND Attempt4PrefixShell.sourceAngularTransformND
    _root_.OAI.CurrentFalconer.sourceAngularTransformND
  congr 1
  let H : V → ℂ := fun x => Attempt4PrefixShell.spherePlaneWaveND r x w *
    (Attempt4PrefixShell.SpatialFourierND.spatialFourierPhase (n+1) 1 ξ x * assemblyInverseLeft e c f p x w)
  have he : (fun x => _root_.OAI.CurrentFalconer.spherePlaneWaveND r x w *
      assemblySymbol e c (prefixLeftWords p) (assemblySpatialFactor X f ξ) recursiveUnit x w) = X.indicator H := by
    funext x
    by_cases hx : x∈X
    · simp only [Set.indicator_of_mem hx,assemblySymbol,assemblySpatialFactor,recursiveUnit,
        one_mul,H,assemblyInverseLeft_eq]
      rw [mul_assoc]
      rfl
    · simp only [Set.indicator_of_notMem hx,assemblySymbol,assemblySpatialFactor,recursiveUnit,
        mul_zero,zero_mul]
  rw [he,integral_indicator hX,Measure.restrict_restrict_of_subset hXroot]

lemma assembly_right_transform (e : RecursiveEnvironmentND n) (c : ℕ)
    {X : Set V} (hX : MeasurableSet X) (hXroot : X ⊆ treeCell []) (f : V → ℂ)
    (p : PrefixAssignment n) (ξ : V) (r : ℝ) (w : V) :
    Attempt4PrefixShell.spatialEndpointTransformND 1 e.ρ X (((2:ℝ)^e.N)^(-e.mass 0))
      (assemblyInverseRight e c f p) (ξ,(r,w)) =
    _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ (treeCell []) (((2:ℝ)^e.N)^(-e.mass 0))
      (assemblySymbol e c (prefixRightWords p) (assemblySpatialFactor X f ξ) recursiveUnit) r w := by
  unfold Attempt4PrefixShell.spatialEndpointTransformND Attempt4PrefixShell.sourceAngularTransformND
    _root_.OAI.CurrentFalconer.sourceAngularTransformND
  congr 1
  let H : V → ℂ := fun x => Attempt4PrefixShell.spherePlaneWaveND r x w *
    (Attempt4PrefixShell.SpatialFourierND.spatialFourierPhase (n+1) 1 ξ x * assemblyInverseRight e c f p x w)
  have he : (fun x => _root_.OAI.CurrentFalconer.spherePlaneWaveND r x w *
      assemblySymbol e c (prefixRightWords p) (assemblySpatialFactor X f ξ) recursiveUnit x w) = X.indicator H := by
    funext x
    by_cases hx : x∈X
    · simp only [Set.indicator_of_mem hx,assemblySymbol,assemblySpatialFactor,recursiveUnit,
        one_mul,H,assemblyInverseRight_eq]
      rw [mul_assoc]
      rfl
    · simp only [Set.indicator_of_notMem hx,assemblySymbol,assemblySpatialFactor,recursiveUnit,
        mul_zero,zero_mul]
  rw [he,integral_indicator hX,Measure.restrict_restrict_of_subset hXroot]

lemma assembly_HF_transform (e₁ e₂ : RecursiveEnvironmentND n) (c : ℕ)
    {X Y : Set V} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXroot : X ⊆ treeCell []) (hYroot : Y ⊆ treeCell []) (f g : V → ℂ)
    (p : PrefixAssignment n) (ξ : V) (Ψ : ℝ → ℝ) (ψ : V → ℂ) :
    Attempt4PrefixShell.sourceAngularHFND (n+1) (Attempt4PrefixShell.canonicalSphereMeasureND V)
      0 e₁.N Ψ ψ
      (fun z => Attempt4PrefixShell.spatialEndpointTransformND 1 e₁.ρ X (((2:ℝ)^e₁.N)^(-e₁.mass 0))
        (assemblyInverseLeft e₁ c f p) (ξ,z))
      (fun z => Attempt4PrefixShell.spatialEndpointTransformND 1 e₂.ρ Y (((2:ℝ)^e₂.N)^(-e₂.mass 0))
        (assemblyInverseRight e₂ c g p) (ξ,z)) =
    assemblyRootEnergy e₁ e₂ c (prefixLeftWords p) (prefixRightWords p)
      (assemblySpatialFactor X f ξ) (assemblySpatialFactor Y g ξ) recursiveUnit recursiveUnit Ψ ψ := by
  simp only [assembly_left_transform e₁ c hX hXroot,assembly_right_transform e₂ c hY hYroot,
    Attempt4PrefixShell.sourceAngularHFND,assemblyRootEnergy,_root_.OAI.Attempt4Near.sourceAngularHFND]
  rfl
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Classical Topology
variable {n : ℕ}

lemma assembly_bounded_cutoff (ψ : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) :
    ∃ φ : EuclideanSpace ℝ (Fin (n+1)) → ℂ, ContDiff ℝ ∞ φ ∧
      (∀ w, ‖w‖=1 → φ =ᶠ[𝓝 w] ψ) ∧ ∃ P : ℝ, ∀ w, ‖φ w‖ ≤ P := by
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin (n+1))) := ⟨2,3,by norm_num,by norm_num⟩
  let φ : EuclideanSpace ℝ (Fin (n+1)) → ℂ := fun w => (b w:ℂ)*ψ w
  refine ⟨φ,(Complex.ofRealCLM.contDiff.comp b.contDiff).mul hψ,?_,?_⟩
  · intro w hw
    have hb := b.eventuallyEq_one_of_mem_ball (x:=w) (by simp [Metric.mem_ball,dist_zero_right,b,hw])
    filter_upwards [hb] with z hz
    simp only [φ,hz,Pi.one_apply,Complex.ofReal_one,one_mul]
  · obtain ⟨P,hP⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) 3).exists_bound_of_continuousOn hψ.continuous.continuousOn
    refine ⟨max P 0,?_⟩
    intro w
    by_cases hw : ‖w‖ ≤ 3
    · calc
        ‖φ w‖ = |b w| *‖ψ w‖ := by simp [φ]
        _ ≤ 1*‖ψ w‖ := mul_le_mul_of_nonneg_right (by rw [abs_of_nonneg b.nonneg]; exact b.le_one) (norm_nonneg _)
        _ ≤ max P 0 := by simpa only [one_mul] using (hP w (by simpa [Metric.mem_closedBall,dist_zero_right] using hw)).trans (le_max_left _ _)
    · have hb : b w=0 := b.zero_of_le_dist (by simpa [b,dist_zero_right] using (le_of_lt (lt_of_not_ge hw)))
      simp only [φ,hb,Complex.ofReal_zero,zero_mul,norm_zero]
      exact le_max_right _ _

lemma assembly_cutoff_transfer (ρ ν : Measure (EuclideanSpace ℝ (Fin (n+1))))
    [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    {X Y : Set (EuclideanSpace ℝ (Fin (n+1)))} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ x∈X,∀ y∈Y,δ ≤ dist x y)
    {ψ φ : EuclideanSpace ℝ (Fin (n+1)) → ℂ}
    (hφ : ∀ w,‖w‖=1 → φ =ᶠ[𝓝 w] ψ)
    (hc : ∀ᵐ z ∂(ρ.restrict X).prod (ν.restrict Y),
      ψ =ᶠ[𝓝 ((dist z.1 z.2)⁻¹ • (z.1-z.2))] (fun _ => 1) ∧
      ψ =ᶠ[𝓝 (-((dist z.1 z.2)⁻¹ • (z.1-z.2)))] (fun _ => 0)) :
    ∀ᵐ z ∂(ρ.restrict X).prod (ν.restrict Y),
      φ =ᶠ[𝓝 ((dist z.1 z.2)⁻¹ • (z.1-z.2))] (fun _ => 1) ∧
      φ =ᶠ[𝓝 (-((dist z.1 z.2)⁻¹ • (z.1-z.2)))] (fun _ => 0) := by
  have hxy : ∀ᵐ z ∂(ρ.restrict X).prod (ν.restrict Y), z.1∈X ∧ z.2∈Y :=
    (Measure.ae_prod_iff_ae_ae (hX.prod hY)).mpr (by
      filter_upwards [ae_restrict_mem hX] with x hx
      filter_upwards [ae_restrict_mem hY] with y hy
      exact ⟨hx,hy⟩)
  filter_upwards [hxy,hc] with z hz hc
  have hd : 0 < dist z.1 z.2 := hδ.trans_le (hsep _ hz.1 _ hz.2)
  have hw : ‖(dist z.1 z.2)⁻¹ • (z.1-z.2)‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hd,←dist_eq_norm,inv_mul_cancel₀ hd.ne']
  exact ⟨(hφ _ hw).trans hc.1,(hφ _ (by simpa only [norm_neg] using hw)).trans hc.2⟩
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
