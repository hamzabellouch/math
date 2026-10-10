import OAI.MathematicalPhysics.Elasticity.BoundaryData

namespace OAI

noncomputable section

namespace ElasticityBoundaryTensorPull
/-! Finite sesquilinear tensor change of coordinates. The real change of
variables assumption is explicit and is proved for the actual Jacobian. -/
open scoped BigOperators

lemma sum_four_exchange {ι κ σ τ A : Type*} [Fintype ι] [Fintype κ]
    [Fintype σ] [Fintype τ] [AddCommMonoid A] (f : ι → κ → σ → τ → A) :
    (∑ i, ∑ j, ∑ r, ∑ s, f i j r s)=∑ r, ∑ s, ∑ i, ∑ j, f i j r s := by
  calc
    _ = ∑ i, ∑ r, ∑ j, ∑ s, f i j r s := by
      apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
    _ = ∑ r, ∑ i, ∑ j, ∑ s, f i j r s := Finset.sum_comm
    _ = ∑ r, ∑ i, ∑ s, ∑ j, f i j r s := by
      apply Finset.sum_congr rfl; intro r _
      apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
    _ = _ := by apply Finset.sum_congr rfl; intro r _; exact Finset.sum_comm

lemma sesqui_pull {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ι → ℂ) (R : ι → κ → ℂ) (hR : ∀ i j, star (R i j)=R i j)
    (u v : κ → ℂ) :
    (∑ i, ∑ j, a i j*(∑ r, R i r*u r)*star (∑ s, R j s*v s))=
      ∑ r, ∑ s, (∑ i, ∑ j, R i r*a i j*R j s)*u r*star (v s) := by
  simp only [star_sum,star_mul,hR,Finset.mul_sum,Finset.sum_mul]
  rw [sum_four_exchange,Finset.sum_comm]
  apply Finset.sum_congr rfl; intro r _
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

end ElasticityBoundaryTensorPull
namespace Elasticity
/-! The complex physical variational density is exactly the Hermitian
contraction of the literal isotropic elasticity tensor. -/
open scoped BigOperators
open ElasticityBoundaryLayerOperator
abbrev CMatrix := Fin 3 → Fin 3 → ℂ

def tensorDensity (a : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ) (P Q : CMatrix) : ℂ :=
  ∑ i, ∑ α, ∑ j, ∑ β, a i α j β*P i α*star (Q j β)

def sesquiDensity (l m : ℂ) (P Q : CMatrix) : ℂ :=
  l*(∑ i, P i i)*star (∑ i, Q i i)+
    (m/2)*∑ i, ∑ j, (P i j+P j i)*star (Q i j+Q j i)

lemma complexDensity_sesqui (l m : ℝ) (P Q : CMatrix) :
    complexDensity l m P Q=sesquiDensity (l:ℂ) (m:ℂ) P Q := by
  apply Complex.ext <;>
    simp only [complexDensity,realMatrix,elasticDensity,sesquiDensity,
      Fin.sum_univ_three,PiLp.toLp_apply,Complex.reCLM_apply,Complex.imCLM_apply,
      Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,Complex.star_def,Complex.conj_re,Complex.conj_im,
      Complex.div_ofNat_re,Complex.div_ofNat_im] <;> ring

lemma tensorDensity_isotropic (l m : ℂ) (P Q : CMatrix) :
    tensorDensity (elasticityTensor l m) P Q=sesquiDensity l m P Q := by
  unfold tensorDensity elasticityTensor
  simp only [add_mul,mul_add,Finset.sum_add_distrib,mul_ite,ite_mul,mul_one,mul_zero,
    zero_mul,Finset.sum_ite_irrel,Fintype.sum_ite_eq,Finset.sum_const_zero]
  simp only [sesquiDensity,Fin.sum_univ_three,star_add]
  ring

lemma complexDensity_tensor (l m : ℝ) (P Q : CMatrix) :
    complexDensity l m P Q=tensorDensity (elasticityTensor (l:ℂ) (m:ℂ)) P Q := by
  rw [complexDensity_sesqui,tensorDensity_isotropic]

end Elasticity
namespace ElasticityBoundaryDensityPull
open Set Filter
open scoped Topology BigOperators

section
/-! The exact physical elastic density under the honest boundary chart. -/
open Elasticity ElasticityBoundaryTensorPull ElasticityBoundaryRotation
  ElasticityBoundaryGradientTransfer ElasticityBoundaryFrameInverse
  ElasticityBoundaryChainRule ElasticityBoundaryChartOperator ElasticityBoundaryPhysicalMass
  ElasticityBoundaryPhysicalTransfer ElasticityBoundaryPullback ElasticityBoundaryFrameOperator
  ElasticityBoundaryPhysicalStrong ElasticityBoundaryStrongLayer ElasticityBoundaryCompactMatrix
  ElasticityBoundaryLayerOperator
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I
abbrev Y := I → ℝ

def pullMatrix (Q J U : I → I → ℂ) (i k : I) : ℂ :=
  ∑ s, ∑ α, (Q i s*J k α)*U s α

def pullTensor (Q J : I → I → ℂ) (a : I → I → I → I → ℂ)
    (s α r β : I) : ℂ :=
  ∑ i, ∑ k, ∑ j, ∑ v, (Q i s*J k α)*a i k j v*(Q j r*J v β)

lemma tensor_pull (Q J : I → I → ℂ) (hQ : ∀ i j, star (Q i j)=Q i j)
    (hJ : ∀ i j, star (J i j)=J i j) (a : I → I → I → I → ℂ) (U V : CMatrix) :
    tensorDensity a (pullMatrix Q J U) (pullMatrix Q J V)=tensorDensity (pullTensor Q J a) U V := by
  have hh := sesqui_pull (fun p q : I×I => a p.1 p.2 q.1 q.2)
    (fun p q : I×I => Q p.1 q.1*J p.2 q.2)
    (fun p q => by rw [star_mul,hQ,hJ]; ring) (fun p : I×I => U p.1 p.2) (fun p : I×I => V p.1 p.2)
  simpa only [Fintype.sum_prod_type,tensorDensity,pullMatrix,pullTensor] using hh

lemma principal_pullTensor (Q : X ≃ₗᵢ[ℝ] X) (Φ Ψ : X → X) (l m : X → ℂ)
    (y : X) (s α r β : I) :
    ElasticityBoundaryPhysicalMass.principal Q Φ Ψ l m s α r β y.ofLp=
      pullTensor (frameMatrix Q) (fun k a => jacobian Φ Ψ k a y)
        (elasticityTensor (l (Φ y)) (m (Φ y))) s α r β := by
  unfold ElasticityBoundaryPhysicalMass.principal chartPrincipal principalPull mixedTensor coeff pullTensor
  simp only [WithLp.toLp_ofLp,Finset.sum_mul]
  rw [sum_four_exchange]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro v _
  simp only [jacobian]
  ring

lemma gradient_pullMatrix (e : OpenPartialHomeomorph X X) {K : Set X}
    (hK : IsCompact K) (hs : K⊆e.source) {η : X → ℝ} (hηs : tsupport η⊆e.target)
    (hη : ∀ z∈e '' K, η z=1) (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j))
    (hus : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K)
    (Φ Ψ : X → X) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΦ : ∀ y∈K, Φ y=e y) (hΨe : ∀ z∈e '' K, Ψ =ᶠ[𝓝 z] e.symm)
    {y : X} (hy : y∈e.source) :
    fieldGradient (transferred e η Q u) (e y)=
      pullMatrix (frameMatrix Q) (fun k a => jacobian Φ Ψ k a y) (fun i α => dpart (u i) α y.ofLp) := by
  funext i d
  have hh := frame_inverse Q (fun j => dd (transferred e η Q u j) (basis d) (e y)) i
  simp only [gradient_all e hK hs hηs hη Q u hu hus Φ Ψ hΨ hΦ hΨe hy] at hh
  change dd (transferred e η Q u i) (basis d) (e y) = _
  rw [← hh]
  simp only [row,pullMatrix,Finset.mul_sum,mul_assoc]

lemma density_chart (e : OpenPartialHomeomorph X X) {K : Set X}
    (hK : IsCompact K) (hs : K⊆e.source) {η : X → ℝ} (hηs : tsupport η⊆e.target)
    (hη : ∀ z∈e '' K, η z=1) (Q : X ≃ₗᵢ[ℝ] X) (u v : I → Y → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (hv : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (v j))
    (hus : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K)
    (hvs : ∀ j, Function.support (fun z : X => v j z.ofLp)⊆K)
    (Φ Ψ : X → X) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΦ : ∀ y∈K, Φ y=e y) (hΨe : ∀ z∈e '' K, Ψ =ᶠ[𝓝 z] e.symm)
    (l m : X → ℝ) {y : X} (hy : y∈K) :
    complexDensity (l (e y)) (m (e y)) (fieldGradient (transferred e η Q u) (e y))
      (fieldGradient (transferred e η Q v) (e y))=
      tensorDensity (fun i α j β => ElasticityBoundaryPhysicalMass.principal Q Φ Ψ
        (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) i α j β y.ofLp)
        (fun i α => dpart (u i) α y.ofLp) (fun i α => dpart (v i) α y.ofLp) := by
  rw [complexDensity_tensor,gradient_pullMatrix e hK hs hηs hη Q u hu hus Φ Ψ hΨ hΦ hΨe (hs hy),
    gradient_pullMatrix e hK hs hηs hη Q v hv hvs Φ Ψ hΨ hΦ hΨe (hs hy)]
  have hR (i j : I) : star (frameMatrix Q i j)=frameMatrix Q i j := Complex.conj_ofReal _
  have hJ (i j : I) : star (jacobian Φ Ψ i j y)=jacobian Φ Ψ i j y := Complex.conj_ofReal _
  rw [tensor_pull _ _ hR hJ]
  simp only [principal_pullTensor,hΦ y hy]

end
/-! The exact tensor-density identity extends over the whole honest chart;
all derivatives vanish outside the actual compact packet support. -/
open Elasticity ElasticityBoundaryGradientTransfer ElasticityBoundaryPhysicalTransfer
  ElasticityBoundaryChainRule ElasticityBoundaryChartOperator ElasticityBoundaryPhysicalMass
  ElasticityBoundaryStrongLayer ElasticityBoundaryForceSupport

lemma tensor_zero_left (a : I → I → I → I → ℂ) (V : CMatrix) :
    tensorDensity a 0 V=0 := by simp [tensorDensity]

lemma physical_density_support {K : Set X} (hK : IsClosed K) (l m : X → ℝ)
    (u v : I → X → ℂ) (hus : ∀ i, Function.support (u i)⊆K) :
    Function.support (fun z => complexDensity (l z) (m z) (fieldGradient u z) (fieldGradient v z))⊆K := by
  intro z hz
  by_contra hn
  have ht : fieldGradient u z=0 := by
    funext i d
    exact Function.notMem_support.mp (fun h => hn (dd_support hK (hus i) (basis d) h))
  exact hz (by dsimp only; rw [complexDensity_tensor,ht,tensor_zero_left])

lemma chart_density_support {K : Set X} (hK : IsClosed K)
    (a : X → I → I → I → I → ℂ) (u v : I → Y → ℂ)
    (hus : ∀ i, Function.support (fun z : X => u i z.ofLp)⊆K) :
    Function.support (fun z : X => tensorDensity (a z)
      (fun i α => dpart (u i) α z.ofLp) (fun i α => dpart (v i) α z.ofLp))⊆K := by
  intro z hz
  by_contra hn
  have ht : (fun i α => dpart (u i) α z.ofLp)=(0:CMatrix) := by
    funext i d
    exact Function.notMem_support.mp (fun h => hn (dpart_support_lifted hK (hus i) d h))
  exact hz (by dsimp only; rw [ht,tensor_zero_left])

lemma density_chart_all (e : OpenPartialHomeomorph X X) {K : Set X}
    (hK : IsCompact K) (hs : K⊆e.source) {η : X → ℝ} (hηs : tsupport η⊆e.target)
    (hη : ∀ z∈e '' K, η z=1) (Q : X ≃ₗᵢ[ℝ] X) (u v : I → Y → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (hv : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (v j))
    (hus : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K)
    (hvs : ∀ j, Function.support (fun z : X => v j z.ofLp)⊆K)
    (Φ Ψ : X → X) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΦ : ∀ y∈K, Φ y=e y) (hΨe : ∀ z∈e '' K, Ψ =ᶠ[𝓝 z] e.symm)
    (l m : X → ℝ) {y : X} (hy : y∈e.source) :
    complexDensity (l (e y)) (m (e y)) (fieldGradient (transferred e η Q u) (e y))
      (fieldGradient (transferred e η Q v) (e y))=
      tensorDensity (fun i α j β => ElasticityBoundaryPhysicalMass.principal Q Φ Ψ
        (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) i α j β y.ofLp)
        (fun i α => dpart (u i) α y.ofLp) (fun i α => dpart (v i) α y.ofLp) := by
  by_cases hyK : y∈K
  · exact density_chart e hK hs hηs hη Q u v hu hv hus hvs Φ Ψ hΨ hΦ hΨe l m hyK
  · have hn : e y∉e '' K := by
      rintro ⟨z,hz,he⟩
      exact hyK (e.injOn (hs hz) hy he ▸ hz)
    rw [Function.notMem_support.mp (fun h => hn
      (physical_density_support (compact_image e hK hs).isClosed l m _ _
        (support_transferred e hηs Q u hus) h)),
      Function.notMem_support.mp (fun h => hyK (chart_density_support hK.isClosed
        (fun z i α j β => ElasticityBoundaryPhysicalMass.principal Q Φ Ψ
          (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) i α j β z.ofLp) u v hus h))]

end ElasticityBoundaryDensityPull
namespace ElasticityBoundaryEnergyChart
/-! Exact complex physical energy change of variables for the actual packets. -/
open Set Filter MeasureTheory
open scoped Topology BigOperators
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- A compactly supported physical integrand pulls back with its exact
Jacobian, including the domain's half-space indicator. -/
theorem compact_chart_integral_complex (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    {K Ω H : Set E} (hs : K⊆e.source) (hΩ : MeasurableSet Ω) (hH : MeasurableSet H)
    (hhalf : ∀ y∈e.source, e y∈Ω ↔ y∈H)
    {Φ : E → E} (hΦ : ∀ y∈K, Φ =ᶠ[𝓝 y] e)
    (f g : E → ℂ) (hf : Function.support f⊆e '' K) (hg : Function.support g⊆K)
    (hfg : ∀ y∈e.source, f (e y)=g y) :
    (∫ x in Ω, f x ∂μ)=(∫ y in H, |(fderiv ℝ Φ y).det| • g y ∂μ) := by
  have hd (y : E) (hy : y∈e.source) : HasFDerivAt e (fderiv ℝ e y) y :=
    ((he.differentiableOn (by simp)).differentiableAt (e.open_source.mem_nhds hy)).hasFDerivAt
  rw [← integral_indicator hΩ]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := e.target) (f := Ω.indicator f)
    (fun x hx => by
      have hh : f x=0 := by
        by_contra hn
        obtain ⟨y,hy,rfl⟩ := hf hn
        exact hx (e.map_source (hs hy))
      simp only [indicator,hh,ite_self])]
  rw [integral_target_eq_integral_abs_det_fderiv_smul μ hd]
  have heq : (∫ y in e.source, |(fderiv ℝ e y).det| • Ω.indicator f (e y) ∂μ)=
      ∫ y in e.source, H.indicator (fun z => |(fderiv ℝ Φ z).det| • g z) y ∂μ := by
    apply setIntegral_congr_fun e.open_source.measurableSet
    intro y hy
    dsimp only
    by_cases hyK : y∈K
    · rw [← (hΦ y hyK).fderiv_eq]
      by_cases hyH : y∈H
      · rw [indicator_of_mem ((hhalf y hy).mpr hyH),indicator_of_mem hyH,hfg y hy]
      · rw [indicator_of_notMem (fun h => hyH ((hhalf y hy).mp h)),indicator_of_notMem hyH,smul_zero]
    · have hz : g y=0 := Function.notMem_support.mp (fun h => hyK (hg h))
      simp only [indicator, hfg y hy]
      simp only [hz,smul_zero,ite_self]
  rw [heq]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_indicator hH
  · intro y hy
    have hz : g y=0 := Function.notMem_support.mp (fun h => hy (hs (hg h)))
    simp only [indicator,hz,smul_zero,ite_self]

end ElasticityBoundaryEnergyChart
namespace ElasticityBoundaryPacket
/-! Smooth compact localization of the literal pulled physical energy tensor.
The true chart Jacobian is retained, including its nonzero value at the center. -/
open Set Filter
open scoped Topology BigOperators
open Elasticity ElasticityBoundary ElasticityBoundaryPhysicalMass
  ElasticityBoundaryChartOperator ElasticityBoundaryLayerOperator

variable {Ω : Set X} {x : X}

def Setup.jacobian (s : Setup Ω x) (y : Y) : ℝ :=
  |(fderiv ℝ s.Φ (WithLp.toLp 2 y)).det|

def Setup.rawCoeff (s : Setup Ω x) (l m : X → ℂ) (i α j β : I) (y : Y) : ℂ :=
  (s.jacobian y:ℂ)*principal s.Q s.Φ s.Ψ l m i α j β y

lemma Setup.jacobian_continuous (s : Setup Ω x) : Continuous s.jacobian :=
  ((ContinuousLinearMap.continuous_det.comp (s.Φ_smooth.continuous_fderiv (by simp))).abs).comp
    (PiLp.continuous_toLp 2 (fun _ : I => ℝ))

lemma Setup.jacobian_pos (s : Setup Ω x) : 0<s.jacobian 0 := by
  have hf : fderiv ℝ s.Φ 0=s.Q.toContinuousLinearEquiv.toContinuousLinearMap := by
    rw [(s.Φ_germ 0 s.zero_mem).fderiv_eq]
    exact s.deriv.fderiv
  simp only [Setup.jacobian,WithLp.toLp_zero,hf]
  exact abs_pos.mpr s.Q.toLinearEquiv.isUnit_det'.ne_zero

lemma Setup.rawCoeff_continuous (s : Setup Ω x) {l m : X → ℂ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m) (i α j β : I) :
    Continuous (s.rawCoeff l m i α j β) := by
  exact (Complex.continuous_ofReal.comp s.jacobian_continuous).mul
    (smooth_chartPrincipal s.Q (s.Φ_smooth.comp PiLp.contDiff_toLp)
      (PiLp.contDiff_ofLp.comp s.Ψ_smooth) hl hm i α j β).continuous

lemma Setup.rawCoeff_zero (s : Setup Ω x) (l m : X → ℂ) (i α j β : I) :
    s.rawCoeff l m i α j β 0=(s.jacobian 0:ℂ)*elasticityTensor (l x) (m x) i α j β := by
  rw [Setup.rawCoeff,s.frozen]

/-- All modifications of this coefficient are outside the support of the
actual trial gradients. Its leading coefficient is the actual isotropic tensor. -/
lemma Setup.compact_energy_coefficients (s : Setup Ω x) {l m : X → ℂ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m) :
    ∃ H : I → I → I → I → Y → ℂ,
      (∀ i α j β, Continuous (H i α j β)) ∧
      (∀ i α j β, HasCompactSupport (H i α j β)) ∧
      (∀ i α j β y, WithLp.toLp 2 y∈s.K → H i α j β y=s.rawCoeff l m i α j β y) := by
  obtain ⟨ρ,hρ,hρc,_,hρ1,_⟩ := compact_smooth_cutoff s.compact isOpen_univ (subset_univ s.K)
  let ρc : Y → ℂ := fun y => (ρ (WithLp.toLp 2 y):ℂ)
  have hρcc : HasCompactSupport ρc :=
    (hρc.comp_homeomorph (PiLp.homeomorph 2 (fun _ : I => ℝ)).symm).comp_left
      (g := Complex.ofReal) Complex.ofReal_zero
  refine ⟨fun i α j β y => ρc y*s.rawCoeff l m i α j β y,?_,?_,?_⟩
  · intro i α j β
    exact (Complex.continuous_ofReal.comp (hρ.continuous.comp
      (PiLp.continuous_toLp 2 (fun _ : I => ℝ)))).mul (s.rawCoeff_continuous hl hm i α j β)
  · intro i α j β
    exact hρcc.mul_right
  · intro i α j β y hy
    simp only [ρc,hρ1.self_of_nhdsSet _ hy,Complex.ofReal_one,one_mul]

end ElasticityBoundaryPacket
namespace ElasticityBoundaryLimit
/-! Genuine Gaussian boundary scaling limits for the finite corrected
amplitudes. Dominated convergence is proved from the uniform polynomial
majorants and the actual half-space weight. -/
open Set Filter MeasureTheory
open scoped Topology BigOperators
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryScaling ElasticityBoundaryWeights ElasticityBoundaryOrderBound
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundaryCutoffParametrix
  ElasticityBoundaryProfileBounds ElasticityBoundaryCutoffLayer
abbrev Y := Fin 3 → ℝ

lemma eventually_small_positive : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0<δ ∧ δ≤1 := by
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with δ hδ h1
  exact ⟨hδ,h1.le⟩

lemma OrderBound.conj {F : ℝ → Y → ℂ} {k : ℕ} (hF : OrderBound F k) :
    OrderBound (fun δ y => star (F δ y)) k := by
  obtain ⟨A,hA,n,h⟩ := hF
  exact ⟨A,hA,n,fun δ hδ h1 y => by simpa only [norm_star] using h δ hδ h1 y⟩

/-- Domination uses the full Gaussian-normal weight, and is uniform for every
small positive scale. No convergence of the physical DN symbol is assumed. -/
theorem weighted_tendsto {F : ℝ → Y → ℂ} {f : Y → ℂ}
    (hF : OrderBound F 0) (hc : ∀ δ, Continuous (F δ))
    (ht : ∀ y, Tendsto (fun δ => F δ y) (𝓝[>] 0) (𝓝 (f y)))
    {b : ℝ} (hb : 0<b) :
    Tendsto (fun δ => ∫ y, weight b y • F δ y) (𝓝[>] 0) (𝓝 (∫ y, weight b y • f y)) := by
  obtain ⟨A,hA,n,hB⟩ := hF
  let g : Y → ℝ := fun y => (A*2^n)*(weight b y+‖y‖^n*weight b y)
  have hg : Integrable g := ((integrable_weight hb).add (integrable_norm_moment hb n)).const_mul _
  apply tendsto_integral_filter_of_dominated_convergence g
  · exact Eventually.of_forall (fun δ => (measurable_weight b).aestronglyMeasurable.smul
      (hc δ).aestronglyMeasurable)
  · filter_upwards [eventually_small_positive] with δ hδ
    exact Eventually.of_forall (fun y => by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (weight_nonneg b y)]
      have h := hB δ hδ.1 hδ.2 y
      simp only [pow_zero,mul_one] at h
      calc
        _ ≤ weight b y*(A*(1+‖y‖)^n) := mul_le_mul_of_nonneg_left h (weight_nonneg b y)
        _ ≤ weight b y*(A*(2^n*(1+‖y‖^n))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (one_add_pow_le (norm_nonneg y) n) hA)
            (weight_nonneg b y)
        _ = g y := by dsimp [g]; ring)
  · exact hg
  · exact Eventually.of_forall (fun y => tendsto_const_nhds.smul (ht y))

lemma continuous_value_parameter (q : Polynomial MP) (y : Y) :
    Continuous (fun δ : ℝ => value (atParameter q δ) y) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      have he : (fun δ : ℝ => value (atParameter (p+q) δ) y)=
          (fun δ => value (atParameter p δ) y+value (atParameter q δ) y) := by
        funext δ
        rw [atParameter_add,value_add]
      rw [he]
      exact hp.add hq
  | monomial n p =>
      simp_rw [value_parameter_monomial]
      exact continuous_const.mul (Complex.continuous_ofReal.pow n)

lemma value_parameter_zero (q : Polynomial MP) (y : Y) :
    value (atParameter q 0) y=value (q.coeff 0) y := by
  simp only [atParameter,Complex.ofReal_zero,map_zero,← Polynomial.coeff_zero_eq_eval_zero]

lemma PD_coeff_zero (q : Polynomial MP) (β : Fin 3) :
    (PD β q).coeff 0=E₀ β (q.coeff 0) := by
  simp [PD_apply,coeffMap_coeff]

lemma firstScaled_tendsto {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (h0 : χ 0=1)
    (q : Polynomial W) (j β : Fin 3) (y : Y) :
    Tendsto (fun δ => firstScaled χ q δ j β y) (𝓝[>] 0)
      (𝓝 (value (E₀ β (q.coeff 0 j)) y)) := by
  have hχt : Tendsto (fun δ => χ (scale δ y)) (𝓝 (0:ℝ)) (𝓝 1) := by
    simpa only [Function.comp_def,h0] using hχ.continuous.continuousAt.tendsto.comp (scale_tendsto_zero y)
  have hpt : Tendsto (fun δ => value (atParameter (PD β (unpack j q)) δ) y)
      (𝓝 (0:ℝ)) (𝓝 (value (E₀ β (q.coeff 0 j)) y)) := by
    simpa only [value_parameter_zero,PD_coeff_zero,unpack,coeffMap_coeff,LinearMap.proj_apply]
      using (continuous_value_parameter (PD β (unpack j q)) y).tendsto 0
  have hdt := (smooth_dpart hχ β).continuous.continuousAt.tendsto.comp (scale_tendsto_zero y)
  have hqt := (continuous_value_parameter (unpack j q) y).tendsto 0
  have ht := (hχt.mul hpt).add (((Complex.continuous_ofReal.tendsto 0).pow 2).mul hdt |>.mul hqt)
  simpa only [Complex.ofReal_zero,zero_pow (by norm_num : 2≠0),zero_mul,one_mul,add_zero,Function.comp_def,firstScaled]
    using ht.mono_left nhdsWithin_le_nhds

lemma amplitude_coeff_zero (p : ℕ → W) (N : ℕ) : (amplitude p N).coeff 0=p 0 := by
  simp [amplitude,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]

end ElasticityBoundaryLimit
namespace ElasticityBoundaryEnergyLimit
/-! Actual normalized mixed energy limits of the corrected, cut-off boundary
layers. The coefficient has its genuine normal factor and arbitrary compact
smooth remainder; all Jacobian and physical-derivative powers are exact. -/
open Set Filter MeasureTheory
open scoped Topology BigOperators
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryScaling ElasticityBoundaryWeights ElasticityBoundaryOrderBound
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundaryCutoffParametrix ElasticityBoundaryLimit
  ElasticityBoundaryProfileBounds ElasticityBoundaryCutoffLayer ElasticityBoundaryProfile
  ElasticityBoundaryCutoffBound
abbrev Y := Fin 3 → ℝ

lemma normal_power_bound (n : ℕ) : OrderBound (fun (_ : ℝ) (y : Y) => (y 2:ℂ)^n) 0 := by
  refine ⟨1,by norm_num,n,fun δ _ _ y => ?_⟩
  simp only [pow_zero,mul_one,one_mul,norm_pow,Complex.norm_real]
  exact pow_le_pow_left₀ (norm_nonneg _) ((norm_le_pi_norm y 2).trans (by linarith [norm_nonneg y])) n

def mixedScaled (n : ℕ) (H χ : Y → ℂ) (p q : Polynomial W)
    (i α j β : Fin 3) (δ : ℝ) (y : Y) : ℂ :=
  (y 2:ℂ)^n*H (scale δ y)*firstScaled χ p δ i α y*star (firstScaled χ q δ j β y)

lemma mixed_scaled_bound (n : ℕ) {H χ : Y → ℂ} (hH : Continuous H) (hcH : HasCompactSupport H)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcχ : HasCompactSupport χ)
    (p q : Polynomial W) (i α j β : Fin 3) :
    OrderBound (mixedScaled n H χ p q i α j β) 0 := by
  exact (((normal_power_bound n).mul (compact_scaled hH hcH)).mul
    (first_scaled_bound hχ hcχ p i α)).mul (OrderBound.conj (first_scaled_bound hχ hcχ q j β))

lemma mixed_scaled_continuous (n : ℕ) {H χ : Y → ℂ} (hH : Continuous H)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (p q : Polynomial W) (i α j β : Fin 3) (δ : ℝ) :
    Continuous (mixedScaled n H χ p q i α j β δ) :=
  (((Complex.continuous_ofReal.comp (continuous_apply 2)).pow n |>.mul
    (hH.comp (scale δ).continuous)).mul (first_scaled_continuous hχ p δ i α)).mul
    (first_scaled_continuous hχ q δ j β).star

/-- The coefficient at the base point is extracted from the exact mixed
boundary energy. Corrections of every positive parameter order disappear. -/
theorem mixed_scaled_limit (n : ℕ) {H χ : Y → ℂ} (hH : Continuous H) (hcH : HasCompactSupport H)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcχ : HasCompactSupport χ) (h0 : χ 0=1)
    (p q : Polynomial W) (i α j β : Fin 3) :
    Tendsto (fun δ => ∫ y, weight 2 y • mixedScaled n H χ p q i α j β δ y) (𝓝[>] 0)
      (𝓝 (∫ y : Y, weight 2 y • ((y 2:ℂ)^n*H 0*
        value (E₀ α (p.coeff 0 i)) y*star (value (E₀ β (q.coeff 0 j)) y)))) := by
  apply weighted_tendsto (mixed_scaled_bound n hH hcH hχ hcχ p q i α j β)
    (mixed_scaled_continuous n hH hχ p q i α j β) _ (by norm_num)
  intro y
  have hHt : Tendsto (fun δ => H (scale δ y)) (𝓝[>] 0) (𝓝 (H 0)) :=
    (hH.tendsto 0 |>.comp (scale_tendsto_zero y)).mono_left nhdsWithin_le_nhds
  exact ((tendsto_const_nhds.mul hHt).mul (firstScaled_tendsto hχ h0 p i α y)).mul
    (firstScaled_tendsto hχ h0 q j β y).star

end ElasticityBoundaryEnergyLimit
namespace ElasticityBoundaryMixedScaling
/-! Exact physical mixed-energy Jacobian cancellation, followed by the actual
boundary limit. These integrals contain literal Frechet derivatives of the
cut-off corrected fields. -/
open Set Filter MeasureTheory
open scoped Topology BigOperators
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryScaling ElasticityBoundaryWeights ElasticityBoundaryOrderBound
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundaryCutoffParametrix ElasticityBoundaryLimit
  ElasticityBoundaryProfileBounds ElasticityBoundaryCutoffLayer ElasticityBoundaryProfile
  ElasticityBoundaryCutoffBound ElasticityBoundaryEnergyLimit ElasticityBoundaryStrongLayer
abbrev Y := Fin 3 → ℝ

lemma envelope_product_weight (δ : ℝ) (g : Y → ℂ) (y : Y) :
    halfspace.indicator (fun z => envelope δ z*star (envelope δ z)*g z) y=
      weight 2 y • g y := by
  have h := profile_square_weight δ (C 1) y
  simp only [profile,value_C,mul_one,norm_one,one_pow,one_mul] at h
  change halfspace.indicator (fun z => ‖envelope δ z‖^2) y=weight 2 y at h
  by_cases hy : y∈halfspace
  · rw [indicator_of_mem hy] at h ⊢
    rw [show envelope δ y*star (envelope δ y)=(‖envelope δ y‖:ℂ)^2 from Complex.mul_conj' _]
    rw [← Complex.ofReal_pow,h,Complex.real_smul]
  · rw [indicator_of_notMem hy] at h ⊢
    rw [← h,zero_smul]

lemma integral_envelope_mixed (δ : ℝ) (g : Y → ℂ) :
    (∫ y in halfspace, envelope δ y*star (envelope δ y)*g y)=
      ∫ y, weight 2 y • g y := by
  rw [← integral_indicator measurable_halfspace]
  exact integral_congr_ae (Eventually.of_forall (envelope_product_weight δ g))

def mixedEnergy (n : ℕ) (H χ : Y → ℂ) (p q : Polynomial W)
    (i α j β : Fin 3) (δ : ℝ) : ℂ :=
  ∫ z in halfspace, (z 2:ℂ)^n*H z*dpart (cutoffLayer χ p δ i) α z*
    star (dpart (cutoffLayer χ q δ j) β z)

/-- The factor delta^(2n) comes from the true normal coordinate, while the
volume delta^4 cancels the two true first derivatives delta^-2. -/
theorem mixedEnergy_scaled (n : ℕ) (H : Y → ℂ) {χ : Y → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (p q : Polynomial W) (i α j β : Fin 3)
    {δ : ℝ} (hδ : δ≠0) :
    ((δ^(2*n))⁻¹:ℝ) • mixedEnergy n H χ p q i α j β δ=
      ∫ y, weight 2 y • mixedScaled n H χ p q i α j β δ y := by
  unfold mixedEnergy
  rw [integralOn_scale hδ]
  have he (y : Y) :
      ((scale δ y 2:ℝ):ℂ)^n*H (scale δ y)*dpart (cutoffLayer χ p δ i) α (scale δ y)*
        star (dpart (cutoffLayer χ q δ j) β (scale δ y))=
      (δ^(2*n)*(δ^4)⁻¹:ℝ) • (envelope δ y*star (envelope δ y)*
        mixedScaled n H χ p q i α j β δ y) := by
    rw [first_scaled_identity hχ hδ,first_scaled_identity hχ hδ]
    simp only [scale_apply,scaleFactor,ite_true,Complex.real_smul,star_mul,Complex.star_def,
      Complex.conj_ofReal,mixedScaled]
    push_cast
    rw [mul_pow,← pow_mul]
    have hd : (δ:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hδ
    field_simp
  simp_rw [he]
  rw [integral_smul,integral_envelope_mixed,smul_smul,smul_smul]
  have hs : ((δ^(2*n))⁻¹*δ^4)*(δ^(2*n)*(δ^4)⁻¹)=1 := by field_simp
  rw [hs,one_smul]

theorem mixedEnergy_limit (n : ℕ) {H χ : Y → ℂ} (hH : Continuous H) (hcH : HasCompactSupport H)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcχ : HasCompactSupport χ) (h0 : χ 0=1)
    (p q : Polynomial W) (i α j β : Fin 3) :
    Tendsto (fun δ => ((δ^(2*n))⁻¹:ℝ) • mixedEnergy n H χ p q i α j β δ) (𝓝[>] 0)
      (𝓝 (∫ y : Y, weight 2 y • ((y 2:ℂ)^n*H 0*
        value (E₀ α (p.coeff 0 i)) y*star (value (E₀ β (q.coeff 0 j)) y)))) := by
  apply (mixed_scaled_limit n hH hcH hχ hcχ h0 p q i α j β).congr'
  filter_upwards [eventually_small_positive] with δ hδ
  exact (mixedEnergy_scaled n H hχ p q i α j β hδ.1.ne').symm

end ElasticityBoundaryMixedScaling
namespace ElasticityBoundaryPacket
/-! Exact physical variational packet energy, with its true compact chart
Jacobian, equals the finite mixed coordinate-energy integrals. -/
open Set Filter MeasureTheory
open scoped Topology BigOperators
open Elasticity ElasticityBoundaryDensityPull ElasticityBoundaryEnergyChart
  ElasticityBoundaryPacketMass ElasticityBoundaryPhysicalMass ElasticityBoundaryCutoffLayer
  ElasticityBoundaryStrongLayer ElasticityBoundaryMixedScaling ElasticityBoundaryGradientTransfer
  ElasticityBoundaryChartOperator ElasticityBoundaryMVNormal ElasticityBoundaryPhysicalTransfer
  ElasticityBoundaryCutoffParametrix ElasticityBoundaryActualTower

variable {Ω : Set X} {x : X}

lemma Setup.energy_chart (s : Setup Ω x) (hΩ : MeasurableSet Ω) {l m : X → ℝ}
    (hl : BoundedCoefficient Ω l) (hm : BoundedCoefficient Ω m) (p q : Polynomial W) (δ : ℝ) :
    complexTrialEnergy l m (s.trial p δ) (s.trial q δ)=
      ∫ y in ElasticityBoundaryProfileBounds.halfspace,
        tensorDensity (fun i α j β => s.rawCoeff (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) i α j β y)
          (fun i α => dpart (cutoffLayer s.cutoff p δ i) α y)
          (fun i α => dpart (cutoffLayer s.cutoff q δ i) α y) := by
  rw [Setup.trial,Setup.trial,complexFieldTrial_energy hl hm]
  have he := compact_chart_integral_complex volume s.e s.smooth s.source hΩ measurable_H s.inside
    s.Φ_germ
    (fun z => complexDensity (l z) (m z) (fieldGradient (s.field p δ) z) (fieldGradient (s.field q δ) z))
    (fun y : X => tensorDensity (fun i α j β => principal s.Q s.Φ s.Ψ
      (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) i α j β y.ofLp)
      (fun i α => dpart (cutoffLayer s.cutoff p δ i) α y.ofLp)
      (fun i α => dpart (cutoffLayer s.cutoff q δ i) α y.ofLp))
    (physical_density_support s.image_compact.isClosed l m _ _ (s.field_support p δ))
    (chart_density_support s.compact.isClosed _ _ _ (s.cutoff_layer_support p δ))
    (fun y hy => density_chart_all s.e s.compact s.source s.η_support s.η_one s.Q _ _
      (smooth_cutoffLayer s.cutoff_smooth p δ) (smooth_cutoffLayer s.cutoff_smooth q δ)
      (s.cutoff_layer_support p δ) (s.cutoff_layer_support q δ) s.Φ s.Ψ s.Ψ_smooth
      (fun z hz => (s.Φ_germ z hz).eq_of_nhds) s.Ψ_germ l m hy)
  rw [he]
  rw [← integral_ofLp (fun y => tensorDensity (fun i α j β =>
    s.rawCoeff (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) i α j β y)
    (fun i α => dpart (cutoffLayer s.cutoff p δ i) α y)
    (fun i α => dpart (cutoffLayer s.cutoff q δ i) α y))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    simp only [tensorDensity,Setup.rawCoeff,Setup.jacobian,WithLp.toLp_ofLp,
      Complex.real_smul,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro α _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro β _
    ring)

lemma Setup.energy_compact_tensor (s : Setup Ω x) (hΩ : MeasurableSet Ω) {l m : X → ℝ}
    (hl : BoundedCoefficient Ω l) (hm : BoundedCoefficient Ω m)
    (H : I → I → I → I → Y → ℂ)
    (hH : ∀ i α j β y, WithLp.toLp 2 y∈s.K → H i α j β y=
      s.rawCoeff (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) i α j β y)
    (p q : Polynomial W) (δ : ℝ) :
    complexTrialEnergy l m (s.trial p δ) (s.trial q δ)=
      ∫ y in ElasticityBoundaryProfileBounds.halfspace,
        tensorDensity (fun i α j β => H i α j β y)
          (fun i α => dpart (cutoffLayer s.cutoff p δ i) α y)
          (fun i α => dpart (cutoffLayer s.cutoff q δ i) α y) := by
  rw [s.energy_chart hΩ hl hm]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  by_cases hy : WithLp.toLp 2 y∈s.K
  · simp only [hH _ _ _ _ y hy]
  · have hdp (i α : I) : dpart (cutoffLayer s.cutoff p δ i) α y=0 :=
      Function.notMem_support.mp (fun h => hy
        (dpart_support_lifted s.compact.isClosed (s.cutoff_layer_support p δ i) α h))
    simp only [tensorDensity,hdp,mul_zero,zero_mul,Finset.sum_const_zero]

lemma Setup.energy_sum (s : Setup Ω x) (hΩ : MeasurableSet Ω) {l m : X → ℝ}
    (hl : BoundedCoefficient Ω l) (hm : BoundedCoefficient Ω m)
    (H : I → I → I → I → Y → ℂ)
    (hHc : ∀ i α j β, Continuous (H i α j β))
    (hHs : ∀ i α j β, HasCompactSupport (H i α j β))
    (hH : ∀ i α j β y, WithLp.toLp 2 y∈s.K → H i α j β y=
      s.rawCoeff (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) i α j β y)
    (p q : Polynomial W) (δ : ℝ) :
    complexTrialEnergy l m (s.trial p δ) (s.trial q δ)=
      ∑ i, ∑ α, ∑ j, ∑ β, mixedEnergy 0 (H i α j β) s.cutoff p q i α j β δ := by
  rw [s.energy_compact_tensor hΩ hl hm H hH]
  have hInt (i α j β : I) : Integrable (fun y => H i α j β y*
      dpart (cutoffLayer s.cutoff p δ i) α y*star (dpart (cutoffLayer s.cutoff q δ j) β y)) :=
    (((hHc i α j β).mul (smooth_dpart (smooth_cutoffLayer s.cutoff_smooth p δ i) α).continuous).mul
      (smooth_dpart (smooth_cutoffLayer s.cutoff_smooth q δ j) β).continuous.star).integrable_of_hasCompactSupport
        ((hHs i α j β).mul_right.mul_right)
  simp only [tensorDensity,mixedEnergy,pow_zero,one_mul]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun α _ =>
    integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun β _ => (hInt i α j β).integrableOn))))]
  apply Finset.sum_congr rfl; intro i _
  rw [integral_finsetSum _ (fun α _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun β _ => (hInt i α j β).integrableOn)))]
  apply Finset.sum_congr rfl; intro α _
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun β _ => (hInt i α j β).integrableOn))]
  apply Finset.sum_congr rfl; intro j _
  exact integral_finsetSum _ (fun β _ => (hInt i α j β).integrableOn)

end ElasticityBoundaryPacket
namespace ElasticityBoundaryPacket
/-! The actual variational energy difference extracts a true normal factor of
the coefficient difference. No equality in a boundary neighborhood is used. -/
open Set Filter MeasureTheory
open scoped Topology BigOperators
open Elasticity ElasticityBoundaryMixedScaling ElasticityBoundaryMVNormal
  ElasticityBoundaryCutoffLayer ElasticityBoundaryStrongLayer ElasticityBoundaryDensityPull
  ElasticityBoundaryGradientTransfer ElasticityBoundaryProfileBounds
variable {Ω : Set X} {x : X}

lemma mixed_integrable (n : ℕ) {H χ : Y → ℂ} (hH : Continuous H) (hcH : HasCompactSupport H)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (p q : Polynomial W) (i α j β : I) (δ : ℝ) :
    Integrable (fun y => (y 2:ℂ)^n*H y*dpart (cutoffLayer χ p δ i) α y*
      star (dpart (cutoffLayer χ q δ j) β y)) :=
  ((((Complex.continuous_ofReal.comp (continuous_apply 2)).pow n |>.mul hH).mul
    (smooth_dpart (smooth_cutoffLayer hχ p δ i) α).continuous).mul
    (smooth_dpart (smooth_cutoffLayer hχ q δ j) β).continuous.star).integrable_of_hasCompactSupport
      (hcH.mul_left.mul_right.mul_right)

lemma Setup.energy_difference_normal (s : Setup Ω x) (hΩ : MeasurableSet Ω)
    {l₁ m₁ l₂ m₂ : X → ℝ}
    (hl₁ : ContDiff ℝ (⊤ : ℕ∞) l₁) (hm₁ : ContDiff ℝ (⊤ : ℕ∞) m₁)
    (hl₂ : ContDiff ℝ (⊤ : ℕ∞) l₂) (hm₂ : ContDiff ℝ (⊤ : ℕ∞) m₂)
    (hb₁ : BoundedCoefficient Ω l₁) (hc₁ : BoundedCoefficient Ω m₁)
    (hb₂ : BoundedCoefficient Ω l₂) (hc₂ : BoundedCoefficient Ω m₂)
    (n : ℕ) (H : I → I → I → I → Y → ℂ)
    (hH : ∀ i α j β y, WithLp.toLp 2 y∈s.K →
      s.rawCoeff (fun z => (l₁ z:ℂ)) (fun z => (m₁ z:ℂ)) i α j β y-
      s.rawCoeff (fun z => (l₂ z:ℂ)) (fun z => (m₂ z:ℂ)) i α j β y=(y 2:ℂ)^n*H i α j β y)
    (p q : Polynomial W) (δ : ℝ) :
    complexTrialEnergy l₁ m₁ (s.trial p δ) (s.trial q δ)-
      complexTrialEnergy l₂ m₂ (s.trial p δ) (s.trial q δ)=
      ∑ i, ∑ α, ∑ j, ∑ β, mixedEnergy n (H i α j β) s.cutoff p q i α j β δ := by
  obtain ⟨H₁,hH₁,hH₁c,hE₁⟩ := s.compact_energy_coefficients
    (Complex.ofRealCLM.contDiff.comp hl₁) (Complex.ofRealCLM.contDiff.comp hm₁)
  obtain ⟨H₂,hH₂,hH₂c,hE₂⟩ := s.compact_energy_coefficients
    (Complex.ofRealCLM.contDiff.comp hl₂) (Complex.ofRealCLM.contDiff.comp hm₂)
  rw [s.energy_sum hΩ hb₁ hc₁ H₁ hH₁ hH₁c hE₁,s.energy_sum hΩ hb₂ hc₂ H₂ hH₂ hH₂c hE₂]
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro α _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro β _
  unfold mixedEnergy
  rw [← integral_sub (mixed_integrable 0 (hH₁ i α j β) (hH₁c i α j β) s.cutoff_smooth p q i α j β δ).integrableOn
    (mixed_integrable 0 (hH₂ i α j β) (hH₂c i α j β) s.cutoff_smooth p q i α j β δ).integrableOn]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  simp only [pow_zero,one_mul,← sub_mul]
  by_cases hy : WithLp.toLp 2 y∈s.K
  · rw [hE₁ _ _ _ _ y hy,hE₂ _ _ _ _ y hy]
    exact congrArg (fun a : ℂ => a*dpart (cutoffLayer s.cutoff p δ i) α y*
      star (dpart (cutoffLayer s.cutoff q δ j) β y)) (hH i α j β y hy)
  · have hp : dpart (cutoffLayer s.cutoff p δ i) α y=0 :=
      Function.notMem_support.mp (fun h => hy
        (dpart_support_lifted s.compact.isClosed (s.cutoff_layer_support p δ i) α h))
    simp only [hp,mul_zero,zero_mul]

end ElasticityBoundaryPacket
namespace ElasticityBoundaryPacket
/-! Direct extraction of every factored normal coefficient by the real physical
DN map and the genuine physical localized asymptotic tests. -/
open Set Filter MeasureTheory
open scoped Topology BigOperators
open Elasticity ElasticityBoundaryMVNormal ElasticityBoundaryMixedScaling
  ElasticityBoundaryLimit ElasticityBoundaryMVCalculus ElasticityBoundaryWeights
  ElasticityBoundaryTensorSeries ElasticityBoundaryParameter
variable {Ω : Set X} {x : X}

lemma normalized_tendsto_zero (n : ℕ) {f : ℝ → ℂ} {C : ℝ}
    (hf : ∀ δ : ℝ, 0<δ → δ≤1 → ‖f δ‖≤C*δ^(2*n+1)) :
    Tendsto (fun δ => ((δ^(2*n))⁻¹:ℝ) • f δ) (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun δ => C*δ)
  · filter_upwards [eventually_small_positive] with δ hδ
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hδ.1.le _))]
    apply (mul_le_mul_of_nonneg_left (hf δ hδ.1 hδ.2)
      (inv_nonneg.mpr (pow_nonneg hδ.1.le _))).trans_eq
    rw [pow_succ]
    field_simp [hδ.1.ne']
  · simpa using (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds) :
      Tendsto (fun δ : ℝ => C*δ) (𝓝[>] 0) (𝓝 (C*0)))

def frozenPair (n : ℕ) (a : I → I → I → I → ℂ) (p q : W) : ℂ :=
  ∑ i, ∑ α, ∑ j, ∑ β, ∫ y : Y, weight 2 y • ((y 2:ℂ)^n*a i α j β*
    value (E₀ α (p i)) y*star (value (E₀ β (q j)) y))

/-- Any actual normal factor of the pulled tensor is detected. The hypothesis
is an exact factorization on the packet support, not a boundary agreement
assumption and not an abstract conclusion-carrying jet interface. -/
lemma Setup.extract_normal (s : Setup Ω x) {l₁ m₁ l₂ m₂ : X → ℝ}
    (hl₁ : ContDiff ℝ (⊤ : ℕ∞) l₁) (hm₁ : ContDiff ℝ (⊤ : ℕ∞) m₁)
    (hl₂ : ContDiff ℝ (⊤ : ℕ∞) l₂) (hm₂ : ContDiff ℝ (⊤ : ℕ∞) m₂)
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω) (hx : x∈closure Ω)
    (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂)
    (n : ℕ) (H : I → I → I → I → Y → ℂ)
    (hHc : ∀ i α j β, Continuous (H i α j β))
    (hHs : ∀ i α j β, HasCompactSupport (H i α j β))
    (hH : ∀ i α j β y, WithLp.toLp 2 y∈s.K →
      s.rawCoeff (fun z => (l₁ z:ℂ)) (fun z => (m₁ z:ℂ)) i α j β y-
      s.rawCoeff (fun z => (l₂ z:ℂ)) (fun z => (m₂ z:ℂ)) i α j β y=(y 2:ℂ)^n*H i α j β y)
    (p₀ q₀ : W) (hp₀ : normal (l₁ x) (m₁ x) p₀=0) (hq₀ : normal (l₂ x) (m₂ x) q₀=0) :
    frozenPair n (fun i α j β => H i α j β 0) p₀ q₀=0 := by
  obtain ⟨p,q,hp,hq,C,_hC,hEst⟩ := s.paired_packets hl₁ hm₁ hl₂ hm₂ ha₁ ha₂
    hO hB hx hDN p₀ q₀ hp₀ hq₀ (2*n+1)
  have he (δ : ℝ) := s.energy_difference_normal hO.measurableSet hl₁ hm₁ hl₂ hm₂
    (ha₁.1.boundedCoefficient hO hB) (ha₁.2.1.boundedCoefficient hO hB)
    (ha₂.1.boundedCoefficient hO hB) (ha₂.2.1.boundedCoefficient hO hB) n H hH p q δ
  have ht := normalized_tendsto_zero n hEst
  have hlim := tendsto_finsetSum Finset.univ (fun i _ => tendsto_finsetSum Finset.univ
    (fun α _ => tendsto_finsetSum Finset.univ (fun j _ => tendsto_finsetSum Finset.univ
      (fun β _ => mixedEnergy_limit n (hHc i α j β) (hHs i α j β) s.cutoff_smooth
        s.cutoff_compact s.cutoff_one.eq_of_nhds p q i α j β))))
  have ht' : Tendsto (fun δ => ∑ i, ∑ α, ∑ j, ∑ β,
      ((δ^(2*n))⁻¹:ℝ) • mixedEnergy n (H i α j β) s.cutoff p q i α j β δ)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [he,Finset.smul_sum] using ht
  have hEq := tendsto_nhds_unique hlim ht'
  simpa only [frozenPair,hp,hq] using hEq

end ElasticityBoundaryPacket

end

end OAI
