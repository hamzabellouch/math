import OAI.MathematicalPhysics.Elasticity.BoundaryCharts

namespace OAI

section
/-! Physical displacements obtained from compact chart fields. Their literal
strong Lamé force is the constructed curved-coordinate operator on the
whole trial support, rather than a formally equated auxiliary DN system. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryPhysicalTransfer
open ElasticityBoundary ElasticityBoundaryChainRule ElasticityBoundaryPullback
  ElasticityBoundaryPhysicalStrong ElasticityBoundaryRotation ElasticityBoundaryFrameOperator
  ElasticityBoundaryChartOperator ElasticityBoundaryOperatorLocal ElasticityBoundaryStrongLayer
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I
abbrev Y := I → ℝ

def lifted (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ) (i : I) (z : X) : ℂ :=
  mix (frameMatrix Q) u i z.ofLp

def transferred (e : OpenPartialHomeomorph X X) (η : X → ℝ)
    (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ) (i : I) : X → ℂ :=
  chartTransfer e η (lifted Q u i)

def force (l m : X → ℂ) (u : I → X → ℂ) : I → X → ℂ :=
  directional basis (coeff l m) (lower basis l m) u

lemma smooth_lifted (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i : I) :
    ContDiff ℝ (⊤ : ℕ∞) (lifted Q u i) :=
  (smooth_mix (frameMatrix Q) u hu i).comp PiLp.contDiff_ofLp

lemma smooth_transferred (e : OpenPartialHomeomorph X X)
    (hi : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {η : X → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hs : tsupport η⊆e.target)
    (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i : I) :
    ContDiff ℝ (⊤ : ℕ∞) (transferred e η Q u i) :=
  smooth_chartTransfer e hi hη hs (smooth_lifted Q u hu i)

lemma support_lifted (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ) {K : Set X}
    (hu : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K) (i : I) :
    Function.support (lifted Q u i)⊆K := by
  intro x hx
  by_contra hn
  apply hx
  change (∑ j, frameMatrix Q i j*u j x.ofLp)=0
  apply Finset.sum_eq_zero
  intro j _
  have hz : u j x.ofLp=0 := Function.notMem_support.mp (fun hh => hn (hu j hh))
  rw [hz,mul_zero]

lemma support_transferred (e : OpenPartialHomeomorph X X) {η : X → ℝ}
    (hs : tsupport η⊆e.target) (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ) {K : Set X}
    (hu : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K) (i : I) :
    Function.support (transferred e η Q u i)⊆e '' K :=
  chartTransfer_support e hs (support_lifted Q u hu i)

lemma transferred_germ (e : OpenPartialHomeomorph X X) {K : Set X}
    {η : X → ℝ} (hη : ∀ z∈e '' K, η z=1)
    (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
    (hu : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K) {x : X} (hx : x∈e.target)
    {Ψ : X → X} (hΨ : Ψ =ᶠ[𝓝 x] e.symm) (i : I) :
    transferred e η Q u i =ᶠ[𝓝 x]
      mix (frameMatrix Q) (fun j z => u j (Ψ z).ofLp) i :=
  chartTransfer_extension_germ e hη (support_lifted Q u hu i) hx hΨ

lemma chart_force (Q : X ≃ₗᵢ[ℝ] X) (Φ : Y → X) {ψ : X → Y}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {l m : X → ℂ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (u : I → Y → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j))
    (y : Y) (hy : ψ (Φ y)=y) (s : I) :
    (∑ i, frameMatrix Q i s*force l m (mix (frameMatrix Q) (fun j x => u j (ψ x))) i (Φ y))=
      strong (chartPrincipal Q Φ ψ l m) (chartLower Q Φ ψ l m) u s y := by
  calc
    _ = ∑ i, frameMatrix Q i s*(∑ k, dd
        (stress basis l m (mix (frameMatrix Q) (fun j x => u j (ψ x))) i k) (basis k) (Φ y)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply congrArg (fun z => frameMatrix Q i s*z)
      exact (stress_divergence basis hl hm _
        (fun j => smooth_mix (frameMatrix Q) _ (fun k => (hu k).comp hψ) j) i (Φ y)).symm
    _ = _ := physical_chart_operator Q Φ hψ hl hm u hu y hy s

/-- The exact coordinate operator controls the genuine transferred physical
force at every point of the compact trial support. -/
theorem transferred_force (e : OpenPartialHomeomorph X X) {K : Set X}
    (hK : K⊆e.source) {η : X → ℝ} (hη : ∀ z∈e '' K, η z=1)
    (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
    (hus : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j))
    (Φ Ψ : X → X) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    {l m : X → ℂ} (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (y : Y) (hy : WithLp.toLp 2 y∈K)
    (hΦy : Φ (WithLp.toLp 2 y)=e (WithLp.toLp 2 y))
    (hΨy : Ψ =ᶠ[𝓝 (e (WithLp.toLp 2 y))] e.symm) (s : I) :
    (∑ i, frameMatrix Q i s*force l m (transferred e η Q u) i (e (WithLp.toLp 2 y)))=
      strong (chartPrincipal Q (fun z => Φ (WithLp.toLp 2 z)) (fun z => (Ψ z).ofLp) l m)
        (chartLower Q (fun z => Φ (WithLp.toLp 2 z)) (fun z => (Ψ z).ofLp) l m) u s y := by
  have hx := e.map_source (hK hy)
  have hg := transferred_germ e hη Q u hus hx hΨy
  have hid : (Ψ (Φ (WithLp.toLp 2 y))).ofLp=y := by
    rw [hΦy,hΨy.eq_of_nhds,e.left_inv (hK hy)]
  calc
    _ = ∑ i, frameMatrix Q i s*force l m
        (mix (frameMatrix Q) (fun j z => u j (Ψ z).ofLp)) i (e (WithLp.toLp 2 y)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z => frameMatrix Q i s*z)
        (directional_germ_eq basis (coeff l m) (lower basis l m) hg i)
    _ = _ := by
      rw [← hΦy]
      exact chart_force Q (fun z => Φ (WithLp.toLp 2 z))
        (PiLp.contDiff_ofLp.comp hΨ) hl hm u hu y hid s

end ElasticityBoundaryPhysicalTransfer

end
end
section
/-! Pointwise all-order cutoff bounds. These bounds feed exactly the same
weighted-mass estimate used for the smooth coefficient Taylor error. -/
noncomputable section
open Set
namespace ElasticityBoundaryCutoffBound
open ElasticityBoundaryOrderBound ElasticityBoundaryScaling
abbrev Y := Fin 3 → ℝ

lemma bounded_scaled {f : Y → ℂ} {M : ℝ} (hM : 0≤M) (hf : ∀ y, ‖f y‖≤M) :
    OrderBound (fun δ y => f (scale δ y)) 0 := by
  exact ⟨M,hM,0,fun δ _ _ y => by simpa using hf (scale δ y)⟩

lemma compact_scaled {f : Y → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    OrderBound (fun δ y => f (scale δ y)) 0 := by
  obtain ⟨M,hM⟩ := hf.bounded_above_of_compact_support hc
  exact bounded_scaled (le_trans (norm_nonneg (f 0)) (hM 0))
    hM

/-- A bounded coefficient vanishing on a fixed neighborhood of the base
point yields every power of the true concentration parameter. -/
theorem flat_scaled {f : Y → ℂ} {M r : ℝ} (hM : 0≤M) (hr : 0<r)
    (hf : ∀ y, ‖f y‖≤M) (hz : ∀ y, ‖y‖<r → f y=0) (N : ℕ) :
    OrderBound (fun δ y => f (scale δ y)) N := by
  refine ⟨M/r^N,by positivity,N,fun δ hδ hδ1 y => ?_⟩
  change ‖f (scale δ y)‖ ≤ _
  by_cases hy : ‖scale δ y‖<r
  · rw [hz _ hy, norm_zero]
    positivity
  · have hy' : r≤δ*‖y‖ := (le_of_not_gt hy).trans (scale_norm_le hδ.le hδ1 y)
    calc
      _ ≤ M := hf _
      _ = (M/r^N)*r^N := (div_mul_cancel₀ M (pow_pos hr N).ne').symm
      _ ≤ (M/r^N)*(δ*‖y‖)^N := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hr.le hy' N) (by positivity)
      _ = (M/r^N)*δ^N*‖y‖^N := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg y) (by linarith) N) (by positivity)

lemma compact_flat_scaled {f : Y → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hz : f =ᶠ[nhds (0:Y)] 0) (N : ℕ) :
    OrderBound (fun δ y => f (scale δ y)) N := by
  obtain ⟨M,hM⟩ := hf.bounded_above_of_compact_support hc
  obtain ⟨r,hr,hrf⟩ := Metric.mem_nhds_iff.mp hz
  apply flat_scaled (le_trans (norm_nonneg (f 0)) (hM 0)) hr
    hM
  intro y hy
  exact hrf (by simpa only [Metric.mem_ball, dist_zero_right] using hy)

end ElasticityBoundaryCutoffBound

end
end
section
/-! Cut off actual boundary fields. The complete product-rule residual is
retained; its derivatives are flat at the concentration point. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace ElasticityBoundaryCutoffLayer
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundarySmoothOperator ElasticityBoundaryProfile
  ElasticityBoundaryProfileBounds ElasticityBoundaryScaling ElasticityBoundaryLayerOperator
  ElasticityBoundaryWeights ElasticityBoundaryStrongLayer ElasticityBoundaryOrderBound
  ElasticityBoundaryCutoffBound
abbrev Y := Fin 3 → ℝ

lemma smooth_dpart {f : Y → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (dpart f j) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma compact_dpart {f : Y → ℂ} (hf : HasCompactSupport f) (j : Fin 3) :
    HasCompactSupport (dpart f j) := HasCompactSupport.fderiv_apply ℝ hf _

lemma dpart_eventually_zero {f : Y → ℂ} {c : ℂ} (hf : f =ᶠ[𝓝 (0:Y)] fun _ => c)
    (j : Fin 3) : dpart f j =ᶠ[𝓝 (0:Y)] 0 := by
  filter_upwards [hf.fderiv (𝕜 := ℝ)] with y hy
  simp only [dpart, hy, fderiv_const_apply, zero_apply, Pi.zero_apply]

lemma dpart_mul {f g : Y → ℂ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (j : Fin 3) (y : Y) :
    dpart (fun z => f z*g z) j y=dpart f j y*g y+f y*dpart g j y := by
  rw [dpart, fderiv_fun_mul (hf y) (hg y)]
  simp only [add_apply, smul_apply, smul_eq_mul, dpart]
  ring

lemma second_mul {f g : Y → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (α β : Fin 3) (y : Y) :
    dpart (dpart (fun z => f z*g z) β) α y =
      dpart (dpart f β) α y*g y+dpart f β y*dpart g α y+
      (dpart f α y*dpart g β y+f y*dpart (dpart g β) α y) := by
  have heq : dpart (fun z => f z*g z) β = fun z => dpart f β z*g z+f z*dpart g β z :=
    funext (fun z => dpart_mul (hf.differentiable (by simp)) (hg.differentiable (by simp)) β z)
  rw [heq, dpart, fderiv_fun_add
    (((smooth_dpart hf β).mul hg).differentiable (by simp) y)
    ((hf.mul (smooth_dpart hg β)).differentiable (by simp) y), add_apply]
  change dpart (fun z => dpart f β z*g z) α y+dpart (fun z => f z*dpart g β z) α y=_
  rw [dpart_mul ((smooth_dpart hf β).differentiable (by simp)) (hg.differentiable (by simp)),
    dpart_mul (hf.differentiable (by simp)) ((smooth_dpart hg β).differentiable (by simp))]

/-- All cutoff product terms, before taking an absolute value or norm. -/
def cutoffCorrection (a : SmoothTensor) (b : SmoothLower) (χ : Y → ℂ)
    (q : Polynomial W) (δ : ℝ) (i : Fin 3) (y : Y) : ℂ :=
  (δ:ℂ)^2 * (∑ α, ∑ j, ∑ β, a i α j β (scale δ y) *
    (dpart χ β (scale δ y)*value (atParameter (PD α (unpack j q)) δ) y+
     dpart χ α (scale δ y)*value (atParameter (PD β (unpack j q)) δ) y)) +
  (δ:ℂ)^4 * ((∑ α, ∑ j, ∑ β, a i α j β (scale δ y) *
    dpart (dpart χ β) α (scale δ y)*value (atParameter (unpack j q) δ) y)+
    ∑ j, ∑ β, b i j β (scale δ y)*dpart χ β (scale δ y)*
      value (atParameter (unpack j q) δ) y)

def cutoffScaled (a : SmoothTensor) (b : SmoothLower) (χ : Y → ℂ)
    (q : Polynomial W) (δ : ℝ) (i : Fin 3) (y : Y) : ℂ :=
  χ (scale δ y)*scaledOperator a b q δ i y+cutoffCorrection a b χ q δ i y

lemma correction_order_bound (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, Continuous (a i α j β) ∧ HasCompactSupport (a i α j β))
    (hb : ∀ i j β, Continuous (b i j β) ∧ HasCompactSupport (b i j β))
    {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχ0 : χ =ᶠ[𝓝 (0:Y)] fun _ => 1) (q : Polynomial W) (N : ℕ) (i : Fin 3) :
    OrderBound (fun δ y => cutoffCorrection a b χ q δ i y) N := by
  have hd (α : Fin 3) := compact_flat_scaled (smooth_dpart hχ α).continuous
    (compact_dpart hc α) (dpart_eventually_zero hχ0 α) N
  have hdd (α β : Fin 3) := compact_flat_scaled (smooth_dpart (smooth_dpart hχ β) α).continuous
    (compact_dpart (compact_dpart hc β) α)
    (dpart_eventually_zero (dpart_eventually_zero hχ0 β) α) N
  have hA : OrderBound (fun δ y => ∑ α, ∑ j, ∑ β, a i α j β (scale δ y) *
      (dpart χ β (scale δ y)*value (atParameter (PD α (unpack j q)) δ) y+
       dpart χ α (scale δ y)*value (atParameter (PD β (unpack j q)) δ) y)) N := by
    apply OrderBound.sum
    intro α _
    apply OrderBound.sum
    intro j _
    apply OrderBound.sum
    intro β _
    simpa only [Nat.add_zero, Nat.zero_add] using
      (compact_scaled (ha i α j β).1 (ha i α j β).2).mul
        (((hd β).mul (parameter_bound (PD α (unpack j q)))).add
         ((hd α).mul (parameter_bound (PD β (unpack j q)))))
  have hB : OrderBound (fun δ y => ∑ α, ∑ j, ∑ β, a i α j β (scale δ y) *
      dpart (dpart χ β) α (scale δ y)*value (atParameter (unpack j q) δ) y) N := by
    apply OrderBound.sum
    intro α _
    apply OrderBound.sum
    intro j _
    apply OrderBound.sum
    intro β _
    simpa only [Nat.add_zero, Nat.zero_add] using
      ((compact_scaled (ha i α j β).1 (ha i α j β).2).mul (hdd α β)).mul
        (parameter_bound (unpack j q))
  have hC : OrderBound (fun δ y => ∑ j, ∑ β, b i j β (scale δ y)*dpart χ β (scale δ y)*
      value (atParameter (unpack j q) δ) y) N := by
    apply OrderBound.sum
    intro j _
    apply OrderBound.sum
    intro β _
    simpa only [Nat.add_zero, Nat.zero_add] using
      ((compact_scaled (hb i j β).1 (hb i j β).2).mul (hd β)).mul
        (parameter_bound (unpack j q))
  exact (((power_bound 2).mul hA).weaken (by omega)).add
    (((power_bound 4).mul (hB.add hC)).weaken (by omega))

def cutoffLayer (χ : Y → ℂ) (q : Polynomial W) (δ : ℝ) (j : Fin 3) (z : Y) : ℂ :=
  χ z*layer q δ j z

lemma smooth_cutoffLayer {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (q : Polynomial W) (δ : ℝ) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffLayer χ q δ j) :=
  hχ.mul (smooth_physicalProfile δ _)

lemma compact_cutoffLayer {χ : Y → ℂ} (hχ : HasCompactSupport χ)
    (q : Polynomial W) (δ : ℝ) (j : Fin 3) :
    HasCompactSupport (cutoffLayer χ q δ j) := hχ.mul_right

lemma first_cutoff {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (q : Polynomial W) (δ : ℝ) (j β : Fin 3) (y : Y) :
    dpart (cutoffLayer χ q δ j) β y =
      dpart χ β y*layer q δ j y+χ y*dpart (layer q δ j) β y :=
  dpart_mul (hχ.differentiable (by simp)) ((smooth_physicalProfile δ _).differentiable (by simp)) β y

lemma second_cutoff {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (q : Polynomial W) (δ : ℝ) (j α β : Fin 3) (y : Y) :
    dpart (dpart (cutoffLayer χ q δ j) β) α y =
      dpart (dpart χ β) α y*layer q δ j y+dpart χ β y*dpart (layer q δ j) α y+
      (dpart χ α y*dpart (layer q δ j) β y+χ y*dpart (dpart (layer q δ j) β) α y) :=
  second_mul hχ (smooth_physicalProfile δ _) α β y

/-- Literal product-rule residual of the localized physical boundary layer. -/
theorem strong_cutoff_scale (a : SmoothTensor) (b : SmoothLower)
    {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {δ : ℝ} (hδ : δ≠0) (q : Polynomial W) (i : Fin 3) (y : Y) :
    strong a b (cutoffLayer χ q δ) i (scale δ y) =
      ((δ^4)⁻¹:ℝ) • (envelope δ y*cutoffScaled a b χ q δ i y) := by
  have hd : (δ:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hδ
  have hterm (a c cb ca cab u ua ub uab : ℂ) :
      a*(cab*(envelope δ y*u)+cb*(((δ:ℂ)^2)⁻¹*(envelope δ y*ua))+
        (ca*(((δ:ℂ)^2)⁻¹*(envelope δ y*ub))+
          c*(((δ:ℂ)^4)⁻¹*(envelope δ y*uab)))) =
      ((δ:ℂ)^4)⁻¹*envelope δ y*(c*(a*uab)+(δ:ℂ)^2*(a*(cb*ua+ca*ub))+
        (δ:ℂ)^4*(a*cab*u)) := by field_simp [hd]; ring
  have hlower (b c cb u ub : ℂ) :
      b*(cb*(envelope δ y*u)+c*(((δ:ℂ)^2)⁻¹*(envelope δ y*ub))) =
      ((δ:ℂ)^4)⁻¹*envelope δ y*((δ:ℂ)^2*(c*(b*ub))+(δ:ℂ)^4*(b*cb*u)) := by
    field_simp [hd]; ring
  simp only [strong, second_cutoff hχ, first_cutoff hχ, second_layer hδ, partial_layer hδ]
  simp only [layer, physicalProfile_scale hδ, profile, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_pow]
  simp_rw [hterm, hlower, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold cutoffScaled cutoffCorrection scaledOperator
  simp only [mul_add, Finset.sum_add_distrib, ← mul_assoc]
  ring

lemma continuous_cutoffScaled (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, Continuous (a i α j β)) (hb : ∀ i j β, Continuous (b i j β))
    {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (q : Polynomial W) (δ : ℝ) (i : Fin 3) : Continuous (cutoffScaled a b χ q δ i) := by
  have hc := hχ.continuous.comp (scale δ).continuous
  apply Continuous.add (hc.mul (continuous_scaledOperator a b ha hb q δ i))
  apply Continuous.add
  · apply continuous_const.mul
    apply continuous_finsetSum
    intro α _
    apply continuous_finsetSum
    intro j _
    apply continuous_finsetSum
    intro β _
    exact ((ha i α j β).comp (scale δ).continuous).mul
      ((((smooth_dpart hχ β).continuous.comp (scale δ).continuous).mul (smooth_value _).continuous).add
       (((smooth_dpart hχ α).continuous.comp (scale δ).continuous).mul (smooth_value _).continuous))
  · apply continuous_const.mul
    apply Continuous.add
    · apply continuous_finsetSum
      intro α _
      apply continuous_finsetSum
      intro j _
      apply continuous_finsetSum
      intro β _
      exact (((ha i α j β).comp (scale δ).continuous).mul
        ((smooth_dpart (smooth_dpart hχ β) α).continuous.comp (scale δ).continuous)).mul
          (smooth_value _).continuous
    · apply continuous_finsetSum
      intro j _
      apply continuous_finsetSum
      intro β _
      exact (((hb i j β).comp (scale δ).continuous).mul
        ((smooth_dpart hχ β).continuous.comp (scale δ).continuous)).mul (smooth_value _).continuous

end ElasticityBoundaryCutoffLayer

end
end
section
/-! Compactly supported actual half-space quasimodes with arbitrary strong
residual order and uniform H1 bounds. All scalings are those of the physical
boundary layer, not a formal symbol expansion. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace ElasticityBoundaryCutoffParametrix
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundarySmoothOperator ElasticityBoundaryProfile
  ElasticityBoundaryProfileBounds ElasticityBoundaryScaling ElasticityBoundaryLayerOperator
  ElasticityBoundaryWeights ElasticityBoundaryStrongLayer ElasticityBoundaryOrderBound
  ElasticityBoundaryCutoffBound ElasticityBoundaryCutoffLayer
abbrev Y := Fin 3 → ℝ

lemma scaled_envelope_mass {δ : ℝ} (hδ : δ≠0) (r : ℝ) (F g : Y → ℂ)
    (hF : ∀ y, F (scale δ y)=r • (envelope δ y*g y)) :
    (∫ z in halfspace, ‖F z‖^2)=δ^4*r^2*∫ y : Y, ‖g y‖^2*weight 2 y := by
  rw [integralOn_scale hδ]
  simp_rw [hF, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [integral_const_mul, integral_envelope_product]
  ring

lemma scaled_envelope_integrable {δ : ℝ} (hδ : δ≠0) (r : ℝ) (F g : Y → ℂ)
    (hF : ∀ y, F (scale δ y)=r • (envelope δ y*g y))
    (hg : Integrable (fun y => ‖g y‖^2*weight 2 y)) :
    IntegrableOn (fun z => ‖F z‖^2) halfspace := by
  rw [← integrableOn_scaled_iff hδ]
  simp_rw [hF, norm_smul, mul_pow]
  exact ((integrable_envelope_product_iff δ g).mpr hg).const_mul _

lemma continuous_strong (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, Continuous (a i α j β)) (hb : ∀ i j β, Continuous (b i j β))
    (u : Fin 3 → Y → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i : Fin 3) :
    Continuous (strong a b u i) := by
  apply Continuous.add
  · apply continuous_finsetSum
    intro α _
    apply continuous_finsetSum
    intro j _
    apply continuous_finsetSum
    intro β _
    exact (ha i α j β).mul (smooth_dpart (smooth_dpart (hu j) β) α).continuous
  · apply continuous_finsetSum
    intro j _
    apply continuous_finsetSum
    intro β _
    exact (hb i j β).mul (smooth_dpart (hu j) β).continuous

/-- A localized smooth physical trial field with arbitrary small strong force. -/
theorem finite_cutoff_layer (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, ContDiff ℝ (⊤ : ℕ∞) (a i α j β) ∧ HasCompactSupport (a i α j β))
    (hb : ∀ i j β, ContDiff ℝ (⊤ : ℕ∞) (b i j β) ∧ HasCompactSupport (b i j β))
    {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχ0 : χ =ᶠ[𝓝 (0:Y)] fun _ => 1)
    (l m : ℂ) (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0)
    (ha0 : ∀ i α j β, a i α j β 0=elasticityTensor l m i α j β)
    (p₀ : W) (h₀ : normal l m p₀=0) (N : ℕ) :
    ∃ p : ℕ → W, p 0=p₀ ∧ (∀ n, 0<n → boundary (p n)=0) ∧
      ∀ i : Fin 3, ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 →
        MemLp (strong a b (cutoffLayer χ (amplitude p (N+1)) δ) i) 2 (volume.restrict halfspace) ∧
        (∫ z in halfspace, ‖strong a b (cutoffLayer χ (amplitude p (N+1)) δ) i z‖^2) ≤ C*δ^(2*N) := by
  have hta0 : ∀ i α j β, (tensorTaylor a (N+1) i α j β).coeff 0=C (elasticityTensor l m i α j β) := by
    intro i α j β
    rw [tensorTaylor, taylor_coeff_zero (ha i α j β).1 (ha i α j β).2, ha0]
  obtain ⟨p,R,hp0,hpb,hR⟩ := finite_tensor_amplitude (tensorTaylor a (N+1)) (lowerTaylor b (N+1))
    l m hm he hp hta0 p₀ h₀ (N+1)
  refine ⟨p,hp0,hpb,fun i => ?_⟩
  let q := amplitude p (N+1)
  have hq := scaledOperator_order_bound a b ha hb q R (N+1) hR i
  have ho : OrderBound (fun δ y => cutoffScaled a b χ q δ i y) (N+1+1) := by
    have hmain : OrderBound (fun δ y => χ (scale δ y)*scaledOperator a b q δ i y) (N+1+1) := by
      simpa only [Nat.zero_add] using (compact_scaled hχ.continuous hc).mul hq
    exact hmain.add
      (correction_order_bound a b (fun i α j β => ⟨(ha i α j β).1.continuous,(ha i α j β).2⟩)
        (fun i j β => ⟨(hb i j β).1.continuous,(hb i j β).2⟩) hχ hc hχ0 q (N+1+1) i)
  obtain ⟨C,hC,hI⟩ := ho.square_mass
    (fun δ => continuous_cutoffScaled a b (fun i α j β => (ha i α j β).1.continuous)
      (fun i j β => (hb i j β).1.continuous) hχ q δ i) (by norm_num : (0:ℝ)<2)
  refine ⟨C,hC,fun δ hδ hδ1 => ?_⟩
  obtain ⟨hInt,hBound⟩ := hI δ hδ hδ1
  have hid := strong_cutoff_scale a b hχ hδ.ne' q i
  have hcont := continuous_strong a b (fun i α j β => (ha i α j β).1.continuous)
    (fun i j β => (hb i j β).1.continuous) (cutoffLayer χ q δ) (smooth_cutoffLayer hχ q δ) i
  refine ⟨(memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr
    (scaled_envelope_integrable hδ.ne' _ _ _ hid hInt), ?_⟩
  rw [scaled_envelope_mass hδ.ne' _ _ _ hid]
  calc
    _ ≤ δ^4*((δ^4)⁻¹)^2*(C*δ^(2*(N+1+1))) := mul_le_mul_of_nonneg_left hBound (by positivity)
    _ = C*δ^(2*N) := by
      rw [show 2*(N+1+1)=4+2*N by omega, pow_add]
      field_simp

/-- Amplitude of a genuine first derivative, including the cutoff derivative. -/
def firstScaled (χ : Y → ℂ) (q : Polynomial W) (δ : ℝ) (j β : Fin 3) (y : Y) : ℂ :=
  χ (scale δ y)*value (atParameter (PD β (unpack j q)) δ) y+
    (δ:ℂ)^2*dpart χ β (scale δ y)*value (atParameter (unpack j q) δ) y

lemma first_scaled_identity {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {δ : ℝ} (hδ : δ≠0) (q : Polynomial W) (j β : Fin 3) (y : Y) :
    dpart (cutoffLayer χ q δ j) β (scale δ y)=
      ((δ^2)⁻¹:ℝ) • (envelope δ y*firstScaled χ q δ j β y) := by
  rw [first_cutoff hχ, partial_layer hδ]
  simp only [layer, physicalProfile_scale hδ, profile, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_pow, firstScaled]
  have hd : (δ:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hδ
  field_simp
  ring

lemma first_scaled_bound {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (q : Polynomial W) (j β : Fin 3) :
    OrderBound (fun δ y => firstScaled χ q δ j β y) 0 := by
  have hmain : OrderBound (fun δ y => χ (scale δ y)*value (atParameter (PD β (unpack j q)) δ) y) 0 := by
    simpa only [Nat.zero_add] using (compact_scaled hχ.continuous hc).mul
      (parameter_bound (PD β (unpack j q)))
  have herr : OrderBound (fun δ y => (δ:ℂ)^2*dpart χ β (scale δ y)*value (atParameter (unpack j q) δ) y) 0 := by
    have h := (((power_bound 2).mul (compact_scaled (smooth_dpart hχ β).continuous (compact_dpart hc β))).mul
      (parameter_bound (unpack j q))).weaken (show 0≤2+0+0 by omega)
    exact h
  exact hmain.add herr

lemma first_scaled_continuous {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (q : Polynomial W) (δ : ℝ) (j β : Fin 3) : Continuous (firstScaled χ q δ j β) := by
  exact ((hχ.continuous.comp (scale δ).continuous).mul (smooth_value _).continuous).add
    ((continuous_const.mul ((smooth_dpart hχ β).continuous.comp (scale δ).continuous)).mul
      (smooth_value _).continuous)

/-- The actual physical gradient is uniformly L2 bounded; its delta^-2
factor is canceled by the genuine anisotropic delta^4 volume factor. -/
theorem cutoff_gradient_bound {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (q : Polynomial W) (j β : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 →
      MemLp (dpart (cutoffLayer χ q δ j) β) 2 (volume.restrict halfspace) ∧
      (∫ z in halfspace, ‖dpart (cutoffLayer χ q δ j) β z‖^2) ≤ C := by
  obtain ⟨C,hC,hI⟩ := (first_scaled_bound hχ hc q j β).square_mass
    (fun δ => first_scaled_continuous hχ q δ j β) (by norm_num : (0:ℝ)<2)
  refine ⟨C,hC,fun δ hδ hδ1 => ?_⟩
  obtain ⟨hInt,hB⟩ := hI δ hδ hδ1
  have hid := first_scaled_identity hχ hδ.ne' q j β
  refine ⟨(memLp_two_iff_integrable_sq_norm
    (smooth_dpart (smooth_cutoffLayer hχ q δ j) β).continuous.aestronglyMeasurable).mpr
      (scaled_envelope_integrable hδ.ne' _ _ _ hid hInt), ?_⟩
  rw [scaled_envelope_mass hδ.ne' _ _ _ hid]
  have hpow : δ^4*((δ^2)⁻¹)^2=1 := by field_simp
  rw [hpow,one_mul]
  simpa only [Nat.mul_zero,pow_zero,mul_one] using hB

end ElasticityBoundaryCutoffParametrix

end
end
section
/-! Local boundary layers for arbitrary smooth coefficients. Auxiliary compact
coefficient extensions are removed on the actual trial support; thus no
artificial compactness or global geometry assumption is imposed on a chart. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryLocalParametrix
open ElasticityBoundaryCutoffParametrix ElasticityBoundaryCutoffLayer
  ElasticityBoundaryStrongLayer ElasticityBoundarySmoothOperator
  ElasticityBoundaryMVNormal ElasticityBoundaryActualTower ElasticityBoundaryMVTower
  ElasticityBoundaryLayerOperator ElasticityBoundaryProfile ElasticityBoundaryOperatorLocal
  ElasticityBoundary ElasticityBoundaryProfileBounds
abbrev I := Fin 3
abbrev Y := I → ℝ

lemma strong_support (a : SmoothTensor) (b : SmoothLower) {K : Set Y} (hK : IsClosed K)
    (u : I → Y → ℂ) (hu : ∀ j, Function.support (u j)⊆K) (i : I) :
    Function.support (strong a b u i)⊆K :=
  directional_support (fun j => Pi.single j 1) a b hK u hu i

lemma strong_mul_coeff (κ : Y → ℂ) (a : SmoothTensor) (b : SmoothLower)
    (u : I → Y → ℂ) (i : I) (y : Y) :
    strong (fun i α j β z => κ z*a i α j β z) (fun i j β z => κ z*b i j β z) u i y=
      κ y*strong a b u i y := by
  simp only [strong,mul_assoc,← Finset.mul_sum,mul_add]

lemma localize_strong (κ : Y → ℂ) (a : SmoothTensor) (b : SmoothLower)
    {K : Set Y} (hK : IsClosed K) (hκ : ∀ y∈K, κ y=1)
    (u : I → Y → ℂ) (hu : ∀ j, Function.support (u j)⊆K) :
    strong (fun i α j β z => κ z*a i α j β z) (fun i j β z => κ z*b i j β z) u=
      strong a b u := by
  funext i y
  rw [strong_mul_coeff]
  by_cases hy : y∈K
  · rw [hκ y hy,one_mul]
  · have hz : strong a b u i y=0 := Function.notMem_support.mp
      (fun h => hy (strong_support a b hK u hu i h))
    rw [hz,mul_zero]

lemma cutoff_support {χ : Y → ℂ} (q : Polynomial W) (δ : ℝ) (j : I) :
    Function.support (cutoffLayer χ q δ j)⊆tsupport χ := by
  intro y hy
  apply subset_tsupport χ
  intro hz
  exact hy (by simp [cutoffLayer,hz])

lemma compact_coefficients (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, ContDiff ℝ (⊤ : ℕ∞) (a i α j β))
    (hb : ∀ i j β, ContDiff ℝ (⊤ : ℕ∞) (b i j β))
    {K : Set Y} (hK : IsCompact K) :
    ∃ (a' : SmoothTensor) (b' : SmoothLower),
      (∀ i α j β, ContDiff ℝ (⊤ : ℕ∞) (a' i α j β) ∧ HasCompactSupport (a' i α j β)) ∧
      (∀ i j β, ContDiff ℝ (⊤ : ℕ∞) (b' i j β) ∧ HasCompactSupport (b' i j β)) ∧
      (∀ y∈K, ∀ i α j β, a' i α j β y=a i α j β y) ∧
      ∀ u : I → Y → ℂ, (∀ j, Function.support (u j)⊆K) → strong a' b' u=strong a b u := by
  obtain ⟨κ,hκ,hκc,_,hκ1,_⟩ := compact_smooth_cutoff hK isOpen_univ (subset_univ _)
  let κc : Y → ℂ := fun y => (κ y:ℂ)
  have hκcs : ContDiff ℝ (⊤ : ℕ∞) κc := Complex.ofRealCLM.contDiff.comp hκ
  have hκcc : HasCompactSupport κc :=
    hκc.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hκK (y : Y) (hy : y∈K) : κc y=1 := by
    change (κ y:ℂ)=1
    exact_mod_cast hκ1.self_of_nhdsSet y hy
  refine ⟨(fun i α j β z => κc z*a i α j β z),
    (fun i j β z => κc z*b i j β z),?_,?_,?_,?_⟩
  · exact fun i α j β => ⟨hκcs.mul (ha i α j β),hκcc.mul_right⟩
  · exact fun i j β => ⟨hκcs.mul (hb i j β),hκcc.mul_right⟩
  · intro y hy i α j β
    dsimp only
    rw [hκK y hy,one_mul]
  · exact fun u hu => localize_strong κc a b hK.isClosed hκK u hu

/-- The true arbitrary-order strong quasimode theorem needs only local
smoothness of the physical pullback. Compact coefficients used during the
Taylor construction leave the literal final operator unchanged. -/
theorem finite_local_layer (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, ContDiff ℝ (⊤ : ℕ∞) (a i α j β))
    (hb : ∀ i j β, ContDiff ℝ (⊤ : ℕ∞) (b i j β))
    {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχ0 : χ =ᶠ[𝓝 (0:Y)] fun _ => 1)
    (l m : ℂ) (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0)
    (ha0 : ∀ i α j β, a i α j β 0=elasticityTensor l m i α j β)
    (p₀ : W) (h₀ : normal l m p₀=0) (N : ℕ) :
    ∃ p : ℕ → W, p 0=p₀ ∧ (∀ n, 0<n → boundary (p n)=0) ∧
      ∀ i : I, ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 →
        MemLp (strong a b (cutoffLayer χ (amplitude p (N+1)) δ) i) 2 (volume.restrict halfspace) ∧
        (∫ z in halfspace, ‖strong a b (cutoffLayer χ (amplitude p (N+1)) δ) i z‖^2) ≤ C*δ^(2*N) := by
  obtain ⟨a',b',ha',hb',haa,hEq⟩ := compact_coefficients a b ha hb hc
  have h00 : (0:Y)∈tsupport χ := subset_tsupport χ (by
    change χ 0≠0
    rw [hχ0.eq_of_nhds]
    exact one_ne_zero)
  have ha'0 : ∀ i α j β, a' i α j β 0=elasticityTensor l m i α j β := by
    intro i α j β
    exact (haa 0 h00 i α j β).trans (ha0 i α j β)
  obtain ⟨p,hp0,hpb,hpB⟩ := finite_cutoff_layer a' b' ha' hb'
    hχ hc hχ0 l m hm he hp ha'0 p₀ h₀ N
  refine ⟨p,hp0,hpb,fun i => ?_⟩
  obtain ⟨C,hC,hB⟩ := hpB i
  refine ⟨C,hC,fun δ hδ hδ1 => ?_⟩
  have heq := hEq (cutoffLayer χ (amplitude p (N+1)) δ) (cutoff_support _ δ)
  simpa only [heq] using hB δ hδ hδ1

end ElasticityBoundaryLocalParametrix

end
end

end OAI
