import OAI.Geometry.Riemannian.HarmonicCore.InteriorBounds

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction

namespace HarmonicCounterexample.Main.SmoothMetric3

noncomputable def testSobolev (T : ℝ) (F : DirichletTest T) : ZeroSobolev T :=
  ⟨testGraph T F,subset_closure (Set.mem_range_self F)⟩

lemma affineSobolev_value {R T : ℝ} (hRT : R ≤ T) (F : DirichletTest T) (u : ZeroSobolev R) :
    (sobolevValue T (testSobolev T F+includeSobolev hRT u) : E3 → ℝ) =ᵐ[volume]
      fun x ↦ (F:E3 → ℝ) x+(sobolevValue R u) x := by
  change ((testValueLinear T F+sobolevValue R u:ValueL2) : E3 → ℝ) =ᵐ[volume] _
  exact (Lp.coeFn_add _ _).trans (F.value_memLp.coeFn_toLp.add Filter.EventuallyEq.rfl)

lemma affineSobolev_derivative {R T : ℝ} (hRT : R ≤ T) (F : DirichletTest T) (u : ZeroSobolev R) :
    (sobolevDerivative T (testSobolev T F+includeSobolev hRT u) : E3 → E3) =ᵐ[volume]
      fun x ↦ gradient (F:E3 → ℝ) x+(sobolevDerivative R u) x := by
  change ((testDerivativeLinear T F+sobolevDerivative R u:DerivativeL2) : E3 → E3) =ᵐ[volume] _
  exact (Lp.coeFn_add _ _).trans (F.derivative_memLp.coeFn_toLp.add Filter.EventuallyEq.rfl)

lemma compact_test_extension {F : E3 → ℝ} (_hF : ContDiff ℝ ∞ F)
    (hcompact : HasCompactSupport F) (R : ℝ) :
    ∃ T : ℝ, R ≤ T ∧ tsupport F ⊆ Metric.ball (0:E3) T := by
  obtain ⟨T,hT,hTs⟩ := hcompact.isBounded.subset_ball_lt R (0:E3)
  exact ⟨T,hT.le,hTs⟩

theorem metric_affine_weak_continuous (g : SmoothMetric3) (R : ℝ) (hR : 0 < R)
    {F : E3 → ℝ} (hF : ContDiff ℝ ∞ F) (hcompact : HasCompactSupport F) :
    ∃ u : ZeroSobolev R,
      (∀ v : ZeroSobolev R,
        (∫ x, ⟪g.energyOperator x (gradient F x+(sobolevDerivative R u) x),
          (sobolevDerivative R v) x⟫_ℝ) = 0) ∧
      ∀ r : ℝ, 0 < r → r < R → ∃ U : E3 →ᵇ ℝ,
        (U:E3 → ℝ) =ᵐ[volume.restrict (Metric.ball 0 r)]
          (fun x ↦ F x+(sobolevValue R u) x) := by
  obtain ⟨u,hu,_⟩ := g.metric_affine_weak_dirichlet R hR.le hF hcompact
  obtain ⟨T,hRT,hTs⟩ := compact_test_extension hF hcompact R
  let φ : DirichletTest T := ⟨F,hF,hcompact,hTs⟩
  let w : ZeroSobolev T := testSobolev T φ+includeSobolev hRT u
  have hw : ∀ v : ZeroSobolev R,
      (∫ x, ⟪g.energyOperator x ((sobolevDerivative T w) x),(sobolevDerivative R v) x⟫_ℝ) = 0 := by
    intro v
    rw [←hu v]
    apply integral_congr_ae
    filter_upwards [affineSobolev_derivative hRT φ u] with x hx
    rw [hx]
  refine ⟨u,hu,fun r hr hrR ↦ ?_⟩
  obtain ⟨B,hB,hBs⟩ := g.metric_weak_interior_sup_L2 r R T hr hrR
  obtain ⟨U,hU,hUn⟩ := hBs w hw
  exact ⟨U,hU.trans ((affineSobolev_value hRT φ u).filter_mono ae_restrict_le)⟩


open HarmonicCounterexample.Analytic
open scoped BoundedContinuousFunction

lemma graph_H2_continuous {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E3)
    (R N : ℝ) (u : ZeroSobolev R) (w : ι → ZeroSobolev N)
    (hw : ∀ i, sobolevValue N (w i) = componentL2 (b i) (sobolevDerivative R u)) :
    ∃ U : E3 →ᵇ ℝ, (U : E3 → ℝ) =ᵐ[volume] (sobolevValue R u : E3 → ℝ) := by
  have hΔ := graph_laplacian b R N u w hw
  obtain ⟨U,hU⟩ := laplacianL2_exists_continuous (E:=E3) (by norm_num [E3])
    (complexifyL2 (sobolevValue R u))
    (complexifyL2 (∑ i,componentL2 (b i) (sobolevDerivative N (w i)))) hΔ
  have he := boundedDistribution_eq_L2_ae U _ hU
  let V : E3 →ᵇ ℝ := BoundedContinuousFunction.comp Complex.re Complex.reCLM.lipschitzWith U
  refine ⟨V,?_⟩
  filter_upwards [he,complexifyL2_coe (sobolevValue R u)] with x hx hy
  change (U x).re = _
  rw [hx,hy,Complex.ofReal_re]

theorem weak_interior_gradient_continuous (r S T : ℝ) (hr : 0 < r) (hrS : r < S)
    (A : E3 → E3 →L[ℝ] E3) (hA : ContDiff ℝ ∞ A) (C L Q c : ℝ)
    (hc : 0 < c) (hC : ∀ x, ‖A x‖ ≤ C) (hL0 : 0 ≤ L) (hQ : 0 ≤ Q)
    (hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖)
    (hQbound : ∀ x y, ‖fderiv ℝ A y-fderiv ℝ A x‖ ≤ Q*‖y-x‖)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A x v,v⟫_ℝ)
    (u : ZeroSobolev T)
    (hu : ∀ v : ZeroSobolev S,
      ⟪coefficientCLM A C hA.continuous.aestronglyMeasurable hC (sobolevDerivative T u),sobolevDerivative S v⟫_ℝ = 0)
    (a : E3) (hcompact : HasCompactSupport (fun x ↦ fderiv ℝ A x a)) :
    ∃ U : E3 →ᵇ ℝ, (U : E3 → ℝ) =ᵐ[volume.restrict (Metric.ball 0 r)]
      (fun x ↦ ⟪a,(sobolevDerivative T u) x⟫_ℝ) := by
  classical
  let R₂ := (r+S)/2
  let R₁ := (r+R₂)/2
  let R₀ := (r+R₁)/2
  let Rm := (r+R₀)/2
  have hab : r < Rm ∧ Rm < R₀ ∧ R₀ < R₁ ∧ R₁ < R₂ ∧ R₂ < S := by
    refine ⟨?_,?_,?_,?_,?_⟩ <;> dsimp [Rm,R₀,R₁,R₂] <;> linarith
  obtain ⟨χ,D,hχ,hsχ,hK,hD,hχ1,hdχ⟩ := smooth_ball_cutoff R₁ R₂ (by linarith [hab.1,hab.2.1,hab.2.2.1]) hab.2.2.2.1
  let K : ℝ := 1
  let v := cutoffSobolev R₂ T χ hχ hsχ K D hK hD u
  let b := stdOrthonormalBasis ℝ E3
  choose w hw using fun i ↦ weak_cutoff_H2 R₂ S T hab.2.2.2.2 A C L c hc hL0 hA.continuous hC hL hpos
    u hu χ hχ hsχ K D hK hD (b i)
  have hu₂ (z : ZeroSobolev R₂) :
      ⟪coefficientCLM A C hA.continuous.aestronglyMeasurable hC (sobolevDerivative T u),sobolevDerivative R₂ z⟫_ℝ = 0 :=
    hu (includeSobolev hab.2.2.2.2.le z)
  have hv := weak_cutoff_restrict R₁ R₂ T hab.2.2.2.1.le A C hA.continuous.aestronglyMeasurable hC
    u hu₂ χ hχ hsχ K D hK hD hχ1 hdχ
  obtain ⟨ψ,Dψ,hψ,hsψ,hKψ,hDψ,hψ1,hdψ⟩ := smooth_ball_cutoff r Rm hr hab.1
  let Kψ : ℝ := 1
  obtain ⟨q,hq,hqH⟩ := weak_direction_H2 b Rm R₀ R₁ R₂ R₂ hab.2.1 hab.2.2.1 A hA C L Q c
    hc hC hL0 hQ hL hQbound hpos v hv w hw a hcompact ψ hψ hsψ Kψ Dψ hKψ hDψ
  choose z hz using fun i ↦ hqH (b i)
  obtain ⟨U,hU⟩ := graph_H2_continuous b Rm Rm (cutoffSobolev Rm (R₂+1) ψ hψ hsψ Kψ Dψ hKψ hDψ q) z hz
  have hqae : (sobolevValue (R₂+1) q : E3 → ℝ) =ᵐ[volume]
      (fun x ↦ ⟪a,(sobolevDerivative R₂ v) x⟫_ℝ) := by
    rw [hq]
    exact componentL2_coe a _
  have hall : (U : E3 → ℝ) =ᵐ[volume] fun x ↦
      ψ x*⟪a,χ x • (sobolevDerivative T u) x+(sobolevValue T u) x • gradient χ x⟫_ℝ := by
    filter_upwards [hU,scalarFieldCLM_coe ψ hψ.continuous Kψ hKψ (sobolevValue (R₂+1) q),
      hqae,cutoffSobolev_derivative_coe R₂ T χ hχ hsχ K D hK hD u] with x h1 h2 h3 h4
    change U x = (scalarFieldCLM ψ hψ.continuous Kψ hKψ (sobolevValue (R₂+1) q)) x at h1
    rw [h1,h2,h3,h4]
    rfl
  refine ⟨U,?_⟩
  filter_upwards [hall.filter_mono ae_restrict_le,ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxball
  have hxr : x ∈ Metric.closedBall (0:E3) r := Metric.ball_subset_closedBall hxball
  have hxR : x ∈ Metric.closedBall (0:E3) R₁ :=
    Metric.closedBall_subset_closedBall (by linarith [hab.1,hab.2.1,hab.2.2.1]) hxr
  rw [hx,hψ1 x hxr,hχ1 x hxR,hdχ x hxR,one_smul,smul_zero,add_zero,one_mul]

lemma identity_perturbation_derivatives (δ : E3 → E3 →L[ℝ] E3)
    (hδ : ContDiff ℝ ∞ δ) (hsδ : HasCompactSupport δ) :
    ∃ Q : ℝ, 0 ≤ Q ∧
      (∀ x y, ‖fderiv ℝ (fun z ↦ ContinuousLinearMap.id ℝ E3+δ z) y-
        fderiv ℝ (fun z ↦ ContinuousLinearMap.id ℝ E3+δ z) x‖ ≤ Q*‖y-x‖) ∧
      ∀ a : E3, HasCompactSupport
        (fun x ↦ fderiv ℝ (fun z ↦ ContinuousLinearMap.id ℝ E3+δ z) x a) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ δ) := hδ.fderiv_right (by simp)
  have hs : HasCompactSupport (fderiv ℝ δ) := hsδ.fderiv ℝ
  have hLip : ∃ Q : NNReal, LipschitzWith Q (fderiv ℝ δ) :=
    ContDiff.lipschitzWith_of_hasCompactSupport (𝕂:=ℝ) hs hd (by simp)
  obtain ⟨Q,hQ⟩ := hLip
  refine ⟨Q,Q.coe_nonneg,?_,?_⟩
  · intro x y
    simpa only [fderiv_const_add,dist_eq_norm] using hQ.dist_le_mul y x
  · intro a
    simpa only [Function.comp_def,fderiv_const_add] using
      (hsδ.fderiv ℝ).comp_left (g:=fun B : E3 →L[ℝ] E3 →L[ℝ] E3 ↦ B a) (by simp)

theorem smooth_energy_extension_higher (g : SmoothMetric3) (R : ℝ) (hR : 0 ≤ R) :
    ∃ (A : E3 → E3 →L[ℝ] E3) (C L Q c : ℝ), ContDiff ℝ ∞ A ∧ 0 ≤ C ∧ 0 ≤ L ∧ 0 ≤ Q ∧ 0 < c ∧
      (∀ x, ‖A x‖ ≤ C) ∧ (∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖) ∧
      (∀ x y, ‖fderiv ℝ A y-fderiv ℝ A x‖ ≤ Q*‖y-x‖) ∧
      (∀ x v, c*‖v‖^2 ≤ ⟪A x v,v⟫_ℝ) ∧
      (∀ x ∈ Metric.closedBall (0:E3) R, A x = g.energyOperator x) ∧
      (∀ a : E3, HasCompactSupport (fun x ↦ fderiv ℝ A x a)) := by
  let ψ : ContDiffBump (0:E3) := ⟨R+1,R+2,by linarith,by linarith⟩
  let I := ContinuousLinearMap.id ℝ E3
  let δ : E3 → E3 →L[ℝ] E3 := fun x ↦ ψ x • (g.energyOperator x-I)
  let A : E3 → E3 →L[ℝ] E3 := fun x ↦ I+δ x
  have hδ : ContDiff ℝ ∞ δ := ψ.contDiff.smul (g.energyOperator_contDiff.sub contDiff_const)
  have hsδ : HasCompactSupport δ := ψ.hasCompactSupport.smul_right (f':=fun x ↦ g.energyOperator x-I)
  obtain ⟨K,L,hK0,hL0,hK,hL⟩ := compact_coefficient_bounds δ hδ hsδ
  obtain ⟨Q,hQ0,hQ,hQs⟩ := identity_perturbation_derivatives δ hδ hsδ
  obtain ⟨c,C,hc,hC,hbound,hpos⟩ := g.energyOperator_uniform (R+2) (by linarith)
  refine ⟨A,1+K,L,Q,min c 1,contDiff_const.add hδ,by positivity,hL0,hQ0,
    lt_min hc zero_lt_one,?_,?_,hQ,?_,?_,hQs⟩
  · intro x
    exact (norm_add_le I (δ x)).trans (add_le_add ContinuousLinearMap.norm_id_le (hK x))
  · intro x y
    simpa only [A,add_sub_add_left_eq_sub] using hL x y
  · exact bump_coefficient_coercive g.energyOperator ψ c hpos
  · intro x hx
    have h1 : ψ x = 1 := ψ.one_of_mem_closedBall
      (Metric.closedBall_subset_closedBall (show R ≤ ψ.rIn by dsimp [ψ]; linarith) hx)
    simp only [A,δ,h1,one_smul]
    rw [←add_sub_assoc,add_sub_cancel_left]

theorem metric_weak_gradient_continuous (g : SmoothMetric3) (r S T : ℝ)
    (hr : 0 < r) (hrS : r < S) (u : ZeroSobolev T)
    (hu : ∀ v : ZeroSobolev S,
      (∫ x, ⟪g.energyOperator x ((sobolevDerivative T u) x),
        (sobolevDerivative S v) x⟫_ℝ) = 0) (a : E3) :
    ∃ U : E3 →ᵇ ℝ, (U : E3 → ℝ) =ᵐ[volume.restrict (Metric.ball 0 r)]
      (fun x ↦ ⟪a,(sobolevDerivative T u) x⟫_ℝ) := by
  obtain ⟨A,C,L,Q,c,hA,hC0,hL0,hQ0,hc,hC,hL,hQ,hpos,hAg,hcomp⟩ :=
    g.smooth_energy_extension_higher S (hr.trans hrS).le
  apply weak_interior_gradient_continuous r S T hr hrS A hA C L Q c hc hC hL0 hQ0 hL hQ hpos u ?_ a (hcomp a)
  intro v
  rw [coefficient_ball_energy_eq g S A C hA.continuous.aestronglyMeasurable hC hAg]
  exact hu v

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
