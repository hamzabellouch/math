import OAI.Analysis.Brenier.Basic

namespace OAI

noncomputable section

open Set Filter
open scoped Topology NNReal

namespace Problem358

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- For a locally Lipschitz real function, a linear family of genuine line
 derivatives is already its full Fréchet derivative. This local form does not
require an artificial global Lipschitz bound on moving-cell parameters. -/
theorem hasFDerivAt_of_local_lipschitz_lineDeriv
    {f : E → ℝ} {x : E} {L : E →L[ℝ] ℝ} {S : Set E} {C : ℝ≥0}
    (hS : S ∈ 𝓝 x) (hf : LipschitzOnWith C f S)
    (hline : ∀ v, HasLineDerivAt ℝ f (L v) x v) :
    HasFDerivAt f L x := by
  obtain ⟨g, hg, hfg⟩ := hf.extend_real
  have heq : f =ᶠ[𝓝 x] g := by
    filter_upwards [hS] with y hy
    exact hfg hy
  have hd : HasFDerivAt g L x := by
    apply hg.hasFDerivAt_of_hasLineDerivAt_of_closure (s := univ)
    · simp
    · intro v _
      exact (hline v).congr_of_eventuallyEq heq.symm
  exact hd.congr_of_eventuallyEq heq

/-- A continuous field of linear line derivatives for a locally Lipschitz
real function proves genuine `C¹` regularity on an open parameter domain. -/
theorem contDiffOn_one_of_local_lipschitz_lineDeriv
    {f : E → ℝ} {U : Set E} {L : E → E →L[ℝ] ℝ}
    (hU : IsOpen U) (hL : ContinuousOn L U)
    (hlip : ∀ x ∈ U, ∃ (S : Set E) (C : ℝ≥0), S ∈ 𝓝 x ∧ LipschitzOnWith C f S)
    (hline : ∀ x ∈ U, ∀ v, HasLineDerivAt ℝ f (L x v) x v) :
    ContDiffOn ℝ 1 f U := by
  have hd (x : E) (hx : x ∈ U) : HasFDerivAt f (L x) x := by
    obtain ⟨S, C, hS, hf⟩ := hlip x hx
    exact hasFDerivAt_of_local_lipschitz_lineDeriv hS hf (hline x hx)
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn]
  refine ⟨by simp, L, ?_, fun x hx => (hd x hx).hasFDerivWithinAt⟩
  exact contDiffOn_zero.mpr hL

/-- Finite-vector version, suited to the full vector of cell masses. -/
theorem hasFDerivAt_pi_of_local_lipschitz_lineDeriv
    {ι : Type*} [Fintype ι] {f : E → ι → ℝ} {x : E}
    {L : E →L[ℝ] (ι → ℝ)} {S : Set E} {C : ℝ≥0}
    (hS : S ∈ 𝓝 x) (hf : LipschitzOnWith C f S)
    (hline : ∀ v, HasLineDerivAt ℝ f (L v) x v) :
    HasFDerivAt f L x := by
  obtain ⟨g, hg, hfg⟩ := hf.extend_pi
  have heq : f =ᶠ[𝓝 x] g := by
    filter_upwards [hS] with y hy
    exact hfg hy
  have hd : HasFDerivAt g L x := by
    apply hg.hasFDerivAt_of_hasLineDerivAt_of_closure (s := univ)
    · simp
    · intro v _
      exact (hline v).congr_of_eventuallyEq heq.symm
  exact hd.congr_of_eventuallyEq heq

/-- The locally Lipschitz finite-vector function is `C¹` when its linear
line-derivative field is continuous. -/
theorem contDiffOn_one_pi_of_local_lipschitz_lineDeriv
    {ι : Type*} [Fintype ι] {f : E → ι → ℝ} {U : Set E}
    {L : E → E →L[ℝ] (ι → ℝ)}
    (hU : IsOpen U) (hL : ContinuousOn L U)
    (hlip : ∀ x ∈ U, ∃ (S : Set E) (C : ℝ≥0), S ∈ 𝓝 x ∧ LipschitzOnWith C f S)
    (hline : ∀ x ∈ U, ∀ v, HasLineDerivAt ℝ f (L x v) x v) :
    ContDiffOn ℝ 1 f U := by
  have hd (x : E) (hx : x ∈ U) : HasFDerivAt f (L x) x := by
    obtain ⟨S, C, hS, hf⟩ := hlip x hx
    exact hasFDerivAt_pi_of_local_lipschitz_lineDeriv hS hf (hline x hx)
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn]
  refine ⟨by simp, L, ?_, fun x hx => (hd x hx).hasFDerivWithinAt⟩
  exact contDiffOn_zero.mpr hL

end Problem358

end

noncomputable section
open Set Filter Asymptotics
open scoped Topology

namespace Problem358

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma hasDerivAt_line_of_hasLineDerivAt
    {f : V → F} {x v : V} {t : ℝ} {p : F}
    (h : HasLineDerivAt ℝ f p (x + t • v) v) :
    HasDerivAt (fun r : ℝ => f (x + r • v)) p t := by
  have h' : HasDerivAt (fun r : ℝ => f ((x + t • v) + r • v)) p (t - t) := by
    simpa only [HasLineDerivAt, sub_self] using h
  have hh := h'.comp_sub_const t t
  convert hh using 1
  funext r
  congr 1
  simp only [sub_smul]
  abel

lemma norm_sub_le_of_continuous_linear_line_derivatives
    {s : Set V} (hs : Convex ℝ s) {f : V → F} {D : V → V →L[ℝ] F}
    (hD : ∀ x ∈ s, ∀ v, HasLineDerivAt ℝ f (D x v) x v)
    {A : V →L[ℝ] F} {C : ℝ} (hb : ∀ x ∈ s, ‖D x - A‖ ≤ C)
    {x y : V} (hx : x ∈ s) (hy : y ∈ s) :
    ‖f y - f x - A (y - x)‖ ≤ C * ‖y - x‖ := by
  let v := y - x
  let g : ℝ → F := fun t => f (x + t • v) - t • A v
  have hd : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt g ((D (x + t • v) - A) v) t := by
    intro t ht
    have hz : x + t • v ∈ s := hs.add_smul_sub_mem hx hy ht
    have hh := hasDerivAt_line_of_hasLineDerivAt (hD _ hz v)
    simpa only [g, sub_apply, one_smul, Pi.sub_def, id_eq] using
      hh.sub ((hasDerivAt_id t).smul_const (A v))
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖(D (x + t • v) - A) v‖ ≤ C * ‖v‖ := by
    intro t ht
    have hz : x + t • v ∈ s := hs.add_smul_sub_mem hx hy (Ico_subset_Icc_self ht)
    exact ((D (x + t • v) - A).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hb _ hz) (norm_nonneg v))
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (hd t ht).hasDerivWithinAt) hbound
  simpa only [g, v, one_smul, zero_smul, add_zero, sub_zero, add_sub_cancel_left,
    add_sub_cancel, sub_sub_sub_cancel_right, sub_right_comm] using hm

/-- A continuous field of bounded linear directional derivatives implies strict
Fréchet differentiability. No completeness or finite-dimensional hypothesis is needed. -/
lemma hasStrictFDerivAt_of_continuousAt_lineDeriv
    {f : V → F} {D : V → V →L[ℝ] F} {x : V}
    (hD : ∀ᶠ y in 𝓝 x, ∀ v, HasLineDerivAt ℝ f (D y v) y v)
    (hc : ContinuousAt D x) : HasStrictFDerivAt f (D x) x := by
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hD
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hc ε hε
  let η := min r δ
  have hη : 0 < η := lt_min hr hδ
  have hline : ∀ y ∈ Metric.ball x η, ∀ v, HasLineDerivAt ℝ f (D y v) y v := by
    intro y hy
    exact hball (Metric.mem_ball.mpr (lt_of_lt_of_le
      (Metric.mem_ball.mp hy) (min_le_left r δ)))
  have hbound : ∀ y ∈ Metric.ball x η, ‖D y - D x‖ ≤ ε := by
    intro y hy
    have hh := hclose (lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_right r δ))
    exact le_of_lt (by simpa only [dist_eq_norm] using hh)
  have hevent : ∀ᶠ y in 𝓝 x, y ∈ Metric.ball x η := Metric.ball_mem_nhds x hη
  filter_upwards [hevent.prod_nhds hevent] with p hp
  exact norm_sub_le_of_continuous_linear_line_derivatives
    (convex_ball x η) hline hbound hp.2 hp.1

/-- On an open set, a continuous field of bounded linear line derivatives gives C¹. -/
lemma contDiffOn_one_of_continuousOn_lineDeriv
    {s : Set V} (hs : IsOpen s) {f : V → F} {D : V → V →L[ℝ] F}
    (hD : ∀ x ∈ s, ∀ v, HasLineDerivAt ℝ f (D x v) x v)
    (hc : ContinuousOn D s) : ContDiffOn ℝ 1 f s := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  rw [contDiffAt_one_iff]
  refine ⟨D, s, hs.mem_nhds hx, hc, ?_⟩
  intro y hy
  apply HasStrictFDerivAt.hasFDerivAt
  apply hasStrictFDerivAt_of_continuousAt_lineDeriv
  · filter_upwards [hs.mem_nhds hy] with z hz
    exact hD z hz
  · exact (hc y hy).continuousAt (hs.mem_nhds hy)

end Problem358

end

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace Problem358.FaceDerivative

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A face contribution to the mass derivative, with its scalar and vector moments
made explicit. The input is the site and intercept variation `(v,r)`. -/
def linearMap (A M : ℝ) (B : V) : V × ℝ →L[ℝ] ℝ :=
  A⁻¹ • (M • ContinuousLinearMap.snd ℝ V ℝ +
    (innerSL ℝ B).comp (ContinuousLinearMap.fst ℝ V ℝ))

@[simp] lemma linearMap_apply (A M : ℝ) (B v : V) (r : ℝ) :
    linearMap A M B (v, r) = (r / A) * M + (1 / A) * ⟪v, B⟫_ℝ := by
  change A⁻¹ * (M * r + ⟪B, v⟫_ℝ) = _
  rw [real_inner_comm B v]
  ring

/-- Operator-norm continuity of the face derivative follows solely from continuity
of its nonzero normal scale, face mass, and vector face moment. -/
theorem continuousAt_linearMap {P : Type*} [TopologicalSpace P]
    {A M : P → ℝ} {B : P → V} {p : P}
    (hA : ContinuousAt A p) (hM : ContinuousAt M p) (hB : ContinuousAt B p)
    (hzero : A p ≠ 0) :
    ContinuousAt (fun q => linearMap (A q) (M q) (B q)) p := by
  unfold linearMap
  exact (hA.inv₀ hzero).smul
    ((hM.smul continuousAt_const).add
      (((innerSL ℝ).continuous.continuousAt.comp hB).clm_comp continuousAt_const))

/-- Globally continuous coefficient fields give a continuous derivative field. -/
theorem continuous_linearMap {P : Type*} [TopologicalSpace P]
    {A M : P → ℝ} {B : P → V}
    (hA : Continuous A) (hM : Continuous M) (hB : Continuous B)
    (hzero : ∀ p, A p ≠ 0) :
    Continuous (fun q => linearMap (A q) (M q) (B q)) := by
  rw [continuous_iff_continuousAt]
  intro p
  exact continuousAt_linearMap hA.continuousAt hM.continuousAt hB.continuousAt (hzero p)

/-- The same coefficient criterion on an arbitrary configuration domain. -/
theorem continuousOn_linearMap {P : Type*} [TopologicalSpace P]
    {S : Set P} {A M : P → ℝ} {B : P → V}
    (hA : ContinuousOn A S) (hM : ContinuousOn M S) (hB : ContinuousOn B S)
    (hzero : ∀ p ∈ S, A p ≠ 0) :
    ContinuousOn (fun q => linearMap (A q) (M q) (B q)) S := by
  unfold linearMap
  exact (hA.inv₀ hzero).smul
    ((hM.smul continuousOn_const).add
      (((innerSL ℝ).continuous.comp_continuousOn hB).clm_comp continuousOn_const))

section Finite
variable {ι : Type*}

/-- Extract the difference of the two site and intercept perturbations. -/
def pairVariation (i j : ι) : ((ι → V) × (ι → ℝ)) →L[ℝ] V × ℝ :=
  (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => V) i -
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => V) j) : (ι → V) →L[ℝ] V).comp
    (ContinuousLinearMap.fst ℝ (ι → V) (ι → ℝ))).prod
  (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i -
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j) : (ι → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.snd ℝ (ι → V) (ι → ℝ)))

@[simp] lemma pairVariation_apply (i j : ι) (v : ι → V) (r : ι → ℝ) :
    pairVariation i j (v, r) = (v i - v j, r i - r j) := rfl

/-- Face derivatives assembled into one continuous linear cell-mass derivative.
The index set can exclude the diagonal or any inactive faces. -/
def cellLinearMap (J : Finset ι) (i : ι) (A M : ι → ℝ) (B : ι → V) :
    ((ι → V) × (ι → ℝ)) →L[ℝ] ℝ :=
  ∑ j ∈ J, (linearMap (A j) (M j) (B j)).comp (pairVariation i j)

@[simp] lemma cellLinearMap_apply (J : Finset ι) (i : ι)
    (A M : ι → ℝ) (B v : ι → V) (r : ι → ℝ) :
    cellLinearMap J i A M B (v, r) =
      ∑ j ∈ J, (((r i - r j) / A j) * M j +
        (1 / A j) * ⟪v i - v j, B j⟫_ℝ) := by
  simp [cellLinearMap]

/-- A finite cell derivative field is continuous in operator norm whenever all
its face scales and scalar/vector moments are continuous. -/
theorem continuousOn_cellLinearMap [Fintype ι]
    {P : Type*} [TopologicalSpace P] {S : Set P}
    (J : Finset ι) (i : ι) {A M : P → ι → ℝ} {B : P → ι → V}
    (hA : ∀ j ∈ J, ContinuousOn (fun p => A p j) S)
    (hM : ∀ j ∈ J, ContinuousOn (fun p => M p j) S)
    (hB : ∀ j ∈ J, ContinuousOn (fun p => B p j) S)
    (hzero : ∀ p ∈ S, ∀ j ∈ J, A p j ≠ 0) :
    ContinuousOn (fun p => cellLinearMap J i (A p) (M p) (B p)) S := by
  unfold cellLinearMap
  apply continuousOn_finsetSum J
  intro j hj
  exact (continuousOn_linearMap (hA j hj) (hM j hj) (hB j hj)
    (fun p hp => hzero p hp j hj)).clm_comp continuousOn_const

end Finite

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {z : X → V} {τ : X → ℝ}

/-- Integrability of a moving-face speed times its trace follows from the two
natural face-moment integrability hypotheses. -/
lemma integrable_speed_trace (hτ : Integrable τ μ)
    (hz : Integrable (fun x => τ x • z x) μ) (A r : ℝ) (v : V) :
    Integrable (fun x => ((r + ⟪v, z x⟫_ℝ) / A) * τ x) μ := by
  have heq : (fun x => ((r + ⟪v, z x⟫_ℝ) / A) * τ x) =
      (fun x => (r / A) * τ x + (1 / A) * ⟪v, τ x • z x⟫_ℝ) := by
    funext x
    simp only [inner_smul_right]
    ring
  rw [heq]
  exact (hτ.const_mul (r / A)).add ((hz.const_inner v).const_mul (1 / A))

variable [CompleteSpace V]

/-- The genuine face integral is linear in the site and intercept variation. -/
theorem integral_speed_trace (hτ : Integrable τ μ)
    (hz : Integrable (fun x => τ x • z x) μ) (A r : ℝ) (v : V) :
    (∫ x, ((r + ⟪v, z x⟫_ℝ) / A) * τ x ∂μ) =
      (r / A) * (∫ x, τ x ∂μ) + (1 / A) * ⟪v, ∫ x, τ x • z x ∂μ⟫_ℝ := by
  have hpoint : (fun x => ((r + ⟪v, z x⟫_ℝ) / A) * τ x) =
      (fun x => (r / A) * τ x + (1 / A) * ⟪v, τ x • z x⟫_ℝ) := by
    funext x
    simp only [inner_smul_right]
    ring
  rw [hpoint, integral_add (hτ.const_mul _) ((hz.const_inner v).const_mul _),
    integral_const_mul, integral_const_mul, integral_inner hz]

/-- The integral formula is exactly evaluation of the continuous linear face map. -/
theorem integral_speed_trace_eq_linearMap (hτ : Integrable τ μ)
    (hz : Integrable (fun x => τ x • z x) μ) (A r : ℝ) (v : V) :
    (∫ x, ((r + ⟪v, z x⟫_ℝ) / A) * τ x ∂μ) =
      linearMap A (∫ x, τ x ∂μ) (∫ x, τ x • z x ∂μ) (v, r) := by
  rw [linearMap_apply]
  exact integral_speed_trace hτ hz A r v

end Problem358.FaceDerivative

end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology InnerProductSpace

namespace Problem358.FaceDerivative

section LocalFields
variable {W F : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Local continuous line-derivative fields patch to C¹ without choosing a
 global normal chart. Each field need only be continuous at its own centre. -/
theorem contDiffOn_one_of_local_line_fields
    {S : Set W} (hS : IsOpen S) {f : W → F}
    (hlocal : ∀ x ∈ S, ∃ D : W → W →L[ℝ] F,
      ContinuousAt D x ∧
      ∀ᶠ y in 𝓝 x, ∀ v, HasLineDerivAt ℝ f (D y v) y v) :
    ContDiffOn ℝ 1 f S := by
  have hd : ∀ x ∈ S, DifferentiableAt ℝ f x := by
    intro x hx
    obtain ⟨D, hc, hD⟩ := hlocal x hx
    exact (Problem358.hasStrictFDerivAt_of_continuousAt_lineDeriv hD hc).hasFDerivAt.differentiableAt
  have hc : ContinuousOn (fderiv ℝ f) S := by
    intro x hx
    obtain ⟨D, hcont, hD⟩ := hlocal x hx
    have heq : fderiv ℝ f =ᶠ[𝓝 x] D := by
      filter_upwards [hD, hS.mem_nhds hx] with y hy hyS
      ext v
      exact ((hd y hyS).hasFDerivAt.hasLineDerivAt v).unique (hy v)
    exact (hcont.congr_of_eventuallyEq heq).continuousWithinAt
  apply Problem358.contDiffOn_one_of_continuousOn_lineDeriv hS
  · intro x hx v
    exact (hd x hx).hasFDerivAt.hasLineDerivAt v
  · exact hc

end LocalFields

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype ι]

omit [Fintype ι] in
/-- The scalar line formula of the cell calculus is a bounded linear directional
 derivative, with exactly the site/intercept order used by `closedCell`. -/
theorem hasLineDerivAt_of_cell_formula
    {f : ((ι → V) × (ι → ℝ)) → ℝ} {p : (ι → V) × (ι → ℝ)}
    (J : Finset ι) (i : ι) (A M : ι → ℝ) (B : ι → V)
    (hderiv : ∀ (v : ι → V) (r : ι → ℝ),
      HasDerivAt (fun t : ℝ => f (p + t • (v, r)))
        (∑ j ∈ J, (((r i - r j) / A j) * M j +
          (1 / A j) * ⟪v i - v j, B j⟫_ℝ)) 0) :
    ∀ w, HasLineDerivAt ℝ f (cellLinearMap J i A M B w) p w := by
  rintro ⟨v, r⟩
  simpa only [HasLineDerivAt, cellLinearMap_apply] using hderiv v r

/-- A local face chart need only provide coefficient continuity at its centre.
The formulas must hold at nearby configurations, but their coefficients need not
be defined by any global choice of hyperplane coordinates. -/
theorem hasStrictFDerivAt_of_local_cell_formula
    {f : ((ι → V) × (ι → ℝ)) → ℝ}
    (J : Finset ι) (i : ι)
    {A M : ((ι → V) × (ι → ℝ)) → ι → ℝ}
    {B : ((ι → V) × (ι → ℝ)) → ι → V}
    {p : (ι → V) × (ι → ℝ)}
    (hA : ∀ j ∈ J, ContinuousAt (fun q => A q j) p)
    (hM : ∀ j ∈ J, ContinuousAt (fun q => M q j) p)
    (hB : ∀ j ∈ J, ContinuousAt (fun q => B q j) p)
    (hzero : ∀ j ∈ J, A p j ≠ 0)
    (hderiv : ∀ᶠ q in 𝓝 p, ∀ (v : ι → V) (r : ι → ℝ),
      HasDerivAt (fun t : ℝ => f (q + t • (v, r)))
        (∑ j ∈ J, (((r i - r j) / A q j) * M q j +
          (1 / A q j) * ⟪v i - v j, B q j⟫_ℝ)) 0) :
    HasStrictFDerivAt f (cellLinearMap J i (A p) (M p) (B p)) p := by
  apply Problem358.hasStrictFDerivAt_of_continuousAt_lineDeriv
    (D := fun q => cellLinearMap J i (A q) (M q) (B q))
  · filter_upwards [hderiv] with q hq
    exact hasLineDerivAt_of_cell_formula J i (A q) (M q) (B q) hq
  · unfold cellLinearMap
    apply tendsto_finsetSum J
    intro j hj
    exact (continuousAt_linearMap (hA j hj) (hM j hj) (hB j hj)
      (hzero j hj)).clm_comp continuousAt_const

/-- Continuous scalar and vector face coefficients upgrade the actual line
 derivative formula to a strict Fréchet derivative. The domain may be any open
 set of admissible configurations; no global chart is required. -/
theorem hasStrictFDerivAt_of_cell_formula
    {S : Set ((ι → V) × (ι → ℝ))} (hS : IsOpen S)
    {f : ((ι → V) × (ι → ℝ)) → ℝ}
    (J : Finset ι) (i : ι)
    {A M : ((ι → V) × (ι → ℝ)) → ι → ℝ}
    {B : ((ι → V) × (ι → ℝ)) → ι → V}
    (hA : ∀ j ∈ J, ContinuousOn (fun p => A p j) S)
    (hM : ∀ j ∈ J, ContinuousOn (fun p => M p j) S)
    (hB : ∀ j ∈ J, ContinuousOn (fun p => B p j) S)
    (hzero : ∀ p ∈ S, ∀ j ∈ J, A p j ≠ 0)
    (hderiv : ∀ p ∈ S, ∀ (v : ι → V) (r : ι → ℝ),
      HasDerivAt (fun t : ℝ => f (p + t • (v, r)))
        (∑ j ∈ J, (((r i - r j) / A p j) * M p j +
          (1 / A p j) * ⟪v i - v j, B p j⟫_ℝ)) 0)
    {p : (ι → V) × (ι → ℝ)} (hp : p ∈ S) :
    HasStrictFDerivAt f (cellLinearMap J i (A p) (M p) (B p)) p := by
  apply Problem358.hasStrictFDerivAt_of_continuousAt_lineDeriv
    (D := fun q => cellLinearMap J i (A q) (M q) (B q))
  · filter_upwards [hS.mem_nhds hp] with q hq
    exact hasLineDerivAt_of_cell_formula J i (A q) (M q) (B q) (hderiv q hq)
  · exact ((continuousOn_cellLinearMap J i hA hM hB hzero) p hp).continuousAt
      (hS.mem_nhds hp)

/-- The joint C¹ conclusion needed before applying the normalized cell implicit
 function theorem. All geometry is confined to the scalar line formula and the
 continuous face coefficients. -/
theorem contDiffOn_one_of_cell_formula
    {S : Set ((ι → V) × (ι → ℝ))} (hS : IsOpen S)
    {f : ((ι → V) × (ι → ℝ)) → ℝ}
    (J : Finset ι) (i : ι)
    {A M : ((ι → V) × (ι → ℝ)) → ι → ℝ}
    {B : ((ι → V) × (ι → ℝ)) → ι → V}
    (hA : ∀ j ∈ J, ContinuousOn (fun p => A p j) S)
    (hM : ∀ j ∈ J, ContinuousOn (fun p => M p j) S)
    (hB : ∀ j ∈ J, ContinuousOn (fun p => B p j) S)
    (hzero : ∀ p ∈ S, ∀ j ∈ J, A p j ≠ 0)
    (hderiv : ∀ p ∈ S, ∀ (v : ι → V) (r : ι → ℝ),
      HasDerivAt (fun t : ℝ => f (p + t • (v, r)))
        (∑ j ∈ J, (((r i - r j) / A p j) * M p j +
          (1 / A p j) * ⟪v i - v j, B p j⟫_ℝ)) 0) :
    ContDiffOn ℝ 1 f S := by
  apply Problem358.contDiffOn_one_of_continuousOn_lineDeriv hS
  · intro p hp
    exact hasLineDerivAt_of_cell_formula J i (A p) (M p) (B p) (hderiv p hp)
  · exact continuousOn_cellLinearMap J i hA hM hB hzero

section Integral
variable [CompleteSpace V]
variable {X : ι → Type*} [∀ j, MeasurableSpace (X j)]

omit [Fintype ι] in
/-- Convert the actual finite sum of moving-face integrals to the bounded
linear cell derivative. Each face may have its own intrinsic parameter space. -/
theorem sum_integral_speed_trace_eq_cellLinearMap
    (J : Finset ι) (i : ι) (μ : ∀ j, Measure (X j))
    (z : ∀ j, X j → V) (τ : ∀ j, X j → ℝ)
    (hτ : ∀ j ∈ J, Integrable (τ j) (μ j))
    (hz : ∀ j ∈ J, Integrable (fun x => τ j x • z j x) (μ j))
    (A : ι → ℝ) (v : ι → V) (r : ι → ℝ) :
    (∑ j ∈ J, ∫ x, ((r i - r j + ⟪v i - v j, z j x⟫_ℝ) / A j) *
      τ j x ∂μ j) =
      cellLinearMap J i A (fun j => ∫ x, τ j x ∂μ j)
        (fun j => ∫ x, τ j x • z j x ∂μ j) (v, r) := by
  rw [cellLinearMap_apply]
  apply Finset.sum_congr rfl
  intro j hj
  exact integral_speed_trace (hτ j hj) (hz j hj) (A j) (r i - r j) (v i - v j)

end Integral

/-- Simultaneous strict differentiation of a finite family of cell quantities.
No extra operator-continuity argument is needed after the scalar quantities
have been treated. -/
theorem hasStrictFDerivAt_cells
    {κ : Type*} [Fintype κ]
    {f : ((ι → V) × (ι → ℝ)) → κ → ℝ}
    {D : κ → ((ι → V) × (ι → ℝ)) →L[ℝ] ℝ}
    {p : (ι → V) × (ι → ℝ)}
    (h : ∀ k, HasStrictFDerivAt (fun q => f q k) (D k) p) :
    HasStrictFDerivAt f (ContinuousLinearMap.pi D) p :=
  hasStrictFDerivAt_pi.mpr h

end Problem358.FaceDerivative

end

noncomputable section

open MeasureTheory
open scoped Topology InnerProductSpace

namespace Problem358.FaceDerivative

/-- In finite-dimensional Euclidean space, scalar coordinate face integrals
control the vector face moment, including its transverse normalization. -/
theorem continuousAt_normalized_faceMoment_of_coordinates
    {d : ℕ} {P X : Type*} [TopologicalSpace P] [MeasurableSpace X]
    {μ : Measure X} {a : P → ℝ} {τ : P → X → ℝ} {z : P → X → E d}
    {p : P}
    (hint : ∀ q, Integrable (fun x => τ q x • z q x) μ)
    (hcoord : ∀ k : Fin d, ContinuousAt
      (fun q => (∫ x, τ q x * z q x k ∂μ) / a q) p) :
    ContinuousAt (fun q => (a q)⁻¹ • ∫ x, τ q x • z q x ∂μ) p := by
  have heq (q : P) (k : Fin d) :
      ((a q)⁻¹ • ∫ x, τ q x • z q x ∂μ) k =
        (∫ x, τ q x * z q x k ∂μ) / a q := by
    have h := ((EuclideanSpace.proj k).integral_comp_comm (hint q)).symm
    change (a q)⁻¹ * (∫ x, τ q x • z q x ∂μ) k = _
    rw [show (∫ x, τ q x • z q x ∂μ) k =
      ∫ x, τ q x * z q x k ∂μ by simpa using h]
    ring
  have hc : ContinuousAt (fun q k =>
      ((a q)⁻¹ • ∫ x, τ q x • z q x ∂μ) k) p := by
    apply continuousAt_pi.mpr
    intro k
    simpa only [heq] using hcoord k
  exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).continuousAt.comp hc

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Absorb the transverse normal scale into the scalar and vector coefficients.
The equality remains valid for the totalized zero denominator. -/
theorem cellLinearMap_normalize (J : Finset ι) (i : ι)
    (A M : ι → ℝ) (B : ι → V) :
    cellLinearMap J i A M B =
      cellLinearMap J i (fun _ => 1) (fun j => M j / A j)
        (fun j => (A j)⁻¹ • B j) := by
  apply ContinuousLinearMap.ext
  rintro ⟨v, r⟩
  simp only [cellLinearMap_apply, div_one, one_mul, inner_smul_right]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end Problem358.FaceDerivative

end

end OAI
