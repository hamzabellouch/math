import OAI.Analysis.Naimark.Representations

namespace OAI

noncomputable section

namespace NaimarkZFC

attribute [local instance] Classical.propDecidable

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def IsTracialPositive (τ : A →ₚ[ℂ] ℂ) : Prop :=
  ∀ a b, τ (a * b) = τ (b * a)

theorem preGNS_norm_star (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ) (a : A) :
    ‖τ.toPreGNS (star a)‖ = ‖τ.toPreGNS a‖ := by
  simp only [PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.ofPreGNS_toPreGNS,
    star_star]
  rw [hτ a (star a)]

def rightMulMapPreGNS (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ) (a : A) :
    τ.PreGNS →L[ℂ] τ.PreGNS :=
  (τ.toPreGNS.toLinearMap ∘ₗ LinearMap.mulRight ℂ a ∘ₗ τ.ofPreGNS.toLinearMap).mkContinuous
    ‖a‖ fun x => by
      change ‖τ.toPreGNS (τ.ofPreGNS x * a)‖ ≤ ‖a‖ * ‖x‖
      calc
        _ = ‖τ.toPreGNS (star (τ.ofPreGNS x * a))‖ := (preGNS_norm_star τ hτ _).symm
        _ = ‖τ.leftMulMapPreGNS (star a) (τ.toPreGNS (star (τ.ofPreGNS x)))‖ := by
          simp [star_mul]
        _ ≤ ‖star a‖ * ‖τ.toPreGNS (star (τ.ofPreGNS x))‖ := by
          apply le_trans ((τ.leftMulMapPreGNS (star a)).le_opNorm _)
          gcongr
          exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
        _ = _ := by rw [norm_star, preGNS_norm_star τ hτ, τ.toPreGNS_ofPreGNS]

@[simp] theorem rightMulMapPreGNS_apply (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (a : A) (x : τ.PreGNS) :
    rightMulMapPreGNS τ hτ a x = τ.toPreGNS (τ.ofPreGNS x * a) := rfl

def gnsRight (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ) (a : A) : τ.GNS →L[ℂ] τ.GNS :=
  (rightMulMapPreGNS τ hτ a).completion

@[simp] theorem gnsRight_coe (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ) (a b : A) :
    gnsRight τ hτ a (τ.toPreGNS b : τ.GNS) = (τ.toPreGNS (b * a) : τ.GNS) := by
  simp [gnsRight]

@[simp] theorem gnsLeft_coe (τ : A →ₚ[ℂ] ℂ) (a b : A) :
    τ.gnsStarAlgHom a (τ.toPreGNS b : τ.GNS) = (τ.toPreGNS (a * b) : τ.GNS) := by
  simp [PositiveLinearMap.gnsStarAlgHom, PositiveLinearMap.gnsNonUnitalStarAlgHom,
    ContinuousLinearMap.completion_apply_coe, PositiveLinearMap.leftMulMapPreGNS]

theorem gnsLeft_commute_right (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ) (a b : A) :
    Commute (τ.gnsStarAlgHom a) (gnsRight τ hτ b) := by
  ext x
  induction x using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    obtain ⟨c, rfl⟩ := τ.toPreGNS.surjective x
    simp [mul_assoc]

theorem gnsRight_star (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ) (a : A) :
    gnsRight τ hτ (star a) = star (gnsRight τ hτ a) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x, y using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    obtain ⟨b, rfl⟩ := τ.toPreGNS.surjective x
    obtain ⟨c, rfl⟩ := τ.toPreGNS.surjective y
    simp only [gnsRight_coe, Completion.inner_coe, PositiveLinearMap.preGNS_inner_def,
      PositiveLinearMap.ofPreGNS_toPreGNS, star_mul, star_star]
    rw [mul_assoc, hτ a (star b * c), mul_assoc]

theorem gnsRight_mul (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ) (a b : A) :
    gnsRight τ hτ (a * b) = gnsRight τ hτ b * gnsRight τ hτ a := by
  ext x
  induction x using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    obtain ⟨c, rfl⟩ := τ.toPreGNS.surjective x
    simp [mul_assoc]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def gnsRightStarAlgHom (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ) :
    Aᵐᵒᵖ →⋆ₐ[ℂ] (τ.GNS →L[ℂ] τ.GNS) where
  toFun a := gnsRight τ hτ a.unop
  map_zero' := by
    ext x
    induction x using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x =>
      obtain ⟨b, rfl⟩ := τ.toPreGNS.surjective x
      simp [Completion.coe_zero]
  map_add' a b := by
    ext x
    induction x using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x =>
      obtain ⟨c, rfl⟩ := τ.toPreGNS.surjective x
      simp [mul_add, Completion.coe_add]
  map_one' := by
    ext x
    induction x using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x =>
      obtain ⟨b, rfl⟩ := τ.toPreGNS.surjective x
      simp
  map_mul' a b := gnsRight_mul τ hτ b.unop a.unop
  commutes' c := by
    ext x
    induction x using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x =>
      obtain ⟨b, rfl⟩ := τ.toPreGNS.surjective x
      simp [Algebra.algebraMap_eq_smul_one, Completion.coe_smul]
  map_star' a := gnsRight_star τ hτ a.unop

@[simp] theorem gnsRightStarAlgHom_apply (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (a : A) : gnsRightStarAlgHom τ hτ (MulOpposite.op a) = gnsRight τ hτ a := rfl

def traceVacuum (τ : A →ₚ[ℂ] ℂ) : τ.GNS := (τ.toPreGNS 1 : τ.GNS)

@[simp] theorem traceVacuum_left (τ : A →ₚ[ℂ] ℂ) (a : A) :
    τ.gnsStarAlgHom a (traceVacuum τ) = (τ.toPreGNS a : τ.GNS) := by
  simp [traceVacuum]

@[simp] theorem traceVacuum_right (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ) (a : A) :
    gnsRight τ hτ a (traceVacuum τ) = (τ.toPreGNS a : τ.GNS) := by
  simp [traceVacuum]

theorem traceVacuum_cyclic (τ : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a : A => τ.gnsStarAlgHom a (traceVacuum τ)) := by
  simp only [traceVacuum_left]
  exact Completion.denseRange_coe.comp τ.toPreGNS.surjective.denseRange
    (Completion.continuous_coe _)

theorem traceGNS_injective (τ : A →ₚ[ℂ] ℂ)
    (hf : ∀ a : A, τ (star a * a) = 0 → a = 0) :
    Function.Injective (fun a : A => (τ.toPreGNS a : τ.GNS)) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply hf
  have hcoe : (τ.toPreGNS (a-b) : τ.GNS) = 0 := by
    simpa [Completion.coe_sub] using sub_eq_zero.mpr hab
  have hnorm : ‖τ.toPreGNS (a-b)‖ = 0 := by
    simpa only [Completion.norm_coe, norm_zero] using congrArg norm hcoe
  simpa only [hnorm, Complex.ofReal_zero, zero_pow (by decide : 2 ≠ 0),
    PositiveLinearMap.ofPreGNS_toPreGNS] using (τ.preGNS_norm_sq (τ.toPreGNS (a-b))).symm

theorem traceRepresentation_injective (τ : A →ₚ[ℂ] ℂ)
    (hf : ∀ a : A, τ (star a * a) = 0 → a = 0) : Function.Injective τ.gnsStarAlgHom := by
  intro a b hab
  apply traceGNS_injective τ hf
  simpa only [traceVacuum_left] using congrArg (fun T => T (traceVacuum τ)) hab

open Filter
open scoped Topology

theorem tendsto_zero_of_dense_contractives {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] {ι β : Type*} (l : Filter ι) (T : ι → H →L[ℂ] H)
    (hT : ∀ i, ‖T i‖ ≤ 1) (v : β → H) (hv : DenseRange v)
    (hlim : ∀ b, Tendsto (fun i => T i (v b)) l (𝓝 0)) (x : H) :
    Tendsto (fun i => T i x) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨b, hb⟩ := hv.exists_dist_lt x (half_pos hε)
  have he := (Metric.tendsto_nhds.mp (hlim b)) (ε/2) (half_pos hε)
  filter_upwards [he] with i hi
  rw [dist_zero_right] at hi ⊢
  have hxb : ‖T i (x-v b)‖ < ε/2 := by
    calc
      _ ≤ ‖T i‖ * ‖x-v b‖ := (T i).le_opNorm _
      _ ≤ 1 * ‖x-v b‖ := mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _)
      _ < ε/2 := by simpa only [one_mul, dist_eq_norm] using hb
  have heq : T i x = T i (x-v b) + T i (v b) := by rw [map_sub]; abel
  rw [heq]
  exact (norm_add_le _ _).trans_lt (by linarith)

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem gns_projection_norm (τ : A →ₚ[ℂ] ℂ) (q : A) (hq : IsStarProjection q) :
    ‖(τ.toPreGNS q : τ.GNS)‖ = Real.sqrt (τ q).re := by
  rw [Completion.norm_coe, PositiveLinearMap.preGNS_norm_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, hq.isSelfAdjoint.star_eq,
    hq.isIdempotentElem.eq]

theorem trace_projection_strong_zero (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    {ι : Type*} (l : Filter ι) (p : ι → A) (hp : ∀ i, IsStarProjection (p i))
    (hlim : Tendsto (fun i => (τ (p i)).re) l (𝓝 0)) (x : τ.GNS) :
    Tendsto (fun i => τ.gnsStarAlgHom (p i) x) l (𝓝 0) := by
  have hvac : Tendsto (fun i => (τ.toPreGNS (p i) : τ.GNS)) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [gns_projection_norm τ _ (hp _)]
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hlim
  apply tendsto_zero_of_dense_contractives l (fun i => τ.gnsStarAlgHom (p i))
    (fun i => (NonUnitalStarAlgHom.norm_apply_le τ.gnsStarAlgHom (p i)).trans ((hp i).norm_le _))
    (fun a : A => (τ.toPreGNS a : τ.GNS))
    (Completion.denseRange_coe.comp τ.toPreGNS.surjective.denseRange (Completion.continuous_coe _))
    _ x
  intro a
  have h := (gnsRight τ hτ a).continuous.continuousAt.tendsto.comp hvac
  simpa [Function.comp_def] using h

theorem trace_projection_right_strong_zero (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    {ι : Type*} (l : Filter ι) (p : ι → A) (hp : ∀ i, IsStarProjection (p i))
    (hlim : Tendsto (fun i => (τ (p i)).re) l (𝓝 0)) (x : τ.GNS) :
    Tendsto (fun i => gnsRight τ hτ (p i) x) l (𝓝 0) := by
  have hvac : Tendsto (fun i => (τ.toPreGNS (p i) : τ.GNS)) l (𝓝 0) := by
    simpa only [traceVacuum_left] using trace_projection_strong_zero τ hτ l p hp hlim (traceVacuum τ)
  apply tendsto_zero_of_dense_contractives l (fun i => gnsRight τ hτ (p i))
    (fun i => (NonUnitalStarAlgHom.norm_apply_le (gnsRightStarAlgHom τ hτ)
      (MulOpposite.op (p i))).trans ((hp i).norm_le _))
    (fun a : A => (τ.toPreGNS a : τ.GNS))
    (Completion.denseRange_coe.comp τ.toPreGNS.surjective.denseRange (Completion.continuous_coe _))
    _ x
  intro a
  have h := (τ.gnsStarAlgHom a).continuous.continuousAt.tendsto.comp hvac
  simpa [Function.comp_def] using h

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def restrictRepresentation {A : Type*} [CStarAlgebra A]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (M : Submodule ℂ H) [CompleteSpace M]
    (hinv : ∀ a : A, ∀ x ∈ M, π a x ∈ M) : A →⋆ₐ[ℂ] (M →L[ℂ] M) where
  toFun a := (π a).restrict (hinv a)
  map_zero' := by ext x; simp
  map_one' := by ext x; simp
  map_add' a b := by ext x; simp
  map_mul' a b := by ext x; simp
  commutes' c := by
    ext x
    change (π (algebraMap ℂ A c)) (x : H) = c • (x : H)
    exact congrArg (fun T : H →L[ℂ] H => T (x : H)) (π.commutes c)
  map_star' a := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    change inner ℂ (π (star a) (x : H)) (y : H) = inner ℂ (x : H) (π a (y : H))
    rw [map_star]
    exact ContinuousLinearMap.adjoint_inner_left _ _ _

@[simp] theorem restrictRepresentation_apply {A : Type*} [CStarAlgebra A]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (M : Submodule ℂ H) [CompleteSpace M]
    (hinv : ∀ a : A, ∀ x ∈ M, π a x ∈ M) (a : A) (x : M) :
    (restrictRepresentation π M hinv a x : H) = π a (x : H) := rfl

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem gnsRight_projection (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : A) (hq : IsStarProjection q) : IsStarProjection (gnsRight τ hτ q) := by
  refine ⟨?_, ?_⟩
  · change gnsRight τ hτ q * gnsRight τ hτ q = gnsRight τ hτ q
    rw [← gnsRight_mul, hq.isIdempotentElem.eq]
  · change star (gnsRight τ hτ q) = gnsRight τ hτ q
    rw [← gnsRight_star, hq.isSelfAdjoint.star_eq]

def TraceColumn (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) : Submodule ℂ τ.GNS :=
  (gnsRight τ hτ q.1).range

instance traceColumnComplete (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) : CompleteSpace (TraceColumn τ hτ q) :=
  (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (gnsRight_projection τ hτ q.1 q.2).isIdempotentElem).completeSpace_coe

theorem traceColumn_invariant (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) (a : A) (x : τ.GNS)
    (hx : x ∈ TraceColumn τ hτ q) : τ.gnsStarAlgHom a x ∈ TraceColumn τ hτ q := by
  rcases hx with ⟨y, rfl⟩
  exact ⟨τ.gnsStarAlgHom a y,
    (congrArg (fun T : τ.GNS →L[ℂ] τ.GNS => T y) (gnsLeft_commute_right τ hτ a q.1).eq).symm⟩

def traceColumnRepresentation (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) :
    A →⋆ₐ[ℂ] (TraceColumn τ hτ q →L[ℂ] TraceColumn τ hτ q) :=
  restrictRepresentation τ.gnsStarAlgHom (TraceColumn τ hτ q) (traceColumn_invariant τ hτ q)

def columnVacuum (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) : TraceColumn τ hτ q :=
  ⟨(τ.toPreGNS q.1 : τ.GNS), traceVacuum τ, traceVacuum_right τ hτ q.1⟩

@[simp] theorem columnVacuum_norm (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) :
    ‖columnVacuum τ hτ q‖ = Real.sqrt (τ q.1).re :=
  gns_projection_norm τ q.1 q.2

def columnUnit (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) : TraceColumn τ hτ q :=
  ((Real.sqrt (τ q.1).re)⁻¹ : ℂ) • columnVacuum τ hτ q

theorem columnUnit_norm (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) (ht : 0 < (τ q.1).re) :
    ‖columnUnit τ hτ q‖ = 1 := by
  rw [columnUnit, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _),
    columnVacuum_norm, inv_mul_cancel₀ (Real.sqrt_pos.mpr ht).ne']

@[simp] theorem columnVacuum_action (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) (a : A) :
    (traceColumnRepresentation τ hτ q a (columnVacuum τ hτ q) : τ.GNS) =
      (τ.toPreGNS (a * q.1) : τ.GNS) := by
  exact gnsLeft_coe τ a q.1

open Filter
open scoped Topology
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in

theorem finiteAtomSum_projection (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0) (s : Finset V) :
    IsStarProjection (∑ l ∈ s, (e l).1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    apply (e a).property.add ih
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro b hb
    exact horth a b (fun h => ha (h ▸ hb))

theorem traceAtoms_jointKernel (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    (hmass : HasSum (fun l => (τ (e l).1).re) (τ 1).re)
    (x : τ.GNS) (hx : ∀ l, τ.gnsStarAlgHom (e l).1 x = 0) : x = 0 := by
  classical
  let p : Finset V → A := fun s => 1 - ∑ l ∈ s, (e l).1
  have hp : ∀ s, IsStarProjection (p s) := fun s => (finiteAtomSum_projection e horth s).one_sub
  have hlim : Tendsto (fun s => (τ (p s)).re) atTop (𝓝 0) := by
    simpa only [p, map_sub, map_sum, Complex.sub_re, Complex.re_sum, sub_self] using
      (tendsto_const_nhds (x := (τ 1).re) (f := (atTop : Filter (Finset V)))).sub hmass
  have hstrong := trace_projection_strong_zero τ hτ atTop p hp hlim x
  have he (s : Finset V) : τ.gnsStarAlgHom (p s) x = x := by
    simp only [p, map_sub, map_one, map_sum, sub_apply,
      one_apply_eq_self, sum_apply, hx, Finset.sum_const_zero,
      sub_zero]
  simp only [he] at hstrong
  exact tendsto_nhds_unique tendsto_const_nhds hstrong

theorem columnAtoms_jointKernel (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    (hmass : HasSum (fun l => (τ (e l).1).re) (τ 1).re) (r : V)
    (x : TraceColumn τ hτ (e r))
    (hx : ∀ l, traceColumnRepresentation τ hτ (e r) (e l).1 x = 0) : x = 0 := by
  apply Subtype.ext
  apply traceAtoms_jointKernel τ hτ e horth hmass (x : τ.GNS)
  intro l
  exact congrArg Subtype.val (hx l)

theorem columnUnit_ownRow (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {a : A // IsStarProjection a}) :
    traceColumnRepresentation τ hτ q q.1 (columnUnit τ hτ q) = columnUnit τ hτ q := by
  rw [columnUnit, map_smul]
  congr 1
  apply Subtype.ext
  rw [columnVacuum_action, q.property.isIdempotentElem.eq]
  rfl

open scoped InnerProductSpace
variable {V : Type*} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

def centeredRow (M : V → Submodule ℂ H) (ξ : H) (l : V) : Submodule ℂ H :=
  M l ⊓ (ℂ ∙ ξ)ᗮ

instance centeredRowComplete (M : V → Submodule ℂ H) [∀ l, CompleteSpace (M l)]
    (ξ : H) (l : V) : CompleteSpace (centeredRow M ξ l) := by
  have hm : IsClosed (M l : Set H) :=
    (completeSpace_coe_iff_isComplete.mp (inferInstance : CompleteSpace (M l))).isClosed
  exact (hm.inter (Submodule.isClosed_orthogonal _)).completeSpace_coe

def vacuumRowFamily (M : V → Submodule ℂ H) (ξ : H) {J : V → Type*}
    (b : ∀ l, HilbertBasis (J l) ℂ (centeredRow M ξ l)) : Option (Σ l, J l) → H
  | none => ξ
  | some ⟨l,j⟩ => b l j

omit [CompleteSpace H] in
theorem vacuumRowFamily_orthonormal (M : V → Submodule ℂ H) (ξ : H)
    (hξ : ‖ξ‖ = 1) (horth : ∀ l k, l ≠ k → ∀ x ∈ M l, ∀ y ∈ M k, inner ℂ x y = 0)
    {J : V → Type*} (b : ∀ l, HilbertBasis (J l) ℂ (centeredRow M ξ l)) :
    Orthonormal ℂ (vacuumRowFamily M ξ b) := by
  classical
  refine ⟨?_, ?_⟩
  · rintro (_ | ⟨l,j⟩)
    · exact hξ
    · exact (b l).orthonormal.1 j
  · rintro (_ | ⟨l,j⟩) (_ | ⟨k,t⟩) hne
    · exact False.elim (hne rfl)
    · exact (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b k t).property.2)
    · exact (Submodule.mem_orthogonal_singleton_iff_inner_left.mp (b l j).property.2)
    · by_cases hlk : l = k
      · subst k
        have hjt : j ≠ t := fun h => hne (by subst t; rfl)
        exact (b l).orthonormal.2 hjt
      · exact horth l k hlk (b l j) (b l j).property.1 (b k t) (b k t).property.1

omit [CompleteSpace H] in

theorem orthogonal_of_basis_inner_zero (M : Submodule ℂ H) [CompleteSpace M]
    {J : Type*} (b : HilbertBasis J ℂ M) (x : H)
    (hx : ∀ j, inner ℂ (b j : H) x = 0) : x ∈ Mᗮ := by
  have hp : M.orthogonalProjectionOnto x = 0 := by
    apply b.repr.injective
    ext j
    simp only [map_zero, lp.coeFn_zero, Pi.zero_apply, HilbertBasis.repr_apply_apply]
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
    exact hx j
  apply (M.mem_orthogonal x).mpr
  intro y hy
  have hi := M.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨y, hy⟩ x
  rw [hp, inner_zero_right] at hi
  exact hi.symm

def vacuumRowBasis (M : V → Submodule ℂ H) [∀ l, CompleteSpace (M l)]
    (ξ : H) (r : V) (hξ : ‖ξ‖ = 1) (hmem : ξ ∈ M r)
    (horth : ∀ l k, l ≠ k → ∀ x ∈ M l, ∀ y ∈ M k, inner ℂ x y = 0)
    (htotal : ∀ x : H, (∀ l, ∀ y ∈ M l, inner ℂ y x = 0) → x = 0)
    {J : V → Type*} (b : ∀ l, HilbertBasis (J l) ℂ (centeredRow M ξ l)) :
    HilbertBasis (Option (Σ l, J l)) ℂ H :=
  HilbertBasis.mkOfOrthogonalEqBot (vacuumRowFamily_orthonormal M ξ hξ horth b) (by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Submodule.mem_bot]
    have hf : ∀ j, inner ℂ (vacuumRowFamily M ξ b j) x = 0 := fun j =>
      (Submodule.mem_orthogonal _ _).mp hx _ (Submodule.subset_span ⟨j, rfl⟩)
    have hv : inner ℂ ξ x = 0 := hf none
    have hc (l : V) : x ∈ (centeredRow M ξ l)ᗮ :=
      orthogonal_of_basis_inner_zero _ (b l) x (fun j => hf (some ⟨l,j⟩))
    apply htotal x
    intro l y hy
    by_cases hlr : l = r
    · subst l
      have hnorm : inner ℂ ξ ξ = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hξ]; norm_num
      have hyc : y - (inner ℂ ξ y) • ξ ∈ centeredRow M ξ r := by
        refine ⟨(M r).sub_mem hy ((M r).smul_mem _ hmem), ?_⟩
        apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        rw [inner_sub_right,
          inner_smul_right, hnorm, mul_one, sub_self]
      have hh := (Submodule.mem_orthogonal _ _).mp (hc r) _ hyc
      simpa only [inner_sub_left, inner_smul_left, hv, mul_zero, sub_zero] using hh
    · have hyc : y ∈ centeredRow M ξ l := by
        refine ⟨hy, ?_⟩
        apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        exact horth r l (Ne.symm hlr) ξ hmem y hy
      exact (Submodule.mem_orthogonal _ _).mp (hc l) y hyc)

@[simp] theorem vacuumRowBasis_apply (M : V → Submodule ℂ H) [∀ l, CompleteSpace (M l)]
    (ξ : H) (r : V) (hξ : ‖ξ‖ = 1) (hmem : ξ ∈ M r)
    (horth : ∀ l k, l ≠ k → ∀ x ∈ M l, ∀ y ∈ M k, inner ℂ x y = 0)
    (htotal : ∀ x : H, (∀ l, ∀ y ∈ M l, inner ℂ y x = 0) → x = 0)
    {J : V → Type*} (b : ∀ l, HilbertBasis (J l) ℂ (centeredRow M ξ l)) (j) :
    vacuumRowBasis M ξ r hξ hmem horth htotal b j = vacuumRowFamily M ξ b j := by
  simp [vacuumRowBasis]

open scoped InnerProductSpace
variable {V A H : Type*} [CStarAlgebra A] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

def projectionRow (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (e : V → {a : A // IsStarProjection a}) (l : V) : Submodule ℂ H :=
  (π (e l).1).range

instance projectionRowComplete (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (e : V → {a : A // IsStarProjection a}) (l : V) :
    CompleteSpace (projectionRow π e l) :=
  (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    ((e l).property.map π).isIdempotentElem).completeSpace_coe

theorem projectionRow_orthogonal (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    (l k : V) (hlk : l ≠ k) (x : H) (hx : x ∈ projectionRow π e l)
    (y : H) (hy : y ∈ projectionRow π e k) : inner ℂ x y = 0 := by
  rcases hx with ⟨u, rfl⟩
  rcases hy with ⟨v, rfl⟩
  have hs : (π (e l).1).adjoint = π (e l).1 := by
    change star (π (e l).1) = π (e l).1
    rw [← map_star, (e l).property.isSelfAdjoint.star_eq]
  change inner ℂ (π (e l).1 u) (π (e k).1 v) = 0
  rw [← ContinuousLinearMap.adjoint_inner_right, hs]
  have hm : π (e l).1 (π (e k).1 v) = 0 := by
    change (π (e l).1 * π (e k).1) v = 0
    rw [← map_mul, horth l k hlk, map_zero, zero_apply]
  rw [hm, inner_zero_right]

theorem projectionRow_total (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (e : V → {a : A // IsStarProjection a})
    (hker : ∀ x : H, (∀ l, π (e l).1 x = 0) → x = 0)
    (x : H) (hx : ∀ l, ∀ y ∈ projectionRow π e l, inner ℂ y x = 0) : x = 0 := by
  apply hker x
  intro l
  have hs : (π (e l).1).adjoint = π (e l).1 := ((e l).property.map π).isSelfAdjoint.star_eq
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [← ContinuousLinearMap.adjoint_inner_right, hs]
  have he : π (e l).1 (π (e l).1 x) = π (e l).1 x :=
    congrArg (fun T : H →L[ℂ] H => T x) ((e l).property.map π).isIdempotentElem.eq
  rw [he]
  exact inner_eq_zero_symm.mpr (hx l (π (e l).1 x) ⟨x,rfl⟩)

theorem projectionRow_eigen (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    [DecidableEq V] (l k : V) (x : H) (hx : x ∈ projectionRow π e k) :
    π (e l).1 x = if l = k then x else 0 := by
  rcases hx with ⟨u,rfl⟩
  change (π (e l).1 * π (e k).1) u = _
  rw [← map_mul]
  by_cases hlk : l = k
  · subst k; rw [(e l).property.isIdempotentElem.eq, ite_eq_left rfl]; rfl
  · rw [horth l k hlk, map_zero, zero_apply, ite_eq_right hlk]

open scoped InnerProductSpace lp

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def hilbertChoiceSet : Set H := (exists_hilbertBasis ℂ H).choose

def hilbertChoiceBasis : HilbertBasis (hilbertChoiceSet H) ℂ H :=
  (exists_hilbertBasis ℂ H).choose_spec.choose

variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def CenteredColumn (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a}) (l r : V) :
    Submodule ℂ (TraceColumn τ hτ (e r)) :=
  centeredRow (projectionRow (traceColumnRepresentation τ hτ (e r)) e)
    (columnUnit τ hτ (e r)) l

instance centeredColumnComplete (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a}) (l r : V) :
    CompleteSpace (CenteredColumn τ hτ e l r) := by
  unfold CenteredColumn
  infer_instance

abbrev CenteredColumnIndex (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a}) (l r : V) :=
  hilbertChoiceSet (CenteredColumn τ hτ e l r)

def tracialColumnBasis (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    (hmass : HasSum (fun l => (τ (e l).1).re) (τ 1).re)
    (hpos : ∀ l, 0 < (τ (e l).1).re) (r : V) :
    HilbertBasis (Option (Σ l, CenteredColumnIndex τ hτ e l r)) ℂ (TraceColumn τ hτ (e r)) :=
  vacuumRowBasis (projectionRow (traceColumnRepresentation τ hτ (e r)) e)
    (columnUnit τ hτ (e r)) r (columnUnit_norm τ hτ (e r) (hpos r))
    ⟨columnUnit τ hτ (e r), columnUnit_ownRow τ hτ (e r)⟩
    (projectionRow_orthogonal _ e horth)
    (projectionRow_total _ e (columnAtoms_jointKernel τ hτ e horth hmass r))
    (fun l => hilbertChoiceBasis (CenteredColumn τ hτ e l r))

@[simp] theorem tracialColumnBasis_none (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    (hmass : HasSum (fun l => (τ (e l).1).re) (τ 1).re)
    (hpos : ∀ l, 0 < (τ (e l).1).re) (r : V) :
    tracialColumnBasis τ hτ e horth hmass hpos r none = columnUnit τ hτ (e r) := by
  simp [tracialColumnBasis, vacuumRowBasis, vacuumRowFamily]

def columnVertex {J : V → Type*} (r : V) : Option (Σ l, J l) → V
  | none => r
  | some ⟨l,_⟩ => l

theorem tracialColumnBasis_row (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    (hmass : HasSum (fun l => (τ (e l).1).re) (τ 1).re)
    (hpos : ∀ l, 0 < (τ (e l).1).re) (r : V)
    (j : Option (Σ l, CenteredColumnIndex τ hτ e l r)) :
    tracialColumnBasis τ hτ e horth hmass hpos r j ∈
      projectionRow (traceColumnRepresentation τ hτ (e r)) e (columnVertex r j) := by
  cases j with
  | none => exact ⟨columnUnit τ hτ (e r), by
      rw [tracialColumnBasis_none]
      exact columnUnit_ownRow τ hτ (e r)⟩
  | some j =>
    rcases j with ⟨l,t⟩
    simp only [tracialColumnBasis, vacuumRowBasis, HilbertBasis.coe_mkOfOrthogonalEqBot,
      vacuumRowFamily]
    exact (hilbertChoiceBasis (CenteredColumn τ hτ e l r) t).property.1

def indexedColumnRepresentation (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    (hmass : HasSum (fun l => (τ (e l).1).re) (τ 1).re)
    (hpos : ∀ l, 0 < (τ (e l).1).re) (r : V) :
    A →⋆ₐ[ℂ] (ℓ²(Option (Σ l, CenteredColumnIndex τ hτ e l r), ℂ) →L[ℂ]
      ℓ²(Option (Σ l, CenteredColumnIndex τ hτ e l r), ℂ)) := by
  letI : Algebra ℂ (TraceColumn τ hτ (e r) →L[ℂ] TraceColumn τ hτ (e r)) :=
    ContinuousLinearMap.algebra
  exact ((tracialColumnBasis τ hτ e horth hmass hpos r).repr.conjStarAlgEquiv).toStarAlgHom.comp
    (traceColumnRepresentation τ hτ (e r))

theorem indexedColumnRepresentation_apply (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    (hmass : HasSum (fun l => (τ (e l).1).re) (τ 1).re)
    (hpos : ∀ l, 0 < (τ (e l).1).re) (r : V) (a : A)
    (x : ℓ²(Option (Σ l, CenteredColumnIndex τ hτ e l r), ℂ)) :
    indexedColumnRepresentation τ hτ e horth hmass hpos r a x =
      (tracialColumnBasis τ hτ e horth hmass hpos r).repr
        (traceColumnRepresentation τ hτ (e r) a
          ((tracialColumnBasis τ hτ e horth hmass hpos r).repr.symm x)) := rfl

theorem indexedColumnRepresentation_atom [DecidableEq V] (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    (hmass : HasSum (fun l => (τ (e l).1).re) (τ 1).re)
    (hpos : ∀ l, 0 < (τ (e l).1).re) (r l : V)
    (x : ℓ²(Option (Σ l, CenteredColumnIndex τ hτ e l r), ℂ))
    (j : Option (Σ l, CenteredColumnIndex τ hτ e l r)) :
    indexedColumnRepresentation τ hτ e horth hmass hpos r (e l).1 x j =
      if l = columnVertex r j then x j else 0 := by
  classical
  let b := tracialColumnBasis τ hτ e horth hmass hpos r
  let π := traceColumnRepresentation τ hτ (e r)
  change b.repr (π (e l).1 (b.repr.symm x)) j = _
  have hs : (π (e l).1).adjoint = π (e l).1 := ((e l).property.map π).isSelfAdjoint.star_eq
  have eigen : π (e l).1 (b j) = if l = columnVertex r j then b j else 0 :=
    projectionRow_eigen π e horth l _ _
      (tracialColumnBasis_row τ hτ e horth hmass hpos r j)
  calc
    b.repr (π (e l).1 (b.repr.symm x)) j =
        inner ℂ (b j) (π (e l).1 (b.repr.symm x)) := b.repr_apply_apply _ j
    _ = inner ℂ ((π (e l).1).adjoint (b j)) (b.repr.symm x) :=
      (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
    _ = inner ℂ (if l = columnVertex r j then b j else 0) (b.repr.symm x) :=
      congrArg (fun vector : TraceColumn τ hτ (e r) => inner ℂ vector (b.repr.symm x))
        ((congrArg (fun operator : TraceColumn τ hτ (e r) →L[ℂ] TraceColumn τ hτ (e r) =>
          operator (b j)) hs).trans eigen)
    _ = if l = columnVertex r j then x j else 0 := by
      split_ifs
      · exact (b.repr_apply_apply (b.repr.symm x) j).symm.trans
          (congrArg (fun vector => vector j) (b.repr.apply_symm_apply x))
      · exact inner_zero_left _

open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem columnUnit_inner_action (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) (a : A) :
    inner ℂ (columnUnit τ hτ q) (traceColumnRepresentation τ hτ q a (columnUnit τ hτ q)) =
      (((Real.sqrt (τ q.1).re)⁻¹ : ℂ) ^ 2) * τ (q.1 * a * q.1) := by
  rw [columnUnit, map_smul]
  rw [inner_smul_left (𝕜 := ℂ) (columnVacuum τ hτ q) _]
  rw [inner_smul_right (𝕜 := ℂ) (columnVacuum τ hτ q) _]
  have hv : inner ℂ (columnVacuum τ hτ q)
      (traceColumnRepresentation τ hτ q a (columnVacuum τ hτ q)) = τ (q.1 * a * q.1) := by
    change inner ℂ (columnVacuum τ hτ q : τ.GNS)
      (traceColumnRepresentation τ hτ q a (columnVacuum τ hτ q) : τ.GNS) = _
    rw [columnVacuum_action]
    change inner ℂ (τ.toPreGNS q.1 : τ.GNS) (τ.toPreGNS (a * q.1) : τ.GNS) = _
    simp only [Completion.inner_coe, PositiveLinearMap.preGNS_inner_def,
      PositiveLinearMap.ofPreGNS_toPreGNS, q.property.isSelfAdjoint.star_eq, mul_assoc]
  rw [hv]
  simp only [map_inv₀, Complex.conj_ofReal]
  ring

theorem columnUnit_inner_action_zero (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) (a : A) (ha : τ (q.1 * a * q.1) = 0) :
    inner ℂ (columnUnit τ hτ q) (traceColumnRepresentation τ hτ q a (columnUnit τ hτ q)) = 0 := by
  rw [columnUnit_inner_action, ha, mul_zero]

theorem columnUnit_action_norm_sq (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) (ht : 0 < (τ q.1).re) (a : A) :
    ‖traceColumnRepresentation τ hτ q a (columnUnit τ hτ q)‖ ^ 2 =
      (τ (q.1 * (star a * a) * q.1)).re / (τ q.1).re := by
  let π := traceColumnRepresentation τ hτ q
  let ξ := columnUnit τ hτ q
  have h : inner ℂ (π a ξ) (π a ξ) = inner ℂ ξ (π (star a * a) ξ) := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    have hs : (π a).adjoint = π (star a) := (map_star π a).symm
    rw [hs]
    rw [map_mul]
    rfl
  have hr := congrArg Complex.re h
  have hn : (inner ℂ (π a ξ) (π a ξ)).re = ‖π a ξ‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (π a ξ)).symm
  rw [hn] at hr
  rw [columnUnit_inner_action] at hr
  simp only [← Complex.ofReal_inv, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hr
  have hs : (Real.sqrt (τ q.1).re) ^ 2 = (τ q.1).re := Real.sq_sqrt ht.le
  simpa only [inv_pow, hs, div_eq_mul_inv, mul_comm] using hr

section
open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
  (e : V → {a : A // IsStarProjection a})
  (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
  (hmass : HasSum (fun l => (τ (e l).1).re) (τ 1).re)
  (hpos : ∀ l, 0 < (τ (e l).1).re)

theorem indexedColumnRepresentation_vacuum_vector (r : V)
    [DecidableEq (Option (Σ l, CenteredColumnIndex τ hτ e l r))] (a : A) :
    indexedColumnRepresentation τ hτ e horth hmass hpos r a (lp.single 2 none 1) =
      (tracialColumnBasis τ hτ e horth hmass hpos r).repr
        (traceColumnRepresentation τ hτ (e r) a (columnUnit τ hτ (e r))) := by
  let basis := tracialColumnBasis τ hτ e horth hmass hpos r
  exact (indexedColumnRepresentation_apply τ hτ e horth hmass hpos r a _).trans
    (congrArg (fun vector => basis.repr (traceColumnRepresentation τ hτ (e r) a vector))
      ((basis.repr_symm_single none).trans
        (tracialColumnBasis_none τ hτ e horth hmass hpos r)))

theorem indexedColumnRepresentation_vacuum (r : V)
    [DecidableEq (Option (Σ l, CenteredColumnIndex τ hτ e l r))] (a : A) :
    indexedColumnRepresentation τ hτ e horth hmass hpos r a (lp.single 2 none 1) none =
      (((Real.sqrt (τ (e r).1).re)⁻¹ : ℂ) ^ 2) * τ ((e r).1 * a * (e r).1) := by
  let b := tracialColumnBasis τ hτ e horth hmass hpos r
  calc
    _ = b.repr (traceColumnRepresentation τ hτ (e r) a (columnUnit τ hτ (e r))) none :=
      congrArg (fun vector => vector none)
        (indexedColumnRepresentation_vacuum_vector τ hτ e horth hmass hpos r a)
    _ = inner ℂ (b none)
        (traceColumnRepresentation τ hτ (e r) a (columnUnit τ hτ (e r))) :=
      b.repr_apply_apply _ none
    _ = inner ℂ (columnUnit τ hτ (e r))
        (traceColumnRepresentation τ hτ (e r) a (columnUnit τ hτ (e r))) :=
      congrArg (fun vector => inner ℂ vector
        (traceColumnRepresentation τ hτ (e r) a (columnUnit τ hτ (e r))))
        (tracialColumnBasis_none τ hτ e horth hmass hpos r)
    _ = _ := columnUnit_inner_action τ hτ (e r) a

theorem indexedColumnRepresentation_vacuum_norm (r : V)
    [DecidableEq (Option (Σ l, CenteredColumnIndex τ hτ e l r))] (a : A) :
    ‖indexedColumnRepresentation τ hτ e horth hmass hpos r a (lp.single 2 none 1)‖ ^ 2 =
      (τ ((e r).1 * (star a * a) * (e r).1)).re / (τ (e r).1).re := by
  let b := tracialColumnBasis τ hτ e horth hmass hpos r
  change ‖b.repr (traceColumnRepresentation τ hτ (e r) a
    (b.repr.symm (lp.single 2 none 1)))‖ ^ 2 = _
  rw [b.repr.norm_map, b.repr_symm_single]
  change ‖traceColumnRepresentation τ hτ (e r) a
    (tracialColumnBasis τ hτ e horth hmass hpos r none)‖ ^ 2 = _
  rw [tracialColumnBasis_none, columnUnit_action_norm_sq τ hτ (e r) (hpos r)]

end

open Filter Topology
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem traceRightAtoms_jointKernel (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    (hmass : HasSum (fun l => (τ (e l).1).re) (τ 1).re)
    (x : τ.GNS) (hx : ∀ l, gnsRight τ hτ (e l).1 x = 0) : x = 0 := by
  classical
  let p : Finset V → A := fun s => 1 - ∑ l ∈ s, (e l).1
  have hp : ∀ s, IsStarProjection (p s) := fun s => (finiteAtomSum_projection e horth s).one_sub
  have hlim : Tendsto (fun s => (τ (p s)).re) atTop (𝓝 0) := by
    simpa only [p, map_sub, map_sum, Complex.sub_re, Complex.re_sum, sub_self] using
      (tendsto_const_nhds (x := (τ 1).re) (f := (atTop : Filter (Finset V)))).sub hmass
  have hstrong := trace_projection_right_strong_zero τ hτ atTop p hp hlim x
  have he (s : Finset V) : gnsRight τ hτ (p s) x = x := by
    change gnsRightStarAlgHom τ hτ (MulOpposite.op (p s)) x = x
    simp only [p, MulOpposite.op_sub, MulOpposite.op_one, Finset.op_sum,
      map_sub, map_one, map_sum, sub_apply, one_apply_eq_self, sum_apply]
    change x - ∑ l ∈ s, gnsRight τ hτ (e l).1 x = x
    simp only [hx, Finset.sum_const_zero, sub_zero]
  simp only [he] at hstrong
  exact tendsto_nhds_unique tendsto_const_nhds hstrong

open Filter Topology
open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem trace_hasSum_atom_corners (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    (hmass : HasSum (fun l => (τ (e l).1).re) (τ 1).re) (a : A) :
    HasSum (fun r => τ ((e r).1 * a * (e r).1)) (τ a) := by
  classical
  let p : Finset V → A := fun s => 1 - ∑ r ∈ s, (e r).1
  have hp : ∀ s, IsStarProjection (p s) := fun s => (finiteAtomSum_projection e horth s).one_sub
  have hlim : Tendsto (fun s => (τ (p s)).re) atTop (𝓝 0) := by
    simpa only [p, map_sub, map_sum, Complex.sub_re, Complex.re_sum, sub_self] using
      (tendsto_const_nhds (x := (τ 1).re) (f := (atTop : Filter (Finset V)))).sub hmass
  have hstrong := trace_projection_right_strong_zero τ hτ atTop p hp hlim
    (τ.toPreGNS a : τ.GNS)
  have hz := ((innerSL ℂ (traceVacuum τ)).continuous.tendsto 0).comp hstrong
  have hc (r : V) : τ (a * (e r).1) = τ ((e r).1 * a * (e r).1) := by
    rw [hτ ((e r).1 * a) (e r).1, ← mul_assoc, (e r).property.isIdempotentElem.eq,
      hτ (e r).1 a]
  have he (s : Finset V) : inner ℂ (traceVacuum τ)
      (gnsRight τ hτ (p s) (τ.toPreGNS a : τ.GNS)) =
        τ a - ∑ r ∈ s, τ ((e r).1 * a * (e r).1) := by
    rw [gnsRight_coe]
    simp only [traceVacuum, Completion.inner_coe, PositiveLinearMap.preGNS_inner_def,
      PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul, p, mul_sub,
      mul_one, Finset.mul_sum, map_sub, map_sum, hc]
  simp only [map_zero] at hz
  change Tendsto (fun s => inner ℂ (traceVacuum τ)
    (gnsRight τ hτ (p s) (τ.toPreGNS a : τ.GNS))) atTop (𝓝 0) at hz
  simp only [he] at hz
  have ht := (tendsto_const_nhds (x := τ a) (f := (atTop : Filter (Finset V)))).sub hz
  simpa only [HasSum, SummationFilter.unconditional_filter, sub_sub_cancel, sub_zero] using ht

theorem traceColumn_vacuum_cyclic (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) :
    DenseRange (fun a : A => traceColumnRepresentation τ hτ q a (columnVacuum τ hτ q)) := by
  let P : τ.GNS →L[ℂ] TraceColumn τ hτ q := (gnsRight τ hτ q.1).rangeRestrict
  have hP : Function.Surjective P := by
    rintro ⟨x, y, hy⟩
    exact ⟨y, Subtype.ext hy⟩
  have hd := hP.denseRange.comp
    (Completion.denseRange_coe.comp τ.toPreGNS.surjective.denseRange (Completion.continuous_coe _))
    P.continuous
  have he (a : A) : P (τ.toPreGNS a : τ.GNS) =
      traceColumnRepresentation τ hτ q a (columnVacuum τ hτ q) := by
    apply Subtype.ext
    exact (gnsRight_coe τ hτ q.1 a).trans (columnVacuum_action τ hτ q a).symm
  simpa only [Function.comp_def, he] using hd

theorem traceColumn_unit_cyclic (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) (ht : 0 < (τ q.1).re) :
    DenseRange (fun a : A => traceColumnRepresentation τ hτ q a (columnUnit τ hτ q)) := by
  have hn : (Real.sqrt (τ q.1).re : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ht).ne'
  have he : Set.range (fun a : A => traceColumnRepresentation τ hτ q a (columnUnit τ hτ q)) =
      Set.range (fun a : A => traceColumnRepresentation τ hτ q a (columnVacuum τ hτ q)) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨((Real.sqrt (τ q.1).re)⁻¹ : ℂ) • a, ?_⟩
      simp only [columnUnit, map_smul, smul_apply]
    · rintro ⟨a, rfl⟩
      refine ⟨(Real.sqrt (τ q.1).re : ℂ) • a, ?_⟩
      simp only [columnUnit, map_smul, smul_apply, smul_smul,
        inv_mul_cancel₀ hn, one_smul]
  change Dense (Set.range _)
  rw [he]
  exact traceColumn_vacuum_cyclic τ hτ q

attribute [local instance] Classical.propDecidable

section
universe u v w

variable {I : Type u} {V : Type v} (L : I → V → V → Type w)

inductive ReducedPath : Option I → V → Type (max u v w)
  | nil (r : V) : ReducedPath none r
  | cons (i : I) (l r : V) (a : L i l r) (j : Option I)
      (tail : ReducedPath j r) (hn : some i ≠ j) : ReducedPath (some i) l

abbrev FockIndex := Σ j : Option I, Σ l : V, ReducedPath L j l

abbrev FockTail (i : I) := {x : FockIndex L // x.1 ≠ some i}

abbrev ColumnIndex (i : I) (r : V) := Option (Σ l : V, L i l r)

abbrev FockBlockIndex (i : I) := Σ t : FockTail L i, ColumnIndex L i t.1.2.1

def fockJoin (i : I) : FockBlockIndex L i → FockIndex L
  | ⟨t, none⟩ => t.1
  | ⟨t, some ⟨l, a⟩⟩ =>
    ⟨some i, l, ReducedPath.cons i l t.1.2.1 a t.1.1 t.1.2.2 (Ne.symm t.2)⟩

def fockSplit [DecidableEq I] (i : I) : FockIndex L → FockBlockIndex L i
  | ⟨none, l, ReducedPath.nil _⟩ => ⟨⟨⟨none, l, .nil l⟩, by simp⟩, none⟩
  | ⟨some k, l, ReducedPath.cons _ _ r a j tail hn⟩ =>
    if hki : k = i then
      hki ▸ ⟨⟨⟨j, r, tail⟩, Ne.symm hn⟩, some ⟨l, a⟩⟩
    else
      ⟨⟨⟨some k, l, .cons k l r a j tail hn⟩, by simpa using hki⟩, none⟩

@[simp] theorem fockJoin_split [DecidableEq I] (i : I) (x : FockIndex L) :
    fockJoin L i (fockSplit L i x) = x := by
  rcases x with ⟨j, l, x⟩
  cases x with
  | nil l => rfl
  | cons k l r a j tail hn =>
    by_cases hki : k = i
    · subst k; simp [fockSplit, fockJoin]
    · simp [fockSplit, hki, fockJoin]

@[simp] theorem fockSplit_join [DecidableEq I] (i : I) (x : FockBlockIndex L i) :
    fockSplit L i (fockJoin L i x) = x := by
  rcases x with ⟨⟨⟨j, r, t⟩, ht⟩, c⟩
  cases c with
  | none =>
    cases t with
    | nil r => rfl
    | cons k l r a j tail hn =>
      have hki : k ≠ i := by simpa using ht
      simp [fockJoin, fockSplit, hki]
  | some c =>
    rcases c with ⟨l, a⟩
    simp [fockJoin, fockSplit]

def fockBlockEquiv [DecidableEq I] (i : I) : FockBlockIndex L i ≃ FockIndex L where
  toFun := fockJoin L i
  invFun := fockSplit L i
  left_inv := fockSplit_join L i
  right_inv := fockJoin_split L i

end

open scoped InnerProductSpace ENNReal lp

variable {ι κ : Type*} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

def hilbertBasisReindex (b : HilbertBasis ι ℂ H) (e : ι ≃ κ) : HilbertBasis κ ℂ H :=
  HilbertBasis.mk (b.orthonormal.comp e.symm e.symm.injective) (by
    have hr : Set.range (fun j => b (e.symm j)) = Set.range b := by
      rw [← Function.comp_def, Set.range_comp, e.symm.surjective.range_eq, Set.image_univ]
    simp only [Function.comp_def]
    rw [hr]
    exact b.dense_span.symm.le)

@[simp] theorem hilbertBasisReindex_apply (b : HilbertBasis ι ℂ H) (e : ι ≃ κ) (j : κ) :
    hilbertBasisReindex b e j = b (e.symm j) := by
  simp [hilbertBasisReindex]

def l2Basis (ι : Type*) : HilbertBasis ι ℂ ℓ²(ι, ℂ) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

@[simp] theorem l2Basis_apply [DecidableEq ι] (i : ι) : l2Basis ι i = lp.single 2 i (1 : ℂ) := by
  rw [← HilbertBasis.repr_symm_single]; rfl

def l2Reindex (e : ι ≃ κ) : ℓ²(ι, ℂ) ≃ₗᵢ[ℂ] ℓ²(κ, ℂ) :=
  (hilbertBasisReindex (l2Basis ι) e).repr

@[simp] theorem l2Reindex_apply (e : ι ≃ κ) (x : ℓ²(ι, ℂ)) (j : κ) :
    l2Reindex e x j = x (e.symm j) := by
  classical
  rw [l2Reindex, HilbertBasis.repr_apply_apply, hilbertBasisReindex_apply, l2Basis_apply]
  simp [lp.inner_single_left]

@[simp] theorem l2Reindex_single [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (i : ι) (c : ℂ) :
    l2Reindex e (lp.single 2 i c) = lp.single 2 (e i) c := by
  classical
  ext j
  simp only [l2Reindex_apply, lp.single_apply]
  by_cases h : j = e i
  · subst j; simp
  · have h' : e.symm j ≠ i := fun he => h (by simpa using congrArg e he)
    simp [h, h']

variable {ι : Type*} {J : ι → Type*} {H : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, CompleteSpace (H i)]

omit [∀ i, CompleteSpace (H i)] in

theorem sumBasis_orthonormal [DecidableEq ι] (b : ∀ i, HilbertBasis (J i) ℂ (H i)) :
    Orthonormal ℂ (fun j : Σ i, J i => lp.single 2 j.1 (b j.1 j.2)) := by
  classical
  refine ⟨?_, ?_⟩
  · rintro ⟨i,j⟩
    simpa only [lp.norm_single (by norm_num : 0 < (2 : ℝ≥0∞))] using (b i).orthonormal.1 j
  · rintro ⟨i,j⟩ ⟨k,l⟩ hne
    rw [lp.inner_single_left]
    by_cases hik : i = k
    · subst k
      have hjl : j ≠ l := fun h => hne (by subst l; rfl)
      simpa only [lp.single_apply, Pi.single_eq_same] using (b i).orthonormal.2 hjl
    · simp [lp.single_apply, hik]

def sumHilbertBasis [DecidableEq ι] (b : ∀ i, HilbertBasis (J i) ℂ (H i)) :
    HilbertBasis (Σ i, J i) ℂ (lp H 2) :=
  HilbertBasis.mkOfOrthogonalEqBot (sumBasis_orthonormal b) (by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Submodule.mem_bot]
    ext i
    apply (b i).repr.injective
    ext j
    simp only [lp.coeFn_zero, Pi.zero_apply, map_zero]
    rw [HilbertBasis.repr_apply_apply]
    have hm := (Submodule.mem_orthogonal _ _).mp hx (lp.single 2 i (b i j))
      (Submodule.subset_span ⟨⟨i,j⟩, rfl⟩)
    simpa only [lp.inner_single_left] using hm)

@[simp] theorem sumHilbertBasis_apply [DecidableEq ι]
    (b : ∀ i, HilbertBasis (J i) ℂ (H i)) (j : Σ i, J i) :
    sumHilbertBasis b j = lp.single 2 j.1 (b j.1 j.2) := by
  simp [sumHilbertBasis]

def l2Sigma [DecidableEq ι] (J : ι → Type*) :
    lp (fun i => ℓ²(J i, ℂ)) 2 ≃ₗᵢ[ℂ] ℓ²((Σ i, J i), ℂ) :=
  (sumHilbertBasis fun i => l2Basis (J i)).repr

@[simp] theorem l2Sigma_apply [DecidableEq ι] (x : lp (fun i => ℓ²(J i, ℂ)) 2)
    (j : Σ i, J i) : l2Sigma J x j = x j.1 j.2 := by
  classical
  rw [l2Sigma, HilbertBasis.repr_apply_apply, sumHilbertBasis_apply,
    l2Basis_apply, lp.inner_single_left]
  simp [lp.inner_single_left]

open scoped InnerProductSpace ENNReal lp

variable {ι : Type*} {H K : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedAddCommGroup (K i)]
  [∀ i, InnerProductSpace ℂ (H i)] [∀ i, InnerProductSpace ℂ (K i)]

def hilbertSumMap (T : ∀ i, H i →L[ℂ] K i) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) : lp H 2 →L[ℂ] lp K 2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun i => T i (x i),
        ((lp.memℓp x).norm.const_mul C).mono fun i =>
          ((T i).le_opNorm (x i)).trans (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _))⟩
      map_add' := fun x y => by ext i; exact map_add (T i) _ _
      map_smul' := fun c x => by ext i; exact map_smul (T i) _ _ }
    C (fun x => by
      calc
        _ ≤ ‖C • lp.toNorm x‖ := lp.norm_mono (by norm_num) fun i => by
          change ‖T i (x i)‖ ≤ ‖C * ‖x i‖‖
          rw [Real.norm_of_nonneg (mul_nonneg hC (norm_nonneg _))]
          exact ((T i).le_opNorm (x i)).trans (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _))
        _ = C * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg hC, lp.norm_toNorm])

@[simp] theorem hilbertSumMap_apply (T : ∀ i, H i →L[ℂ] K i) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) (x : lp H 2) (i : ι) :
    hilbertSumMap T C hC hT x i = T i (x i) := rfl

theorem hilbertSumMap_norm_le (T : ∀ i, H i →L[ℂ] K i) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) : ‖hilbertSumMap T C hC hT‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

variable [∀ i, CompleteSpace (H i)] [∀ i, CompleteSpace (K i)]

theorem hilbertSumMap_adjoint (T : ∀ i, H i →L[ℂ] K i) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) :
    hilbertSumMap (fun i => (T i).adjoint) C hC (fun i => by simpa using hT i) =
      (hilbertSumMap T C hC hT).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [lp.inner_eq_tsum, hilbertSumMap_apply]
  apply tsum_congr
  intro i
  exact ContinuousLinearMap.adjoint_inner_left (T i) _ _

variable {A : Type*} [CStarAlgebra A]

def hilbertSumRepresentation (π : ∀ i, A →⋆ₐ[ℂ] (H i →L[ℂ] H i)) :
    A →⋆ₐ[ℂ] (lp H 2 →L[ℂ] lp H 2) where
  toFun a := hilbertSumMap (fun i => π i a) ‖a‖ (norm_nonneg _) (fun i => NonUnitalStarAlgHom.norm_apply_le (π i) a)
  map_zero' := by ext x i; simp
  map_one' := by ext x i; simp
  map_add' a b := by ext x i; simp
  map_mul' a b := by ext x i; simp
  commutes' c := by
    ext x i
    change (π i (algebraMap ℂ A c)) (x i) = c • x i
    exact congrArg (fun T : H i →L[ℂ] H i => T (x i)) ((π i).commutes c)
  map_star' a := by
    have h := hilbertSumMap_adjoint (fun i => π i a) ‖a‖ (norm_nonneg _)
      (fun i => NonUnitalStarAlgHom.norm_apply_le (π i) a)
    change _ = (hilbertSumMap (fun i => π i a) ‖a‖ (norm_nonneg _) _).adjoint
    rw [← h]
    ext x i
    exact congrArg (fun T : H i →L[ℂ] H i => T (x i)) (map_star (π i) a)

@[simp] theorem hilbertSumRepresentation_apply (π : ∀ i, A →⋆ₐ[ℂ] (H i →L[ℂ] H i))
    (a : A) (x : lp H 2) (i : ι) : hilbertSumRepresentation π a x i = π i a (x i) := rfl

open scoped InnerProductSpace ENNReal lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

abbrev AtomicFockSpace := ℓ²(FockIndex L, ℂ)
abbrev FactorBlockSpace (i : I) :=
  lp (fun t : FockTail L i => ℓ²(ColumnIndex L i t.1.2.1, ℂ)) 2

def fockBlockUnitary (i : I) : FactorBlockSpace L i ≃ₗᵢ[ℂ] AtomicFockSpace L := by
  classical
  exact (l2Sigma fun t : FockTail L i => ColumnIndex L i t.1.2.1).trans
    (l2Reindex (fockBlockEquiv L i))

@[simp] theorem fockBlockUnitary_apply (i : I) (x : FactorBlockSpace L i)
    (j : FockIndex L) :
    fockBlockUnitary L i x j = x (fockSplit L i j).1 (fockSplit L i j).2 := by
  classical
  simp only [fockBlockUnitary, LinearIsometryEquiv.trans_apply, l2Reindex_apply, l2Sigma_apply]
  rfl

@[simp] theorem fockBlockUnitary_apply_join (i : I) (x : FactorBlockSpace L i)
    (t : FockTail L i) (c : ColumnIndex L i t.1.2.1) :
    fockBlockUnitary L i x (fockJoin L i ⟨t,c⟩) = x t c := by
  rw [fockBlockUnitary_apply, fockSplit_join]

@[simp] theorem fockBlockUnitary_symm_apply (i : I) (x : AtomicFockSpace L)
    (t : FockTail L i) (c : ColumnIndex L i t.1.2.1) :
    (fockBlockUnitary L i).symm x t c = x (fockJoin L i ⟨t,c⟩) := by
  have h := fockBlockUnitary_apply_join L i ((fockBlockUnitary L i).symm x) t c
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]

def atomicFockRepresentation
    (π : ∀ i r, A i →⋆ₐ[ℂ] (ℓ²(ColumnIndex L i r, ℂ) →L[ℂ] ℓ²(ColumnIndex L i r, ℂ)))
    (i : I) : A i →⋆ₐ[ℂ] (AtomicFockSpace L →L[ℂ] AtomicFockSpace L) :=
  ((fockBlockUnitary L i).conjStarAlgEquiv).toStarAlgHom.comp
    (hilbertSumRepresentation fun t : FockTail L i => π i t.1.2.1)

theorem atomicFockRepresentation_block
    (π : ∀ i r, A i →⋆ₐ[ℂ] (ℓ²(ColumnIndex L i r, ℂ) →L[ℂ] ℓ²(ColumnIndex L i r, ℂ)))
    (i : I) (a : A i) (x : AtomicFockSpace L) (t : FockTail L i)
    (c : ColumnIndex L i t.1.2.1) :
    atomicFockRepresentation L π i a x (fockJoin L i ⟨t,c⟩) =
      π i t.1.2.1 a ((fockBlockUnitary L i).symm x t) c := by
  change fockBlockUnitary L i
    ((hilbertSumRepresentation fun t : FockTail L i => π i t.1.2.1) a
    ((fockBlockUnitary L i).symm x)) (fockJoin L i ⟨t,c⟩) = _
  rw [fockBlockUnitary_apply_join, hilbertSumRepresentation_apply]

open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

def fockColumnVertex (i : I) (r : V) : ColumnIndex L i r → V
  | none => r
  | some ⟨l,_⟩ => l

omit [DecidableEq I] in
@[simp] theorem fockJoin_left (i : I) (t : FockTail L i) (c : ColumnIndex L i t.1.2.1) :
    (fockJoin L i ⟨t,c⟩).2.1 = fockColumnVertex L i t.1.2.1 c := by
  cases c with
  | none => rfl
  | some c => cases c; rfl

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]

theorem atomicFockRepresentation_diagonal [DecidableEq V]
    (π : ∀ i r, A i →⋆ₐ[ℂ] (ℓ²(ColumnIndex L i r, ℂ) →L[ℂ] ℓ²(ColumnIndex L i r, ℂ)))
    (e : ∀ i, V → A i)
    (hdiag : ∀ i r l, ∀ x : ℓ²(ColumnIndex L i r, ℂ), ∀ c,
      π i r (e i l) x c = if l = fockColumnVertex L i r c then x c else 0)
    (i : I) (l : V) (x : AtomicFockSpace L) (j : FockIndex L) :
    atomicFockRepresentation L π i (e i l) x j = if l = j.2.1 then x j else 0 := by
  obtain ⟨⟨t,c⟩, rfl⟩ := (fockBlockEquiv L i).surjective j
  change atomicFockRepresentation L π i (e i l) x (fockJoin L i ⟨t,c⟩) = _
  rw [atomicFockRepresentation_block, hdiag, fockBlockUnitary_symm_apply]
  change (if l = fockColumnVertex L i t.1.2.1 c then
    x (fockJoin L i ⟨t,c⟩) else 0) =
    if l = (fockJoin L i ⟨t,c⟩).2.1 then x (fockJoin L i ⟨t,c⟩) else 0
  rw [fockJoin_left]

theorem atomicFockRepresentation_agree_atoms [DecidableEq V]
    (π : ∀ i r, A i →⋆ₐ[ℂ] (ℓ²(ColumnIndex L i r, ℂ) →L[ℂ] ℓ²(ColumnIndex L i r, ℂ)))
    (e : ∀ i, V → A i)
    (hdiag : ∀ i r l, ∀ x : ℓ²(ColumnIndex L i r, ℂ), ∀ c,
      π i r (e i l) x c = if l = fockColumnVertex L i r c then x c else 0)
    (i k : I) (l : V) :
    atomicFockRepresentation L π i (e i l) = atomicFockRepresentation L π k (e k l) := by
  ext x j
  rw [atomicFockRepresentation_diagonal L π e hdiag,
    atomicFockRepresentation_diagonal L π e hdiag]

theorem starAlgHom_ext_closed_adjoin {D B : Type*} [CStarAlgebra D] [CStarAlgebra B]
    (f g : D →⋆ₐ[ℂ] B) (s : Set D)
    (hgen : (StarAlgebra.adjoin ℂ s).topologicalClosure = ⊤)
    (heq : s.EqOn f g) : f = g := by
  apply DFunLike.ext
  intro x
  have hm : x ∈ (StarAlgebra.adjoin ℂ s).topologicalClosure := by rw [hgen]; trivial
  let := NonUnitalStarAlgHom.instContinuousLinearMapClassComplex (F := D →⋆ₐ[ℂ] B)
  apply (isClosed_eq (map_continuous f) (map_continuous g)).closure_subset_iff.mpr _ hm
  exact StarAlgHom.adjoin_le_equalizer f g heq

section
open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

def FockAway (i : I) (x : AtomicFockSpace L) : Prop :=
  ∀ j, j.1 = some i → x j = 0

def FockStarts (i : I) (x : AtomicFockSpace L) : Prop :=
  ∀ j, j.1 ≠ some i → x j = 0

theorem fockBlockUnitary_symm_away (i : I) (x : AtomicFockSpace L)
    (hx : FockAway L i x) (t : FockTail L i) :
    (fockBlockUnitary L i).symm x t = lp.single 2 none (x t.1) := by
  classical
  ext c
  rw [fockBlockUnitary_symm_apply]
  cases c with
  | none => simp [fockJoin]
  | some c =>
    simp only [lp.single_apply, Pi.single_eq_of_ne (Option.some_ne_none c)]
    exact hx _ rfl

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]
variable (π : ∀ i r, A i →⋆ₐ[ℂ]
  (ℓ²(ColumnIndex L i r, ℂ) →L[ℂ] ℓ²(ColumnIndex L i r, ℂ)))

theorem atomicFock_creation (i : I) (a : A i) (x : AtomicFockSpace L)
    (hx : FockAway L i x) (t : FockTail L i) (c : ColumnIndex L i t.1.2.1) :
    atomicFockRepresentation L π i a x (fockJoin L i ⟨t,c⟩) =
      x t.1 * π i t.1.2.1 a (lp.single 2 none 1) c := by
  classical
  rw [atomicFockRepresentation_block, fockBlockUnitary_symm_away L i x hx]
  have h : lp.single 2 none (x t.1) = x t.1 •
      (lp.single 2 none 1 : ℓ²(ColumnIndex L i t.1.2.1, ℂ)) := by
    rw [← lp.single_smul]; simp
  rw [h, map_smul]
  rfl

theorem atomicFock_creation_starts (i : I) (a : A i)
    (ha : ∀ r, π i r a (lp.single 2 none 1) none = 0)
    (x : AtomicFockSpace L) (hx : FockAway L i x) :
    FockStarts L i (atomicFockRepresentation L π i a x) := by
  intro j hj
  have h := atomicFock_creation L π i a x hx ⟨j,hj⟩ none
  simpa [fockJoin, ha] using h

theorem atomicFock_creation_norm (i : I) (a : A i) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ r, ‖π i r a (lp.single 2 none 1)‖ ≤ C)
    (x : AtomicFockSpace L) (hx : FockAway L i x) :
    ‖atomicFockRepresentation L π i a x‖ ≤ C * ‖x‖ := by
  classical
  let U := fockBlockUnitary L i
  rw [← U.symm.norm_map (atomicFockRepresentation L π i a x)]
  calc
    ‖U.symm (atomicFockRepresentation L π i a x)‖ ≤ ‖C • U.symm x‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro t
      have hb : U.symm (atomicFockRepresentation L π i a x) t =
          x t.1 • π i t.1.2.1 a (lp.single 2 none 1) := by
        ext c
        change (fockBlockUnitary L i).symm _ t c = _
        rw [fockBlockUnitary_symm_apply, atomicFock_creation L π i a x hx]
        rfl
      rw [hb, norm_smul]
      change _ ≤ ‖C • ((fockBlockUnitary L i).symm x t)‖
      rw [fockBlockUnitary_symm_away L i x hx, norm_smul,
        lp.norm_single (by norm_num : 0 < (2 : ℝ≥0∞)), Real.norm_eq_abs, abs_of_nonneg hC]
      simpa only [mul_comm C] using mul_le_mul_of_nonneg_left (ha t.1.2.1) (norm_nonneg _)
    _ = C * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC, U.symm.norm_map]

end

section
open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

def fockStartProjection (i : I) : AtomicFockSpace L →L[ℂ] AtomicFockSpace L :=
  hilbertSumMap (fun j : FockIndex L =>
    if j.1 = some i then (1 : ℂ →L[ℂ] ℂ) else 0) 1 zero_le_one
    (fun j => by split_ifs <;> simp)

@[simp] theorem fockStartProjection_apply (i : I) (x : AtomicFockSpace L) (j : FockIndex L) :
    fockStartProjection L i x j = if j.1 = some i then x j else 0 := by
  simp only [fockStartProjection, hilbertSumMap_apply]
  split_ifs <;> rfl

theorem fockStartProjection_norm_le (i : I) : ‖fockStartProjection L i‖ ≤ 1 :=
  hilbertSumMap_norm_le _ _ _ _

@[simp] theorem fockStartProjection_star (i : I) :
    star (fockStartProjection L i) = fockStartProjection L i := by
  change (fockStartProjection L i).adjoint = _
  rw [fockStartProjection, ← hilbertSumMap_adjoint]
  ext x j
  simp only [hilbertSumMap_apply]
  split_ifs <;> simp [ContinuousLinearMap.adjoint_one]

theorem fockStartProjection_complement_away (i : I) (x : AtomicFockSpace L) :
    FockAway L i ((1 - fockStartProjection L i) x) := by
  intro j hj
  simp [hj]

theorem fockStartProjection_starts (i : I) (x : AtomicFockSpace L) :
    FockStarts L i (fockStartProjection L i x) := by
  intro j hj
  simp [hj]

theorem fockStartProjection_fix (i : I) (x : AtomicFockSpace L)
    (hx : FockStarts L i x) : fockStartProjection L i x = x := by
  ext j
  rw [fockStartProjection_apply]
  split_ifs with hj
  · rfl
  · exact (hx j hj).symm

omit [DecidableEq I] in

theorem fockStarts_away {i k : I} (hik : i ≠ k) (x : AtomicFockSpace L)
    (hx : FockStarts L i x) : FockAway L k x := by
  intro j hj
  apply hx j
  rw [hj]
  exact fun h => hik (Option.some.inj h).symm

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]

inductive AlternatingFactorWord (A : I → Type*) : I → I → Type _
  | single (i : I) (a : A i) : AlternatingFactorWord A i i
  | cons (i j k : I) (a : A i) (w : AlternatingFactorWord A j k)
      (hij : i ≠ j) : AlternatingFactorWord A i k

variable (π : ∀ i r, A i →⋆ₐ[ℂ]
  (ℓ²(ColumnIndex L i r, ℂ) →L[ℂ] ℓ²(ColumnIndex L i r, ℂ)))

def AlternatingFactorWord.eval {i k : I} :
    AlternatingFactorWord A i k → (AtomicFockSpace L →L[ℂ] AtomicFockSpace L)
  | .single i a => atomicFockRepresentation L π i a
  | .cons i _ _ a w _ => atomicFockRepresentation L π i a * AlternatingFactorWord.eval w

def AlternatingFactorWord.Centered {i k : I} : AlternatingFactorWord A i k → Prop
  | .single i a => ∀ r, π i r a (lp.single 2 none 1) none = 0
  | .cons i _ _ a w _ => (∀ r, π i r a (lp.single 2 none 1) none = 0) ∧ AlternatingFactorWord.Centered w

theorem AlternatingFactorWord.creation {i k : I} (w : AlternatingFactorWord A i k)
    (hw : w.Centered L π) (x : AtomicFockSpace L) (hx : FockAway L k x) :
    FockStarts L i (w.eval L π x) := by
  induction w with
  | single i a => exact atomicFock_creation_starts L π i a hw x hx
  | cons i j k a w hij ih =>
    exact atomicFock_creation_starts L π i a hw.1 _
      (fockStarts_away L (Ne.symm hij) _ (ih hw.2 hx))

theorem AlternatingFactorWord.zero_complement {i : I} (w : AlternatingFactorWord A i i)
    (hw : w.Centered L π) :
    (1 - fockStartProjection L i) * w.eval L π * (1 - fockStartProjection L i) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  change (1 - fockStartProjection L i) (w.eval L π ((1 - fockStartProjection L i) x)) = 0
  rw [sub_apply, one_apply_eq_self,
    fockStartProjection_fix L i _ (w.creation L π hw _ (fockStartProjection_complement_away L i x)),
    sub_self]

end

open scoped InnerProductSpace lp
variable {V J : Type*}

def l2Embed (e : V ↪ J) : ℓ²(V, ℂ) →ₗᵢ[ℂ] ℓ²(J, ℂ) :=
  ((l2Basis J).orthonormal.comp e e.injective).orthogonalFamily.linearIsometry

@[simp] theorem l2Embed_single [DecidableEq V] [DecidableEq J] (e : V ↪ J) (r : V) (c : ℂ) :
    l2Embed e (lp.single 2 r c) = lp.single 2 (e r) c := by
  rw [l2Embed, OrthogonalFamily.linearIsometry_apply_single]
  simp [LinearIsometry.toSpanSingleton_apply, l2Basis_apply, ← lp.single_smul]

@[simp] theorem l2Embed_apply (e : V ↪ J) (z : ℓ²(V, ℂ)) (r : V) :
    l2Embed e z (e r) = z r := by
  classical
  have h := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) z).mapL
    ((lp.evalCLM ℂ (fun _ : J => ℂ) 2 (e r)).comp (l2Embed e).toContinuousLinearMap)
  simpa [lp.evalCLM, l2Embed_single, lp.single_apply, Pi.single_apply, e.injective.eq_iff] using h.tsum_eq.symm

theorem l2Embed_apply_of_not_mem (e : V ↪ J) (z : ℓ²(V, ℂ)) (j : J)
    (hj : j ∉ Set.range e) : l2Embed e z j = 0 := by
  classical
  have h := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) z).mapL
    ((lp.evalCLM ℂ (fun _ : J => ℂ) 2 j).comp (l2Embed e).toContinuousLinearMap)
  have hne : ∀ r, j ≠ e r := fun r he => hj ⟨r, he.symm⟩
  simpa [lp.evalCLM, l2Embed_single, lp.single_apply, Pi.single_eq_of_ne, hne] using h.tsum_eq.symm

section
open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*)

def fockVacuumIndex : V ↪ FockIndex L where
  toFun r := ⟨none, r, .nil r⟩
  inj' _r _s hrs := congrArg (fun j : FockIndex L => j.2.1) hrs

def fockVacuum (z : ℓ²(V, ℂ)) : AtomicFockSpace L := l2Embed (fockVacuumIndex L) z

@[simp] theorem fockVacuum_apply_nil (z : ℓ²(V, ℂ)) (r : V) :
    fockVacuum L z ⟨none,r,.nil r⟩ = z r := l2Embed_apply _ _ _

theorem fockVacuum_away (z : ℓ²(V, ℂ)) (i : I) : FockAway L i (fockVacuum L z) := by
  intro j hj
  apply l2Embed_apply_of_not_mem
  rintro ⟨r,hr⟩
  have he := congrArg (fun j : FockIndex L => j.1) hr
  change none = j.1 at he
  rw [hj] at he
  cases he

@[simp] theorem fockVacuum_norm (z : ℓ²(V, ℂ)) : ‖fockVacuum L z‖ = ‖z‖ :=
  (l2Embed _).norm_map z

theorem fockVacuum_inner_starts (z : ℓ²(V, ℂ)) (i : I) (x : AtomicFockSpace L)
    (hx : FockStarts L i x) : inner ℂ (fockVacuum L z) x = 0 := by
  rw [lp.inner_eq_tsum]
  suffices h : ∀ j, inner ℂ (fockVacuum L z j) (x j) = 0 by simp only [h, tsum_zero]
  rintro ⟨j,r,p⟩
  cases p with
  | nil r => rw [hx _ (by simp), inner_zero_right]
  | cons k l r a j p hn =>
    rw [fockVacuum_away L z k _ rfl, inner_zero_left]

variable [DecidableEq I] {A : I → Type*} [∀ i, CStarAlgebra (A i)]
variable (π : ∀ i r, A i →⋆ₐ[ℂ]
  (ℓ²(ColumnIndex L i r, ℂ) →L[ℂ] ℓ²(ColumnIndex L i r, ℂ)))

theorem AlternatingFactorWord.vacuum_zero {i k : I} (w : AlternatingFactorWord A i k)
    (hw : w.Centered L π) (z : ℓ²(V, ℂ)) :
    inner ℂ (fockVacuum L z) (w.eval L π (fockVacuum L z)) = 0 :=
  fockVacuum_inner_starts L z i _ (w.creation L π hw _ (fockVacuum_away L z k))

end

section
open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]
  {A : I → Type*} [∀ i, CStarAlgebra (A i)]
variable (π : ∀ i r, A i →⋆ₐ[ℂ]
  (ℓ²(ColumnIndex L i r, ℂ) →L[ℂ] ℓ²(ColumnIndex L i r, ℂ)))

theorem atomicFock_zero_column (i : I) (a : A i)
    (ha : atomicFockRepresentation L π i a = 0) (r : V) :
    π i r a (lp.single 2 none 1) = 0 := by
  classical
  let x : AtomicFockSpace L := lp.single 2 ⟨none, r, .nil r⟩ 1
  have hx : FockAway L i x := by
    intro j hj
    have hn : j ≠ ⟨none, r, .nil r⟩ := by
      intro he
      have hf := congrArg (fun j : FockIndex L => j.1) he
      change j.1 = none at hf
      rw [hj] at hf
      cases hf
    simp only [x, lp.single_apply, Pi.single_eq_of_ne hn]
  let t : FockTail L i := ⟨⟨none, r, .nil r⟩, by simp⟩
  ext c
  have hb := atomicFock_creation L π i a x hx t c
  rw [ha] at hb
  simpa [x, t, fockVacuumIndex, zero_apply] using hb.symm

end

section
open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*)

theorem fockVacuum_inner (z : ℓ²(V, ℂ)) (x : AtomicFockSpace L) :
    inner ℂ (fockVacuum L z) x =
      ∑' r, inner ℂ (z r) (x (fockVacuumIndex L r)) := by
  rw [lp.inner_eq_tsum]
  have hs : Function.support (fun j => inner ℂ (fockVacuum L z j) (x j)) ⊆
      Set.range (fockVacuumIndex L) := by
    intro j hj
    by_contra hn
    exact hj (by
      change inner ℂ (l2Embed (fockVacuumIndex L) z j) (x j) = 0
      rw [l2Embed_apply_of_not_mem _ _ _ hn, inner_zero_left])
  rw [← (fockVacuumIndex L).injective.tsum_eq hs]
  congr 1
  funext r
  rw [show fockVacuum L z (fockVacuumIndex L r) = z r from l2Embed_apply _ _ _]

variable [DecidableEq I] {A : I → Type*} [∀ i, CStarAlgebra (A i)]
variable (π : ∀ i r, A i →⋆ₐ[ℂ]
  (ℓ²(ColumnIndex L i r, ℂ) →L[ℂ] ℓ²(ColumnIndex L i r, ℂ)))

theorem atomicFock_vacuum_coeff (i : I) (a : A i) (z : ℓ²(V, ℂ)) (r : V) :
    atomicFockRepresentation L π i a (fockVacuum L z) (fockVacuumIndex L r) =
      z r * π i r a (lp.single 2 none 1) none := by
  have h := atomicFock_creation L π i a (fockVacuum L z) (fockVacuum_away L z i)
    ⟨⟨none, r, .nil r⟩, by simp⟩ none
  simp only [fockJoin, fockVacuum_apply_nil] at h
  convert h using 1
  rfl

theorem atomicFock_vacuum_inner (i : I) (a : A i) (z : ℓ²(V, ℂ)) :
    inner ℂ (fockVacuum L z) (atomicFockRepresentation L π i a (fockVacuum L z)) =
      ∑' r, star (z r) * (z r * π i r a (lp.single 2 none 1) none) := by
  rw [fockVacuum_inner]
  congr 1
  funext r
  rw [atomicFock_vacuum_coeff, RCLike.inner_apply']
  rfl

end

section
open scoped lp InnerProductSpace ENNReal
variable {V : Type*} (w : V → ℝ) (hw : ∀ r, 0 ≤ w r) (hm : HasSum w 1)

def atomicWeightVector : ℓ²(V, ℂ) := ⟨fun r => (Real.sqrt (w r) : ℂ), by
  apply memℓp_gen
  convert hm.summable using 1
  ext r
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hw r)]⟩

@[simp] theorem atomicWeightVector_apply (r : V) :
    atomicWeightVector w hw hm r = (Real.sqrt (w r) : ℂ) := rfl

@[simp] theorem atomicWeightVector_norm : ‖atomicWeightVector w hw hm‖ = 1 := by
  have hn := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    (atomicWeightVector w hw hm)
  have hc (r : V) : ‖atomicWeightVector w hw hm r‖ ^ 2 = w r := by
    simp only [atomicWeightVector_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hw r)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, hc, hm.tsum_eq] at hn
  nlinarith [norm_nonneg (atomicWeightVector w hw hm)]

end

open scoped InnerProductSpace ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def operatorVectorFunctional (ξ : H) : (H →L[ℂ] H) →L[ℂ] ℂ where
  toFun T := inner ℂ ξ (T ξ)
  map_add' S T := by simp
  map_smul' c T := by simp
  cont := by fun_prop

@[simp] theorem operatorVectorFunctional_apply (ξ : H) (T : H →L[ℂ] H) :
    operatorVectorFunctional ξ T = inner ℂ ξ (T ξ) := rfl

theorem operatorVectorFunctional_star_mul (ξ : H) (T : H →L[ℂ] H) :
    operatorVectorFunctional ξ (star T * T) = (‖T ξ‖ ^ 2 : ℝ) := by
  change inner ℂ ξ (T.adjoint (T ξ)) = _
  rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  exact (Complex.ofReal_pow _ _).symm

@[simp] theorem operatorVectorFunctional_star (ξ : H) (T : H →L[ℂ] H) :
    operatorVectorFunctional ξ (star T) = star (operatorVectorFunctional ξ T) := by
  change inner ℂ ξ (T.adjoint ξ) = star (inner ℂ ξ (T ξ))
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm (𝕜 := ℂ) (T ξ) ξ).symm

theorem operatorVectorFunctional_norm (ξ : H) (hξ : ‖ξ‖ = 1) : ‖operatorVectorFunctional ξ‖ = 1 := by
  apply le_antisymm
  · apply (operatorVectorFunctional ξ).opNorm_le_bound (show (0 : ℝ) ≤ 1 by norm_num)
    intro T
    calc
      ‖operatorVectorFunctional ξ T‖ ≤ ‖ξ‖ * ‖T ξ‖ := norm_inner_le_norm _ _
      _ ≤ ‖ξ‖ * (‖T‖ * ‖ξ‖) := mul_le_mul_of_nonneg_left (T.le_opNorm ξ) (norm_nonneg _)
      _ = 1 * ‖T‖ := by rw [hξ]; ring
  · have hn := (operatorVectorFunctional ξ).le_opNorm (1 : H →L[ℂ] H)
    have hn1 : operatorVectorFunctional ξ 1 = 1 := by simp [inner_self_eq_norm_sq_to_K, hξ]
    rw [hn1, norm_one] at hn
    have hid : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hh := mul_le_mul_of_nonneg_left hid (norm_nonneg (operatorVectorFunctional ξ))
    simpa only [mul_one] using hn.trans hh

theorem operatorVectorFunctional_faithful (B : StarSubalgebra ℂ (H →L[ℂ] H))
    (ξ : H) (hcyc : DenseRange (fun T : B => (T : H →L[ℂ] H) ξ))
    (htr : ∀ S T : B, operatorVectorFunctional ξ ((S : H →L[ℂ] H) * T) =
      operatorVectorFunctional ξ ((T : H →L[ℂ] H) * S))
    (S : B) (hS : operatorVectorFunctional ξ (star (S : H →L[ℂ] H) * S) = 0) : S = 0 := by
  have hz : ∀ T : B, (T : H →L[ℂ] H) ξ = 0 → (star (T : H →L[ℂ] H)) ξ = 0 := by
    intro T hT
    have ht := htr (star T) T
    simp only [StarMemClass.coe_star] at ht
    rw [operatorVectorFunctional_star_mul] at ht
    have hstar := operatorVectorFunctional_star_mul ξ (star (T : H →L[ℂ] H))
    simp only [star_star] at hstar
    rw [hstar, hT, norm_zero, zero_pow (by decide)] at ht
    exact norm_eq_zero.mp (by have hh := congrArg Complex.re ht; simp only [Complex.ofReal_re] at hh; nlinarith [norm_nonneg ((star (T : H →L[ℂ] H)) ξ)])
  have ha : (S : H →L[ℂ] H) ξ = 0 := by
    rw [operatorVectorFunctional_star_mul] at hS
    have hh := congrArg Complex.re hS
    simp only [Complex.ofReal_re, Complex.zero_re] at hh
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg ((S : H →L[ℂ] H) ξ)])
  have hs := hz S ha
  have he : ∀ T : B, (S : H →L[ℂ] H) ((T : H →L[ℂ] H) ξ) = 0 := by
    intro T
    have hh : ((star (S * T) : B) : H →L[ℂ] H) ξ = 0 := by
      simp [star_mul, hs]
    have h := hz (star (S * T)) hh
    simpa using h
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact hcyc.induction_on x (isClosed_eq S.1.continuous continuous_const) he

section
open scoped InnerProductSpace lp

structure AtomicTraceData (A V : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] where
  trace : A →ₚ[ℂ] ℂ
  tracial : IsTracialPositive trace
  normalized : trace 1 = 1
  faithful : ∀ a, trace (star a * a) = 0 → a = 0
  atom : V → {e : A // IsStarProjection e}
  orthogonal : ∀ l k, l ≠ k → (atom l).1 * (atom k).1 = 0
  positive : ∀ r, 0 < (trace (atom r).1).re
  mass : HasSum (fun r => (trace (atom r).1).re) (trace 1).re

variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V)

abbrev AtomicLetters (i : I) (l r : V) : Type _ :=
  CenteredColumnIndex (d i).trace (d i).tracial (d i).atom l r

abbrev AtomicHilbertSpace : Type _ := AtomicFockSpace (AtomicLetters d)

def atomicColumnReps (i : I) (r : V) :
    A i →⋆ₐ[ℂ] (ℓ²(ColumnIndex (AtomicLetters d) i r, ℂ) →L[ℂ]
      ℓ²(ColumnIndex (AtomicLetters d) i r, ℂ)) :=
  indexedColumnRepresentation (d i).trace (d i).tracial (d i).atom
    (d i).orthogonal (d i).mass (d i).positive r

variable [DecidableEq I]

def atomicLeft (i : I) : A i →⋆ₐ[ℂ] (AtomicHilbertSpace d →L[ℂ] AtomicHilbertSpace d) :=
  atomicFockRepresentation (AtomicLetters d) (atomicColumnReps d) i

theorem atomicLeft_atoms [DecidableEq V] (i k : I) (r : V) :
    atomicLeft d i ((d i).atom r).1 = atomicLeft d k ((d k).atom r).1 := by
  apply atomicFockRepresentation_agree_atoms (AtomicLetters d) (atomicColumnReps d)
    (fun i r => ((d i).atom r).1)
  intro j r l x c
  have hv : fockColumnVertex (AtomicLetters d) j r c = columnVertex r c := by
    cases c <;> rfl
  simpa only [atomicColumnReps, hv] using indexedColumnRepresentation_atom
    (d j).trace (d j).tracial (d j).atom (d j).orthogonal (d j).mass (d j).positive r l x c

theorem atomicLeft_centered (i : I) (a : A i)
    (ha : ∀ r, (d i).trace (((d i).atom r).1 * a * ((d i).atom r).1) = 0)
    (x : AtomicHilbertSpace d) (hx : FockAway (AtomicLetters d) i x) :
    FockStarts (AtomicLetters d) i (atomicLeft d i a x) := by
  apply atomicFock_creation_starts (AtomicLetters d) (atomicColumnReps d) i a _ x hx
  intro r
  rw [atomicColumnReps, indexedColumnRepresentation_vacuum, ha r, mul_zero]

theorem atomicLeft_away_norm (i : I) (a : A i) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ r, ((d i).trace (((d i).atom r).1 * (star a * a) * ((d i).atom r).1)).re ≤
      C ^ 2 * ((d i).trace ((d i).atom r).1).re)
    (x : AtomicHilbertSpace d) (hx : FockAway (AtomicLetters d) i x) :
    ‖atomicLeft d i a x‖ ≤ C * ‖x‖ := by
  apply atomicFock_creation_norm (AtomicLetters d) (atomicColumnReps d) i a C hC _ x hx
  intro r
  apply (sq_le_sq₀ (norm_nonneg _) hC).mp
  rw [atomicColumnReps, indexedColumnRepresentation_vacuum_norm]
  exact (div_le_iff₀ ((d i).positive r)).mpr (ha r)

theorem atomicLeft_injective (i : I) : Function.Injective (atomicLeft d i) := by
  classical
  have hk : ∀ a : A i, atomicLeft d i a = 0 → a = 0 := by
    intro a ha
    let τ := (d i).trace
    have hx : (τ.toPreGNS a : τ.GNS) = 0 := by
      apply traceRightAtoms_jointKernel τ (d i).tracial (d i).atom
        (d i).orthogonal (d i).mass
      intro r
      let : ∀ l, DecidableEq (AtomicLetters d i l r) := fun _ => Classical.decEq _
      have hc := atomicFock_zero_column (AtomicLetters d) (atomicColumnReps d) i a ha r
      change indexedColumnRepresentation (d i).trace (d i).tracial (d i).atom
        (d i).orthogonal (d i).mass (d i).positive r a (lp.single 2 none 1) = 0 at hc
      let basis := tracialColumnBasis (d i).trace (d i).tracial (d i).atom
        (d i).orthogonal (d i).mass (d i).positive r
      have vector_zero :=
        (indexedColumnRepresentation_vacuum_vector (d i).trace (d i).tracial (d i).atom
          (d i).orthogonal (d i).mass (d i).positive r a).symm.trans hc
      have hv : traceColumnRepresentation (d i).trace (d i).tracial ((d i).atom r)
          a (columnUnit (d i).trace (d i).tracial ((d i).atom r)) = 0 :=
        basis.repr.injective (vector_zero.trans (map_zero basis.repr).symm)
      rw [columnUnit, map_smul] at hv
      have hn : (((Real.sqrt (τ ((d i).atom r).1).re)⁻¹ : ℂ)) ≠ 0 := by
        exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ((d i).positive r)).ne')
      have hv' := (smul_eq_zero.mp hv).resolve_left hn
      have hv'' := congrArg Subtype.val hv'
      rw [columnVacuum_action] at hv''
      simpa [gnsRight_coe, τ] using hv''
    apply (d i).faithful a
    have hh : inner ℂ (τ.toPreGNS a : τ.GNS) (τ.toPreGNS a : τ.GNS) = 0 := by simp [hx]
    simpa only [Completion.inner_coe, PositiveLinearMap.preGNS_inner_def,
      PositiveLinearMap.ofPreGNS_toPreGNS] using hh
  intro a b hab
  apply sub_eq_zero.mp
  apply hk
  rw [map_sub, hab, sub_self]

end

section
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V)

def atomicVacuum (k : I) : AtomicHilbertSpace d :=
  fockVacuum (AtomicLetters d)
    (atomicWeightVector (fun r => ((d k).trace ((d k).atom r).1).re)
      (fun r => ((d k).positive r).le)
      (by simpa only [(d k).normalized, Complex.one_re] using (d k).mass))

@[simp] theorem atomicVacuum_norm (k : I) : ‖atomicVacuum d k‖ = 1 := by
  rw [atomicVacuum, fockVacuum_norm, atomicWeightVector_norm]

variable [DecidableEq I]

theorem atomicLeft_vacuum_trace (k i : I)
    (hw : ∀ r, ((d k).trace ((d k).atom r).1).re =
      ((d i).trace ((d i).atom r).1).re) (a : A i) :
    inner ℂ (atomicVacuum d k) (atomicLeft d i a (atomicVacuum d k)) = (d i).trace a := by
  rw [atomicVacuum, atomicLeft, atomicFock_vacuum_inner]
  rw [← (trace_hasSum_atom_corners (d i).trace (d i).tracial (d i).atom
    (d i).orthogonal (d i).mass a).tsum_eq]
  apply tsum_congr
  intro r
  rw [atomicColumnReps, indexedColumnRepresentation_vacuum,
    atomicWeightVector_apply, hw r]
  have hne : (Real.sqrt (((d i).trace ((d i).atom r).1).re) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ((d i).positive r)).ne'
  simp only [Complex.star_def, Complex.conj_ofReal]
  field_simp

end

section

variable {I B : Type*} [Ring B] [Algebra ℂ B]

structure IsCenteredWord (K : I → Submodule ℂ B) (w : List (I × B)) : Prop where
  centered : ∀ x ∈ w, x.2 ∈ K x.1
  alternating : w.IsChain (fun x y => x.1 ≠ y.1)

def wordValue (w : List (I × B)) : B := (w.map Prod.snd).prod

omit [Algebra ℂ B] in
@[simp] theorem wordValue_nil : wordValue ([] : List (I × B)) = 1 := rfl
omit [Algebra ℂ B] in
@[simp] theorem wordValue_cons (x : I × B) (w : List (I × B)) :
    wordValue (x :: w) = x.2 * wordValue w := rfl

theorem IsCenteredWord.tail {K : I → Submodule ℂ B} {x : I × B} {w : List (I × B)}
    (h : IsCenteredWord K (x :: w)) : IsCenteredWord K w :=
  ⟨fun _ hx => h.centered _ (List.mem_cons_of_mem _ hx), h.alternating.tail⟩

theorem IsCenteredWord.head {K : I → Submodule ℂ B} {x : I × B} {w : List (I × B)}
    (h : IsCenteredWord K (x :: w)) : x.2 ∈ K x.1 := h.centered x (by simp)

theorem IsCenteredWord.modify_head {K : I → Submodule ℂ B}
    {x : I × B} {w : List (I × B)} (h : IsCenteredWord K (x :: w))
    {b : B} (hb : b ∈ K x.1) : IsCenteredWord K ((x.1, b) :: w) := by
  refine ⟨?_, List.IsChain.imp_head (x := x) (y := (x.1, b)) (fun hh => hh) h.alternating⟩
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact hb
  · exact h.centered y (List.mem_cons_of_mem x hy)

theorem IsCenteredWord.prepend {K : I → Submodule ℂ B}
    {x : I × B} {w : List (I × B)} (h : IsCenteredWord K (x :: w))
    {i : I} {b : B} (hb : b ∈ K i) (hi : i ≠ x.1) :
    IsCenteredWord K ((i, b) :: x :: w) := by
  refine ⟨?_, List.isChain_cons_cons.mpr ⟨hi, h.alternating⟩⟩
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact hb
  · exact h.centered y hy

variable (D : NonUnitalSubalgebra ℂ B) (F : I → NonUnitalSubalgebra ℂ B) (K : I → Submodule ℂ B)

structure CenteredDecomposition : Prop where
  diagonal_le : ∀ i, D ≤ F i
  centered_le : ∀ i, K i ≤ (F i).toSubmodule
  decompose : ∀ i a, a ∈ F i → ∃ d ∈ D, ∃ c ∈ K i, a = d + c
  diagonal_mul : ∀ i d c, d ∈ D → c ∈ K i → d * c ∈ K i

def normalSpan : Submodule ℂ B :=
  Submodule.span ℂ {b | b ∈ D ∨ ∃ w, IsCenteredWord K w ∧ b = wordValue w}

theorem normalSpan_diagonal {d : B} (hd : d ∈ D) : d ∈ normalSpan D K :=
  Submodule.subset_span (Or.inl hd)

theorem normalSpan_word {w : List (I × B)} (hw : IsCenteredWord K w) :
    wordValue w ∈ normalSpan D K := Submodule.subset_span (Or.inr ⟨w, hw, rfl⟩)

variable {D F K}

theorem CenteredDecomposition.diagonal_word_mem (h : CenteredDecomposition D F K)
    {d : B} (hd : d ∈ D) {w : List (I × B)} (hw : IsCenteredWord K w) :
    d * wordValue w ∈ normalSpan D K := by
  cases w with
  | nil => simpa using normalSpan_diagonal D K hd
  | cons x w =>
    have hh := hw.modify_head (h.diagonal_mul x.1 d x.2 hd hw.head)
    simpa only [wordValue_cons, mul_assoc] using normalSpan_word D K hh

theorem CenteredDecomposition.factor_word_mem (h : CenteredDecomposition D F K)
    {i : I} {a : B} (ha : a ∈ F i) {w : List (I × B)} (hw : IsCenteredWord K w) :
    a * wordValue w ∈ normalSpan D K := by
  classical
  cases w with
  | nil =>
    rcases h.decompose i a ha with ⟨d, hd, c, hc, rfl⟩
    have hcw : IsCenteredWord K [(i,c)] :=
      ⟨by simpa, List.isChain_singleton _⟩
    have hh := (normalSpan D K).add_mem (normalSpan_diagonal D K hd)
      (normalSpan_word D K hcw)
    simpa using hh
  | cons x w =>
    by_cases hi : i = x.1
    · have hap : a * x.2 ∈ F x.1 := (F x.1).mul_mem (hi ▸ ha)
        (h.centered_le x.1 hw.head)
      rcases h.decompose x.1 (a * x.2) hap with ⟨d, hd, c, hc, he⟩
      rw [wordValue_cons, ← mul_assoc, he, add_mul]
      exact (normalSpan D K).add_mem (h.diagonal_word_mem hd hw.tail)
        (normalSpan_word D K (hw.modify_head hc))
    · rcases h.decompose i a ha with ⟨d, hd, c, hc, rfl⟩
      rw [add_mul]
      exact (normalSpan D K).add_mem (h.diagonal_word_mem hd hw)
        (normalSpan_word D K (hw.prepend hc hi))

def leftStabilizer (W : Submodule ℂ B) : Subalgebra ℂ B where
  carrier := {a | ∀ w ∈ W, a * w ∈ W}
  mul_mem' ha hb w hw := by simpa only [mul_assoc] using ha _ (hb w hw)
  add_mem' ha hb w hw := by simpa only [add_mul] using W.add_mem (ha w hw) (hb w hw)
  algebraMap_mem' c w hw := by simpa only [Algebra.smul_def] using W.smul_mem c hw

theorem CenteredDecomposition.factor_stabilizes (h : CenteredDecomposition D F K)
    {i : I} {a : B} (ha : a ∈ F i) : a ∈ leftStabilizer (normalSpan D K) := by
  intro b hb
  induction hb using Submodule.span_induction with
  | mem b hb =>
    rcases hb with hb | ⟨w, hw, rfl⟩
    · have hab := (F i).mul_mem ha (h.diagonal_le i hb)
      simpa using h.factor_word_mem hab
        (show IsCenteredWord K [] from ⟨by simp, List.isChain_nil⟩)
    · exact h.factor_word_mem ha hw
  | zero => simp
  | add b c _ _ hb hc => simpa only [mul_add] using (normalSpan D K).add_mem hb hc
  | smul c b _ hb => simpa only [mul_smul_comm] using (normalSpan D K).smul_mem c hb

theorem CenteredDecomposition.adjoin_le_normalSpan (h : CenteredDecomposition D F K) :
    (Algebra.adjoin ℂ (⋃ i, (F i : Set B))).toSubmodule ≤ normalSpan D K := by
  have hs : Algebra.adjoin ℂ (⋃ i, (F i : Set B)) ≤ leftStabilizer (normalSpan D K) := by
    apply Algebra.adjoin_le
    intro a ha
    rcases Set.mem_iUnion.mp ha with ⟨i, hi⟩
    exact h.factor_stabilizes hi
  intro a ha
  have h1 := normalSpan_word D K
    (show IsCenteredWord K [] from ⟨by simp, List.isChain_nil⟩)
  simpa only [mul_one] using hs ha 1 h1

variable (φ : B →ₗ[ℂ] ℂ)
variable (hfree : ∀ w, IsCenteredWord K w → w ≠ [] → φ (wordValue w) = 0)

include hfree

theorem CenteredDecomposition.diagonal_word_zero (h : CenteredDecomposition D F K)
    {d : B} (hd : d ∈ D) {w : List (I × B)} (hw : IsCenteredWord K w) (hne : w ≠ []) :
    φ (d * wordValue w) = 0 := by
  cases w with
  | nil => exact (hne rfl).elim
  | cons x w =>
    have hh := hw.modify_head (h.diagonal_mul x.1 d x.2 hd hw.head)
    simpa only [wordValue_cons, mul_assoc] using hfree _ hh (by simp)

theorem CenteredDecomposition.factor_different_zero (h : CenteredDecomposition D F K)
    {i : I} {a : B} (ha : a ∈ F i) {x : I × B} {w : List (I × B)}
    (hw : IsCenteredWord K (x :: w)) (hi : i ≠ x.1) :
    φ (a * wordValue (x :: w)) = 0 := by
  rcases h.decompose i a ha with ⟨d, hd, c, hc, rfl⟩
  rw [add_mul, map_add, h.diagonal_word_zero φ hfree hd hw (by simp)]
  simpa only [zero_add, wordValue_cons] using hfree _ (hw.prepend hc hi) (by simp)

theorem CenteredDecomposition.factor_long_zero (h : CenteredDecomposition D F K)
    {i : I} {a : B} (ha : a ∈ F i) {w : List (I × B)}
    (hw : IsCenteredWord K w) (hlen : 2 ≤ w.length) : φ (a * wordValue w) = 0 := by
  classical
  cases w with
  | nil => simp at hlen
  | cons x w =>
    have hwne : w ≠ [] := by intro he; simp [he] at hlen
    by_cases hi : i = x.1
    · have hap : a * x.2 ∈ F x.1 := (F x.1).mul_mem (hi ▸ ha)
        (h.centered_le x.1 hw.head)
      rcases h.decompose x.1 (a * x.2) hap with ⟨d, hd, c, hc, he⟩
      rw [wordValue_cons, ← mul_assoc, he, add_mul, map_add,
        h.diagonal_word_zero φ hfree hd hw.tail hwne]
      simpa only [zero_add, wordValue_cons] using hfree _ (hw.modify_head hc) (by simp)
    · exact h.factor_different_zero φ hfree ha hw hi

omit hfree

variable [StarRing B]

def starWord (w : List (I × B)) : List (I × B) :=
  w.reverse.map (fun x => (x.1, star x.2))

omit [Algebra ℂ B] in
@[simp] theorem wordValue_starWord (w : List (I × B)) :
    wordValue (starWord w) = star (wordValue w) := by
  induction w with
  | nil => simp [starWord, wordValue]
  | cons x w ih =>
    simp only [starWord, List.reverse_cons, List.map_append,
      wordValue, List.map_append, List.prod_append,
      List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one, star_mul] at *
    rw [ih]

omit [Algebra ℂ B] in
@[simp] theorem starWord_length (w : List (I × B)) : (starWord w).length = w.length := by
  simp [starWord]

variable (hKstar : ∀ i c, c ∈ K i → star c ∈ K i)

include hKstar in
theorem IsCenteredWord.starWord {w : List (I × B)} (hw : IsCenteredWord K w) :
    IsCenteredWord K (starWord w) := by
  constructor
  · intro x hx
    rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact hKstar y.1 y.2 (hw.centered y (List.mem_reverse.mp hy))
  · apply (List.isChain_map _).mpr
    apply List.isChain_reverse.mpr
    exact hw.alternating.imp (fun _ _ hh => Ne.symm hh)

variable (hφstar : ∀ b, φ (star b) = star (φ b))
variable (hFstar : ∀ i a, a ∈ F i → star a ∈ F i)
variable (htr : ∀ i a b, a ∈ F i → b ∈ F i → φ (a * b) = φ (b * a))

include hfree hKstar hφstar hFstar

theorem CenteredDecomposition.factor_long_zero_right (h : CenteredDecomposition D F K)
    {i : I} {a : B} (ha : a ∈ F i) {w : List (I × B)}
    (hw : IsCenteredWord K w) (hlen : 2 ≤ w.length) : φ (wordValue w * a) = 0 := by
  have hh := h.factor_long_zero φ hfree (hFstar i a ha) (hw.starWord hKstar)
    (by simpa using hlen)
  rw [wordValue_starWord, ← star_mul, hφstar, star_eq_zero] at hh
  exact hh

include htr

theorem CenteredDecomposition.factor_word_trace (h : CenteredDecomposition D F K)
    {i : I} {a : B} (ha : a ∈ F i) {w : List (I × B)} (hw : IsCenteredWord K w) :
    φ (a * wordValue w) = φ (wordValue w * a) := by
  classical
  cases w with
  | nil => simp
  | cons x w =>
    cases w with
    | nil =>
      by_cases hi : i = x.1
      · simpa using htr i a x.2 ha (hi.symm ▸ h.centered_le x.1 hw.head)
      · have hl := h.factor_different_zero φ hfree ha hw hi
        have hs : IsCenteredWord K [(x.1, star x.2)] := hw.starWord hKstar
        have hr := h.factor_different_zero φ hfree (hFstar i a ha) hs hi
        simp only [wordValue_cons, wordValue_nil, mul_one] at hl hr ⊢
        rw [← star_mul, hφstar, star_eq_zero] at hr
        exact hl.trans hr.symm
    | cons y w =>
      have hl := h.factor_long_zero φ hfree ha hw (by simp)
      have hr := h.factor_long_zero_right φ hfree hKstar hφstar hFstar ha hw (by simp)
      exact hl.trans hr.symm

theorem CenteredDecomposition.factor_span_trace (h : CenteredDecomposition D F K)
    {i : I} {a : B} (ha : a ∈ F i) {b : B} (hb : b ∈ normalSpan D K) :
    φ (a * b) = φ (b * a) := by
  induction hb using Submodule.span_induction with
  | mem b hb =>
    rcases hb with hb | ⟨w, hw, rfl⟩
    · exact htr i a b ha (h.diagonal_le i hb)
    · exact h.factor_word_trace φ hfree hKstar hφstar hFstar htr ha hw
  | zero => simp
  | add b c _ _ hb hc => simp only [mul_add, add_mul, map_add, hb, hc]
  | smul c b _ hb => simp only [mul_smul_comm, smul_mul_assoc, map_smul, hb]

theorem CenteredDecomposition.adjoin_trace (h : CenteredDecomposition D F K)
    {a b : B} (ha : a ∈ Algebra.adjoin ℂ (⋃ i, (F i : Set B)))
    (hb : b ∈ Algebra.adjoin ℂ (⋃ i, (F i : Set B))) : φ (a * b) = φ (b * a) := by
  induction ha using Algebra.adjoin_induction generalizing b with
  | mem a ha =>
    rcases Set.mem_iUnion.mp ha with ⟨i, hi⟩
    exact h.factor_span_trace φ hfree hKstar hφstar hFstar htr hi
      (h.adjoin_le_normalSpan hb)
  | algebraMap c => rw [Algebra.commutes]
  | add a c _ _ ha hc => simp only [add_mul, mul_add, map_add, ha hb, hc hb]
  | mul a c ha hc hia hic =>
    calc
      φ ((a * c) * b) = φ (a * (c * b)) := by rw [mul_assoc]
      _ = φ ((c * b) * a) := hia ((Algebra.adjoin ℂ _).mul_mem hc hb)
      _ = φ (c * (b * a)) := by rw [mul_assoc]
      _ = φ ((b * a) * c) := hic ((Algebra.adjoin ℂ _).mul_mem hb ha)
      _ = φ (b * (a * c)) := by rw [mul_assoc]

end

section

variable {V B : Type*} [Ring B] [Algebra ℂ B]

def projectionCorner (p : B) : NonUnitalSubalgebra ℂ B where
  carrier := {a | p * a = a ∧ a * p = a}
  zero_mem' := by simp
  add_mem' ha hb := ⟨by rw [mul_add, ha.1, hb.1], by rw [add_mul, ha.2, hb.2]⟩
  smul_mem' c a ha := ⟨by rw [mul_smul_comm, ha.1], by rw [smul_mul_assoc, ha.2]⟩
  mul_mem' ha hb := by
    constructor
    · rw [← mul_assoc, ha.1]
    · rw [mul_assoc, hb.2]

@[simp] theorem mem_projectionCorner {p a : B} :
    a ∈ projectionCorner p ↔ p * a = a ∧ a * p = a := Iff.rfl

variable (q : V → B)
variable (hq : ∀ r, q r * q r = q r)
variable (ho : ∀ r t, r ≠ t → q r * q t = 0)

omit [Algebra ℂ B] in
include hq ho in
lemma atom_mul_sum [DecidableEq V] (s : Finset V) (r : V) :
    q r * (∑ t ∈ s, q t) = if r ∈ s then q r else 0 := by
  rw [Finset.mul_sum]
  by_cases hr : r ∈ s
  · rw [ite_eq_left hr, Finset.sum_eq_single r]
    · exact hq r
    · intro t _ ht
      exact ho r t ht.symm
    · exact fun hn => (hn hr).elim
  · rw [ite_eq_right hr]
    exact Finset.sum_eq_zero fun t ht => ho r t (by rintro rfl; exact hr ht)

omit [Algebra ℂ B] in
include hq ho in
lemma sum_mul_atom [DecidableEq V] (s : Finset V) (r : V) :
    (∑ t ∈ s, q t) * q r = if r ∈ s then q r else 0 := by
  rw [Finset.sum_mul]
  by_cases hr : r ∈ s
  · rw [ite_eq_left hr, Finset.sum_eq_single r]
    · exact hq r
    · intro t _ ht
      exact ho t r ht
    · exact fun hn => (hn hr).elim
  · rw [ite_eq_right hr]
    exact Finset.sum_eq_zero fun t ht => ho t r (by rintro rfl; exact hr ht)

include hq ho in
lemma atom_mem_finiteCorner [DecidableEq V] {s : Finset V} {r : V} (hr : r ∈ s) :
    q r ∈ projectionCorner (∑ t ∈ s, q t) := by
  constructor
  · rw [sum_mul_atom q hq ho, ite_eq_left hr]
  · rw [atom_mul_sum q hq ho, ite_eq_left hr]

def finiteAtomicSpan (s : Finset V) : Submodule ℂ B :=
  Submodule.span ℂ (q '' (s : Set V))

include hq ho in
theorem finiteAtomicSpan_mul {s : Finset V} {a b : B}
    (ha : a ∈ finiteAtomicSpan q s) (hb : b ∈ finiteAtomicSpan q s) :
    a * b ∈ finiteAtomicSpan q s := by
  classical
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rcases ha with ⟨r, hr, rfl⟩
    induction hb using Submodule.span_induction with
    | mem b hb =>
      rcases hb with ⟨t, _, rfl⟩
      by_cases ht : r = t
      · subst t
        rw [hq]
        exact Submodule.subset_span ⟨r, hr, rfl⟩
      · rw [ho r t ht]
        exact Submodule.zero_mem _
    | zero => simp
    | add b c _ _ hb hc => simpa only [mul_add] using (finiteAtomicSpan q s).add_mem hb hc
    | smul c b _ hb => simpa only [mul_smul_comm] using (finiteAtomicSpan q s).smul_mem c hb
  | zero => simp
  | add a c _ _ ha hc => simpa only [add_mul] using (finiteAtomicSpan q s).add_mem ha hc
  | smul c a _ ha => simpa only [smul_mul_assoc] using (finiteAtomicSpan q s).smul_mem c ha

def finiteAtomicDiagonal (s : Finset V) : NonUnitalSubalgebra ℂ B where
  __ := finiteAtomicSpan q s
  mul_mem' := finiteAtomicSpan_mul q hq ho

@[simp] theorem finiteAtomicDiagonal_toSubmodule (s : Finset V) :
    (finiteAtomicDiagonal q hq ho s).toSubmodule = finiteAtomicSpan q s := rfl

include hq ho in
theorem finiteAtomicDiagonal_le_corner [DecidableEq V] (s : Finset V) :
    finiteAtomicDiagonal q hq ho s ≤ projectionCorner (∑ t ∈ s, q t) := by
  change finiteAtomicSpan q s ≤ (projectionCorner (∑ t ∈ s, q t)).toSubmodule
  apply Submodule.span_le.mpr
  rintro a ⟨r, hr, rfl⟩
  exact atom_mem_finiteCorner q hq ho hr

include hq ho in
theorem finiteAtomicDiagonal_eigen {s : Finset V} {a : B}
    (ha : a ∈ finiteAtomicDiagonal q hq ho s) (r : V) :
    ∃ z : ℂ, q r * a = z • q r ∧ a * q r = z • q r := by
  classical
  change a ∈ finiteAtomicSpan q s at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rcases ha with ⟨t, _, rfl⟩
    by_cases ht : r = t
    · subst t
      exact ⟨1, by rw [hq, one_smul], by rw [hq, one_smul]⟩
    · exact ⟨0, by rw [ho r t ht, zero_smul], by rw [ho t r (Ne.symm ht), zero_smul]⟩
  | zero => exact ⟨0, by simp, by simp⟩
  | add a b _ _ ha hb =>
    rcases ha with ⟨z, hz, hz'⟩
    rcases hb with ⟨w, hw, hw'⟩
    exact ⟨z+w, by rw [mul_add, hz, hw, add_smul], by rw [add_mul, hz', hw', add_smul]⟩
  | smul c a _ ha =>
    rcases ha with ⟨z, hz, hz'⟩
    exact ⟨c*z, by rw [mul_smul_comm, hz, smul_smul], by rw [smul_mul_assoc, hz', smul_smul]⟩

variable (φ : B →ₗ[ℂ] ℂ)

def atomCornerFunctional (r : V) : B →ₗ[ℂ] ℂ where
  toFun a := φ (q r * a * q r)
  map_add' a b := by simp only [mul_add, add_mul, map_add]
  map_smul' c a := by simp only [mul_smul_comm, smul_mul_assoc, map_smul, RingHom.id_apply]

@[simp] theorem atomCornerFunctional_apply (r : V) (a : B) :
    atomCornerFunctional q φ r a = φ (q r * a * q r) := rfl

def finiteAtomExpectation (s : Finset V) (a : B) : B :=
  ∑ r ∈ s, (φ (q r * a * q r) / φ (q r)) • q r

theorem finiteAtomExpectation_mem (s : Finset V) (a : B) :
    finiteAtomExpectation q φ s a ∈ finiteAtomicDiagonal q hq ho s := by
  change (∑ r ∈ s, _) ∈ finiteAtomicSpan q s
  apply Submodule.sum_mem
  intro r hr
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, hr, rfl⟩)

include hq ho in
theorem finiteAtomExpectation_atom [DecidableEq V] (s : Finset V) (a : B) (r : V) :
    q r * finiteAtomExpectation q φ s a * q r =
      if r ∈ s then (φ (q r * a * q r) / φ (q r)) • q r else 0 := by
  simp only [finiteAtomExpectation, Finset.mul_sum, Finset.sum_mul,
    mul_smul_comm, smul_mul_assoc]
  by_cases hr : r ∈ s
  · rw [ite_eq_left hr, Finset.sum_eq_single r]
    · rw [hq, hq]
    · intro t _ ht
      rw [ho r t ht.symm, zero_mul, smul_zero]
    · exact fun hn => (hn hr).elim
  · rw [ite_eq_right hr]
    apply Finset.sum_eq_zero
    intro t ht
    rw [ho r t (by rintro rfl; exact hr ht), zero_mul, smul_zero]

include hq ho in
theorem finiteCorner_outside [DecidableEq V] {s : Finset V} {a : B}
    (ha : a ∈ projectionCorner (∑ t ∈ s, q t)) {r : V} (hr : r ∉ s) :
    q r * a = 0 := by
  rw [← ha.1, ← mul_assoc, atom_mul_sum q hq ho, ite_eq_right hr, zero_mul]

include hq ho in
theorem finiteAtomExpectation_centered [DecidableEq V]
    (hφq : ∀ r, φ (q r) ≠ 0) {s : Finset V} {a : B}
    (ha : a ∈ projectionCorner (∑ t ∈ s, q t)) (r : V) :
    φ (q r * (a - finiteAtomExpectation q φ s a) * q r) = 0 := by
  rw [mul_sub, sub_mul, map_sub, finiteAtomExpectation_atom q hq ho]
  by_cases hr : r ∈ s
  · rw [ite_eq_left hr, map_smul, smul_eq_mul, div_mul_cancel₀ _ (hφq r), sub_self]
  · rw [ite_eq_right hr, map_zero, finiteCorner_outside q hq ho ha hr, zero_mul, map_zero,
      sub_self]

def finiteFactorCorner (F : NonUnitalSubalgebra ℂ B) (s : Finset V) :
    NonUnitalSubalgebra ℂ B := F ⊓ projectionCorner (∑ r ∈ s, q r)

def atomicCenteredSubmodule (F : NonUnitalSubalgebra ℂ B) : Submodule ℂ B :=
  F.toSubmodule ⊓ ⨅ r, LinearMap.ker (atomCornerFunctional q φ r)

@[simp] theorem mem_atomicCenteredSubmodule (F : NonUnitalSubalgebra ℂ B) (a : B) :
    a ∈ atomicCenteredSubmodule q φ F ↔ a ∈ F ∧ ∀ r, φ (q r * a * q r) = 0 := by
  simp [atomicCenteredSubmodule]

include hq ho in
theorem finiteDiagonal_le_factorCorner [DecidableEq V]
    (F : NonUnitalSubalgebra ℂ B) (hF : ∀ r, q r ∈ F) (s : Finset V) :
    finiteAtomicDiagonal q hq ho s ≤ finiteFactorCorner q F s := by
  intro a ha
  constructor
  · have hh : finiteAtomicSpan q s ≤ F.toSubmodule := by
      apply Submodule.span_le.mpr
      rintro b ⟨r, _, rfl⟩
      exact hF r
    exact hh ha
  · exact finiteAtomicDiagonal_le_corner q hq ho s ha

include hq ho in
theorem finiteFactorCorner_decompose [DecidableEq V]
    (F : NonUnitalSubalgebra ℂ B) (hF : ∀ r, q r ∈ F)
    (hφq : ∀ r, φ (q r) ≠ 0) {s : Finset V} {a : B}
    (ha : a ∈ finiteFactorCorner q F s) :
    ∃ d ∈ finiteAtomicDiagonal q hq ho s,
      ∃ c ∈ atomicCenteredSubmodule q φ (finiteFactorCorner q F s), a = d + c := by
  let b := finiteAtomExpectation q φ s a
  have hb : b ∈ finiteAtomicDiagonal q hq ho s := finiteAtomExpectation_mem q hq ho φ s a
  have hbF := finiteDiagonal_le_factorCorner q hq ho F hF s hb
  refine ⟨b, hb, a-b, ?_, by simp⟩
  rw [mem_atomicCenteredSubmodule]
  exact ⟨(finiteFactorCorner q F s).sub_mem ha hbF,
    finiteAtomExpectation_centered q hq ho φ hφq ha.2⟩

include hq ho in
theorem finiteDiagonal_mul_centered [DecidableEq V]
    (F : NonUnitalSubalgebra ℂ B) (hF : ∀ r, q r ∈ F)
    {s : Finset V} {d c : B} (hd : d ∈ finiteAtomicDiagonal q hq ho s)
    (hc : c ∈ atomicCenteredSubmodule q φ (finiteFactorCorner q F s)) :
    d * c ∈ atomicCenteredSubmodule q φ (finiteFactorCorner q F s) := by
  rw [mem_atomicCenteredSubmodule] at hc ⊢
  refine ⟨(finiteFactorCorner q F s).mul_mem
    (finiteDiagonal_le_factorCorner q hq ho F hF s hd) hc.1, ?_⟩
  intro r
  obtain ⟨z, hz, _⟩ := finiteAtomicDiagonal_eigen q hq ho hd r
  rw [← mul_assoc (q r) d c, hz, smul_mul_assoc, smul_mul_assoc, map_smul, hc.2 r, smul_zero]

variable [StarRing B]
variable (hqstar : ∀ r, star (q r) = q r)
variable (hφstar : ∀ a, φ (star a) = star (φ a))

include hqstar in
theorem finiteFactorCorner_star (F : NonUnitalSubalgebra ℂ B)
    (hFs : ∀ a, a ∈ F → star a ∈ F) {s : Finset V} {a : B}
    (ha : a ∈ finiteFactorCorner q F s) : star a ∈ finiteFactorCorner q F s := by
  refine ⟨hFs a ha.1, ?_, ?_⟩
  · have hh := congrArg star ha.2.2
    simpa only [star_mul, star_sum, hqstar] using hh
  · have hh := congrArg star ha.2.1
    simpa only [star_mul, star_sum, hqstar] using hh

include hqstar hφstar in
theorem atomicCenteredSubmodule_star (F : NonUnitalSubalgebra ℂ B)
    (hFs : ∀ a, a ∈ F → star a ∈ F) {a : B}
    (ha : a ∈ atomicCenteredSubmodule q φ F) :
    star a ∈ atomicCenteredSubmodule q φ F := by
  rw [mem_atomicCenteredSubmodule] at ha ⊢
  refine ⟨hFs a ha.1, ?_⟩
  intro r
  have hh := congrArg star (ha.2 r)
  rw [star_zero, ← hφstar, star_mul, star_mul, hqstar] at hh
  simpa only [mul_assoc] using hh

end

section
variable {V I B : Type*} [Ring B] [Algebra ℂ B] [DecidableEq V]
variable (q : V → B) (hq : ∀ r, q r * q r = q r)
  (ho : ∀ r t, r ≠ t → q r * q t = 0)
  (φ : B →ₗ[ℂ] ℂ) (hφq : ∀ r, φ (q r) ≠ 0)
  (F : I → NonUnitalSubalgebra ℂ B) (hF : ∀ i r, q r ∈ F i)

include hφq hF

theorem finiteCornerCenteredDecomposition (s : Finset V) :
    CenteredDecomposition (finiteAtomicDiagonal q hq ho s)
      (fun i => finiteFactorCorner q (F i) s)
      (fun i => atomicCenteredSubmodule q φ (finiteFactorCorner q (F i) s)) where
  diagonal_le i := finiteDiagonal_le_factorCorner q hq ho (F i) (hF i) s
  centered_le _ _ ha := ha.1
  decompose i _ ha := finiteFactorCorner_decompose q hq ho φ (F i) (hF i) hφq ha
  diagonal_mul i _ _ hd hc := finiteDiagonal_mul_centered q hq ho φ (F i) (hF i) hd hc

include hq ho hφq hF

theorem finiteCorner_adjoin_trace [StarRing B]
    (hqstar : ∀ r, star (q r) = q r)
    (hφstar : ∀ a, φ (star a) = star (φ a))
    (hFstar : ∀ i a, a ∈ F i → star a ∈ F i)
    (htr : ∀ i a b, a ∈ F i → b ∈ F i → φ (a*b) = φ (b*a))
    (hfree : ∀ w, IsCenteredWord (fun i => atomicCenteredSubmodule q φ (F i)) w →
      w ≠ [] → φ (wordValue w) = 0)
    (s : Finset V) {a b : B}
    (ha : a ∈ Algebra.adjoin ℂ (⋃ i, (finiteFactorCorner q (F i) s : Set B)))
    (hb : b ∈ Algebra.adjoin ℂ (⋃ i, (finiteFactorCorner q (F i) s : Set B))) :
    φ (a*b) = φ (b*a) := by
  let h := finiteCornerCenteredDecomposition q hq ho φ hφq F hF s
  apply h.adjoin_trace φ _ _ hφstar _ _ ha hb
  · intro w hw hn
    apply hfree w ⟨?_, hw.alternating⟩ hn
    intro x hx
    have hh := hw.centered x hx
    rw [mem_atomicCenteredSubmodule] at hh ⊢
    exact ⟨hh.1.1, hh.2⟩
  · intro i c hc
    exact atomicCenteredSubmodule_star q φ hqstar hφstar _
      (fun a ha => finiteFactorCorner_star q hqstar (F i) (hFstar i) ha) hc
  · intro i a ha
    exact finiteFactorCorner_star q hqstar (F i) (hFstar i) ha
  · intro i a b ha hb
    exact htr i a b ha.1 hb.1

end

section
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {ι : Type*} {l : Filter ι}

theorem strong_apply_tendsto (S : ι → H →L[ℂ] H) (T : H →L[ℂ] H)
    (C : ℝ) (hS : ∀ i, ‖S i‖ ≤ C)
    (hlim : ∀ x, Tendsto (fun i => S i x) l (𝓝 (T x)))
    {x : ι → H} {y : H} (hx : Tendsto x l (𝓝 y)) :
    Tendsto (fun i => S i (x i)) l (𝓝 (T y)) := by
  have hz : Tendsto (fun i => S i (x i-y)) l (𝓝 0) := by
    apply squeeze_zero_norm (fun i => (S i).le_opNorm (x i-y) |>.trans
      (mul_le_mul_of_nonneg_right (hS i) (norm_nonneg _)))
    simpa only [sub_self, norm_zero, mul_zero] using
      (tendsto_const_nhds (x := C) (f := l)).mul
        ((hx.sub (tendsto_const_nhds (x := y) (f := l))).norm)
  have hh := hz.add (hlim y)
  simpa only [← map_add, sub_add_cancel, zero_add] using hh

theorem strong_mul_tendsto (S R : ι → H →L[ℂ] H) (T U : H →L[ℂ] H)
    (C : ℝ) (hS : ∀ i, ‖S i‖ ≤ C)
    (hlimS : ∀ x, Tendsto (fun i => S i x) l (𝓝 (T x)))
    (hlimR : ∀ x, Tendsto (fun i => R i x) l (𝓝 (U x))) (x : H) :
    Tendsto (fun i => (S i * R i) x) l (𝓝 ((T*U) x)) :=
  strong_apply_tendsto S T C hS hlimS (hlimR x)

def StronglyApproximable (F : ι → Subalgebra ℂ (H →L[ℂ] H)) (l : Filter ι)
    (T : H →L[ℂ] H) : Prop :=
  ∃ S : ι → H →L[ℂ] H, ∃ C : ℝ, 0 ≤ C ∧ (∀ i, S i ∈ F i) ∧
    (∀ i, ‖S i‖ ≤ C) ∧ ∀ x, Tendsto (fun i => S i x) l (𝓝 (T x))

variable (F : ι → Subalgebra ℂ (H →L[ℂ] H)) (l : Filter ι)

theorem StronglyApproximable.constant {T : H →L[ℂ] H} (hT : ∀ i, T ∈ F i) :
    StronglyApproximable F l T :=
  ⟨fun _ => T, ‖T‖, norm_nonneg _, hT, fun _ => le_rfl, fun _ => tendsto_const_nhds⟩

theorem StronglyApproximable.add {T U : H →L[ℂ] H}
    (hT : StronglyApproximable F l T) (hU : StronglyApproximable F l U) :
    StronglyApproximable F l (T + U) := by
  rcases hT with ⟨S, C, hC, hSF, hS, hlimS⟩
  rcases hU with ⟨R, D, hD, hRF, hR, hlimR⟩
  exact ⟨fun i => S i + R i, C+D, add_nonneg hC hD,
    fun i => (F i).add_mem (hSF i) (hRF i),
    fun i => (norm_add_le _ _).trans (add_le_add (hS i) (hR i)),
    fun x => (hlimS x).add (hlimR x)⟩

theorem StronglyApproximable.mul {T U : H →L[ℂ] H}
    (hT : StronglyApproximable F l T) (hU : StronglyApproximable F l U) :
    StronglyApproximable F l (T * U) := by
  rcases hT with ⟨S, C, hC, hSF, hS, hlimS⟩
  rcases hU with ⟨R, D, hD, hRF, hR, hlimR⟩
  exact ⟨fun i => S i * R i, C*D, mul_nonneg hC hD,
    fun i => (F i).mul_mem (hSF i) (hRF i),
    fun i => (norm_mul_le _ _).trans (mul_le_mul (hS i) (hR i) (norm_nonneg _) hC),
    strong_mul_tendsto S R T U C hS hlimS hlimR⟩

def stronglyApproximableAlgebra : Subalgebra ℂ (H →L[ℂ] H) where
  carrier := StronglyApproximable F l
  mul_mem' := StronglyApproximable.mul F l
  add_mem' := StronglyApproximable.add F l
  algebraMap_mem' c := StronglyApproximable.constant F l fun i => (F i).algebraMap_mem c

end

section
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι : Type*} (F : ι → Subalgebra ℂ (H →L[ℂ] H)) (l : Filter ι)

theorem StronglyApproximable.vector_trace (ξ : H)
    (htr : ∀ i a b, a ∈ F i → b ∈ F i → inner ℂ ξ ((a*b) ξ) = inner ℂ ξ ((b*a) ξ))
    [l.NeBot] {T U : H →L[ℂ] H} (hT : StronglyApproximable F l T)
    (hU : StronglyApproximable F l U) :
    inner ℂ ξ ((T*U) ξ) = inner ℂ ξ ((U*T) ξ) := by
  rcases hT with ⟨S, C, _, hSF, hS, hlimS⟩
  rcases hU with ⟨R, D, _, hRF, hR, hlimR⟩
  have hleft := ((innerSL ℂ ξ).continuous.tendsto ((T*U) ξ)).comp
    (strong_mul_tendsto S R T U C hS hlimS hlimR ξ)
  have hright := ((innerSL ℂ ξ).continuous.tendsto ((U*T) ξ)).comp
    (strong_mul_tendsto R S U T D hR hlimR hlimS ξ)
  simp only [Function.comp_def, innerSL_apply_apply] at hleft hright
  apply tendsto_nhds_unique hleft
  have heq : (fun i => inner ℂ ξ ((S i * R i) ξ)) =
      (fun i => inner ℂ ξ ((R i * S i) ξ)) := by
    funext i
    exact htr i (S i) (R i) (hSF i) (hRF i)
  rw [heq]
  exact hright

end

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B]

theorem continuous_trace_closure (φ : B →L[ℂ] ℂ) (s : Set B)
    (h : ∀ a ∈ s, ∀ b ∈ s, φ (a*b) = φ (b*a))
    {a b : B} (ha : a ∈ closure s) (hb : b ∈ closure s) :
    φ (a*b) = φ (b*a) := by
  have hleft (b : B) (hb : b ∈ s) : ∀ a ∈ closure s, φ (a*b) = φ (b*a) := by
    apply closure_minimal (fun a ha => h a ha b hb)
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have hright : closure s ⊆ {b | φ (a*b) = φ (b*a)} := by
    apply closure_minimal (fun b hb => hleft b hb a ha)
    exact isClosed_eq (by fun_prop) (by fun_prop)
  exact hright hb

open Filter Topology
open scoped lp
variable {J V : Type*} [DecidableEq V]

def l2RootTruncation (root : J → V) (s : Finset V) : ℓ²(J, ℂ) →L[ℂ] ℓ²(J, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun j => if root j ∈ s then x j else 0,
        (lp.memℓp x).mono' (by intro j; split_ifs <;> simp_all)⟩
      map_add' := by
        intro x y
        ext j
        change (if root j ∈ s then x j + y j else 0) =
          (if root j ∈ s then x j else 0) + (if root j ∈ s then y j else 0)
        split_ifs <;> simp
      map_smul' := by
        intro c x
        ext j
        change (if root j ∈ s then c • x j else 0) = c • (if root j ∈ s then x j else 0)
        split_ifs <;> simp }
    1 (by
      intro x
      rw [one_mul]
      apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      intro j
      change ‖if root j ∈ s then x j else 0‖ ≤ ‖x j‖
      split_ifs <;> simp)

@[simp] theorem l2RootTruncation_apply (root : J → V) (s : Finset V)
    (x : ℓ²(J, ℂ)) (j : J) :
    l2RootTruncation root s x j = if root j ∈ s then x j else 0 := rfl

theorem l2RootTruncation_norm (root : J → V) (s : Finset V) :
    ‖l2RootTruncation root s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [one_mul]
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro j
  rw [l2RootTruncation_apply]
  split_ifs <;> simp

theorem l2RootTruncation_complement_norm (root : J → V) (s : Finset V) :
    ‖(1 : ℓ²(J, ℂ) →L[ℂ] ℓ²(J, ℂ)) - l2RootTruncation root s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [one_mul]
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro j
  change ‖x j - l2RootTruncation root s x j‖ ≤ ‖x j‖
  rw [l2RootTruncation_apply]
  split_ifs <;> simp

variable [DecidableEq J]

theorem l2RootTruncation_single (root : J → V) (s : Finset V) (j : J) (z : ℂ) :
    l2RootTruncation root s (lp.single 2 j z) =
      if root j ∈ s then lp.single 2 j z else 0 := by
  ext k
  by_cases hk : j = k
  · subst k
    by_cases hs : root j ∈ s <;> simp [hs]
  · by_cases hs : root j ∈ s <;> simp [hs, lp.single_apply, Ne.symm hk]

theorem l2RootTruncation_strong (root : J → V) (x : ℓ²(J, ℂ)) :
    Tendsto (fun s : Finset V => l2RootTruncation root s x) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlim := lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x
  have hlim' : Tendsto (fun t : Finset J => ∑ j ∈ t, lp.single 2 j (x j)) atTop (𝓝 x) := hlim
  obtain ⟨t, ht⟩ := Metric.tendsto_atTop.mp hlim' ε hε
  refine ⟨t.image root, ?_⟩
  intro s hs
  let y : ℓ²(J, ℂ) := ∑ j ∈ t, lp.single 2 j (x j)
  have hsy : l2RootTruncation root s y = y := by
    dsimp [y]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [l2RootTruncation_single, ite_eq_left (hs (Finset.mem_image_of_mem root hj))]
  have hid : (l2RootTruncation root s x - x) =
      -(((1 : ℓ²(J, ℂ) →L[ℂ] ℓ²(J, ℂ)) - l2RootTruncation root s) (x-y)) := by
    simp only [sub_apply, one_apply_eq_self, map_sub, hsy]
    abel
  rw [dist_eq_norm, hid, norm_neg]
  have hb := ((1 : ℓ²(J, ℂ) →L[ℂ] ℓ²(J, ℂ)) - l2RootTruncation root s).le_opNorm (x-y)
  have hh := l2RootTruncation_complement_norm root s
  calc
    _ ≤ ‖(1 : ℓ²(J, ℂ) →L[ℂ] ℓ²(J, ℂ)) - l2RootTruncation root s‖ * ‖x-y‖ := hb
    _ ≤ 1 * ‖x-y‖ := mul_le_mul_of_nonneg_right hh (norm_nonneg _)
    _ < ε := by simpa only [one_mul, ← dist_eq_norm, dist_comm] using ht t le_rfl

section
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I]

abbrev AtomicOperators := AtomicHilbertSpace d →L[ℂ] AtomicHilbertSpace d

def atomicFactor (i : I) : NonUnitalSubalgebra ℂ (AtomicOperators d) :=
  NonUnitalAlgHom.range (atomicLeft d i).toAlgHom.toNonUnitalAlgHom

def atomicCommonAtom (k : I) (r : V) : AtomicOperators d :=
  atomicLeft d k ((d k).atom r).1

def atomicState (k : I) : AtomicOperators d →ₗ[ℂ] ℂ :=
  (operatorVectorFunctional (atomicVacuum d k)).toLinearMap

omit [DecidableEq I] in
@[simp] theorem atomicState_apply (k : I) (T : AtomicOperators d) :
    atomicState d k T = inner ℂ (atomicVacuum d k) (T (atomicVacuum d k)) := rfl

theorem atomicCommonAtom_idempotent (k : I) (r : V) :
    atomicCommonAtom d k r * atomicCommonAtom d k r = atomicCommonAtom d k r := by
  rw [atomicCommonAtom, ← map_mul, ((d k).atom r).property.isIdempotentElem.eq]

theorem atomicCommonAtom_orthogonal (k : I) (r t : V) (h : r ≠ t) :
    atomicCommonAtom d k r * atomicCommonAtom d k t = 0 := by
  rw [atomicCommonAtom, atomicCommonAtom, ← map_mul, (d k).orthogonal r t h, map_zero]

theorem atomicCommonAtom_star (k : I) (r : V) :
    star (atomicCommonAtom d k r) = atomicCommonAtom d k r := by
  rw [atomicCommonAtom, ← map_star, ((d k).atom r).property.isSelfAdjoint.star_eq]

theorem atomicCommonAtom_mem [DecidableEq V] (k i : I) (r : V) :
    atomicCommonAtom d k r ∈ atomicFactor d i := by
  exact ⟨((d i).atom r).1, atomicLeft_atoms d i k r⟩

theorem atomicCommonAtom_state_ne (k : I) (r : V) :
    atomicState d k (atomicCommonAtom d k r) ≠ 0 := by
  rw [atomicState_apply, atomicCommonAtom, atomicLeft_vacuum_trace d k k (fun _ => rfl)]
  intro h
  have hh := (d k).positive r
  rw [h, Complex.zero_re] at hh
  exact (lt_irrefl 0) hh

theorem atomicFactor_star (i : I) (a : AtomicOperators d) (ha : a ∈ atomicFactor d i) :
    star a ∈ atomicFactor d i := by
  change ∃ b, atomicLeft d i b = a at ha
  rcases ha with ⟨a,rfl⟩
  change ∃ b, atomicLeft d i b = star (atomicLeft d i a)
  exact ⟨star a, map_star _ _⟩

variable (k : I) (hw : ∀ i r, ((d k).trace ((d k).atom r).1).re =
    ((d i).trace ((d i).atom r).1).re)
include hw

theorem atomicFactor_trace (i : I) (a b : AtomicOperators d)
    (ha : a ∈ atomicFactor d i) (hb : b ∈ atomicFactor d i) :
    atomicState d k (a*b) = atomicState d k (b*a) := by
  change ∃ a', atomicLeft d i a' = a at ha
  change ∃ b', atomicLeft d i b' = b at hb
  rcases ha with ⟨a,rfl⟩
  rcases hb with ⟨b,rfl⟩
  simp only [← map_mul, atomicState_apply, atomicLeft_vacuum_trace d k i (hw i)]
  exact (d i).tracial a b

variable [DecidableEq V]

theorem atomicCentered_starts (i : I) (T : AtomicOperators d)
    (hT : T ∈ atomicCenteredSubmodule (atomicCommonAtom d k) (atomicState d k)
      (atomicFactor d i)) (x : AtomicHilbertSpace d)
    (hx : FockAway (AtomicLetters d) i x) :
    FockStarts (AtomicLetters d) i (T x) := by
  rw [mem_atomicCenteredSubmodule] at hT
  rcases hT with ⟨hT, ha⟩
  change ∃ a, atomicLeft d i a = T at hT
  rcases hT with ⟨a, rfl⟩
  apply atomicLeft_centered d i a _ x hx
  intro r
  have hh := ha r
  simp only [atomicCommonAtom, ← atomicLeft_atoms d i k r, ← map_mul,
    atomicState_apply, atomicLeft_vacuum_trace d k i (hw i)] at hh
  exact hh

theorem atomicCenteredWord_starts (x : I × AtomicOperators d)
    (w : List (I × AtomicOperators d))
    (h : IsCenteredWord (fun i => atomicCenteredSubmodule (atomicCommonAtom d k)
      (atomicState d k) (atomicFactor d i)) (x :: w)) :
    FockStarts (AtomicLetters d) x.1 (wordValue (x :: w) (atomicVacuum d k)) := by
  induction w generalizing x with
  | nil =>
    simp only [wordValue_cons, wordValue_nil, mul_one]
    exact atomicCentered_starts d k hw x.1 x.2 h.head _
      (fockVacuum_away (AtomicLetters d) _ x.1)
  | cons y w ih =>
    rw [wordValue_cons, mul_apply_eq_comp]
    apply atomicCentered_starts d k hw x.1 x.2 h.head
    apply fockStarts_away (AtomicLetters d) _ _ (ih y h.tail)
    exact (List.isChain_cons_cons.mp h.alternating).1.symm

theorem atomicCenteredWord_zero (w : List (I × AtomicOperators d))
    (h : IsCenteredWord (fun i => atomicCenteredSubmodule (atomicCommonAtom d k)
      (atomicState d k) (atomicFactor d i)) w) (hn : w ≠ []) :
    atomicState d k (wordValue w) = 0 := by
  cases w with
  | nil => exact (hn rfl).elim
  | cons x w =>
    exact fockVacuum_inner_starts (AtomicLetters d) _ x.1 _
      (atomicCenteredWord_starts d k hw x w h)

theorem atomicFiniteCorner_trace (s : Finset V) {a b : AtomicOperators d}
    (ha : a ∈ Algebra.adjoin ℂ (⋃ i, (finiteFactorCorner (atomicCommonAtom d k)
      (atomicFactor d i) s : Set (AtomicOperators d))))
    (hb : b ∈ Algebra.adjoin ℂ (⋃ i, (finiteFactorCorner (atomicCommonAtom d k)
      (atomicFactor d i) s : Set (AtomicOperators d)))) :
    atomicState d k (a*b) = atomicState d k (b*a) := by
  exact finiteCorner_adjoin_trace (atomicCommonAtom d k)
    (atomicCommonAtom_idempotent d k) (atomicCommonAtom_orthogonal d k)
    (atomicState d k) (atomicCommonAtom_state_ne d k)
    (atomicFactor d) (atomicCommonAtom_mem d k) (atomicCommonAtom_star d k)
    (operatorVectorFunctional_star (atomicVacuum d k)) (atomicFactor_star d)
    (atomicFactor_trace d k hw) (atomicCenteredWord_zero d k hw) s ha hb

end

section
open Filter Topology
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I] [DecidableEq V]

theorem atomicCommonAtom_apply (k : I) (r : V) (x : AtomicHilbertSpace d)
    (j : FockIndex (AtomicLetters d)) :
    atomicCommonAtom d k r x j = if r = j.2.1 then x j else 0 := by
  apply atomicFockRepresentation_diagonal (AtomicLetters d) (atomicColumnReps d)
    (fun i r => ((d i).atom r).1)
  intro i r l x c
  have hv : fockColumnVertex (AtomicLetters d) i r c = columnVertex r c := by
    cases c <;> rfl
  simpa only [atomicColumnReps, hv] using indexedColumnRepresentation_atom
    (d i).trace (d i).tracial (d i).atom (d i).orthogonal (d i).mass (d i).positive r l x c

theorem atomicCommonAtom_sum (k : I) (s : Finset V) :
    (∑ r ∈ s, atomicCommonAtom d k r) =
      l2RootTruncation (fun j : FockIndex (AtomicLetters d) => j.2.1) s := by
  ext x j
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply, atomicCommonAtom_apply,
    l2RootTruncation_apply]
  exact Finset.sum_ite_eq' s j.2.1 (fun _ => x j)

def atomicFiniteAlgebra (k : I) (s : Finset V) : Subalgebra ℂ (AtomicOperators d) :=
  Algebra.adjoin ℂ (⋃ i, (finiteFactorCorner (atomicCommonAtom d k)
    (atomicFactor d i) s : Set (AtomicOperators d)))

theorem atomicFactor_stronglyApproximable (k i : I) (T : AtomicOperators d)
    (hT : T ∈ atomicFactor d i) :
    StronglyApproximable (atomicFiniteAlgebra d k) atTop T := by
  let P : Finset V → AtomicOperators d := fun s => ∑ r ∈ s, atomicCommonAtom d k r
  have hPF (s : Finset V) : P s ∈ atomicFactor d i :=
    (atomicFactor d i).sum_mem (fun r _ => atomicCommonAtom_mem d k i r)
  have hPP (s : Finset V) : P s * P s = P s := by
    change (∑ r ∈ s, atomicCommonAtom d k r) * _ = _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    exact (atom_mul_sum (atomicCommonAtom d k) (atomicCommonAtom_idempotent d k)
      (atomicCommonAtom_orthogonal d k) s r).trans (ite_eq_left hr)
  have hPn (s : Finset V) : ‖P s‖ ≤ 1 := by
    dsimp [P]
    rw [atomicCommonAtom_sum]
    exact l2RootTruncation_norm _ s
  have hPlim (x : AtomicHilbertSpace d) :
      Tendsto (fun s => P s x) atTop (𝓝 x) := by
    simpa only [P, atomicCommonAtom_sum] using
      l2RootTruncation_strong (fun j : FockIndex (AtomicLetters d) => j.2.1) x
  refine ⟨fun s => P s * T * P s, ‖T‖, norm_nonneg _, ?_, ?_, ?_⟩
  · intro s
    apply Algebra.subset_adjoin
    apply Set.mem_iUnion.mpr
    refine ⟨i, (atomicFactor d i).mul_mem ((atomicFactor d i).mul_mem (hPF s) hT) (hPF s), ?_⟩
    constructor
    · change P s * (P s * T * P s) = _
      rw [← mul_assoc, ← mul_assoc, hPP]
    · change (P s * T * P s) * P s = _
      rw [mul_assoc (P s * T), hPP]
  · intro s
    calc
      ‖P s * T * P s‖ ≤ (‖P s‖ * ‖T‖) * ‖P s‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1 * ‖T‖) * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_right (hPn s) (norm_nonneg _)) (hPn s)
        (norm_nonneg _) (by positivity)
      _ = ‖T‖ := by simp
  · intro x
    have hh := strong_apply_tendsto P (1 : AtomicOperators d) 1 hPn hPlim
      ((T.continuous.tendsto x).comp (hPlim x))
    exact hh

def atomicAlgebra : Subalgebra ℂ (AtomicOperators d) :=
  Algebra.adjoin ℂ (⋃ i, (atomicFactor d i : Set (AtomicOperators d)))

theorem atomicAlgebra_stronglyApproximable (k : I) {T : AtomicOperators d}
    (hT : T ∈ atomicAlgebra d) :
    StronglyApproximable (atomicFiniteAlgebra d k) atTop T := by
  have hh : atomicAlgebra d ≤ stronglyApproximableAlgebra (atomicFiniteAlgebra d k) atTop := by
    apply Algebra.adjoin_le
    rintro T hT
    rcases Set.mem_iUnion.mp hT with ⟨i,hi⟩
    exact atomicFactor_stronglyApproximable d k i T hi
  exact hh hT

theorem atomicAlgebra_trace (k : I)
    (hw : ∀ i r, ((d k).trace ((d k).atom r).1).re = ((d i).trace ((d i).atom r).1).re)
    {a b : AtomicOperators d} (ha : a ∈ atomicAlgebra d) (hb : b ∈ atomicAlgebra d) :
    atomicState d k (a*b) = atomicState d k (b*a) := by
  exact StronglyApproximable.vector_trace (atomicFiniteAlgebra d k) atTop (atomicVacuum d k)
    (fun s a b ha hb => atomicFiniteCorner_trace d k hw s ha hb)
    (atomicAlgebra_stronglyApproximable d k ha) (atomicAlgebra_stronglyApproximable d k hb)

end

section
open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

def fockColumnIndexEmbedding (i : I) (t : FockTail L i) :
    ColumnIndex L i t.1.2.1 ↪ FockIndex L where
  toFun c := fockJoin L i ⟨t,c⟩
  inj' c e h := by
    have hh := (fockBlockEquiv L i).injective h
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hh

theorem fockColumnIndexEmbedding_ne {i : I} (t u : FockTail L i) (hu : u ≠ t)
    (c : ColumnIndex L i u.1.2.1) :
    fockJoin L i ⟨u,c⟩ ∉ Set.range (fockColumnIndexEmbedding L i t) := by
  rintro ⟨e, he⟩
  exact hu (congrArg Sigma.fst ((fockBlockEquiv L i).injective he)).symm

theorem fock_single_away (i : I) (t : FockTail L i) :
    FockAway L i (lp.single 2 t.1 1) := by
  classical
  intro j hj
  have hne : j ≠ t.1 := by
    rintro rfl
    exact t.2 hj
  simp [lp.single_apply, hne]

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]
variable (π : ∀ i r, A i →⋆ₐ[ℂ]
  (ℓ²(ColumnIndex L i r, ℂ) →L[ℂ] ℓ²(ColumnIndex L i r, ℂ)))

theorem fockColumn_action (i : I) (t : FockTail L i) (a : A i) :
    atomicFockRepresentation L π i a (lp.single 2 t.1 1) =
      l2Embed (fockColumnIndexEmbedding L i t) (π i t.1.2.1 a (lp.single 2 none 1)) := by
  classical
  ext j
  obtain ⟨⟨u,c⟩, rfl⟩ := (fockBlockEquiv L i).surjective j
  change atomicFockRepresentation L π i a (lp.single 2 t.1 1)
    (fockJoin L i ⟨u,c⟩) =
      l2Embed (fockColumnIndexEmbedding L i t)
        (π i t.1.2.1 a (lp.single 2 none 1)) (fockJoin L i ⟨u,c⟩)
  rw [atomicFock_creation L π i a _ (fock_single_away L i t) u c]
  by_cases hu : u = t
  · subst u
    change _ = l2Embed (fockColumnIndexEmbedding L i t) _
      (fockColumnIndexEmbedding L i t c)
    rw [l2Embed_apply]
    simp
  · rw [l2Embed_apply_of_not_mem _ _ _ (fockColumnIndexEmbedding_ne L t u hu c)]
    have hne : u.1 ≠ t.1 := fun h => hu (Subtype.ext h)
    simp [lp.single_apply, hne]

theorem fock_cyclic_total
    (hcol : ∀ i r, DenseRange (fun a : A i => π i r a (lp.single 2 none 1)))
    (C : Submodule ℂ (AtomicFockSpace L)) (hC : IsClosed (C : Set (AtomicFockSpace L)))
    (hinv : ∀ i (a : A i) x, x ∈ C → atomicFockRepresentation L π i a x ∈ C)
    (hvac : ∀ r, lp.single 2 (fockVacuumIndex L r) 1 ∈ C) : C = ⊤ := by
  classical
  have hblock (i : I) (t : FockTail L i) (ht : lp.single 2 t.1 1 ∈ C)
      (z : ℓ²(ColumnIndex L i t.1.2.1, ℂ)) :
      l2Embed (fockColumnIndexEmbedding L i t) z ∈ C := by
    refine (hcol i t.1.2.1).induction_on
      (p := fun z => l2Embed (fockColumnIndexEmbedding L i t) z ∈ C) z ?_ ?_
    · exact hC.preimage (l2Embed (fockColumnIndexEmbedding L i t)).continuous
    intro a
    rw [← fockColumn_action L π i t a]
    exact hinv i a _ ht
  have hsingle (j : FockIndex L) : lp.single 2 j 1 ∈ C := by
    rcases j with ⟨i,l,p⟩
    induction p with
    | nil r => exact hvac r
    | cons i l r a j p hn ih =>
      let t : FockTail L i := ⟨⟨j,r,p⟩, hn.symm⟩
      have hh := hblock i t ih (lp.single 2 (some ⟨l,a⟩) 1)
      rw [l2Embed_single] at hh
      exact hh
  apply top_unique
  rw [← (l2Basis (FockIndex L)).dense_span]
  have hh : Submodule.span ℂ (Set.range (l2Basis (FockIndex L))) ≤ C := by
    apply Submodule.span_le.mpr
    rintro x ⟨j,rfl⟩
    rw [l2Basis_apply]
    exact hsingle j
  exact (Submodule.topologicalClosure_mono hh).trans_eq hC.submodule_topologicalClosure_eq

end

section
open Filter Topology
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I]

omit [DecidableEq I] in

theorem atomicColumnReps_cyclic (i : I) (r : V) :
    DenseRange (fun a : A i => atomicColumnReps d i r a (lp.single 2 none 1)) := by
  let b := tracialColumnBasis (d i).trace (d i).tracial (d i).atom
    (d i).orthogonal (d i).mass (d i).positive r
  have hd := b.repr.surjective.denseRange.comp
    (traceColumn_unit_cyclic (d i).trace (d i).tracial ((d i).atom r) ((d i).positive r))
    b.repr.continuous
  have functions_eq : (fun a : A i => atomicColumnReps d i r a (lp.single 2 none 1)) =
      fun a => b.repr (traceColumnRepresentation (d i).trace (d i).tracial
        ((d i).atom r) a (columnUnit (d i).trace (d i).tracial ((d i).atom r))) :=
    funext (indexedColumnRepresentation_vacuum_vector (d i).trace (d i).tracial
      (d i).atom (d i).orthogonal (d i).mass (d i).positive r)
  rw [functions_eq]
  exact hd

theorem atomicCommonAtom_vacuum (k : I) (r : V) :
    atomicCommonAtom d k r (atomicVacuum d k) =
      (Real.sqrt (((d k).trace ((d k).atom r).1).re) : ℂ) •
        lp.single 2 (fockVacuumIndex (AtomicLetters d) r) 1 := by
  classical
  ext j
  rw [atomicCommonAtom_apply]
  rcases j with ⟨i,l,p⟩
  cases p with
  | nil l =>
    simp only [atomicVacuum, fockVacuum_apply_nil, atomicWeightVector_apply,
      lp.coeFn_smul, Pi.smul_apply, lp.single_apply]
    by_cases h : r = l
    · subst l
      change _ = (Real.sqrt (((d k).trace ((d k).atom r).1).re) : ℂ) *
        (Pi.single (fockVacuumIndex (AtomicLetters d) r) (1 : ℂ) :
          FockIndex (AtomicLetters d) → ℂ) (fockVacuumIndex (AtomicLetters d) r)
      rw [Pi.single_eq_same, mul_one, ite_eq_left rfl]
    · have hn : (⟨none,l,ReducedPath.nil l⟩ : FockIndex (AtomicLetters d)) ≠
          fockVacuumIndex (AtomicLetters d) r := by
        intro he
        exact h (congrArg (fun j : FockIndex (AtomicLetters d) => j.2.1) he).symm
      simp only [ite_eq_right h, Pi.single_eq_of_ne hn, smul_zero]
  | cons i l t a j p hn =>
    have hz : atomicVacuum d k ⟨some i,l,.cons i l t a j p hn⟩ = 0 :=
      fockVacuum_away (AtomicLetters d) _ i _ rfl
    have hne : (⟨some i,l,ReducedPath.cons i l t a j p hn⟩ : FockIndex (AtomicLetters d)) ≠
        fockVacuumIndex (AtomicLetters d) r := by
      intro h
      have hh := congrArg (fun j : FockIndex (AtomicLetters d) => j.1) h
      cases hh
    simp only [hz, ite_self, lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_eq_of_ne hne, smul_zero]

theorem atomicLeft_mem_algebra (i : I) (a : A i) : atomicLeft d i a ∈ atomicAlgebra d :=
  Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, a, rfl⟩)

def atomicEval (k : I) : atomicAlgebra d →ₗ[ℂ] AtomicHilbertSpace d where
  toFun T := (T : AtomicOperators d) (atomicVacuum d k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem atomicAlgebra_cyclic (k : I) : DenseRange (atomicEval d k) := by
  let M := LinearMap.range (atomicEval d k)
  let C := M.topologicalClosure
  have hclosed : IsClosed (C : Set (AtomicHilbertSpace d)) := isClosed_closure
  have hinv (i : I) (a : A i) (x : AtomicHilbertSpace d) (hx : x ∈ C) :
      atomicLeft d i a x ∈ C := by
    apply map_mem_closure (atomicLeft d i a).continuous hx
    rintro y ⟨T,rfl⟩
    exact ⟨⟨atomicLeft d i a * T.1,
      (atomicAlgebra d).mul_mem (atomicLeft_mem_algebra d i a) T.2⟩, rfl⟩
  have hvac (r : V) : lp.single 2 (fockVacuumIndex (AtomicLetters d) r) 1 ∈ C := by
    have he : atomicCommonAtom d k r (atomicVacuum d k) ∈ M :=
      ⟨⟨atomicCommonAtom d k r, atomicLeft_mem_algebra d k ((d k).atom r).1⟩, rfl⟩
    rw [atomicCommonAtom_vacuum] at he
    have hn : (Real.sqrt (((d k).trace ((d k).atom r).1).re) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ((d k).positive r)).ne'
    exact M.le_topologicalClosure ((M.smul_mem_iff (s :=
      (Real.sqrt (((d k).trace ((d k).atom r).1).re) : ℂ)) hn).mp he)
  have htotal : C = ⊤ := fock_cyclic_total (AtomicLetters d) (atomicColumnReps d)
    (atomicColumnReps_cyclic d) C hclosed hinv hvac
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr htotal

def atomicStarAlgebra : StarSubalgebra ℂ (AtomicOperators d) where
  toSubalgebra := atomicAlgebra d
  star_mem' := by
    intro T hT
    change star T ∈ atomicAlgebra d
    induction hT using Algebra.adjoin_induction with
    | mem T hT =>
      rcases Set.mem_iUnion.mp hT with ⟨i,hi⟩
      exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i,atomicFactor_star d i T hi⟩)
    | algebraMap c =>
      simpa only [Algebra.algebraMap_eq_smul_one, star_smul, star_one] using
        (atomicAlgebra d).algebraMap_mem (star c)
    | add T U _ _ hT hU =>
      rw [star_add]
      exact (atomicAlgebra d).add_mem hT hU
    | mul T U _ _ hT hU =>
      rw [star_mul]
      exact (atomicAlgebra d).mul_mem hU hT

def atomicCStarAlgebra : StarSubalgebra ℂ (AtomicOperators d) :=
  (atomicStarAlgebra d).topologicalClosure

instance : IsClosed (atomicCStarAlgebra d : Set (AtomicOperators d)) := isClosed_closure

abbrev AtomicCStar := atomicCStarAlgebra d

def atomicEmbedding (i : I) : A i →⋆ₐ[ℂ] AtomicCStar d :=
  (atomicLeft d i).codRestrict (atomicCStarAlgebra d) fun a =>
    subset_closure (atomicLeft_mem_algebra d i a)

theorem atomicEmbedding_injective (i : I) : Function.Injective (atomicEmbedding d i) := by
  intro a b h
  exact atomicLeft_injective d i (congrArg Subtype.val h)

theorem atomicCStar_trace (k : I)
    (hw : ∀ i r, ((d k).trace ((d k).atom r).1).re = ((d i).trace ((d i).atom r).1).re)
    (a b : AtomicCStar d) :
    operatorVectorFunctional (atomicVacuum d k) ((a : AtomicOperators d)*b) =
      operatorVectorFunctional (atomicVacuum d k) ((b : AtomicOperators d)*a) := by
  exact continuous_trace_closure (operatorVectorFunctional (atomicVacuum d k)) (atomicAlgebra d)
    (fun a ha b hb => atomicAlgebra_trace d k hw ha hb) a.2 b.2

theorem atomicCStar_cyclic (k : I) :
    DenseRange (fun T : AtomicCStar d => (T : AtomicOperators d) (atomicVacuum d k)) := by
  apply (atomicAlgebra_cyclic d k).mono
  rintro x ⟨T,rfl⟩
  exact ⟨⟨T.1,subset_closure T.2⟩,rfl⟩

theorem atomicCStar_faithful (k : I)
    (hw : ∀ i r, ((d k).trace ((d k).atom r).1).re = ((d i).trace ((d i).atom r).1).re)
    (a : AtomicCStar d)
    (ha : operatorVectorFunctional (atomicVacuum d k) (star (a : AtomicOperators d)*a) = 0) : a = 0 :=
  operatorVectorFunctional_faithful (atomicCStarAlgebra d) (atomicVacuum d k)
    (atomicCStar_cyclic d k) (atomicCStar_trace d k hw) a ha

end

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def operatorCompression (M : Submodule ℂ H) [CompleteSpace M] :
    (H →L[ℂ] H) →L[ℂ] (M →L[ℂ] M) where
  toFun T := M.orthogonalProjectionOnto.comp (T.comp M.subtypeL)
  map_add' := by intros; ext x; simp
  map_smul' := by intros; ext x; simp
  cont := by fun_prop

@[simp] theorem operatorCompression_apply (M : Submodule ℂ H) [CompleteSpace M]
    (T : H →L[ℂ] H) (x : M) :
    operatorCompression M T x = M.orthogonalProjectionOnto (T (x : H)) := rfl

theorem operatorCompression_norm_le (M : Submodule ℂ H) [CompleteSpace M]
    (T : H →L[ℂ] H) : ‖operatorCompression M T‖ ≤ ‖T‖ := by
  apply (operatorCompression M T).opNorm_le_bound (norm_nonneg T)
  intro x
  exact (M.norm_orthogonalProjectionOnto_apply_le _).trans (T.le_opNorm (x : H))

@[simp] theorem operatorCompression_one (M : Submodule ℂ H) [CompleteSpace M] :
    operatorCompression M 1 = 1 := by
  ext x
  simp

theorem operatorCompression_inner (M : Submodule ℂ H) [CompleteSpace M]
    (T : H →L[ℂ] H) (x y : M) :
    inner ℂ x (operatorCompression M T y) = inner ℂ (x : H) (T (y : H)) :=
  M.inner_orthogonalProjectionOnto_eq_of_mem_left x _

theorem operatorCompression_zero_of_dense {J : Type*}
    (M : Submodule ℂ H) [CompleteSpace M] (v : J → M) (hv : DenseRange v)
    (T : H →L[ℂ] H)
    (hT : ∀ i j, inner ℂ (v i : H) (T (v j : H)) = 0) :
    operatorCompression M T = 0 := by
  apply ContinuousLinearMap.ext
  intro y
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  have hleft (i : J) : inner ℂ (v i) (operatorCompression M T y) = 0 := by
    refine hv.induction_on (p := fun z : M => inner ℂ (v i) (operatorCompression M T z) = 0)
      y (isClosed_eq (by fun_prop) continuous_const) ?_
    intro j
    rw [operatorCompression_inner]
    exact hT i j
  exact hv.induction_on (p := fun z : M => inner ℂ z (operatorCompression M T y) = 0)
    (operatorCompression M T y) (isClosed_eq (by fun_prop) continuous_const) hleft

variable [CompleteSpace H]

@[simp] theorem operatorCompression_star (M : Submodule ℂ H) [CompleteSpace M]
    (T : H →L[ℂ] H) : operatorCompression M (star T) = star (operatorCompression M T) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  rw [← inner_conj_symm, operatorCompression_inner]
  change star (inner ℂ (y : H) (T.adjoint (x : H))) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change (starRingEnd ℂ) (inner ℂ (T (y : H)) (x : H)) = _
  rw [inner_conj_symm, operatorCompression_inner]

variable {A : Type*} [CStarAlgebra A]

theorem faithfulRepresentation_range_closed (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hπ : Function.Injective π) : IsClosed (Set.range π) :=
  (NonUnitalStarAlgHom.isometry π hπ).isClosedEmbedding.isClosed_range

def representationInverse (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hπ : Function.Injective π) :
    π.range →L[ℂ] A :=
  (StarAlgEquiv.ofInjective π hπ).symm.toAlgEquiv.toLinearMap.mkContinuous 1 (by
    intro x
    rw [one_mul]
    exact le_of_eq (by
      have he : π ((StarAlgEquiv.ofInjective π hπ).symm x) = x :=
        congrArg Subtype.val ((StarAlgEquiv.ofInjective π hπ).apply_symm_apply x)
      rw [← NonUnitalStarAlgHom.norm_map π hπ]
      change ‖π ((StarAlgEquiv.ofInjective π hπ).symm x)‖ = ‖(x : H →L[ℂ] H)‖
      rw [he]))

@[simp] theorem representationInverse_apply_map (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hπ : Function.Injective π) (x : A) :
    representationInverse π hπ ⟨π x, ⟨x,rfl⟩⟩ = x :=
  (StarAlgEquiv.ofInjective π hπ).symm_apply_apply x

@[simp] theorem representation_map_inverse (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hπ : Function.Injective π) (x : π.range) :
    π (representationInverse π hπ x) = x :=
  congrArg Subtype.val ((StarAlgEquiv.ofInjective π hπ).apply_symm_apply x)

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : Type*} [CStarAlgebra A]

def cyclicOrbitLinear (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : A →ₗ[ℂ] H where
  toFun a := π a ξ
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def cyclicSpan (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : Submodule ℂ H :=
  (cyclicOrbitLinear π ξ).range.topologicalClosure

instance cyclicSpanComplete (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    CompleteSpace (cyclicSpan π ξ) := isClosed_closure.completeSpace_coe

theorem cyclicSpan_invariant (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (a : A) (x : H) (hx : x ∈ cyclicSpan π ξ) : π a x ∈ cyclicSpan π ξ := by
  apply map_mem_closure (π a).continuous hx
  rintro y ⟨b,rfl⟩
  refine ⟨a*b, ?_⟩
  simp [cyclicOrbitLinear, map_mul]

theorem cyclicSpan_vector_mem (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : ξ ∈ cyclicSpan π ξ := by
  apply subset_closure
  refine ⟨1, ?_⟩
  simp [cyclicOrbitLinear]

def cyclicOrbit (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (a : A) : cyclicSpan π ξ :=
  ⟨π a ξ, subset_closure ⟨a,rfl⟩⟩

theorem cyclicOrbit_dense (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    DenseRange (cyclicOrbit π ξ) := by
  have h := ((denseRange_inclusion_iff (subset_closure
    (s := Set.range (fun a : A => π a ξ)))).2 Set.Subset.rfl).comp
    Set.rangeFactorization_surjective.denseRange (continuous_inclusion subset_closure)
  exact h

def cyclicRepresentation (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    A →⋆ₐ[ℂ] ((cyclicSpan π ξ) →L[ℂ] (cyclicSpan π ξ)) :=
  restrictRepresentation π (cyclicSpan π ξ) (cyclicSpan_invariant π ξ)

@[simp] theorem cyclicRepresentation_apply (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (a : A) (x : cyclicSpan π ξ) : (cyclicRepresentation π ξ a x : H) = π a (x : H) := rfl

theorem cyclicRepresentation_injective (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hsep : ∀ a : A, π a ξ = 0 → a = 0) : Function.Injective (cyclicRepresentation π ξ) := by
  intro a b h
  apply sub_eq_zero.mp
  apply hsep
  have he := congrArg (fun T => (T ⟨ξ, cyclicSpan_vector_mem π ξ⟩ : H)) h
  simpa only [cyclicRepresentation_apply, map_sub, sub_apply,
    sub_eq_zero] using he

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def restrictedVectorFunctional (B : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) :
    B →L[ℂ] ℂ where
  toFun b := operatorVectorFunctional ξ b
  map_add' _ _ := (operatorVectorFunctional ξ).map_add _ _
  map_smul' _ _ := (operatorVectorFunctional ξ).map_smul _ _
  cont := (operatorVectorFunctional ξ).continuous.comp continuous_subtype_val

@[simp] theorem restrictedVectorFunctional_apply (B : StarSubalgebra ℂ (H →L[ℂ] H))
    (ξ : H) (b : B) : restrictedVectorFunctional B ξ b = operatorVectorFunctional ξ b := rfl

@[simp] theorem restrictedVectorFunctional_norm (B : StarSubalgebra ℂ (H →L[ℂ] H))
    (ξ : H) (hξ : ‖ξ‖ = 1) : ‖restrictedVectorFunctional B ξ‖ = 1 := by
  apply le_antisymm
  · apply (restrictedVectorFunctional B ξ).opNorm_le_bound zero_le_one
    intro b
    change ‖operatorVectorFunctional ξ (b : H →L[ℂ] H)‖ ≤ 1 * ‖(b : H →L[ℂ] H)‖
    simpa only [operatorVectorFunctional_norm ξ hξ]
      using (operatorVectorFunctional ξ).le_opNorm (b : H →L[ℂ] H)
  · have h := (restrictedVectorFunctional B ξ).le_opNorm (1 : B)
    have he : restrictedVectorFunctional B ξ 1 = 1 := by
      simp [inner_self_eq_norm_sq_to_K, hξ]
    rw [he, norm_one] at h
    have hn : ‖(1 : B)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hh := mul_le_mul_of_nonneg_left hn (norm_nonneg (restrictedVectorFunctional B ξ))
    exact h.trans (by simpa using hh)

theorem restrictedVectorFunctional_strict (B : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H)
    (hcyc : DenseRange (fun T : B => (T : H →L[ℂ] H) ξ))
    (htr : ∀ S T : B, operatorVectorFunctional ξ ((S : H →L[ℂ] H)*T) =
      operatorVectorFunctional ξ ((T : H →L[ℂ] H)*S))
    (a : B) (ha : a ≠ 0) : 0 < (restrictedVectorFunctional B ξ (star a*a)).re := by
  have hz : operatorVectorFunctional ξ (star (a : H →L[ℂ] H)*a) ≠ 0 :=
    fun h => ha (operatorVectorFunctional_faithful B ξ hcyc htr a h)
  change 0 < (operatorVectorFunctional ξ (star (a : H →L[ℂ] H)*a)).re
  rw [operatorVectorFunctional_star_mul] at hz ⊢
  simp only [Complex.ofReal_re]
  have hn : ‖(a : H →L[ℂ] H) ξ‖ ^ 2 ≠ 0 := fun h => hz (by rw [h]; rfl)
  exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm hn)

section
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (B : StarSubalgebra ℂ (H →L[ℂ] H))
variable {I : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
variable (ι : ∀ i, A i →⋆ₐ[ℂ] B) (ξ : H)

def ambientFactor (i : I) : A i →⋆ₐ[ℂ] (H →L[ℂ] H) := B.subtype.comp (ι i)

def factorCompression (i : I) :
    B →L[ℂ] ((cyclicSpan (ambientFactor B ι i) ξ) →L[ℂ]
      (cyclicSpan (ambientFactor B ι i) ξ)) where
  toFun b := operatorCompression (cyclicSpan (ambientFactor B ι i) ξ) b
  map_add' _ _ := (operatorCompression _).map_add _ _
  map_smul' _ _ := (operatorCompression _).map_smul _ _
  cont := (operatorCompression _).continuous.comp continuous_subtype_val

@[simp] theorem factorCompression_apply (i : I) (b : B) :
    factorCompression B ι ξ i b =
      operatorCompression (cyclicSpan (ambientFactor B ι i) ξ) b := rfl

@[simp] theorem factorCompression_factor (i : I) (a : A i) :
    factorCompression B ι ξ i (ι i a) = cyclicRepresentation (ambientFactor B ι i) ξ a := by
  ext x
  change ((cyclicSpan (ambientFactor B ι i) ξ).orthogonalProjectionOnto
      ((ambientFactor B ι i a) (x : H)) : H) = _
  rw [Submodule.coe_orthogonalProjectionOnto_apply]
  exact Submodule.starProjection_eq_self_iff.mpr
    (cyclicSpan_invariant (ambientFactor B ι i) ξ a x x.property)

theorem factor_word_coefficient (i : I) (a b : A i) (w : B) :
    inner ℂ ((ambientFactor B ι i a) ξ) ((w : H →L[ℂ] H) ((ambientFactor B ι i b) ξ)) =
      restrictedVectorFunctional B ξ (star (ι i a) * w * ι i b) := by
  change inner ℂ ((ambientFactor B ι i a) ξ)
      ((w : H →L[ℂ] H) ((ambientFactor B ι i b) ξ)) =
    inner ℂ ξ ((((star (ι i a) * w * ι i b : B) : H →L[ℂ] H)) ξ)
  rw [← ContinuousLinearMap.adjoint_inner_right]
  rfl

def factorAlgebra (i : I) : NonUnitalSubalgebra ℂ B :=
  (ι i).range.toSubalgebra.toNonUnitalSubalgebra

variable (D : NonUnitalSubalgebra ℂ B) (K : I → Submodule ℂ B)
variable (h : CenteredDecomposition D (factorAlgebra B ι) K)
variable (hfree : ∀ w, IsCenteredWord K w → w ≠ [] →
  restrictedVectorFunctional B ξ (wordValue w) = 0)
variable (htr : ∀ a b : B, restrictedVectorFunctional B ξ (a*b) =
  restrictedVectorFunctional B ξ (b*a))
include h hfree htr

theorem factorCompression_long_zero (i : I) {w : List (I × B)}
    (hw : IsCenteredWord K w) (hlen : 2 ≤ w.length) :
    factorCompression B ι ξ i (wordValue w) = 0 := by
  apply operatorCompression_zero_of_dense _ (cyclicOrbit (ambientFactor B ι i) ξ)
    (cyclicOrbit_dense (ambientFactor B ι i) ξ)
  intro a b
  change inner ℂ ((ambientFactor B ι i a) ξ)
    (((wordValue w : B) : H →L[ℂ] H) ((ambientFactor B ι i b) ξ)) = 0
  rw [factor_word_coefficient]
  rw [htr (star (ι i a) * wordValue w) (ι i b), ← mul_assoc]
  have hab : ι i b * star (ι i a) ∈ factorAlgebra B ι i := ⟨b * star a, by
    change ι i (b * star a) = _
    rw [map_mul, map_star]⟩
  exact h.factor_long_zero (restrictedVectorFunctional B ξ).toLinearMap hfree hab hw hlen

theorem factorCompression_different_zero (i j : I) (hij : i ≠ j) (x : B) (hx : x ∈ K j) :
    factorCompression B ι ξ i x = 0 := by
  apply operatorCompression_zero_of_dense _ (cyclicOrbit (ambientFactor B ι i) ξ)
    (cyclicOrbit_dense (ambientFactor B ι i) ξ)
  intro a b
  change inner ℂ ((ambientFactor B ι i a) ξ)
    ((x : H →L[ℂ] H) ((ambientFactor B ι i b) ξ)) = 0
  rw [factor_word_coefficient]
  rw [htr (star (ι i a) * x) (ι i b), ← mul_assoc]
  have hw : IsCenteredWord K [(j,x)] := by
    refine ⟨?_, List.isChain_singleton _⟩
    intro y hy
    cases List.mem_singleton.mp hy
    exact hx
  have hz := h.factor_different_zero (restrictedVectorFunctional B ξ).toLinearMap hfree
    (i := i) (show ι i b * star (ι i a) ∈ factorAlgebra B ι i from ⟨b * star a, by
      change ι i (b * star a) = _
      rw [map_mul, map_star]⟩) hw hij
  simpa using hz

theorem factorCompression_normal_mem (i : I) (z : B) (hz : z ∈ normalSpan D K) :
    factorCompression B ι ξ i z ∈
      (cyclicRepresentation (ambientFactor B ι i) ξ).range := by
  let W : Submodule ℂ B :=
    ((cyclicRepresentation (ambientFactor B ι i) ξ).range).toSubalgebra.toSubmodule.comap
      (factorCompression B ι ξ i).toLinearMap
  have hs : normalSpan D K ≤ W := by
    apply Submodule.span_le.mpr
    intro z hz
    rcases hz with hd | ⟨w, hw, rfl⟩
    · have hm : ∃ a : A i, ι i a = z := h.diagonal_le i hd
      obtain ⟨a,rfl⟩ := hm
      exact ⟨a, (factorCompression_factor B ι ξ i a).symm⟩
    · cases w with
      | nil =>
        refine ⟨1, ?_⟩
        change cyclicRepresentation (ambientFactor B ι i) ξ 1 =
          operatorCompression (cyclicSpan (ambientFactor B ι i) ξ) 1
        rw [map_one, operatorCompression_one]
      | cons x w =>
        cases w with
        | nil =>
          by_cases hi : i = x.1
          · have hm : ∃ a : A x.1, ι x.1 a = x.2 := h.centered_le x.1 hw.head
            obtain ⟨a,ha⟩ := hm
            subst i
            refine ⟨a, ?_⟩
            change cyclicRepresentation (ambientFactor B ι x.1) ξ a = _
            rw [wordValue_cons, wordValue_nil, mul_one, ← ha]
            exact (factorCompression_factor B ι ξ x.1 a).symm
          · refine ⟨0, ?_⟩
            simp only [map_zero, wordValue_cons, wordValue_nil, mul_one]
            exact (factorCompression_different_zero B ι ξ D K h hfree htr i x.1 hi x.2 hw.head).symm
        | cons y w =>
          refine ⟨0, ?_⟩
          rw [map_zero]
          exact (factorCompression_long_zero B ι ξ D K h hfree htr i hw (by simp)).symm
  exact hs hz

end

section
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (B : StarSubalgebra ℂ (H →L[ℂ] H))
variable {I : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
variable (ι : ∀ i, A i →⋆ₐ[ℂ] B) (ξ : H)

@[simp] theorem factorCompression_star (i : I) (b : B) :
    factorCompression B ι ξ i (star b) = star (factorCompression B ι ξ i b) := by
  change operatorCompression (cyclicSpan (ambientFactor B ι i) ξ) (star (b : H →L[ℂ] H)) =
    star (operatorCompression (cyclicSpan (ambientFactor B ι i) ξ) (b : H →L[ℂ] H))
  exact operatorCompression_star (cyclicSpan (ambientFactor B ι i) ξ) (b : H →L[ℂ] H)

theorem factorCompression_norm_le (i : I) (b : B) :
    ‖factorCompression B ι ξ i b‖ ≤ ‖b‖ := by
  change ‖operatorCompression (cyclicSpan (ambientFactor B ι i) ξ) (b : H →L[ℂ] H)‖ ≤ ‖(b : H →L[ℂ] H)‖
  exact operatorCompression_norm_le _ (b : H →L[ℂ] H)

theorem factorCompression_mul_factor (i : I) (b : B) (a : A i) :
    factorCompression B ι ξ i (b * ι i a) =
      factorCompression B ι ξ i b * cyclicRepresentation (ambientFactor B ι i) ξ a := by
  ext x
  rfl

theorem factorCompression_factor_mul (i : I) (a : A i) (b : B) :
    factorCompression B ι ξ i (ι i a * b) =
      cyclicRepresentation (ambientFactor B ι i) ξ a * factorCompression B ι ξ i b := by
  apply star_injective
  rw [← factorCompression_star, star_mul, ← map_star, factorCompression_mul_factor,
    map_star (cyclicRepresentation (ambientFactor B ι i) ξ), factorCompression_star]
  exact (star_mul (cyclicRepresentation (ambientFactor B ι i) ξ a)
    (factorCompression B ι ξ i b)).symm

theorem factorCompression_vector (i : I) (b : B) :
    inner ℂ (⟨ξ,cyclicSpan_vector_mem (ambientFactor B ι i) ξ⟩ : cyclicSpan (ambientFactor B ι i) ξ)
      (factorCompression B ι ξ i b ⟨ξ,cyclicSpan_vector_mem (ambientFactor B ι i) ξ⟩) =
      restrictedVectorFunctional B ξ b := by
  change inner ℂ _ (operatorCompression (cyclicSpan (ambientFactor B ι i) ξ) (b : H →L[ℂ] H) _) =
    inner ℂ ξ ((b : H →L[ℂ] H) ξ)
  exact operatorCompression_inner (cyclicSpan (ambientFactor B ι i) ξ) (b : H →L[ℂ] H) _ _

def cyclicFactorAlgebra (i : I) : StarSubalgebra ℂ
    ((cyclicSpan (ambientFactor B ι i) ξ) →L[ℂ] (cyclicSpan (ambientFactor B ι i) ξ)) :=
  (cyclicRepresentation (ambientFactor B ι i) ξ).range

variable (D : NonUnitalSubalgebra ℂ B) (K : I → Submodule ℂ B)
variable (h : CenteredDecomposition D (factorAlgebra B ι) K)
variable (hfree : ∀ w, IsCenteredWord K w → w ≠ [] →
  restrictedVectorFunctional B ξ (wordValue w) = 0)
variable (htr : ∀ a b : B, restrictedVectorFunctional B ξ (a*b) =
  restrictedVectorFunctional B ξ (b*a))
variable (hdense : Dense (normalSpan D K : Set B))
variable (hsep : ∀ (i : I) (a : A i), (ambientFactor B ι i a) ξ = 0 → a = 0)
include h hfree htr hdense hsep

theorem factorCompression_mem (i : I) (b : B) :
    factorCompression B ι ξ i b ∈ (cyclicRepresentation (ambientFactor B ι i) ξ).range := by
  have hc : IsClosed {b : B | factorCompression B ι ξ i b ∈
      (cyclicRepresentation (ambientFactor B ι i) ξ).range} :=
    (faithfulRepresentation_range_closed _
      (cyclicRepresentation_injective _ ξ (hsep i))).preimage (factorCompression B ι ξ i).continuous
  exact closure_minimal
    (fun z hz => factorCompression_normal_mem B ι ξ D K h hfree htr i z hz) hc (hdense b)

def compressionIntoFactor (i : I) :
    B →L[ℂ] cyclicFactorAlgebra B ι ξ i where
  toFun b := ⟨factorCompression B ι ξ i b,
    factorCompression_mem B ι ξ D K h hfree htr hdense hsep i b⟩
  map_add' b c := Subtype.ext ((factorCompression B ι ξ i).map_add b c)
  map_smul' c b := Subtype.ext ((factorCompression B ι ξ i).map_smul c b)
  cont := (factorCompression B ι ξ i).continuous.subtype_mk _

def factorExpectation (i : I) : B →L[ℂ] A i :=
  (representationInverse (cyclicRepresentation (ambientFactor B ι i) ξ)
    (cyclicRepresentation_injective _ ξ (hsep i))).comp
      (compressionIntoFactor B ι ξ D K h hfree htr hdense hsep i)

@[simp] theorem factorExpectation_rep (i : I) (b : B) :
    cyclicRepresentation (ambientFactor B ι i) ξ
      (factorExpectation B ι ξ D K h hfree htr hdense hsep i b) =
      factorCompression B ι ξ i b :=
  representation_map_inverse (cyclicRepresentation (ambientFactor B ι i) ξ)
    (cyclicRepresentation_injective _ ξ (hsep i))
    (compressionIntoFactor B ι ξ D K h hfree htr hdense hsep i b)

@[simp] theorem factorExpectation_factor (i : I) (a : A i) :
    factorExpectation B ι ξ D K h hfree htr hdense hsep i (ι i a) = a := by
  apply cyclicRepresentation_injective _ ξ (hsep i)
  rw [factorExpectation_rep, factorCompression_factor]

theorem factorExpectation_norm_le (i : I) (b : B) :
    ‖factorExpectation B ι ξ D K h hfree htr hdense hsep i b‖ ≤ ‖b‖ := by
  rw [← NonUnitalStarAlgHom.norm_map (cyclicRepresentation (ambientFactor B ι i) ξ)
    (cyclicRepresentation_injective _ ξ (hsep i)), factorExpectation_rep]
  exact factorCompression_norm_le B ι ξ i b

@[simp] theorem factorExpectation_star (i : I) (b : B) :
    factorExpectation B ι ξ D K h hfree htr hdense hsep i (star b) =
      star (factorExpectation B ι ξ D K h hfree htr hdense hsep i b) := by
  apply cyclicRepresentation_injective _ ξ (hsep i)
  rw [map_star (cyclicRepresentation (ambientFactor B ι i) ξ), factorExpectation_rep, factorExpectation_rep, factorCompression_star]

theorem factorExpectation_mul_factor (i : I) (b : B) (a : A i) :
    factorExpectation B ι ξ D K h hfree htr hdense hsep i (b * ι i a) =
      factorExpectation B ι ξ D K h hfree htr hdense hsep i b * a := by
  apply cyclicRepresentation_injective _ ξ (hsep i)
  rw [map_mul (cyclicRepresentation (ambientFactor B ι i) ξ), factorExpectation_rep, factorExpectation_rep, factorCompression_mul_factor]

theorem factorExpectation_factor_mul (i : I) (a : A i) (b : B) :
    factorExpectation B ι ξ D K h hfree htr hdense hsep i (ι i a * b) =
      a * factorExpectation B ι ξ D K h hfree htr hdense hsep i b := by
  apply cyclicRepresentation_injective _ ξ (hsep i)
  rw [map_mul (cyclicRepresentation (ambientFactor B ι i) ξ), factorExpectation_rep, factorExpectation_rep, factorCompression_factor_mul]

theorem factorExpectation_trace (i : I) (b : B) :
    restrictedVectorFunctional B ξ
      (ι i (factorExpectation B ι ξ D K h hfree htr hdense hsep i b)) =
      restrictedVectorFunctional B ξ b := by
  rw [← factorCompression_vector B ι ξ i, factorCompression_factor, factorExpectation_rep]
  exact factorCompression_vector B ι ξ i b

end

open scoped CStarAlgebra
section
universe u v
variable {A : Type u} {C : Type v} [CStarAlgebra A] [CStarAlgebra C]

theorem faithfulStarHom_spectrum (π : A →⋆ₐ[ℂ] C) (hπ : Function.Injective π) (a : A) :
    spectrum ℂ (π a) = spectrum ℂ a := by
  let : IsClosed (π.range : Set C) :=
    (NonUnitalStarAlgHom.isometry π hπ).isClosedEmbedding.isClosed_range
  calc
    spectrum ℂ (π a) = spectrum ℂ ((StarAlgEquiv.ofInjective π hπ) a) :=
      (StarSubalgebra.spectrum_eq π.range (a := (StarAlgEquiv.ofInjective π hπ) a)).symm
    _ = spectrum ℂ a := AlgEquiv.spectrum_eq (StarAlgEquiv.ofInjective π hπ) a

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder C] [StarOrderedRing C]

theorem faithfulStarHom_nonneg_iff (π : A →⋆ₐ[ℂ] C) (hπ : Function.Injective π) (a : A) :
    0 ≤ π a ↔ 0 ≤ a := by
  refine ⟨fun hp => ?_, map_nonneg π⟩
  have hpsa : IsSelfAdjoint (π a) := IsSelfAdjoint.of_nonneg hp
  have hsa : IsSelfAdjoint a := by
    apply hπ
    rw [map_star]
    exact hpsa.star_eq
  apply (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) a hsa).mpr
  intro x hx
  apply spectrum_nonneg_of_nonneg hp
  apply hpsa.coe_mem_spectrum_complex.mp
  rw [faithfulStarHom_spectrum π hπ]
  exact hsa.coe_mem_spectrum_complex.mpr hx

end

section
open scoped InnerProductSpace ComplexOrder CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem operatorCompression_nonneg (M : Submodule ℂ H) [CompleteSpace M]
    (T : H →L[ℂ] H) (hT : 0 ≤ T) : 0 ≤ operatorCompression M T := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  apply (ContinuousLinearMap.isPositive_iff' _).mpr
  refine ⟨?_, fun x => ?_⟩
  · change star (operatorCompression M T) = operatorCompression M T
    rw [← operatorCompression_star, (IsSelfAdjoint.of_nonneg hT).star_eq]
  · rw [← inner_conj_symm, operatorCompression_inner]
    exact star_nonneg_iff.mpr ((ContinuousLinearMap.nonneg_iff_isPositive (f := T)).mp hT |>.inner_nonneg_right x)

variable (B : StarSubalgebra ℂ (H →L[ℂ] H))
variable {I : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (ι : ∀ i, A i →⋆ₐ[ℂ] B) (ξ : H)
variable (D : NonUnitalSubalgebra ℂ B) (K : I → Submodule ℂ B)
variable (h : CenteredDecomposition D (factorAlgebra B ι) K)
variable (hfree : ∀ w, IsCenteredWord K w → w ≠ [] →
  restrictedVectorFunctional B ξ (wordValue w) = 0)
variable (htr : ∀ a b : B, restrictedVectorFunctional B ξ (a*b) =
  restrictedVectorFunctional B ξ (b*a))
variable (hdense : Dense (normalSpan D K : Set B))
variable (hsep : ∀ (i : I) (a : A i), (ambientFactor B ι i a) ξ = 0 → a = 0)

theorem factorExpectation_nonneg (i : I) (b : B) (hb : 0 ≤ b) :
    0 ≤ factorExpectation B ι ξ D K h hfree htr hdense hsep i b := by
  let π : A i →⋆ₐ[ℂ] ((cyclicSpan (ambientFactor B ι i) ξ) →L[ℂ]
    (cyclicSpan (ambientFactor B ι i) ξ)) := cyclicRepresentation (ambientFactor B ι i) ξ
  have hπ : Function.Injective π := cyclicRepresentation_injective _ ξ (hsep i)
  apply (faithfulStarHom_nonneg_iff (A := A i) (C := (cyclicSpan (ambientFactor B ι i) ξ →L[ℂ]
    cyclicSpan (ambientFactor B ι i) ξ)) π hπ _).mp
  rw [factorExpectation_rep]
  exact operatorCompression_nonneg _ _ hb

def factorExpectationPositive (i : I) : B →ₚ[ℂ] A i where
  toLinearMap := (factorExpectation B ι ξ D K h hfree htr hdense hsep i).toLinearMap
  monotone' := by
    intro a b hab
    have hp := factorExpectation_nonneg B ι ξ D K h hfree htr hdense hsep i (b-a)
      (sub_nonneg.mpr hab)
    rw [map_sub] at hp
    exact sub_nonneg.mp hp

end

section
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I] [DecidableEq V]

theorem atomicCommonAtom_separate (k : I) (T U : AtomicOperators d)
    (h : ∀ r, atomicCommonAtom d k r * T = atomicCommonAtom d k r * U) : T = U := by
  ext x j
  have hh := congrArg (fun W : AtomicOperators d => W x j) (h j.2.1)
  simpa only [mul_apply_eq_comp, atomicCommonAtom_apply, ite_eq_left rfl, ite_true] using hh

variable {Δ : Type*} [CStarAlgebra Δ]
variable (δ : ∀ i, Δ →⋆ₐ[ℂ] A i) (χ : Δ → V → ℂ)
variable (hatom : ∀ i x r, ((d i).atom r).1 * δ i x = χ x r • ((d i).atom r).1)
include hatom

theorem atomicLeft_diagonal_agree (i k : I) (x : Δ) :
    atomicLeft d i (δ i x) = atomicLeft d k (δ k x) := by
  apply atomicCommonAtom_separate d k
  intro r
  change atomicLeft d k ((d k).atom r).1 * atomicLeft d i (δ i x) = _
  rw [← atomicLeft_atoms d i k r, ← map_mul, hatom i x r, map_smul]
  rw [atomicLeft_atoms d i k r]
  change χ x r • atomicLeft d k ((d k).atom r).1 =
    atomicLeft d k ((d k).atom r).1 * atomicLeft d k (δ k x)
  rw [← map_mul, hatom k x r, map_smul]

theorem atomicEmbedding_diagonal_agree (i k : I) (x : Δ) :
    atomicEmbedding d i (δ i x) = atomicEmbedding d k (δ k x) :=
  Subtype.ext (atomicLeft_diagonal_agree d δ χ hatom i k x)

def atomicDiagonal (k : I) : NonUnitalSubalgebra ℂ (AtomicCStar d) :=
  ((atomicEmbedding d k).comp (δ k)).range.toSubalgebra.toNonUnitalSubalgebra

def atomicKernel (E : ∀ i, A i →L[ℂ] Δ) (i : I) : Submodule ℂ (AtomicCStar d) :=
  (LinearMap.ker (E i).toLinearMap).map (atomicEmbedding d i).toAlgHom.toLinearMap

variable (E : ∀ i, A i →L[ℂ] Δ)
variable (hfix : ∀ i x, E i (δ i x) = x)
variable (hleft : ∀ i x a, E i (δ i x * a) = x * E i a)

include hfix hleft

theorem atomicDiagonal_decomposition (k : I) :
    CenteredDecomposition (atomicDiagonal d δ k)
      (factorAlgebra (atomicCStarAlgebra d) (atomicEmbedding d)) (atomicKernel d E) where
  diagonal_le := by
    intro i x hx
    rcases hx with ⟨y,rfl⟩
    exact ⟨δ i y, atomicEmbedding_diagonal_agree d δ χ hatom i k y⟩
  centered_le := by
    intro i x hx
    rcases hx with ⟨a,_,rfl⟩
    exact ⟨a,rfl⟩
  decompose := by
    intro i x hx
    rcases hx with ⟨a,rfl⟩
    refine ⟨atomicEmbedding d i (δ i (E i a)), ?_,
      atomicEmbedding d i (a - δ i (E i a)), ?_, ?_⟩
    · exact ⟨E i a, (atomicEmbedding_diagonal_agree d δ χ hatom k i (E i a))⟩
    · refine ⟨a - δ i (E i a), ?_, rfl⟩
      change E i (a - δ i (E i a)) = 0
      rw [map_sub, hfix i, sub_self]
    · change atomicEmbedding d i a = atomicEmbedding d i (δ i (E i a)) +
        atomicEmbedding d i (a - δ i (E i a))
      rw [map_sub, add_sub_cancel]
  diagonal_mul := by
    intro i x c hx hc
    rcases hx with ⟨y,rfl⟩
    rcases hc with ⟨a,ha,rfl⟩
    refine ⟨δ i y * a, ?_, ?_⟩
    · change E i (δ i y * a) = 0
      change E i a = 0 at ha
      rw [hleft i, ha, mul_zero]
    · change atomicEmbedding d i (δ i y * a) =
        atomicEmbedding d k (δ k y) * atomicEmbedding d i a
      rw [map_mul, atomicEmbedding_diagonal_agree d δ χ hatom i k y]

end

section
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I] [DecidableEq V]
variable {Δ : Type*} [CStarAlgebra Δ]
variable (δ : ∀ i, Δ →⋆ₐ[ℂ] A i) (χ : Δ → V → ℂ)
variable (hatom : ∀ i x r, ((d i).atom r).1 * δ i x = χ x r • ((d i).atom r).1)
variable (E : ∀ i, A i →L[ℂ] Δ)
variable (hfix : ∀ i x, E i (δ i x) = x)
variable (hleft : ∀ i x a, E i (δ i x * a) = x * E i a)

include hatom hfix hleft

theorem atomicNormalSpan_dense (k : I) :
    Dense (normalSpan (atomicDiagonal d δ k) (atomicKernel d E) : Set (AtomicCStar d)) := by
  let S : Subalgebra ℂ (AtomicCStar d) := Algebra.adjoin ℂ
    (⋃ i, (factorAlgebra (atomicCStarAlgebra d) (atomicEmbedding d) i : Set (AtomicCStar d)))
  have hlift (a : AtomicOperators d) (ha : a ∈ atomicAlgebra d) :
      (⟨a,subset_closure ha⟩ : AtomicCStar d) ∈ S := by
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      rcases Set.mem_iUnion.mp ha with ⟨i,hi⟩
      rcases hi with ⟨b,rfl⟩
      exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i,⟨b,rfl⟩⟩)
    | algebraMap c => exact S.algebraMap_mem c
    | add a b _ _ ha hb => exact S.add_mem ha hb
    | mul a b _ _ ha hb => exact S.mul_mem ha hb
  have hd : DenseRange (fun a : atomicAlgebra d =>
      (⟨a.1,subset_closure a.2⟩ : AtomicCStar d)) :=
    (denseRange_inclusion_iff subset_closure).mpr Set.Subset.rfl
  apply hd.mono
  rintro a ⟨a,rfl⟩
  exact (atomicDiagonal_decomposition d δ χ hatom E hfix hleft k).adjoin_le_normalSpan
    (hlift a.1 a.2)

omit hatom hfix hleft [DecidableEq V]

variable (hcenter : ∀ i a, E i a = 0 → ∀ r,
  (d i).trace (((d i).atom r).1 * a * ((d i).atom r).1) = 0)
include hcenter

theorem atomicKernel_starts (i : I) (T : AtomicCStar d) (hT : T ∈ atomicKernel d E i)
    (x : AtomicHilbertSpace d) (hx : FockAway (AtomicLetters d) i x) :
    FockStarts (AtomicLetters d) i ((T : AtomicOperators d) x) := by
  rcases hT with ⟨a,ha,rfl⟩
  exact atomicLeft_centered d i a (hcenter i a ha) x hx

theorem atomicKernelWord_starts (k : I) (x : I × AtomicCStar d)
    (w : List (I × AtomicCStar d)) (h : IsCenteredWord (atomicKernel d E) (x :: w)) :
    FockStarts (AtomicLetters d) x.1
      (((wordValue (x :: w) : AtomicCStar d) : AtomicOperators d) (atomicVacuum d k)) := by
  induction w generalizing x with
  | nil =>
    simp only [wordValue_cons, wordValue_nil, mul_one]
    exact atomicKernel_starts d E hcenter x.1 x.2 h.head _
      (fockVacuum_away (AtomicLetters d) _ x.1)
  | cons y w ih =>
    rw [wordValue_cons]
    change FockStarts (AtomicLetters d) x.1
      ((x.2 : AtomicOperators d) (((wordValue (y::w) : AtomicCStar d) : AtomicOperators d) _))
    apply atomicKernel_starts d E hcenter x.1 x.2 h.head
    apply fockStarts_away (AtomicLetters d) _ _ (ih y h.tail)
    exact (List.isChain_cons_cons.mp h.alternating).1.symm

theorem atomicKernelWord_zero (k : I) (w : List (I × AtomicCStar d))
    (h : IsCenteredWord (atomicKernel d E) w) (hne : w ≠ []) :
    restrictedVectorFunctional (atomicCStarAlgebra d) (atomicVacuum d k) (wordValue w) = 0 := by
  cases w with
  | nil => exact (hne rfl).elim
  | cons x w =>
    exact fockVacuum_inner_starts (AtomicLetters d) _ x.1 _
      (atomicKernelWord_starts d E hcenter k x w h)

omit hcenter in

theorem atomicFactor_separating (k : I)
    (hw : ∀ i r, ((d k).trace ((d k).atom r).1).re = ((d i).trace ((d i).atom r).1).re)
    (i : I) (a : A i) (ha : (atomicLeft d i a) (atomicVacuum d k) = 0) : a = 0 := by
  apply (d i).faithful a
  rw [← atomicLeft_vacuum_trace d k i (hw i)]
  change operatorVectorFunctional (atomicVacuum d k) (atomicLeft d i (star a*a)) = 0
  rw [map_mul, map_star, operatorVectorFunctional_star_mul, ha]
  simp

end

section
open scoped InnerProductSpace ComplexOrder CStarAlgebra lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I] [DecidableEq V]
variable {Δ : Type*} [CStarAlgebra Δ]

structure AtomicAmalgamData where
  diagonal : ∀ i, Δ →⋆ₐ[ℂ] A i
  coordinate : Δ → V → ℂ
  atom_mul : ∀ i x r, ((d i).atom r).1 * diagonal i x =
    coordinate x r • ((d i).atom r).1
  expectation : ∀ i, A i →L[ℂ] Δ
  fix : ∀ i x, expectation i (diagonal i x) = x
  left : ∀ i x a, expectation i (diagonal i x * a) = x * expectation i a
  centered : ∀ i a, expectation i a = 0 → ∀ r,
    (d i).trace (((d i).atom r).1 * a * ((d i).atom r).1) = 0
  base : I
  weights : ∀ i r, ((d base).trace ((d base).atom r).1).re =
    ((d i).trace ((d i).atom r).1).re

variable (c : AtomicAmalgamData (Δ := Δ) d)

def atomicExpectation (i : I) : AtomicCStar d →L[ℂ] A i :=
  factorExpectation (atomicCStarAlgebra d) (atomicEmbedding d) (atomicVacuum d c.base)
    (atomicDiagonal d c.diagonal c.base) (atomicKernel d c.expectation)
    (atomicDiagonal_decomposition d c.diagonal c.coordinate c.atom_mul c.expectation
      c.fix c.left c.base)
    (atomicKernelWord_zero d c.expectation c.centered c.base)
    (atomicCStar_trace d c.base c.weights)
    (atomicNormalSpan_dense d c.diagonal c.coordinate c.atom_mul c.expectation c.fix c.left c.base)
    (atomicFactor_separating d c.base c.weights) i

@[simp] theorem atomicExpectation_factor (i : I) (a : A i) :
    atomicExpectation d c i (atomicEmbedding d i a) = a :=
  factorExpectation_factor _ _ _ _ _ _ _ _ _ _ i a

theorem atomicExpectation_norm_le (i : I) (b : AtomicCStar d) :
    ‖atomicExpectation d c i b‖ ≤ ‖b‖ :=
  factorExpectation_norm_le _ _ _ _ _ _ _ _ _ _ i b

@[simp] theorem atomicExpectation_one (i : I) : atomicExpectation d c i 1 = 1 := by
  rw [← map_one (atomicEmbedding d i), atomicExpectation_factor]

@[simp] theorem atomicExpectation_star (i : I) (b : AtomicCStar d) :
    atomicExpectation d c i (star b) = star (atomicExpectation d c i b) :=
  factorExpectation_star _ _ _ _ _ _ _ _ _ _ i b

theorem atomicExpectation_nonneg (i : I) (b : AtomicCStar d) (hb : 0 ≤ b) :
    0 ≤ atomicExpectation d c i b :=
  factorExpectation_nonneg _ _ _ _ _ _ _ _ _ _ i b hb

theorem atomicExpectation_mul_factor (i : I) (b : AtomicCStar d) (a : A i) :
    atomicExpectation d c i (b * atomicEmbedding d i a) = atomicExpectation d c i b * a :=
  factorExpectation_mul_factor _ _ _ _ _ _ _ _ _ _ i b a

theorem atomicExpectation_factor_mul (i : I) (a : A i) (b : AtomicCStar d) :
    atomicExpectation d c i (atomicEmbedding d i a * b) = a * atomicExpectation d c i b :=
  factorExpectation_factor_mul _ _ _ _ _ _ _ _ _ _ i a b

def atomicTrace : AtomicCStar d →L[ℂ] ℂ :=
  restrictedVectorFunctional (atomicCStarAlgebra d) (atomicVacuum d c.base)

omit [DecidableEq V] in
theorem atomicTrace_factor (i : I) (a : A i) :
    atomicTrace d c (atomicEmbedding d i a) = (d i).trace a :=
  atomicLeft_vacuum_trace d c.base i (c.weights i) a

omit [DecidableEq V] in
theorem atomicTrace_mul (a b : AtomicCStar d) :
    atomicTrace d c (a*b) = atomicTrace d c (b*a) := atomicCStar_trace d c.base c.weights a b

omit [DecidableEq V] in
theorem atomicTrace_faithful (a : AtomicCStar d)
    (ha : atomicTrace d c (star a*a) = 0) : a = 0 :=
  atomicCStar_faithful d c.base c.weights a ha

omit [DecidableEq V] in
@[simp] theorem atomicTrace_norm : ‖atomicTrace d c‖ = 1 :=
  restrictedVectorFunctional_norm _ _ (atomicVacuum_norm d c.base)

omit [DecidableEq V] in
theorem atomicTrace_square (a : AtomicCStar d) :
    (atomicTrace d c (star a*a)).im = 0 ∧ 0 ≤ (atomicTrace d c (star a*a)).re := by
  have hv : atomicTrace d c (star a*a) =
      (‖(a : AtomicOperators d) (atomicVacuum d c.base)‖ ^ 2 : ℝ) :=
    by
      change operatorVectorFunctional (atomicVacuum d c.base) (star (a : AtomicOperators d)*a) = _
      exact operatorVectorFunctional_star_mul (atomicVacuum d c.base) (a : AtomicOperators d)
  rw [hv]
  exact ⟨rfl, sq_nonneg _⟩

omit [DecidableEq V] in
theorem atomicTrace_strict (a : AtomicCStar d) (ha : a ≠ 0) :
    0 < (atomicTrace d c (star a*a)).re :=
  restrictedVectorFunctional_strict _ _ (atomicCStar_cyclic d c.base)
    (atomicCStar_trace d c.base c.weights) a ha

theorem atomicExpectation_trace (i : I) (b : AtomicCStar d) :
    (d i).trace (atomicExpectation d c i b) = atomicTrace d c b := by
  rw [← atomicTrace_factor d c i]
  exact factorExpectation_trace _ _ _ _ _ _ _ _ _ _ i b

theorem atomicExpectation_faithful (i : I) (b : AtomicCStar d)
    (hb : atomicExpectation d c i (star b*b) = 0) : b = 0 := by
  apply atomicTrace_faithful d c
  rw [← atomicExpectation_trace d c i, hb, map_zero]

end

open scoped ComplexOrder CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {n : Type*} [Fintype n] [DecidableEq n]

def matrixTrace (τ : A →ₚ[ℂ] ℂ) : CStarMatrix n n A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    { toFun := fun M => ∑ i, τ (M i i)
      map_add' M N := by simp [Finset.sum_add_distrib]
      map_smul' z M := by simp [Finset.mul_sum] }
    (by
      intro M hM
      apply AddSubmonoid.closure_induction
        (motive := fun M _ => 0 ≤ ∑ i, τ (M i i)) ?_ ?_ ?_
        (StarOrderedRing.nonneg_iff.mp hM)
      · rintro M ⟨N,rfl⟩
        simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, map_sum]
        exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          τ.map_nonneg (star_mul_self_nonneg _)
      · simp
      · intro M N _ _ hM hN
        simpa only [CStarMatrix.add_apply, map_add, Finset.sum_add_distrib] using add_nonneg hM hN)

omit [DecidableEq n] in
@[simp] theorem matrixTrace_apply (τ : A →ₚ[ℂ] ℂ) (M : CStarMatrix n n A) :
    matrixTrace τ M = ∑ i, τ (M i i) := rfl

omit [DecidableEq n] in

theorem matrixTrace_tracial (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b, τ (a*b) = τ (b*a))
    (M N : CStarMatrix n n A) : matrixTrace τ (M*N) = matrixTrace τ (N*M) := by
  simp only [matrixTrace_apply, CStarMatrix.mul_apply, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact hτ _ _

omit [DecidableEq n] in

theorem matrixTrace_faithful (τ : A →ₚ[ℂ] ℂ)
    (hf : ∀ a, τ (star a*a) = 0 → a = 0) (M : CStarMatrix n n A)
    (hM : matrixTrace τ (star M * M) = 0) : M = 0 := by
  simp only [matrixTrace_apply, CStarMatrix.mul_apply, CStarMatrix.star_apply, map_sum] at hM
  have hn (i j : n) : 0 ≤ τ (star (M i j)*M i j) := τ.map_nonneg (star_mul_self_nonneg _)
  ext i j
  apply hf
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
    Finset.sum_nonneg (fun l _ => hn l k))).mp hM j (Finset.mem_univ j)
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => hn l j)).mp hj i (Finset.mem_univ i)

@[simp] theorem matrixTrace_one (τ : A →ₚ[ℂ] ℂ) :
    matrixTrace (n := n) τ 1 = (Fintype.card n : ℂ) * τ 1 := by
  simp only [matrixTrace_apply, CStarMatrix.one_apply_eq, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

def normalizedMatrixTrace (τ : A →ₚ[ℂ] ℂ) : CStarMatrix n n A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ ((Fintype.card n : ℝ)⁻¹ • (matrixTrace τ).toLinearMap)
    (by
      intro M hM
      change 0 ≤ (Fintype.card n : ℝ)⁻¹ • matrixTrace τ M
      exact smul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) ((matrixTrace τ).map_nonneg hM))

omit [DecidableEq n] in
@[simp] theorem normalizedMatrixTrace_apply (τ : A →ₚ[ℂ] ℂ) (M : CStarMatrix n n A) :
    normalizedMatrixTrace τ M = (Fintype.card n : ℝ)⁻¹ • matrixTrace τ M := rfl

omit [DecidableEq n] in
theorem normalizedMatrixTrace_tracial (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b, τ (a*b) = τ (b*a))
    (M N : CStarMatrix n n A) : normalizedMatrixTrace τ (M*N) = normalizedMatrixTrace τ (N*M) := by
  simp only [normalizedMatrixTrace_apply, matrixTrace_tracial τ hτ M N]

omit [DecidableEq n] in
theorem normalizedMatrixTrace_faithful [Nonempty n] (τ : A →ₚ[ℂ] ℂ)
    (hf : ∀ a, τ (star a*a) = 0 → a = 0) (M : CStarMatrix n n A)
    (hM : normalizedMatrixTrace τ (star M*M) = 0) : M = 0 := by
  apply matrixTrace_faithful τ hf M
  rw [normalizedMatrixTrace_apply] at hM
  exact (smul_eq_zero.mp hM).resolve_left
    (inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))

theorem normalizedMatrixTrace_one [Nonempty n] (τ : A →ₚ[ℂ] ℂ) (hn : τ 1 = 1) :
    normalizedMatrixTrace (n := n) τ 1 = 1 := by
  rw [normalizedMatrixTrace_apply, matrixTrace_one, hn, mul_one]
  change (Fintype.card n : ℝ)⁻¹ * (Fintype.card n : ℂ) = 1
  rw [Complex.ofReal_inv, Complex.ofReal_natCast, inv_mul_cancel₀]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

open scoped CStarAlgebra
variable {A B n : Type*} [CStarAlgebra A] [CStarAlgebra B] [Fintype n] [DecidableEq n]

def matrixSingle (i j : n) (a : A) : CStarMatrix n n A :=
  CStarMatrix.ofMatrix (Matrix.single i j a)

omit [Fintype n] in
@[simp] theorem matrixSingle_apply (i j k l : n) (a : A) :
    matrixSingle i j a k l = if i = k ∧ j = l then a else 0 := rfl

omit [Fintype n] in
@[simp] theorem matrixSingle_star (i j : n) (a : A) :
    star (matrixSingle i j a) = matrixSingle j i (star a) := by
  change (Matrix.single i j a).conjTranspose = Matrix.single j i (star a)
  exact Matrix.conjTranspose_single _ _ _

@[simp] theorem matrixSingle_mul (i j k : n) (a b : A) :
    matrixSingle i j a * matrixSingle j k b = matrixSingle i k (a*b) := by
  change Matrix.single i j a * Matrix.single j k b = Matrix.single i k (a*b)
  exact Matrix.single_mul_single_same a i j k b

theorem matrixSingle_mul_of_ne (i j k l : n) (a b : A) (h : j ≠ k) :
    matrixSingle i j a * matrixSingle k l b = 0 := by
  change Matrix.single i j a * Matrix.single k l b = 0
  exact Matrix.single_mul_single_of_ne a i j k h b

omit [Fintype n] in
@[simp] theorem matrixSingle_zero (i j : n) : matrixSingle i j (0 : A) = 0 := by
  ext; simp

omit [Fintype n] in
@[simp] theorem matrixSingle_smul (i j : n) (a : A) (z : ℂ) :
    matrixSingle i j (z • a) = z • matrixSingle i j a := by
  ext k l
  by_cases h : i = k ∧ j = l <;> simp [h]

theorem matrixSingle_projection (i : n) (a : A) (ha : IsStarProjection a) :
    IsStarProjection (matrixSingle i i a) := by
  refine ⟨?_, ?_⟩
  · simp only [IsIdempotentElem, matrixSingle_mul, ha.isIdempotentElem.eq]
  · simp only [IsSelfAdjoint, matrixSingle_star, ha.isSelfAdjoint.star_eq]

@[simp] theorem matrixSingle_compress (i j : n) (a b : A) (M : CStarMatrix n n A) :
    matrixSingle i i a * M * matrixSingle j j b = matrixSingle i j (a * M i j * b) := by
  change Matrix.single i i a * CStarMatrix.ofMatrix.symm M * Matrix.single j j b = _
  exact Matrix.single_mul_mul_single i i j j a _ b

def matrixDiagonalHom (δ : n → B →⋆ₐ[ℂ] A) : (n → B) →⋆ₐ[ℂ] CStarMatrix n n A where
  toFun x := CStarMatrix.ofMatrix (Matrix.diagonal (fun i => δ i (x i)))
  map_zero' := by
    change Matrix.diagonal (fun i => δ i 0) = 0
    simp
  map_one' := by
    change Matrix.diagonal (fun i => δ i 1) = (1 : Matrix n n A)
    simp
  map_add' x y := by
    change Matrix.diagonal (fun i => δ i (x i + y i)) =
      Matrix.diagonal (fun i => δ i (x i)) + Matrix.diagonal (fun i => δ i (y i))
    simp only [map_add, Matrix.diagonal_add]
  map_mul' x y := by
    change CStarMatrix.ofMatrix (Matrix.diagonal (fun i => δ i (x i * y i))) = _
    change Matrix.diagonal (fun i => δ i (x i * y i)) =
      Matrix.diagonal (fun i => δ i (x i)) * Matrix.diagonal (fun i => δ i (y i))
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext i; exact map_mul _ _ _
  commutes' z := by
    change Matrix.diagonal (fun i => δ i (algebraMap ℂ B z)) = algebraMap ℂ (Matrix n n A) z
    rw [Matrix.algebraMap_eq_diagonal]
    congr 1
    funext i
    exact (δ i).commutes z
  map_star' x := by
    change Matrix.diagonal (fun i => δ i (star (x i))) =
      (Matrix.diagonal (fun i => δ i (x i))).conjTranspose
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    exact map_star (δ i) (x i)

@[simp] theorem matrixDiagonalHom_apply (δ : n → B →⋆ₐ[ℂ] A) (x : n → B) (i j : n) :
    matrixDiagonalHom δ x i j = if i = j then δ i (x i) else 0 := by
  simp [matrixDiagonalHom, Matrix.diagonal_apply]

@[simp] theorem matrixDiagonalHom_mul_apply (δ : n → B →⋆ₐ[ℂ] A) (x : n → B)
    (M : CStarMatrix n n A) (i j : n) :
    (matrixDiagonalHom δ x * M) i j = δ i (x i) * M i j := by
  exact Matrix.diagonal_mul _ _ _ _

@[simp] theorem matrixSingle_diagonal (δ : n → B →⋆ₐ[ℂ] A) (x : n → B) (i : n) (a : A) :
    matrixSingle i i a * matrixDiagonalHom δ x = matrixSingle i i (a * δ i (x i)) := by
  ext k l
  change (Matrix.single i i a * Matrix.diagonal (fun j => δ j (x j))) k l = _
  rw [Matrix.mul_diagonal]
  by_cases h : i = k ∧ i = l
  · rcases h with ⟨rfl,rfl⟩; simp
  · simp [matrixSingle_apply, h]

variable [PartialOrder A] [StarOrderedRing A]

def matrixDiagonalExpectation (E : n → A →L[ℂ] B) (hE : ∀ i a, ‖E i a‖ ≤ ‖a‖) :
    CStarMatrix n n A →L[ℂ] (n → B) :=
  LinearMap.mkContinuous
    { toFun := fun M i => E i (M i i)
      map_add' M N := by ext i; simp
      map_smul' z M := by ext i; simp }
    1 (fun M => by
      change ‖fun i => E i (M i i)‖ ≤ 1 * ‖M‖
      rw [one_mul]
      exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i =>
        (hE i _).trans CStarMatrix.norm_entry_le_norm)

omit [DecidableEq n] in
@[simp] theorem matrixDiagonalExpectation_apply (E : n → A →L[ℂ] B)
    (hE : ∀ i a, ‖E i a‖ ≤ ‖a‖) (M : CStarMatrix n n A) (i : n) :
    matrixDiagonalExpectation E hE M i = E i (M i i) := rfl

open scoped ComplexOrder CStarAlgebra
variable {A V n : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n]

@[simp] theorem matrixTrace_single (τ : A →ₚ[ℂ] ℂ) (i : n) (a : A) :
    matrixTrace τ (matrixSingle i i a) = τ a := by
  simp only [matrixTrace_apply, matrixSingle_apply, and_self]
  simp_rw [apply_ite τ, map_zero]
  simp

@[simp] theorem normalizedMatrixTrace_single (τ : A →ₚ[ℂ] ℂ) (i : n) (a : A) :
    normalizedMatrixTrace τ (matrixSingle i i a) = (Fintype.card n : ℝ)⁻¹ • τ a := by
  rw [normalizedMatrixTrace_apply, matrixTrace_single]

variable [Nonempty n]

def matrixAtomicTraceData (τ : A →ₚ[ℂ] ℂ) (htr : IsTracialPositive τ)
    (hn : τ 1 = 1) (hf : ∀ a, τ (star a*a) = 0 → a = 0)
    (d : n → AtomicTraceData A V) (hd : ∀ i, (d i).trace = τ) :
    AtomicTraceData (CStarMatrix n n A) (n × V) where
  trace := normalizedMatrixTrace τ
  tracial := normalizedMatrixTrace_tracial τ htr
  normalized := normalizedMatrixTrace_one τ hn
  faithful := normalizedMatrixTrace_faithful τ hf
  atom v := ⟨matrixSingle v.1 v.1 ((d v.1).atom v.2).1,
    matrixSingle_projection _ _ ((d v.1).atom v.2).2⟩
  orthogonal v w h := by
    by_cases hvw : v.1 = w.1
    · rcases v with ⟨i,v⟩; rcases w with ⟨j,w⟩
      dsimp only at hvw
      subst j
      rw [matrixSingle_mul, (d i).orthogonal v w (by intro he; exact h (congrArg (Prod.mk i) he)),
        matrixSingle_zero]
    · exact matrixSingle_mul_of_ne _ _ _ _ _ _ hvw
  positive v := by
    rw [normalizedMatrixTrace_single, Complex.smul_re, smul_eq_mul]
    rw [← hd v.1]
    exact mul_pos (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)) ((d v.1).positive _)
  mass := by
    let c : ℝ := (Fintype.card n : ℝ)⁻¹
    have hc : 0 < c := inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
    let w : n × V → ℝ := fun v => c * ((d v.1).trace ((d v.1).atom v.2).1).re
    have hw (i : n) : HasSum (fun v : V => w (i,v)) c := by
      simpa only [w, (d i).normalized, Complex.one_re, mul_one] using (d i).mass.mul_left c
    have hsum : Summable w := (summable_prod_of_nonneg (fun v =>
      mul_nonneg hc.le ((d v.1).positive v.2).le)).mpr
      ⟨fun i => (hw i).summable, (hasSum_fintype _).summable⟩
    have hval : ∑' v, w v = 1 := by
      rw [hsum.tsum_prod' (fun i => (hw i).summable)]
      simp_rw [(hw _).tsum_eq]
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp only [c]
      exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    convert hval ▸ hsum.hasSum using 1
    · funext v
      rw [normalizedMatrixTrace_single, ← hd v.1, Complex.smul_re, smul_eq_mul]
    · rw [normalizedMatrixTrace_one τ hn]
      rfl

@[simp] theorem matrixAtomicTraceData_atom (τ : A →ₚ[ℂ] ℂ) (htr : IsTracialPositive τ)
    (hn : τ 1 = 1) (hf : ∀ a, τ (star a*a) = 0 → a = 0)
    (d : n → AtomicTraceData A V) (hd : ∀ i, (d i).trace = τ) (v : n × V) :
    ((matrixAtomicTraceData τ htr hn hf d hd).atom v).1 =
      matrixSingle v.1 v.1 ((d v.1).atom v.2).1 := rfl

open scoped ComplexOrder CStarAlgebra
variable {B n V : Type*} [CStarAlgebra B] [Fintype n] [DecidableEq n] [Nonempty n]

structure MatrixDiagonalInput (A : Type*) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (χ : B → V → ℂ) where
  trace : A →ₚ[ℂ] ℂ
  tracial : IsTracialPositive trace
  normalized : trace 1 = 1
  faithful : ∀ a, trace (star a*a) = 0 → a = 0
  data : n → AtomicTraceData A V
  sameTrace : ∀ i, (data i).trace = trace
  diagonal : n → B →⋆ₐ[ℂ] A
  atom_mul : ∀ i x v, ((data i).atom v).1 * diagonal i x = χ x v • ((data i).atom v).1
  expectation : n → A →L[ℂ] B
  bound : ∀ i a, ‖expectation i a‖ ≤ ‖a‖
  fix : ∀ i x, expectation i (diagonal i x) = x
  left : ∀ i x a, expectation i (diagonal i x * a) = x * expectation i a
  centered : ∀ i a, expectation i a = 0 → ∀ v,
    trace (((data i).atom v).1 * a * ((data i).atom v).1) = 0

variable {I : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
  (χ : B → V → ℂ) (c : ∀ j, MatrixDiagonalInput (n := n) (A j) χ)

def matrixInputData (j : I) : AtomicTraceData (CStarMatrix n n (A j)) (n × V) :=
  matrixAtomicTraceData (c j).trace (c j).tracial (c j).normalized (c j).faithful
    (c j).data (c j).sameTrace

def matrixAmalgamData (base : I)
    (weights : ∀ j i v, ((c base).trace (((c base).data i).atom v).1).re =
      ((c j).trace (((c j).data i).atom v).1).re) :
    AtomicAmalgamData (Δ := n → B) (matrixInputData χ c) where
  diagonal j := matrixDiagonalHom (c j).diagonal
  coordinate x v := χ (x v.1) v.2
  atom_mul j x v := by
    change matrixSingle v.1 v.1 _ * matrixDiagonalHom _ x = _
    rw [matrixSingle_diagonal, (c j).atom_mul, matrixSingle_smul]
    rfl
  expectation j := matrixDiagonalExpectation (c j).expectation (c j).bound
  fix j x := by
    funext i
    simp only [matrixDiagonalExpectation_apply, matrixDiagonalHom_apply, ite_true]
    exact (c j).fix i (x i)
  left j x a := by
    funext i
    simp only [matrixDiagonalExpectation_apply, matrixDiagonalHom_mul_apply, Pi.mul_apply]
    exact (c j).left i (x i) (a i i)
  centered j a ha v := by
    change normalizedMatrixTrace (c j).trace (matrixSingle v.1 v.1 _ * a *
      matrixSingle v.1 v.1 _) = 0
    rw [matrixSingle_compress, normalizedMatrixTrace_single]
    have he : (c j).expectation v.1 (a v.1 v.1) = 0 := congrFun ha v.1
    rw [(c j).centered v.1 _ he v.2, smul_zero]
  base := base
  weights j v := by
    change (normalizedMatrixTrace (c base).trace (matrixSingle v.1 v.1 _)).re =
      (normalizedMatrixTrace (c j).trace (matrixSingle v.1 v.1 _)).re
    simp only [normalizedMatrixTrace_single, Complex.smul_re, smul_eq_mul]
    rw [weights j v.1 v.2]

section
open Filter Topology
open scoped ComplexOrder CStarAlgebra OnePoint
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem AtomicTraceData.separating (d : AtomicTraceData A V) (a b : A)
    (h : ∀ r, (d.atom r).1 * a = (d.atom r).1 * b) : a = b := by
  apply sub_eq_zero.mp
  apply d.faithful
  rw [d.tracial]
  have hs := trace_hasSum_atom_corners d.trace d.tracial d.atom d.orthogonal d.mass
    ((a-b)*star (a-b))
  have hz (r : V) : d.trace ((d.atom r).1 * ((a-b)*star (a-b)) * (d.atom r).1) = 0 := by
    rw [← mul_assoc (d.atom r).1, mul_sub, h r, sub_self, zero_mul, zero_mul, map_zero]
  rw [← hs.tsum_eq]
  simp only [hz, tsum_zero]

def peakAtomicTraceData {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →ₚ[ℂ] ℂ) (htr : IsTracialPositive τ) (hn : τ 1 = 1)
    (hf : ∀ a, τ (star a*a) = 0 → a = 0)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re)
    (hlim : Tendsto (fun n => (τ (p n)).re) atTop (𝓝 0)) : AtomicTraceData A ℕ where
  trace := τ
  tracial := htr
  normalized := hn
  faithful := hf
  atom n := ⟨peakAtom p n, hp.peakAtom_projection n⟩
  orthogonal := hp.peakAtom_orthogonal
  positive := hpos
  mass := by
    apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => (hpos n).le) _).mpr
    have he n : ∑ r ∈ Finset.range n, (τ (peakAtom p r)).re = (τ 1).re - (τ (p n)).re := by
      rw [← Complex.re_sum, ← map_sum, peakAtom_sum, hp0, map_sub, Complex.sub_re]
    simp_rw [he]
    simpa using tendsto_const_nhds.sub hlim

theorem SequenceDiagonal.tendsto (g : SequenceDiagonal) :
    Tendsto (fun n : ℕ => g n) atTop (𝓝 (g ∞)) := by
  apply g.continuous.continuousAt.tendsto.comp
  simpa only [coclosedCompact_eq_cocompact, Filter.cocompact_eq_cofinite,
    Nat.cofinite_eq_atTop] using (OnePoint.tendsto_coe_infty (X := ℕ))

variable {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (hp0 : p 0 = 1)

def sequenceDiagonalMap (p : ℕ → A) (g : SequenceDiagonal) : A :=
  peakDiagonal p (g ∞) (fun n => g n)

include hp hp0 in
theorem sequenceDiagonalMap_norm_le (g : SequenceDiagonal) :
    ‖sequenceDiagonalMap p g‖ ≤ ‖g‖ := by
  exact hp.norm_peakDiagonal_le hp0 _ _ g.tendsto ‖g‖ (norm_nonneg _)
    (ContinuousMap.norm_coe_le_norm g ∞) (fun n => ContinuousMap.norm_coe_le_norm g n)

include hp in

theorem sequenceDiagonalMap_atom (g : SequenceDiagonal) (n : ℕ) :
    peakAtom p n * sequenceDiagonalMap p g = g n • peakAtom p n := by
  change peakAtom p n * ((g ∞) • (1 : A) + ∑' i : ℕ, (g i - g ∞) • peakAtom p i) = _
  rw [mul_add, mul_smul_comm, mul_one,
    orthogonalProjection_mul_tsum _ hp.peakAtom_projection hp.peakAtom_orthogonal
      (fun i : ℕ => g i - g ∞) (by simpa using g.tendsto.sub_const (g ∞)) n,
    ← add_smul, add_sub_cancel]

include hp in

theorem sequenceDiagonalMap_mem (g : SequenceDiagonal) :
    sequenceDiagonalMap p g ∈ peakAlgebra p := by
  apply (StarSubalgebra.isClosed_topologicalClosure _).mem_of_tendsto
    (hp.tendsto_peakDiagonal (g ∞) (fun n => g n) g.tendsto)
  apply Filter.Eventually.of_forall
  intro n
  exact (peakAlgebra p).add_mem ((peakAlgebra p).smul_mem (one_mem _) _)
    ((peakAlgebra p).sum_mem fun r _ => (peakAlgebra p).smul_mem
      (peakAtom_mem_peakAlgebra p r) _)

include hp in
theorem sequenceDiagonalMap_atom_right (g : SequenceDiagonal) (n : ℕ) :
    sequenceDiagonalMap p g * peakAtom p n = g n • peakAtom p n := by
  have hs := summable_orthogonalProjection _ hp.peakAtom_projection hp.peakAtom_orthogonal
    (fun i : ℕ => g i - g ∞) (by simpa using g.tendsto.sub_const (g ∞))
  change ((g ∞) • (1 : A) + ∑' i : ℕ, (g i - g ∞) • peakAtom p i) * peakAtom p n = _
  rw [add_mul, smul_mul_assoc, one_mul, ← hs.tsum_mul_right]
  have he : (∑' i : ℕ, ((g i - g ∞) • peakAtom p i) * peakAtom p n) =
      (g n - g ∞) • peakAtom p n := by
    rw [tsum_eq_single n]
    · rw [smul_mul_assoc, (hp.peakAtom_projection n).isIdempotentElem.eq]
    · intro i hi
      rw [smul_mul_assoc, hp.peakAtom_orthogonal hi, smul_zero]
  rw [he, ← add_smul, add_sub_cancel]

variable (d : AtomicTraceData A ℕ) (hd : ∀ n, (d.atom n).1 = peakAtom p n)
include hd

theorem peakAtom_separating (a b : A)
    (h : ∀ n, peakAtom p n * a = peakAtom p n * b) : a = b := by
  apply d.separating
  simpa only [hd] using h

include hp in

def sequenceDiagonalHom : SequenceDiagonal →⋆ₐ[ℂ] A where
  toFun := sequenceDiagonalMap p
  map_one' := by
    apply peakAtom_separating d hd
    intro n
    rw [sequenceDiagonalMap_atom hp, mul_one]
    simp only [ContinuousMap.one_apply, one_smul]
  map_mul' g h := by
    apply peakAtom_separating d hd
    intro n
    rw [sequenceDiagonalMap_atom hp, ContinuousMap.mul_apply, ← mul_assoc,
      sequenceDiagonalMap_atom hp, smul_mul_assoc, sequenceDiagonalMap_atom hp,
      smul_smul]
  map_zero' := by
    apply peakAtom_separating d hd
    intro n
    rw [sequenceDiagonalMap_atom hp, ContinuousMap.zero_apply, zero_smul, mul_zero]
  map_add' g h := by
    apply peakAtom_separating d hd
    intro n
    rw [sequenceDiagonalMap_atom hp, ContinuousMap.add_apply, mul_add,
      sequenceDiagonalMap_atom hp, sequenceDiagonalMap_atom hp, add_smul]
  commutes' z := by
    apply peakAtom_separating d hd
    intro n
    rw [sequenceDiagonalMap_atom hp]
    change z • peakAtom p n = peakAtom p n * algebraMap ℂ A z
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  map_star' g := by
    apply peakAtom_separating d hd
    intro n
    rw [sequenceDiagonalMap_atom hp, ContinuousMap.star_apply]
    have h := congrArg star (sequenceDiagonalMap_atom_right hp g n)
    rw [star_mul, (hp.peakAtom_projection n).isSelfAdjoint.star_eq,
      star_smul, (hp.peakAtom_projection n).isSelfAdjoint.star_eq] at h
    exact h.symm

include hp in
theorem sequenceDiagonalHom_injective : Function.Injective (sequenceDiagonalHom hp d hd) := by
  intro g h he
  have hf (n : ℕ) : g n = h n := by
    have hq : peakAtom p n ≠ 0 := by
      intro hz
      have hp' := d.positive n
      rw [hd, hz, map_zero, Complex.zero_re] at hp'
      exact lt_irrefl 0 hp'
    apply smul_left_injective ℂ hq
    change g n • peakAtom p n = h n • peakAtom p n
    rw [← sequenceDiagonalMap_atom hp, ← sequenceDiagonalMap_atom hp]
    exact congrArg (peakAtom p n * ·) he
  ext n
  induction n using OnePoint.rec with
  | infty => exact tendsto_nhds_unique g.tendsto (by simpa only [hf] using h.tendsto)
  | coe n => exact hf n

end

section
open Filter Topology
open scoped ComplexOrder CStarAlgebra OnePoint
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (hp0 : p 0 = 1)
variable (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ n, 0 < (τ (peakAtom p n)).re)

variable (d : AtomicTraceData A ℕ) (hd : ∀ n, (d.atom n).1 = peakAtom p n)

theorem sequenceDiagonalHom_peakingCoefficients (a : A) :
    sequenceDiagonalHom hp d hd (peakingCoefficients hp τ hτ hpos a) =
      peakingExpectation hp hp0 τ hτ hpos a := rfl

include hp0 in
theorem peakingCoefficients_fixes (g : SequenceDiagonal) :
    peakingCoefficients hp τ hτ hpos (sequenceDiagonalHom hp d hd g) = g := by
  apply sequenceDiagonalHom_injective hp d hd
  rw [sequenceDiagonalHom_peakingCoefficients hp hp0]
  exact peakingExpectation_fixes hp hp0 τ hτ hpos _ (sequenceDiagonalMap_mem hp g)

include hp0 in
theorem peakingCoefficients_left (g : SequenceDiagonal) (a : A) :
    peakingCoefficients hp τ hτ hpos (sequenceDiagonalHom hp d hd g * a) =
      g * peakingCoefficients hp τ hτ hpos a := by
  apply sequenceDiagonalHom_injective hp d hd
  rw [map_mul (sequenceDiagonalHom hp d hd), sequenceDiagonalHom_peakingCoefficients hp hp0,
    sequenceDiagonalHom_peakingCoefficients hp hp0]
  exact peakingExpectation_leftBimodule hp hp0 τ hτ hpos _ _ (sequenceDiagonalMap_mem hp g)

include hp0 τ hτ hpos in

theorem sequenceDiagonalHom_range : (sequenceDiagonalHom hp d hd).range = peakAlgebra p := by
  apply le_antisymm
  · rintro a ⟨g,rfl⟩
    exact sequenceDiagonalMap_mem hp g
  · intro a ha
    refine ⟨peakingCoefficients hp τ hτ hpos a, ?_⟩
    change sequenceDiagonalHom hp d hd (peakingCoefficients hp τ hτ hpos a) = a
    rw [sequenceDiagonalHom_peakingCoefficients hp hp0]
    exact peakingExpectation_fixes hp hp0 τ hτ hpos a ha

theorem peakingCoefficients_zero_corners (a : A)
    (ha : peakingCoefficients hp τ hτ hpos a = 0) (n : ℕ) :
    τ (peakAtom p n * a * peakAtom p n) = 0 := by
  have h := congrArg (fun g : SequenceDiagonal => g n) ha
  change (τ (peakAtom p n)).re⁻¹ • τ (peakAtom p n * a * peakAtom p n) = 0 at h
  exact (smul_eq_zero.mp h).resolve_left (inv_ne_zero (ne_of_gt (hpos n)))

end

open scoped ComplexOrder CStarAlgebra
variable {A B V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def positivePullback (τ : A →ₚ[ℂ] ℂ) (φ : B →⋆ₐ[ℂ] A) : B →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (τ.toLinearMap.comp φ.toLinearMap) (by
    intro b hb
    obtain ⟨c, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hb
    change 0 ≤ τ (φ (star c*c))
    rw [map_mul, map_star]
    exact τ.map_nonneg (star_mul_self_nonneg _))

@[simp] theorem positivePullback_apply (τ : A →ₚ[ℂ] ℂ) (φ : B →⋆ₐ[ℂ] A) (b : B) :
    positivePullback τ φ b = τ (φ b) := rfl

def AtomicTraceData.pullback (d : AtomicTraceData A V) (φ : B →⋆ₐ[ℂ] A)
    (hinj : Function.Injective φ) (p : V → B) (hp : ∀ v, φ (p v) = (d.atom v).1) :
    AtomicTraceData B V where
  trace := positivePullback d.trace φ
  tracial a b := by simp only [positivePullback_apply, map_mul]; exact d.tracial _ _
  normalized := by simpa only [positivePullback_apply, map_one] using d.normalized
  faithful b hb := by
    apply hinj
    rw [map_zero]
    apply d.faithful
    simpa only [positivePullback_apply, map_mul, map_star] using hb
  atom v := ⟨p v, by
    refine ⟨?_, ?_⟩
    · apply hinj
      simpa only [map_mul, hp] using (d.atom v).2.isIdempotentElem.eq
    · apply hinj
      simpa only [map_star, hp] using (d.atom v).2.isSelfAdjoint.star_eq⟩
  orthogonal v w h := by
    apply hinj
    simpa only [map_mul, hp, map_zero] using d.orthogonal v w h
  positive v := by simpa only [positivePullback_apply, hp] using d.positive v
  mass := by simpa only [positivePullback_apply, hp, map_one] using d.mass

@[simp] theorem AtomicTraceData.pullback_atom (d : AtomicTraceData A V) (φ : B →⋆ₐ[ℂ] A)
    (hinj : Function.Injective φ) (p : V → B) (hp : ∀ v, φ (p v) = (d.atom v).1) (v : V) :
    ((d.pullback φ hinj p hp).atom v).1 = p v := rfl

section
open Filter Topology
open scoped OnePoint ComplexOrder CStarAlgebra
variable {A n : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n] [Nonempty n]

theorem positiveCLM_isState (τ : A →ₚ[ℂ] ℂ) (hn : τ 1 = 1) : IsState (positiveCLM τ) := by
  rw [isState_iff]
  refine ⟨hn, fun a => ?_⟩
  have h := τ.map_nonneg (star_mul_self_nonneg a)
  exact ⟨h.2.symm,h.1⟩

variable (τ : A →ₚ[ℂ] ℂ) (htr : IsTracialPositive τ) (hn : τ 1 = 1)
  (hf : ∀ a, τ (star a*a) = 0 → a = 0)
  (p : n → ℕ → A) (f : n → A →L[ℂ] ℂ) (hp : ∀ i, Peaks (p i) (f i))
  (hp0 : ∀ i, p i 0 = 1) (hpos : ∀ i v, 0 < (τ (peakAtom (p i) v)).re)
  (hlim : ∀ i, Tendsto (fun v => (τ (p i v)).re) atTop (𝓝 0))

def peakingMatrixInput : MatrixDiagonalInput (n := n) A (fun x : SequenceDiagonal => fun v : ℕ => x v) where
  trace := τ
  tracial := htr
  normalized := hn
  faithful := hf
  data i := peakAtomicTraceData (hp i) (hp0 i) τ htr hn hf (hpos i) (hlim i)
  sameTrace _ := rfl
  diagonal i := sequenceDiagonalHom (hp i)
    (peakAtomicTraceData (hp i) (hp0 i) τ htr hn hf (hpos i) (hlim i)) (fun _ => rfl)
  atom_mul i x v := sequenceDiagonalMap_atom (hp i) x v
  expectation i := peakingCoefficients (hp i) (positiveCLM τ) (positiveCLM_isState τ hn) (hpos i)
  bound i a := peakingCoefficientsFun_norm_le (hp i) (positiveCLM τ) (positiveCLM_isState τ hn) (hpos i) a
  fix i x := peakingCoefficients_fixes (hp i) (hp0 i) (positiveCLM τ)
    (positiveCLM_isState τ hn) (hpos i) _ (fun _ => rfl) x
  left i x a := peakingCoefficients_left (hp i) (hp0 i) (positiveCLM τ)
    (positiveCLM_isState τ hn) (hpos i) _ (fun _ => rfl) x a
  centered i a ha v := peakingCoefficients_zero_corners (hp i) (positiveCLM τ)
    (positiveCLM_isState τ hn) (hpos i) a ha v

end

section
open Filter Topology
open scoped OnePoint ComplexOrder CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (hp0 : p 0 = 1)
variable (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ v, 0 < (τ (peakAtom p v)).re)
variable (d : AtomicTraceData A ℕ) (hd : ∀ v, (d.atom v).1 = peakAtom p v)

def sequenceAtom (v : ℕ) : SequenceDiagonal := peakingCoefficients hp τ hτ hpos (peakAtom p v)

include hp0 in
@[simp] theorem sequenceDiagonalHom_sequenceAtom (v : ℕ) :
    sequenceDiagonalHom hp d hd (sequenceAtom hp τ hτ hpos v) = peakAtom p v := by
  rw [sequenceAtom, sequenceDiagonalHom_peakingCoefficients hp hp0]
  exact peakingExpectation_fixes hp hp0 τ hτ hpos _ (peakAtom_mem_peakAlgebra p v)

def sequenceAtomicTraceData : AtomicTraceData SequenceDiagonal ℕ :=
  d.pullback (sequenceDiagonalHom hp d hd) (sequenceDiagonalHom_injective hp d hd)
    (sequenceAtom hp τ hτ hpos) (fun v => by
      rw [sequenceDiagonalHom_sequenceAtom hp hp0 τ hτ hpos d hd, hd])

theorem sequenceAtomicTraceData_atom_mul (x : SequenceDiagonal) (v : ℕ) :
    ((sequenceAtomicTraceData hp hp0 τ hτ hpos d hd).atom v).1 * x =
      x v • ((sequenceAtomicTraceData hp hp0 τ hτ hpos d hd).atom v).1 := by
  apply sequenceDiagonalHom_injective hp d hd
  change sequenceDiagonalHom hp d hd (sequenceAtom hp τ hτ hpos v * x) =
    sequenceDiagonalHom hp d hd (x v • sequenceAtom hp τ hτ hpos v)
  rw [map_mul, map_smul, sequenceDiagonalHom_sequenceAtom hp hp0]
  exact sequenceDiagonalMap_atom hp x v

def sequenceMatrixInput {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] :
    MatrixDiagonalInput (n := n) SequenceDiagonal (fun x : SequenceDiagonal => fun v : ℕ => x v) where
  trace := (sequenceAtomicTraceData hp hp0 τ hτ hpos d hd).trace
  tracial := (sequenceAtomicTraceData hp hp0 τ hτ hpos d hd).tracial
  normalized := (sequenceAtomicTraceData hp hp0 τ hτ hpos d hd).normalized
  faithful := (sequenceAtomicTraceData hp hp0 τ hτ hpos d hd).faithful
  data _ := sequenceAtomicTraceData hp hp0 τ hτ hpos d hd
  sameTrace _ := rfl
  diagonal _ := StarAlgHom.id ℂ SequenceDiagonal
  atom_mul _ x v := sequenceAtomicTraceData_atom_mul hp hp0 τ hτ hpos d hd x v
  expectation _ := ContinuousLinearMap.id ℂ SequenceDiagonal
  bound _ _ := le_rfl
  fix _ _ := rfl
  left _ _ _ := rfl
  centered _ a ha v := by
    change a = 0 at ha
    simp only [ha, mul_zero, zero_mul, map_zero]

end

section
open Filter Topology
open scoped OnePoint ComplexOrder CStarAlgebra

abbrev HNNFactor (A : Type) : Bool → Type _
  | false => A
  | true => SequenceDiagonal

instance {A : Type} [CStarAlgebra A] : (j : Bool) → CStarAlgebra (HNNFactor A j)
  | false => inferInstanceAs (CStarAlgebra A)
  | true => inferInstanceAs (CStarAlgebra SequenceDiagonal)
instance {A : Type} [CStarAlgebra A] [PartialOrder A] :
    (j : Bool) → PartialOrder (HNNFactor A j)
  | false => inferInstanceAs (PartialOrder A)
  | true => inferInstanceAs (PartialOrder SequenceDiagonal)
instance {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    (j : Bool) → StarOrderedRing (HNNFactor A j)
  | false => inferInstanceAs (StarOrderedRing A)
  | true => inferInstanceAs (StarOrderedRing SequenceDiagonal)

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (htr : IsTracialPositive τ) (hn : τ 1 = 1)
  (hf : ∀ a, τ (star a*a) = 0 → a = 0)
  (p : Bool → ℕ → A) (f : Bool → A →L[ℂ] ℂ) (hp : ∀ i, Peaks (p i) (f i))
  (hp0 : ∀ i, p i 0 = 1) (hpos : ∀ i v, 0 < (τ (peakAtom (p i) v)).re)
  (hlim : ∀ i, Tendsto (fun v => (τ (p i v)).re) atTop (𝓝 0))

def hnnMatrixInput : (j : Bool) → MatrixDiagonalInput (n := Bool) (HNNFactor A j)
    (fun x : SequenceDiagonal => fun v : ℕ => x v)
  | false => peakingMatrixInput τ htr hn hf p f hp hp0 hpos hlim
  | true => sequenceMatrixInput (hp false) (hp0 false) (positiveCLM τ)
      (positiveCLM_isState τ hn) (hpos false)
      (peakAtomicTraceData (hp false) (hp0 false) τ htr hn hf (hpos false) (hlim false))
      (fun _ => rfl)

variable (hmatch : ∀ i v, τ (p i v) = τ (p false v))

include hmatch in

theorem hnnMatrixInput_weights (j i : Bool) (v : ℕ) :
    ((hnnMatrixInput τ htr hn hf p f hp hp0 hpos hlim false).trace
      (((hnnMatrixInput τ htr hn hf p f hp hp0 hpos hlim false).data i).atom v).1).re =
    ((hnnMatrixInput τ htr hn hf p f hp hp0 hpos hlim j).trace
      (((hnnMatrixInput τ htr hn hf p f hp hp0 hpos hlim j).data i).atom v).1).re := by
  cases j
  · rfl
  · have he := sequenceDiagonalHom_sequenceAtom (hp false) (hp0 false)
      (positiveCLM τ) (positiveCLM_isState τ hn) (hpos false)
      (peakAtomicTraceData (hp false) (hp0 false) τ htr hn hf (hpos false) (hlim false))
      (fun _ => rfl) v
    have ht : τ (peakAtom (p i) v) = τ (peakAtom (p false) v) := by
      simp only [peakAtom, map_sub, hmatch]
    exact congrArg Complex.re (ht.trans (congrArg τ he).symm)

def hnnAmalgamData : AtomicAmalgamData (Δ := Bool → SequenceDiagonal)
    (matrixInputData (fun x : SequenceDiagonal => fun v : ℕ => x v)
      (hnnMatrixInput τ htr hn hf p f hp hp0 hpos hlim)) :=
  matrixAmalgamData _ _ false (hnnMatrixInput_weights τ htr hn hf p f hp hp0 hpos hlim hmatch)

end

end NaimarkZFC

end

end OAI
