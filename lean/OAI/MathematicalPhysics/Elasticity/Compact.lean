import Mathlib

namespace OAI

section
noncomputable section
open Set Filter Topology
namespace ElasticityCompact
variable {A P F : Type*} [TopologicalSpace A] [CompactSpace A]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Interchanging a compact continuous-variable slot and a bounded linear slot. -/
def flipLinear (q : C(A,P →L[ℝ] F)) : P →L[ℝ] C(A,F) :=
  LinearMap.mkContinuous
    ({ toFun := fun p => ⟨fun a => q a p,q.continuous.clm_apply continuous_const⟩
       map_add' := fun v w => by ext a; exact map_add (q a) v w
       map_smul' := fun c v => by ext a; exact map_smul (q a) c v } : P →ₗ[ℝ] C(A,F))
    ‖q‖ (fun p => by
      change ‖(⟨fun a => q a p,q.continuous.clm_apply continuous_const⟩ : C(A,F))‖ ≤ ‖q‖ * ‖p‖
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg q) (norm_nonneg p))).mpr
      intro a
      exact (q a).le_opNorm p |>.trans (mul_le_mul_of_nonneg_right
        (q.norm_coe_le_norm a) (norm_nonneg p)))
lemma flipLinear_apply (q : C(A,P →L[ℝ] F)) (p : P) (a : A) : flipLinear q p a=q a p := rfl

def flipCLM : C(A,P →L[ℝ] F) →L[ℝ] (P →L[ℝ] C(A,F)) :=
  LinearMap.mkContinuous
    ({ toFun := fun q : C(A,P →L[ℝ] F) => flipLinear q
       map_add' := fun q r => by ext p a; rfl
       map_smul' := fun c q => by ext p a; rfl } :
      C(A,P →L[ℝ] F) →ₗ[ℝ] (P →L[ℝ] C(A,F))) 1 (fun q : C(A,P →L[ℝ] F) => by
        change ‖flipLinear q‖ ≤ 1 * ‖q‖
        rw [one_mul]
        apply ContinuousLinearMap.opNorm_le_bound (flipLinear q) (norm_nonneg q)
        intro p
        exact
          (ContinuousMap.norm_le (flipLinear q p) (mul_nonneg (norm_nonneg q) (norm_nonneg p))).mpr
            (fun a => (q a).le_opNorm p |>.trans
              (mul_le_mul_of_nonneg_right (q.norm_coe_le_norm a) (norm_nonneg p))))

lemma hasFDerivAt_compact (f : P → C(A,F)) (q : P → C(A,P →L[ℝ] F))
    (hq : Continuous q)
    (hd : ∀ p a, HasFDerivAt (fun p => f p a) (q p a) p) (p : P) :
    HasFDerivAt f (flipLinear (q p)) p := by
  rw [hasFDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨r,hr,he⟩ := (Metric.continuousAt_iff (f := q) (a := p)).mp hq.continuousAt ε hε
  filter_upwards [Metric.ball_mem_nhds p hr] with y hy
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro a
  have hb (z : P) (hz : z∈Metric.ball p r) : ‖q z a-q p a‖ ≤ ε := by
    have hh := le_of_lt (he hz)
    simpa only [dist_eq_norm] using (ContinuousMap.dist_apply_le_dist (f := q z) (g := q p) a).trans hh
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z _ => (hd z a).hasFDerivWithinAt) hb (convex_ball p r)
    (Metric.mem_ball_self hr) hy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def curryCompact (f : P × E → F) (hf : Continuous f) (j : A → E) (hj : Continuous j) :
    P → C(A,F) :=
  fun p => ⟨fun a => f (p,j a),hf.comp (continuous_const.prodMk hj)⟩
omit [CompactSpace A] [NormedSpace ℝ P] [NormedSpace ℝ F] [NormedSpace ℝ E] in
lemma curryCompact_apply (f : P × E → F) (hf : Continuous f) (j : A → E) (hj : Continuous j)
    (p : P) (a : A) : curryCompact f hf j hj p a=f (p,j a) := rfl
omit [CompactSpace A] [NormedSpace ℝ P] [NormedSpace ℝ F] [NormedSpace ℝ E] in
lemma curryCompact_continuous (f : P × E → F) (hf : Continuous f) (j : A → E) (hj : Continuous j) :
    Continuous (curryCompact f hf j hj) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact hf.comp (continuous_fst.prodMk (hj.comp continuous_snd))

lemma curryCompact_hasFDerivAt (f : P × E → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (j : A → E) (hj : Continuous j) (p : P) :
    HasFDerivAt (curryCompact f hf.continuous j hj)
      (flipLinear ⟨fun a => (fderiv ℝ f (p,j a)).comp (ContinuousLinearMap.inl ℝ P E),
        ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.comp (continuous_const.prodMk hj)).clm_comp continuous_const⟩) p := by
  let q : P → C(A,P →L[ℝ] F) := fun p =>
    ⟨fun a => (fderiv ℝ f (p,j a)).comp (ContinuousLinearMap.inl ℝ P E),
      ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.comp (continuous_const.prodMk hj)).clm_comp continuous_const⟩
  apply hasFDerivAt_compact _ q ?_ ?_ p
  · apply ContinuousMap.continuous_of_continuous_uncurry
    exact ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.comp
      (continuous_fst.prodMk (hj.comp continuous_snd))).clm_comp continuous_const
  · intro p a
    exact (hf.differentiable (by simp) (p,j a)).hasFDerivAt.comp p
      ((hasFDerivAt_id p).prodMk (hasFDerivAt_const (j a) p))

/-- Smooth currying over a compact set. This supplies the Banach-space parameter
regularity needed for the actual coefficient multipliers and linear ODE. -/
theorem curryCompact_contDiff [FiniteDimensional ℝ P]
    (f : P × E → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : A → E) (hj : Continuous j) :
    ContDiff ℝ (⊤ : ℕ∞) (curryCompact f hf.continuous j hj) := by
  apply contDiff_infty.mpr
  intro n
  induction n generalizing f with
  | zero =>
    simp only [Nat.cast_zero,contDiff_zero]
    exact curryCompact_continuous f hf.continuous j hj
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_fderiv_apply]
    refine ⟨fun p => (curryCompact_hasFDerivAt f hf j hj p).differentiableAt,by simp,fun v => ?_⟩
    let f' : P × E → F := fun q => fderiv ℝ f q (v,0)
    have hf' : ContDiff ℝ (⊤ : ℕ∞) f' := (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
    have he : (fun p => fderiv ℝ (curryCompact f hf.continuous j hj) p v)=
        curryCompact f' hf'.continuous j hj := by
      funext p
      ext a
      rw [(curryCompact_hasFDerivAt f hf j hj p).fderiv]
      rfl
    rw [he]
    exact ih f' hf'
end ElasticityCompact

end
end
section
noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal
namespace ElasticityCompact
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {S : Set E} [CompactSpace S]
def zeroExtend (f : C(S,ℂ)) : E → ℂ := Function.extend Subtype.val f 0
omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompactSpace S] in
lemma zeroExtend_mem (f : C(S,ℂ)) (x : S) : zeroExtend f x=f x :=
  Subtype.val_injective.extend_apply f 0 x
omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompactSpace S] in
lemma zeroExtend_notMem (f : C(S,ℂ)) {x : E} (hx : x∉S) : zeroExtend f x=0 := by
  apply Function.extend_apply'
  rintro ⟨y,rfl⟩
  exact hx y.property
omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma zeroExtend_norm (f : C(S,ℂ)) (x : E) : ‖zeroExtend f x‖ ≤ ‖f‖ := by
  by_cases hx : x∈S
  · exact (zeroExtend_mem f ⟨x,hx⟩) ▸ f.norm_coe_le_norm ⟨x,hx⟩
  · rw [zeroExtend_notMem f hx,norm_zero]; exact norm_nonneg _
omit [NormedSpace ℝ E] in
lemma zeroExtend_memLp (hS : MeasurableSet S) (μ : Measure E) (f : C(S,ℂ)) :
    MemLp (zeroExtend f) ∞ μ := by
  apply memLp_top_of_bound _ ‖f‖ (Eventually.of_forall (zeroExtend_norm f))
  exact ((MeasurableEmbedding.subtype_coe hS).stronglyMeasurable_extend
    f.continuous.stronglyMeasurable stronglyMeasurable_const).aestronglyMeasurable
omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompactSpace S] in
lemma zeroExtend_add (f g : C(S,ℂ)) : zeroExtend (f+g)=zeroExtend f+zeroExtend g := by
  funext x
  by_cases hx : x∈S
  · change zeroExtend (f+g) (⟨x,hx⟩ : S)=zeroExtend f (⟨x,hx⟩ : S)+zeroExtend g (⟨x,hx⟩ : S)
    rw [zeroExtend_mem (f+g) ⟨x,hx⟩,zeroExtend_mem f ⟨x,hx⟩,zeroExtend_mem g ⟨x,hx⟩]
    rfl
  · simp only [Pi.add_apply,zeroExtend_notMem _ hx,add_zero]
omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompactSpace S] in
lemma zeroExtend_smul (c : ℂ) (f : C(S,ℂ)) : zeroExtend (c • f)=c • zeroExtend f := by
  funext x
  by_cases hx : x∈S
  · change zeroExtend (c • f) (⟨x,hx⟩ : S)=c • zeroExtend f (⟨x,hx⟩ : S)
    rw [zeroExtend_mem (c • f) ⟨x,hx⟩,zeroExtend_mem f ⟨x,hx⟩]
    rfl
  · simp only [Pi.smul_apply,zeroExtend_notMem _ hx,smul_zero]
def toLinfCompact (hS : MeasurableSet S) (μ : Measure E) : C(S,ℂ) →L[ℂ] Lp ℂ ∞ μ :=
  LinearMap.mkContinuous
    ({ toFun := fun f => (zeroExtend_memLp hS μ f).toLp (zeroExtend f)
       map_add' := fun f g => by
         apply Lp.ext
         filter_upwards [MemLp.coeFn_toLp (zeroExtend_memLp hS μ (f+g)),
           MemLp.coeFn_toLp (zeroExtend_memLp hS μ f),MemLp.coeFn_toLp (zeroExtend_memLp hS μ g),
           Lp.coeFn_add ((zeroExtend_memLp hS μ f).toLp _) ((zeroExtend_memLp hS μ g).toLp _)] with x ha hb hc hd
         rw [ha,hd]
         simp only [Pi.add_apply,hb,hc,zeroExtend_add]
       map_smul' := fun c f => by
         apply Lp.ext
         filter_upwards [MemLp.coeFn_toLp (zeroExtend_memLp hS μ (c • f)),
           MemLp.coeFn_toLp (zeroExtend_memLp hS μ f),
           Lp.coeFn_smul c ((zeroExtend_memLp hS μ f).toLp _)] with x ha hb hc
         simp only [RingHom.id_apply]
         rw [ha,hc]
         simp only [Pi.smul_apply,hb,zeroExtend_smul] } : C(S,ℂ) →ₗ[ℂ] Lp ℂ ∞ μ) 1 (fun f => by
      rw [one_mul]
      change ‖(zeroExtend_memLp hS μ f).toLp (zeroExtend f)‖ ≤ ‖f‖
      rw [Lp.norm_toLp]
      have h := eLpNorm_le_of_ae_bound (p := ∞) (μ := μ)
        (zeroExtend_memLp hS μ f).aestronglyMeasurable
        (Eventually.of_forall (zeroExtend_norm f))
      simp only [ENNReal.toReal_top,inv_zero,ENNReal.rpow_zero,one_mul] at h
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq
        (ENNReal.toReal_ofReal (norm_nonneg f)))
omit [NormedSpace ℝ E] in
lemma toLinfCompact_ae (hS : MeasurableSet S) (μ : Measure E) (f : C(S,ℂ)) :
    toLinfCompact hS μ f =ᵐ[μ] zeroExtend f := MemLp.coeFn_toLp (zeroExtend_memLp hS μ f)
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
/-- A joint smooth family with a fixed compact spatial support is genuinely
smooth with values in L-infinity, not merely pointwise smooth. -/
theorem exists_smooth_linf_family (hS : MeasurableSet S) (μ : Measure E)
    (a : P × E → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hs : ∀ p x, x∉S → a (p,x)=0) :
    ∃ b : P → Lp ℂ ∞ μ, ContDiff ℝ (⊤ : ℕ∞) b ∧ ∀ p, b p =ᵐ[μ] fun x => a (p,x) := by
  let f := curryCompact a ha.continuous (fun x : S => (x:E)) continuous_subtype_val
  have hf := curryCompact_contDiff a ha (fun x : S => (x:E)) continuous_subtype_val
  refine ⟨fun p => toLinfCompact hS μ (f p),?_,fun p => ?_⟩
  · have hL : ContDiff ℝ (⊤ : ℕ∞) (toLinfCompact hS μ) :=
      (toLinfCompact hS μ).restrictScalars ℝ |>.contDiff
    exact hL.comp hf
  · apply (toLinfCompact_ae hS μ (f p)).trans
    apply Eventually.of_forall
    intro x
    by_cases hx : x∈S
    · exact zeroExtend_mem (f p) ⟨x,hx⟩
    · rw [zeroExtend_notMem _ hx]
      change 0=a (p,x)
      exact (hs p x hx).symm
end ElasticityCompact

end
end

end OAI
