import Mathlib
import OAI.MathematicalPhysics.BFSS.OscillatorForms

namespace OAI

/-! Weighted Sobolev form closure and normal oscillator nonnegativity. -/

namespace BFSSSliceSobolev
noncomputable section
open MeasureTheory Set Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
variable {ι : Type*} [Fintype ι] (e : ι → E)

def weightedToL2 (w : E → ℝ) (hw : Continuous w) (f : Core (E := E) (F := F)) : Lp F 2 μ :=
  ((hw.smul f.continuous).memLp_of_hasCompactSupport f.hasCompactSupport.smul_left).toLp
    (fun x => w x • f x)

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma weightedToL2_ae (w : E → ℝ) (hw : Continuous w) (f : Core (E := E) (F := F)) :
    (weightedToL2 μ w hw f : E → F) =ᵐ[μ] fun x => w x • f x := MemLp.coeFn_toLp _

def weightedClosure (w : E → ℝ) (hw : Continuous w) :
    Set (Lp F 2 μ × Gradient (F := F) μ (ι := ι) × Lp F 2 μ) :=
  closure (Set.range fun f : Core (E := E) (F := F) =>
    (toL2 μ f,gradient μ e f,weightedToL2 μ w hw f))

def coreMul (χ : Core (E := E) (F := ℝ)) (f : Core (E := E) (F := F)) : Core (E := E) (F := F) :=
  ⟨fun x => χ x • f x,χ.contDiff.smul f.contDiff,f.hasCompactSupport.smul_left,
    by intro x hx; trivial⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma coreMul_apply (χ : Core (E := E) (F := ℝ)) (f : Core (E := E) (F := F)) (x : E) :
    coreMul χ f x = χ x • f x := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma coreMul_derivative (χ : Core (E := E) (F := ℝ)) (f : Core (E := E) (F := F)) (v : E) (x : E) :
    (TestFunction.lineDerivCLM (k := ⊤) ℝ v (coreMul χ f)) x =
      χ x • (TestFunction.lineDerivCLM (k := ⊤) ℝ v f) x +
      (TestFunction.lineDerivCLM (k := ⊤) ℝ v χ) x • f x := by
  change fderiv ℝ (fun x => χ x • f x) x v =
    χ x • fderiv ℝ (f : E → F) x v + fderiv ℝ (χ : E → ℝ) x v • f x
  rw [fderiv_fun_smul (χ.contDiff.differentiable (by simp) x)
    (f.contDiff.differentiable (by simp) x)]
  rfl

abbrev scalarMul (χ : Core (E := E) (F := ℝ)) (u : Lp F 2 μ) : Lp F 2 μ :=
  BFSSLocalL2.compactMul χ χ.continuous χ.hasCompactSupport u

def cutoffGradient (χ : Core (E := E) (F := ℝ)) (u : Lp F 2 μ)
    (v : Gradient (F := F) μ (ι := ι)) : Gradient (F := F) μ (ι := ι) :=
  WithLp.toLp 2 (fun j => scalarMul μ χ (v j) + scalarMul μ (TestFunction.lineDerivCLM (k := ⊤) ℝ (e j) χ) u)

def cutoffMoment (w : E → ℝ) (hw : Continuous w) (χ : Core (E := E) (F := ℝ)) (u : Lp F 2 μ) : Lp F 2 μ :=
  BFSSLocalL2.compactMul (fun x => w x * χ x) (hw.mul χ.continuous) χ.hasCompactSupport.mul_left u

omit [FiniteDimensional ℝ E] [CompleteSpace F] [IsFiniteMeasureOnCompacts μ] [Fintype ι] in
lemma cutoffGradient_continuous (χ : Core (E := E) (F := ℝ)) :
    Continuous (fun p : Lp F 2 μ × Gradient (F := F) μ (ι := ι) => cutoffGradient μ e χ p.1 p.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro j
  exact ((BFSSLocalL2.compactMul_continuous _ _ _).comp
    ((PiLp.continuous_apply 2 _ j).comp continuous_snd)).add
    ((BFSSLocalL2.compactMul_continuous _ _ _).comp continuous_fst)

omit [FiniteDimensional ℝ E] [CompleteSpace F] [Fintype ι] in
lemma cutoff_core_tuple (w : E → ℝ) (hw : Continuous w) (χ : Core (E := E) (F := ℝ))
    (f : Core (E := E) (F := F)) :
    (toL2 μ (coreMul χ f),gradient μ e (coreMul χ f),weightedToL2 μ w hw (coreMul χ f)) =
      (scalarMul μ χ (toL2 μ f),cutoffGradient μ e χ (toL2 μ f) (gradient μ e f),
        cutoffMoment μ w hw χ (toL2 μ f)) := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [toL2_ae μ (coreMul χ f),BFSSLocalL2.compactMul_ae χ χ.continuous χ.hasCompactSupport (toL2 μ f),toL2_ae μ f] with x h₁ h₂ h₃
    rw [h₁,h₂,h₃,coreMul_apply]
  apply Prod.ext
  · apply PiLp.ext
    intro j
    apply Lp.ext
    filter_upwards [toL2_ae μ (TestFunction.lineDerivCLM (k := ⊤) ℝ (e j) (coreMul χ f)),
      BFSSLocalL2.compactMul_ae χ χ.continuous χ.hasCompactSupport (gradient μ e f j),
      BFSSLocalL2.compactMul_ae _ _ _ (toL2 μ f),
      toL2_ae μ (TestFunction.lineDerivCLM (k := ⊤) ℝ (e j) f),toL2_ae μ f,
      Lp.coeFn_add (scalarMul μ χ (gradient μ e f j))
        (scalarMul μ (TestFunction.lineDerivCLM (k := ⊤) ℝ (e j) χ) (toL2 μ f))] with x h₁ h₂ h₃ h₄ h₅ h₆
    change (toL2 μ (TestFunction.lineDerivCLM (k := ⊤) ℝ (e j) (coreMul χ f)) : E → F) x =
      ((scalarMul μ χ (gradient μ e f j) + scalarMul μ (TestFunction.lineDerivCLM (k := ⊤) ℝ (e j) χ) (toL2 μ f) : Lp F 2 μ) : E → F) x
    rw [h₁,h₆,Pi.add_apply,h₂,h₃,gradient_apply,h₄,h₅,coreMul_derivative]
  · apply Lp.ext
    filter_upwards [weightedToL2_ae μ w hw (coreMul χ f),
      BFSSLocalL2.compactMul_ae (fun x => w x*χ x) (hw.mul χ.continuous) χ.hasCompactSupport.mul_left (toL2 μ f),
      toL2_ae μ f] with x h₁ h₂ h₃
    change (weightedToL2 μ w hw (coreMul χ f) : E → F) x =
      (BFSSLocalL2.compactMul (fun x => w x*χ x) (hw.mul χ.continuous) χ.hasCompactSupport.mul_left (toL2 μ f) : E → F) x
    rw [h₁,h₂,h₃,coreMul_apply,mul_smul]

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma cutoff_mem_weightedClosure (w : E → ℝ) (hw : Continuous w) (χ : Core (E := E) (F := ℝ))
    {u : Lp F 2 μ} {v : Gradient (F := F) μ (ι := ι)} (hp : (u,v) ∈ closedGraph μ e) :
    (scalarMul μ χ u,cutoffGradient μ e χ u v,cutoffMoment μ w hw χ u) ∈ weightedClosure μ e w hw := by
  change (u,v) ∈ closure (Set.range fun f : Core (E := E) (F := F) => (toL2 μ f,gradient μ e f)) at hp
  obtain ⟨p,hp,ht⟩ := mem_closure_iff_seq_limit.mp hp
  choose f hf using hp
  have hf₂ : Tendsto (fun n => (toL2 μ (f n),gradient μ e (f n))) atTop (𝓝 (u,v)) := by simpa only [hf] using ht
  have hf₁ : Tendsto (fun n => toL2 μ (f n)) atTop (𝓝 u) :=
    (continuous_fst.tendsto (u,v)).comp hf₂
  apply mem_closure_of_tendsto (b := (atTop : Filter ℕ)) (f := fun n =>
    (scalarMul μ χ (toL2 μ (f n)),cutoffGradient μ e χ (toL2 μ (f n)) (gradient μ e (f n)),
      cutoffMoment μ w hw χ (toL2 μ (f n))))
  · exact ((BFSSLocalL2.compactMul_continuous _ _ _).tendsto u |>.comp hf₁).prodMk_nhds
      (((cutoffGradient_continuous μ e χ).tendsto (u,v) |>.comp hf₂).prodMk_nhds
        ((BFSSLocalL2.compactMul_continuous _ _ _).tendsto u |>.comp hf₁))
  · exact Eventually.of_forall (fun n => ⟨coreMul χ (f n),cutoff_core_tuple μ e w hw χ (f n)⟩)
end
end BFSSSliceSobolev

namespace BFSSSliceSobolev
noncomputable section
open MeasureTheory Set Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
variable {ι : Type*} [Fintype ι] (e : ι → E)

def bumpCore (φ : ContDiffBump (0 : E)) (h : ℝ) (hh : h ≠ 0) : Core (E := E) (F := ℝ) :=
  ⟨fun x => φ (h • x),φ.contDiff.comp (contDiff_const.smul contDiff_id),
    φ.hasCompactSupport.comp_smul hh,by intro x hx; trivial⟩

omit [MeasurableSpace E] [BorelSpace E] in
lemma bumpCore_apply (φ : ContDiffBump (0 : E)) (h : ℝ) (hh : h ≠ 0) (x : E) :
    bumpCore φ h hh x = φ (h • x) := rfl

omit [MeasurableSpace E] [BorelSpace E] in
lemma bumpCore_derivative (φ : ContDiffBump (0 : E)) (h : ℝ) (hh : h ≠ 0) (x a : E) :
    TestFunction.lineDerivCLM (k := ⊤) ℝ a (bumpCore φ h hh) x =
      fderiv ℝ (φ : E → ℝ) (h • x) (h • a) := by
  change fderiv ℝ (fun x => φ (h • x)) x a = _
  have hs : HasFDerivAt (fun y : E => h • y) (h • ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).const_smul h
  have he := (((φ.contDiff : ContDiff ℝ 1 (φ : E → ℝ)).differentiable (by norm_num) (h • x)).hasFDerivAt.comp x hs).fderiv
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,_root_.smul_apply,ContinuousLinearMap.id_apply,map_smul] using congrArg (fun L : E →L[ℝ] ℝ => L a) he

omit [CompleteSpace F] [IsFiniteMeasureOnCompacts μ] in
lemma scalarMul_bump_tendsto (φ : ContDiffBump (0 : E)) (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0)
    (ht : Tendsto h atTop (𝓝 0)) (u : Lp F 2 μ) :
    Tendsto (fun n => scalarMul μ (bumpCore φ (h n) (hh n)) u) atTop (𝓝 u) := by
  have hm (n : ℕ) : AEStronglyMeasurable (fun x : E => φ (h n • x)) μ :=
    (φ.continuous.comp (continuous_const.smul continuous_id)).aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐ x ∂μ, |φ (h n • x)| ≤ 1 :=
    ae_of_all μ (fun x => by rw [abs_of_nonneg φ.nonneg]; exact φ.le_one)
  have hl : ∀ᵐ x ∂μ, Tendsto (fun n => φ (h n • x)) atTop (𝓝 1) := by
    apply ae_of_all
    intro x
    have hhx : Tendsto (fun n => h n • x) atTop (𝓝 (0 : E)) := by simpa only [zero_smul] using ht.smul_const x
    have hφ0 : φ (0 : E) = 1 := φ.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_self] using φ.rIn_pos.le)
    simpa only [hφ0,Function.comp_def] using φ.continuous.continuousAt.tendsto.comp hhx
  have he (n : ℕ) : scalarMul μ (bumpCore φ (h n) (hh n)) u =
      BFSSLocalL2.boundedMul (fun x => φ (h n • x)) (hm n) 1 (hb n) u := by
    apply Lp.ext
    filter_upwards [BFSSLocalL2.compactMul_ae _ _ _ u,
      BFSSLocalL2.boundedMul_ae _ (hm n) 1 (hb n) u] with x hx hy
    rw [hx,hy,bumpCore_apply]
  simpa only [he] using BFSSLocalL2.boundedMul_fixed_tendsto
    (fun n x => φ (h n • x)) hm 1 (by norm_num) hb hl u

omit [CompleteSpace F] [IsFiniteMeasureOnCompacts μ] in
lemma scalarMul_bump_derivative_tendsto (φ : ContDiffBump (0 : E)) (h : ℕ → ℝ)
    (hh : ∀ n, h n ≠ 0) (ht : Tendsto h atTop (𝓝 0)) (a : E) (u : Lp F 2 μ) :
    Tendsto (fun n => scalarMul μ (TestFunction.lineDerivCLM (k := ⊤) ℝ a
      (bumpCore φ (h n) (hh n))) u) atTop (𝓝 0) := by
  have hdc : Continuous (fderiv ℝ (φ : E → ℝ)) := (φ.contDiff : ContDiff ℝ 1 (φ : E → ℝ)).continuous_fderiv (by norm_num)
  obtain ⟨D,hD⟩ := (φ.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous hdc
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  have hb (n : ℕ) : ‖scalarMul μ (TestFunction.lineDerivCLM (k := ⊤) ℝ a (bumpCore φ (h n) (hh n))) u‖ ≤
      (D*|h n| *‖a‖)*‖u‖ := by
    apply BFSSLocalL2.norm_le_mul_of_ae_norm_le _ u (D*|h n| *‖a‖) (by positivity)
    filter_upwards [BFSSLocalL2.compactMul_ae _ _ _ u] with x hx
    rw [hx,norm_smul,bumpCore_derivative]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ ≤ ‖fderiv ℝ (φ : E → ℝ) (h n • x)‖*‖h n • a‖ := (fderiv ℝ (φ : E → ℝ) (h n • x)).le_opNorm _
      _ ≤ D*‖h n • a‖ := mul_le_mul_of_nonneg_right (hD _) (norm_nonneg _)
      _ = D*|h n| *‖a‖ := by rw [norm_smul,Real.norm_eq_abs,mul_assoc]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) hb
  simpa only [abs_zero,mul_zero,zero_mul] using (ht.abs.const_mul D).mul_const ‖a‖ |>.mul_const ‖u‖

omit [CompleteSpace F] [IsFiniteMeasureOnCompacts μ] [Fintype ι] in
lemma cutoffGradient_bump_tendsto (φ : ContDiffBump (0 : E)) (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0)
    (ht : Tendsto h atTop (𝓝 0)) (u : Lp F 2 μ) (v : Gradient (F := F) μ (ι := ι)) :
    Tendsto (fun n => cutoffGradient μ e (bumpCore φ (h n) (hh n)) u v) atTop (𝓝 v) := by
  have hp : Tendsto (fun n j => scalarMul μ (bumpCore φ (h n) (hh n)) (v j) +
      scalarMul μ (TestFunction.lineDerivCLM (k := ⊤) ℝ (e j) (bumpCore φ (h n) (hh n))) u)
      atTop (𝓝 (fun j => v j)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    simpa only [add_zero] using (scalarMul_bump_tendsto μ φ h hh ht (v j)).add
      (scalarMul_bump_derivative_tendsto μ φ h hh ht (e j) u)
  exact (PiLp.continuous_toLp 2 _).tendsto (fun j => v j) |>.comp hp

omit [FiniteDimensional ℝ E] [CompleteSpace F] [IsFiniteMeasureOnCompacts μ] in
lemma cutoffMoment_eq_scalarMul (w : E → ℝ) (hw : Continuous w) (χ : Core (E := E) (F := ℝ))
    (u : Lp F 2 μ) (hm : MemLp (fun x => w x • u x) 2 μ) :
    cutoffMoment μ w hw χ u = scalarMul μ χ (hm.toLp (fun x => w x • u x)) := by
  apply Lp.ext
  filter_upwards [BFSSLocalL2.compactMul_ae (fun x => w x*χ x) (hw.mul χ.continuous)
    χ.hasCompactSupport.mul_left u,BFSSLocalL2.compactMul_ae _ _ _ (hm.toLp (fun x => w x • u x)),
    hm.coeFn_toLp] with x hx hy hz
  change (BFSSLocalL2.compactMul (fun x => w x*χ x) (hw.mul χ.continuous)
    χ.hasCompactSupport.mul_left u : E → F) x = _
  rw [hx,hy,hz,mul_comm,mul_smul]

omit [CompleteSpace F] in
theorem mem_weightedClosure (w : E → ℝ) (hw : Continuous w)
    {u : Lp F 2 μ} {v : Gradient (F := F) μ (ι := ι)} (hp : (u,v) ∈ closedGraph μ e)
    (hm : MemLp (fun x => w x • u x) 2 μ) :
    (u,v,hm.toLp (fun x => w x • u x)) ∈ weightedClosure μ e w hw := by
  let φ : ContDiffBump (0 : E) := ⟨1,2,by norm_num,by norm_num⟩
  let h : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hh : ∀ n, h n ≠ 0 := fun n => ne_of_gt (by dsimp [h]; positivity)
  have ht : Tendsto h atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have h₁ := scalarMul_bump_tendsto μ φ h hh ht u
  have h₂ := cutoffGradient_bump_tendsto μ e φ h hh ht u v
  have h₃ : Tendsto (fun n => cutoffMoment μ w hw (bumpCore φ (h n) (hh n)) u)
      atTop (𝓝 (hm.toLp (fun x => w x • u x))) := by
    simp only [cutoffMoment_eq_scalarMul μ w hw _ u hm]
    exact scalarMul_bump_tendsto μ φ h hh ht _
  exact isClosed_closure.mem_of_tendsto (h₁.prodMk_nhds (h₂.prodMk_nhds h₃))
    (Eventually.of_forall fun n => cutoff_mem_weightedClosure μ e w hw (bumpCore φ (h n) (hh n)) hp)
end
end BFSSSliceSobolev

namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory Set Filter Topology
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] normalSlice gaugeAction coreToL2
local instance formClosureFermionNormedAddCommGroup :
    NormedAddCommGroup (Fermion N →L[ℝ] Fermion N) := inferInstance
local instance formClosureFermionNormedSpace :
    NormedSpace ℝ (Fermion N →L[ℝ] Fermion N) := inferInstance

def normalMomentWeight (q : Boson N) (x : M.NormalCoordinates q) : ℝ :=
  Real.sqrt (M.normalQuadratic q (M.normalCoordinateIsometry q x : Boson N))

lemma normalMomentWeight_continuous (q : Boson N) : Continuous (M.normalMomentWeight q) :=
  ((M.normalQuadratic_continuous q).comp
    ((continuous_subtype_val).comp (M.normalCoordinateIsometry q).continuous)).sqrt

lemma normalWeightedCore_norm_sq (q : Boson N) (f : M.NormalCore q) :
    ‖BFSSSliceSobolev.weightedToL2 volume (M.normalMomentWeight q) (M.normalMomentWeight_continuous q) f‖^2 =
      ∫ x : M.NormalCoordinates q, M.normalQuadratic q (M.normalCoordinateIsometry q x : Boson N)*
        ‖(BFSSSliceSobolev.toL2 volume f) x‖^2 := by
  rw [BFSSLocalL2.lp_norm_sq]
  apply integral_congr_ae
  filter_upwards [BFSSSliceSobolev.weightedToL2_ae volume (M.normalMomentWeight q)
    (M.normalMomentWeight_continuous q) f,BFSSSliceSobolev.toL2_ae volume f] with x hw hf
  rw [hw,hf,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,normalMomentWeight,
    Real.sq_sqrt (M.normalQuadratic_nonneg q _)]

theorem normalOscillator_nonneg (q : Boson N) (hq : q ∈ M.massiveZeros)
    (u : Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q))) (v : M.NormalGradient q)
    (hd : M.NormalFormDomain q u v) : 0 ≤ M.normalOscillatorForm q u v := by
  let A := M.deformedFermionField 1 1 q
  let C : Set (Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)) ×
      M.NormalGradient q × Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q))) :=
    {p | 0 ≤ (1/2 : ℝ)*‖p.2.1‖^2+‖p.2.2‖^2+inner ℝ p.1 (A.compLp p.1)}
  have hC : IsClosed C := by
    apply isClosed_le continuous_const
    exact ((continuous_const.mul (((continuous_fst.comp continuous_snd).norm).pow 2)).add
      (((continuous_snd.comp continuous_snd).norm).pow 2)).add
      (continuous_fst.inner ((A.compLpL 2 volume).continuous.comp continuous_fst))
  have hs : Set.range (fun f : M.NormalCore q =>
      (BFSSSliceSobolev.toL2 volume f,
        BFSSSliceSobolev.gradient volume (EuclideanSpace.basisFun (M.NormalIndex q) ℝ) f,
        BFSSSliceSobolev.weightedToL2 volume (M.normalMomentWeight q) (M.normalMomentWeight_continuous q) f)) ⊆ C := by
    rintro _ ⟨f,rfl⟩
    have hf := M.normalOscillator_core_nonneg q hq f
    change 0 ≤ (1/2 : ℝ)*‖BFSSSliceSobolev.gradient volume
      (EuclideanSpace.basisFun (M.NormalIndex q) ℝ) f‖^2 +
      ‖BFSSSliceSobolev.weightedToL2 volume (M.normalMomentWeight q) (M.normalMomentWeight_continuous q) f‖^2 +
      inner ℝ (BFSSSliceSobolev.toL2 volume f) (A.compLp (BFSSSliceSobolev.toL2 volume f))
    rw [M.normalWeightedCore_norm_sq]
    simpa only [normalOscillatorForm,BFSSNormalAnalysis.constant_quadratic_eq,A] using hf
  have hm := BFSSSliceSobolev.mem_weightedClosure volume
    (EuclideanSpace.basisFun (M.NormalIndex q) ℝ) (M.normalMomentWeight q)
    (M.normalMomentWeight_continuous q) hd.1 hd.2
  have hc := closure_minimal hs hC hm
  change 0 ≤ (1/2 : ℝ)*‖v‖^2+‖hd.2.toLp (fun x => M.normalMomentWeight q x • u x)‖^2+
    inner ℝ u (A.compLp u) at hc
  rw [normalOscillatorForm,←M.normalPotential_norm_sq q u hd.2,
    BFSSNormalAnalysis.constant_quadratic_eq]
  exact hc
end
end BFSSQuantum.AlgebraData

end OAI
