import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveVolterra
import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedMeshStep
import OAI.MathematicalPhysics.Boltzmann.Branching.RestrictedCone
import OAI.MathematicalPhysics.Boltzmann.Collision.TransverseStripeWeak
import OAI.MathematicalPhysics.Boltzmann.Compactness.FiniteThermalLimit

namespace OAI

section

/-! # The cost of removing collisions close to a transverse origin -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.PositiveIteration

def nearOriginRegion (c : Transverse) (ρ : ℝ) : Set KineticPhase :=
  {z | ‖transverse z.1.2-c‖ < ρ}

theorem nearOriginRegion_measurable (c : Transverse) (ρ : ℝ) :
    MeasurableSet (nearOriginRegion c ρ) := by
  apply measurableSet_lt _ measurable_const
  unfold transverse
  fun_prop

def nearOriginKernel (c : Transverse) (ρ : ℝ) (K : Kernel KineticPhase Velocity) :
    Kernel KineticPhase Velocity := by
  classical
  exact Kernel.piecewise (nearOriginRegion_measurable c ρ) K 0

def awayOriginKernel (c : Transverse) (ρ : ℝ) (K : Kernel KineticPhase Velocity) :
    Kernel KineticPhase Velocity := by
  classical
  exact Kernel.piecewise (nearOriginRegion_measurable c ρ) 0 K

instance nearOriginKernel_sFinite (c : Transverse) (ρ : ℝ) (K : Kernel KineticPhase Velocity)
    [IsSFiniteKernel K] : IsSFiniteKernel (nearOriginKernel c ρ K) := by
  unfold nearOriginKernel
  infer_instance

instance awayOriginKernel_sFinite (c : Transverse) (ρ : ℝ) (K : Kernel KineticPhase Velocity)
    [IsSFiniteKernel K] : IsSFiniteKernel (awayOriginKernel c ρ K) := by
  unfold awayOriginKernel
  infer_instance

theorem originKernel_decomposition (c : Transverse) (ρ : ℝ) (K : Kernel KineticPhase Velocity) :
    awayOriginKernel c ρ K+nearOriginKernel c ρ K = K := by
  classical
  ext z E hE
  by_cases hz : z ∈ nearOriginRegion c ρ <;>
    simp [nearOriginKernel,awayOriginKernel,Kernel.piecewise_apply,hz]

theorem step_nearOrigin_bound {a T ρ b : ℝ} (hρ : 0 ≤ ρ) (hb : 0 < b)
    (c : Transverse) (K : Kernel KineticPhase Velocity)
    {B C : ℝ≥0∞} (hK : ∀ y, y.1.1 ∈ Icc a T → K y univ ≤ C)
    {f : KineticPhase → ℝ≥0∞} (hf : ∀ y, y.1.1 ∈ Icc a T → f y ≤ B)
    {z : KineticPhase} (hz : z.1.1 ∈ Icc a T) (hv : b ≤ ‖transverse z.2‖) :
    step a (nearOriginKernel c ρ K) f z ≤ (B*C)*ENNReal.ofReal (2*ρ/b) := by
  classical
  let E : Set ℝ := {s | ‖(transverse z.1.2-c)-(z.1.1-s) • transverse z.2‖ < ρ}
  have hE : MeasurableSet E := by apply measurableSet_lt <;> fun_prop
  have hflight (s : ℝ) : flight z s ∈ nearOriginRegion c ρ ↔ s ∈ E := by
    change ‖transverse (z.1.2-(z.1.1-s) • z.2)-c‖ < ρ ↔ _
    have he : transverse (z.1.2-(z.1.1-s) • z.2)-c =
        (transverse z.1.2-c)-(z.1.1-s) • transverse z.2 := by
      unfold transverse
      apply (WithLp.ext_iff 2).mpr
      funext i
      change z.1.2 i.castSucc-(z.1.1-s)*z.2 i.castSucc-c i =
        (z.1.2 i.castSucc-c i)-(z.1.1-s)*z.2 i.castSucc
      ring
    rw [he]
    rfl
  have hnonzero : transverse z.2 ≠ 0 := norm_pos_iff.mp (hb.trans_le hv)
  have hvol : volume E ≤ ENNReal.ofReal (2*ρ/b) := by
    apply (transverse_flight_time_bound (transverse z.1.2-c) (transverse z.2)
      hnonzero z.1.1 ρ).trans
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (by positivity) hb hv)
  unfold step
  calc
    _ ≤ ∫⁻ s in Ioc a z.1.1, E.indicator (fun _ => B*C) s := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have ht : s ∈ Icc a T := ⟨hs.1.le,hs.2.trans hz.2⟩
      by_cases he : s ∈ E
      · rw [indicator_of_mem he]
        have hk : nearOriginKernel c ρ K (flight z s) = K (flight z s) := by
          simp only [nearOriginKernel,Kernel.piecewise_apply,(hflight s).mpr he,ite_true]
        rw [hk]
        calc
          _ ≤ ∫⁻ _v, B ∂K (flight z s) := lintegral_mono (fun v => hf _ ht)
          _ = B*K (flight z s) univ := by rw [lintegral_const,mul_comm]
          _ ≤ B*C := mul_le_mul' le_rfl (hK _ ht)
      · have hk : nearOriginKernel c ρ K (flight z s) = 0 := by
          simp [nearOriginKernel,Kernel.piecewise_apply,(not_congr (hflight s)).mpr he]
        rw [hk,lintegral_zero_measure,indicator_of_notMem he]
    _ ≤ ∫⁻ s, E.indicator (fun _ => B*C) s := setLIntegral_le_lintegral _ _
    _ = (B*C)*volume E := lintegral_indicator_const hE _
    _ ≤ _ := mul_le_mul' le_rfl hvol

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # Exact finite mesh representation of the restricted fixed-origin gain chain -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.PositiveIteration

theorem finiteGainChain_measurable {I : Type*} [Fintype I] (a : ℝ)
    (K : ℕ → I → Kernel Published.KineticPhase Velocity) [∀ i j, IsSFiniteKernel (K i j)]
    {weight : ℕ → I → Published.KineticPhase → ℝ≥0∞}
    (hw : ∀ i j, Measurable (weight i j)) {f : Published.KineticPhase → ℝ≥0∞}
    (hf : Measurable f) (i n : ℕ) : Measurable (finiteGainChain a K weight f i n) := by
  induction n generalizing i with
  | zero => exact hf
  | succ n ih =>
    exact Finset.measurable_sum _ (fun j _ => step_measurable a (K i j)
      ((hw i j).mul (ih (i+1))))

theorem step_slab_congr {a T : ℝ} (K : Kernel Published.KineticPhase Velocity)
    {f g : Published.KineticPhase → ℝ≥0∞}
    (h : ∀ y, y.1.1 ∈ Icc a T → f y = g y)
    {z : Published.KineticPhase} (hz : z.1.1 ∈ Icc a T) : step a K f z = step a K g z :=
  le_antisymm (step_slab_mono K (fun y hy => (h y hy).le) hz)
    (step_slab_mono K (fun y hy => (h y hy).ge) hz)

end BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

def meshFamily (s₀ η K α γ d₀ q : ℝ) (r : ℕ → ℝ) {J : Finset ℤ} (n : ℕ) :
    ℕ → MeshLabel J → Kernel Published.KineticPhase Velocity :=
  thermalKernelFamily (r n) η K α γ q (fun _ j => meshScale s₀ η r n j/r n)
    (fun _ j => d₀*meshScale s₀ η r n j^10) (fun _ j => j.2)

instance meshFamily_sFinite (s₀ η K α γ d₀ q : ℝ) (r : ℕ → ℝ) {J : Finset ℤ}
    (n i : ℕ) (j : MeshLabel J) : IsSFiniteKernel (meshFamily s₀ η K α γ d₀ q r n i j) := by
  unfold meshFamily
  infer_instance

theorem meshFamily_apply {s₀ η K α γ d₀ q : ℝ} {r : ℕ → ℝ} {J : Finset ℤ}
    (n : ℕ) (hr : 0 < r n) (i : ℕ) (j : MeshLabel J) :
    meshFamily s₀ η K α γ d₀ q r n i j =
      dilatedFreeKernel (r n) η K α γ (meshScale s₀ η r n j)
        (d₀*meshScale s₀ η r n j^10) q j.2 := by
  unfold meshFamily thermalKernelFamily
  congr 1
  field_simp [(hr).ne']

def meshWeights (s₀ η δ M a T : ℝ) (r : ℕ → ℝ) (N n : ℕ)
    (S : ℕ → Set Velocity) : ℕ → MeshLabel (windowMesh η δ M) → Published.KineticPhase → ℝ≥0∞ :=
  fun i j => boundedMeshWeight s₀ η δ M a T r N n (S (i+1)) j

theorem originScale_chain_eq_mesh {s₀ η K α γ d₀ q δ M a T : ℝ}
    {r : ℕ → ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (n : ℕ) (hr : 0 < r n) (hδ : 0 < δ) (N : ℕ)
    (S : ℕ → Set Velocity) (hS : ∀ i, MeasurableSet (S i))
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) (i m : ℕ)
    {z : Published.KineticPhase} (hz : z.1.1 ∈ Icc a T) :
    restrictedChain a (originScaleKernel (r n) s₀ η K α γ d₀ q δ M N 0) S hS f i m z =
      finiteGainChain a (meshFamily s₀ η K α γ d₀ q r n)
        (meshWeights s₀ η δ M a T r N n S) f i m z := by
  have hwm (i : ℕ) (j : MeshLabel (windowMesh η δ M)) :
      Measurable (meshWeights s₀ η δ M a T r N n S i j) :=
    boundedMeshWeight_measurable s₀ η δ M a T r N n (hS (i+1)) j
  induction m generalizing i z with
  | zero => rfl
  | succ m ih =>
    let f' := finiteGainChain a (meshFamily s₀ η K α γ d₀ q r n)
      (meshWeights s₀ η δ M a T r N n S) f (i+1) m
    have hfm : Measurable f' := finiteGainChain_measurable a _ hwm hf (i+1) m
    calc
      _ = step a ((originScaleKernel (r n) s₀ η K α γ d₀ q δ M N 0).restrict (hS (i+1))) f' z := by
        apply step_slab_congr _ _ hz
        intro y hy
        exact ih (i+1) hy
      _ = ∑ j : MeshLabel (windowMesh η δ M),
          step a (dilatedFreeKernel (r n) η K α γ (meshScale s₀ η r n j)
            (d₀*meshScale s₀ η r n j^10) q j.2)
            (fun y => boundedMeshWeight s₀ η δ M a T r N n (S (i+1)) j y*f' y) z :=
        originScale_restricted_step_eq hs₀ hsmax hη hηmax n hr hδ N (hS (i+1)) hfm hz
      _ = _ := by
        change _ = ∑ j : MeshLabel (windowMesh η δ M), step a _ _ z
        apply Finset.sum_congr rfl
        intro j _
        rw [meshFamily_apply n hr]
        rfl

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Propagating the small-origin error through the retained nonaxial chain -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.PositiveIteration

theorem restrictedChain_origin_deletion {a T ρ b : ℝ} (hρ : 0 ≤ ρ) (hb : 0 < b)
    (c : Transverse) (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K]
    (S : ℕ → Set Velocity) (hS : ∀ i, MeasurableSet (S i))
    (hspeed : ∀ i v, v ∈ S i → b ≤ ‖transverse v‖)
    {C B : ℝ≥0∞} (hK : ∀ z, z.1.1 ∈ Icc a T → K z univ ≤ C)
    {f : KineticPhase → ℝ≥0∞} (hfm : Measurable f)
    (hf : ∀ z, z.1.1 ∈ Icc a T → f z ≤ B) (i n : ℕ) :
    ∀ z, z.1.1 ∈ Icc a T → z.2 ∈ S i →
      restrictedChain a K S hS f i n z ≤
        restrictedChain a (awayOriginKernel c ρ K) S hS f i n z+
          (C*ENNReal.ofReal (2*ρ/b))*deletionCoefficient B (C*ENNReal.ofReal (T-a)) n := by
  let L := awayOriginKernel c ρ K
  let D := nearOriginKernel c ρ K
  let P := C*ENNReal.ofReal (T-a)
  let Q := C*ENNReal.ofReal (2*ρ/b)
  have hLD : L+D = K := originKernel_decomposition c ρ K
  have hL : ∀ z, z.1.1 ∈ Icc a T → L z univ ≤ C := by
    intro z hz
    apply le_trans ?_ (hK z hz)
    calc
      L z univ ≤ L z univ+D z univ := le_self_add
      _ = K z univ := congrArg (fun κ : Kernel KineticPhase Velocity => κ z univ) hLD
  induction n generalizing i with
  | zero => simp only [restrictedChain,deletionCoefficient,mul_zero,add_zero,le_refl,implies_true]
  | succ n ih =>
    intro z hz hzS
    let LR := L.restrict (hS (i+1))
    let DR := D.restrict (hS (i+1))
    let E := Q*deletionCoefficient B P n
    have hLR : ∀ y, y.1.1 ∈ Icc a T → LR y univ ≤ C := by
      intro y hy
      exact (Measure.restrict_apply_le _ _).trans (hL y hy)
    have hsplitK : LR+DR = K.restrict (hS (i+1)) := by
      dsimp only [LR,DR]
      rw [← kernel_restrict_add,hLD]
    have htail : ∀ y, y.1.1 ∈ Icc a T → y.2 ∈ S (i+1) →
        restrictedChain a K S hS f (i+1) n y ≤
          restrictedChain a L S hS f (i+1) n y+E := ih (i+1)
    have hgood := step_restrict_slab_mono L (hS (i+1)) htail hz
    have hm := restrictedChain_measurable a L S hS hfm (i+1) n
    have hadd := congrFun (step_add a LR (g := fun _ => E) hm) z
    have hsplit := congrFun (step_add_kernel a LR DR
      (restrictedChain_measurable a K S hS hfm (i+1) n)) z
    have hconst : step a LR (fun _ => E) z ≤ E*P :=
      step_uniform_bound LR hLR (fun _ _ => le_rfl) hz
    have hbad : step a DR (restrictedChain a K S hS f (i+1) n) z ≤ B*P^n*Q := by
      apply (step_restrict_le a D (hS (i+1)) _ z).trans
      have hh := step_nearOrigin_bound hρ hb c K hK
        (restrictedChain_uniform_bound K S hS hK hf (i+1) n) hz (hspeed i z.2 hzS)
      simpa only [mul_assoc] using hh
    calc
      restrictedChain a K S hS f i (n+1) z =
          step a LR (restrictedChain a K S hS f (i+1) n) z+
            step a DR (restrictedChain a K S hS f (i+1) n) z := by
        change step a (K.restrict (hS (i+1))) _ z = _
        simpa only [hsplitK,Pi.add_apply] using hsplit
      _ ≤ step a LR (fun y => restrictedChain a L S hS f (i+1) n y+E) z+B*P^n*Q :=
        add_le_add hgood hbad
      _ = (restrictedChain a L S hS f i (n+1) z+step a LR (fun _ => E) z)+B*P^n*Q := by
        change step a LR (restrictedChain a L S hS f (i+1) n+(fun _ => E)) z+_ = _
        rw [hadd,Pi.add_apply]
        rfl
      _ ≤ (restrictedChain a L S hS f i (n+1) z+E*P)+B*P^n*Q :=
        add_le_add (add_le_add le_rfl hconst) le_rfl
      _ = _ := by
        change (_+(Q*deletionCoefficient B P n)*P)+B*P^n*Q =
          _+Q*(B*P^n+P*deletionCoefficient B P n)
        ring

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # Vanishing of the actual selected fifth gain at a fixed origin and compact scales -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.FiveGainMap
open BoltzmannNonuniqueness.PositiveIteration
open BoltzmannNonuniqueness.JetCoreSheet
open BoltzmannNonuniqueness.GeometricMesh
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem origin_scale_five_tendsto
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {K α γ qexp a T b Vmax s₀ η d₀ θ δ M : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq : 0 ≤ qexp)
    (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hd₀ : 0 < d₀) (hθ : 0 < θ) (hδ : 0 < δ)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hphase : Tendsto (fun n => phase (s₀/r n) η) atTop (𝓝 θ)) (N : ℕ → ℕ)
    (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    (states : ℕ → State) (hstates : Tendsto states atTop (𝓝 (t₀,x,v)))
    (htime : ∀ n, (states n).1 ∈ Icc a T)
    (S : ℕ → Set Velocity) (hS : ∀ i, MeasurableSet (S i))
    (hbound : ∀ i w, w ∈ S i → ‖w‖ ≤ Vmax ∧ b ≤ ‖transverse w‖)
    (hinit : ∀ n, WithLp.toLp 2 (states n).2.2 ∈ S 0)
    {g : ℕ → Published.KineticPhase → ℝ≥0∞} {B : ℝ≥0∞}
    (hB : B ≠ ∞) (hg : ∀ n, Measurable (g n)) (hgB : ∀ n z, g n z ≤ B)
    (hL : ∀ C : Set Published.KineticPhase, IsCompact C →
      Tendsto (fun n => ∫⁻ z in C, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => restrictedChain a
      (originScaleKernel (r n) s₀ η K α γ d₀ qexp δ M (N n) 0)
      S hS (g n) 0 5 (toKinetic (states n))) atTop (𝓝 0) := by
  let weights : ℕ → Fin 5 → MeshLabel (windowMesh η δ M) → Published.KineticPhase → ℝ≥0∞ :=
    fun n i => boundedMeshWeight s₀ η δ M a T r (N n) n (S (i.val+1))
  have hlim := geometric_thermal_five_tendsto hMityagin hK hα hγ hq ha hb hV
    hs₀ hη hd₀ hθ r hr hrlim hphase (windowMesh η δ M) t₀ x v hv states hstates
    (fun n => hbound 0 _ (hinit n)) weights
    (fun n i j => boundedMeshWeight_measurable s₀ η δ M a T r (N n) n (hS (i.val+1)) j)
    (fun n i j z => boundedMeshWeight_le_one s₀ η δ M a T r (N n) n (S (i.val+1)) j z)
    (fun n i j z hz => boundedMeshWeight_support (hbound (i.val+1)) j z hz) hB hg hgB hL
  apply hlim.congr'
  apply Eventually.of_forall
  intro n
  have he := originScale_chain_eq_mesh (K := K) (α := α) (γ := γ) (d₀ := d₀)
    (q := qexp) (M := M) (a := a) (T := T) (z := toKinetic (states n)) hs₀ hsmax hη hηmax n (hr n) hδ (N n) S hS
    (hg n) 0 5 (htime n)
  have hw : ∀ k, 0 ≤ k → k < 0+5 →
      meshWeights s₀ η δ M a T r (N n) n S k = cycleFive (weights n) k := by
    intro k _ hk
    have hk' : k < 5 := by omega
    rw [show cycleFive (weights n) k = weights n ⟨k,hk'⟩ from cycleFive_apply (weights n) ⟨k,hk'⟩]
    rfl
  have he' := finiteGainChain_congr_weights a (meshFamily s₀ η K α γ d₀ qexp r n)
    _ _ (g n) 0 5 hw (toKinetic (states n))
  exact (he.trans he').symm

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
