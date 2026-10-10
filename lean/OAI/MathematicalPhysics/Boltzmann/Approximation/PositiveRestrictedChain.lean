import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveVolterra
import OAI.MathematicalPhysics.Boltzmann.Branching.MainPositiveRemainderBound
import OAI.MathematicalPhysics.Boltzmann.Branching.SmallFirstGain
import OAI.MathematicalPhysics.Boltzmann.Branching.TwoCoreLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.SelectedLargeOutput
import OAI.MathematicalPhysics.Boltzmann.Compactness.SelectedTwoGainLimit
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

namespace OAI

section

/-! # Transverse spatial escape forces the actual positive fifth gain to vanish -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem positive_five_transverse_escape_tendsto {K α γ q a T V s₀ η d₀ : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (N : ℕ → ℕ) (z : ℕ → Published.KineticPhase)
    (ht : ∀ n, (z n).1.1 ∈ Icc a T) (hv : ∀ n, ‖(z n).2‖ ≤ V)
    (hx : ∀ R : ℝ, ∀ᶠ n in atTop, ∀ k : Lattice,
      R ≤ ‖transverse ((z n).1.2-(r n)⁻¹ • latticeVector k)‖)
    {f : ℕ → Published.KineticPhase → ℝ≥0∞} {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hf : ∀ n y, y.1.1 ∈ Icc a T → f n y ≤ B) :
    Tendsto (fun n => iterate a (positiveMainKernel (r n) s₀ η K α γ d₀ q (N n))
      (f n) 5 (z n)) atTop (𝓝 0) := by
  refine five_tendsto_of_small_first_mass
    (C := ENNReal.ofReal ((2*JetCoreSheet.growthConstant K α γ q)/a))
    (fun n => positiveMainKernel (r n) s₀ η K α γ d₀ q (N n)) ENNReal.ofReal_ne_top hB ?_ hf z ht ?_
  · intro n y hy
    apply (positiveMainKernel_bound (hr n) hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax hq₁ hq₂
      (N n) y (ha.trans_le hy.1)).trans
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left
      (mul_nonneg (by norm_num) (JetCoreSheet.growthConstant_nonneg hK α γ q)) ha hy.1)
  · intro ε hε
    filter_upwards [selected_transverse_escape_small hK hα hγ hq₁ hq₂ ha.le hs₀ hsmax
      hη hηmax hd₀ hdmax r hr N z ht hv hx (half_pos hε)] with n hn
    intro s hs
    have h := hn s hs
    change ((selectedFreeKernel (r n) s₀ η K α γ d₀ q (N n) (flight (z n) s))+
      (selectedFreeKernel (r n) s₀ η K α γ d₀ q (N n) (flight (z n) s))) univ ≤ _
    rw [Measure.add_apply]
    apply (add_le_add h h).trans_eq
    rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
    congr 1
    ring

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Vanishing of the actual positive main two-gain iteration at the axis -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem positive_two_gain_axial_tendsto {K α γ q a s₀ η d₀ V T : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) (hV : 0 ≤ V)
    (r t : ℕ → ℝ) (N : ℕ → ℕ) (x v : ℕ → Velocity)
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (ht : ∀ n, t n ≤ T) (hv : ∀ n, ‖v n‖ ≤ V)
    (htrans : Tendsto (fun n => ‖transverse (v n)‖) atTop (𝓝 0)) :
    Tendsto (fun n => PositiveIteration.iterate a
      (positiveMainKernel (r n) s₀ η K α γ d₀ q (N n)) (fun _ => 1) 2 ((t n,x n),v n))
      atTop (𝓝 0) := by
  have hs := selected_two_gain_axial_tendsto hK hα hγ hq₁ hq₂ ha hs₀ hsmax hη hηmax
    hd₀ hdmax hV r t N x v hr hrlim ht hv htrans
  have hfour := ENNReal.Tendsto.const_mul (a := (4 : ℝ≥0∞)) hs (Or.inr (by norm_num))
  simp only [mul_zero] at hfour
  apply hfour.congr'
  apply Eventually.of_forall
  intro n
  exact (congrFun (PositiveIteration.iterate_two_add_self a
    (selectedFreeKernel (r n) s₀ η K α γ d₀ q (N n))) ((t n,x n),v n)).symm

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A positive integral budget passes through almost-everywhere convergence -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem lintegral_of_ae_tendsto_le {g : ℕ → X → ℝ} {f : X → ℝ} {C : ℝ≥0∞}
    (hgm : ∀ n, Measurable (g n))
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (f x)))
    (hb : ∀ n, (∫⁻ x, ENNReal.ofReal (g n x) ∂μ) ≤ C) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ C := by
  calc
    _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (g n x)) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ht] with x hx
      exact (ENNReal.tendsto_ofReal hx).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (g n x) ∂μ) atTop :=
      lintegral_liminf_le (fun n => (hgm n).ennreal_ofReal)
    _ ≤ C := liminf_le_of_frequently_le (Eventually.of_forall hb).frequently

theorem integrable_of_positive_limit_budget {g : ℕ → X → ℝ} {f : X → ℝ} {C : ℝ≥0∞}
    (hgm : ∀ n, Measurable (g n)) (hfm : Measurable f) (hfn : 0 ≤ᵐ[μ] f)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (f x)))
    (hb : ∀ n, (∫⁻ x, ENNReal.ofReal (g n x) ∂μ) ≤ C) (hC : C ≠ ∞) :
    Integrable f μ :=
  ⟨hfm.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal hfn).mpr
    ((lintegral_of_ae_tendsto_le hgm ht hb).trans_lt (lt_top_iff_ne_top.mpr hC))⟩

end BoltzmannNonuniqueness

end

end

section

/-! # Escape to large outgoing velocity makes five positive gains vanish -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem positive_five_large_velocity_tendsto {K α γ q a T s₀ η d₀ : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (N : ℕ → ℕ)
    (z : ℕ → Published.KineticPhase) (ht : ∀ n, (z n).1.1 ∈ Icc a T)
    (hv : Tendsto (fun n => ‖(z n).2‖) atTop atTop)
    {f : ℕ → Published.KineticPhase → ℝ≥0∞} {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hf : ∀ n y, y.1.1 ∈ Icc a T → f n y ≤ B) :
    Tendsto (fun n => iterate a (positiveMainKernel (r n) s₀ η K α γ d₀ q (N n))
      (f n) 5 (z n)) atTop (𝓝 0) := by
  let C := ENNReal.ofReal ((2*JetCoreSheet.growthConstant K α γ q)/a)
  let Δ := ENNReal.ofReal (T-a)
  let D := B*(C*Δ)^4
  have hD : D ≠ ∞ := ENNReal.mul_ne_top hB
    (ENNReal.pow_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))
  have hmass (n y) (hy : y.1.1 ∈ Icc a T) :
      positiveMainKernel (r n) s₀ η K α γ d₀ q (N n) y univ ≤ C := by
    apply (positiveMainKernel_bound (hr n) hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax hq₁ hq₂
      (N n) y (ha.trans_le hy.1)).trans
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left
      (mul_nonneg (by norm_num) (JetCoreSheet.growthConstant_nonneg hK α γ q)) ha hy.1)
  have htail (n y) (hy : y.1.1 ∈ Icc a T) :
      iterate a (positiveMainKernel (r n) s₀ η K α γ d₀ q (N n)) (f n) 4 y ≤ D :=
    iterate_uniform_bound _ (hmass n) (hf n) 4 y hy
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨e,he,heε⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (ENNReal.mul_ne_top hD ENNReal.ofReal_ne_top : D*Δ ≠ ∞) hε.ne'
  obtain ⟨R,_,hR⟩ := positive_large_output hK hα hγ hq₁ hq₂ ha (NNReal.coe_pos.mpr he)
  filter_upwards [hv.eventually_gt_atTop R] with n hn
  change step a (positiveMainKernel (r n) s₀ η K α γ d₀ q (N n))
    (iterate a (positiveMainKernel (r n) s₀ η K α γ d₀ q (N n)) (f n) 4) (z n) ≤ ε
  unfold step
  calc
    _ ≤ ∫⁻ _s in Ioc a (z n).1.1, D*(e:ℝ≥0∞) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have htime : s ∈ Icc a T := ⟨hs.1.le,hs.2.trans (ht n).2⟩
      calc
        _ ≤ ∫⁻ _w, D ∂positiveMainKernel (r n) s₀ η K α γ d₀ q (N n) (flight (z n) s) :=
          lintegral_mono (fun w => htail n _ htime)
        _ = D*positiveMainKernel (r n) s₀ η K α γ d₀ q (N n) (flight (z n) s) univ := by
          rw [lintegral_const,mul_comm]
        _ ≤ D*(e:ℝ≥0∞) := by
          apply mul_le_mul' le_rfl
          simpa only [ENNReal.ofReal_coe_nnreal] using
            hR (hr n) hs₀ hsmax hη hηmax hd₀ hdmax (N n) (flight (z n) s) hs.1.le hn
    _ ≤ D*(e:ℝ≥0∞)*Δ := by
      rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioc]
      exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (sub_le_sub_right (ht n).2 a))
    _ = (e:ℝ≥0∞)*(D*Δ) := by ring
    _ ≤ ε := heε.le

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Propagation of a small deleted kernel through finitely many gains -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.PositiveIteration

def deletionCoefficient (B P : ℝ≥0∞) : ℕ → ℝ≥0∞
  | 0 => 0
  | n+1 => B*P^n+P*deletionCoefficient B P n

theorem deletionCoefficient_ne_top {B P : ℝ≥0∞} (hB : B ≠ ∞) (hP : P ≠ ∞) (n : ℕ) :
    deletionCoefficient B P n ≠ ∞ := by
  induction n with
  | zero => exact ENNReal.zero_ne_top
  | succ n ih =>
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top hB (ENNReal.pow_ne_top hP),ENNReal.mul_ne_top hP ih⟩

theorem iterate_deletion_bound {a T : ℝ} (L D : Kernel KineticPhase Velocity)
    [IsSFiniteKernel L] [IsSFiniteKernel D] {C B δ : ℝ≥0∞}
    (hK : ∀ z, z.1.1 ∈ Icc a T → (L+D) z univ ≤ C)
    (hD : ∀ z, z.1.1 ∈ Icc a T → D z univ ≤ δ)
    {f : KineticPhase → ℝ≥0∞} (hfm : Measurable f)
    (hf : ∀ z, z.1.1 ∈ Icc a T → f z ≤ B) (n : ℕ) :
    ∀ z, z.1.1 ∈ Icc a T →
      iterate a (L+D) f n z ≤ iterate a L f n z+
        (δ*ENNReal.ofReal (T-a))*deletionCoefficient B (C*ENNReal.ofReal (T-a)) n := by
  let P := C*ENNReal.ofReal (T-a)
  let Q := δ*ENNReal.ofReal (T-a)
  have hL : ∀ z, z.1.1 ∈ Icc a T → L z univ ≤ C := by
    intro z hz
    apply le_trans ?_ (hK z hz)
    change L z univ ≤ L z univ+D z univ
    exact le_self_add
  induction n with
  | zero => simp only [iterate,deletionCoefficient,mul_zero,add_zero,le_refl,implies_true]
  | succ n ih =>
    intro z hz
    let E := Q*deletionCoefficient B P n
    have hm := iterate_measurable a L hfm n
    have hI : step a (L+D) (iterate a (L+D) f n) z ≤
        step a (L+D) (fun y => iterate a L f n y+E) z :=
      step_slab_mono (L+D) ih hz
    have hadd := congrFun (step_add a (L+D) (g := fun _ => E) hm) z
    have hsplit := congrFun (step_add_kernel a L D hm) z
    have hsmall : step a D (iterate a L f n) z ≤ B*P^n*Q :=
      step_uniform_bound D hD (iterate_uniform_bound L hL hf n) hz
    have hconst : step a (L+D) (fun _ => E) z ≤ E*P :=
      step_uniform_bound (L+D) hK (fun _ _ => le_rfl) hz
    calc
      iterate a (L+D) f (n+1) z ≤ step a (L+D) (fun y => iterate a L f n y+E) z := hI
      _ = (iterate a L f (n+1) z+step a D (iterate a L f n) z)+
          step a (L+D) (fun _ => E) z := by
        change step a (L+D) (iterate a L f n+(fun _ => E)) z = _
        rw [hadd,Pi.add_apply,hsplit,Pi.add_apply]
        rfl
      _ ≤ (iterate a L f (n+1) z+B*P^n*Q)+E*P :=
        add_le_add (add_le_add le_rfl hsmall) hconst
      _ = iterate a L f (n+1) z+
          (δ*ENNReal.ofReal (T-a))*deletionCoefficient B (C*ENNReal.ofReal (T-a)) (n+1) := by
        change (_+B*P^n*Q)+(Q*deletionCoefficient B P n)*P =
          _+Q*(B*P^n+P*deletionCoefficient B P n)
        ring

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # Axial vanishing with any fixed number of subsequent positive gains -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem positive_axial_gain_tendsto {K α γ q a s₀ η d₀ V T B : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) (hV : 0 ≤ V) (hB : 0 ≤ B)
    (r t : ℕ → ℝ) (N : ℕ → ℕ) (x v : ℕ → Velocity)
    (f : ℕ → Published.KineticPhase → ℝ≥0∞)
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (ht : ∀ n, t n ∈ Icc a T) (hv : ∀ n, ‖v n‖ ≤ V)
    (htrans : Tendsto (fun n => ‖transverse (v n)‖) atTop (𝓝 0))
    (hf : ∀ n z, z.1.1 ∈ Icc a T → f n z ≤ ENNReal.ofReal B) (m : ℕ) :
    Tendsto (fun n => PositiveIteration.iterate a
      (positiveMainKernel (r n) s₀ η K α γ d₀ q (N n)) (f n) (m+2) ((t n,x n),v n))
      atTop (𝓝 0) := by
  let G := 2*JetCoreSheet.growthConstant K α γ q
  let C := ENNReal.ofReal (B*(G*Real.log (T/a))^m)
  have hG : 0 ≤ G := mul_nonneg (by norm_num) (JetCoreSheet.growthConstant_nonneg hK α γ q)
  have htwo := positive_two_gain_axial_tendsto hK hα hγ hq₁ hq₂ ha hs₀ hsmax hη hηmax
    hd₀ hdmax hV r t N x v hr hrlim (fun n => (ht n).2) hv htrans
  have hlim : Tendsto (fun n => C*PositiveIteration.iterate a
      (positiveMainKernel (r n) s₀ η K α γ d₀ q (N n)) (fun _ => 1) 2 ((t n,x n),v n))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul htwo (Or.inr ENNReal.ofReal_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
  intro n
  apply PositiveIteration.iterate_first_two_le _ _ m C ENNReal.ofReal_ne_top ?_ (ht n)
  intro z hz
  apply (iterate_positiveMain_bound (hr n) hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax hq₁ hq₂
    ha hB (N n) (hf n) m z hz).trans
  apply ENNReal.ofReal_le_ofReal
  have hlog : 0 ≤ Real.log (z.1.1/a) := Real.log_nonneg ((one_le_div ha).mpr hz.1)
  have hlogle : Real.log (z.1.1/a) ≤ Real.log (T/a) :=
    Real.log_le_log (div_pos (ha.trans_le hz.1) ha) (div_le_div_of_nonneg_right hz.2 ha.le)
  change B*(G*Real.log (z.1.1/a))^m ≤ B*(G*Real.log (T/a))^m
  gcongr

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Successive velocity restrictions in a finite positive gain chain

The retained sets may differ at each collision. Deleted mass is estimated only
at endpoints in the preceding retained set, as required for successive
nonaxial thresholds.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.PositiveIteration

def restrictedChain (a : ℝ) (K : Kernel KineticPhase Velocity)
    (S : ℕ → Set Velocity) (hS : ∀ i, MeasurableSet (S i))
    (f : KineticPhase → ℝ≥0∞) (i : ℕ) : ℕ → KineticPhase → ℝ≥0∞
  | 0 => f
  | n+1 => step a (K.restrict (hS (i+1))) (restrictedChain a K S hS f (i+1) n)

theorem restrictedChain_measurable (a : ℝ) (K : Kernel KineticPhase Velocity)
    [IsSFiniteKernel K] (S : ℕ → Set Velocity) (hS : ∀ i, MeasurableSet (S i))
    {f : KineticPhase → ℝ≥0∞} (hf : Measurable f) (i n : ℕ) :
    Measurable (restrictedChain a K S hS f i n) := by
  induction n generalizing i with
  | zero => exact hf
  | succ n ih => exact step_measurable a _ (ih (i+1))

theorem step_restrict_slab_mono {a T : ℝ} (K : Kernel KineticPhase Velocity)
    {S : Set Velocity} (hS : MeasurableSet S) {f g : KineticPhase → ℝ≥0∞}
    (h : ∀ z, z.1.1 ∈ Icc a T → z.2 ∈ S → f z ≤ g z)
    {z : KineticPhase} (hz : z.1.1 ∈ Icc a T) :
    step a (K.restrict hS) f z ≤ step a (K.restrict hS) g z := by
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  change (∫⁻ v in S, f ((flight z s).1,v) ∂K (flight z s)) ≤
    ∫⁻ v in S, g ((flight z s).1,v) ∂K (flight z s)
  apply setLIntegral_mono' hS
  intro v hv
  exact h _ ⟨hs.1.le,hs.2.trans hz.2⟩ hv

theorem restrict_add_compl (K : Kernel KineticPhase Velocity)
    {S : Set Velocity} (hS : MeasurableSet S) :
    K.restrict hS+K.restrict hS.compl = K := by
  ext z A hA
  change (K z).restrict S A+(K z).restrict Sᶜ A = K z A
  exact congrArg (fun μ : Measure Velocity => μ A) (Measure.restrict_add_restrict_compl hS)

theorem restrictedChain_deletion_bound {a T : ℝ} (K : Kernel KineticPhase Velocity)
    [IsSFiniteKernel K] (S : ℕ → Set Velocity) (hS : ∀ i, MeasurableSet (S i))
    {C B δ : ℝ≥0∞} (hK : ∀ z, z.1.1 ∈ Icc a T → K z univ ≤ C)
    {f : KineticPhase → ℝ≥0∞} (hfm : Measurable f)
    (hf : ∀ z, z.1.1 ∈ Icc a T → f z ≤ B) (i n : ℕ)
    (hsmall : ∀ j, i ≤ j → j < i+n → ∀ z, z.1.1 ∈ Icc a T → z.2 ∈ S j →
      K z (S (j+1))ᶜ ≤ δ) :
    ∀ z, z.1.1 ∈ Icc a T → z.2 ∈ S i →
      iterate a K f n z ≤ restrictedChain a K S hS f i n z+
        (δ*ENNReal.ofReal (T-a))*deletionCoefficient B (C*ENNReal.ofReal (T-a)) n := by
  let P := C*ENNReal.ofReal (T-a)
  let Q := δ*ENNReal.ofReal (T-a)
  induction n generalizing i with
  | zero => simp only [iterate,restrictedChain,deletionCoefficient,mul_zero,add_zero,
      le_refl,implies_true]
  | succ n ih =>
    intro z hz hzS
    let L := K.restrict (hS (i+1))
    let D := K.restrict (hS (i+1)).compl
    let E := Q*deletionCoefficient B P n
    have hLD : L+D = K := restrict_add_compl K (hS (i+1))
    have hL : ∀ y, y.1.1 ∈ Icc a T → L y univ ≤ C := by
      intro y hy
      exact (Measure.restrict_apply_le _ _).trans (hK y hy)
    have htail : ∀ y, y.1.1 ∈ Icc a T → y.2 ∈ S (i+1) →
        iterate a K f n y ≤ restrictedChain a K S hS f (i+1) n y+E := by
      apply ih (i+1)
      intro j hj hjn
      exact hsmall j (by omega) (by omega)
    have hgood := step_restrict_slab_mono K (hS (i+1)) htail hz
    have hm := restrictedChain_measurable a K S hS hfm (i+1) n
    have hadd := congrFun (step_add a L (g := fun _ => E) hm) z
    have hsplit := congrFun (step_add_kernel a L D (iterate_measurable a K hfm n)) z
    have hconst : step a L (fun _ => E) z ≤ E*P :=
      step_uniform_bound L hL (fun _ _ => le_rfl) hz
    have hbad : step a D (iterate a K f n) z ≤ B*P^n*Q := by
      unfold step
      calc
        _ ≤ ∫⁻ _s in Ioc a z.1.1, (B*P^n)*δ := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          have ht : s ∈ Icc a T := ⟨hs.1.le,hs.2.trans hz.2⟩
          calc
            _ ≤ ∫⁻ _v, B*P^n ∂D (flight z s) := lintegral_mono
              (fun v => iterate_uniform_bound K hK hf n _ ht)
            _ = (B*P^n)*K (flight z s) (S (i+1))ᶜ := by
              rw [lintegral_const]
              change (B*P^n)*(K (flight z s)).restrict (S (i+1))ᶜ univ = _
              rw [Measure.restrict_apply_univ]
            _ ≤ _ := mul_le_mul' le_rfl (hsmall i le_rfl (by omega) _ ht hzS)
        _ ≤ ((B*P^n)*δ)*ENNReal.ofReal (T-a) := by
          rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioc]
          exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (sub_le_sub_right hz.2 a))
        _ = _ := by dsimp [Q]; ring
    calc
      iterate a K f (n+1) z = step a L (iterate a K f n) z+
          step a D (iterate a K f n) z := by
        change step a K (iterate a K f n) z = _
        simpa only [hLD,Pi.add_apply] using hsplit
      _ ≤ step a L (fun y => restrictedChain a K S hS f (i+1) n y+E) z+B*P^n*Q :=
        add_le_add hgood hbad
      _ = (restrictedChain a K S hS f i (n+1) z+step a L (fun _ => E) z)+B*P^n*Q := by
        change step a L (restrictedChain a K S hS f (i+1) n+(fun _ => E)) z+_ = _
        rw [hadd,Pi.add_apply]
        rfl
      _ ≤ (restrictedChain a K S hS f i (n+1) z+E*P)+B*P^n*Q :=
        add_le_add (add_le_add le_rfl hconst) le_rfl
      _ = restrictedChain a K S hS f i (n+1) z+
          (δ*ENNReal.ofReal (T-a))*deletionCoefficient B (C*ENNReal.ofReal (T-a)) (n+1) := by
        change (_+(Q*deletionCoefficient B P n)*P)+B*P^n*Q =
          _+Q*(B*P^n+P*deletionCoefficient B P n)
        ring

end BoltzmannNonuniqueness.PositiveIteration

end

end

end OAI
