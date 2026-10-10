import OAI.MathematicalPhysics.Boltzmann.Branching.DilatedTwoCoreLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.TwoCoreLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.FiniteThermalLimit
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricMesh
import OAI.MathematicalPhysics.Boltzmann.Jets.JetCoreMomentBound

namespace OAI

section

/-! # The actual geometric mesh supplies the two-core scale and width bounds -/

noncomputable section

open Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.GeometricMesh

/-- The cardinality bound is independent of the dilation and cutoff index. -/
theorem exists_retained_scale_list {s₀ η r μ R : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (hr : 0 < r) (hμ : 0 < μ) (N : ℕ) :
    ∃ S : Finset ℝ, S.card ≤ (Finset.Icc (index (μ/Real.exp η) η) (index R η)).card ∧
      ∀ j < N, μ ≤ JetGeometry.jetScale s₀ η j/r →
        JetGeometry.jetScale s₀ η j/r ≤ R → JetGeometry.jetScale s₀ η j/r ∈ S := by
  classical
  let J := (Finset.range N).filter fun j =>
    μ ≤ JetGeometry.jetScale s₀ η j/r ∧ JetGeometry.jetScale s₀ η j/r ≤ R
  refine ⟨J.image (fun j => JetGeometry.jetScale s₀ η j/r),?_,?_⟩
  · exact Finset.card_image_le.trans (retained_scale_card_le hs₀ hη hr hμ J
      (fun j hj => (Finset.mem_filter.mp hj).2))
  · intro j hj hlo hhi
    exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hlo,hhi⟩,rfl⟩

theorem retained_thermal_width_le {s₀ η r d₀ R : ℝ} (hr : 0 < r)
    (hd₀ : 0 ≤ d₀) {j : ℕ} (hs₀ : 0 < s₀)
    (hscale : JetGeometry.jetScale s₀ η j/r ≤ R) :
    d₀*JetGeometry.jetScale s₀ η j^10 ≤ d₀*(r*R)^10 := by
  have hs := DatumBounds.scale_pos hs₀ (η := η) (j+1)
  have hb : JetGeometry.jetScale s₀ η j ≤ r*R := by
    simpa only [mul_comm] using (div_le_iff₀ hr).mp hscale
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.le hb 10) hd₀

theorem retained_thermal_width_tendsto (d₀ R : ℝ) {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => d₀*(r n*R)^10) atTop (𝓝 0) := by
  simpa using tendsto_const_nhds.mul ((hr.mul_const R).pow 10)

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # The finite retained geometric mesh has vanishing fifth gain -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.FiveGainMap
open BoltzmannNonuniqueness.PositiveIteration
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.GeometricMesh

namespace BoltzmannNonuniqueness.JetCoreSheet

abbrev MeshLabel (J : Finset ℤ) := {k : ℤ // k ∈ J} × Bool

def meshScale (s₀ η : ℝ) (r : ℕ → ℝ) {J : Finset ℤ} (n : ℕ) (j : MeshLabel J) : ℝ :=
  JetGeometry.jetScale s₀ η (jetIndex s₀ η r j.1.val n)

theorem geometric_thermal_five_tendsto
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {K α γ qexp a T b Vmax s₀ η d₀ θ : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : 0 ≤ qexp) (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (hs₀ : 0 < s₀) (hη : 0 < η) (hd₀ : 0 < d₀) (hθ : 0 < θ)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hphase : Tendsto (fun n => phase (s₀/r n) η) atTop (𝓝 θ)) (J : Finset ℤ)
    (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    (states : ℕ → State) (hstates : Tendsto states atTop (𝓝 (t₀,x,v)))
    (hinit : ∀ n, ‖WithLp.toLp 2 (states n).2.2‖ ≤ Vmax ∧
      b ≤ ‖transverse (WithLp.toLp 2 (states n).2.2)‖)
    (weight : ℕ → Fin 5 → MeshLabel J → Published.KineticPhase → ℝ≥0∞)
    (hwm : ∀ n i j, Measurable (weight n i j)) (hw : ∀ n i j z, weight n i j z ≤ 1)
    (hweight : ∀ n i j z, weight n i j z ≠ 0 →
      z.1.1 ∈ Icc a T ∧ ‖z.2‖ ≤ Vmax ∧ b ≤ ‖transverse z.2‖)
    {g : ℕ → Published.KineticPhase → ℝ≥0∞} {M : ℝ≥0∞}
    (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n)) (hgM : ∀ n z, g n z ≤ M)
    (hL : ∀ C : Set Published.KineticPhase, IsCompact C →
      Tendsto (fun n => ∫⁻ z in C, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => finiteGainChain a
      (thermalKernelFamily (r n) η K α γ qexp
        (fun _ j => meshScale s₀ η r n j/r n)
        (fun _ j => d₀*meshScale s₀ η r n j^10) (fun _ j => j.2))
      (cycleFive (weight n)) (g n) 0 5 (toKinetic (states n))) atTop (𝓝 0) := by
  have hs (n : ℕ) (j : MeshLabel J) : 0 < meshScale s₀ η r n j :=
    DatumBounds.scale_pos hs₀ _
  apply finite_thermal_five_tendsto hMityagin hK hα hγ hq ha hb hV
    (fun _ j => j.2) η (fun _ j => θ*Real.exp (η*(j.1.val:ℝ)))
    (fun _ _ => mul_pos hθ (Real.exp_pos _))
    (fun n _ j => meshScale s₀ η r n j/r n)
    (fun n _ j => d₀*meshScale s₀ η r n j^10)
    (fun n _ j => div_pos (hs n j) (hr n))
    (fun n _ j => mul_pos hd₀ (pow_pos (hs n j) 10))
    (fun _ j => jet_scale_approximation hs₀ hη hr hrlim hphase j.1.val)
    (fun _ j => mesh_width_tendsto_zero hs₀ hη hr hrlim hphase d₀ j.1.val)
    t₀ x v hv states hstates r hr hinit weight hwm hw hweight hM hg hgM hL

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Two dilated gains for the actual geometric scales and thermal widths -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem geometric_two_core_axial_tendsto {K α γ q a s₀ η d₀ M : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (r t₁ t₂ : ℕ → ℝ) (N j₁ : ℕ → ℕ) (j₂ : ℕ → Velocity → ℕ)
    (sign₁ : ℕ → Bool) (sign₂ : ℕ → Velocity → Bool)
    (x : ℕ → JetPrototype.Space) (v : ℕ → Velocity) (y₂ : ℕ → Velocity → Transverse)
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (ht₂ : ∀ n, a ≤ t₂ n) (htt : ∀ n, t₂ n ≤ t₁ n)
    (hj₂ : ∀ n w, j₂ n w < N n)
    (hscale : ∀ n w, JetGeometry.jetScale s₀ η (j₂ n w)/r n ≤ M)
    (hv : Tendsto (fun n => ‖transverse (v n)‖) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ w,
      rescaledBallisticSecondCoreMass (r n) η K α γ q (t₁ n) (t₂ n) (x n).2
        (fun w => JetGeometry.jetScale s₀ η (j₂ n w)/r n)
        (fun w => d₀*JetGeometry.jetScale s₀ η (j₂ n w)^10) (sign₂ n) (y₂ n) w
      ∂rescaledCoreMeasure (r n) η K α γ (JetGeometry.jetScale s₀ η (j₁ n)/r n)
        (d₀*JetGeometry.jetScale s₀ η (j₁ n)^10) q (sign₁ n) (t₁ n) (x n) (v n))
      atTop (𝓝 0) := by
  have hpos (j : ℕ) : 0 < JetGeometry.jetScale s₀ η j := DatumBounds.scale_pos hs₀ _
  have hwidth (j : ℕ) : d₀*JetGeometry.jetScale s₀ η j^10 ≤ 1/16 :=
    JetEnvelopeGain.thermal_width_le hdmax (hpos j).le
      ((JetEscapedTotal.scale_bound hs₀ hη j).trans hsmax)
  apply rescaled_two_core_axial_tendsto hK hα hγ hq₁ hq₂ ha r (fun _ => η)
    (fun n => JetGeometry.jetScale s₀ η (j₁ n)/r n)
    (fun n => d₀*JetGeometry.jetScale s₀ η (j₁ n)^10) t₁ t₂
    (fun n => d₀*(r n*M)^10) sign₁ x v
    (fun n w => JetGeometry.jetScale s₀ η (j₂ n w)/r n)
    (fun n w => d₀*JetGeometry.jetScale s₀ η (j₂ n w)^10) sign₂ y₂ hr
  · exact fun n => div_pos (hpos _) (hr n)
  · exact fun _ => mul_pos hd₀ (pow_pos (hpos _) _)
  · exact fun _ => hwidth _
  · exact ht₂
  · exact htt
  · exact fun n _ => div_pos (hpos _) (hr n)
  · exact fun _ _ => mul_pos hd₀ (pow_pos (hpos _) _)
  · exact fun _ _ => hwidth _
  · exact fun n w => GeometricMesh.retained_thermal_width_le (hr n) hd₀.le hs₀ (hscale n w)
  · exact GeometricMesh.retained_thermal_width_tendsto d₀ M hrlim
  · exact hv
  · intro μ hμ
    refine ⟨(Finset.Icc (GeometricMesh.index (μ/Real.exp η) η) (GeometricMesh.index M η)).card,?_⟩
    intro n
    obtain ⟨S,hS,hmem⟩ := GeometricMesh.exists_retained_scale_list hs₀ hη (hr n) hμ (N n)
    exact ⟨S,hS,fun w hw => hmem _ (hj₂ n w) hw (hscale n w)⟩

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Uniformity in both collision times for the geometric two-core integral -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

def geometricTwoCoreMass (r s₀ η K α γ d₀ q : ℝ) (j₁ : ℕ) (j₂ : Velocity → ℕ)
    (sign₁ : Bool) (sign₂ : Velocity → Bool) (x : JetPrototype.Space) (v : Velocity)
    (y₂ : Velocity → Transverse) (τ : ℝ × ℝ) : ℝ≥0∞ :=
  ∫⁻ w, rescaledBallisticSecondCoreMass r η K α γ q τ.1 τ.2 x.2
    (fun w => JetGeometry.jetScale s₀ η (j₂ w)/r)
    (fun w => d₀*JetGeometry.jetScale s₀ η (j₂ w)^10) sign₂ y₂ w
    ∂rescaledCoreMeasure r η K α γ (JetGeometry.jetScale s₀ η j₁/r)
      (d₀*JetGeometry.jetScale s₀ η j₁^10) q sign₁ τ.1 x v

variable {K α γ q a s₀ η d₀ M : ℝ}
  (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
  (ha : 0 < a) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
  (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
  (r V : ℕ → ℝ) (N : ℕ → ℕ) (j₁ : ℕ → ℝ × ℝ → ℕ)
  (j₂ : ℕ → ℝ × ℝ → Velocity → ℕ)
  (sign₁ : ℕ → ℝ × ℝ → Bool) (sign₂ : ℕ → ℝ × ℝ → Velocity → Bool)
  (x : ℕ → ℝ × ℝ → JetPrototype.Space) (v : ℕ → ℝ × ℝ → Velocity)
  (y₂ : ℕ → ℝ × ℝ → Velocity → Transverse)
  (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0)) (hV : Tendsto V atTop (𝓝 0))
  (hj₂ : ∀ n τ w, a ≤ τ.2 → τ.2 ≤ τ.1 → j₂ n τ w < N n)
  (hscale : ∀ n τ w, a ≤ τ.2 → τ.2 ≤ τ.1 →
    JetGeometry.jetScale s₀ η (j₂ n τ w)/r n ≤ M)
  (hv : ∀ n τ, a ≤ τ.2 → τ.2 ≤ τ.1 → ‖transverse (v n τ)‖ ≤ V n)

include hK hα hγ hq₁ hq₂ ha hs₀ hsmax hη hd₀ hdmax hr hrlim hV hj₂ hscale hv in
theorem geometric_two_core_uniform {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ τ : ℝ × ℝ, a ≤ τ.2 → τ.2 ≤ τ.1 →
      geometricTwoCoreMass (r n) s₀ η K α γ d₀ q (j₁ n τ) (j₂ n τ)
        (sign₁ n τ) (sign₂ n τ) (x n τ) (v n τ) (y₂ n τ) τ ≤ ENNReal.ofReal ε := by
  obtain ⟨μ,hμ,hsmall⟩ := rescaled_two_core_small_integral hK hα hγ hq₁ hq₂ ha hε
  let J := (Finset.Icc (GeometricMesh.index (μ/Real.exp η) η) (GeometricMesh.index M η)).card
  obtain ⟨d,r₀,hd,hr₀,hs⟩ := hsmall J
  have hD := GeometricMesh.retained_thermal_width_tendsto d₀ M hrlim
  filter_upwards [hD.eventually (gt_mem_nhds hd),hV.eventually (gt_mem_nhds hr₀)]
    with n hnD hnV τ ht₂ htt
  obtain ⟨S,hS,hmem⟩ := GeometricMesh.exists_retained_scale_list hs₀ hη (hr n) hμ (N n)
  have hpos (j : ℕ) : 0 < JetGeometry.jetScale s₀ η j := DatumBounds.scale_pos hs₀ _
  have hwidth (j : ℕ) : d₀*JetGeometry.jetScale s₀ η j^10 ≤ 1/16 :=
    JetEnvelopeGain.thermal_width_le hdmax (hpos j).le
      ((JetEscapedTotal.scale_bound hs₀ hη j).trans hsmax)
  apply hs (hr n) (div_pos (hpos _) (hr n)) (mul_pos hd₀ (pow_pos (hpos _) _))
    (hwidth _) ht₂ htt η (sign₁ n τ) (x n τ) (v n τ) S
    (fun w => JetGeometry.jetScale s₀ η (j₂ n τ w)/r n)
    (fun w => d₀*JetGeometry.jetScale s₀ η (j₂ n τ w)^10) (sign₂ n τ) (y₂ n τ)
    ((hv n τ ht₂ htt).trans hnV.le) hS
  · exact fun _ => div_pos (hpos _) (hr n)
  · exact fun _ => mul_pos hd₀ (pow_pos (hpos _) _)
  · exact fun _ => hwidth _
  · exact fun w => (GeometricMesh.retained_thermal_width_le (hr n) hd₀.le hs₀
      (hscale n τ w ht₂ htt)).trans hnD.le
  · exact fun w hw => hmem _ (hj₂ n τ w ht₂ htt) hw (hscale n τ w ht₂ htt)

include hK hα hγ hq₁ hq₂ ha hs₀ hsmax hη hd₀ hdmax hr hrlim hV hj₂ hscale hv in
theorem geometric_two_core_time_tendsto (T : ℝ) :
    Tendsto (fun n => ∫⁻ t₁ in Ioc a T, ∫⁻ t₂ in Ioc a t₁,
      geometricTwoCoreMass (r n) s₀ η K α γ d₀ q (j₁ n (t₁,t₂)) (j₂ n (t₁,t₂))
        (sign₁ n (t₁,t₂)) (sign₂ n (t₁,t₂)) (x n (t₁,t₂)) (v n (t₁,t₂))
        (y₂ n (t₁,t₂)) (t₁,t₂)) atTop (𝓝 0) := by
  apply GainPullback.two_time_uniform_tendsto
  intro ε hε
  obtain ⟨e,he,heε⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (by simp : (1 : ℝ≥0∞) ≠ ∞) hε.ne'
  have he' : (0 : ℝ) < e := he
  have heε' : ENNReal.ofReal (e : ℝ) ≤ ε := by simpa using heε.le
  filter_upwards [geometric_two_core_uniform hK hα hγ hq₁ hq₂ ha hs₀ hsmax hη hd₀ hdmax
    r V N j₁ j₂ sign₁ sign₂ x v y₂ hr hrlim hV hj₂ hscale hv he'] with n hn
  intro t₁ _ t₂ ht₂
  exact (hn (t₁,t₂) ht₂.1.le ht₂.2).trans heε'

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
