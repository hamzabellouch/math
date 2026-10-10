import OAI.MathematicalPhysics.Boltzmann.Branching.MainCoreScaleWindow
import OAI.MathematicalPhysics.Boltzmann.Branching.RestrictedCone
import OAI.MathematicalPhysics.Boltzmann.Branching.RetainedAxialDecay
import OAI.MathematicalPhysics.Boltzmann.Branching.TranslatedTwoCoreLimit
import OAI.MathematicalPhysics.Boltzmann.Jets.PeriodicJetFamilies
import OAI.MathematicalPhysics.Boltzmann.Jets.OriginMeshLimit
import OAI.MathematicalPhysics.Boltzmann.Jets.OriginMeshStep

namespace OAI

section

/-! # The central cube gives the closest periodic origin in every coordinate -/

noncomputable section

open Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.JetCopyDatum

namespace BoltzmannNonuniqueness.TorusChart

theorem interval_abs_le_shift {x : ℝ} (hx : x ∈ interval) (n : ℤ) : |x| ≤ |x-(n:ℝ)| := by
  by_cases hn : n = 0
  · simp [hn]
  have h1 : (1:ℝ) ≤ |(n:ℝ)| := by simpa using integer_distance hn
  have hx' : |x| ≤ 1/2 := abs_le.mpr ⟨hx.1.le,hx.2⟩
  have h := abs_add_le ((n:ℝ)-x) x
  rw [sub_add_cancel,abs_sub_comm] at h
  linarith

theorem scaled_coordinate_nearest {r x : ℝ} (hr : 0 < r)
    (hx : r*x ∈ interval) (n : ℤ) : |x| ≤ |x-r⁻¹*(n:ℝ)| := by
  have h := interval_abs_le_shift hx n
  have he : r*x-(n:ℝ) = r*(x-r⁻¹*(n:ℝ)) := by field_simp
  rw [he,abs_mul,abs_mul,abs_of_pos hr] at h
  nlinarith

theorem central_coordinate_nearest {r : ℝ} (hr : 0 < r) {x : Velocity}
    (hx : r • x ∈ cube) (k : Lattice) (i : Fin 3) :
    |x i| ≤ |(x-r⁻¹ • latticeVector k) i| :=
  scaled_coordinate_nearest hr (hx i) (k i)

theorem central_axial_nearest {r : ℝ} (hr : 0 < r) {x : Velocity}
    (hx : r • x ∈ cube) (k : Lattice) :
    |axial x| ≤ |axial (x-r⁻¹ • latticeVector k)| :=
  central_coordinate_nearest hr hx k (Fin.last 2)

theorem central_transverse_nearest {r : ℝ} (hr : 0 < r) {x : Velocity}
    (hx : r • x ∈ cube) (k : Lattice) :
    ‖transverse x‖ ≤ ‖transverse (x-r⁻¹ • latticeVector k)‖ := by
  have hs : ‖transverse x‖^2 ≤ ‖transverse (x-r⁻¹ • latticeVector k)‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    have h := central_coordinate_nearest hr hx k i.castSucc
    change x i.castSucc^2 ≤ ((x-r⁻¹ • latticeVector k) i.castSucc)^2
    exact sq_le_sq.mpr h
  nlinarith [norm_nonneg (transverse x),norm_nonneg (transverse (x-r⁻¹ • latticeVector k))]

end BoltzmannNonuniqueness.TorusChart

end

end

section

/-! # The retained kernel away from the origin is controlled by the compact mesh window -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem central_away_retained_le_originScale {s₀ η r K α γ d₀ q ρ M : ℝ} {N : ℕ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hr : 0 < r) (z : Published.KineticPhase) (hz : r • z.1.2 ∈ TorusChart.cube) :
    awayOriginKernel 0 ρ (retainedFreeKernel r s₀ η K α γ d₀ q M N) z ≤
      originScaleKernel r s₀ η K α γ d₀ q (ρ/Real.exp η) M N 0 z := by
  classical
  by_cases hnear : z ∈ nearOriginRegion 0 ρ
  · simp only [awayOriginKernel,Kernel.piecewise_apply,hnear,ite_true]
    exact bot_le
  have haway : ρ ≤ ‖transverse z.1.2‖ := by
    change ¬ ‖transverse z.1.2-0‖ < ρ at hnear
    simpa only [sub_zero] using le_of_not_gt hnear
  simp only [awayOriginKernel,Kernel.piecewise_apply,hnear,ite_false]
  rcases retainedFreeKernel_zero_or_copy hs₀ hsmax hη hηmax z with hzero | ⟨i,hi,hscale,he⟩
  · rw [hzero]
    exact bot_le
  have hk : i.lattice = 0 := enlargement_central_lattice hs₀ hsmax hη hi.2.1 hz hi.2.2
  have hl : ρ ≤ ‖transverse (z.1.2-r⁻¹ • latticeVector i.lattice)‖ := by
    rw [hk]
    have h0 : latticeVector (0 : Lattice) = 0 := by simp [latticeVector]; rfl
    simpa only [h0,smul_zero,sub_zero] using haway
  have hw := mainCoreRegion_retained_scale_window hs₀ hη hr hi hl le_rfl
  have hright := originScaleKernel_eq_copy (K := K) (α := α) (γ := γ) (d₀ := d₀) (q := q)
    hs₀ hsmax hη hηmax hi hk hw.1.le hscale
  rw [he,hright]

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Almost-everywhere bounds on one scaled periodic cell extend globally -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetCopyDatum BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.TorusChart

theorem exists_lattice_central {r : ℝ} (hr : 0 < r) (x : Velocity) :
    ∃ k : Lattice, r • (x-r⁻¹ • latticeVector k) ∈ cube := by
  let k : Lattice := fun i => ⌈r*x i-1/2⌉
  refine ⟨k,?_⟩
  intro i
  have hle := Int.le_ceil (r*x i-1/2)
  have hlt := Int.ceil_lt_add_one (r*x i-1/2)
  have he : (r • (x-r⁻¹ • latticeVector k)) i = r*x i-(k i:ℝ) := by
    change r*(x i-r⁻¹*(k i:ℝ)) = _
    field_simp
  change -(1/2:ℝ) < _ ∧ _ ≤ 1/2
  rw [he]
  dsimp [k]
  constructor <;> linarith

theorem ae_le_of_central {r c : ℝ} (hr : 0 < r)
    {f : Velocity × Velocity → ℝ}
    (hper : ∀ k : Lattice, ∀ p, f (p.1-r⁻¹ • latticeVector k,p.2) = f p)
    (hb : ∀ᵐ p ∂(volume : Measure (Velocity × Velocity)), r • p.1 ∈ cube → f p ≤ c) :
    ∀ᵐ p ∂(volume : Measure (Velocity × Velocity)), f p ≤ c := by
  have hm (k : Lattice) : MeasurePreserving
      (fun p : Velocity × Velocity => (p.1-r⁻¹ • latticeVector k,p.2)) volume volume := by
    exact (measurePreserving_sub_right volume (r⁻¹ • latticeVector k)).prod
      (MeasurePreserving.id (volume : Measure Velocity))
  have hall : ∀ᵐ p ∂(volume : Measure (Velocity × Velocity)), ∀ k : Lattice,
      r • (p.1-r⁻¹ • latticeVector k) ∈ cube → f p ≤ c := by
    apply ae_all_iff.mpr
    intro k
    filter_upwards [(hm k).quasiMeasurePreserving.ae hb] with p hp
    simpa only [hper] using hp
  filter_upwards [hall] with p hp
  obtain ⟨k,hk⟩ := exists_lattice_central hr p.1
  exact hp k hk

end BoltzmannNonuniqueness.TorusChart

end

end

section

/-! # Retained nonaxial paths vanish using their bounded backward cone -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.FiveGainMap
open BoltzmannNonuniqueness.PositiveIteration
open BoltzmannNonuniqueness.GeometricMesh
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem central_retained_five_tendsto
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {K α γ qexp a T b Vmax X s₀ η d₀ θ ρ M : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq : 0 ≤ qexp)
    (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hd₀ : 0 < d₀) (hθ : 0 < θ) (hρ : 0 < ρ)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hphase : Tendsto (fun n => phase (s₀/r n) η) atTop (𝓝 θ)) (N : ℕ → ℕ)
    (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    (states : ℕ → State) (hstates : Tendsto states atTop (𝓝 (t₀,x,v)))
    (htime : ∀ n, (states n).1 ∈ Icc a T)
    (hcone : ∀ n, inSpatialCone X T Vmax (toKinetic (states n)))
    (S : ℕ → Set Velocity) (hS : ∀ i, MeasurableSet (S i))
    (hbound : ∀ i w, w ∈ S i → ‖w‖ ≤ Vmax ∧ b ≤ ‖transverse w‖)
    (hinit : ∀ n, WithLp.toLp 2 (states n).2.2 ∈ S 0)
    {g : ℕ → Published.KineticPhase → ℝ≥0∞} {B : ℝ≥0∞}
    (hB : B ≠ ∞) (hg : ∀ n, Measurable (g n)) (hgB : ∀ n z, g n z ≤ B)
    (hL : ∀ C : Set Published.KineticPhase, IsCompact C →
      Tendsto (fun n => ∫⁻ z in C, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => restrictedChain a
      (awayOriginKernel 0 ρ (retainedFreeKernel (r n) s₀ η K α γ d₀ qexp M (N n)))
      S hS (g n) 0 5 (toKinetic (states n))) atTop (𝓝 0) := by
  have hlim := origin_scale_five_tendsto (M := M) hMityagin hK hα hγ hq ha hb hV
    hs₀ hsmax hη hηmax hd₀ hθ (div_pos hρ (Real.exp_pos η)) r hr hrlim hphase N
    t₀ x v hv states hstates htime S hS hbound hinit hB hg hgB hL
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun _ => bot_le))
  have hr' : Tendsto (fun n => r n*(X+T*Vmax)) atTop (𝓝 0) := by
    simpa only [zero_mul] using hrlim.mul_const (X+T*Vmax)
  have hsmall := hr'.eventually (gt_mem_nhds (show (0 : ℝ) < 1/2 by norm_num))
  filter_upwards [hsmall] with n hn
  apply restrictedChain_cone_mono _ _ S hS (fun i w hw => (hbound i w hw).1) ?_
    (g n) 0 5 (toKinetic (states n)) (htime n) (hcone n) (hinit n)
  intro i z hz hcz _
  exact central_away_retained_le_originScale hs₀ hsmax hη hηmax (hr n) z
    (small_scaled_cone_in_cube ha.le hV (hr n).le hn hz hcz)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
