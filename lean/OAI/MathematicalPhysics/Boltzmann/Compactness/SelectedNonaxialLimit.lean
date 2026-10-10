import OAI.MathematicalPhysics.Boltzmann.Branching.CentralRetainedLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.DilatedTwoCoreLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.RetainedWindowDeletion
import OAI.MathematicalPhysics.Boltzmann.Compactness.SelectedOriginDeletion
import OAI.MathematicalPhysics.Boltzmann.Jets.CoreDensityTranslation
import OAI.MathematicalPhysics.Boltzmann.Jets.OriginMeshLimit

namespace OAI

section

/-! # The Gaussian remainder selected by the actual main-core regions -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

def copyRemainderDensity (r s₀ η K α γ d₀ : ℝ) (i : Label) (z : KineticPhase) : ℝ≥0∞ :=
  ENNReal.ofReal r*ENNReal.ofReal
    (JetRemainderSheet.remainder η K α γ (JetGeometry.jetScale s₀ η i.annulus)
      (d₀*JetGeometry.jetScale s₀ η i.annulus^10) (r*z.1.1) i.positive
      (JetPeriodicDatum.spatialMap (r • z.1.2)-displacement i.lattice) z.2)

def selectedRemainderDensity (r s₀ η K α γ d₀ : ℝ) (N : ℕ) (z : KineticPhase) : ℝ≥0∞ := by
  classical
  exact ∑' i : Label, if z.1 ∈ mainCoreRegion s₀ η r N i
    then copyRemainderDensity r s₀ η K α γ d₀ i z else 0

theorem selectedCoreDensity_eq {s₀ η r : ℝ} {N : ℕ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (K α γ d₀ : ℝ) {z : KineticPhase} {i : Label}
    (hi : z.1 ∈ mainCoreRegion s₀ η r N i) :
    selectedCoreDensity r s₀ η K α γ d₀ N z = copyCoreDensity r s₀ η K α γ d₀ i z := by
  classical
  rw [selectedCoreDensity,tsum_eq_single i]
  · simp only [hi,ite_true]
  · intro j hji
    have hj : z.1 ∉ mainCoreRegion s₀ η r N j :=
      fun hj => hji (mainCoreRegion_unique hs₀ hsmax hη hηmax hj hi)
    simp only [hj,ite_false]

theorem selectedRemainderDensity_eq {s₀ η r : ℝ} {N : ℕ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (K α γ d₀ : ℝ) {z : KineticPhase} {i : Label}
    (hi : z.1 ∈ mainCoreRegion s₀ η r N i) :
    selectedRemainderDensity r s₀ η K α γ d₀ N z = copyRemainderDensity r s₀ η K α γ d₀ i z := by
  classical
  rw [selectedRemainderDensity,tsum_eq_single i]
  · simp only [hi,ite_true]
  · intro j hji
    have hj : z.1 ∉ mainCoreRegion s₀ η r N j :=
      fun hj => hji (mainCoreRegion_unique hs₀ hsmax hη hηmax hj hi)
    simp only [hj,ite_false]

theorem selectedRemainderDensity_eq_zero (r s₀ η K α γ d₀ : ℝ) (N : ℕ)
    (z : KineticPhase) (hz : ∀ i, z.1 ∉ mainCoreRegion s₀ η r N i) :
    selectedRemainderDensity r s₀ η K α γ d₀ N z = 0 := by
  classical
  simp only [selectedRemainderDensity,hz,ite_false,tsum_zero]

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Uniformly small gain from the selected Gaussian remainder -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem selectedRemainder_gain_bound {r s₀ η K α γ d₀ q : ℝ} {N : ℕ}
    (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) (hq₁ : 1 < q) (hq₂ : q < 2)
    (x : SpaceTime) (ht : 0 < x.1) {v : Velocity} (hv : transverse v ≠ 0) :
    normalizedChartGain (volume.withDensity
      (fun p => selectedRemainderDensity r s₀ η K α γ d₀ N (x,p))) q v ≤
      ENNReal.ofReal r*(ENNReal.ofReal (JetRemainderSheet.uniformConstant K)*
        SheetTotal.bound q (2*Real.exp (16*(1+α)^2))) := by
  classical
  by_cases hi : ∃ i, x ∈ mainCoreRegion s₀ η r N i
  · obtain ⟨i,hi⟩ := hi
    have hs : 0 < JetGeometry.jetScale s₀ η i.annulus := DatumBounds.scale_pos hs₀ _
    have hsle : JetGeometry.jetScale s₀ η i.annulus ≤ 1/8 := by
      have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (i.annulus+1))
      have hle : DatumBounds.scale s₀ η (i.annulus+1) ≤ s₀ := by
        simpa only [DatumBounds.scale,Nat.cast_zero,neg_zero,zero_mul,Real.exp_zero,mul_one] using h
      exact hle.trans hsmax
    have he : (fun p => selectedRemainderDensity r s₀ η K α γ d₀ N (x,p)) =
        (fun p => copyRemainderDensity r s₀ η K α γ d₀ i (x,p)) := by
      funext p
      exact selectedRemainderDensity_eq hs₀ hsmax hη hηmax K α γ d₀ hi
    rw [he]
    let f : Velocity → ℝ≥0∞ := fun p => ENNReal.ofReal (JetRemainderSheet.remainder η K α γ
        (JetGeometry.jetScale s₀ η i.annulus) (d₀*JetGeometry.jetScale s₀ η i.annulus^10)
        (r*x.1) i.positive (JetPeriodicDatum.spatialMap (r • x.2)-displacement i.lattice) p)
    have hm : Measurable f := by
      apply Measurable.ennreal_ofReal
      exact measurable_const.mul (JetBarrierCollision.measurable_velocity (by positivity)
        η K α γ _ _ _ _)
    change normalizedChartGain (volume.withDensity (ENNReal.ofReal r • f)) q v ≤ _
    rw [withDensity_smul _ hm]
    exact JetRemainderSheet.dilated_gain_bound hK hα hs (hsle.trans (by norm_num)) hd₀ hdmax
      (JetEnvelopeGain.thermal_width_le hdmax hs.le hsle) (mul_pos hr ht)
      (hi.2.1.trans (by norm_num)) hq₁ hq₂ r η i.positive _ hv
  · have he : (fun p => selectedRemainderDensity r s₀ η K α γ d₀ N (x,p)) = 0 := by
      funext p
      exact selectedRemainderDensity_eq_zero _ _ _ _ _ _ _ _ _ (fun i h => hi ⟨i,h⟩)
    rw [he]
    simp only [withDensity_zero,normalizedChartGain,chartGain,MeasureTheory.lintegral_zero_measure,mul_zero]
    exact bot_le

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Five selected gains vanish at bounded nonaxial endpoints -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.FiveGainMap
open BoltzmannNonuniqueness.PositiveIteration
open BoltzmannNonuniqueness.GeometricMesh
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

attribute [local irreducible] selectedFreeKernel retainedFreeKernel awayOriginKernel

theorem selected_five_nonaxial_tendsto
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {K α γ q a T R₀ b₀ X s₀ η d₀ θ : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hR₀ : 0 < R₀) (hb₀ : 0 < b₀)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) (hθ : 0 < θ)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hphase : Tendsto (fun n => phase (s₀/r n) η) atTop (𝓝 θ)) (N : ℕ → ℕ)
    (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    (states : ℕ → State) (hstates : Tendsto states atTop (𝓝 (t₀,x,v)))
    (htime : ∀ n, (states n).1 ∈ Icc a T)
    (hposition : ∀ n, ‖WithLp.toLp 2 (states n).2.1‖ ≤ X)
    (hvelocity : ∀ n, WithLp.toLp 2 (states n).2.2 ∈ velocityWindow R₀ b₀)
    {g : ℕ → Published.KineticPhase → ℝ≥0∞} {B : ℝ≥0∞}
    (hB : B ≠ ∞) (hg : ∀ n, Measurable (g n)) (hgB : ∀ n z, g n z ≤ B)
    (hL : ∀ C : Set Published.KineticPhase, IsCompact C →
      Tendsto (fun n => ∫⁻ z in C, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => iterate a (selectedFreeKernel (r n) s₀ η K α γ d₀ q (N n))
      (g n) 5 (toKinetic (states n))) atTop (𝓝 0) := by
  let G := JetCoreSheet.growthConstant K α γ q
  let C := ENNReal.ofReal (G/a)
  let Δ := ENNReal.ofReal (T-a)
  let D := deletionCoefficient B (C*Δ) 5
  let W := (3*Δ+C)*D+1
  have hG : 0 ≤ G := JetCoreSheet.growthConstant_nonneg hK α γ q
  have hD : D ≠ ∞ := deletionCoefficient_ne_top hB
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) 5
  have hW : W ≠ ∞ := by
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top,
        ENNReal.ofReal_ne_top⟩) hD,by norm_num⟩
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨e,he,heε⟩ := ENNReal.exists_nnreal_pos_mul_lt hW hε.ne'
  have heR : 0 < (e : ℝ) := NNReal.coe_pos.mpr he
  obtain ⟨Vmax,β,S,hS,hV,hβ,hS0,hbound,hcut⟩ := retained_window_deletion hK hα hγ hq₁ hq₂
    ha heR hR₀ hb₀ hs₀ hsmax hη hηmax hd₀ hdmax hr hrlim 5 hg (fun n z _ => hgB n z)
  let M := (G+1)/(e:ℝ)
  have hM : 0 < M := div_pos (by linarith) heR
  have hGM : G/M ≤ (e:ℝ) := by
    apply (div_le_iff₀ hM).mpr
    have hmul : (e:ℝ)*M = G+1 := by dsimp [M]; field_simp
    linarith
  let ρ := (e:ℝ)*β/2
  have hρ : 0 < ρ := div_pos (mul_pos heR hβ) (by norm_num)
  have hρeq : 2*ρ/β = (e:ℝ) := by dsimp [ρ]; field_simp
  have hinit (n : ℕ) : WithLp.toLp 2 (states n).2.2 ∈ S 0 := hS0.symm ▸ hvelocity n
  have hcone (n : ℕ) : inSpatialCone X T Vmax (toKinetic (states n)) := by
    apply (hposition n).trans
    exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr (htime n).2) hV.le)
  have htail := central_retained_five_tendsto (M := M) hMityagin hK hα hγ
    (le_of_lt (zero_lt_one.trans hq₁)) ha hβ hV.le hs₀ hsmax hη hηmax hd₀ hθ hρ
    r hr hrlim hphase N t₀ x v hv states hstates htime hcone S hS hbound hinit hB hg hgB hL
  have hepos : (0 : ℝ≥0∞) < e := ENNReal.coe_pos.mpr he
  filter_upwards [hcut,ENNReal.tendsto_nhds_zero.mp htail e hepos] with n hn htn
  let z := toKinetic (states n)
  have hz : z.1.1 ∈ Icc a T := htime n
  have hscale := selected_scale_deletion (hr n) hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax
    hq₁ hq₂ ha hM (N n) (hg n) (fun z _ => hgB n z) 5 hz
  have hwindow := hn M (N n) z hz (hvelocity n)
  have hmass (y : Published.KineticPhase) (hy : y.1.1 ∈ Icc a T) :
      retainedFreeKernel (r n) s₀ η K α γ d₀ q M (N n) y univ ≤ C := by
    apply (retainedFreeKernel_bound (hr n) hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax hq₁ hq₂
      (N n) y (ha.trans_le hy.1)).trans
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left hG ha hy.1)
  have horigin := restrictedChain_origin_deletion hρ.le hβ 0
    (retainedFreeKernel (r n) s₀ η K α γ d₀ q M (N n)) S hS
    (fun i w hw => (hbound i w hw).2) hmass (hg n) (fun z _ => hgB n z) 0 5 z hz (hinit n)
  have hscaleError : (ENNReal.ofReal (G/M)*Δ)*D ≤ ((e:ℝ≥0∞)*Δ)*D := by
    apply mul_le_mul' (mul_le_mul' _ le_rfl) le_rfl
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hGM
  calc
    _ ≤ (restrictedChain a (retainedFreeKernel (r n) s₀ η K α γ d₀ q M (N n))
        S hS (g n) 0 5 z+((e:ℝ≥0∞)+e)*Δ*D)+((e:ℝ≥0∞)*Δ)*D := by
      apply hscale.trans
      apply add_le_add _ hscaleError
      simpa only [ENNReal.ofReal_coe_nnreal] using hwindow
    _ ≤ ((e+C*(e:ℝ≥0∞)*D)+((e:ℝ≥0∞)+e)*Δ*D)+((e:ℝ≥0∞)*Δ)*D := by
      apply add_le_add (add_le_add _ le_rfl) le_rfl
      apply horigin.trans
      simpa only [hρeq,ENNReal.ofReal_coe_nnreal] using add_le_add htn (le_refl (C*(e:ℝ≥0∞)*D))
    _ = (e:ℝ≥0∞)*W := by dsimp only [W]; ring
    _ ≤ ε := heε.le

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
