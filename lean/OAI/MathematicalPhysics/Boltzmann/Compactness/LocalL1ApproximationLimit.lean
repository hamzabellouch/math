import OAI.MathematicalPhysics.Boltzmann.Branching.AveragingTailSources
import OAI.MathematicalPhysics.Boltzmann.Branching.CompactCapFamily
import OAI.MathematicalPhysics.Boltzmann.Branching.ComplexWeakL2Diagonal
import OAI.MathematicalPhysics.Boltzmann.Branching.RationalUniformApproximation
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicRenormalizedCompactness
import OAI.MathematicalPhysics.Boltzmann.Compactness.RenormalizedIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1ToWeakStar
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations

namespace OAI

section

/-! # The actual gain divided by one plus density is uniformly integrable locally -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem gain_unit_uniformIntegrable_local
    {f : ℕ → X × Velocity → ℝ} {N : ℕ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p) (hN : ∀ n, 0 < N n)
    (hi : UniformIntegrable (fun n p => gain (N n) (f n) p/normalizer (f n) p)
      1 (μ.prod volume)) :
    UniformIntegrable (fun n p => gain (N n) (f n) p/(1+f n p)) 1
      (μ.prod ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))) := by
  have hres := uniformIntegrable_restrict hi (univ ×ˢ Metric.closedBall (0:Velocity) R)
  rw [← Measure.prod_restrict,Measure.restrict_univ] at hres
  have hvel : ∀ᵐ p ∂μ.prod ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)),
      p.2 ∈ Metric.closedBall (0:Velocity) R :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_closedBall)
  apply uniformIntegrable_change_normalizer
    (fun n => gain_measurable (N n) (hfm n)) hfm
    (fun n p => (gain_bounds (hN n) (hfm n) (hf n) p).1) hf (maxwellianLower_pos R) _ hres
  filter_upwards [hvel] with p hp
  exact maxwellianLower_le hR (by simpa only [Metric.mem_closedBall,dist_zero_right] using hp)

theorem approximatingSolution_gain_unit_uniformIntegrable_local
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyMoment f)) {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    let F := fun n => (approximatingSolution f hfm (n+Nat.ceil T)).kineticProfile
    let N := fun n : ℕ => ((n+Nat.ceil T:ℕ):ℝ)+1
    UniformIntegrable (fun n p => gain (N n) (F n) p/(1+F n p)) 1
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))) := by
  apply gain_unit_uniformIntegrable_local hR
    (fun n => (approximatingSolution f hfm (n+Nat.ceil T)).kineticProfile_measurable)
    (fun n p => (approximatingSolution f hfm (n+Nat.ceil T)).nonnegative _)
    (fun n => by positivity)
  exact (approximatingSolution_normalizedSources_uniformIntegrable f hfm hf hi hT).1

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Local strong L2 convergence controls the local L1 seminorm -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.Published

theorem localL2_L1_bound (K : Set FourierSpace)
    (a : Lp ℂ 2 (volume : Measure FourierSpace)) :
    eLpNorm (a : FourierSpace → ℂ) 1 (volume.restrict K) ≤
      ENNReal.ofReal ‖complexL2Restriction K a‖ * volume K ^ (1/2 : ℝ) := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict K) (f := (a : FourierSpace → ℂ)) (p := 1) (q := 2)
    (by norm_num) (Lp.aestronglyMeasurable a).restrict
  have he : eLpNorm (a : FourierSpace → ℂ) 2 (volume.restrict K) =
      ENNReal.ofReal ‖complexL2Restriction K a‖ := by
    rw [ofReal_norm,complexL2Restriction,Lp.enorm_toLp]
  rw [he] at h
  convert h using 1; norm_num

theorem localL2_L1_tendsto {u : ℕ → Lp ℂ 2 (volume : Measure FourierSpace)}
    (K : Set FourierSpace) (hK : volume K < ⊤)
    (hu : Tendsto (fun n => ‖complexL2Restriction K (u n)‖) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (u n : FourierSpace → ℂ) 1 (volume.restrict K)) atTop (𝓝 0) := by
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hu
  have hb := ENNReal.Tendsto.mul_const h
    (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by positivity : (0:ℝ) ≤ 1/2) hK.ne))
  have hb' : Tendsto (fun n => ENNReal.ofReal ‖complexL2Restriction K (u n)‖ *
      volume K ^ (1/2 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,ENNReal.ofReal_zero,zero_mul] using hb
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb'
    (fun _ => bot_le) (fun n => localL2_L1_bound K (u n))

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Uniform integrability of the physical loss with a unit density normalizer -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.CollisionCompactness
open Compactness PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem physicalLoss_unit_uniformIntegrable_local
    {f : ℕ → X × Velocity → ℝ} {R C : ℝ} (hR : 0 ≤ R)
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C) :
    UniformIntegrable (fun n p => lossDensity (f n) p/(1+f n p)) 1
      (μ.prod ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))) := by
  have hres := uniformIntegrable_restrict (renormalized_loss_uniformIntegrable hfm hf hi hb)
    (univ ×ˢ Metric.closedBall (0:Velocity) R)
  rw [← Measure.prod_restrict,Measure.restrict_univ] at hres
  have hvel : ∀ᵐ p ∂μ.prod ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)),
      p.2 ∈ Metric.closedBall (0:Velocity) R :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_closedBall)
  apply uniformIntegrable_change_normalizer
    (fun n => lossDensity_measurable (hfm n)) hfm
    (fun n p => lossDensity_nonneg (hf n) p) hf (maxwellianLower_pos R) _ hres
  filter_upwards [hvel] with p hp
  exact maxwellianLower_le hR (by simpa only [Metric.mem_closedBall,dist_zero_right] using hp)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Local factorization of pair moments along the actual averaging subsequence -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

theorem local_pair_moment_factorization {T : ℝ} {μ : Measure SpaceTime} [SFinite μ]
    (hμ : μ ≤ timeSpaceVolume T)
    {f : ℕ → KineticPhase → ℝ} {g : KineticPhase → ℝ}
    {W : SpaceTime × (Velocity × Velocity) → ℝ}
    (hfm : ∀ n, Measurable (f n))
    (hfi : ∀ n, Integrable (f n) (μ.prod volume))
    (hpUI : UniformIntegrable (fun (n : ℕ) (z : SpaceTime × (Velocity × Velocity)) =>
      f n (z.1,z.2.1)*f n (z.1,z.2.2)) 1 (μ.prod volume))
    (hg : WeakL1Converges (μ.prod volume) f g)
    (hW : WeakL1Converges (μ.prod volume)
      (fun n z => f n (z.1,z.2.1)*f n (z.1,z.2.2)) W)
    {k l : KineticPhase → ℝ} (hk : Continuous k) (hl : Continuous l)
    (hkc : HasCompactSupport k) (hlc : HasCompactSupport l)
    {A B : SpaceTime → ℝ}
    (hA : TimeLocalL1Converges T (fun n x => ∫ v, k (x,v)*f n (x,v)) A)
    (hB : TimeLocalL1Converges T (fun n x => ∫ v, l (x,v)*f n (x,v)) B)
    {K : Set SpaceTime} (hK : IsCompact K) [IsFiniteMeasure (μ.restrict K)] :
    (fun x => ∫ y : Velocity × Velocity, (k (x,y.1)*l (x,y.2))*W (x,y)) =ᵐ[μ.restrict K]
      (fun x => (∫ v, k (x,v)*g (x,v))*(∫ w, l (x,w)*g (x,w))) := by
  have hμv : μ ≤ (volume : Measure SpaceTime) := hμ.trans
    (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hmK := Measure.restrict_mono_measure hμ K
  have hAi := (hA.1.integrableOn_isCompact hK).mono_measure hμv
  have hBi := (hB.1.integrableOn_isCompact hK).mono_measure hμv
  have hA' : Tendsto (fun n => eLpNorm (fun x => (∫ v, k (x,v)*f n (x,v))-A x) 1
      (μ.restrict K)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hA.2 K hK)
      (fun _ => zero_le) (fun _ => eLpNorm_mono_measure _ hmK)
  have hB' : Tendsto (fun n => eLpNorm (fun x => (∫ v, l (x,v)*f n (x,v))-B x) 1
      (μ.restrict K)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hB.2 K hK)
      (fun _ => zero_le) (fun _ => eLpNorm_mono_measure _ hmK)
  have hfK (n) : Integrable (f n) ((μ.restrict K).prod volume) := by
    exact (hfi n).mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hpK (n) : Integrable (fun z : SpaceTime × (Velocity × Velocity) =>
      f n (z.1,z.2.1)*f n (z.1,z.2.2)) ((μ.restrict K).prod (volume.prod volume)) := by
    have hi : Integrable (fun z : SpaceTime × (Velocity × Velocity) =>
        f n (z.1,z.2.1)*f n (z.1,z.2.2))
        ((μ.restrict K).prod (volume : Measure (Velocity × Velocity))) :=
      (memLp_one_iff_integrable.mp (hpUI.memLp n)).mono_measure
        (Measure.prod_mono Measure.restrict_le_self le_rfl)
    simpa only [Measure.volume_eq_prod] using hi
  have hgK := hg.restrict_base hK.measurableSet
  have hWK := hW.restrict_base hK.measurableSet
  rw [Measure.volume_eq_prod] at hWK
  obtain ⟨C,hC⟩ := hk.bounded_above_of_compact_support hkc
  obtain ⟨D,hD⟩ := hl.bounded_above_of_compact_support hlc
  have hui := Compactness.uniformIntegrable_restrict
    (Compactness.uniformIntegrable_compact_average_product hfm hpUI hk hl hkc hlc) K
  have he := weak_pair_moment_factorization hfm hfK hpK hgK hWK hk.measurable hl.measurable
    C D hC hD hAi hBi hA' hB' hui
  simpa only [← Measure.volume_eq_prod] using he

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Uniform integral bounds on finite balls give a global integral bound -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.Published

theorem lintegral_le_of_closedBall_bounds (f : FourierSpace → ℝ≥0∞) (B : ℝ≥0∞)
    (h : ∀ n : ℕ, (∫⁻ x in Metric.closedBall (0 : FourierSpace) n, f x) ≤ B) :
    (∫⁻ x, f x) ≤ B := by
  let μ := (volume : Measure FourierSpace).withDensity f
  have hm : Monotone (fun n : ℕ => Metric.closedBall (0 : FourierSpace) n) := by
    intro n m hnm
    exact Metric.closedBall_subset_closedBall (by exact_mod_cast hnm)
  have he : (∫⁻ x, f x) = μ (Set.univ : Set FourierSpace) := by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [he,← Metric.iUnion_closedBall_nat (0 : FourierSpace),hm.measure_iUnion]
  exact iSup_le (fun n => by simpa only [μ,withDensity_apply _ measurableSet_closedBall] using h n)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Global L1 bounds pass through local L1 convergence -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.Published

theorem localL1_global_bound {u : ℕ → FourierSpace → ℂ} {g : FourierSpace → ℂ}
    (hg : AEStronglyMeasurable g volume) (B : ℝ≥0∞)
    (hu : ∀ n, eLpNorm (u n) 1 volume ≤ B)
    (hc : ∀ K : Set FourierSpace, volume K < ⊤ →
      Tendsto (fun n => eLpNorm (u n-g) 1 (volume.restrict K)) atTop (𝓝 0)) :
    eLpNorm g 1 volume ≤ B := by
  rw [eLpNorm_one_eq_lintegral_enorm hg]
  apply lintegral_le_of_closedBall_bounds
  intro m
  let K := Metric.closedBall (0 : FourierSpace) (m : ℝ)
  have hK : volume K < ⊤ := measure_closedBall_lt_top
  have he n : eLpNorm g 1 (volume.restrict K) ≤
      eLpNorm (u n-g) 1 (volume.restrict K)+B := by
    have hid : g = (g-u n)+u n := by funext x; simp
    calc
      _ = eLpNorm ((g-u n)+u n) 1 (volume.restrict K) := by rw [← hid]
      _ ≤ eLpNorm (g-u n) 1 (volume.restrict K)+eLpNorm (u n) 1 (volume.restrict K) :=
        eLpNorm_add_le (by norm_num)
      _ ≤ eLpNorm (u n-g) 1 (volume.restrict K)+B := by
        rw [eLpNorm_sub_comm]
        exact add_le_add_right ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hu n)) _
  have ht : Tendsto (fun n => eLpNorm (u n-g) 1 (volume.restrict K)+B) atTop (𝓝 B) := by
    simpa using (hc K hK).add_const B
  have h := ge_of_tendsto ht (Eventually.of_forall he)
  simpa only [eLpNorm_one_eq_lintegral_enorm hg.restrict] using h

theorem localL2_global_L1_bound {u : ℕ → Lp ℂ 2 (volume : Measure FourierSpace)}
    {g : Lp ℂ 2 (volume : Measure FourierSpace)} (B : ℝ≥0∞)
    (hu : ∀ n, eLpNorm (u n : FourierSpace → ℂ) 1 volume ≤ B)
    (hc : ∀ K : Set FourierSpace, volume K < ⊤ →
      Tendsto (fun n => ‖complexL2Restriction K (u n-g)‖) atTop (𝓝 0)) :
    eLpNorm (g : FourierSpace → ℂ) 1 volume ≤ B := by
  apply localL1_global_bound (Lp.aestronglyMeasurable g) B hu
  intro K hK
  have h := localL2_L1_tendsto K hK (hc K hK)
  have he n : eLpNorm (u n-g : Lp ℂ 2 volume) 1 (volume.restrict K) =
      eLpNorm ((u n : FourierSpace → ℂ)-(g : FourierSpace → ℂ)) 1 (volume.restrict K) :=
    eLpNorm_congr_ae (ae_restrict_of_ae (Lp.coeFn_sub _ _))
  simpa only [he] using h

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Local L1 convergence is stable under differences -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.Published

theorem eLpNorm_sub_triangle {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g h : X → ℂ) : eLpNorm (f-h) 1 μ ≤ eLpNorm (f-g) 1 μ+eLpNorm (g-h) 1 μ := by
  have he : f-h = (f-g)+(g-h) := by ext x; simp
  rw [he]
  exact eLpNorm_add_le (by norm_num)

theorem localL1_difference_tendsto {u v : ℕ → FourierSpace → ℂ}
    {g h : FourierSpace → ℂ} (K : Set FourierSpace)
    (hu : Tendsto (fun n => eLpNorm (u n-g) 1 (volume.restrict K)) atTop (𝓝 0))
    (hv : Tendsto (fun n => eLpNorm (v n-h) 1 (volume.restrict K)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm ((u n-v n)-(g-h)) 1 (volume.restrict K)) atTop (𝓝 0) := by
  have he n : (u n-v n)-(g-h) = (u n-g)-(v n-h) := by ext x; simp only [Pi.sub_apply]; ring
  have hb n : eLpNorm ((u n-v n)-(g-h)) 1 (volume.restrict K) ≤
      eLpNorm (u n-g) 1 (volume.restrict K)+eLpNorm (v n-h) 1 (volume.restrict K) := by
    rw [he]
    exact eLpNorm_sub_le (by norm_num)
  have ht : Tendsto (fun n => eLpNorm (u n-g) 1 (volume.restrict K)+
      eLpNorm (v n-h) 1 (volume.restrict K)) atTop (𝓝 0) := by simpa using hu.add hv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) hb

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Limits of uniform L1 approximations are Cauchy in global L1 -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.Published

theorem localL1_approximation_difference_bound
    (f : ℕ → FourierSpace → ℂ) (u : ℕ → ℕ → FourierSpace → ℂ)
    (g : ℕ → FourierSpace → ℂ) (hg : ∀ m, Integrable (g m))
    (δ : ℕ → ℝ) (hδ : ∀ m, 0 ≤ δ m)
    (he : ∀ m n, eLpNorm (f n-u m n) 1 volume ≤ ENNReal.ofReal (δ m))
    (hc : ∀ m (K : Set FourierSpace), volume K < ⊤ →
      Tendsto (fun n => eLpNorm (u m n-g m) 1 (volume.restrict K)) atTop (𝓝 0))
    (m k : ℕ) : eLpNorm (g m-g k) 1 volume ≤ ENNReal.ofReal (δ m+δ k) := by
  apply localL1_global_bound ((hg m).sub (hg k)).aestronglyMeasurable
  · intro n
    have h := eLpNorm_sub_triangle volume (u m n) (f n) (u k n)
    rw [eLpNorm_sub_comm (u m n) (f n)] at h
    apply h.trans
    simpa only [ENNReal.ofReal_add (hδ m) (hδ k)] using add_le_add (he m n) (he k n)
  · intro K hK
    exact localL1_difference_tendsto K (hc m K hK) (hc k K hK)

theorem localL1_approximation_cauchy
    (f : ℕ → FourierSpace → ℂ) (u : ℕ → ℕ → FourierSpace → ℂ)
    (g : ℕ → FourierSpace → ℂ) (hg : ∀ m, Integrable (g m))
    (δ : ℕ → ℝ) (hδ : ∀ m, 0 ≤ δ m) (hδ0 : Tendsto δ atTop (𝓝 0))
    (he : ∀ m n, eLpNorm (f n-u m n) 1 volume ≤ ENNReal.ofReal (δ m))
    (hc : ∀ m (K : Set FourierSpace), volume K < ⊤ →
      Tendsto (fun n => eLpNorm (u m n-g m) 1 (volume.restrict K)) atTop (𝓝 0)) :
    CauchySeq (fun m => (hg m).toL1 (g m)) := by
  have hb m k := localL1_approximation_difference_bound f u g hg δ hδ he hc m k
  have hd m k : dist ((hg m).toL1 (g m)) ((hg k).toL1 (g k)) ≤ δ m+δ k := by
    apply (ENNReal.ofReal_le_ofReal_iff (add_nonneg (hδ m) (hδ k))).mp
    rw [dist_eq_norm,L1.ofReal_norm_sub_eq_lintegral]
    have hae : (fun x => ‖(hg m).toL1 (g m) x-(hg k).toL1 (g k) x‖ₑ) =ᵐ[volume]
        (fun x => ‖(g m-g k) x‖ₑ) := by
      filter_upwards [(hg m).coeFn_toL1,(hg k).coeFn_toL1] with x hm hk
      simp only [hm,hk,Pi.sub_apply]
    rw [lintegral_congr_ae hae]
    simpa only [eLpNorm_one_eq_lintegral_enorm ((hg m).sub (hg k)).aestronglyMeasurable] using hb m k
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hδ0.eventually (gt_mem_nhds (half_pos hε)))
  exact ⟨N,fun m hm k hk => (hd m k).trans_lt (by linarith [hN m hm,hN k hk])⟩

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Identification on compact subsets of a local weak-convergence window -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

theorem WeakL1Converges.eq_of_local_strong
    {X : Type*} [NormedAddCommGroup X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {Ω E : Set X} {f : ℕ → X → ℝ} {g A : X → ℝ}
    (h : WeakL1Converges (μ.restrict Ω) f g)
    (hf : ∀ᶠ n in atTop, Integrable (f n) (μ.restrict Ω))
    (hA : LocallyIntegrable A μ) (hE : IsCompact E) (hEΩ : E ⊆ Ω)
    (hstrong : Tendsto (fun n => eLpNorm (fun x => f n x-A x) 1 (μ.restrict E))
      atTop (𝓝 0)) : A =ᵐ[μ.restrict E] g := by
  have hr := h.restrict hE.measurableSet
  rw [Measure.restrict_restrict_of_subset hEΩ] at hr
  apply hr.eq_of_strong_eventually _ (hA.integrableOn_isCompact hE) hstrong
  filter_upwards [hf] with n hn
  exact hn.mono_measure (Measure.restrict_mono hEΩ le_rfl)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Transfer of local strong convergence through eventual equality on a window -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.Published

theorem LocalL1Converges.congr_on_window {f h : ℕ → SpaceTime → ℝ}
    {g : SpaceTime → ℝ} (hf : LocalL1Converges f g) {Ω : Set SpaceTime}
    (he : ∀ᶠ n in atTop, h n =ᵐ[volume.restrict Ω] f n) :
    ∀ K : Set SpaceTime, IsCompact K → K ⊆ Ω →
      Tendsto (fun n => eLpNorm (fun z => h n z-g z) 1 (volume.restrict K)) atTop (𝓝 0) := by
  intro K hK hKΩ
  apply (hf.2 K hK).congr'
  filter_upwards [he] with n hn
  apply eLpNorm_congr_ae
  have hkn := hn.filter_mono (ae_mono (Measure.restrict_mono hKΩ le_rfl))
  filter_upwards [hkn] with z hz
  rw [hz]

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Completing a sequence uniformly approximated by locally compact families -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.Published

theorem localL1_approximation_limit
    (f : ℕ → FourierSpace → ℂ) (u : ℕ → ℕ → FourierSpace → ℂ)
    (g : ℕ → FourierSpace → ℂ) (hg : ∀ m, Integrable (g m))
    (δ : ℕ → ℝ) (hδ : ∀ m, 0 ≤ δ m) (hδ0 : Tendsto δ atTop (𝓝 0))
    (he : ∀ m n, eLpNorm (f n-u m n) 1 volume ≤ ENNReal.ofReal (δ m))
    (hc : ∀ m (K : Set FourierSpace), volume K < ⊤ →
      Tendsto (fun n => eLpNorm (u m n-g m) 1 (volume.restrict K)) atTop (𝓝 0)) :
    ∃ q : Lp ℂ 1 (volume : Measure FourierSpace),
      ∀ K : Set FourierSpace, volume K < ⊤ →
        Tendsto (fun n => eLpNorm (f n-(q : FourierSpace → ℂ)) 1 (volume.restrict K)) atTop (𝓝 0) := by
  obtain ⟨q,hq⟩ := cauchySeq_tendsto_of_complete
    (localL1_approximation_cauchy f u g hg δ hδ hδ0 he hc)
  have hq0 : Tendsto (fun m => eLpNorm (g m-(q : FourierSpace → ℂ)) 1 volume) atTop (𝓝 0) := by
    have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hq.sub_const q).norm)
    have heq m : ENNReal.ofReal ‖(hg m).toL1 (g m)-q‖ = eLpNorm (g m-(q : FourierSpace → ℂ)) 1 volume := by
      rw [L1.ofReal_norm_sub_eq_lintegral,
        eLpNorm_one_eq_lintegral_enorm ((hg m).sub (L1.integrable_coeFn q)).aestronglyMeasurable]
      apply lintegral_congr_ae
      filter_upwards [(hg m).coeFn_toL1] with x hx
      simp only [hx,Pi.sub_apply]
    simpa only [Function.comp_def,sub_self,norm_zero,ENNReal.ofReal_zero,heq] using ht
  have herror : Tendsto (fun m => ENNReal.ofReal (δ m)+eLpNorm (g m-(q : FourierSpace → ℂ)) 1 volume) atTop (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.ofReal_zero,zero_add] using
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hδ0).add hq0
  refine ⟨q,fun K hK => ?_⟩
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hh : 0 < ε/2 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨m,hm⟩ := (ENNReal.tendsto_nhds_zero.mp herror (ε/2) hh).exists
  filter_upwards [ENNReal.tendsto_nhds_zero.mp (hc m K hK) (ε/2) hh] with n hn
  calc
    eLpNorm (f n-(q : FourierSpace → ℂ)) 1 (volume.restrict K) ≤
        eLpNorm (f n-u m n) 1 (volume.restrict K)+eLpNorm (u m n-(q : FourierSpace → ℂ)) 1 (volume.restrict K) :=
      eLpNorm_sub_triangle _ _ _ _
    _ ≤ ENNReal.ofReal (δ m)+(eLpNorm (u m n-g m) 1 (volume.restrict K)+eLpNorm (g m-(q : FourierSpace → ℂ)) 1 volume) := by
      apply add_le_add ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (he m n))
      exact (eLpNorm_sub_triangle _ _ _ _).trans
        (add_le_add le_rfl (eLpNorm_mono_measure _ Measure.restrict_le_self))
    _ = (ENNReal.ofReal (δ m)+eLpNorm (g m-(q : FourierSpace → ℂ)) 1 volume)+eLpNorm (u m n-g m) 1 (volume.restrict K) := by ac_rfl
    _ ≤ ε/2+ε/2 := add_le_add hm hn
    _ = ε := ENNReal.add_halves ε

end BoltzmannNonuniqueness.Published

end

end

end OAI
