import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionWeakMarginals
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongCompactPairTests
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1ToWeakStar
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

section

/-! # Extending supported weak convergence from a measurable region -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.of_restrict_support {μ : Measure X}
    {f : ℕ → X → ℝ} {g : X → ℝ} {s : Set X} (hs : MeasurableSet s)
    (h : WeakL1Converges (μ.restrict s) f g)
    (hf : ∀ n x, x ∉ s → f n x = 0) (hg : ∀ x, x ∉ s → g x = 0) :
    WeakL1Converges μ f g := by
  have heg : s.indicator g = g := by
    funext x
    by_cases hx : x ∈ s
    · exact indicator_of_mem hx g
    · rw [indicator_of_notMem hx,hg x hx]
  refine ⟨h.1,?_,?_⟩
  · have hi := (integrable_indicator_iff hs).mpr h.2.1
    rwa [heg] at hi
  · intro ψ hψ hB
    have he (u : X → ℝ) (hu : ∀ x, x ∉ s → u x = 0) :
        (∫ x in s, ψ x*u x ∂μ) = ∫ x, ψ x*u x ∂μ := by
      rw [← integral_indicator hs]
      congr 1
      funext x
      by_cases hx : x ∈ s
      · exact indicator_of_mem hx _
      · rw [indicator_of_notMem hx,hu x hx,mul_zero]
    simpa only [he _ (hf _),he _ hg] using h.2.2 ψ hψ hB

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Weak positive source integrals with strongly convergent survival kernels -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Published
open Compactness
variable {P : Type*} [MeasurableSpace P]
variable {μ : Measure ℝ} {ν : Measure P} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

def survivalVolterra (μ : Measure ℝ) (a : (ℝ × P) × ℝ → ℝ)
    (f : ℝ × P → ℝ) (z : ℝ × P) : ℝ :=
  ∫ s, if s ≤ z.1 then a (z,s)*f (s,z.2) else 0 ∂μ

theorem WeakL1Converges.survivalVolterra
    {f : ℕ → ℝ × P → ℝ} {g : ℝ × P → ℝ}
    {a : ℕ → (ℝ × P) × ℝ → ℝ} {b : (ℝ × P) × ℝ → ℝ}
    (hw : WeakL1Converges (μ.prod ν) f g) (hui : UniformIntegrable f 1 (μ.prod ν))
    (hfm : ∀ n, Measurable (f n)) (ham : ∀ n, Measurable (a n)) (hbm : Measurable b)
    (C : ℝ≥0) (ha : ∀ n z, |a n z| ≤ C) (hb : ∀ z, |b z| ≤ C)
    (hs : Tendsto (fun n => eLpNorm (a n-b) 1 ((μ.prod ν).prod μ)) atTop (𝓝 0)) :
    WeakL1Converges (μ.prod ν) (fun n => survivalVolterra μ (a n) (f n))
      (survivalVolterra μ b g) := by
  have hfi n := memLp_one_iff_integrable.mp (hui.memLp n)
  have hprod := hw.prod_constant (ν := μ) hfi
  have hlm n : Measurable (fun z : (ℝ × P) × ℝ => f n (z.2,z.1.2)) :=
    (hfm n).comp (measurable_snd.prodMk measurable_fst.snd)
  have hlg : Measurable (fun z : (ℝ × P) × ℝ => g (z.2,z.1.2)) :=
    hw.1.comp (measurable_snd.prodMk measurable_fst.snd)
  have hl : WeakL1Converges ((μ.prod ν).prod μ)
      (fun n z => f n (z.2,z.1.2)) (fun z => g (z.2,z.1.2)) := by
    apply WeakL1Converges.of_comp_measurePreserving (timeExchange_measurePreserving μ ν) hlm hlg
    exact hprod
  have hut : UniformIntegrable (fun n (z : (ℝ × P) × ℝ) => f n z.1) 1 ((μ.prod ν).prod μ) := by
    simpa only [mul_one] using uniformIntegrable_tensor hfm hui measurable_const
      (integrable_const (1:ℝ) : Integrable (fun _ : ℝ => (1:ℝ)) μ)
  have hul : UniformIntegrable (fun n (z : (ℝ × P) × ℝ) => f n (z.2,z.1.2))
      1 ((μ.prod ν).prod μ) := by
    apply uniformIntegrable_of_comp_measurePreserving (timeExchange_measurePreserving μ ν) hlm
    exact hut
  have hv := hl.varying_bounded_mul hul hlm ham hbm C ha hb hs
  have hvi n : Integrable (fun z : (ℝ × P) × ℝ => a n z*f n (z.2,z.1.2))
      ((μ.prod ν).prod μ) :=
    (memLp_one_iff_integrable.mp (hul.memLp n)).bdd_mul (ham n).aestronglyMeasurable
      (ae_of_all _ (ha n))
  let k : (ℝ × P) × ℝ → ℝ := fun z => if z.2 ≤ z.1.1 then 1 else 0
  have hkm : Measurable k := measurable_const.ite
    (measurableSet_le measurable_snd measurable_fst.fst) measurable_const
  have hkb : ∀ z, |k z| ≤ 1 := by intro z; dsimp [k]; split <;> norm_num
  have h := hv.marginal hvi hkm 1 hkb
  have he (A : (ℝ × P) × ℝ → ℝ) (F : ℝ × P → ℝ) :
      (fun z : ℝ × P => ∫ s, k (z,s)*(A (z,s)*F (s,z.2)) ∂μ) =
        Published.survivalVolterra μ A F := by
    funext z
    apply integral_congr_ae
    filter_upwards [] with s
    dsimp only [k,Published.survivalVolterra]
    split <;> simp
  have hseq : (fun n (z : ℝ × P) => ∫ s, k (z,s)*(a n (z,s)*f n (s,z.2)) ∂μ) =
      (fun n => Published.survivalVolterra μ (a n) (f n)) := funext (fun n => he (a n) (f n))
  rw [hseq,he b g] at h
  exact h

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Weak gain and loss convergence needs pair integrability only eventually -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.Published

theorem WeakL1Converges.of_add {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} {g : X → ℝ} {N : ℕ}
    (h : WeakL1Converges μ (fun n => f (n+N)) g) : WeakL1Converges μ f g :=
  ⟨h.1,h.2.1,fun ψ hψ hB => (tendsto_add_atTop_iff_nat N).mp (h.2.2 ψ hψ hB)⟩

end BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.CollisionCompactness

theorem weak_gainLoss_eventually {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hfn : ∀ n z, 0 ≤ f n z) (hgm : Measurable g)
    (h : Published.WeakL1Converges (μ.prod (volume : Measure (Velocity × Velocity)))
      (fun n => pairDensity (f n)) (pairDensity g))
    (hf : ∀ᶠ n in atTop, Integrable (pairDensity (f n))
      (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Published.WeakL1Converges (μ.prod volume) (fun n => gainDensity (f n)) (gainDensity g) ∧
      Published.WeakL1Converges (μ.prod volume) (fun n => lossDensity (f n)) (lossDensity g) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hf
  have ht := weak_gainLoss (fun n => hfm (n+N)) (fun n => hfn (n+N)) hgm
    (h.comp (tendsto_add_atTop_nat N)) (fun n => hN (n+N) (Nat.le_add_left N n))
  exact ⟨ht.1.of_add,ht.2.of_add⟩

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # A conserved integral passes through strong convergence of its density -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Published
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem conserved_marginal_of_strong {μ : Measure X} [IsFiniteMeasure μ]
    {ν : Measure Y} [SFinite ν] {F : ℕ → X × Y → ℝ} {g : X × Y → ℝ}
    (hFi : ∀ n, Integrable (F n) (μ.prod ν)) (hgm : Measurable g)
    (hgi : Integrable g (μ.prod ν))
    (hs : Tendsto (fun n => eLpNorm (fun p => F n p-g p) 1 (μ.prod ν)) atTop (𝓝 0))
    {c : ℕ → ℝ} {a : ℝ} (hc : Tendsto c atTop (𝓝 a))
    (he : ∀ n, (fun x => ∫ y, F n (x,y) ∂ν) =ᵐ[μ] fun _ => c n) :
    (fun x => ∫ y, g (x,y) ∂ν) =ᵐ[μ] fun _ => a := by
  have hw := (weakL1_of_eLpNorm_sub hFi hgm hgi hs).marginal hFi
    (k := fun _ => (1:ℝ)) measurable_const 1 (fun _ => by norm_num)
  simp only [one_mul] at hw
  have hconst : WeakL1Converges μ (fun n _ => c n) (fun _ => a) := by
    refine ⟨measurable_const,integrable_const a,?_⟩
    intro ψ _ _
    simp only [integral_mul_const]
    exact tendsto_const_nhds.mul hc
  exact (hw.congr_sequence he).unique hconst

end BoltzmannNonuniqueness.Published

end

end

end OAI
