import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.PositiveFunctions
import OAI.Geometry.TamingCompatibility.Functional.QuadraticShell

namespace OAI

section

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace TamingCompatibility.FourthShell
open QuadraticShell
lemma dyadic_term_identity (C r : ℝ) (n : ℕ) :
    (1/64:ℝ)^n*(C*(2^(n+1)*r)^4) = 16*C*r^4*(1/4:ℝ)^n := by
  have hpow : ((2:ℝ)^n)^4 = ((2:ℝ)^4)^n := by
    rw [← pow_mul,← pow_mul,Nat.mul_comm]
  calc
    _ = 16*C*r^4*((1/64:ℝ)^n*((2:ℝ)^4)^n) := by rw [pow_succ,←hpow]; ring
    _ = _ := by rw [←mul_pow]; norm_num

theorem lintegral_profile_le {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (δ : Y → ℝ≥0∞) (hδ : Measurable δ)
    (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ s : ℝ, 0 < s → μ.real {y | δ y < ENNReal.ofReal s} ≤ C*s^4)
    {r : ℝ} (hr : 0 < r) :
    ∫⁻ y, profile r (δ y) ∂μ ≤ ENNReal.ofReal (32*C*r^4) := by
  let f : ℕ → Y → ℝ≥0∞ := fun n =>
    {y | δ y < ENNReal.ofReal (2^(n+1)*r)}.indicator
      (fun _ => ENNReal.ofReal ((1/64:ℝ)^n))
  have hf : ∀ n, Measurable (f n) := fun n =>
    measurable_const.indicator (measurableSet_lt hδ measurable_const)
  have hi (n : ℕ) : ∫⁻ y, f n y ∂μ ≤ ENNReal.ofReal (16*C*r^4*(1/4:ℝ)^n) := by
    rw [lintegral_indicator_const (measurableSet_lt hδ measurable_const)]
    have hm : μ {y | δ y < ENNReal.ofReal (2^(n+1)*r)} ≤
        ENNReal.ofReal (C*(2^(n+1)*r)^4) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
      exact ENNReal.ofReal_le_ofReal (hgrowth _ (by positivity))
    calc
      _ ≤ ENNReal.ofReal ((1/64:ℝ)^n) * ENNReal.ofReal (C*(2^(n+1)*r)^4) :=
        by gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity), dyadic_term_identity]
  calc
    _ ≤ ∫⁻ y, ∑' n, f n y ∂μ := lintegral_mono fun y => profile_majorant hr (δ y)
    _ = ∑' n, ∫⁻ y, f n y ∂μ := lintegral_tsum fun n => (hf n).aemeasurable
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (16*C*r^4*(1/4:ℝ)^n) := ENNReal.tsum_le_tsum hi
    _ = ENNReal.ofReal (16*C*r^4) * (1-ENNReal.ofReal (1/4))⁻¹ := by
      simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 16*C*r^4), ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤1/4)]
      rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric]
    _ ≤ ENNReal.ofReal (32*C*r^4) := by
      have hratio : (1-ENNReal.ofReal (1/4))⁻¹ ≤ ENNReal.ofReal 2 := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num : (0:ℝ) ≤ 1/4)]
        rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 1-1/4)]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
      calc
        _ ≤ ENNReal.ofReal (16*C*r^4)*ENNReal.ofReal 2 := by gcongr
        _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

end TamingCompatibility.FourthShell

end
end

section
noncomputable section
open Bundle Set TopologicalSpace
lemma bundle_totalSpace_secondCountable {B F : Type*} [TopologicalSpace B] [TopologicalSpace F]
    [SecondCountableTopology B] [SecondCountableTopology F] (E : B → Type*)
    [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E] :
    SecondCountableTopology (TotalSpace F E) := by
  let e : B → Trivialization F (π F E) := fun b => trivializationAt F E b
  obtain ⟨s,hsc,hs⟩ := isOpen_iUnion_countable (fun b => (e b).baseSet) (fun b => (e b).open_baseSet)
  have hcover : (⋃ b : B, (e b).baseSet) = univ := by
    apply eq_univ_iff_forall.mpr
    intro b
    exact mem_iUnion.mpr ⟨b,mem_baseSet_trivializationAt F E b⟩
  rw [hcover] at hs
  let := hsc.to_subtype
  let U : s → Set (TotalSpace F E) := fun b => (e b.val).source
  have (b : s) : SecondCountableTopology (U b) :=
    (e b.val).toOpenPartialHomeomorph.secondCountableTopology_source
  apply secondCountableTopology_of_countable_cover (U := U) (fun b => (e b.val).open_source)
  apply eq_univ_iff_forall.mpr
  intro v
  have hv : v.proj ∈ ⋃ b ∈ s, (e b).baseSet := hs.symm ▸ mem_univ _
  obtain ⟨b,hb,hv⟩ := mem_iUnion₂.mp hv
  exact mem_iUnion.mpr ⟨⟨b,hb⟩,(e b).mem_source.mpr hv⟩
namespace TamingCompatibility
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [SecondCountableTopology X]
lemma unitSecondCountable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type)) :
    SecondCountableTopology (MetricUnit g) := by
  have : SecondCountableTopology (TangentBundle Model X) :=
    bundle_totalSpace_secondCountable (TangentSpace Model : X → Type)
  exact TopologicalSpace.Subtype.secondCountableTopology {p : TangentBundle Model X | g.inner p.proj p.2 p.2 = 1}
end TamingCompatibility

end
end

end OAI
