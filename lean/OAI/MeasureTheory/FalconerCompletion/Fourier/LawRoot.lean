import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Measures.AssemblyClassLaw
import OAI.MeasureTheory.FalconerCompletion.Recursion.AssemblyListsCard

namespace OAI

/-! Fourier kernels and oscillatory estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Classical Topology ENNReal NNReal
variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin (n+1))

namespace AssemblyClassFamily
variable {ι : Type*} {μ : Measure (EuclideanSpace ℝ (Fin (n+1)))} {N B : ℕ} {chi sig : ℝ}
    (F : AssemblyClassFamily ι μ N B chi sig)
lemma law_root [IsFiniteMeasure μ] (i : ι) : assemblyClassLaw μ (F.domain i) (treeCell [])=1 := by
  rw [assemblyClassLaw,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply (measurableSet_treeCell _),
    inter_eq_right.mpr (F.root i)]
  exact ENNReal.inv_mul_cancel (F.positive i) (measure_ne_top _ _)
lemma coefficient_law [IsFiniteMeasure μ] (i : ι) :
    F.coefficient i • assemblyClassLaw μ (F.domain i) = μ.restrict (F.domain i) := by
  rw [coefficient,ENNReal.smul_def,ENNReal.coe_toNNReal (measure_ne_top _ _),assemblyClassLaw,
    smul_smul,ENNReal.mul_inv_cancel (F.positive i) (measure_ne_top _ _),one_smul]
lemma coefficient_sum [Fintype ι] [IsProbabilityMeasure μ] :
    (∑ i, (F.coefficient i:ℝ)) ≤ 1 := by
  have hs : (∑ i, μ (F.domain i)) ≤ 1 := by
    have he := measure_iUnion (μ:=μ) (fun i j hij => F.disjoint hij) F.measurable
    rw [tsum_fintype] at he
    rw [← he]
    exact prob_le_one
  have ht : (∑ i, μ (F.domain i)).toReal ≤ (1:ENNReal).toReal :=
    ENNReal.toReal_mono ENNReal.one_ne_top hs
  simpa only [ENNReal.toReal_sum (fun i _ => measure_ne_top μ _),ENNReal.toReal_one,
    coefficient,ENNReal.coe_toNNReal_eq_toReal] using ht
end AssemblyClassFamily

lemma assemblyPairMask_measurable (e₁ e₂ : RecursiveEnvironmentND n) (c : ℕ) :
    Measurable (assemblyPairMask e₁ e₂ c) := by
  have hL : Measurable (fun z : V×V => ∏ b ∈ assemblyDescriptorList e₁.profile e₁.N e₁.q c,
      actualEndpointMask e₁.ρ e₁.mass e₁.N e₁.sig e₁.C e₁.J 0 b z.1
        ((dist z.1 z.2)⁻¹ • (z.1-z.2))) :=
    Finset.measurable_prod _ (fun b _ => assembly_endpoint_radial_left e₁ b)
  have hR : Measurable (fun z : V×V => ∏ b ∈ assemblyDescriptorList e₂.profile e₂.N e₂.q c,
      actualEndpointMask e₂.ρ e₂.mass e₂.N e₂.sig e₂.C e₂.J 0 b z.2
        ((dist z.1 z.2)⁻¹ • (z.1-z.2))) :=
    Finset.measurable_prod _ (fun b _ => assembly_endpoint_radial_right e₂ b)
  change Measurable (fun z : V×V => _ * _)
  convert hL.mul hR using 1
  funext z
  simp only [Pi.mul_apply,radialVector,dist_eq_norm]
lemma assemblyPairMask_bounds (e₁ e₂ : RecursiveEnvironmentND n) (c : ℕ) (z : V×V) :
    0≤assemblyPairMask e₁ e₂ c z ∧ assemblyPairMask e₁ e₂ c z≤1 := by
  have hr : ‖radialVector z.1 z.2‖≤1 := by
    by_cases h : z.1=z.2
    · simp [radialVector,h]
    · exact (norm_radialVector h).le
  have hp (e : RecursiveEnvironmentND n) (x : V) :
      0 ≤ ∏ b∈assemblyDescriptorList e.profile e.N e.q c,
        actualEndpointMask e.ρ e.mass e.N e.sig e.C e.J 0 b x (radialVector z.1 z.2) ∧
      (∏ b∈assemblyDescriptorList e.profile e.N e.q c,
        actualEndpointMask e.ρ e.mass e.N e.sig e.C e.J 0 b x (radialVector z.1 z.2))≤1 :=
    ⟨Finset.prod_nonneg (fun b _ => (actualEndpointMask_bounds _ _ _ _ _ _ _ _ _ hr).1),
     Finset.prod_le_one₀ (fun b _ => (actualEndpointMask_bounds _ _ _ _ _ _ _ _ _ hr).1)
       (fun b _ => (actualEndpointMask_bounds _ _ _ _ _ _ _ _ _ hr).2)⟩
  exact ⟨mul_nonneg (hp e₁ z.1).1 (hp e₂ z.2).1,
    (mul_le_of_le_one_left (hp e₂ z.2).1 (hp e₁ z.1).2).trans (hp e₂ z.2).2⟩

noncomputable def assemblySpatialWeight (e₁ e₂ : RecursiveEnvironmentND n) (c : ℕ) (z : V×V) : ℝ :=
  (dist z.1 z.2)^(-(n:ℝ)/2)*assemblyPairMask e₁ e₂ c z
lemma assemblySpatialWeight_measurable (e₁ e₂ : RecursiveEnvironmentND n) (c : ℕ) :
    Measurable (assemblySpatialWeight e₁ e₂ c) :=
  ((continuous_fst.dist continuous_snd).measurable.pow_const _).mul (assemblyPairMask_measurable e₁ e₂ c)
lemma assemblySpatialWeight_nonneg (e₁ e₂ : RecursiveEnvironmentND n) (c : ℕ) (z : V×V) :
    0≤assemblySpatialWeight e₁ e₂ c z :=
  mul_nonneg (Real.rpow_nonneg dist_nonneg _) (assemblyPairMask_bounds e₁ e₂ c z).1

noncomputable def assemblyComponentMeasure (e₁ e₂ : RecursiveEnvironmentND n) (c : ℕ)
    (X Y : Set V) : Measure ℝ :=
  (((e₁.ρ.restrict X).prod (e₂.ρ.restrict Y)).withDensity
    (fun z => ENNReal.ofReal (assemblySpatialWeight e₁ e₂ c z))).map (fun z => dist z.1 z.2)

lemma assemblyComponentMeasure_fourier (e₁ e₂ : RecursiveEnvironmentND n) (c : ℕ)
    (X Y : Set V) (h₁ : e₁.mass 0=0) (h₂ : e₂.mass 0=0) (r : ℝ) :
    charFun (assemblyComponentMeasure e₁ e₂ c X Y) r =
      assemblyDistanceTransform e₁ e₂ c X Y (fun _ => 1) (fun _ => 1) r := by
  rw [charFun_apply_real,assemblyComponentMeasure,integral_map (by fun_prop) (by fun_prop)]
  rw [integral_withDensity_eq_integral_toReal_smul
    (assemblySpatialWeight_measurable e₁ e₂ c).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [assemblyDistanceTransform,Attempt4PrefixShell.weightedMaskTransformND,h₁,h₂,
    neg_zero,Real.rpow_zero,mul_one,inv_one,one_smul,map_one,one_mul]
  apply integral_congr_ae
  filter_upwards with z
  rw [ENNReal.toReal_ofReal (assemblySpatialWeight_nonneg e₁ e₂ c z)]
  simp only [Attempt4PrefixShell.outgoingWeightedKernelND,assembly_pairMask_eq,
    assemblySpatialWeight,assemblyPairMask,mul_one,radialVector,dist_eq_norm,
    Complex.real_smul,Complex.ofReal_mul,mul_comm Complex.I]
  ring

lemma assemblyComponentMeasure_finite (e₁ e₂ : RecursiveEnvironmentND n) (c : ℕ)
    [IsFiniteMeasure e₁.ρ] [IsFiniteMeasure e₂.ρ] (X Y : Set V)
    (hX : MeasurableSet X) (hY : MeasurableSet Y) {δ : ℝ} (hδ : 0<δ)
    (hsep : ∀ x∈X,∀ y∈Y,δ≤dist x y) :
    IsFiniteMeasure (assemblyComponentMeasure e₁ e₂ c X Y) := by
  let m := (e₁.ρ.restrict X).prod (e₂.ρ.restrict Y)
  have hm : ∀ᵐ z ∂m, z.1∈X ∧ z.2∈Y :=
    (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hX)).and
      (Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hY))
  have hle : m.withDensity (fun z => ENNReal.ofReal (assemblySpatialWeight e₁ e₂ c z)) ≤
      ENNReal.ofReal (δ^(-(n:ℝ)/2)) • m := by
    rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [hm] with z hz
    apply ENNReal.ofReal_le_ofReal
    have hp := assemblyPairMask_bounds e₁ e₂ c z
    have hr := Real.rpow_le_rpow_of_nonpos hδ (hsep _ hz.1 _ hz.2)
      (show -(n:ℝ)/2≤0 from div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (by norm_num))
    exact (mul_le_of_le_one_right (Real.rpow_nonneg dist_nonneg _) hp.2).trans hr
  have : IsFiniteMeasure (m.withDensity (fun z => ENNReal.ofReal (assemblySpatialWeight e₁ e₂ c z))) :=
    ⟨(Measure.le_iff.mp hle univ MeasurableSet.univ).trans_lt (by
      rw [Measure.smul_apply,smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))⟩
  exact Measure.isFiniteMeasure_map _ _
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
