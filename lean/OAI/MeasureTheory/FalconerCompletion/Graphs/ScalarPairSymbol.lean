import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Graphs.NormIteratedFDerivSmoothStar
import OAI.MeasureTheory.FalconerCompletion.Graphs.SphereAxisIntegralNormBoundGeneral
import OAI.MeasureTheory.FalconerCompletion.Graphs.SpherePlaneWaveSub2

namespace OAI

/-! Graph energies and pair estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set MeasureTheory _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ComplexConjugate RealInnerProductSpace
variable {n : ℕ}

section General
variable {V : Type*} [MeasurableSpace V]
def scalarPairSymbolND (b : V → V → ℂ) (z : V×V) (w : V) : ℂ := b z.1 w*conj (b z.2 w)

lemma scalarPairSymbolND_measurable {b : V → V → ℂ}
    (hb : Measurable (Function.uncurry b)) : Measurable (Function.uncurry (scalarPairSymbolND b)) := by
  exact (hb.comp (measurable_fst.fst.prodMk measurable_snd)).mul
    (Complex.continuous_conj.measurable.comp (hb.comp (measurable_fst.snd.prodMk measurable_snd)))
end General

lemma physical_pairAxis_measurable (v : ℝ)
    (b : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (hb : Measurable (Function.uncurry b)) :
    Measurable (fun z : ℝ × (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) =>
      sphereAxisIntegralND (((2:ℝ)^v*dist z.2.1 z.2.2)*z.1) (euclideanPairDirectionND z.2) (b z.2)) := by
  apply StronglyMeasurable.measurable
  apply sphereAxisIntegralND_stronglyMeasurable
  · fun_prop
  · exact euclideanPairDirectionND_measurable.comp measurable_snd
  · exact hb.comp (show Measurable (fun z : (ℝ × (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))) × EuclideanSpace ℝ (Fin (n+1)) => (z.1.2,z.2)) by fun_prop)

theorem physical_kernel_joint_integrableND {Ψ : ℝ → ℝ} (hmΨ : Measurable Ψ) (hΨ : Integrable Ψ)
    (v : ℝ)
    (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    (η : Measure ((EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) ×
      (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))))) [IsFiniteMeasure η]
    {B C : ℝ} (hB : 0≤B) (hC : 0≤C)
    (hbd : ∀ z w, ‖w‖=1 → ‖b z w‖≤B) (hcd : ∀ z w, ‖w‖=1 → ‖c z w‖≤C) :
    Integrable (fun p : ℝ × ((EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) ×
      (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))) =>
      (Ψ p.1:ℂ)*sphereAxisIntegralND (((2:ℝ)^v*dist p.2.1.1 p.2.1.2)*p.1)
        (euclideanPairDirectionND p.2.1) (b p.2.1)*
      conj (sphereAxisIntegralND (((2:ℝ)^v*dist p.2.2.1 p.2.2.2)*p.1)
        (euclideanPairDirectionND p.2.2) (c p.2.2))) (volume.prod η) := by
  let S := (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))).real univ
  have hSb : 0≤B*S := mul_nonneg hB ENNReal.toReal_nonneg
  have hSc : 0≤C*S := mul_nonneg hC ENNReal.toReal_nonneg
  let V := EuclideanSpace ℝ (Fin (n+1))
  have hm₁ : Measurable (fun p : ℝ × ((V×V)×(V×V)) => (p.1,p.2.1)) :=
    measurable_fst.prodMk measurable_snd.fst
  have hm₂ : Measurable (fun p : ℝ × ((V×V)×(V×V)) => (p.1,p.2.2)) :=
    measurable_fst.prodMk measurable_snd.snd
  have hb' := (physical_pairAxis_measurable v b hb).comp hm₁
  have hc' := (physical_pairAxis_measurable v c hc).comp hm₂
  have hm := (((Complex.continuous_ofReal.measurable.comp hmΨ).comp measurable_fst).mul hb').mul
    (Complex.continuous_conj.measurable.comp hc')
  have hi : Integrable (fun p : ℝ × ((EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) ×
      (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))) =>
      ‖Ψ p.1‖*((B*S)*(C*S))) (volume.prod η) := hΨ.norm.mul_prod (integrable_const _)
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards with p
  change ‖(Ψ p.1:ℂ)*sphereAxisIntegralND (((2:ℝ)^v*dist p.2.1.1 p.2.1.2)*p.1)
      (euclideanPairDirectionND p.2.1) (b p.2.1)*
    conj (sphereAxisIntegralND (((2:ℝ)^v*dist p.2.2.1 p.2.2.2)*p.1)
      (euclideanPairDirectionND p.2.2) (c p.2.2))‖ ≤ ‖Ψ p.1‖*((B*S)*(C*S))
  simp only [norm_mul,Complex.norm_real,Complex.norm_conj]
  have h₁ := sphereAxisIntegralND_norm_bound_general (((2:ℝ)^v*dist p.2.1.1 p.2.1.2)*p.1)
    (euclideanPairDirectionND p.2.1) (hbd p.2.1)
  have h₂ := sphereAxisIntegralND_norm_bound_general (((2:ℝ)^v*dist p.2.2.1 p.2.2.2)*p.1)
    (euclideanPairDirectionND p.2.2) (hcd p.2.2)
  calc
    _ ≤ (‖Ψ p.1‖*(B*S))*(C*S) := mul_le_mul
      (mul_le_mul_of_nonneg_left h₁ (norm_nonneg (Ψ p.1))) h₂
      (norm_nonneg _) (mul_nonneg (norm_nonneg (Ψ p.1)) hSb)
    _ = _ := by ring

theorem physical_energy_identityND {Ψ : ℝ → ℝ} (hmΨ : Measurable Ψ) (hΨ : Integrable Ψ)
    (v : ℝ)
    (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (X Y : Set (EuclideanSpace ℝ (Fin (n+1)))) (M N : ℝ)
    (b c : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0≤B) (hC : 0≤C)
    (hbd : ∀ z w, ‖w‖=1 → ‖b z w‖≤B) (hcd : ∀ z w, ‖w‖=1 → ‖c z w‖≤C) :
    (((M*M)*(N*N))⁻¹:ℝ) • (∫ z, euclideanFarKernelND Ψ v (scalarPairSymbolND b) (scalarPairSymbolND c) z
      ∂((ρ.restrict X).prod (ρ.restrict X)).prod ((κ.restrict Y).prod (κ.restrict Y))) =
    ((∫ u : ℝ, Ψ u*physicalAngularMomentND ρ X M b ((2:ℝ)^v*u)*
      physicalAngularMomentND κ Y N c ((2:ℝ)^v*u)):ℝ) := by
  let V := EuclideanSpace ℝ (Fin (n+1))
  let b' := scalarPairSymbolND b
  let c' := scalarPairSymbolND c
  have hb' := scalarPairSymbolND_measurable hb
  have hc' := scalarPairSymbolND_measurable hc
  have hbb : ∀ z w, ‖w‖=1 → ‖b' z w‖≤B*B := by
    intro z w hw
    change ‖b z.1 w*conj (b z.2 w)‖≤B*B
    rw [norm_mul,Complex.norm_conj]
    exact mul_le_mul (hbd _ _ hw) (hbd _ _ hw) (norm_nonneg _) hB
  have hcc : ∀ z w, ‖w‖=1 → ‖c' z w‖≤C*C := by
    intro z w hw
    change ‖c z.1 w*conj (c z.2 w)‖≤C*C
    rw [norm_mul,Complex.norm_conj]
    exact mul_le_mul (hcd _ _ hw) (hcd _ _ hw) (norm_nonneg _) hC
  let F := fun (u : ℝ) (z : (V×V)×(V×V)) => (Ψ u:ℂ)*
    sphereAxisIntegralND (((2:ℝ)^v*dist z.1.1 z.1.2)*u) (euclideanPairDirectionND z.1) (b' z.1)*
    conj (sphereAxisIntegralND (((2:ℝ)^v*dist z.2.1 z.2.2)*u) (euclideanPairDirectionND z.2) (c' z.2))
  have hF : Integrable (Function.uncurry F)
      (volume.prod (((ρ.restrict X).prod (ρ.restrict X)).prod ((κ.restrict Y).prod (κ.restrict Y)))) :=
    physical_kernel_joint_integrableND hmΨ hΨ v b' c' hb' hc' _ (mul_nonneg hB hB) (mul_nonneg hC hC) hbb hcc
  have hswap := integral_integral_swap hF
  change (((M*M)*(N*N))⁻¹:ℝ) • (∫ z, (∫ u, F u z)
    ∂((ρ.restrict X).prod (ρ.restrict X)).prod ((κ.restrict Y).prod (κ.restrict Y))) = _
  rw [← hswap,← integral_smul,← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with u
  have hmul : (∫ z : (V×V)×(V×V), F u z
      ∂((ρ.restrict X).prod (ρ.restrict X)).prod ((κ.restrict Y).prod (κ.restrict Y))) =
      (Ψ u:ℂ)*(∫ x, sphereAxisIntegralND (((2:ℝ)^v*u)*dist x.1 x.2) (euclideanPairDirectionND x) (b' x)
        ∂(ρ.restrict X).prod (ρ.restrict X))*
        conj (∫ y, sphereAxisIntegralND (((2:ℝ)^v*u)*dist y.1 y.2) (euclideanPairDirectionND y) (c' y)
          ∂(κ.restrict Y).prod (κ.restrict Y)) := by
    dsimp [F]
    simp_rw [mul_assoc (Ψ u:ℂ),mul_assoc ((2:ℝ)^v),mul_comm (dist _ _) u,← mul_assoc ((2:ℝ)^v)]
    rw [integral_const_mul,integral_prod_mul
      (μ := (ρ.restrict X).prod (ρ.restrict X))
      (ν := (κ.restrict Y).prod (κ.restrict Y))
      (fun x : V×V => sphereAxisIntegralND (((2:ℝ)^v*u)*dist x.1 x.2) (euclideanPairDirectionND x) (b' x))
      (fun y : V×V => conj (sphereAxisIntegralND (((2:ℝ)^v*u)*dist y.1 y.2) (euclideanPairDirectionND y) (c' y))),integral_conj]
  rw [hmul]
  have hbM := physical_pair_momentND ρ X M ((2:ℝ)^v*u) b hb hB hbd
  have hcM := physical_pair_momentND κ Y N ((2:ℝ)^v*u) c hc hC hcd
  have halg (z w : ℂ) : (((M*M)*(N*N))⁻¹:ℝ) • ((Ψ u:ℂ)*z*conj w) =
      (Ψ u:ℂ)*((M*M)⁻¹ • z)*conj ((N*N)⁻¹ • w) := by
    simp only [Complex.real_smul,map_mul,Complex.conj_ofReal,mul_inv_rev,Complex.ofReal_mul]
    ring
  rw [halg]
  change (Ψ u:ℂ)*((M*M)⁻¹ • _)*conj ((N*N)⁻¹ • _) = _
  change (M*M)⁻¹ • (∫ x, sphereAxisIntegralND (((2:ℝ)^v*u)*dist x.1 x.2)
    (euclideanPairDirectionND x) (b' x) ∂(ρ.restrict X).prod (ρ.restrict X)) =
    (physicalAngularMomentND ρ X M b ((2:ℝ)^v*u):ℂ) at hbM
  change (N*N)⁻¹ • (∫ y, sphereAxisIntegralND (((2:ℝ)^v*u)*dist y.1 y.2)
    (euclideanPairDirectionND y) (c' y) ∂(κ.restrict Y).prod (κ.restrict Y)) =
    (physicalAngularMomentND κ Y N c ((2:ℝ)^v*u):ℂ) at hcM
  rw [hbM,hcM,Complex.conj_ofReal]
  push_cast
  rfl

end CurrentFalconer
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set MeasureTheory _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ComplexConjugate
variable {n : ℕ}

noncomputable def physicalCrossMomentND
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1))))
    (X₁ X₂ : Set (EuclideanSpace ℝ (Fin (n+1)))) (M : ℝ)
    (b : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) → ℂ) (r : ℝ) : ℂ :=
  ∫ w, sourceAngularTransformND ρ X₁ M b r w*conj (sourceAngularTransformND ρ X₂ M b r w)
    ∂canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))

lemma physical_pair_crossND
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ]
    (X₁ X₂ : Set (EuclideanSpace ℝ (Fin (n+1)))) (M r : ℝ)
    (b : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (hb : Measurable (Function.uncurry b)) {B : ℝ} (hB : 0≤B)
    (hbd : ∀ x w, ‖w‖=1 → ‖b x w‖≤B) :
    ((M*M)⁻¹:ℝ) • (∫ x, sphereAxisIntegralND (r*dist x.1 x.2) (euclideanPairDirectionND x)
      (scalarPairSymbolND b x) ∂(ρ.restrict X₁).prod (ρ.restrict X₂)) =
      physicalCrossMomentND ρ X₁ X₂ M b r := by
  have ha : ∀ᵐ w ∂canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1))), ∀ x, ‖b x w‖≤B := by
    filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw
    exact fun x => hbd x w hw
  have hh := angular_pair_factorizationND_ae (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1))))
    ρ ρ X₁ X₂ M M r (ψ:=fun _ => 1) measurable_const hb hb (by norm_num : (0:ℝ)≤1) hB hB
    (Filter.Eventually.of_forall (fun _ => by norm_num)) ha ha
  simp only [one_mul,physicalCrossMomentND] at hh ⊢
  simp_rw [physical_sphereAxisND]
  simpa only [scalarPairSymbolND,mul_assoc] using hh

lemma physicalCrossMomentND_swap
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1))))
    (X₁ X₂ : Set (EuclideanSpace ℝ (Fin (n+1)))) (M r : ℝ)
    (b : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) → ℂ) :
    physicalCrossMomentND ρ X₂ X₁ M b r=conj (physicalCrossMomentND ρ X₁ X₂ M b r) := by
  simp only [physicalCrossMomentND,← integral_conj,map_mul,Complex.conj_conj,mul_comm]

theorem physical_cross_energy_identityND {Ψ : ℝ → ℝ} (hmΨ : Measurable Ψ) (hΨ : Integrable Ψ)
    (v : ℝ)
    (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (X₁ X₂ Y₁ Y₂ : Set (EuclideanSpace ℝ (Fin (n+1)))) (M N : ℝ)
    (b c : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0≤B) (hC : 0≤C)
    (hbd : ∀ x w, ‖w‖=1 → ‖b x w‖≤B) (hcd : ∀ x w, ‖w‖=1 → ‖c x w‖≤C) :
    (((M*M)*(N*N))⁻¹:ℝ) • (∫ z, euclideanFarKernelND Ψ v (scalarPairSymbolND b) (scalarPairSymbolND c) z
      ∂((ρ.restrict X₁).prod (ρ.restrict X₂)).prod ((κ.restrict Y₁).prod (κ.restrict Y₂))) =
    ∫ u : ℝ, (Ψ u:ℂ)*physicalCrossMomentND ρ X₁ X₂ M b ((2:ℝ)^v*u)*
      conj (physicalCrossMomentND κ Y₁ Y₂ N c ((2:ℝ)^v*u)) := by
  let V := EuclideanSpace ℝ (Fin (n+1))
  let b' := scalarPairSymbolND b
  let c' := scalarPairSymbolND c
  have hb' := scalarPairSymbolND_measurable hb
  have hc' := scalarPairSymbolND_measurable hc
  have hbb : ∀ z w, ‖w‖=1 → ‖b' z w‖≤B*B := by
    intro z w hw
    change ‖b z.1 w*conj (b z.2 w)‖≤B*B
    rw [norm_mul,Complex.norm_conj]
    exact mul_le_mul (hbd _ _ hw) (hbd _ _ hw) (norm_nonneg _) hB
  have hcc : ∀ z w, ‖w‖=1 → ‖c' z w‖≤C*C := by
    intro z w hw
    change ‖c z.1 w*conj (c z.2 w)‖≤C*C
    rw [norm_mul,Complex.norm_conj]
    exact mul_le_mul (hcd _ _ hw) (hcd _ _ hw) (norm_nonneg _) hC
  let F := fun (u : ℝ) (z : (V×V)×(V×V)) => (Ψ u:ℂ)*
    sphereAxisIntegralND (((2:ℝ)^v*dist z.1.1 z.1.2)*u) (euclideanPairDirectionND z.1) (b' z.1)*
    conj (sphereAxisIntegralND (((2:ℝ)^v*dist z.2.1 z.2.2)*u) (euclideanPairDirectionND z.2) (c' z.2))
  have hF : Integrable (Function.uncurry F)
      (volume.prod (((ρ.restrict X₁).prod (ρ.restrict X₂)).prod ((κ.restrict Y₁).prod (κ.restrict Y₂)))) :=
    physical_kernel_joint_integrableND hmΨ hΨ v b' c' hb' hc' _ (mul_nonneg hB hB) (mul_nonneg hC hC) hbb hcc
  have hswap := integral_integral_swap hF
  change (((M*M)*(N*N))⁻¹:ℝ) • (∫ z, (∫ u, F u z)
    ∂((ρ.restrict X₁).prod (ρ.restrict X₂)).prod ((κ.restrict Y₁).prod (κ.restrict Y₂))) = _
  rw [← hswap,← integral_smul]
  apply integral_congr_ae
  filter_upwards with u
  have hmul : (∫ z : (V×V)×(V×V), F u z
      ∂((ρ.restrict X₁).prod (ρ.restrict X₂)).prod ((κ.restrict Y₁).prod (κ.restrict Y₂))) =
      (Ψ u:ℂ)*(∫ x, sphereAxisIntegralND (((2:ℝ)^v*u)*dist x.1 x.2) (euclideanPairDirectionND x) (b' x)
        ∂(ρ.restrict X₁).prod (ρ.restrict X₂))*
        conj (∫ y, sphereAxisIntegralND (((2:ℝ)^v*u)*dist y.1 y.2) (euclideanPairDirectionND y) (c' y)
          ∂(κ.restrict Y₁).prod (κ.restrict Y₂)) := by
    dsimp [F]
    simp_rw [mul_assoc (Ψ u:ℂ),mul_assoc ((2:ℝ)^v),mul_comm (dist _ _) u,← mul_assoc ((2:ℝ)^v)]
    rw [integral_const_mul,integral_prod_mul
      (μ := (ρ.restrict X₁).prod (ρ.restrict X₂))
      (ν := (κ.restrict Y₁).prod (κ.restrict Y₂))
      (fun x : V×V => sphereAxisIntegralND (((2:ℝ)^v*u)*dist x.1 x.2) (euclideanPairDirectionND x) (b' x))
      (fun y : V×V => conj (sphereAxisIntegralND (((2:ℝ)^v*u)*dist y.1 y.2) (euclideanPairDirectionND y) (c' y))),integral_conj]
  rw [hmul]
  have hbM := physical_pair_crossND ρ X₁ X₂ M ((2:ℝ)^v*u) b hb hB hbd
  have hcM := physical_pair_crossND κ Y₁ Y₂ N ((2:ℝ)^v*u) c hc hC hcd
  have halg (z w : ℂ) : (((M*M)*(N*N))⁻¹:ℝ) • ((Ψ u:ℂ)*z*conj w) =
      (Ψ u:ℂ)*((M*M)⁻¹ • z)*conj ((N*N)⁻¹ • w) := by
    simp only [Complex.real_smul,map_mul,Complex.conj_ofReal,mul_inv_rev,Complex.ofReal_mul]
    ring
  rw [halg,hbM,hcM]

end CurrentFalconer
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory Filter _root_.OAI.GraphLiteralSupport.Attempt4FullFar PlanarFalconer
open scoped ContDiff Topology ComplexConjugate
variable {n : ℕ}

lemma actualPairSourceSymbol_eq_scalarPair
    (A : ℕ → ℝ) (N q a t : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) :
    (fun z w => (actualPairSourceSymbol A N q a t L ρ m sig C J i f Q z).1 w) =
    scalarPairSymbolND (fun x w => (actualSourceSymbol A N q a t L ρ m sig C J i f Q x).1 w) := rfl

theorem actual_transform_uniform_package
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (B total : ℕ) (hW : ∀ L∈W, L.length≤B)
    {sig : ℝ} (hsig : 0<sig) (Cq : ℝ) (hCq : 0≤Cq) :
    ∃ E : ℝ, 0≤E ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ],
      ∀ (A : ℕ → ℝ) (q a t : ℕ), 0<q →
      ∀ (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (m : ℝ → ℝ) (C : ℝ) (J i : ℕ)
        (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))),
      Measurable f → (∀ x, ‖f x‖≤1) →
      (∀ b∈policyDescriptorList A N q a t, L b∈W) →
      (∑ b∈policyDescriptorList A N q a t, (L b).length≤total) →
      (∀ w, ‖w‖=1 → ‖Q.1 w‖≤Cq) →
      let b := fun x w => (actualSourceSymbol A N q a t L ρ m sig C J i f Q x).1 w
      Measurable (Function.uncurry b) ∧ (∀ x w, ‖w‖=1 → ‖b x w‖≤E) ∧
      ∀ (X : Set (EuclideanSpace ℝ (Fin (n+1)))) (M : ℝ),
      Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin (n+1)) => sourceAngularTransformND ρ X M b p.1 p.2) ∧
      ∀ r, ∀ᵐ w ∂canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1))),
        ‖sourceAngularTransformND ρ X M b r w‖≤|M⁻¹| * (ρ X).toReal*E := by
  obtain ⟨E,hE,he⟩ := uniform_actualSourceSymbol_derivatives W 0 B total hW sig hsig Cq hCq
  refine ⟨E,hE,?_⟩
  filter_upwards [he] with N he
  intro ρ hρ A q a t hq L m C J i f Q hf hfb hL htotal hQ
  let b := fun x w => (actualSourceSymbol A N q a t L ρ m sig C J i f Q x).1 w
  have hQ' : ∀ j≤0, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j Q.1 w‖≤Cq := by
    intro j hj w hw
    have hj0 : j=0 := Nat.eq_zero_of_le_zero hj
    subst j
    simpa only [norm_iteratedFDeriv_zero] using hQ w hw
  have hb : ∀ x w, ‖w‖=1 → ‖b x w‖≤E := by
    intro x w hw
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using
      he A q a t hq L ρ m C J i f Q hL htotal hfb hQ' x 0 le_rfl w hw
  have hm : Measurable (Function.uncurry b) := actualSourceSymbol_measurable A N q a t L ρ m sig C J i f hf Q
  refine ⟨hm,hb,?_⟩
  intro X M
  refine ⟨sourceAngularTransformND_measurable ρ X M hm,?_⟩
  intro r
  filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw
  exact sourceAngularTransformND_norm_le ρ X M b r w (fun x => hb x w hw)

theorem actual_energy_identityND
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (B total : ℕ) (hW : ∀ L∈W, L.length≤B)
    {sig : ℝ} (hsig : 0<sig) (Cq : ℝ) (hCq : 0≤Cq) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ],
      ∀ (A : ℕ → ℝ) (q a t : ℕ), 0<q →
      ∀ (L₁ L₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (m : ℝ → ℝ) (C : ℝ) (J i : ℕ)
        (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (Q P : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))),
      Measurable f → Measurable g → (∀ x, ‖f x‖≤1) → (∀ x, ‖g x‖≤1) →
      (∀ b∈policyDescriptorList A N q a t, L₁ b∈W) →
      (∀ b∈policyDescriptorList A N q a t, L₂ b∈W) →
      (∑ b∈policyDescriptorList A N q a t, (L₁ b).length≤total) →
      (∑ b∈policyDescriptorList A N q a t, (L₂ b).length≤total) →
      (∀ w, ‖w‖=1 → ‖Q.1 w‖≤Cq) → (∀ w, ‖w‖=1 → ‖P.1 w‖≤Cq) →
      ∀ (X Y : Set (EuclideanSpace ℝ (Fin (n+1)))) (M Nt v : ℝ) (Ψ : ℝ → ℝ),
      Measurable Ψ → Integrable Ψ →
      let b := fun x w => (actualSourceSymbol A N q a t L₁ ρ m sig C J i f Q x).1 w
      let c := fun x w => (actualSourceSymbol A N q a t L₂ κ m sig C J i g P x).1 w
      (((M*M)*(Nt*Nt))⁻¹:ℝ) •
        (∫ z, euclideanFarKernelND Ψ v
          (fun z => (actualPairSourceSymbol A N q a t L₁ ρ m sig C J i f Q z).1)
          (fun z => (actualPairSourceSymbol A N q a t L₂ κ m sig C J i g P z).1) z
          ∂((ρ.restrict X).prod (ρ.restrict X)).prod ((κ.restrict Y).prod (κ.restrict Y))) =
      ((∫ u : ℝ, Ψ u*physicalAngularMomentND ρ X M b ((2:ℝ)^v*u)*
        physicalAngularMomentND κ Y Nt c ((2:ℝ)^v*u)):ℝ) := by
  obtain ⟨E,hE,he⟩ := actual_transform_uniform_package W B total hW hsig Cq hCq
  filter_upwards [he] with N he
  intro ρ κ hρ hκ A q a t hq L₁ L₂ m C J i f g Q P hf hg hfb hgb hL₁ hL₂ htotal₁ htotal₂ hQ hP X Y M Nt v Ψ hmΨ hΨ
  obtain ⟨hbm,hbb,_⟩ := he ρ A q a t hq L₁ m C J i f Q hf hfb hL₁ htotal₁ hQ
  obtain ⟨hcm,hcc,_⟩ := he κ A q a t hq L₂ m C J i g P hg hgb hL₂ htotal₂ hP
  dsimp only
  rw [actualPairSourceSymbol_eq_scalarPair A N q a t L₁ ρ m sig C J i f Q,
    actualPairSourceSymbol_eq_scalarPair A N q a t L₂ κ m sig C J i g P]
  exact physical_energy_identityND hmΨ hΨ v ρ κ X Y M Nt
    (fun x w => (actualSourceSymbol A N q a t L₁ ρ m sig C J i f Q x).1 w)
    (fun x w => (actualSourceSymbol A N q a t L₂ κ m sig C J i g P x).1 w)
    hbm hcm hE hE hbb hcc

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
