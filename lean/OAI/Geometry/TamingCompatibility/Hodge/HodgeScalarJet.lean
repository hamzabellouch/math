import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeH1

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeScalar
open MeasureTheory LineDeriv EuclideanEnergy ManifoldLocalization
open scoped SchwartzMap LineDeriv ContDiff
abbrev F := EuclideanSpace ℂ (Fin 6)
def inject (j : Fin 6) : ℝ →L[ℝ] F :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 6 => ℂ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℝ (fun _ : Fin 6 => ℂ) j ∘L Complex.ofRealCLM
lemma inject_apply (j i : Fin 6) (s : ℝ) : inject j s i = if i=j then (s : ℂ) else 0 := by
  simp [inject]
def make (f : Fin 6 → 𝓢(Space,ℝ)) : 𝓢(Space,F) := ∑ j, SchwartzMap.postcompCLM (inject j) (f j)
lemma make_apply (f : Fin 6 → 𝓢(Space,ℝ)) (x : Space) (i : Fin 6) : make f x i = (f i x : ℂ) := by
  simp [make,inject_apply]
lemma make_norm_sq (f : Fin 6 → 𝓢(Space,ℝ)) (x : Space) :
    ‖make f x‖^2 = ‖HodgeMatrixEnergy.value f x‖^2 := by
  simp [PiLp.norm_sq_eq_of_L2,make_apply,HodgeMatrixEnergy.value,Complex.norm_real]
lemma make_derivative (f : Fin 6 → 𝓢(Space,ℝ)) (v : Space) :
    ∂_{v} (make f) = make (fun j => ∂_{v} (f j)) := by
  simp only [make,lineDerivOp_sum,ScalarPair.postcomp_derivative]
abbrev Jet := PiLp 2 (fun _ : DerivativeIndex => Lp F 2 (volume : Measure Space))
def jetComponent (j : DerivativeIndex) : 𝓢(Space,F) →L[ℝ] 𝓢(Space,F) :=
  match j with
  | none => ContinuousLinearMap.id ℝ _
  | some i => lineDerivOpCLM ℝ 𝓢(Space,F) (stdOrthonormalBasis ℝ Space i)
def jet : 𝓢(Space,F) →L[ℝ] Jet :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : DerivativeIndex => Lp F 2 (volume : Measure Space))).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun j => SchwartzMap.toLpCLM ℝ F 2 (volume : Measure Space) ∘L jetComponent j)
lemma make_jet_bound (f : Fin 6 → 𝓢(Space,ℝ)) :
    ‖jet (make f)‖^2 ≤ 20*((∫ x, HodgeMatrixEnergy.gradient f x)+(∫ x, ‖HodgeMatrixEnergy.value f x‖^2)) := by
  let G := ∫ x, HodgeMatrixEnergy.gradient f x
  let Z := ∫ x, ‖HodgeMatrixEnergy.value f x‖^2
  have hG : 0 ≤ G := integral_nonneg (fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hZ : 0 ≤ Z := integral_nonneg (fun x => sq_nonneg _)
  have hd : ∑ i : Fin 4, ∫ x, ‖(∂_{e i} (make f)) x‖^2 = G := by
    simp only [make_derivative,make_norm_sq]
    change (∑ i : Fin 4, ∫ x, ‖HodgeMatrixEnergy.derivative f i x‖^2) = _
    symm
    exact integral_finsetSum _ (fun i _ => HodgeMatrixEnergy.value_integrable (fun j => coordinateDeriv i (f j)))
  have hj (j : DerivativeIndex) : ‖jet (make f) j‖^2 ≤ 4*(G+Z) := by
    change ‖(jetComponent j (make f)).toLp 2 (volume : Measure Space)‖^2 ≤ _
    rw [GeometricChart.schwartz_l2_norm_sq]
    cases j with
    | none =>
      change (∫ x, ‖make f x‖^2) ≤ _
      simp_rw [make_norm_sq]
      change Z ≤ 4*(G+Z)
      linarith
    | some i =>
      have hb := direction_integral_bound (make f) (stdOrthonormalBasis ℝ Space i)
        ((stdOrthonormalBasis ℝ Space).orthonormal.norm_eq_one i).le
      rw [hd] at hb
      exact hb.trans (by linarith)
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ ≤ ∑ j : DerivativeIndex, 4*(G+Z) := Finset.sum_le_sum (fun j _ => hj j)
    _ = _ := by simp [DerivativeIndex,Space,G,Z]; ring

def jetDistribution (j : DerivativeIndex) : Jet →L[ℝ] 𝓢'(Space,F) :=
  (Lp.toTemperedDistributionCLM F (volume : Measure Space) 2).restrictScalars ℝ ∘L PiLp.proj 2 _ j
lemma jetDistribution_jet (u : 𝓢(Space,F)) (j : DerivativeIndex) :
    jetDistribution j (jet u) = SchwartzMap.toTemperedDistributionCLM Space F volume (jetComponent j u) :=
  Lp.toTemperedDistribution_toLp_eq _
lemma jet_derivative (u : 𝓢(Space,F)) (i : Fin (Module.finrank ℝ Space)) :
    lineDerivOpCLM ℝ 𝓢'(Space,F) (stdOrthonormalBasis ℝ Space i) (jetDistribution none (jet u)) =
      jetDistribution (some i) (jet u) := by
  rw [jetDistribution_jet,jetDistribution_jet]
  exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq _ _
end TamingCompatibility.HodgeScalar

namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldLocalization Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
omit [CompactSpace X] in
lemma scalar_add (p : A.centers) (a b : TwoForm X) (j : Fin 6) :
    scalar A J α ht D p (a+b) j = scalar A J α ht D p a j + scalar A J α ht D p b j := by
  ext x
  unfold scalar
  by_cases hx : x ∈ (D p).domain
  · simp only [indicator_of_mem hx,Pi.add_apply,localizedFunction_add,ContinuousAlternatingMap.add_apply]
  · simp only [indicator_of_notMem hx,Pi.add_apply,add_zero]
omit [CompactSpace X] in
lemma scalar_smul (p : A.centers) (c : ℝ) (a : TwoForm X) (j : Fin 6) :
    scalar A J α ht D p (c • a) j = c • scalar A J α ht D p a j := by
  ext x
  unfold scalar
  by_cases hx : x ∈ (D p).domain
  · simp only [indicator_of_mem hx,Pi.smul_apply,localizedFunction_smul,ContinuousAlternatingMap.smul_apply]
  · simp only [indicator_of_notMem hx,Pi.smul_apply,smul_zero]
def scalarLinear (p : A.centers) (j : Fin 6) : smoothForms X 2 →ₗ[ℝ] 𝓢(Space,ℝ) where
  toFun a := scalarSchwartz A J α ht D hD p a.val a.property j
  map_add' a b := by
    ext x
    exact congrFun (scalar_add A J α ht D p a.val b.val j) x
  map_smul' c a := by
    ext x
    exact congrFun (scalar_smul A J α ht D p c a.val j) x

def scalarVectorLinear (p : A.centers) : smoothForms X 2 →ₗ[ℝ] 𝓢(Space,HodgeScalar.F) :=
  ∑ j : Fin 6, (SchwartzMap.postcompCLM (HodgeScalar.inject j)).toLinearMap ∘ₗ scalarLinear A J α ht D hD p j
lemma scalarVectorLinear_eq_make (p : A.centers) (a : smoothForms X 2) :
    scalarVectorLinear A J α ht D hD p a =
      HodgeScalar.make (scalarSchwartz A J α ht D hD p a.val a.property) := by
  simp only [scalarVectorLinear,LinearMap.sum_apply,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,
    HodgeScalar.make,scalarLinear,LinearMap.coe_mk,AddHom.coe_mk]
end TamingCompatibility.HodgeChart

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart MeasureTheory
open EuclideanSobolevOperators TemperedDistribution
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

def hodgeScalarToJet (p : A.centers) : PreL2 A J α hs ht true →ₗ[ℝ] HodgeScalar.Jet :=
  HodgeScalar.jet.toLinearMap ∘ₗ scalarVectorLinear A J α ht (fun q => (D q).toData) hD p

lemma hodgeScalarToJet_bound (p : A.centers) : ∃ C : ℝ, ∀ a : PreL2 A J α hs ht true,
    ‖hodgeScalarToJet A J α hs ht D hD p a‖ ≤ C * ‖hodgeSmooth A J α hs ht a‖ := by
  obtain ⟨C,hC,hb⟩ := scalar_garding A J α hs ht D hD p
  refine ⟨Real.sqrt (20*C),fun a => ?_⟩
  have h := HodgeScalar.make_jet_bound (scalarSchwartz A J α ht (fun q => (D q).toData) hD p a.val a.property)
  have hga := hb a.val a.property
  rw [← hodgeGraph_norm_sq A J α hs ht a] at hga
  have hn : ‖hodgeScalarToJet A J α hs ht D hD p a‖^2 ≤ 20*C*‖hodgeSmooth A J α hs ht a‖^2 := by
    change ‖HodgeScalar.jet (HodgeScalar.make (scalarSchwartz A J α ht (fun q => (D q).toData) hD p a.val a.property))‖^2 ≤ 20*C*‖hodgeGraph A J α hs ht a‖^2
    exact h.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hga (show (0:ℝ) ≤ 20 by norm_num))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 20*C)]
  exact hn

def hodgeEnergyToScalarJet (p : A.centers) : hodgeEnergy A J α hs ht →L[ℝ] HodgeScalar.Jet :=
  (hodgeScalarToJet A J α hs ht D hD p).extendOfNorm (hodgeSmooth A J α hs ht)
lemma hodgeEnergyToScalarJet_smooth (p : A.centers) (a : PreL2 A J α hs ht true) :
    hodgeEnergyToScalarJet A J α hs ht D hD p (hodgeSmooth A J α hs ht a) =
      hodgeScalarToJet A J α hs ht D hD p a :=
  LinearMap.extendOfNorm_eq (hodgeSmooth_dense A J α hs ht) (hodgeScalarToJet_bound A J α hs ht D hD p) a
lemma hodge_energy_scalar_derivative (p : A.centers) (u : hodgeEnergy A J α hs ht)
    (i : Fin (Module.finrank ℝ Space)) :
    LineDeriv.lineDerivOpCLM ℝ 𝓢'(Space,HodgeScalar.F) (stdOrthonormalBasis ℝ Space i)
      (HodgeScalar.jetDistribution none (hodgeEnergyToScalarJet A J α hs ht D hD p u)) =
      HodgeScalar.jetDistribution (some i) (hodgeEnergyToScalarJet A J α hs ht D hD p u) := by
  let L := LineDeriv.lineDerivOpCLM ℝ 𝓢'(Space,HodgeScalar.F) (stdOrthonormalBasis ℝ Space i) ∘L
    HodgeScalar.jetDistribution none ∘L hodgeEnergyToScalarJet A J α hs ht D hD p
  let R := HodgeScalar.jetDistribution (some i) ∘L hodgeEnergyToScalarJet A J α hs ht D hD p
  exact (hodgeSmooth_dense A J α hs ht).induction_on u (isClosed_eq L.continuous R.continuous) (fun a => by
    change L (hodgeSmooth A J α hs ht a) = R (hodgeSmooth A J α hs ht a)
    dsimp only [L,R,ContinuousLinearMap.comp_apply]
    rw [hodgeEnergyToScalarJet_smooth]
    exact HodgeScalar.jet_derivative _ i)

def hodgeScalarDistribution (p : A.centers) : hodgeEnergy A J α hs ht →L[ℝ] 𝓢'(Space,HodgeScalar.F) :=
  HodgeScalar.jetDistribution none ∘L hodgeEnergyToScalarJet A J α hs ht D hD p
lemma hodgeScalarDistribution_H1 (p : A.centers) (u : hodgeEnergy A J α hs ht) :
    MemSobolev 1 2 (hodgeScalarDistribution A J α hs ht D hD p u) := by
  have h0 (j : DerivativeIndex) : MemSobolev 0 2
      (HodgeScalar.jetDistribution j (hodgeEnergyToScalarJet A J α hs ht D hD p u)) := by
    refine ⟨hodgeEnergyToScalarJet A J α hs ht D hD p u j,?_⟩
    simp only [besselPotential_zero,ContinuousLinearMap.id_apply]
    rfl
  have hd (i : Fin (Module.finrank ℝ Space)) : MemSobolev 0 2
      (LineDeriv.lineDerivOpCLM ℝ 𝓢'(Space,HodgeScalar.F) (stdOrthonormalBasis ℝ Space i)
        (hodgeScalarDistribution A J α hs ht D hD p u)) := by
    change MemSobolev 0 2 (LineDeriv.lineDerivOpCLM ℝ _ _
      (HodgeScalar.jetDistribution none (hodgeEnergyToScalarJet A J α hs ht D hD p u)))
    rw [hodge_energy_scalar_derivative]
    exact h0 (some i)
  convert memSobolev_succ_of_derivatives (stdOrthonormalBasis ℝ Space) (h0 none) hd using 1
  · norm_num
  · rfl
lemma hodgeScalarDistribution_smooth (p : A.centers) (a : PreL2 A J α hs ht true) :
    hodgeScalarDistribution A J α hs ht D hD p (hodgeSmooth A J α hs ht a) =
      (scalarVectorLinear A J α ht (fun q => (D q).toData) hD p a : 𝓢'(Space,HodgeScalar.F)) := by
  change HodgeScalar.jetDistribution none
    (hodgeEnergyToScalarJet A J α hs ht D hD p (hodgeSmooth A J α hs ht a)) = _
  rw [hodgeEnergyToScalarJet_smooth]
  exact HodgeScalar.jetDistribution_jet _ none

def hodgeRawDistribution (p : A.centers) (τ : 𝓢(Space,ℝ)) :
    hodgeEnergy A J α hs ht →L[ℝ] 𝓢'(Space,HodgeScalar.F) :=
  (smulLeftCLM HodgeScalar.F (SchwartzMap.postcompCLM Complex.ofRealCLM τ)).restrictScalars ℝ ∘L
    hodgeScalarDistribution A J α hs ht D hD p
lemma hodgeRawDistribution_H1 (p : A.centers) (τ : 𝓢(Space,ℝ)) (u : hodgeEnergy A J α hs ht) :
    MemSobolev 1 2 (hodgeRawDistribution A J α hs ht D hD p τ u) := by
  change MemSobolev 1 2 (smulLeftCLM HodgeScalar.F
    (SchwartzMap.postcompCLM Complex.ofRealCLM τ) (hodgeScalarDistribution A J α hs ht D hD p u))
  have hu := hodgeScalarDistribution_H1 A J α hs ht D hD p u
  simpa only [Nat.cast_one] using
    (EuclideanSobolevOperators.memSobolev_nat_product (E := Space) (F := HodgeScalar.F) 1
      (SchwartzMap.postcompCLM Complex.ofRealCLM τ)
      (u := hodgeScalarDistribution A J α hs ht D hD p u) (by simpa only [Nat.cast_one] using hu))
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
