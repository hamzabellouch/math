import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.AntiChartH1
import OAI.Geometry.TamingCompatibility.DifferentialForms.GeometricFrameTest

namespace OAI


noncomputable section
namespace TamingCompatibility.ScalarPair
open MeasureTheory LineDeriv EuclideanEnergy ManifoldLocalization
open scoped SchwartzMap LineDeriv

abbrev Jet := PiLp 2 (fun _ : DerivativeIndex => Lp F 2 (volume : Measure Space))

def jetComponent (j : DerivativeIndex) : 𝓢(Space,F) →L[ℝ] 𝓢(Space,F) :=
  match j with
  | none => ContinuousLinearMap.id ℝ _
  | some i => lineDerivOpCLM ℝ 𝓢(Space,F) (stdOrthonormalBasis ℝ Space i)

def jet : 𝓢(Space,F) →L[ℝ] Jet :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : DerivativeIndex => Lp F 2 (volume : Measure Space))).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun j => SchwartzMap.toLpCLM ℝ F 2 (volume : Measure Space) ∘L jetComponent j)

lemma make_jet_bound (s t : S) :
    ‖jet (make s t)‖^2 ≤ 20*((∫ x, gradientEnergy s t x)+(∫ x, (s x)^2+(t x)^2)) := by
  let G := ∫ x, gradientEnergy s t x
  let Z := ∫ x, (s x)^2+(t x)^2
  have hG : 0 ≤ G := integral_nonneg (fun x => Finset.sum_nonneg fun i _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hZ : 0 ≤ Z := integral_nonneg (fun x => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hd : ∑ i : Fin 4, ∫ x, ‖(∂_{e i} (make s t)) x‖^2 = G := by
    simp only [make_derivative,make_norm_sq]
    change (∑ i : Fin 4, ∫ x, (coordinateDeriv i s x)^2+(coordinateDeriv i t x)^2) = _
    symm
    exact integral_finsetSum _ (fun i _ => (schwartz_sq_integrable (coordinateDeriv i s)).add
      (schwartz_sq_integrable (coordinateDeriv i t)))
  have hj (j : DerivativeIndex) : ‖jet (make s t) j‖^2 ≤ 4*(G+Z) := by
    change ‖(jetComponent j (make s t)).toLp 2 (volume : Measure Space)‖^2 ≤ _
    rw [GeometricChart.schwartz_l2_norm_sq]
    cases j with
    | none =>
      change (∫ x, ‖make s t x‖^2) ≤ _
      simp_rw [make_norm_sq]
      change Z ≤ 4*(G+Z)
      linarith
    | some i =>
      have hb := direction_integral_bound (make s t) (stdOrthonormalBasis ℝ Space i)
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
end TamingCompatibility.ScalarPair

namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart MeasureTheory
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def scalarToJet (p : A.centers) : antiPre A J α hs ht →ₗ[ℝ] ScalarPair.Jet :=
  ScalarPair.jet.toLinearMap ∘ₗ pairLinear A J α ht D hD p ∘ₗ (antiPre A J α hs ht).subtype

lemma scalarToJet_bound (p : A.centers) : ∃ C : ℝ, ∀ a : antiPre A J α hs ht,
    ‖scalarToJet A J α hs ht D hD p a‖ ≤ C * ‖antiToEnergy A J α hs ht a‖ := by
  obtain ⟨C,hC,hb⟩ := scalar_garding A J α hs ht D hD p
  refine ⟨Real.sqrt (20*C),fun a => ?_⟩
  have h := ScalarPair.make_jet_bound (scalarSchwartz A J α ht D hD p a.val.val a.val.property 2)
    (scalarSchwartz A J α ht D hD p a.val.val a.val.property 3)
  have hga := hb a.val.val a.val.property a.property
  rw [← antiGraph_norm_sq A J α hs ht a] at hga
  change (∫ z, EuclideanEnergy.gradientEnergy (scalarSchwartz A J α ht D hD p a.val.val a.val.property 2)
    (scalarSchwartz A J α ht D hD p a.val.val a.val.property 3) z) +
    (∫ z, (scalarSchwartz A J α ht D hD p a.val.val a.val.property 2 z)^2 +
      (scalarSchwartz A J α ht D hD p a.val.val a.val.property 3 z)^2) ≤
      C * ‖antiToEnergy A J α hs ht a‖^2 at hga
  have hn : ‖scalarToJet A J α hs ht D hD p a‖^2 ≤ 20*C*‖antiToEnergy A J α hs ht a‖^2 := by
    exact h.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hga (show (0:ℝ) ≤ 20 by norm_num))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 20*C)]
  exact hn

def energyToScalarJet (p : A.centers) : antiEnergy A J α hs ht →L[ℝ] ScalarPair.Jet :=
  (scalarToJet A J α hs ht D hD p).extendOfNorm (antiToEnergy A J α hs ht)

lemma energyToScalarJet_smooth (p : A.centers) (a : antiPre A J α hs ht) :
    energyToScalarJet A J α hs ht D hD p (antiToEnergy A J α hs ht a) = scalarToJet A J α hs ht D hD p a :=
  LinearMap.extendOfNorm_eq (antiToEnergy_dense A J α hs ht) (scalarToJet_bound A J α hs ht D hD p) a

lemma energy_scalar_derivative (p : A.centers) (u : antiEnergy A J α hs ht)
    (i : Fin (Module.finrank ℝ Space)) :
    LineDeriv.lineDerivOpCLM ℝ 𝓢'(Space,ScalarPair.F) (stdOrthonormalBasis ℝ Space i)
      (ScalarPair.jetDistribution none (energyToScalarJet A J α hs ht D hD p u)) =
      ScalarPair.jetDistribution (some i) (energyToScalarJet A J α hs ht D hD p u) := by
  let L := LineDeriv.lineDerivOpCLM ℝ 𝓢'(Space,ScalarPair.F) (stdOrthonormalBasis ℝ Space i) ∘L
    ScalarPair.jetDistribution none ∘L energyToScalarJet A J α hs ht D hD p
  let R := ScalarPair.jetDistribution (some i) ∘L energyToScalarJet A J α hs ht D hD p
  exact (antiToEnergy_dense A J α hs ht).induction_on u (isClosed_eq L.continuous R.continuous) (fun a => by
    change L (antiToEnergy A J α hs ht a) = R (antiToEnergy A J α hs ht a)
    dsimp only [L,R,ContinuousLinearMap.comp_apply]
    rw [energyToScalarJet_smooth]
    exact ScalarPair.jet_derivative _ i)
end TamingCompatibility.GeometricHilbert

end

end OAI
