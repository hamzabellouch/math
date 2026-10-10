import OAI.Geometry.Relativity.CKS.MassJetRealization
import OAI.Geometry.Relativity.CKS.MixedMassCoefficient

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def traceProduct (q p : Mat) : ℝ := ∑ i, ∑ k, q i k*p k i

lemma traceProduct_diff {q p : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (hp : ContDiffAt ℝ 2 p x) :
    ContDiffAt ℝ 2 (fun y => traceProduct (q y) (p y)) x := by
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun k _ =>
    (component_diff hq i k).mul (component_diff hp k i)

lemma actual_traceProductJet {q p : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (hp : ContDiffAt ℝ 2 p x) :
    actualScalarJet (fun y => traceProduct (q y) (p y)) x =
      traceProductJet (matrixScalarJets q x) (matrixScalarJets p x) := by
  unfold traceProduct traceProductJet
  rw [actualScalarJet_sum _ (fun i _ => ContDiffAt.sum fun k _ =>
    (component_diff hq i k).mul (component_diff hp k i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [actualScalarJet_sum _ (fun k _ => (component_diff hq i k).mul (component_diff hp k i))]
  apply Finset.sum_congr rfl
  intro k _
  exact actualScalarJet_mul (component_diff hq i k) (component_diff hp k i)

lemma inverse_diff_at {n : ℕ} {q : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ n q x) (h0 : determinant (q x) ≠ 0) :
    ContDiffAt ℝ n (fun y => inverse (q y)) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro k
  unfold inverse
  apply ContDiffAt.div
  · fin_cases i <;> fin_cases k <;> dsimp <;> first
      | exact contDiffAt_pi.mp (contDiffAt_pi.mp hq _) _
      | exact (contDiffAt_pi.mp (contDiffAt_pi.mp hq _) _).neg
  · exact (determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt.comp x hq
  · exact h0

lemma actual_inverseJets {q : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (h0 : determinant (q x) ≠ 0) :
    matrixScalarJets (fun y => inverse (q y)) x = inverseMatrixJet (matrixScalarJets q x) := by
  funext i k
  exact actual_inverseMatrixJet hq h0 i k

def massNumeratorField (z D T V : Point → ℝ) : Point → ℝ := fun y =>
  (1+z y^2)*V y+2*T y-2*((1+z y^2)*D y)+
    z y^3*(T y*T y+2*(T y*V y)-(1+z y^2)*(D y*D y))+
    z y^6*((T y*T y)*V y)

def normalizedMassField (z D T V : Point → ℝ) : Point → ℝ := fun y =>
  (1/2:ℝ)*(massNumeratorField z D T V y*(1+z y^3*V y)⁻¹)

lemma massNumeratorField_diff {z D T V : Point → ℝ} {x : Point}
    (hz : ContDiffAt ℝ 2 z x) (hD : ContDiffAt ℝ 2 D x) (hT : ContDiffAt ℝ 2 T x) (hV : ContDiffAt ℝ 2 V x) :
    ContDiffAt ℝ 2 (massNumeratorField z D T V) x := by
  unfold massNumeratorField
  fun_prop

lemma actual_massNumeratorJet {z D T V : Point → ℝ} {x : Point}
    (hz : ContDiffAt ℝ 2 z x) (hD : ContDiffAt ℝ 2 D x) (hT : ContDiffAt ℝ 2 T x) (hV : ContDiffAt ℝ 2 V x) :
    actualScalarJet (massNumeratorField z D T V) x =
      massNumeratorJet (actualScalarJet z x) (actualScalarJet D x) (actualScalarJet T x) (actualScalarJet V x) := by
  unfold massNumeratorField massNumeratorJet
  simp (disch := fun_prop) only [actualScalarJet_add,actualScalarJet_sub,actualScalarJet_smul,
    actualScalarJet_mul,actualScalarJet_pow,actualScalarJet_const]

lemma actual_normalizedMassJet {z D T V : Point → ℝ} {x : Point}
    (hz : ContDiffAt ℝ 2 z x) (hD : ContDiffAt ℝ 2 D x) (hT : ContDiffAt ℝ 2 T x) (hV : ContDiffAt ℝ 2 V x)
    (h0 : 1+z x^3*V x ≠ 0) :
    actualScalarJet (normalizedMassField z D T V) x =
      normalizedMassJet (actualScalarJet z x) (actualScalarJet D x) (actualScalarJet T x) (actualScalarJet V x) := by
  have hm : ContDiffAt ℝ 2 (fun y => z y^3*V y) x := by fun_prop
  have hd : ContDiffAt ℝ 2 (fun y => 1+z y^3*V y) x := by fun_prop
  have hi : ContDiffAt ℝ 2 (fun y => (1+z y^3*V y)⁻¹) x := hd.inv h0
  have hrec : actualScalarJet (fun y => (1+z y^3*V y)⁻¹) x =
      reciprocalJet (actualScalarJet (fun y => 1+z y^3*V y) x) := by
    simpa only [one_div] using actual_reciprocal hd h0
  unfold normalizedMassField normalizedMassJet
  rw [actualScalarJet_smul (1/2:ℝ) ((massNumeratorField_diff hz hD hT hV).mul hi),
    actualScalarJet_mul (massNumeratorField_diff hz hD hT hV) hi,
    actual_massNumeratorJet hz hD hT hV,hrec,
    actualScalarJet_add (f := fun _ : Point => (1:ℝ)) contDiffAt_const hm,
    actualScalarJet_const,actualScalarJet_mul (hz.pow 3) hV,actualScalarJet_pow hz]

end
end CKSMixedGeometry

end

end OAI
