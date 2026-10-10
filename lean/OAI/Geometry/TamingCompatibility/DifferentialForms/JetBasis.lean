import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.RawJetEstimate

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.JetOperator
open EuclideanEnergy ContinuousAlternatingMap Set LineDeriv
open scoped SchwartzMap ContDiff LineDeriv
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type*} [Fintype ι]
abbrev BasisJet (ι F : Type*) := F × (ι → F) × (ι → ι → F)
def basisValue (b : ι → V) (u : 𝓢(V,F)) (x : V) : BasisJet ι F :=
  (u x,(fun i => (∂_{b i} u) x),(fun i j => (∂_{b j} (∂_{b i} u)) x))
def basisProjZero : BasisJet ι F →L[ℝ] F := ContinuousLinearMap.fst ℝ F _
def basisProjOne (i : ι) : BasisJet ι F →L[ℝ] F :=
  (ContinuousLinearMap.proj i).comp ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ F _))
def basisProjTwo (i j : ι) : BasisJet ι F →L[ℝ] F :=
  ((ContinuousLinearMap.proj j) : (ι → F) →L[ℝ] F).comp
    (((ContinuousLinearMap.proj i) : (ι → ι → F) →L[ℝ] (ι → F)).comp
    ((ContinuousLinearMap.snd ℝ (ι → F) (ι → ι → F)).comp
      (ContinuousLinearMap.snd ℝ F _)))
lemma schwartz_direction_any_basis (b : Module.Basis ι ℝ V) (v : V) (u : 𝓢(V,F)) :
    ∂_{v} u = ∑ i : ι, b.repr v i • ∂_{b i} u := by
  have he : v = ∑ i : ι, b.repr v i • b i := (b.sum_repr v).symm
  conv_lhs => rw [he]
  simp only [lineDerivOp_left_sum,lineDerivOp_left_smul]
def basisDirectionOne (b : Module.Basis ι ℝ V) (v : V) : BasisJet ι F →L[ℝ] F :=
  ∑ i : ι, b.repr v i • basisProjOne i
def basisDirectionTwo (b : Module.Basis ι ℝ V) (v w : V) : BasisJet ι F →L[ℝ] F :=
  ∑ i : ι, ∑ j : ι, (b.repr v i * b.repr w j) • basisProjTwo i j
lemma basisDirectionOne_value (b : Module.Basis ι ℝ V) (v : V) (u : 𝓢(V,F)) (x : V) :
    basisDirectionOne b v (basisValue b u x) = (∂_{v} u) x := by
  rw [schwartz_direction_any_basis b]
  simp only [basisDirectionOne,basisValue,basisProjOne,_root_.sum_apply,_root_.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
lemma basisDirectionTwo_value (b : Module.Basis ι ℝ V) (v w : V) (u : 𝓢(V,F)) (x : V) :
    basisDirectionTwo b v w (basisValue b u x) = (∂_{w} (∂_{v} u)) x := by
  rw [schwartz_direction_any_basis b v u]
  simp only [lineDerivOp_sum,lineDerivOp_smul]
  simp_rw [schwartz_direction_any_basis b w]
  simp only [Finset.smul_sum,smul_smul,basisDirectionTwo,basisValue,basisProjTwo,
    _root_.sum_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,ContinuousLinearMap.coe_snd']
def basisToCoordinate (b : Module.Basis ι ℝ V) : BasisJet ι F →L[ℝ] Jet F :=
  basisProjZero.prod ((ContinuousLinearMap.pi (fun i : Fin 4 => basisDirectionOne b (e i))).prod
    (ContinuousLinearMap.pi (fun i : Fin 4 =>
      ContinuousLinearMap.pi (fun j : Fin 4 => basisDirectionTwo b (e i) (e j)))))
lemma basisToCoordinate_value (b : Module.Basis ι ℝ V) (u : 𝓢(V,F)) (x : V) :
    basisToCoordinate b (basisValue b u x) = value u x := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext i
      exact basisDirectionOne_value b (e i) u x
    · funext i j
      exact basisDirectionTwo_value b (e i) (e j) u x
lemma basisValue_norm (b : ι → V) (u : 𝓢(V,F)) (x : V) :
    ‖basisValue b u x‖ ≤ ‖u x‖ + ∑ i : ι, ‖(∂_{b i} u) x‖ +
      ∑ i : ι, ∑ j : ι, ‖(∂_{b j} (∂_{b i} u)) x‖ := by
  have h1 : ‖(fun i : ι => (∂_{b i} u) x)‖ ≤ ∑ i : ι, ‖(∂_{b i} u) x‖ := by
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr
    intro i
    exact Finset.single_le_sum (f := fun i : ι => ‖(∂_{b i} u) x‖)
      (fun i _ => norm_nonneg ((∂_{b i} u) x)) (Finset.mem_univ i)
  have h2 : ‖(fun i : ι => fun j : ι => (∂_{b j} (∂_{b i} u)) x)‖ ≤
      ∑ i : ι, ∑ j : ι, ‖(∂_{b j} (∂_{b i} u)) x‖ := by
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)))).mpr
    intro i
    have hi : ‖(fun j : ι => (∂_{b j} (∂_{b i} u)) x)‖ ≤
        ∑ j : ι, ‖(∂_{b j} (∂_{b i} u)) x‖ := by
      apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun j _ => norm_nonneg ((∂_{b j} (∂_{b i} u)) x)))).mpr
      intro j
      exact Finset.single_le_sum (f := fun j : ι => ‖(∂_{b j} (∂_{b i} u)) x‖)
        (fun j _ => norm_nonneg ((∂_{b j} (∂_{b i} u)) x)) (Finset.mem_univ j)
    exact hi.trans (Finset.single_le_sum
      (f := fun i : ι => ∑ j : ι, ‖(∂_{b j} (∂_{b i} u)) x‖)
      (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg ((∂_{b j} (∂_{b i} u)) x))) (Finset.mem_univ i))
  simp only [basisValue,Prod.norm_def]
  have hz0 := norm_nonneg (u x)
  have hz1 := norm_nonneg (fun i : ι => (∂_{b i} u) x)
  have hz2 := norm_nonneg (fun i j : ι => (∂_{b j} (∂_{b i} u)) x)
  apply max_le
  · linarith
  · apply max_le <;> linarith

lemma basis_linear_output_scaled_bound {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : Jet F →L[ℝ] G) (L : V ≃L[ℝ] V) (b : Module.Basis ι ℝ V) (u : 𝓢(V,F)) (z : V)
    {r M : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (h : let U := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ L.symm u
      r*‖U (L z)‖ + r^2*∑ i, ‖(∂_{b i} U) (L z)‖ +
        r^3*∑ i, ∑ j, ‖(∂_{b j} (∂_{b i} U)) (L z)‖ ≤ M) :
    r^3*‖T (value u z)‖ ≤ ‖T.comp ((linearTransport L).comp (basisToCoordinate b))‖*M := by
  let U := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ L.symm u
  have h13 : r^3 ≤ r := by nlinarith [sq_nonneg r, mul_le_mul_of_nonneg_left hr1 (sq_nonneg r)]
  have h23 : r^3 ≤ r^2 := by nlinarith [mul_le_mul_of_nonneg_left hr1 (sq_nonneg r)]
  have hn : r^3*‖basisValue b U (L z)‖ ≤ M := by
    apply (mul_le_mul_of_nonneg_left (basisValue_norm b U (L z)) (by positivity : 0 ≤ r^3)).trans
    have ha := mul_le_mul_of_nonneg_right h13 (norm_nonneg (U (L z)))
    have hb := mul_le_mul_of_nonneg_right h23
      (show 0 ≤ ∑ i : ι, ‖(∂_{b i} U) (L z)‖ from Finset.sum_nonneg (fun i _ => norm_nonneg ((∂_{b i} U) (L z))))
    dsimp only at h
    change r*‖U (L z)‖ + r^2*∑ i, ‖(∂_{b i} U) (L z)‖ +
        r^3*∑ i, ∑ j, ‖(∂_{b j} (∂_{b i} U)) (L z)‖ ≤ M at h
    nlinarith only [ha,hb,h]
  rw [value_recover_linear L u z,← basisToCoordinate_value b U (L z)]
  let T' := T.comp ((linearTransport L).comp (basisToCoordinate b))
  change r^3*‖T' (basisValue b U (L z))‖ ≤ ‖T'‖*M
  calc
    _ ≤ r^3*(‖T'‖*‖basisValue b U (L z)‖) :=
      mul_le_mul_of_nonneg_left (T'.le_opNorm _) (by positivity)
    _ = ‖T'‖*(r^3*‖basisValue b U (L z)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
end TamingCompatibility.JetOperator

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator GeometricAdjoint Set Filter ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

include hs in

lemma ddstar_scaled_basis_jet_bound {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ Space) (L : Space ≃L[ℝ] Space) {K : Set Space}
    (hK : IsCompact K) (hKD : K ⊆ D.domain) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (a : TwoForm X), IsSmooth a → antiInvariantPart J a = a →
      ∀ (U : Set Space), IsOpen U → U ⊆ D.domain →
      ∀ (u : 𝓢(Space,C 2)), (∀ z ∈ U, rawPair J α ht p D a z = retract 2 (u z)) →
      ∀ (z : Space), z ∈ U → z ∈ K → ∀ (r M : ℝ), 0 < r → r ≤ 1 →
      (let v := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm u
       r*‖v (L z)‖ + r^2*∑ i, ‖(∂_{b i} v) (L z)‖ +
         r^3*∑ i, ∑ j, ‖(∂_{b j} (∂_{b i} v)) (L z)‖ ≤ M) →
      r^3*‖ManifoldForms.pullback (exteriorDerivative (codifferential J α ht a))
        (extChartAt Model p).symm z‖ ≤ C₀*M := by
  obtain ⟨B,hB,hbound⟩ := JetOperator.exteriorJet_bounded D.domain_open hK hKD
    (deltaComplexA J α ht p D) (deltaComplexB J α ht p D)
    (deltaComplexA_smooth J α hs ht p D) (deltaComplexB_smooth J α hs ht p D)
  let T := (JetOperator.linearTransport L (F := C 2)).comp (JetOperator.basisToCoordinate b)
  refine ⟨B*‖T‖,mul_nonneg hB (norm_nonneg _),fun a ha hanti U hU hUD u hrep z hz hzK r M hr hr1 hj => ?_⟩
  have hM : 0 ≤ M := by
    apply le_trans _ hj
    positivity
  rw [ddstar_local_jet J α hs ht p D ha hanti hU hUD u hrep hz]
  apply (JetOperator.basis_linear_output_scaled_bound
    (JetOperator.exteriorJet (deltaComplexA J α ht p D) (deltaComplexB J α ht p D) z)
    L b u z hr hr1 hj).trans
  apply mul_le_mul_of_nonneg_right _ hM
  exact (ContinuousLinearMap.opNorm_comp_le _ T).trans
    (mul_le_mul_of_nonneg_right (hbound z hzK) (norm_nonneg T))
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
