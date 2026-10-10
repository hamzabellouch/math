import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.MatrixAlgebras.MatrixPartialFlips
import OAI.Analysis.JiangSu.CStarAlgebras.TwoParameterPartition

namespace OAI


noncomputable section
namespace JiangSuConstruction
open MatrixTensor Pureness
open scoped CStarAlgebra ComplexOrder TensorProduct

variable {p q r s : ℕ}

lemma dropFiber_zero : dropFiber p q leftEndpoint=(leftAmplification p q).range := by
  simp [dropFiber]
lemma dropFiber_one : dropFiber p q rightEndpoint=(rightAmplification p q).range := by
  have hn : rightEndpoint≠leftEndpoint := by
    intro h
    have := congrArg Subtype.val h
    norm_num [rightEndpoint,leftEndpoint] at this
  simp [dropFiber,hn]

def cutoffFiber (t : Interval) (ρ : C(Interval,ℝ))
    (h0 : t≠leftEndpoint → ρ leftEndpoint=0)
    (h1 : t≠rightEndpoint → ρ rightEndpoint=0) :
    dropFiber p q t →ₗ[ℂ] DimensionDrop p q where
  toFun a := ⟨⟨fun x => (ρ x:ℂ) • a.val,by fun_prop⟩,by
    constructor
    · by_cases ht : t=leftEndpoint
      · subst t
        exact (leftAmplification p q).range.smul_mem (by simpa only [dropFiber_zero] using a.property) _
      · change (ρ leftEndpoint:ℂ) • a.val∈(leftAmplification p q).range
        simp [h0 ht]
    · by_cases ht : t=rightEndpoint
      · subst t
        exact (rightAmplification p q).range.smul_mem (by simpa only [dropFiber_one] using a.property) _
      · change (ρ rightEndpoint:ℂ) • a.val∈(rightAmplification p q).range
        simp [h1 ht]⟩
  map_add' a b := by
    apply Subtype.ext; apply ContinuousMap.ext; intro x
    exact smul_add _ _ _
  map_smul' c a := by
    apply Subtype.ext; apply ContinuousMap.ext; intro x
    exact smul_comm _ _ _

local instance (priority := 2000) localDropSemiring (p q : ℕ) : Semiring (DimensionDrop p q) :=
  (inferInstance : CStarAlgebra (DimensionDrop p q)).toSemiring

lemma tensor_cutoff_apply (t u : Interval) (ρ σ : C(Interval,ℝ)) (h0 h1 k0 k1)
    (z : (dropFiber p q t) ⊗[ℂ] (dropFiber r s u)) (x y : Interval) :
    ((squareTensorMap p q r s)
      (TensorProduct.map (cutoffFiber t ρ h0 h1) (cutoffFiber u σ k0 k1) z)).val (x,y)=
      (ρ x*σ y) • fiberMap (dropFiber p q t) (dropFiber r s u) z := by
  change (sectionMap (dimensionDrop p q) (dimensionDrop r s) _) (x,y) = _
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    change left ((ρ x:ℂ) • a.val)*right ((σ y:ℂ) • b.val)=
      (ρ x*σ y) • (left a.val*right b.val)
    rw [map_smul,map_smul,smul_mul_assoc,mul_smul_comm,smul_smul,←Complex.ofReal_mul,
      Complex.coe_smul]
    rfl
  | add _ _ hz hw =>
    rw [map_add,map_add,ContinuousMap.add_apply,hz,hw,map_add,smul_add]

lemma convex_sum_error {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : ι → ℝ) (v : ι → E) (a : E) (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1)
    {δ : ℝ} (hδ : 0≤δ) (hv : ∀ i,w i≠0 → ‖v i-a‖≤δ) :
    ‖∑ i,w i • v i-a‖≤δ := by
  classical
  have he : ∑ i,w i • v i-a=∑ i,w i • (v i-a) := by
    simp only [smul_sub,Finset.sum_sub_distrib,←Finset.sum_smul,hs,one_smul]
  rw [he]
  calc
    _ ≤ ∑ i,‖w i • (v i-a)‖ := norm_sum_le _ _
    _ ≤ ∑ i,w i*δ := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : w i=0
      · simp only [hi,zero_smul,norm_zero]
        exact mul_nonneg (le_refl 0) hδ
      · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hw i)]
        exact mul_le_mul_of_nonneg_left (hv i hi) (hw i)
    _ = δ := by rw [←Finset.sum_mul,hs,one_mul]

theorem squareTensorMap_dense : DenseRange (squareTensorMap p q r s) := by
  classical
  apply Metric.denseRange_iff.mpr
  intro f ε hε
  obtain ⟨S,T,ρ,σ,hρ,hσ,hs,ht,hx0,hx1,hy0,hy1,hf⟩ :=
    EndpointPartition.exists_rectangular_weights leftEndpoint rightEndpoint
      leftEndpoint rightEndpoint f.val (show 0<ε/2 by positivity)
  have hsample (i : S) (j : T) : ∃ z : dropFiber p q i.val ⊗[ℂ] dropFiber r s j.val,
      fiberMap (dropFiber p q i.val) (dropFiber r s j.val) z=f.val (i.val,j.val) :=
    f.property i.val j.val
  choose z hz using hsample
  let Z := ∑ i,∑ j,TensorProduct.map (cutoffFiber i.val (ρ i) (hx0 i) (hx1 i))
    (cutoffFiber j.val (σ j) (hy0 j) (hy1 j)) (z i j)
  refine ⟨Z,?_⟩
  have heval (x y : Interval) : (squareTensorMap p q r s Z).val (x,y)=
      ∑ i,∑ j,(ρ i x*σ j y) • f.val (i.val,j.val) := by
    change ((squareSections p q r s).subtype (squareTensorMap p q r s Z)) (x,y)=_
    simp only [Z,map_sum,ContinuousMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change (squareTensorMap p q r s _).val (x,y)=_
    rw [tensor_cutoff_apply,hz]
  have hnorm : ‖squareTensorMap p q r s Z-f‖≤ε/2 := by
    change ‖(squareTensorMap p q r s Z).val-f.val‖≤ε/2
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    rintro ⟨x,y⟩
    change ‖(squareTensorMap p q r s Z).val (x,y)-f.val (x,y)‖≤ε/2
    rw [heval,←Finset.sum_product']
    apply convex_sum_error (fun ij : S×T => ρ ij.1 x*σ ij.2 y)
      (fun ij => f.val (ij.1.val,ij.2.val)) (f.val (x,y))
      (fun ij => mul_nonneg (hρ _ _) (hσ _ _))
    · rw [Fintype.sum_prod_type]
      simp only [←Finset.mul_sum,ht,mul_one,hs]
    · positivity
    · intro ij hij
      have hi : ρ ij.1 x≠0 := (mul_ne_zero_iff.mp hij).1
      have hj : σ ij.2 y≠0 := (mul_ne_zero_iff.mp hij).2
      rw [norm_sub_rev]
      exact (hf ij.1 ij.2 x y hi hj).le
  rw [dist_eq_norm,norm_sub_rev]
  exact hnorm.trans_lt (by linarith)

end JiangSuConstruction

end


noncomputable section
namespace JiangSuConstruction
open MatrixTensor FourEdgeSurgery
open scoped CStarAlgebra ComplexOrder

variable {p q : ℕ}

lemma leftAmplification_eq : leftAmplification p q=MatrixTensor.left := by rfl
lemma rightAmplification_eq : rightAmplification p q=MatrixTensor.right := by rfl

def rightUnitary (w : unitary (TensorMat p q)) : unitary (MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q))) :=
  ⟨MatrixTensor.right (I := Fin p×Fin q) (w:(TensorMat p q)),Unitary.map_mem _ w.property⟩
lemma rightUnitary_continuous : Continuous (rightUnitary (p := p) (q := q)) :=
  continuous_induced_rng.mpr ((map_continuous MatrixTensor.right).comp continuous_subtype_val)
@[simp] lemma rightUnitary_one : rightUnitary (p := p) (q := q) 1=1 := by
  apply Subtype.ext
  exact map_one _

variable (W : C(Interval×Interval,unitary (TensorMat p q))) (a b : C(Interval,ℝ))
variable (ha0 : a leftEndpoint=1) (ha1 : a rightEndpoint=0)
variable (hb0 : b leftEndpoint=0) (hb1 : b rightEndpoint=1)
variable (hW0 : W (leftEndpoint,leftEndpoint)=1)
variable (hW1 : W (rightEndpoint,rightEndpoint)=1)

def surgerySection : C(Interval×Interval,unitary (MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q)))) :=
  ⟨fun z => surgery (pFlow (I := Fin p) (J := Fin q)) (qFlow (I := Fin p) (J := Fin q)) (rightUnitary (W (z.1,leftEndpoint)))
    (rightUnitary (W (z.1,rightEndpoint))) (rightUnitary (W z))
    (a z.1) (b z.1) (a z.2) (b z.2),by
    apply surgery_continuous
    · exact pFlow_continuous
    · exact qFlow_continuous
    · exact rightUnitary_continuous.comp (W.continuous.comp (continuous_fst.prodMk continuous_const))
    · exact rightUnitary_continuous.comp (W.continuous.comp (continuous_fst.prodMk continuous_const))
    · exact rightUnitary_continuous.comp W.continuous
    · exact a.continuous.comp continuous_fst
    · exact b.continuous.comp continuous_fst
    · exact a.continuous.comp continuous_snd
    · exact b.continuous.comp continuous_snd⟩

include ha0 hb0 hW0 in
lemma surgerySection_left_zero (t : Interval) :
    surgerySection W a b (leftEndpoint,t)=(pFlow (I := Fin p) (J := Fin q)) (b t)*rightUnitary (W (leftEndpoint,t))*(pFlow (I := Fin p) (J := Fin q)) 1 := by
  change surgery (pFlow (I := Fin p) (J := Fin q)) (qFlow (I := Fin p) (J := Fin q)) _ _ _ _ _ _ _=_
  rw [ha0,hb0,hW0,rightUnitary_one]
  exact surgery_left_zero (pFlow (I := Fin p) (J := Fin q)) (qFlow (I := Fin p) (J := Fin q)) (by simpa only [qFlow_one] using (partialQ_sq (I := Fin p) (J := Fin q))) _ _ _ _
include ha1 hb1 hW1 in
lemma surgerySection_left_one (t : Interval) :
    surgerySection W a b (rightEndpoint,t)=(qFlow (I := Fin p) (J := Fin q)) (a t)*rightUnitary (W (rightEndpoint,t))*(qFlow (I := Fin p) (J := Fin q)) 1 := by
  change surgery (pFlow (I := Fin p) (J := Fin q)) (qFlow (I := Fin p) (J := Fin q)) _ _ _ _ _ _ _=_
  rw [ha1,hb1,hW1,rightUnitary_one]
  exact surgery_left_one (pFlow (I := Fin p) (J := Fin q)) (qFlow (I := Fin p) (J := Fin q)) (by simpa only [pFlow_one] using (partialP_sq (I := Fin p) (J := Fin q)))
    flows_commute _ _ _ _
include ha0 hb0 in
lemma surgerySection_right_zero (s : Interval) :
    surgerySection W a b (s,leftEndpoint)=
      ((qFlow (I := Fin p) (J := Fin q)) 1*rightUnitary (W (s,leftEndpoint))*(qFlow (I := Fin p) (J := Fin q)) 1)*(pFlow (I := Fin p) (J := Fin q)) 1*(pFlow (I := Fin p) (J := Fin q)) (b s) := by
  change surgery (pFlow (I := Fin p) (J := Fin q)) (qFlow (I := Fin p) (J := Fin q)) _ _ _ _ _ _ _=_
  rw [ha0,hb0]
  exact surgery_right_zero (pFlow (I := Fin p) (J := Fin q)) (qFlow (I := Fin p) (J := Fin q)) flows_commute _ _ _ _
include ha1 hb1 in
lemma surgerySection_right_one (s : Interval) :
    surgerySection W a b (s,rightEndpoint)=
      ((pFlow (I := Fin p) (J := Fin q)) 1*rightUnitary (W (s,rightEndpoint))*(pFlow (I := Fin p) (J := Fin q)) 1)*(qFlow (I := Fin p) (J := Fin q)) 1*(qFlow (I := Fin p) (J := Fin q)) (a s) := by
  change surgery (pFlow (I := Fin p) (J := Fin q)) (qFlow (I := Fin p) (J := Fin q)) _ _ _ _ _ _ _=_
  rw [ha1,hb1]
  exact surgery_right_one (pFlow (I := Fin p) (J := Fin q)) (qFlow (I := Fin p) (J := Fin q)) flows_commute _ _ _ _

lemma q_right_mem (w : unitary (TensorMat p q)) :
    (((qFlow (I := Fin p) (J := Fin q)) 1*rightUnitary w*(qFlow (I := Fin p) (J := Fin q)) 1 : unitary (MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q)))) : (MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q))))∈fiberAlgebra (MatrixTensor.right (I := Fin p) (J := Fin q)).range (MatrixTensor.left (I := Fin p) (J := Fin q)).range := by
  change ((qFlow (I := Fin p) (J := Fin q)) 1:(MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q))))*MatrixTensor.right (w:(TensorMat p q))*((qFlow (I := Fin p) (J := Fin q)) 1:(MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q))))∈_
  simp only [qFlow_one]
  simpa only [unitaryConjugation,StarAlgHom.coe_mk,partialQ_star] using partialQ_conjugate_right_mem (w:(TensorMat p q))
lemma p_right_mem (w : unitary (TensorMat p q)) :
    (((pFlow (I := Fin p) (J := Fin q)) 1*rightUnitary w*(pFlow (I := Fin p) (J := Fin q)) 1 : unitary (MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q)))) : (MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q))))∈fiberAlgebra (MatrixTensor.left (I := Fin p) (J := Fin q)).range (MatrixTensor.right (I := Fin p) (J := Fin q)).range := by
  change ((pFlow (I := Fin p) (J := Fin q)) 1:(MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q))))*MatrixTensor.right (w:(TensorMat p q))*((pFlow (I := Fin p) (J := Fin q)) 1:(MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q))))∈_
  simp only [pFlow_one]
  simpa only [unitaryConjugation,StarAlgHom.coe_mk,partialP_star] using partialP_conjugate_right_mem (w:(TensorMat p q))

include ha0 ha1 hb0 hb1 hW0 hW1 in

lemma surgerySection_mem (s t : Interval) :
    (surgerySection W a b (s,t):(MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q))))∈fiberAlgebra (dropFiber p q s) (dropFiber p q t) := by
  have hP (r : ℝ) := pFlow_mem (I := Fin p) (J := Fin q) r
  have hQ (r : ℝ) := qFlow_mem (I := Fin p) (J := Fin q) r
  by_cases hs0 : s=leftEndpoint
  · subst s
    rw [surgerySection_left_zero W a b ha0 hb0 hW0]
    rw [dropFiber_zero,leftAmplification_eq]
    by_cases ht0 : t=leftEndpoint
    · subst t
      rw [hb0,hW0,rightUnitary_one,(pFlow (I := Fin p) (J := Fin q)).map_zero,one_mul,one_mul,
        dropFiber_zero,leftAmplification_eq]
      exact hP 1
    · by_cases ht1 : t=rightEndpoint
      · subst t
        rw [hb1,dropFiber_one,rightAmplification_eq]
        exact p_right_mem _
      · rw [dropFiber,ite_eq_right ht0,ite_eq_right ht1]
        apply mul_mem
        · apply mul_mem
          · exact fiberAlgebra_mono le_rfl le_top (hP _)
          · exact right_mem_fiber (MatrixTensor.left (I := Fin p) (J := Fin q)).range ⊤ (by trivial)
        · exact fiberAlgebra_mono le_rfl le_top (hP _)
  · by_cases hs1 : s=rightEndpoint
    · subst s
      rw [surgerySection_left_one W a b ha1 hb1 hW1]
      rw [dropFiber_one,rightAmplification_eq]
      by_cases ht0 : t=leftEndpoint
      · subst t
        rw [ha0,dropFiber_zero,leftAmplification_eq]
        exact q_right_mem _
      · by_cases ht1 : t=rightEndpoint
        · subst t
          rw [ha1,hW1,rightUnitary_one,(qFlow (I := Fin p) (J := Fin q)).map_zero,one_mul,one_mul,
            dropFiber_one,rightAmplification_eq]
          exact hQ 1
        · rw [dropFiber,ite_eq_right ht0,ite_eq_right ht1]
          apply mul_mem
          · apply mul_mem
            · exact fiberAlgebra_mono le_rfl le_top (hQ _)
            · exact right_mem_fiber (MatrixTensor.right (I := Fin p) (J := Fin q)).range ⊤ (by trivial)
          · exact fiberAlgebra_mono le_rfl le_top (hQ _)
    · rw [dropFiber,ite_eq_right hs0,ite_eq_right hs1]
      by_cases ht0 : t=leftEndpoint
      · subst t
        rw [surgerySection_right_zero W a b ha0 hb0,
          dropFiber_zero,leftAmplification_eq]
        apply mul_mem
        · apply mul_mem
          · exact fiberAlgebra_mono le_top le_rfl (q_right_mem _)
          · exact fiberAlgebra_mono le_top le_rfl (hP _)
        · exact fiberAlgebra_mono le_top le_rfl (hP _)
      · by_cases ht1 : t=rightEndpoint
        · subst t
          rw [surgerySection_right_one W a b ha1 hb1,
            dropFiber_one,rightAmplification_eq]
          apply mul_mem
          · apply mul_mem
            · exact fiberAlgebra_mono le_top le_rfl (p_right_mem _)
            · exact fiberAlgebra_mono le_top le_rfl (hQ _)
          · exact fiberAlgebra_mono le_top le_rfl (hQ _)
        · rw [dropFiber,ite_eq_right ht0,ite_eq_right ht1,fiberAlgebra_top_top]
          trivial

def squareUnitary (U : C(Interval×Interval,unitary (MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q)))))
    (hU : ∀ s t,(U (s,t):(MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q))))∈fiberAlgebra (dropFiber p q s) (dropFiber p q t)) :
    unitary (Square p q p q) :=
  ⟨⟨⟨fun z => (U z:(MatrixTensor.Mat (MatrixTensor.Four (Fin p) (Fin q)))),continuous_subtype_val.comp U.continuous⟩,hU⟩,by
    constructor
    · apply Subtype.ext
      apply ContinuousMap.ext
      intro z
      exact (U z).property.1
    · apply Subtype.ext
      apply ContinuousMap.ext
      intro z
      exact (U z).property.2⟩

def surgeryUnitary : unitary (Square p q p q) :=
  squareUnitary (surgerySection W a b) (surgerySection_mem W a b ha0 ha1 hb0 hb1 hW0 hW1)

end JiangSuConstruction

end

end OAI
