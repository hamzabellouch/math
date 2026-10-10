import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkRadialLimit

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction Matrix

section

variable {J E : Type*} [Fintype J] [DecidableEq J]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def cavityTestReplica (Ψ : EuclideanSpace ℝ J→ᵇℝ) (r : ℕ) :
    EuclideanSpace ℝ (J×Fin r)→ᵇℝ :=
  ∏ i : Fin r, Ψ.compContinuous ⟨fun z=>WithLp.toLp 2 (fun j=>z (j,i)),by fun_prop⟩

omit [Fintype J] [DecidableEq J] in
lemma cavityTestReplica_apply (Ψ : EuclideanSpace ℝ J→ᵇℝ) (r : ℕ)
    (z : EuclideanSpace ℝ (J×Fin r)) :
    cavityTestReplica Ψ r z=∏ i : Fin r, Ψ (WithLp.toLp 2 (fun j=>z (j,i))) := by
  simp [cavityTestReplica]

theorem cavity_marked_moment {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (v : S→J→E)
    (hv : Measurable v) (W : S→ℝ) (hW : Measurable W) {C : ℝ}
    (hWB : ∀ s,|W s|≤C) (Ψ : EuclideanSpace ℝ J→ᵇℝ) (r : ℕ) :
    (∫ y,(∫ s,Real.exp (W s)*Ψ (gaussianRows (v s) y) ∂μ)^r ∂stdGaussian E)=
      ∫ xs : Fin r→S,(∏ i,Real.exp (W (xs i)))*
        cavityMatrixKernel (cavityTestReplica Ψ r)
          (Matrix.gram ℝ (fun p : J×Fin r=>v (xs p.2) p.1))
        ∂Measure.pi (fun _=>μ) := by
  let P:=Measure.pi (fun _ : Fin r=>μ)
  let F : E×(Fin r→S)→ℝ:=fun p=>
    ∏ i : Fin r,Real.exp (W (p.2 i))*Ψ (gaussianRows (v (p.2 i)) p.1)
  have hm : Measurable F := by
    apply Finset.measurable_prod
    intro i hi
    have hvi : Measurable (fun p : E×(Fin r→S)=>v (p.2 i)) :=
      hv.comp ((measurable_pi_apply i).comp measurable_snd)
    have hwi : Measurable (fun p : E×(Fin r→S)=>W (p.2 i)) :=
      hW.comp ((measurable_pi_apply i).comp measurable_snd)
    apply hwi.exp.mul
    apply Ψ.measurable.comp
    change Measurable (fun p : E×(Fin r→S)=>WithLp.toLp 2
      (fun j=>inner ℝ (v (p.2 i) j) p.1))
    fun_prop
  have hb p : ‖F p‖≤(Real.exp C*‖Ψ‖)^r := by
    simp only [F,norm_prod,norm_mul]
    calc
      _ ≤ ∏ i : Fin r, Real.exp C * ‖Ψ‖ := by
        apply Finset.prod_le_prod₀ (fun _ _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))
        intro i hi
        apply mul_le_mul _ (Ψ.norm_coe_le_norm _) (norm_nonneg _) (Real.exp_pos C).le
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (abs_le.mp (hWB _)).2
      _ = _ := by simp
  have hi : Integrable F ((stdGaussian E).prod P) :=
    Integrable.of_bound hm.aestronglyMeasurable _ (ae_of_all _ hb)
  calc
    _=∫ y,∫ xs : Fin r→S,F (y,xs) ∂P ∂stdGaussian E := by
      apply integral_congr_ae
      filter_upwards [] with y
      simpa only [F,P,Fintype.card_fin] using
        (integral_fintype_prod_eq_pow (ι:=Fin r)
          (fun s=>Real.exp (W s)*Ψ (gaussianRows (v s) y)) (μ:=μ)).symm
    _=∫ xs : Fin r→S,∫ y,F (y,xs) ∂stdGaussian E ∂P := integral_integral_swap hi
    _=_ := by
      apply integral_congr_ae
      filter_upwards [] with xs
      have he y : F (y,xs)=(∏ i,Real.exp (W (xs i)))*
          cavityTestReplica Ψ r (gaussianRows (fun p : J×Fin r=>v (xs p.2) p.1) y) := by
        simp only [F,Finset.prod_mul_distrib,cavityTestReplica_apply]
        congr 1
      simp_rw [he]
      rw [integral_const_mul,cavityMatrixKernel_posSemidef _ _ (Matrix.posSemidef_gram ℝ _),
        ←gaussianRows_map_stdGaussian,
        integral_map (gaussianRows _).continuous.measurable.aemeasurable
          (cavityTestReplica Ψ r).continuous.aestronglyMeasurable]

def cavitySingleTest (n d : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ) :
    EuclideanSpace ℝ (Fin (n+1)⊕Fin d)→ᵇℝ :=
  (cappedSphericalExp n (Real.sqrt (n+1:ℕ)) Λ hΛ).compContinuous
      ⟨fun z=>WithLp.toLp 2 (fun i=>z (Sum.inl i)),by fun_prop⟩ *
    ∏ i : Fin d,(expBCF 1 f).compContinuous ⟨fun z=>z (Sum.inr i),by fun_prop⟩

lemma cavitySingleTest_apply (n d : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (z : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) :
    cavitySingleTest n d f Λ hΛ z =
      min (sphericalExp n (WithLp.toLp 2 (fun i=>z (Sum.inl i))) (Real.sqrt (n+1:ℕ))) Λ *
        ∏ i : Fin d,Real.exp (f (z (Sum.inr i))) := by
  simp [cavitySingleTest,cappedSphericalExp,expBCF]

lemma cavitySingleTest_replica (n d r : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ) :
    cavityTestReplica (cavitySingleTest n d f Λ hΛ) r=cavityReplicaTest n d r f Λ hΛ := by
  ext z
  simp only [cavityTestReplica_apply,cavitySingleTest_apply,cavityReplicaTest_apply]

end

lemma posSemidef_independent_blocks {J I : Type*} [Fintype J] [Fintype I]
    [DecidableEq J] [DecidableEq I] (C : J → I → I → ℝ)
    (hC : ∀ j,(Matrix.of (C j)).PosSemidef) :
    (Matrix.of (fun (p q : J×I) => if p.1=q.1 then C p.1 p.2 q.2 else 0)).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · rw [Matrix.IsHermitian.ext_iff]
    intro p q
    change (if q.1=p.1 then C q.1 q.2 p.2 else 0) = (if p.1=q.1 then C p.1 p.2 q.2 else 0)
    by_cases h : p.1=q.1
    · simp only [h]
      exact (Matrix.IsHermitian.ext_iff.mp (hC q.1).isHermitian p.2 q.2)
    · simp [h,Ne.symm h]
  · intro x
    have he : star x ⬝ᵥ ((fun (p q : J×I) => if p.1=q.1 then C p.1 p.2 q.2 else 0) *ᵥ x) =
        ∑ j : J, star (fun i : I=>x (j,i)) ⬝ᵥ (C j *ᵥ (fun i=>x (j,i))) := by
      simp [dotProduct,Matrix.mulVec,Fintype.sum_prod_type,Finset.mul_sum]
    change 0 ≤ star x ⬝ᵥ ((fun (p q : J×I) => if p.1=q.1 then C p.1 p.2 q.2 else 0) *ᵥ x)
    rw [he]
    exact Finset.sum_nonneg fun j _ => (Matrix.posSemidef_iff_dotProduct_mulVec.mp (hC j)).2 _

lemma cavityBlockCovariance_posSemidef (n d r : ℕ) {K : ℝ}
    (Q : CompactArray (BulkPairRange K))
    (hB : Matrix.PosSemidef (fun i j : Fin r=>(Q i j).2.val))
    (hR : Matrix.PosSemidef (fun i j : Fin r=>(Q i j).1.val)) :
    (cavityBlockCovariance n d r Q).PosSemidef := by
  let C : (Fin (n+1) ⊕ Fin d) → Fin r → Fin r → ℝ :=
    fun c i j => Sum.elim (fun _ => (Q i j).2.val) (fun _ => (Q i j).1.val) c
  have hC : ∀ c,Matrix.PosSemidef (C c) := by
    intro c
    cases c
    · exact hB
    · exact hR
  exact posSemidef_independent_blocks C hC

lemma bulkMarkedEntry_B_posSemidef (n M : ℕ) (f : Jet3) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K) (a : BulkDisorder (n+1) M)
    (r : ℕ) (x : Fin r→NormalizedSpin (n+1)) :
    Matrix.PosSemidef (fun i j => (bulkMarkedEntry n M f K hK a (x i) (x j)).2.val) := by
  let v : Fin r→Spin M:=fun i=> WithLp.toLp 2 (fun t=>f.d1 (∑ j,a.1 t j*(x i).val j))
  have h:= (Matrix.posSemidef_gram ℝ v).smul (by positivity : (0:ℝ)≤((n+1:ℕ):ℝ)⁻¹)
  have he : (fun i j => (bulkMarkedEntry n M f K hK a (x i) (x j)).2.val : Matrix (Fin r) (Fin r) ℝ)=
      ((n+1:ℕ):ℝ)⁻¹ • Matrix.gram ℝ v := by
    ext i j
    simp [bulkMarkedEntry,bulkB,v,Matrix.gram,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
      mul_comm]
  rw [he]
  exact h

lemma bulkMarkedEntry_R_posSemidef (n M : ℕ) (f : Jet3) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K) (a : BulkDisorder (n+1) M)
    (r : ℕ) (x : Fin r→NormalizedSpin (n+1)) :
    Matrix.PosSemidef (fun i j => (bulkMarkedEntry n M f K hK a (x i) (x j)).1.val) := by
  exact Matrix.posSemidef_gram ℝ (fun i=> (x i).val)

lemma cavityArrayKernel_actual (n d r m M : ℕ) (g : Jet3) (Λ : ℝ) (hΛ : 1≤Λ)
    (K : ℝ) (hK : M/(m+1:ℕ)*‖g.d1‖^2≤K)
    (p : BulkDisorder (m+1) M×(ℕ→NormalizedSpin (m+1))) :
    cavityArrayKernel n d r g.f Λ hΛ K (bulkMarkedArray m M g K hK p)=
      ∫ z,cavityReplicaTest n d r g.f Λ hΛ z ∂multivariateGaussian 0
        (cavityBlockCovariance n d r (bulkMarkedArray m M g K hK p)) := by
  apply cavityMatrixKernel_posSemidef
  apply cavityBlockCovariance_posSemidef
  · exact bulkMarkedEntry_B_posSemidef m M g K hK p.1 r (fun i=>p.2 i)
  · exact bulkMarkedEntry_R_posSemidef m M g K hK p.1 r (fun i=>p.2 i)

end SphericalPerceptronFreeEnergy
end

end OAI
