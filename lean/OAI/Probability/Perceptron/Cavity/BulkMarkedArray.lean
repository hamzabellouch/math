import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkAnnealedTangent
import OAI.Probability.Perceptron.Cavity.BulkPairLaw
import OAI.Probability.Perceptron.Interpolation.AnnealedMarkedReplica

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction ContDiff

lemma bulkB_measurable (N M : ℕ) (f : Jet3) :
    Measurable (fun p : BulkDisorder N M×(NormalizedSpin N×NormalizedSpin N) =>
      bulkB N M f p.1.1 p.2.1 p.2.2) := by
  unfold bulkB
  fun_prop

lemma bulkB_pairAverage (n M : ℕ) (f : Jet3) (a : BulkDisorder (n+1) M)
    (x : Fin 2→NormalizedSpin (n+1)) :
    bulkB (n+1) M f a.1 (x 0) (x 1)=bulkPairAverage n M f.d1 a x := by
  simp only [bulkB,bulkPairAverage,pairFieldMark,Fin.prod_univ_two,bulkPatternFields]

lemma bulkB_symm (N M : ℕ) (f : Jet3) (a : Fin M→Fin N→ℝ) (x y : NormalizedSpin N) :
    bulkB N M f a x y=bulkB N M f a y x := by
  unfold bulkB
  simp_rw [mul_comm (f.d1 _) (f.d1 _)]

def bulkMarkedEntry (n M : ℕ) (f : Jet3) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K) (a : BulkDisorder (n+1) M)
    (x y : NormalizedSpin (n+1)) : BulkPairRange K :=
  (bulkOverlap x y,⟨bulkB (n+1) M f a.1 x y,abs_le.mp ((bulkB_bound _ _ _ _ _ _).trans hK)⟩)

def bulkMarkedArray (n M : ℕ) (f : Jet3) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K)
    (p : BulkDisorder (n+1) M×(ℕ→NormalizedSpin (n+1))) : CompactArray (BulkPairRange K) :=
  fun i j => bulkMarkedEntry n M f K hK p.1 (p.2 i) (p.2 j)

lemma bulkMarkedArray_measurable (n M : ℕ) (f : Jet3) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K) : Measurable (bulkMarkedArray n M f K hK) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  have hm : Measurable (fun p : BulkDisorder (n+1) M×(ℕ→NormalizedSpin (n+1)) => (p.2 i,p.2 j)) := by fun_prop
  exact ((bulkOverlap_measurable _).comp hm).prodMk
    (((bulkB_measurable _ _ _).comp (measurable_fst.prodMk hm)).subtype_mk)

def bulkGibbsHamiltonian (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    BulkDisorder (n+1) M→NormalizedSpin (n+1)→ℝ :=
  fun a => bulkHamiltonian (n+1) M f v a.1 a.2

lemma bulkGibbsHamiltonian_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    Measurable (Function.uncurry (bulkGibbsHamiltonian n M f v)) :=
  (bulkHamiltonian_continuous (n+1) M f v).measurable

def bulkMarkedArrayLaw (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K) : ProbabilityMeasure (CompactArray (BulkPairRange K)) :=
  ⟨(annealedInfiniteReplicaMeasure (bulkSpinKernel n M) (bulkDisorderLaw (n+1) M)
      (bulkGibbsHamiltonian n M f.f v) (bulkGibbsHamiltonian_measurable n M f.f v)).map
        (bulkMarkedArray n M f K hK),
    (Measure.isProbabilityMeasure_map_iff (bulkMarkedArray_measurable _ _ _ _ _).aemeasurable).2 inferInstance⟩

lemma bulkMarkedArray_block (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K) (r : ℕ) (F : CompactBlock (BulkPairRange K) r→ᵇℝ) :
    (∫ Q,F (compactBlock r Q) ∂(bulkMarkedArrayLaw n M f v K hK : Measure _))=
      bulkReplicaMean n M f.f v r (fun a x => F (fun i j => bulkMarkedEntry n M f K hK a (x i) (x j))) := by
  change (∫ Q,F (compactBlock r Q) ∂Measure.map (bulkMarkedArray n M f K hK)
    (annealedInfiniteReplicaMeasure (bulkSpinKernel n M) (bulkDisorderLaw (n+1) M)
      (bulkGibbsHamiltonian n M f.f v) (bulkGibbsHamiltonian_measurable n M f.f v)))=_
  have hm : Measurable (fun Q : CompactArray (BulkPairRange K) => F (compactBlock r Q)) :=
    F.measurable.comp (compactBlock_continuous r).measurable
  rw [integral_map (bulkMarkedArray_measurable n M f K hK).aemeasurable hm.aestronglyMeasurable]
  unfold bulkReplicaMean
  apply annealedInfiniteReplica_marked_prefix (bulkSpinKernel n M) (bulkDisorderLaw (n+1) M)
    (bulkGibbsHamiltonian n M f.f v) (bulkGibbsHamiltonian_measurable n M f.f v)
    (ae_of_all _ (bulkHamiltonian_exp_integrable n M f.f v)) r
    (G := fun a x => F (fun i j => bulkMarkedEntry n M f K hK a (x i) (x j)))
  · apply F.measurable.comp
    refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
    have hm : Measurable (fun p : BulkDisorder (n+1) M×(Fin r→NormalizedSpin (n+1)) => (p.2 i,p.2 j)) := by fun_prop
    exact ((bulkOverlap_measurable _).comp hm).prodMk
      (((bulkB_measurable _ _ _).comp (measurable_fst.prodMk hm)).subtype_mk)
  · intro a x
    exact F.norm_coe_le_norm _

lemma bulkMarkedArray_exchangeable (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K) (e : Equiv.Perm ℕ) :
    MeasurePreserving (compactRelabel (K:=BulkPairRange K) e)
      (bulkMarkedArrayLaw n M f v K hK : Measure _) (bulkMarkedArrayLaw n M f v K hK : Measure _) := by
  have hr := annealedInfiniteReplica_reindex (bulkSpinKernel n M) (bulkDisorderLaw (n+1) M)
    (bulkGibbsHamiltonian n M f.f v) (bulkGibbsHamiltonian_measurable n M f.f v) e
  have hm := bulkMarkedArray_measurable n M f K hK
  refine ⟨(compactRelabel_continuous e).measurable,?_⟩
  change Measure.map _ (Measure.map (bulkMarkedArray n M f K hK) _)=_
  rw [Measure.map_map (compactRelabel_continuous e).measurable hm]
  change Measure.map ((bulkMarkedArray n M f K hK) ∘
    (fun a : BulkDisorder (n+1) M×(ℕ→NormalizedSpin (n+1)) => (a.1,fun i => a.2 (e i)))) _=_
  rw [←Measure.map_map hm hr.measurable,hr.map_eq]
  rfl

lemma bulkMarkedArray_overlap (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K) :
    compactMapLaw Prod.fst continuous_fst (bulkMarkedArrayLaw n M f v K hK)=bulkGibbsArrayLaw n M f.f v := by
  apply Subtype.ext
  change Measure.map (fun Q : CompactArray (BulkPairRange K) => fun i j => (Q i j).1)
    (Measure.map (bulkMarkedArray n M f K hK) _) = _
  rw [Measure.map_map (by fun_prop) (bulkMarkedArray_measurable _ _ _ _ _)]
  rfl

lemma bulkMarkedArray_pair (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K) :
    (bulkMarkedArrayLaw n M f v K hK).map (fun Q => Q 1 0)=
      bulkPairLaw n M f.f f.d1 v K hK := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  rw [ProbabilityMeasure.toMeasure_map,integral_map (by fun_prop : Measurable (fun Q : CompactArray (BulkPairRange K)=>Q 1 0)).aemeasurable F.continuous.aestronglyMeasurable,
    bulkPairLaw_integral]
  let T : CompactBlock (BulkPairRange K) 2→ᵇℝ := F.compContinuous ⟨fun Q=>Q 1 0,by fun_prop⟩
  have he := bulkMarkedArray_block n M f v K hK 2 T
  change (∫ Q : CompactArray (BulkPairRange K),F (Q 1 0) ∂(bulkMarkedArrayLaw n M f v K hK : Measure _))=_ at he
  rw [he]
  unfold bulkReplicaMean
  apply integral_congr_ae
  exact ae_of_all _ fun a => by
    apply congrArg (gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f.f v a.1 a.2) 2)
    funext x
    apply congrArg F
    change bulkMarkedEntry n M f K hK a (x 1) (x 0) = bulkCompactPair n M f.d1 K hK (a,x)
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact (bulkB_symm _ _ _ _ _ _).trans (bulkB_pairAverage _ _ _ a x)

def markedTangentR (K : ℝ) (G : ℝ→ᵇℝ) : CompactBlock (BulkPairRange K) 2→ᵇℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun Q => (Q 0 1).1.val*G (Q 0 1).1.val,by fun_prop⟩
def markedTangentPair (K : ℝ) (G : ℝ→ᵇℝ) : CompactBlock (BulkPairRange K) 2→ᵇℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun Q => G (Q 0 1).1.val*(Q 0 1).2.val*(1-(Q 0 1).1.val^2),by fun_prop⟩
def markedTangentTriple (K : ℝ) (G : ℝ→ᵇℝ) : CompactBlock (BulkPairRange K) 3→ᵇℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun Q => G (Q 1 2).1.val*(Q 1 0).2.val*((Q 2 0).1.val-(Q 1 2).1.val*(Q 1 0).1.val),by fun_prop⟩

lemma bulk_tangent_pair_sum (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (G : ℝ→ᵇℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K) :
    (∑ j : Fin M,bulkReplicaMean n M f.f v 2 (fun a => freshTangentPair (n+1) f G (WithLp.toLp 2 (a.1 j))))=
      (n+1:ℕ)*(∫ Q,markedTangentPair K G (compactBlock 2 Q) ∂(bulkMarkedArrayLaw n M f v K hK : Measure _)) := by
  have hm (j : Fin M) : Measurable (Function.uncurry (fun a : BulkDisorder (n+1) M => freshTangentPair (n+1) f G (WithLp.toLp 2 (a.1 j)))) := by
    have hc : Continuous (Function.uncurry (fun a : BulkDisorder (n+1) M => freshTangentPair (n+1) f G (WithLp.toLp 2 (a.1 j)))) := by
      unfold Function.uncurry freshTangentPair spinOverlap
      fun_prop
    exact hc.measurable
  have hs := bulkReplicaMean_sum n M 2 f.f v Finset.univ
    (fun j a => freshTangentPair (n+1) f G (WithLp.toLp 2 (a.1 j)))
    (fun j _ => hm j)
    (fun _ => 2*‖G‖*‖f.d1‖^2) (by intros; positivity)
    (fun j _ a x => freshTangentPair_bound _ _ _ _ x)
  rw [←hs,bulkMarkedArray_block,←bulkReplicaMean_const_mul]
  apply congrArg (bulkReplicaMean n M f.f v 2)
  funext a x
  change (∑ j : Fin M,G (spinOverlap (x 0) (x 1))*f.d1 (inner ℝ (x 0).val (WithLp.toLp 2 (a.1 j)))*
    f.d1 (inner ℝ (x 1).val (WithLp.toLp 2 (a.1 j)))*(1-spinOverlap (x 0) (x 1)^2))=
    ((n+1:ℕ):ℝ)*(G (spinOverlap (x 0) (x 1))*bulkB (n+1) M f a.1 (x 0) (x 1)*(1-spinOverlap (x 0) (x 1)^2))
  have he (z : NormalizedSpin (n+1)) (j : Fin M) : inner ℝ z.val (WithLp.toLp 2 (a.1 j))=∑ i,a.1 j i*z.val i := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct]
  simp_rw [he]
  unfold bulkB
  have hn : ((n+1:ℕ):ℝ)≠0 := by positivity
  simp_rw [mul_assoc (G _)]
  rw [←Finset.mul_sum,←Finset.sum_mul]
  field_simp

lemma bulk_tangent_triple_sum (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (G : ℝ→ᵇℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K) :
    (∑ j : Fin M,bulkReplicaMean n M f.f v 3 (fun a => freshTangentTriple (n+1) f G (WithLp.toLp 2 (a.1 j))))=
      (n+1:ℕ)*(∫ Q,markedTangentTriple K G (compactBlock 3 Q) ∂(bulkMarkedArrayLaw n M f v K hK : Measure _)) := by
  have hm (j : Fin M) : Measurable (Function.uncurry (fun a : BulkDisorder (n+1) M => freshTangentTriple (n+1) f G (WithLp.toLp 2 (a.1 j)))) := by
    have hc : Continuous (Function.uncurry (fun a : BulkDisorder (n+1) M => freshTangentTriple (n+1) f G (WithLp.toLp 2 (a.1 j)))) := by
      unfold Function.uncurry freshTangentTriple spinOverlap
      fun_prop
    exact hc.measurable
  have hs := bulkReplicaMean_sum n M 3 f.f v Finset.univ
    (fun j a => freshTangentTriple (n+1) f G (WithLp.toLp 2 (a.1 j)))
    (fun j _ => hm j)
    (fun _ => 2*‖G‖*‖f.d1‖^2) (by intros; positivity)
    (fun j _ a x => freshTangentTriple_bound _ _ _ _ x)
  rw [←hs,bulkMarkedArray_block,←bulkReplicaMean_const_mul]
  apply congrArg (bulkReplicaMean n M f.f v 3)
  funext a x
  change (∑ j : Fin M,G (spinOverlap (x 1) (x 2))*f.d1 (inner ℝ (x 1).val (WithLp.toLp 2 (a.1 j)))*
    f.d1 (inner ℝ (x 0).val (WithLp.toLp 2 (a.1 j)))*(spinOverlap (x 2) (x 0)-spinOverlap (x 1) (x 2)*spinOverlap (x 1) (x 0)))=
    ((n+1:ℕ):ℝ)*(G (spinOverlap (x 1) (x 2))*bulkB (n+1) M f a.1 (x 1) (x 0)*(spinOverlap (x 2) (x 0)-spinOverlap (x 1) (x 2)*spinOverlap (x 1) (x 0)))
  have he (z : NormalizedSpin (n+1)) (j : Fin M) : inner ℝ z.val (WithLp.toLp 2 (a.1 j))=∑ i,a.1 j i*z.val i := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct]
  simp_rw [he]
  unfold bulkB
  have hn : ((n+1:ℕ):ℝ)≠0 := by positivity
  simp_rw [mul_assoc (G _)]
  rw [←Finset.mul_sum,←Finset.sum_mul]
  field_simp

lemma bulk_marked_tangent_bound (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (G : ℝ→ᵇℝ)
    (hG : ContDiff ℝ 1 (G : ℝ→ℝ)) {C : ℝ} (hC : 0≤C) (hv : ∀ j,|v (j+1)|≤C)
    (K : ℝ) (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K)
    {D : ℝ} (hD : 0≤D) (hbD : ∀ r : CompactOverlap,|deriv (G : ℝ→ℝ) r.val*(1-r.val^2)|≤D) :
    |(∫ Q,markedTangentR K G (compactBlock 2 Q) ∂(bulkMarkedArrayLaw n M f v K hK : Measure _))-
        (∫ Q,markedTangentPair K G (compactBlock 2 Q) ∂(bulkMarkedArrayLaw n M f v K hK : Measure _))+
        2*(∫ Q,markedTangentTriple K G (compactBlock 3 Q) ∂(bulkMarkedArrayLaw n M f v K hK : Measure _))|≤
      (‖G‖+D+8*‖G‖*C^2*bulkScale (n+1)^2)/(n+1:ℕ) := by
  have ht := bulk_tangent_annealed n M f v G hG hC hv
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,bulk_tangent_pair_sum n M f v G K hK,bulk_tangent_triple_sum n M f v G K hK] at ht
  have hr := bulkMarkedArray_block n M f v K hK 2 (markedTangentR K G)
  change (∫ Q,markedTangentR K G (compactBlock 2 Q) ∂(bulkMarkedArrayLaw n M f v K hK : Measure _))=
    bulkReplicaMean n M f.f v 2 (fun _ x => spinOverlap (x 0) (x 1)*G (spinOverlap (x 0) (x 1))) at hr
  rw [←hr] at ht
  have hdb := bulkReplicaMean_bound n M 2 f.f v (fun _ => tangentDerivTest (n+1) G)
    ((tangentDerivTest_continuous (n+1) G hG).measurable.comp measurable_snd) hD (fun _ x => hbD (bulkOverlap (x 0) (x 1)))
  have hrb : |∫ Q,markedTangentR K G (compactBlock 2 Q) ∂(bulkMarkedArrayLaw n M f v K hK : Measure _)|≤‖G‖ := by
    have hb : ∀ Q : CompactArray (BulkPairRange K),‖markedTangentR K G (compactBlock 2 Q)‖≤‖G‖ := by
      intro Q
      change |(Q 0 1).1.val*G (Q 0 1).1.val|≤‖G‖
      rw [abs_mul]
      exact (mul_le_mul (abs_le.mpr (Q 0 1).1.property) (G.norm_coe_le_norm _) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)).trans (by simp)
    simpa [Real.norm_eq_abs,Measure.real] using norm_integral_le_of_norm_le_const (ae_of_all (bulkMarkedArrayLaw n M f v K hK : Measure _) hb)
  have hn : (0:ℝ)<(n+1:ℕ) := by positivity
  rw [le_div_iff₀ hn,←abs_of_pos hn,←abs_mul]
  have halg (X Y Z W : ℝ) : (X-Y+2*Z)*(n+1:ℕ)=X+W+((n:ℝ)*X-W-((n+1:ℕ)*Y-2*((n+1:ℕ)*Z))) := by push_cast; ring
  rw [halg]
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hrb hdb)) ht)

end SphericalPerceptronFreeEnergy
end

end OAI
