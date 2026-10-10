import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityLabelLimit
import OAI.Probability.Perceptron.Cavity.CavityCountableIsotropic

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavity_residual_square_integrable {S G T : Type*}
    [MeasurableSpace S] [MeasurableSpace G] [MeasurableSpace T]
    (μ : Measure S) (P : Measure G) (Q : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : G×(S×T)→ℝ) (hF : Measurable F) (K : ℝ)
    (hL2 : ∀ x, MemLp (fun p : G×T=>F (p.1,(x,p.2))) 2 (P.prod Q))
    (h2 : ∀ x, (∫ p : G×T,F (p.1,(x,p.2))^2 ∂P.prod Q)≤K) :
    Integrable (fun p=>F p^2) (P.prod (μ.prod Q)) ∧
      (∫ g,∫ x,F (g,x)^2 ∂μ.prod Q ∂P)≤K := by
  let H : S×(G×T)→ℝ := fun p=>F (p.2.1,(p.1,p.2.2))^2
  have hm : Measurable H := (hF.comp
    (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd))).pow_const 2
  have hi : Integrable H (μ.prod (P.prod Q)) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ fun x=>(memLp_two_iff_integrable_sq (hL2 x).aestronglyMeasurable).mp (hL2 x)
    · apply Integrable.of_bound (hm.norm.stronglyMeasurable.integral_prod_right).aestronglyMeasurable K
      filter_upwards [] with x
      have he : (∫ p : G×T,‖H (x,p)‖ ∂P.prod Q)=(∫ p : G×T,F (p.1,(x,p.2))^2 ∂P.prod Q) := by
        simp only [H,Real.norm_eq_abs,abs_sq]
      rw [he,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun _=>sq_nonneg _)]
      exact h2 x
  have hp : MeasurePreserving (fun p : G×(S×T)=>(p.2.1,(p.1,p.2.2)))
      (P.prod (μ.prod Q)) (μ.prod (P.prod Q)) :=
    (measurePreserving_prodAssoc μ P Q).comp
      ((Measure.measurePreserving_swap.prod (MeasurePreserving.id Q)).comp
        ((measurePreserving_prodAssoc P μ Q).symm _))
  have hi' : Integrable (fun p=>F p^2) (P.prod (μ.prod Q)) :=
    (hp.integrable_comp hm.aestronglyMeasurable).mpr hi
  refine ⟨hi',?_⟩
  rw [←integral_prod _ hi']
  have he : (∫ p : G×(S×T),F p^2 ∂P.prod (μ.prod Q)) =
      ∫ p,H p ∂μ.prod (P.prod Q) := by
    rw [←hp.map_eq,integral_map hp.measurable.aemeasurable hm.aestronglyMeasurable]
  rw [he,integral_prod _ hi]
  calc
    _ ≤ ∫ _ : S,K ∂μ := integral_mono hi.integral_prod_left (integrable_const K) h2
    _ = K := by simp

lemma cavity_expected_cap_residual {S G T : Type*}
    [MeasurableSpace S] [MeasurableSpace G] [MeasurableSpace T]
    (μ : Measure S) (P : Measure G) (Q : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (W F : G×(S×T)→ℝ) (hW : Measurable W) (hF : Measurable F) {C Λ K : ℝ}
    (hWC : ∀ p,|W p|≤C) (hF1 : ∀ p,1≤F p) (hΛ : 1≤Λ)
    (hL2 : ∀ x, MemLp (fun p : G×T=>F (p.1,(x,p.2))) 2 (P.prod Q))
    (h2 : ∀ x, (∫ p : G×T,F (p.1,(x,p.2))^2 ∂P.prod Q)≤K) :
    let D:=fun g=>Real.log (∫ x,Real.exp (W (g,x))*F (g,x) ∂μ.prod Q)-
      Real.log (∫ x,Real.exp (W (g,x))*min (F (g,x)) Λ ∂μ.prod Q)
    Integrable D P ∧ 0≤∫ g,D g ∂P ∧
      (∫ g,D g ∂P)≤Real.exp (2*C)/Λ*K := by
  have h := cavity_residual_square_integrable μ P Q F hF K hL2 h2
  exact cavity_expected_cap_integrated (μ.prod Q) P W F hW hF hWC hF1 hΛ h.1 h.2



def cavityLabelCompletedMark (n d k : ℕ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ)
    (p : (ℕ→ℝ)×(IndexedLeaf k×EuclideanSpace ℝ (Fin (n+1)⊕Fin d))) :
    EuclideanSpace ℝ (Fin (n+1)⊕Fin d) :=
  WithLp.toLp 2 (fun i=>cavityCountableField (cavityLabelRow q) (cavityLabelLength k) p.1 p.2.1 i+σ i*p.2.2 i)

lemma cavityLabelCompletedMark_measurable (n d k : ℕ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ) :
    Measurable (cavityLabelCompletedMark n d k σ q) := by
  have hf : Measurable (fun p : (ℕ→ℝ)×IndexedLeaf k=>
      cavityCountableField (cavityLabelRow q) (cavityLabelLength k) p.1 p.2) :=
    cavityCountableField_measurable (cavityLabelRow q) (cavityLabelLength k)
      (cavityLabelRow_measurable q) (cavityLabelLength_measurable k)
  have hp : Measurable (fun p : (ℕ→ℝ)×(IndexedLeaf k×EuclideanSpace ℝ (Fin (n+1)⊕Fin d))=>
      (p.1,p.2.1)) := measurable_fst.prodMk measurable_snd.fst
  have h := hf.comp hp
  unfold cavityLabelCompletedMark
  apply (MeasurableEquiv.toLp 2 _).measurable.comp
  exact Measurable.of_eval fun coordinate=> ((measurable_pi_apply coordinate).comp
    ((MeasurableEquiv.toLp 2 _).symm.measurable.comp h)).add
      (measurable_const.mul ((measurable_pi_apply coordinate).comp
        ((MeasurableEquiv.toLp 2 _).symm.measurable.comp measurable_snd.snd)))

def cavityLabelSpherical (n d k : ℕ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ) :=
  fun p=>sphericalExp n ((gaussianSumSplit (cavityLabelCompletedMark n d k σ q p)).1) (Real.sqrt (n+1:ℕ))

def cavityLabelWeight (n d k : ℕ) (f : ℝ→ᵇℝ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ) :=
  fun p=>∑ i : Fin d,f (cavityLabelCompletedMark n d k σ q p (Sum.inr i))

lemma cavityLabelSpherical_measurable (n d k : ℕ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ) :
    Measurable (cavityLabelSpherical n d k σ q) :=
  (sphericalExp_continuous n _).measurable.comp
    (gaussianSumSplit_measurable.fst.comp (cavityLabelCompletedMark_measurable n d k σ q))

lemma cavityLabelWeight_measurable (n d k : ℕ) (f : ℝ→ᵇℝ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ) :
    Measurable (cavityLabelWeight n d k f σ q) := by
  apply Finset.measurable_sum
  intro i hi
  exact f.measurable.comp ((measurable_pi_apply (Sum.inr i)).comp
    ((MeasurableEquiv.toLp 2 _).symm.measurable.comp (cavityLabelCompletedMark_measurable n d k σ q)))

lemma cavityLabelWeight_bound (n d k : ℕ) (f : ℝ→ᵇℝ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ) (p) :
    |cavityLabelWeight n d k f σ q p|≤(d:ℝ)*‖f‖ := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i : Fin d,‖f‖ := Finset.sum_le_sum fun _ _=>f.norm_coe_le_norm _
    _ = _ := by simp

lemma cavityLabelSpherical_one (n d k : ℕ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ) (p) :
    1≤cavityLabelSpherical n d k σ q p := one_le_sphericalExp n _ _

lemma cavityLabelSpherical_second (n d : ℕ) {K : ℝ} {k : ℕ}
    (p : Fin (k+1)→BulkPairRange K) (D : BulkPairRange K)
    (hp0 : ∀ i,0≤cavityPairProfile n d p 0 i)
    (hpm : ∀ i,Monotone (fun l=>cavityPairProfile n d p l i))
    (hpD : ∀ i,cavityPairProfile n d p (Fin.last k) i≤cavityPairDiagonal n d D i)
    (x : IndexedLeaf k) :
    let σ:=fun i=>Real.sqrt (cavityPairDiagonal n d D i-cavityPairProfile n d p (Fin.last k) i)
    let F:=cavityLabelSpherical n d k σ (cavityPairProfile n d p)
    let P:=countableGaussianLaw.prod (stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))
    MemLp (fun y=>F (y.1,(x,y.2))) 2 P ∧
      (∫ y,F (y.1,(x,y.2))^2 ∂P)≤Real.exp (2*(n+1:ℕ)*D.2.val) := by
  let V:=cavityCompletedCountableVector n (cavityLabelRow (cavityPairProfile n d p))
    (cavityLabelLength k) (fun _=>Real.sqrt (D.2.val-(p (Fin.last k)).2.val))
    (fun i=>(x,Sum.inl i))
  let R:=Real.sqrt (n+1:ℕ)
  have h := cavityLabelVector_second_moment n d p D hp0 hpm hpD x R
  let T : (ℕ→ℝ)×EuclideanSpace ℝ (Fin (n+1)⊕Fin d)→(ℕ→ℝ)×Spin (n+1) :=
    fun y=>(y.1,(gaussianSumSplit y.2).1)
  have hp : MeasurePreserving T
      (countableGaussianLaw.prod (stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d))))
      (countableGaussianLaw.prod (stdGaussian (Spin (n+1)))) :=
    (MeasurePreserving.id _).prod (measurePreserving_fst.comp gaussianSumSplit_preserving)
  change MemLp ((fun y=>sphericalExp n (V y) R) ∘ T) 2 _ ∧ _
  refine ⟨h.1.comp_measurePreserving hp,?_⟩
  have hm : Measurable (fun y=>sphericalExp n (V y) R^2) :=
    ((sphericalExp_continuous n R).measurable.comp
      (cavityCompletedCountableVector_measurable n _ _ _ _)).pow_const 2
  change (∫ y,(sphericalExp n (V (T y)) R)^2 ∂_)≤_
  rw [←integral_map hp.measurable.aemeasurable hm.aestronglyMeasurable,hp.map_eq]
  simpa only [R,Real.sq_sqrt (by positivity : 0≤((n+1:ℕ):ℝ))] using h.2

theorem cavityLabel_cap_error (n d : ℕ) {K : ℝ} {k : ℕ}
    (p : Fin (k+1)→BulkPairRange K) (D : BulkPairRange K)
    (hp0 : ∀ i,0≤cavityPairProfile n d p 0 i)
    (hpm : ∀ i,Monotone (fun l=>cavityPairProfile n d p l i))
    (hpD : ∀ i,cavityPairProfile n d p (Fin.last k) i≤cavityPairDiagonal n d D i)
    (f : ℝ→ᵇℝ) (b : IndexedCascadeBase k) {Λ : ℝ} (hΛ : 1≤Λ) :
    let σ:=fun i=>Real.sqrt (cavityPairDiagonal n d D i-cavityPairProfile n d p (Fin.last k) i)
    let F:=cavityLabelSpherical n d k σ (cavityPairProfile n d p)
    let W:=cavityLabelWeight n d k f σ (cavityPairProfile n d p)
    let Q:=(indexedLeafProbability k b).prod (stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))
    let E:=fun g=>Real.log (∫ x,Real.exp (W (g,x))*F (g,x) ∂Q)-
      Real.log (∫ x,Real.exp (W (g,x))*min (F (g,x)) Λ ∂Q)
    Integrable E countableGaussianLaw ∧ 0≤∫ g,E g ∂countableGaussianLaw ∧
      (∫ g,E g ∂countableGaussianLaw)≤
        Real.exp (2*((d:ℝ)*‖f‖))/Λ*Real.exp (2*(n+1:ℕ)*D.2.val) := by
  dsimp only
  exact cavity_expected_cap_residual (indexedLeafProbability k b) countableGaussianLaw
    (stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d))) _ _
    (cavityLabelWeight_measurable n d k f _ _) (cavityLabelSpherical_measurable n d k _ _)
    (cavityLabelWeight_bound n d k f _ _) (cavityLabelSpherical_one n d k _ _) hΛ
    (fun x=>(cavityLabelSpherical_second n d p D hp0 hpm hpD x).1)
    (fun x=>(cavityLabelSpherical_second n d p D hp0 hpm hpD x).2)
end SphericalPerceptronFreeEnergy

end

end OAI
