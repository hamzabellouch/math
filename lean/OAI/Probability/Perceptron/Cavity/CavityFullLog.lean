import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityLabelAnnealed
import OAI.Probability.Perceptron.Cavity.CavityResidualFormula
import OAI.Probability.Perceptron.Variational.IndexedFractionalLog

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction ENNReal
namespace SphericalPerceptronFreeEnergy

lemma cavityLabel_full_integrable_ae (n d : ℕ) {K : ℝ} {k : ℕ}
    (p : Fin (k+1)→BulkPairRange K) (D : BulkPairRange K)
    (hp0 : ∀ i,0≤cavityPairProfile n d p 0 i)
    (hpm : ∀ i,Monotone (fun l=>cavityPairProfile n d p l i))
    (hpD : ∀ i,cavityPairProfile n d p (Fin.last k) i≤cavityPairDiagonal n d D i)
    (f : ℝ→ᵇℝ) (b : IndexedCascadeBase k) :
    let σ:=fun i=>Real.sqrt (cavityPairDiagonal n d D i-cavityPairProfile n d p (Fin.last k) i)
    let q:=cavityPairProfile n d p
    ∀ᵐ g ∂countableGaussianLaw,Integrable
      (fun x=>Real.exp (cavityLabelWeight n d k f σ q (g,x))*cavityLabelSpherical n d k σ q (g,x))
      ((indexedLeafProbability k b).prod (stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))) := by
  let σ:=fun i=>Real.sqrt (cavityPairDiagonal n d D i-cavityPairProfile n d p (Fin.last k) i)
  let q:=cavityPairProfile n d p
  let F:=cavityLabelSpherical n d k σ q
  let W:=cavityLabelWeight n d k f σ q
  have hL2 := (cavity_residual_square_integrable (indexedLeafProbability k b) countableGaussianLaw
    (stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d))) F
    (cavityLabelSpherical_measurable n d k σ q) (Real.exp (2*(n+1:ℕ)*D.2.val))
    (fun x=>(cavityLabelSpherical_second n d p D hp0 hpm hpD x).1)
    (fun x=>(cavityLabelSpherical_second n d p D hp0 hpm hpD x).2)).1
  filter_upwards [hL2.prod_right_ae] with g hg
  have hF : MemLp (fun x=>F (g,x)) 2
      ((indexedLeafProbability k b).prod (stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))) :=
    (memLp_two_iff_integrable_sq ((cavityLabelSpherical_measurable n d k σ q).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mpr hg
  apply ((MemLp.integrable (by norm_num : (1:ℝ≥0∞)≤2) hF).const_mul (Real.exp ((d:ℝ)*‖f‖))).mono'
    (((cavityLabelWeight_measurable n d k f σ q).exp.mul
      (cavityLabelSpherical_measurable n d k σ q)).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact ae_of_all _ fun x=>by
    have h0 : 0≤F (g,x) := (by norm_num : (0:ℝ)≤1).trans (cavityLabelSpherical_one n d k σ q (g,x))
    change ‖Real.exp (W (g,x))*F (g,x)‖≤_
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) h0)]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
      ((le_abs_self _).trans (cavityLabelWeight_bound n d k f σ q (g,x)))) h0

lemma cavityLabelFullPartition_ae_root (n d : ℕ) {K : ℝ} {k : ℕ}
    (p : Fin (k+1)→BulkPairRange K) (D : BulkPairRange K)
    (hp0 : ∀ i,0≤cavityPairProfile n d p 0 i)
    (hpm : ∀ i,Monotone (fun l=>cavityPairProfile n d p l i))
    (hpD : ∀ i,cavityPairProfile n d p (Fin.last k) i≤cavityPairDiagonal n d D i)
    (f : ℝ→ᵇℝ) (z : Fin k→ℝ)
    (H : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)→ℝ) (hH : Measurable H)
    (hres : ∀ v,(∫ y,cavityFullSingle n d f (WithLp.toLp 2 (fun i=>v i+
      Real.sqrt (cavityPairDiagonal n d D i-cavityPairProfile n d p (Fin.last k) i)*y i))
      ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))=Real.exp (H v)) :
    let q:=cavityPairProfile n d p
    let σ:=fun i=>Real.sqrt (cavityPairDiagonal n d D i-q (Fin.last k) i)
    let step:=gaussianLinearMarkStep (fun j=>diagonalMark (profileGaussianStep q j))
    let root:=fun y _=>diagonalMark (profileGaussianRoot q) y
    (cavityLabelFullPartition n d k f σ q)=ᵐ[
      (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw]
      (fun t=>indexedRootTerminalPartition step (fun s=>H (s 0)) root k
        ((indexedGaussianDisorder k (Fin (n+1)⊕Fin d) t.2).1,
          (t.1,(indexedGaussianDisorder k (Fin (n+1)⊕Fin d) t.2).2))) := by
  let q:=cavityPairProfile n d p
  let σ:=fun i=>Real.sqrt (cavityPairDiagonal n d D i-q (Fin.last k) i)
  let step:=gaussianLinearMarkStep (fun j=>diagonalMark (profileGaussianStep q j))
  let root:=fun y (_ : ℕ)=>diagonalMark (profileGaussianRoot q) y
  have hr : Measurable root := Measurable.of_eval fun _=>(diagonalMark (profileGaussianRoot q)).measurable
  have hm:=indexedRootTerminalPartition_measurable step (gaussianLinearMarkStep_measurable _) _
    (hH.comp (measurable_pi_apply 0)) root hr k
  have ht:=cavityIndexedRoot_disorder_preserving k (Fin (n+1)⊕Fin d) z
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (cavityLabelFullPartition_measurable n d k f σ q) (hm.comp ht.measurable))).mpr
  exact ae_of_all _ fun b=>by
    filter_upwards [cavityLabel_full_integrable_ae n d p D hp0 hpm hpD f b] with g hg
    unfold cavityLabelFullPartition
    rw [integral_prod _ hg]
    unfold indexedRootTerminalPartition
    apply integral_congr_ae
    exact ae_of_all _ fun l=>by
      have he y : Real.exp (cavityLabelWeight n d k f σ q (g,l,y))*
          cavityLabelSpherical n d k σ q (g,l,y)=
        cavityFullSingle n d f (WithLp.toLp 2 (fun i=>
          cavityCountableField (cavityLabelRow q) (cavityLabelLength k) g l i+σ i*y i)) := by
        exact mul_comm _ _
      change (∫ y,Real.exp (cavityLabelWeight n d k f σ q (g,l,y))*
        cavityLabelSpherical n d k σ q (g,l,y) ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))=_
      simp_rw [he]
      rw [hres,cavity_label_field_state]
      rfl

lemma cavityLabel_full_log_recursion (n d : ℕ) {K : ℝ} {k : ℕ}
    (p : Fin (k+1)→BulkPairRange K) (D : BulkPairRange K)
    (hp0 : ∀ i,0≤cavityPairProfile n d p 0 i)
    (hpm : ∀ i,Monotone (fun l=>cavityPairProfile n d p l i))
    (hpD : ∀ i,cavityPairProfile n d p (Fin.last k) i≤cavityPairDiagonal n d D i)
    (f : ℝ→ᵇℝ) (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1)
    (H : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)→ℝ) (hH : Measurable H)
    (hres : ∀ v,(∫ y,cavityFullSingle n d f (WithLp.toLp 2 (fun i=>v i+
      Real.sqrt (cavityPairDiagonal n d D i-cavityPairProfile n d p (Fin.last k) i)*y i))
      ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))=Real.exp (H v))
    (hfrac : finiteCascadeFractionalIntegrable (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))
      (gaussianLinearMarkStep (fun j=>diagonalMark (profileGaussianStep (cavityPairProfile n d p) j)))
      (fun s=>H (s 0)) k z) :
    let q:=cavityPairProfile n d p
    let σ:=fun i=>Real.sqrt (cavityPairDiagonal n d D i-q (Fin.last k) i)
    let R:=fun y=>finiteCascadeLogRecursion (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))
      (gaussianLinearMarkStep (fun j=>diagonalMark (profileGaussianStep q j))) k z (fun s=>H (s 0))
      (fun _=>diagonalMark (profileGaussianRoot q) y)
    Integrable R (stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d))) ∧
    (∫ t,Real.log (cavityLabelFullPartition n d k f σ q t)
      ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw)=
    ∫ y,R y ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) := by
  let q:=cavityPairProfile n d p
  let σ:=fun i=>Real.sqrt (cavityPairDiagonal n d D i-q (Fin.last k) i)
  let step:=gaussianLinearMarkStep (fun j=>diagonalMark (profileGaussianStep q j))
  let root:=fun y (_ : ℕ)=>diagonalMark (profileGaussianRoot q) y
  let F:=fun t=>Real.log (indexedRootTerminalPartition step (fun s=>H (s 0)) root k t)
  have hr : Measurable root := Measurable.of_eval fun _=>(diagonalMark (profileGaussianRoot q)).measurable
  have hm : Measurable F := (indexedRootTerminalPartition_measurable step
    (gaussianLinearMarkStep_measurable _) _ (hH.comp (measurable_pi_apply 0)) root hr k).log
  have ht:=cavityIndexedRoot_disorder_preserving k (Fin (n+1)⊕Fin d) z
  have he:=cavityLabelFullPartition_ae_root n d p D hp0 hpm hpD f z H hH hres
  have he' : (fun t=>Real.log (cavityLabelFullPartition n d k f σ q t))=ᵐ[_] F ∘ _ :=
    he.mono fun t h=>congrArg Real.log h
  have hi:=((ht.integrable_comp hm.aestronglyMeasurable).mp
    ((cavityLabel_full_log_integrable n d p D hp0 hpm hpD f z).congr he'))
  dsimp only
  constructor
  · apply hi.integral_prod_left.congr
    exact ae_of_all _ fun y=>cavity_indexed_log_recursion_fractional _ step
      (gaussianLinearMarkStep_measurable _) _ (hH.comp (measurable_pi_apply 0)) k z hfrac hz hz0 hz1 (root y)
  rw [integral_congr_ae he']
  simp only [Function.comp_def]
  rw [←integral_map ht.measurable.aemeasurable hm.aestronglyMeasurable,ht.map_eq]
  exact indexed_root_log_fractional _ _ step (gaussianLinearMarkStep_measurable _) _
    (hH.comp (measurable_pi_apply 0)) root k z hz hz0 hz1 hfrac hi
end SphericalPerceptronFreeEnergy

end

end OAI
