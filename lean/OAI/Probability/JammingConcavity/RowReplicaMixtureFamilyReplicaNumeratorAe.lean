import Mathlib
import OAI.Probability.JammingConcavity.UniversalRPCRank

namespace OAI

/-! Row Replica Mixture Family Replica Numerator Ae. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
open Classical
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
open scoped NNReal BigOperators
open MeasureTheory Metric Set
open Metric
open scoped RealInnerProductSpace
open Filter
open Finset Set
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open scoped BigOperators Classical
open scoped ENNReal NNReal Topology BigOperators Matrix MatrixOrder
open scoped BigOperators RealInnerProductSpace
open scoped NNReal Topology BigOperators
open scoped NNReal BigOperators RealInnerProductSpace
open scoped ENNReal NNReal BigOperators MatrixOrder
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

open Classical
namespace MicroscopicJamming

lemma rowReplicaMarkedLaw_eq (k r : ℕ) (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0)
    (μ : Measure (Fin r → CascadePath k)) :
    rowReplicaMarkedLaw k r d p₀ Δ μ =
      gaussianAdjunctionMeasure r (rowReplicaResidualCovariance k r d p₀ Δ) μ := by
  apply gaussianJointLaw_of_fibers
  · apply measurable_from_prod_countable_right
    intro xs
    change Measurable (fun w : (Option (CascadeMarkIndex k) → ℝ) × (Fin r → ℝ) =>
      rowReplicaGaussianField k r xs w.1 + WithLp.toLp 2 w.2)
    exact ((measurable_rowReplicaGaussianField k r xs).comp measurable_fst).add
      ((WithLp.measurable_toLp 2 _).comp measurable_snd)
  · intro xs
    exact (rowReplicaResidual k r d p₀ Δ xs).2

theorem rowReplicaMixture : RowReplicaMixtureStatement := by
  intro ms r d p₀ Δ
  exact rowReplicaMarkedLaw_eq ms.length r d p₀ Δ (cascadeFiniteReplicaLaw ms r)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators MatrixOrder

open Classical
namespace MicroscopicJamming

lemma gaussianAdjunction_naturality_countable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Countable A] [MeasurableSingletonClass A] [Countable B] [MeasurableSingletonClass B]
    (r : ℕ) (μ : Measure A) [SFinite μ] (g : A → B)
    (C : B → Matrix (Fin r) (Fin r) ℝ) :
    (gaussianAdjunctionMeasure r (C ∘ g) μ).map (Prod.map g id) =
      gaussianAdjunctionMeasure r C (μ.map g) := by
  have hg : Measurable g := measurable_of_countable _
  have hKA : Measurable (gaussianAdjunctionMap r (C ∘ g)) := by
    apply measurable_from_prod_countable_right
    intro x
    change Measurable (fun y : EuclideanSpace ℝ (Fin r) =>
      (x,Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (C (g x))) y))
    exact measurable_const.prodMk (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (C (g x)))).continuous.measurable
  have hKB : Measurable (gaussianAdjunctionMap r C) := by
    apply measurable_from_prod_countable_right
    intro x
    change Measurable (fun y : EuclideanSpace ℝ (Fin r) =>
      (x,Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (C x)) y))
    exact measurable_const.prodMk (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (C x))).continuous.measurable
  unfold gaussianAdjunctionMeasure
  rw [Measure.map_map (hg.prodMap measurable_id) hKA]
  rw [← Measure.map_id (μ := stdGaussian (EuclideanSpace ℝ (Fin r))),
    Measure.map_prod_map μ _ hg measurable_id,Measure.map_map hKB (hg.prodMap measurable_id)]
  rw [Measure.map_id]
  rfl
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

open Classical
namespace MicroscopicJamming

theorem rowRankGaussian : RowRankGaussianStatement := by
  intro ms hms h01 r d p₀ Δ
  let := cascadeReplicaLaw_probability ms
  have : IsProbabilityMeasure (cascadeFiniteReplicaLaw ms r) := by
    unfold cascadeFiniteReplicaLaw
    infer_instance
  rw [rowReplicaMarkedLaw_eq]
  have hc : rowReplicaResidualCovariance ms.length r d p₀ Δ =
      rowSignatureCovariance ms.length r d p₀ Δ ∘ cascadeGenealogySignature ms.length r := by
    funext xs
    exact rowReplicaResidualCovariance_signature ms.length r d p₀ Δ xs
  rw [hc, gaussianAdjunction_naturality_countable, rowRankSignature_law ms hms h01 r]
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

open Classical
namespace MicroscopicJamming

lemma rowReplicaKernelView_factor (k r : ℕ) :
    rowReplicaKernelView k r = (Prod.map (cascadeGenealogySignature k r) id) ∘
      (fun w => (w.1,rowReplicaResidualField k r w.1 w.2)) ∘ rowReplicaRearrange k r := by
  funext z
  apply Prod.ext
  · rfl
  · ext i
    rfl

lemma rowReplicaKernel_law_marked (ms : List ℝ) (r : ℕ) (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0) :
    ((rowReplicaEnvironmentLaw ms d p₀) ⊗ₘ replicaKernel (rowReplicaKernel ms Δ) r).map
      (rowReplicaKernelView ms.length r) =
      (rowReplicaMarkedLaw ms.length r d p₀ Δ (cascadeFiniteReplicaLaw ms r)).map
        (Prod.map (cascadeGenealogySignature ms.length r) id) := by
  rw [rowReplicaKernelView_factor]
  have hS : Measurable (Prod.map (cascadeGenealogySignature ms.length r)
      (id : EuclideanSpace ℝ (Fin r) → EuclideanSpace ℝ (Fin r))) := by fun_prop
  have hF : Measurable (fun w : (Fin r → CascadePath ms.length) ×
      ((Option (CascadeMarkIndex ms.length) → ℝ) × (Fin r → ℝ)) =>
      (w.1,rowReplicaResidualField ms.length r w.1 w.2)) := by
    apply measurable_fst.prodMk
    apply measurable_from_prod_countable_right
    intro xs
    exact ((measurable_rowReplicaGaussianField ms.length r xs).comp measurable_fst).add
      ((WithLp.measurable_toLp 2 _).comp measurable_snd)
  rw [← Measure.map_map hS (hF.comp (measurable_rowReplicaRearrange ms.length r)),
    ← Measure.map_map hF (measurable_rowReplicaRearrange ms.length r), rowReplicaRearrangement_law]
  rfl

theorem rowReplicaKernel_exact : RowReplicaKernelStatement := by
  intro ms hms h01 r d p₀ Δ
  rw [rowReplicaKernel_law_marked, rowRankGaussian ms hms h01 r d p₀ Δ]
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

open Classical
namespace MicroscopicJamming
lemma rowCascadeProfile_top (ms : List ℝ) (hm : ∀ m ∈ ms, m < 1) (d : ℕ → ℝ≥0) (p₀ : ℝ≥0) :
    (rowCascadeProfile ms d p₀).val 1 = (p₀:ℝ) + ∑ j : Fin ms.length, (d j:ℝ) := by
  have he : rpcStepLevel ms 1 = ms.length := by
    unfold rpcStepLevel
    congr 1
    exact List.filter_eq_self.mpr (fun m h => by simpa using (hm m h).le)
  simp only [rowCascadeProfile,he]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [ite_eq_left (Nat.succ_le_of_lt j.isLt)]
lemma rowCascadeProfile_bound (ms : List ℝ) (hm : ∀ m ∈ ms, m < 1) (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0) :
    (rowCascadeProfile ms d p₀).val 1 ≤ (rowReplicaDiagonal ms.length d p₀ Δ : ℝ) := by
  rw [rowCascadeProfile_top ms hm]
  simp only [rowReplicaDiagonal,NNReal.coe_add,NNReal.coe_sum]
  exact le_add_of_nonneg_right Δ.coe_nonneg
lemma rowCascadeCovariance_ae {r : ℕ} (ms : List ℝ) (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0) :
    (rowSignatureCovariance ms.length r d p₀ Δ ∘ rankGenealogySignature ms r) =ᵐ[realizedRankLaw]
      rowFullRankCovariance r (rowReplicaDiagonal ms.length d p₀ Δ) (rowCascadeProfile ms d p₀) := by
  filter_upwards [realizedRankLaw_constraints] with U hU
  funext i j
  by_cases hij : i=j
  · subst j
    simp only [Function.comp_apply,rowSignatureCovariance,rankGenealogySignature,ite_true,
      rowFullRankCovariance,rowReplicaDiagonal,NNReal.coe_add,NNReal.coe_sum]
    congr 2
    apply Finset.sum_congr rfl
    intro a _
    rw [ite_eq_left (Nat.succ_le_of_lt a.isLt)]
  · simp only [Function.comp_apply,rowSignatureCovariance,rankGenealogySignature,ite_eq_right hij,
      rowFullRankCovariance,add_zero]
    rw [rowClosedProfile_eq _ (hU.2.2.1 i.val j.val)]
    rfl
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder

open Classical
namespace MicroscopicJamming
lemma gaussianAdjunction_naturality {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Countable B] [MeasurableSingletonClass B] (r : ℕ) (μ : Measure A) [SFinite μ]
    (g : A → B) (hg : Measurable g) (C : B → Matrix (Fin r) (Fin r) ℝ) :
    (gaussianAdjunctionMeasure r (C ∘ g) μ).map (Prod.map g id) =
      gaussianAdjunctionMeasure r C (μ.map g) := by
  have hKB : Measurable (gaussianAdjunctionMap r C) := by
    apply measurable_from_prod_countable_right
    intro x
    change Measurable (fun y : EuclideanSpace ℝ (Fin r) =>
      (x,Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (C x)) y))
    exact measurable_const.prodMk (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (C x))).continuous.measurable
  have hKA : Measurable (gaussianAdjunctionMap r (C ∘ g)) :=
    measurable_fst.prodMk ((hKB.comp (hg.prodMap measurable_id)).snd)
  unfold gaussianAdjunctionMeasure
  rw [Measure.map_map (hg.prodMap measurable_id) hKA]
  rw [← Measure.map_id (μ := stdGaussian (EuclideanSpace ℝ (Fin r))),
    Measure.map_prod_map μ _ hg measurable_id,Measure.map_map hKB (hg.prodMap measurable_id)]
  rw [Measure.map_id]
  rfl
lemma gaussianAdjunction_congr_ae {A : Type*} [MeasurableSpace A]
    (r : ℕ) (μ : Measure A) [SFinite μ] (C D : A → Matrix (Fin r) (Fin r) ℝ)
    (he : C =ᵐ[μ] D) : gaussianAdjunctionMeasure r C μ = gaussianAdjunctionMeasure r D μ := by
  apply Measure.map_congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae he] with z hz
  simp only [gaussianAdjunctionMap,hz]
lemma rowReplicaFields_law (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (hm : ∀ m ∈ ms, 0 < m ∧ m < 1) (r : ℕ) (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0) :
    ((rowReplicaEnvironmentLaw ms d p₀) ⊗ₘ replicaKernel (rowReplicaKernel ms Δ) r).map
      (fun z => WithLp.toLp 2 (fun i => rowReplicaSiteField ms.length (z.1,z.2 i))) =
    (gaussianAdjunctionMeasure r
      (rowFullRankCovariance r (rowReplicaDiagonal ms.length d p₀ Δ) (rowCascadeProfile ms d p₀))
      realizedRankLaw).map Prod.snd := by
  have hk := rowReplicaKernel_exact ms hms hm r d p₀ Δ
  have hg := measurable_rankGenealogySignature ms r
  have hn := gaussianAdjunction_naturality r realizedRankLaw (rankGenealogySignature ms r) hg
    (rowSignatureCovariance ms.length r d p₀ Δ)
  rw [gaussianAdjunction_congr_ae _ _ _ _ (rowCascadeCovariance_ae ms d p₀ Δ)] at hn
  have he := congrArg (fun μ : Measure (RowRankSignature r × EuclideanSpace ℝ (Fin r)) => μ.map Prod.snd) hk
  rw [Measure.map_map measurable_snd (measurable_rowReplicaKernelView ms.length r)] at he
  rw [← hn,Measure.map_map measurable_snd (hg.prodMap measurable_id)] at he
  exact he
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming
lemma rowReplicaRetainedRank_law (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (hm : ∀ m ∈ ms, 0 < m ∧ m < 1) (r : ℕ) (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0) :
    ((rowReplicaEnvironmentLaw ms d p₀) ⊗ₘ replicaKernel (rowReplicaKernel ms Δ) r).map
      (rowReplicaKernelView ms.length r) =
    (gaussianAdjunctionMeasure r
      (rowFullRankCovariance r (rowReplicaDiagonal ms.length d p₀ Δ) (rowCascadeProfile ms d p₀))
      realizedRankLaw).map (Prod.map (rankGenealogySignature ms r) id) := by
  have hn := gaussianAdjunction_naturality r realizedRankLaw (rankGenealogySignature ms r)
    (measurable_rankGenealogySignature ms r) (rowSignatureCovariance ms.length r d p₀ Δ)
  rw [gaussianAdjunction_congr_ae _ _ _ _ (rowCascadeCovariance_ae ms d p₀ Δ)] at hn
  exact (rowReplicaKernel_exact ms hms hm r d p₀ Δ).trans hn.symm

theorem rowRetainedRankLaw : RowRetainedRankLawStatement := by
  intro u L H hu hL hH hb ms hms hm d p₀ Δ B k
  have hdu : ContDiff ℝ 1 (deriv u) := hu.deriv'
  let a : Fin (2+k) := Fin.castAdd k (0:Fin 2)
  let b : Fin (2+k) := Fin.castAdd k (1:Fin 2)
  let F : RowRankSignature (2+k) × EuclideanSpace ℝ (Fin (2+k)) → ℝ × (Fin (2+k) → ℝ) :=
    fun z => (B (z.1 a b)*(deriv u (z.2 a)*deriv u (z.2 b)),fun i => u (z.2 i))
  have hf (i : Fin (2+k)) : Measurable (fun z : RowRankSignature (2+k) ×
      EuclideanSpace ℝ (Fin (2+k)) => z.2 i) :=
    (EuclideanSpace.proj i).continuous.measurable.comp measurable_snd
  have hF : Measurable F := by
    exact (((measurable_of_countable (fun s : RowRankSignature (2+k) => B (s a b))).comp
      measurable_fst).mul (((hdu.continuous.measurable).comp (hf a)).mul
        ((hdu.continuous.measurable).comp (hf b)))).prodMk
      (Measurable.of_eval fun coordinate => hu.continuous.measurable.comp (hf coordinate))
  have he := congrArg (fun μ : Measure (RowRankSignature (2+k) × EuclideanSpace ℝ (Fin (2+k))) =>
      μ.map F) (rowReplicaRetainedRank_law ms hms hm (2+k) d p₀ Δ)
  rw [Measure.map_map hF (measurable_rowReplicaKernelView ms.length (2+k)),
    Measure.map_map hF ((measurable_rankGenealogySignature ms (2+k)).prodMap measurable_id)] at he
  unfold replicaFieldLaw replicaFieldView rowFullPotential rowFullPair
  simpa only [Function.comp_def,F,a,b,rowReplicaKernelView,cascadeGenealogySignature,
    WithLp.ofLp_toLp,replicaFirst,Prod.map_fst,Prod.map_snd,id_eq,rankGenealogySignature,
    Fin.castAdd_inj,Fin.zero_ne_one,ite_false,Fin.val_castAdd,Fin.val_zero,Fin.val_one] using he
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma scaledFamilyWeightedMean {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ≥0∞} {S : B → ℝ≥0∞} {r : A → ℝ} {p : ℝ}
    {w : A × B → ℝ≥0∞} {g : A → ℝ≥0∞}
    (hF : Measurable F) (hw : Measurable w) (_hg : Measurable g)
    (h : ∀ a, IdentDistrib (fun b => F (a,b)) (fun b => ENNReal.ofReal (Real.exp (r a))*S b) ν ν)
    (hs : ∀ᵐ b ∂ν, 0 < S b ∧ S b < ∞)
    (hiS : Integrable (fun b => (S b).toReal^p) ν)
    (hir : Integrable (fun a => Real.exp (p*r a)) μ)
    (hmean : ∀ a, (∫⁻ b, ENNReal.ofReal ((F (a,b)).toReal^p)*w (a,b) ∂ν) /
      ENNReal.ofReal (∫ b, (F (a,b)).toReal^p ∂ν) = g a) :
    weightedChildMean (μ.prod ν) p (fun z => Real.log (F z).toReal) w =
      (∫⁻ a, g a * ENNReal.ofReal (Real.exp (p*r a)) ∂μ) /
        ENNReal.ofReal (∫ a, Real.exp (p*r a) ∂μ) := by
  let C := ∫ b, (S b).toReal^p ∂ν
  have hC : 0 < C := integral_pos_of_positive_ae ν hiS (hs.mono fun _ hb =>
    Real.rpow_pos_of_pos (ENNReal.toReal_pos hb.1.ne' hb.2.ne) _)
  have hp : ∀ᵐ z ∂μ.prod ν, 0 < F z ∧ F z < ∞ := by
    apply (Measure.ae_prod_iff_ae_ae ((measurableSet_lt measurable_const hF).inter
      (measurableSet_lt hF measurable_const))).mpr
    exact Eventually.of_forall fun a => scaledLaw_positive ν (h a) hs
  have he : (fun z => Real.exp (p*Real.log (F z).toReal)) =ᵐ[μ.prod ν]
      (fun z => (F z).toReal^p) := by
    filter_upwards [hp] with z hz
    rw [Real.rpow_def_of_pos (ENNReal.toReal_pos hz.1.ne' hz.2.ne), mul_comm]
  have hiP := scaled_family_rpow μ ν hF h hiS hir
  have hm (a : A) : (∫ b, (F (a,b)).toReal^p ∂ν) = Real.exp (p*r a)*C :=
    (scaledLaw_rpow ν (h a) hiS).2
  have hn (a : A) : (∫⁻ b, ENNReal.ofReal ((F (a,b)).toReal^p)*w (a,b) ∂ν) =
      g a * ENNReal.ofReal (Real.exp (p*r a)*C) := by
    have ha := congrArg (fun z : ℝ≥0∞ => z * ENNReal.ofReal (Real.exp (p*r a)*C)) (hmean a)
    rw [hm, ENNReal.div_mul_cancel (ENNReal.ofReal_pos.mpr (mul_pos (Real.exp_pos _) hC)).ne'
      ENNReal.ofReal_ne_top] at ha
    exact ha
  have heu : (fun z : A × B => w z*ENNReal.ofReal (Real.exp (p*Real.log (F z).toReal))) =ᵐ[μ.prod ν]
      (fun z => ENNReal.ofReal ((F z).toReal^p)*w z) := by
    filter_upwards [he] with z hz
    rw [hz, mul_comm]
  unfold weightedChildMean
  rw [lintegral_congr_ae heu, integral_congr_ae he]
  have hpint : (∫⁻ z : A × B, ENNReal.ofReal ((F z).toReal^p)*w z ∂μ.prod ν) =
      ∫⁻ a, ∫⁻ b, ENNReal.ofReal ((F (a,b)).toReal^p)*w (a,b) ∂ν ∂μ :=
    lintegral_prod _ (((hF.ennreal_toReal.pow_const p).ennreal_ofReal.mul hw).aemeasurable)
  rw [hpint]
  simp_rw [hn]
  have hec (a : A) : g a * ENNReal.ofReal (Real.exp (p*r a)*C) =
      (g a * ENNReal.ofReal (Real.exp (p*r a))) * ENNReal.ofReal C := by
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
  simp_rw [hec]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hiP.2,
    ENNReal.ofReal_mul (integral_exp_pos hir).le]
  exact ENNReal.mul_div_mul_right _ _ (ENNReal.ofReal_pos.mpr hC).ne'
    ENNReal.ofReal_ne_top
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma familyPathMean_cons_ratio {E : Type} [MeasurableSpace E] [Add E] [MeasurableAdd₂ E]
    (m : ℝ) (hm : m ≠ 0) (ms : List ℝ) (ν : ℕ → Measure E)
    (hν : ∀ j, IsProbabilityMeasure (ν j)) {u : E → ℝ} (hu : Measurable u)
    (hi : FamilyMomentsFinite (m::ms) ν u) {φ : E → ℝ≥0∞} (hφ : Measurable φ) (x : E) :
    familyPathMean (m::ms) ν u φ x =
      (∫⁻ a, familyPathMean ms (fun j => ν (j+1)) u φ (x+a) *
        ENNReal.ofReal (Real.exp (m*familyRecursion ms (fun j => ν (j+1)) u (x+a))) ∂ν 0) /
        ENNReal.ofReal (∫ a, Real.exp (m*familyRecursion ms (fun j => ν (j+1)) u (x+a)) ∂ν 0) := by
  let := hν 0
  let c := ∫ a, Real.exp (m*familyRecursion ms (fun j => ν (j+1)) u (x+a)) ∂ν 0
  have hc : 0 < c := integral_exp_pos (hi.1 x)
  have he (a : E) : (familyEdgeMultiplier m ms ν u x a)^m =
      Real.exp (m*familyRecursion ms (fun j => ν (j+1)) u (x+a))/c := by
    change (Real.exp (familyRecursion ms (fun j => ν (j+1)) u (x+a) - (1/m)*Real.log c))^m = _
    rw [← Real.exp_mul, show (familyRecursion ms (fun j => ν (j+1)) u (x+a) -
        (1/m)*Real.log c)*m = m*familyRecursion ms (fun j => ν (j+1)) u (x+a)-Real.log c by field_simp,
      Real.exp_sub, Real.exp_log hc]
  have hcu : Measurable (fun a => (familyEdgeMultiplier m ms ν u x a)^m) := ((measurable_familyEdgeMultiplier m ms ν hν hu).comp
    (measurable_const.prodMk measurable_id)).pow_const m
  have hmu : Measurable (fun a => familyPathMean ms (fun j => ν (j+1)) u φ (x+a)) := (measurable_familyPathMean ms (fun j => ν (j+1)) (fun j => hν (j+1)) hu hφ).comp
    (measurable_const.add measurable_id)
  rw [familyPathMean, decoratedTransition, pointCloudTilt,
    lintegral_withDensity_eq_lintegral_mul (ν 0) hcu.ennreal_ofReal hmu]
  simp_rw [he, ENNReal.ofReal_div_of_pos hc]
  have ho (a : E) : ENNReal.ofReal (Real.exp (m*familyRecursion ms (fun j => ν (j+1)) u (x+a))) /
      ENNReal.ofReal c * familyPathMean ms (fun j => ν (j+1)) u φ (x+a) =
      (familyPathMean ms (fun j => ν (j+1)) u φ (x+a) *
        ENNReal.ofReal (Real.exp (m*familyRecursion ms (fun j => ν (j+1)) u (x+a)))) / ENNReal.ofReal c := by
    simp only [div_eq_mul_inv]
    ac_rfl
  simp only [Pi.mul_apply]
  simp_rw [ho]
  simp only [div_eq_mul_inv]
  exact lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hc).ne')
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma measurable_distinctCloudIntegral_param {I : Type*} (is : List I) :
    ∀ {B X : Type} [MeasurableSpace B] [MeasurableSpace X] [MeasurableEq X]
      (κ : Kernel B X) [IsSFiniteKernel κ]
      (F : I → B × X → ℝ≥0∞), (∀ i ∈ is, Measurable (F i)) →
      ∀ (xs : List (B → X)), (∀ x ∈ xs, Measurable x) →
      Measurable (fun b => distinctCloudIntegral (is.map (fun i x => F i (b,x)))
        (κ b) (xs.map (fun x => x b))) := by
  classical
  induction is with
  | nil => intros; exact measurable_const
  | cons i is ih =>
    intro B X _ _ _ κ _ F hF xs hxs
    have htail : ∀ j ∈ is, Measurable (F j) := fun j hj => hF j (by simp [hj])
    let ys : List (B × X → X) := Prod.snd :: xs.map (fun x => x ∘ Prod.fst)
    have hys : ∀ y ∈ ys, Measurable y := by
      intro y hy
      simp only [ys,List.mem_cons,List.mem_map] at hy
      rcases hy with rfl | ⟨z,hz,rfl⟩
      · exact measurable_snd
      · exact (hxs z hz).comp measurable_fst
    have hi := ih (κ.comap Prod.fst measurable_fst)
      (fun j (z : (B × X) × X) => F j (z.1.1,z.2))
      (fun j hj => (htail j hj).comp (measurable_fst.fst.prodMk measurable_snd)) ys hys
    have hc := measurableSet_mem_evaluated_list
      (xs.map (fun x => x ∘ Prod.fst)) (by
        intro y hy
        obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hy
        exact (hxs z hz).comp measurable_fst)
      (measurable_snd : Measurable (Prod.snd : B × X → X))
    have hm : Measurable (fun z : B × X =>
        if z.2 ∈ xs.map (fun x => x z.1) then 0 else
          F i z * distinctCloudIntegral (is.map (fun j x => F j (z.1,x)))
            (κ z.1) (z.2 :: xs.map (fun x => x z.1))) := by
      apply Measurable.ite
      · simpa only [List.map_map,Function.comp_def] using hc
      · exact measurable_const
      · apply (hF i (by simp)).mul
        simpa only [ys,List.map_cons,List.map_map,Function.comp_def,Kernel.comap_apply] using hi
    exact hm.lintegral_kernel_prod_right'

lemma validMarked_shape {E : Type} [MeasurableSpace E] (k : ℕ)
    (b : MarkedReplicaPattern E k) (hb : ValidMarkedReplicaPattern k b) :
    ValidReplicaPattern k (markedReplicaShape k b) := by
  induction k with
  | zero => exact hb.1
  | succ k ih =>
    change b.map (markedReplicaShape k) ≠ [] ∧ _
    constructor
    · intro he
      exact hb.1 (List.map_eq_nil_iff.mp he)
    · intro a ha
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
      exact ih c (hb.2 c hc)

lemma measurable_familyReplicaWeight {E : Type} [MeasurableSpace E] [MeasurableEq E]
    [Add E] [MeasurableAdd₂ E] (ms : List ℝ) {u : E → ℝ} (hu : Measurable u)
    (b : MarkedReplicaPattern E ms.length) (hb : ValidMarkedReplicaPattern ms.length b) :
    Measurable (fun z : E × FamilyCascadeTree E ms.length =>
      familyReplicaWeight ms b u z.1 z.2) := by
  induction ms with
  | nil => exact hb.2.1.comp measurable_fst
  | cons m ms ih =>
    change Measurable (fun z : E × PointCloud (E × FamilyCascadeTree E ms.length) =>
      ENNReal.ofReal ((familyLeafTotal (m::ms) u z.1 z.2).toReal ^
        (-(replicaPatternSize (ms.length+1) (markedReplicaShape (ms.length+1) b):ℝ))) *
      distinctCloudIntegral (b.map (fun c (a : ℝ × (E × FamilyCascadeTree E ms.length)) =>
        (ENNReal.ofReal (a.1^(-1/m))*familyLeafTotal ms u (z.1+a.2.1) a.2.2)^
          (replicaPatternSize ms.length (markedReplicaShape ms.length c)) *
          familyReplicaWeight ms c u (z.1+a.2.1) a.2.2)) (pointCloudMeasure z.2) [])
    apply Measurable.mul
    · exact ((measurable_familyLeafTotal (m::ms) hu).ennreal_toReal.pow_const _).ennreal_ofReal
    · let κ : Kernel (E × PointCloud (E × FamilyCascadeTree E ms.length))
          (ℝ × (E × FamilyCascadeTree E ms.length)) :=
          (cloudKernel (A := E × FamilyCascadeTree E ms.length)).comap
            Prod.snd measurable_snd
      have h := measurable_distinctCloudIntegral_param b κ
        (fun c z => (ENNReal.ofReal (z.2.1^(-1/m))*
          familyLeafTotal ms u (z.1.1+z.2.2.1) z.2.2.2)^
            (replicaPatternSize ms.length (markedReplicaShape ms.length c)) *
              familyReplicaWeight ms c u (z.1.1+z.2.2.1) z.2.2.2) (by
          intro c hc
          have hmap : Measurable (fun z :
              (E × PointCloud (E × FamilyCascadeTree E ms.length)) ×
                (ℝ × (E × FamilyCascadeTree E ms.length)) => (z.1.1+z.2.2.1,z.2.2.2)) := by fun_prop
          exact (((by fun_prop : Measurable (fun z :
              (E × PointCloud (E × FamilyCascadeTree E ms.length)) ×
                (ℝ × (E × FamilyCascadeTree E ms.length)) => ENNReal.ofReal (z.2.1^(-1/m)))).mul
            ((measurable_familyLeafTotal ms hu).comp hmap)).pow_const _).mul
              ((ih c (hb.2 c hc)).comp hmap)) [] (by simp)
      simpa only [κ,Kernel.comap_apply,cloudKernel_apply,List.map_nil] using h

lemma measurable_familyReplicaMean {E : Type} [MeasurableSpace E] [Add E] [MeasurableAdd₂ E]
    (ms : List ℝ) (ν : ℕ → Measure E) (hν : ∀ j, IsProbabilityMeasure (ν j))
    {u : E → ℝ} (hu : Measurable u)
    (b : MarkedReplicaPattern E ms.length) (hb : ValidMarkedReplicaPattern ms.length b) :
    Measurable (familyReplicaMean ms b ν u) := by
  induction ms generalizing ν with
  | nil => exact hb.2.1
  | cons m ms ih =>
    let := hν 0
    have hc := ((measurable_familyEdgeMultiplier m ms ν hν hu).pow_const m).ennreal_ofReal
    have hi (c : MarkedReplicaPattern E ms.length) (hc' : List.Mem c b) : Measurable (fun x => ∫⁻ a,
        familyReplicaMean ms c (fun j => ν (j+1)) u (x+a) ∂decoratedTransition m ms ν u x) := by
      have hh := ih (fun j => ν (j+1)) (fun j => hν (j+1)) c (hb.2 c hc')
      have he (x : E) : (∫⁻ a, familyReplicaMean ms c (fun j => ν (j+1)) u (x+a)
          ∂decoratedTransition m ms ν u x) =
          ∫⁻ a, ENNReal.ofReal ((familyEdgeMultiplier m ms ν u x a)^m)*
            familyReplicaMean ms c (fun j => ν (j+1)) u (x+a) ∂ν 0 :=
        lintegral_withDensity_eq_lintegral_mul (ν 0)
          (hc.comp (measurable_const.prodMk measurable_id))
          (hh.comp (measurable_const.add measurable_id))
      simp_rw [he]
      exact (hc.mul (hh.comp measurable_add)).lintegral_prod_right'
    change Measurable (fun x => (b.map (fun c => ∫⁻ a,
      familyReplicaMean ms c (fun j => ν (j+1)) u (x+a)
        ∂decoratedTransition m ms ν u x)).prod)
    have hh : ∀ (bs : List (MarkedReplicaPattern E ms.length)),
        (∀ c ∈ bs, List.Mem c b) → Measurable (fun x => (bs.map (fun c => ∫⁻ a,
          familyReplicaMean ms c (fun j => ν (j+1)) u (x+a)
            ∂decoratedTransition m ms ν u x)).prod) := by
      intro bs hs
      induction bs with
      | nil => exact measurable_const
      | cons c cs ih =>
        exact (hi c (hs c (by simp))).mul (ih (fun c hc => hs c (by simp [hc])))
    exact hh b (fun _ hc => hc)

lemma familyReplicaMean_le_one {E : Type} [MeasurableSpace E] [Add E] [MeasurableAdd₂ E]
    (ms : List ℝ) (h01 : ∀ m ∈ ms, 0 < m) (ν : ℕ → Measure E)
    (hν : ∀ j, IsProbabilityMeasure (ν j)) (u : E → ℝ)
    (hi : FamilyMomentsFinite ms ν u) (b : MarkedReplicaPattern E ms.length)
    (hb : ValidMarkedReplicaPattern ms.length b) (x : E) :
    familyReplicaMean ms b ν u x ≤ 1 := by
  induction ms generalizing ν x with
  | nil => exact hb.2.2 x
  | cons m ms ih =>
    let := decoratedTransition_probability m (ne_of_gt (h01 m (by simp))) ms ν hν u hi x
    have he (c : MarkedReplicaPattern E ms.length) (hc : List.Mem c b) :
        (∫⁻ a, familyReplicaMean ms c (fun j => ν (j+1)) u (x+a)
          ∂decoratedTransition m ms ν u x) ≤ 1 := by
      calc
        _ ≤ ∫⁻ _ : E, 1 ∂decoratedTransition m ms ν u x := lintegral_mono fun _ =>
          ih (fun z hz => h01 z (by simp [hz])) (fun j => ν (j+1)) (fun j => hν (j+1))
            hi.2 c (hb.2 c hc) _
        _ = 1 := by simp
    change (b.map (fun c => ∫⁻ a,
      familyReplicaMean ms c (fun j => ν (j+1)) u (x+a)
        ∂decoratedTransition m ms ν u x)).prod ≤ 1
    have hh : ∀ (bs : List (MarkedReplicaPattern E ms.length)),
        (∀ c ∈ bs, List.Mem c b) → (bs.map (fun c => ∫⁻ a,
          familyReplicaMean ms c (fun j => ν (j+1)) u (x+a)
            ∂decoratedTransition m ms ν u x)).prod ≤ 1 := by
      intro bs hs
      induction bs with
      | nil => rfl
      | cons c cs ih =>
        exact mul_le_one' (he c (hs c (by simp))) (ih (fun c hc => hs c (by simp [hc])))
    exact hh b (fun _ hc => hc)
end MicroscopicJamming
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma decoratedTransition_lintegral_ratio {E : Type} [MeasurableSpace E] [Add E]
    [MeasurableAdd₂ E] (m : ℝ) (hm : m ≠ 0) (ms : List ℝ)
    (ν : ℕ → Measure E) (hν : ∀ j, IsProbabilityMeasure (ν j)) {u : E → ℝ}
    (hu : Measurable u) (hi : FamilyMomentsFinite (m::ms) ν u)
    {f : E → ℝ≥0∞} (hf : Measurable f) (x : E) :
    (∫⁻ a, f a ∂decoratedTransition m ms ν u x) =
      (∫⁻ a, f a * ENNReal.ofReal (Real.exp
        (m*familyRecursion ms (fun j => ν (j+1)) u (x+a))) ∂ν 0) /
          ENNReal.ofReal (∫ a, Real.exp (m*familyRecursion ms (fun j => ν (j+1)) u (x+a)) ∂ν 0) := by
  let := hν 0
  let c := ∫ a, Real.exp (m*familyRecursion ms (fun j => ν (j+1)) u (x+a)) ∂ν 0
  have hc : 0 < c := integral_exp_pos (hi.1 x)
  have he (a : E) : (familyEdgeMultiplier m ms ν u x a)^m =
      Real.exp (m*familyRecursion ms (fun j => ν (j+1)) u (x+a))/c := by
    change (Real.exp (familyRecursion ms (fun j => ν (j+1)) u (x+a) - (1/m)*Real.log c))^m = _
    rw [←Real.exp_mul,show (familyRecursion ms (fun j => ν (j+1)) u (x+a) -
      (1/m)*Real.log c)*m = m*familyRecursion ms (fun j => ν (j+1)) u (x+a)-Real.log c by field_simp,
      Real.exp_sub,Real.exp_log hc]
  have hcu : Measurable (fun a => (familyEdgeMultiplier m ms ν u x a)^m) :=
    ((measurable_familyEdgeMultiplier m ms ν hν hu).comp
      (measurable_const.prodMk measurable_id)).pow_const m
  rw [decoratedTransition,pointCloudTilt,
    lintegral_withDensity_eq_lintegral_mul (ν 0) hcu.ennreal_ofReal hf]
  simp_rw [he,ENNReal.ofReal_div_of_pos hc]
  have ho (a : E) : ENNReal.ofReal (Real.exp (m*familyRecursion ms (fun j => ν (j+1)) u (x+a))) /
      ENNReal.ofReal c * f a =
      (f a * ENNReal.ofReal (Real.exp (m*familyRecursion ms (fun j => ν (j+1)) u (x+a)))) /
        ENNReal.ofReal c := by simp only [div_eq_mul_inv]; ac_rfl
  simp only [Pi.mul_apply]
  simp_rw [ho,div_eq_mul_inv]
  exact lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hc).ne')

lemma familyLeafTotal_positive_ae {E : Type} [MeasurableSpace E] [Add E] [MeasurableAdd₂ E]
    (ms : List ℝ) (hms : ms.Pairwise (· < ·)) (h01 : ∀ m ∈ ms, 0 < m ∧ m < 1)
    (ν : ℕ → Measure E) (hν : ∀ j, IsProbabilityMeasure (ν j))
    {u : E → ℝ} (hu : Measurable u) (hi : FamilyMomentsFinite ms ν u) (x : E) :
    ∀ᵐ ω ∂familyCascadeLaw ms.length ν,
      0 < familyLeafTotal ms u x ω ∧ familyLeafTotal ms u x ω < ∞ :=
  scaledLaw_positive _ (familyLeafTotal_identDistrib ms hms h01 ν hν hu hi x)
    (familyUnmarkedTotal_properties ms hms h01 ν hν).1

lemma familyChildTotal_positive_ae {E : Type} [MeasurableSpace E] [Add E] [MeasurableAdd₂ E]
    (ms : List ℝ) (hms : ms.Pairwise (· < ·)) (h01 : ∀ m ∈ ms, 0 < m ∧ m < 1)
    (ν : ℕ → Measure E) (hν : ∀ j, IsProbabilityMeasure (ν j))
    {u : E → ℝ} (hu : Measurable u)
    (hi : FamilyMomentsFinite ms (fun j => ν (j+1)) u) (x : E) :
    ∀ᵐ z ∂(ν 0).prod (familyCascadeLaw ms.length (fun j => ν (j+1))),
      0 < familyLeafTotal ms u (x+z.1) z.2 ∧ familyLeafTotal ms u (x+z.1) z.2 < ∞ := by
  let := hν 0
  let := familyCascadeLaw_probability ms.length (fun j => ν (j+1)) (fun j => hν (j+1))
  have hF := (measurable_familyLeafTotal ms hu).comp
    (show Measurable (fun z : E × FamilyCascadeTree E ms.length => (x+z.1,z.2)) by fun_prop)
  apply (Measure.ae_prod_iff_ae_ae ((measurableSet_lt measurable_const hF).inter
    (measurableSet_lt hF measurable_const))).mpr
  exact Eventually.of_forall fun a => familyLeafTotal_positive_ae ms hms h01
    (fun j => ν (j+1)) (fun j => hν (j+1)) hu hi (x+a)

def familyWeightedBlocks {E : Type} [MeasurableSpace E] [Add E]
    (ms : List ℝ) (bs : List (MarkedReplicaPattern E ms.length)) (u : E → ℝ) (x : E) :
    List (ℕ × (E × FamilyCascadeTree E ms.length → ℝ≥0∞)) :=
  bs.map (fun b => (replicaPatternSize ms.length (markedReplicaShape ms.length b),
    fun z => familyReplicaWeight ms b u (x+z.1) z.2))

lemma familyTotal_expMarked_ae {E : Type} [MeasurableSpace E] [Add E] [MeasurableAdd₂ E]
    (ms : List ℝ) (hms : ms.Pairwise (· < ·)) (h01 : ∀ m ∈ ms, 0 < m ∧ m < 1)
    (ν : ℕ → Measure E) (hν : ∀ j, IsProbabilityMeasure (ν j))
    {u : E → ℝ} (hu : Measurable u)
    (hi : FamilyMomentsFinite ms (fun j => ν (j+1)) u) (m : ℝ) (x : E) :
    familyLeafTotal (m::ms) u x =ᵐ[familyCascadeLaw (m::ms).length ν]
      expMarkedTotal m (fun z : E × FamilyCascadeTree E ms.length =>
        Real.log (familyLeafTotal ms u (x+z.1) z.2).toReal) := by
  let τ := familyCascadeLaw ms.length (fun j => ν (j+1))
  let := hν 0
  let := familyCascadeLaw_probability ms.length (fun j => ν (j+1)) (fun j => hν (j+1))
  have he := pointCloudFunctional_mark_congr ((ν 0).prod τ)
    (f := fun z : ℝ × (E × FamilyCascadeTree E ms.length) =>
      ENNReal.ofReal (z.1^(-1/m))*familyLeafTotal ms u (x+z.2.1) z.2.2)
    (g := fun z : ℝ × (E × FamilyCascadeTree E ms.length) =>
      ENNReal.ofReal (z.1^(-1/m)*Real.exp (Real.log (familyLeafTotal ms u (x+z.2.1) z.2.2).toReal))) (by
        filter_upwards [familyChildTotal_positive_ae ms hms h01 ν hν hu hi x] with z hz
        intro s
        rw [Real.exp_log (ENNReal.toReal_pos hz.1.ne' hz.2.ne),
          ENNReal.ofReal_mul' ENNReal.toReal_nonneg,ENNReal.ofReal_toReal hz.2.ne])
  exact he

lemma familyReplica_numerator_ae {E : Type} [MeasurableSpace E] [MeasurableEq E]
    [Add E] [MeasurableAdd₂ E] (ms : List ℝ) (m η : ℝ)
    (hms : (m::ms).Pairwise (· < ·)) (h01 : ∀ a ∈ m::ms, 0 < a ∧ a < 1)
    (ν : ℕ → Measure E) (hν : ∀ j, IsProbabilityMeasure (ν j))
    {u : E → ℝ} (hu : Measurable u) (hi : FamilyMomentsFinite (m::ms) ν u)
    (bs : List (MarkedReplicaPattern E ms.length)) (x : E) :
    (fun ω => ENNReal.ofReal ((familyLeafTotal (m::ms) u x ω).toReal^η) *
      familyReplicaWeight (m::ms) bs u x ω)
    =ᵐ[familyCascadeLaw (m::ms).length ν]
      weightedMarkedPartitionNumerator m η
        (fun z : E × FamilyCascadeTree E ms.length => Real.log (familyLeafTotal ms u (x+z.1) z.2).toReal)
        (familyWeightedBlocks ms bs u x) := by
  have htms := (List.pairwise_cons.mp hms).2
  have ht01 : ∀ a ∈ ms, 0 < a ∧ a < 1 := fun a ha => h01 a (by simp [ha])
  let τ := familyCascadeLaw ms.length (fun j => ν (j+1))
  let := hν 0
  let := familyCascadeLaw_probability ms.length (fun j => ν (j+1)) (fun j => hν (j+1))
  have hemark : ∀ᵐ z ∂(ν 0).prod τ,
      ENNReal.ofReal (Real.exp (Real.log (familyLeafTotal ms u (x+z.1) z.2).toReal)) =
        familyLeafTotal ms u (x+z.1) z.2 := by
    filter_upwards [familyChildTotal_positive_ae ms htms ht01 ν hν hu hi.2 x] with z hz
    rw [Real.exp_log (ENNReal.toReal_pos hz.1.ne' hz.2.ne),ENNReal.ofReal_toReal hz.2.ne]
  have hmarks := ae_pointCloud_marks ((ν 0).prod τ) hemark
  filter_upwards [familyLeafTotal_positive_ae (m::ms) hms h01 ν hν hu hi x,
    familyTotal_expMarked_ae ms htms ht01 ν hν hu hi.2 m x,hmarks] with ω hp he hω
  have hm := ae_cloud_measure_marks (ω := (ω : PointCloud (E × FamilyCascadeTree E ms.length)))
    (p := fun z => ENNReal.ofReal (Real.exp (Real.log (familyLeafTotal ms u (x+z.1) z.2).toReal)) =
      familyLeafTotal ms u (x+z.1) z.2) hω
  have hfactor : distinctCloudIntegral
      (bs.map (fun b (z : ℝ × (E × FamilyCascadeTree E ms.length)) =>
        (ENNReal.ofReal (z.1^(-1/m))*familyLeafTotal ms u (x+z.2.1) z.2.2)^
          (replicaPatternSize ms.length (markedReplicaShape ms.length b))*
            familyReplicaWeight ms b u (x+z.2.1) z.2.2))
      (pointCloudMeasure ω) [] =
      distinctCloudIntegral ((familyWeightedBlocks ms bs u x).map
        (fun b => weightedMarkedBlock m
          (fun z : E × FamilyCascadeTree E ms.length =>
            Real.log (familyLeafTotal ms u (x+z.1) z.2).toReal) b.1 b.2))
        (pointCloudMeasure ω) [] := by
    simp only [familyWeightedBlocks,List.map_map,Function.comp_def]
    apply distinctCloudIntegral_congr_ae
    intro b hb
    filter_upwards [hm] with z hz
    simp only [weightedMarkedBlock,expMarkedJump,hz]
  have hpow : ENNReal.ofReal ((familyLeafTotal (m::ms) u x ω).toReal^η) *
      ENNReal.ofReal ((familyLeafTotal (m::ms) u x ω).toReal^
        (-(replicaPatternSize (ms.length+1) (markedReplicaShape (ms.length+1) bs):ℝ))) =
      ENNReal.ofReal ((expMarkedTotal m
        (fun z : E × FamilyCascadeTree E ms.length =>
          Real.log (familyLeafTotal ms u (x+z.1) z.2).toReal) ω).toReal^
            (η-(((familyWeightedBlocks ms bs u x).map Prod.fst).sum:ℝ))) := by
    rw [←ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg _),
      ←Real.rpow_add (ENNReal.toReal_pos hp.1.ne' hp.2.ne),he]
    congr 1
    simp only [replicaPatternSize,markedReplicaShape,familyWeightedBlocks,List.map_map,
      Function.comp_def,sub_eq_add_neg]
  change ENNReal.ofReal ((familyLeafTotal (m::ms) u x ω).toReal^η) *
    (ENNReal.ofReal ((familyLeafTotal (m::ms) u x ω).toReal^
      (-(replicaPatternSize (ms.length+1) (markedReplicaShape (ms.length+1) bs):ℝ))) * _) = _
  rw [←mul_assoc,hpow,hfactor]
  rfl
end MicroscopicJamming

end

end OAI
