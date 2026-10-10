import Mathlib
import OAI.Probability.IsingPerceptron.GaussianVariance

namespace OAI

/-! Gaussian Gibbs. -/

noncomputable section

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators Topology
variable {S : Type*} [Fintype S] [Nonempty S]

omit [Nonempty S] in
lemma finiteFunction_bound (V : S → ℝ) (x : S) : |V x| ≤ ∑y,|V y| :=
  Finset.single_le_sum (fun y _ => abs_nonneg (V y)) (Finset.mem_univ x)

lemma finiteGibbs_const (H : S → ℝ) (c : ℝ) : finiteGibbs H (fun _ => c)=c := by
  rw [finiteGibbs,← Finset.sum_mul,mul_div_cancel_left₀ _ (finiteGibbs_den_pos H).ne']

omit [Nonempty S] in
lemma finiteGibbs_sub (H V W : S → ℝ) :
    finiteGibbs H (fun x => V x-W x)=finiteGibbs H V-finiteGibbs H W := by
  simp only [finiteGibbs,mul_sub,Finset.sum_sub_distrib,sub_div]

def gaussianLinear {m : ℕ} (A : S → Fin (m+1) → ℝ) (g : Fin (m+1) → ℝ) (x : S) : ℝ :=
  ∑i,g i*A x i

def gaussianGibbsH {m : ℕ} (W : S → ℝ) (A : S → Fin (m+1) → ℝ)
    (t : ℝ) (g : Fin (m+1) → ℝ) (x : S) : ℝ := W x+t*gaussianLinear A g x

omit [Fintype S] [Nonempty S] in
lemma gaussianLinear_derivative {m : ℕ} (A : S → Fin (m+1) → ℝ)
    (i : Fin (m+1)) (y : Fin m → ℝ) (x : S) (u : ℝ) :
    HasDerivAt (fun u => gaussianLinear A (i.insertNth u y) x) (A x i) u := by
  have he : (fun u => gaussianLinear A (i.insertNth u y) x)=
      fun u => u*A x i+∑j,y j*A x (i.succAbove j) := by
    funext u
    unfold gaussianLinear
    rw [Fin.sum_univ_succAbove _ i]
    simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
  rw [he]
  simpa using ((hasDerivAt_id u).mul_const (A x i)).add_const
    (∑j,y j*A x (i.succAbove j))

omit [Nonempty S] in
lemma gaussianGibbs_measurable {m : ℕ} (W V : S → ℝ)
    (A : S → Fin (m+1) → ℝ) (t : ℝ) :
    Measurable (fun g => finiteGibbs (gaussianGibbsH W A t g) V) := by
  apply finiteGibbs_measurable <;> intro x
  · dsimp only [gaussianGibbsH,gaussianLinear]; fun_prop
  · exact measurable_const

lemma gaussianGibbs_integrable {m : ℕ} (W V : S → ℝ)
    (A : S → Fin (m+1) → ℝ) (t : ℝ) :
    Integrable (fun g => finiteGibbs (gaussianGibbsH W A t g) V)
      (Measure.pi (fun _ => gaussianReal 0 1)) :=
  bounded_integrable _ (gaussianGibbs_measurable W V A t)
    (fun _ => finiteGibbs_abs _ _ (finiteFunction_bound V))

lemma gaussianGibbs_derivative {m : ℕ} (W V : S → ℝ)
    (A : S → Fin (m+1) → ℝ) (t : ℝ) (i : Fin (m+1)) (y : Fin m → ℝ) (u : ℝ) :
    HasDerivAt (fun u => finiteGibbs (gaussianGibbsH W A t (i.insertNth u y)) V)
      (t*(finiteGibbs (gaussianGibbsH W A t (i.insertNth u y)) (fun x => V x*A x i)-
        finiteGibbs (gaussianGibbsH W A t (i.insertNth u y)) V*
        finiteGibbs (gaussianGibbsH W A t (i.insertNth u y)) (fun x => A x i))) u := by
  apply (finiteGibbs_derivative
    (fun x => ((gaussianLinear_derivative A i y x u).const_mul t).const_add (W x))
    (fun x => hasDerivAt_const u (V x))).congr_deriv
  have he (x : S) : 0+V x*(t*A x i)=t*(V x*A x i) := by ring
  simp only [he,finiteGibbs_const_mul]
  change t*finiteGibbs (gaussianGibbsH W A t (i.insertNth u y)) (fun x => V x*A x i)-
    finiteGibbs (gaussianGibbsH W A t (i.insertNth u y)) V*
      (t*finiteGibbs (gaussianGibbsH W A t (i.insertNth u y)) (fun x => A x i)) = _
  ring

lemma gaussianGibbs_coordinate_ibp {m : ℕ} (W V : S → ℝ)
    (A : S → Fin (m+1) → ℝ) (t : ℝ) (i : Fin (m+1)) :
    (∫g,g i*finiteGibbs (gaussianGibbsH W A t g) V
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    ∫g,t*(finiteGibbs (gaussianGibbsH W A t g) (fun x => V x*A x i)-
      finiteGibbs (gaussianGibbsH W A t g) V*
      finiteGibbs (gaussianGibbsH W A t g) (fun x => A x i))
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  apply gaussian_pi_integration_by_parts i (gaussianGibbs_measurable W V A t)
    (measurable_const.mul ((gaussianGibbs_measurable W (fun x => V x*A x i) A t).sub
      ((gaussianGibbs_measurable W V A t).mul
        (gaussianGibbs_measurable W (fun x => A x i) A t))))
    (fun g => finiteGibbs_abs _ _ (finiteFunction_bound V))
    (E:=|t| *((∑x,|V x*A x i|)+(∑x,|V x|)*(∑x,|A x i|)))
  · intro g
    simp only [Pi.mul_apply,Pi.sub_apply]
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg t)
    calc _ ≤ |finiteGibbs (gaussianGibbsH W A t g) (fun x => V x*A x i)|+
        |finiteGibbs (gaussianGibbsH W A t g) V| *
        |finiteGibbs (gaussianGibbsH W A t g) (fun x => A x i)| := by
          simpa only [abs_mul] using abs_sub
            (finiteGibbs (gaussianGibbsH W A t g) (fun x => V x*A x i))
            (finiteGibbs (gaussianGibbsH W A t g) V*
              finiteGibbs (gaussianGibbsH W A t g) (fun x => A x i))
      _ ≤ _ := add_le_add (finiteGibbs_abs _ _ (finiteFunction_bound _))
        (mul_le_mul (finiteGibbs_abs _ _ (finiteFunction_bound _))
          (finiteGibbs_abs _ _ (finiteFunction_bound _)) (abs_nonneg _)
          (Finset.sum_nonneg (fun x _ => abs_nonneg _)))
  · exact gaussianGibbs_derivative W V A t i

theorem gaussianGibbs_ibp {m : ℕ} (W D : S → ℝ)
    (A B : S → Fin (m+1) → ℝ) (t : ℝ) :
    (∫g,finiteGibbs (gaussianGibbsH W A t g)
      (fun x => D x*gaussianLinear B g x) ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    ∫g,t*(finiteGibbs (gaussianGibbsH W A t g) (fun x => D x*∑i,B x i*A x i)-
      finiteGibbsPair (gaussianGibbsH W A t g) (fun x y => D x*∑i,B x i*A y i))
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  let μ : Measure (Fin (m+1) → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
  have hi (i : Fin (m+1)) : Integrable (fun g => g i*
      finiteGibbs (gaussianGibbsH W A t g) (fun x => D x*B x i)) μ :=
    (integrable_comp_eval (i:=i) (μ:=fun _ => gaussianReal 0 1) IsGaussian.integrable_id).mul_bdd
      (gaussianGibbs_measurable W (fun x => D x*B x i) A t).aestronglyMeasurable
      (ae_of_all _ fun g => finiteGibbs_abs _ _ (finiteFunction_bound _))
  have hiD (i : Fin (m+1)) : Integrable (fun g => t*(
      finiteGibbs (gaussianGibbsH W A t g) (fun x => (D x*B x i)*A x i)-
      finiteGibbs (gaussianGibbsH W A t g) (fun x => D x*B x i)*
      finiteGibbs (gaussianGibbsH W A t g) (fun x => A x i))) μ :=
    ((gaussianGibbs_integrable W _ A t).sub
      ((gaussianGibbs_integrable W _ A t).mul_bdd
        (gaussianGibbs_measurable W _ A t).aestronglyMeasurable
        (ae_of_all _ fun g => finiteGibbs_abs _ _ (finiteFunction_bound _)))).const_mul t
  have hs := Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl
    (fun i _ => gaussianGibbs_coordinate_ibp W (fun x => D x*B x i) A t i)
  rw [← integral_finsetSum _ (fun i _ => hi i),
    ← integral_finsetSum _ (fun i _ => hiD i)] at hs
  calc
    _ = ∫g,∑i,g i*finiteGibbs (gaussianGibbsH W A t g) (fun x => D x*B x i) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with g
      have he (x : S) : D x*gaussianLinear B g x=∑i,g i*(D x*B x i) := by
        unfold gaussianLinear
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _; ring
      simp only [he,finiteGibbs_sum,finiteGibbs_const_mul]
    _ = _ := hs
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with g
      simp only [finiteGibbsPair,Finset.mul_sum,finiteGibbs_sum,
        finiteGibbs_const_mul]
      rw [← Finset.mul_sum,Finset.sum_sub_distrib]
      congr 1
      apply congrArg₂ (· - ·) <;> apply Finset.sum_congr rfl <;> intro i _
      · congr 1; funext x; ring
      · simp only [← mul_assoc,finiteGibbs_mul_const]

end IsingPerceptron.Main

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators Topology
variable {S I : Type*} [Fintype S] [Nonempty S] [Fintype I] [DecidableEq I]

def replicasEnergy (H : S → ℝ) (x : I → S) : ℝ := ∑l,H (x l)

def replicatedGibbs (H : S → ℝ) (D : (I → S) → ℝ) : ℝ :=
  finiteGibbs (replicasEnergy H) D

omit [Nonempty S] in
lemma replicatedGibbs_product (H : S → ℝ) (V : I → S → ℝ) :
    replicatedGibbs H (fun x => ∏i,V i (x i))=∏i,finiteGibbs H (V i) := by
  unfold replicatedGibbs finiteGibbs replicasEnergy
  simp only [exp_sum,← Finset.prod_mul_distrib,Finset.prod_div_distrib]
  rw [Fintype.prod_sum (fun i x => exp (H x)*V i x),
    Fintype.prod_sum (fun _ : I => fun x => exp (H x))]

lemma replicatedGibbs_marginal (H V : S → ℝ) (i : I) :
    replicatedGibbs H (fun x : I → S => V (x i))=finiteGibbs H V := by
  have h := replicatedGibbs_product H (fun l x => if l=i then V x else 1)
  have hl (x : I → S) : (∏l,if l=i then V (x l) else (1:ℝ))=V (x i) := by simp
  have hr (l : I) : finiteGibbs H (fun x => if l=i then V x else 1)=
      if l=i then finiteGibbs H V else 1 := by split <;> simp_all [finiteGibbs_const]
  simpa only [hl,hr,Finset.prod_ite_eq',Finset.mem_univ,ite_true] using h

def gaussianCoefficientCov {m : ℕ} (A : S → Fin (m+1) → ℝ) (x y : S) : ℝ :=
  ∑i,A x i*A y i

omit [Fintype S] [Nonempty S] [DecidableEq I] in
lemma replicas_gaussian_hamiltonian {m : ℕ} (W : S → ℝ)
    (A : S → Fin (m+1) → ℝ) (t : ℝ) (g : Fin (m+1) → ℝ) :
    gaussianGibbsH (replicasEnergy W) (fun x : I → S => fun i => ∑l,A (x l) i) t g=
      replicasEnergy (gaussianGibbsH W A t g) := by
  funext x
  dsimp only [gaussianGibbsH,replicasEnergy,gaussianLinear]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  congr 1
  rw [Finset.mul_sum]
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

theorem replicated_gaussian_ibp {m : ℕ} (W : S → ℝ) (D : (I → S) → ℝ)
    (A : S → Fin (m+1) → ℝ) (t : ℝ) (head : I) :
    (∫g,replicatedGibbs (gaussianGibbsH W A t g)
      (fun x => D x*gaussianLinear A g (x head)) ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    ∫g,t*(replicatedGibbs (gaussianGibbsH W A t g)
      (fun x => D x*∑l,gaussianCoefficientCov A (x head) (x l))-
      (Fintype.card I:ℝ)*replicatedGibbs (gaussianGibbsH W A t g)
      (fun x => finiteGibbs (gaussianGibbsH W A t g)
        (fun z => D x*gaussianCoefficientCov A (x head) z)))
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  have h := gaussianGibbs_ibp (replicasEnergy W) D
    (fun x : I → S => fun i => ∑l,A (x l) i) (fun x i => A (x head) i) t
  simp only [replicas_gaussian_hamiltonian] at h
  refine h.trans ?_
  apply integral_congr_ae
  filter_upwards [] with g
  let H := gaussianGibbsH W A t g
  have hc (x y : I → S) : (∑i,A (x head) i*(∑l,A (y l) i))=
      ∑l,gaussianCoefficientCov A (x head) (y l) := by
    simp only [Finset.mul_sum,gaussianCoefficientCov]
    exact Finset.sum_comm
  simp only [hc]
  have hp (x : I → S) : finiteGibbs (replicasEnergy H)
      (fun y : I → S => D x*∑l,gaussianCoefficientCov A (x head) (y l))=
      (Fintype.card I:ℝ)*finiteGibbs H (fun z => D x*gaussianCoefficientCov A (x head) z) := by
    simp only [Finset.mul_sum,finiteGibbs_sum]
    have hm (l : I) : finiteGibbs (replicasEnergy H)
        (fun y : I → S => D x*gaussianCoefficientCov A (x head) (y l))=
        finiteGibbs H (fun z => D x*gaussianCoefficientCov A (x head) z) :=
      replicatedGibbs_marginal H (fun z => D x*gaussianCoefficientCov A (x head) z) l
    simp only [hm,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  change t*(finiteGibbs (replicasEnergy H) _-
    finiteGibbs (replicasEnergy H) (fun x => finiteGibbs (replicasEnergy H) _))=_
  simp only [hp,finiteGibbs_const_mul,replicatedGibbs]
  rfl

end IsingPerceptron.Main

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Filter Set Matrix Complex
open scoped BigOperators Topology Classical MatrixOrder RealInnerProductSpace Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance gaussianGibbsMatrixMeasurableSpace : MeasurableSpace (Matrix ι ι ℝ) := borel _
local instance gaussianGibbsMatrixBorelSpace : BorelSpace (Matrix ι ι ℝ) := ⟨rfl⟩

instance mvGaussian_probability (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    IsProbabilityMeasure (multivariateGaussian m S) := by
  unfold multivariateGaussian
  infer_instance

theorem multivariateGaussian_tendsto {m : ℕ → EuclideanSpace ℝ ι} {m₀ : EuclideanSpace ℝ ι}
    {S : ℕ → Matrix ι ι ℝ} {S₀ : Matrix ι ι ℝ}
    (hm : Tendsto m atTop (𝓝 m₀)) (hS : Tendsto S atTop (𝓝 S₀))
    (hpos : ∀n,(S n).PosSemidef) (hpos₀ : S₀.PosSemidef) :
    Tendsto (fun n => (⟨multivariateGaussian (m n) (S n),inferInstance⟩ :
      ProbabilityMeasure (EuclideanSpace ℝ ι))) atTop
    (nhds (X:=ProbabilityMeasure (EuclideanSpace ℝ ι)) ⟨multivariateGaussian m₀ S₀,inferInstance⟩) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  simp only [ProbabilityMeasure.coe_mk,charFun_multivariateGaussian (hpos _),
    charFun_multivariateGaussian hpos₀]
  have hinner : Tendsto (fun n => ⟪t,m n⟫) atTop (𝓝 ⟪t,m₀⟫) :=
    tendsto_const_nhds.inner hm
  have hquad : Tendsto (fun n => t ⬝ᵥ (S n)*ᵥ t) atTop (𝓝 (t ⬝ᵥ S₀*ᵥ t)) := by
    exact (show Continuous (fun A : Matrix ι ι ℝ => t ⬝ᵥ A*ᵥ t) from by
      unfold dotProduct Matrix.mulVec; fun_prop).continuousAt.tendsto.comp hS
  exact Complex.continuous_exp.continuousAt.tendsto.comp
    ((Complex.continuous_ofReal.continuousAt.tendsto.comp hinner).mul_const I |>.sub
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp hquad).div_const 2))

theorem gaussian_test_tendsto {m : ℕ → EuclideanSpace ℝ ι} {m₀ : EuclideanSpace ℝ ι}
    {S : ℕ → Matrix ι ι ℝ} {S₀ : Matrix ι ι ℝ}
    (hm : Tendsto m atTop (𝓝 m₀)) (hS : Tendsto S atTop (𝓝 S₀))
    (hpos : ∀n,(S n).PosSemidef) (hpos₀ : S₀.PosSemidef)
    (F : BoundedContinuousFunction (EuclideanSpace ℝ ι) ℝ) :
    Tendsto (fun n => ∫x,F x ∂multivariateGaussian (m n) (S n)) atTop
      (𝓝 (∫x,F x ∂multivariateGaussian m₀ S₀)) :=
  ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (multivariateGaussian_tendsto hm hS hpos hpos₀) F

abbrev CovarianceMatrix (ι : Type*) [Fintype ι] := {S : Matrix ι ι ℝ // S.PosSemidef}

lemma probability_dirac_tendsto {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [T1Space X] {x : ℕ → X} {x₀ : X} (hx : Tendsto x atTop (𝓝 x₀)) :
    Tendsto (fun n => (⟨Measure.dirac (x n),inferInstance⟩ : ProbabilityMeasure X)) atTop
      (nhds (X:=ProbabilityMeasure X) ⟨Measure.dirac x₀,inferInstance⟩) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  simpa only [ProbabilityMeasure.coe_mk,integral_dirac,Function.comp_def] using F.continuous.continuousAt.tendsto.comp hx

theorem gaussian_mixed_test_continuous {X : Type*} [MetricSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (F : BoundedContinuousFunction (X × EuclideanSpace ℝ ι) ℝ) :
    Continuous (fun p : X × CovarianceMatrix ι =>
      ∫y,F (p.1,y) ∂multivariateGaussian 0 p.2.val) := by
  apply continuous_iff_seqContinuous.mpr
  intro p p₀ hp
  let D : ℕ → ProbabilityMeasure X := fun n => ⟨Measure.dirac (p n).1,inferInstance⟩
  let D₀ : ProbabilityMeasure X := ⟨Measure.dirac p₀.1,inferInstance⟩
  let G : ℕ → ProbabilityMeasure (EuclideanSpace ℝ ι) := fun n =>
    ⟨multivariateGaussian 0 (p n).2.val,inferInstance⟩
  let G₀ : ProbabilityMeasure (EuclideanSpace ℝ ι) :=
    ⟨multivariateGaussian 0 p₀.2.val,inferInstance⟩
  have hX : Tendsto D atTop (𝓝 D₀) := probability_dirac_tendsto hp.fst_nhds
  have hG : Tendsto G atTop (𝓝 G₀) :=
    multivariateGaussian_tendsto (m:=fun _ => 0) tendsto_const_nhds
      (continuous_subtype_val.continuousAt.tendsto.comp hp.snd_nhds)
      (fun n => (p n).2.property) p₀.2.property
  have hprod : Tendsto (fun n => (D n).prod (G n)) atTop (𝓝 (D₀.prod G₀)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp (hX.prodMk_nhds hG)
  have hF := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hprod F
  simpa only [D,G,D₀,G₀,ProbabilityMeasure.prod,ProbabilityMeasure.coe_mk,
    integral_prod (f:=F) (F.integrable _),integral_dirac,Function.comp_def] using hF

theorem gaussian_mixed_test_limit {X : Type*} [MetricSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    {μ : ℕ → ProbabilityMeasure (X × CovarianceMatrix ι)}
    {μ₀ : ProbabilityMeasure (X × CovarianceMatrix ι)}
    (hμ : Tendsto μ atTop (𝓝 μ₀))
    (F : BoundedContinuousFunction (X × EuclideanSpace ℝ ι) ℝ) :
    Tendsto (fun n => ∫p : X × CovarianceMatrix ι,(∫y,F (p.1,y) ∂multivariateGaussian 0 p.2.val) ∂(μ n : Measure (X × CovarianceMatrix ι)))
      atTop (𝓝 (∫p : X × CovarianceMatrix ι,(∫y,F (p.1,y) ∂multivariateGaussian 0 p.2.val) ∂(μ₀ : Measure (X × CovarianceMatrix ι)))) := by
  let G : BoundedContinuousFunction (X × CovarianceMatrix ι) ℝ :=
    BoundedContinuousFunction.mkOfBound
      ⟨_,gaussian_mixed_test_continuous F⟩ (2*‖F‖) (by
        intro p q
        have hb (s : X × CovarianceMatrix ι) :
            ‖∫y,F (s.1,y) ∂multivariateGaussian 0 s.2.val‖≤‖F‖ := by
          simpa using norm_integral_le_of_norm_le_const
            (μ:=multivariateGaussian (0 : EuclideanSpace ℝ ι) s.2.val)
            (ae_of_all _ fun y => F.norm_coe_le_norm (s.1,y))
        calc dist (∫y,F (p.1,y) ∂multivariateGaussian 0 p.2.val) (∫y,F (q.1,y) ∂multivariateGaussian 0 q.2.val) ≤
            ‖∫y,F (p.1,y) ∂multivariateGaussian 0 p.2.val‖+
            ‖∫y,F (q.1,y) ∂multivariateGaussian 0 q.2.val‖ := dist_le_norm_add_norm _ _
          _ ≤ 2*‖F‖ := by linarith [hb p,hb q])
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ G

end IsingPerceptron.Main

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators Topology RealInnerProductSpace MatrixOrder
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem gaussian_matrix_image (A : Matrix ι κ ℝ) :
    (stdGaussian (EuclideanSpace ℝ κ)).map
      (Matrix.toEuclideanLin A).toContinuousLinearMap =
      multivariateGaussian 0 (A * A.transpose) := by
  let L := (Matrix.toEuclideanLin A).toContinuousLinearMap
  have hpos : (A*A.transpose).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial,transpose_transpose] using
      Matrix.posSemidef_conjTranspose_mul_self A.conjTranspose
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id]
    simp
  rw [← ContinuousLinearMap.toBilinForm_inj]
  apply LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun ι ℝ).toBasis
  intro i j
  have hadj (i : ι) (k : κ) : (L.adjoint (EuclideanSpace.basisFun ι ℝ i)) k=A i k := by
    have he := L.adjoint_inner_left (EuclideanSpace.basisFun κ ℝ k)
      (EuclideanSpace.basisFun ι ℝ i)
    simpa [L,PiLp.inner_apply,Matrix.toEuclideanLin,Matrix.toLpLin_apply] using he
  simp only [ContinuousLinearMap.toBilinForm_apply]
  change covarianceBilin ((stdGaussian (EuclideanSpace ℝ κ)).map L)
    (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ j) = _
  rw [covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_stdGaussian,
    innerSL_apply_apply, covarianceBilin_multivariateGaussian hpos]
  simp only [PiLp.inner_apply,hadj]
  simp [Matrix.mul_apply,mul_comm]

def freshRowLaw (N : ℕ) : Measure (Fin N → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)

instance freshRowLaw_probability (N : ℕ) : IsProbabilityMeasure (freshRowLaw N) := by
  unfold freshRowLaw; infer_instance

def spinOverlap {N : ℕ} (x y : Spins N) : ℝ := (∑i,spin x i*spin y i)/(N:ℝ)

def freshPatternVector {N : ℕ} (x : ι → Spins N) (g : Fin N → ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun l => (∑i,g i*spin (x l) i)/Real.sqrt N)

theorem freshPattern_law {N : ℕ} (hN : 0<N) (x : ι → Spins N) :
    (freshRowLaw N).map (freshPatternVector x) =
      multivariateGaussian 0 (fun l m => spinOverlap (x l) (x m)) := by
  let A : Matrix ι (Fin N) ℝ := fun l i => spin (x l) i/Real.sqrt N
  have hmap : freshPatternVector x =
      (Matrix.toEuclideanLin A).toContinuousLinearMap ∘ WithLp.toLp 2 := by
    funext g
    change WithLp.toLp 2 _ = WithLp.toLp 2 _
    congr 1
    funext l
    change (∑i,g i*spin (x l) i)/Real.sqrt N =
      ∑i,(spin (x l) i/Real.sqrt N)*g i
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hcov : A*A.transpose = fun l m => spinOverlap (x l) (x m) := by
    ext l m
    have hs : (Real.sqrt (N:ℝ))^2=(N:ℝ) := Real.sq_sqrt (by positivity)
    change (∑i,(spin (x l) i/Real.sqrt N)*(spin (x m) i/Real.sqrt N)) =
      (∑i,spin (x l) i*spin (x m) i)/(N:ℝ)
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    rw [div_mul_div_comm,←sq,hs]
  rw [hmap,← Measure.map_map (by fun_prop) (by fun_prop)]
  change ((Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map (WithLp.toLp 2)).map _ = _
  rw [map_pi_eq_stdGaussian,gaussian_matrix_image,hcov]

end IsingPerceptron.Main

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators Topology

def tensorEnumeration {N : ℕ} (hN : 0<N) (j : ℕ) :
    Fin (N^j-1+1) ≃ (Fin j → Fin N) :=
  (Fintype.equivFinOfCardEq (by
    simp only [Fintype.card_fun,Fintype.card_fin]
    exact (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Nat.ne_of_gt hN)))).symm)).symm

def tensorCoefficient {N : ℕ} (hN : 0<N) (j : ℕ) (x : Spins N)
    (a : Fin (N^j-1+1)) : ℝ :=
  ∏k,spin x (tensorEnumeration hN j a k)/sqrt N

def tensorPerturbation {N : ℕ} (hN : 0<N) (j : ℕ)
    (g : Fin (N^j-1+1) → ℝ) (x : Spins N) : ℝ :=
  gaussianLinear (tensorCoefficient hN j) g x

lemma tensor_covariance {N : ℕ} (hN : 0<N) (j : ℕ) (x y : Spins N) :
    gaussianCoefficientCov (tensorCoefficient hN j) x y=(spinOverlap x y)^j := by
  unfold gaussianCoefficientCov tensorCoefficient
  rw [(tensorEnumeration hN j).sum_comp
    (fun a => (∏k,spin x (a k)/sqrt N)*(∏k,spin y (a k)/sqrt N))]
  simp only [← Finset.prod_mul_distrib]
  have hs : (sqrt (N:ℝ))^2=(N:ℝ) := sq_sqrt (by positivity)
  have he (i : Fin N) : (spin x i/sqrt N)*(spin y i/sqrt N)=
      (spin x i*spin y i)/(N:ℝ) := by rw [div_mul_div_comm,← sq,hs]
  simp only [he]
  rw [← Fintype.prod_sum (fun _ : Fin j => fun i : Fin N => (spin x i*spin y i)/(N:ℝ))]
  simp only [← Finset.sum_div,spinOverlap,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem actual_tensor_replica_ibp {N : ℕ} (hN : 0<N) (j : ℕ)
    (W : Spins N → ℝ) {I : Type*} [Fintype I] [DecidableEq I]
    (D : (I → Spins N) → ℝ) (t : ℝ) (head : I) :
    (∫g,replicatedGibbs (gaussianGibbsH W (tensorCoefficient hN j) t g)
      (fun x => D x*tensorPerturbation hN j g (x head))
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    ∫g,t*(replicatedGibbs (gaussianGibbsH W (tensorCoefficient hN j) t g)
      (fun x => D x*∑l,(spinOverlap (x head) (x l))^j)-
      (Fintype.card I:ℝ)*replicatedGibbs (gaussianGibbsH W (tensorCoefficient hN j) t g)
      (fun x => finiteGibbs (gaussianGibbsH W (tensorCoefficient hN j) t g)
        (fun z => D x*(spinOverlap (x head) z)^j)))
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  simpa only [tensor_covariance,tensorPerturbation] using
    replicated_gaussian_ibp W D (tensorCoefficient hN j) t head

variable {S : Type*} [Fintype S] [Nonempty S]

def finiteLogPartition (H : S → ℝ) : ℝ :=
  log ((∑x,exp (H x))/(Fintype.card S : ℝ))

def linearLogPartition {n : ℕ} (W : S → ℝ) (A : S → Fin n → ℝ)
    (g : Fin n → ℝ) : ℝ := finiteLogPartition (fun x => W x+∑i,g i*A x i)

omit [Nonempty S] in
lemma linearLogPartition_measurable {n : ℕ} (W : S → ℝ) (A : S → Fin n → ℝ) :
    Measurable (linearLogPartition W A) := by
  unfold linearLogPartition finiteLogPartition
  fun_prop

lemma linearLogPartition_coordinate {n : ℕ} (W : S → ℝ) (A : S → Fin n → ℝ)
    {c : Fin n → ℝ} (hc : ∀x i,|A x i|≤c i) :
    CoordinateLipschitz c (linearLogPartition W A) := by
  intro i g g' hgg
  apply finite_log_average_difference
  intro x
  have he : (W x+∑k,g k*A x k)-(W x+∑k,g' k*A x k)=(g i-g' i)*A x i := by
    rw [add_sub_add_left_eq_sub,← Finset.sum_sub_distrib,Finset.sum_eq_single i]
    · ring
    · intro k _ hki
      rw [hgg k hki,sub_self]
    · simp
  rw [he,abs_mul]
  exact (mul_le_mul_of_nonneg_left (hc x i) (abs_nonneg _)).trans_eq (mul_comm _ _)

lemma linearLogPartition_memLp {n : ℕ} (W : S → ℝ) (A : S → Fin n → ℝ)
    {c : Fin n → ℝ} (hc : ∀x i,|A x i|≤c i) :
    MemLp (linearLogPartition W A) 2 (Measure.pi (fun _ => gaussianReal 0 1)) := by
  exact coordinateLipschitz_memLp (linearLogPartition_measurable W A)
    (fun i => (abs_nonneg _).trans (hc (Classical.choice inferInstance) i))
    (linearLogPartition_coordinate W A hc)

theorem linearLogPartition_variance {n : ℕ} (W : S → ℝ) (A : S → Fin n → ℝ)
    {c : Fin n → ℝ} (hc : ∀x i,|A x i|≤c i) :
    variance (linearLogPartition W A) (Measure.pi (fun _ => gaussianReal 0 1))≤∑i,c i^2 := by
  exact gaussian_pi_variance_le (linearLogPartition_measurable W A)
    (fun i => (abs_nonneg _).trans (hc (Classical.choice inferInstance) i))
    (linearLogPartition_coordinate W A hc)

lemma tensorCoefficient_abs {N : ℕ} (hN : 0<N) (j : ℕ) (x : Spins N)
    (a : Fin (N^j-1+1)) : |tensorCoefficient hN j x a|=(1/sqrt N)^j := by
  unfold tensorCoefficient
  rw [Finset.abs_prod]
  have hs (i : Fin N) : |spin x i|=1 := by
    unfold spin
    split <;> norm_num
  simp only [abs_div,hs,abs_of_nonneg (sqrt_nonneg _),Finset.prod_const,
    Finset.card_univ,Fintype.card_fin]

lemma tensor_coordinate_squares {N : ℕ} (hN : 0<N) (j : ℕ) (t : ℝ) :
    (∑_a : Fin (N^j-1+1),(|t| *(1/sqrt N)^j)^2)=t^2 := by
  have hNr : (N:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hn : N^j-1+1=N^j := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Nat.ne_of_gt hN)))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hn,
    Nat.cast_pow,mul_pow,sq_abs,div_pow,one_pow]
  field_simp
  rw [← pow_mul, Nat.mul_comm j 2, pow_mul, sq_sqrt (Nat.cast_nonneg N)]
  ring

theorem tensor_logPartition_variance {N : ℕ} (hN : 0<N) (j : ℕ)
    (W : Spins N → ℝ) (t : ℝ) :
    variance (fun g => finiteLogPartition (gaussianGibbsH W (tensorCoefficient hN j) t g))
      (Measure.pi (fun _ => gaussianReal 0 1))≤t^2 := by
  have he : (fun g => finiteLogPartition (gaussianGibbsH W (tensorCoefficient hN j) t g))=
      linearLogPartition W (fun x a => t*tensorCoefficient hN j x a) := by
    funext g
    congr 1
    funext x
    simp only [gaussianGibbsH,gaussianLinear,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he]
  have h := linearLogPartition_variance W (fun x a => t*tensorCoefficient hN j x a)
    (c:=fun _ => |t| *(1/sqrt N)^j) (fun x a => by rw [abs_mul,tensorCoefficient_abs])
  simpa only [tensor_coordinate_squares hN j t] using h

end IsingPerceptron.Main

end

end OAI
