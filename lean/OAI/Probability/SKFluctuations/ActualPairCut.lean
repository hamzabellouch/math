import Mathlib
import OAI.Probability.SKFluctuations.ActualSpinMartingale

namespace OAI

/-! Actual Pair Cut. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

 
def actualPairCut (pre mid tail : List (GaussianStep ι)) (x : ι → ℝ) :
    ForwardPath (ι → ℝ) S (pre++(mid++tail)).length → (ι → ℝ) × (ι → ℝ) :=
  match pre with
  | [] => fun p => (x,actualCutField mid tail x p)
  | _::pre => fun p => actualPairCut pre mid tail (x+p.1) p.2

omit [Fintype ι] [Fintype S] [Nonempty S] [StandardBorelSpace S] in
theorem actualPairCut_measurable_joint (pre mid tail : List (GaussianStep ι)) :
    Measurable (fun p : (ι → ℝ) × ForwardPath (ι → ℝ) S (pre++(mid++tail)).length =>
      actualPairCut pre mid tail p.1 p.2) := by
  induction pre with
  | nil => exact measurable_fst.prodMk (actualCutField_measurable_joint mid tail)
  | cons st pre ih =>
    exact ih.comp ((measurable_fst.add (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))

omit [Fintype ι] [Fintype S] [Nonempty S] [StandardBorelSpace S] in
theorem actualPairCut_measurable (pre mid tail : List (GaussianStep ι)) (x : ι → ℝ) :
    Measurable (actualPairCut (S := S) pre mid tail x) :=
  (actualPairCut_measurable_joint pre mid tail).comp (measurable_const.prodMk measurable_id)

omit [Fintype ι] [Fintype S] [Nonempty S] [MeasurableSpace S] [StandardBorelSpace S] in
theorem bddSmooth0_tensor {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → ℝ} {g : F → ℝ}
    (hf : BddSmooth 0 f) (hg : BddSmooth 0 g) :
    BddSmooth 0 (fun p : E × F => f p.1*g p.2) := by
  obtain ⟨Cf,hCf,hfB⟩ := hf.bound
  obtain ⟨Cg,hCg,hgB⟩ := hg.bound
  refine ⟨(hf.continuous.comp continuous_fst).mul (hg.continuous.comp continuous_snd),
    Cf*Cg,mul_nonneg hCf hCg,?_⟩
  intro p
  rw [abs_mul]
  exact mul_le_mul (hfB p.1) (hgB p.2) (abs_nonneg _) hCf

theorem integrable_actualPairCut_tensor {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre mid tail : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++(mid++tail))) {F G : (ι → ℝ) → ℝ}
    (hF : BddSmooth 0 F) (hG : BddSmooth 0 G) (x : ι → ℝ) :
    Integrable (fun p => F (actualPairCut (S := S) pre mid tail x p).1*
      G (actualPairCut (S := S) pre mid tail x p).2)
      (hierarchyPathKernel w φ (pre++(mid++tail)) x) := by
  have := hierarchyPathKernel_markov hw φ (pre++(mid++tail)) ha
  exact (bddSmooth0_tensor hF hG).integrable_comp_measurable
    (actualPairCut_measurable pre mid tail x)

 
theorem integral_actualPairCut_tensor {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre mid tail : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++(mid++tail))) {F G : (ι → ℝ) → ℝ}
    (hF : BddSmooth 0 F) (hG : BddSmooth 0 G) (x : ι → ℝ) :
    (∫ p, F (actualPairCut (S := S) pre mid tail x p).1*
      G (actualPairCut (S := S) pre mid tail x p).2
      ∂hierarchyPathKernel w φ (pre++(mid++tail)) x) =
      prefixTest pre (gaussianHierarchy w φ (mid++tail))
        (fun y => F y*prefixTest mid (gaussianHierarchy w φ tail) G y) x := by
  induction pre generalizing a x with
  | nil =>
    simp only [List.nil_append,actualPairCut,prefixTest]
    rw [integral_const_mul,integral_actualCutField_test hw φ mid tail ha hG x]
  | cons st pre ih =>
    rcases st with ⟨m,q⟩
    have := plantedStepKernel_markov hw φ m q (pre++(mid++tail)) ha
    have := hierarchyPathKernel_markov hw φ (pre++(mid++tail)) ha.2.2.2
    have hf := integrable_actualPairCut_tensor hw φ ((m,q)::pre) mid tail ha hF hG x
    change Integrable (fun p : (ι → ℝ) × ForwardPath (ι → ℝ) S (pre++(mid++tail)).length =>
      F (actualPairCut pre mid tail (x+p.1) p.2).1*
      G (actualPairCut pre mid tail (x+p.1) p.2).2)
      ((plantedStepKernel w φ m q (pre++(mid++tail)) ⊗ₖ
        (hierarchyPathKernel w φ (pre++(mid++tail))).comap (fun p => p.1+p.2)
          (measurable_fst.add measurable_snd)) x) at hf
    change (∫ p : (ι → ℝ) × ForwardPath (ι → ℝ) S (pre++(mid++tail)).length,
      F (actualPairCut pre mid tail (x+p.1) p.2).1*
      G (actualPairCut pre mid tail (x+p.1) p.2).2 ∂
      ((plantedStepKernel w φ m q (pre++(mid++tail)) ⊗ₖ
        (hierarchyPathKernel w φ (pre++(mid++tail))).comap (fun p => p.1+p.2)
          (measurable_fst.add measurable_snd)) x)) = _
    rw [ProbabilityTheory.integral_compProd hf]
    simp only [Kernel.comap_apply]
    simp_rw [ih ha.2.2.2]
    rw [plantedStepKernel_eq_tilted hw φ m q (pre++(mid++tail)) ha x,
      integral_tiltedLaw (F := fun z => gaussianHierarchy w φ (pre++(mid++tail)) (x+z))
        ((gaussianHierarchy_continuous hw φ (pre++(mid++tail)) ha.2.2.2).comp
          (continuous_const.add continuous_id)).measurable
        (gaussianHierarchy_integrable hw φ (pre++(mid++tail)) ha.2.2.2 m q x)]
    simp only [prefixTest,prefixContinuation_hierarchy]
    rfl

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

 
theorem lipschitz_of_sourceJet {A : (ι → ℝ) → ℝ} {G : ι → (ι → ℝ) → ℝ}
    (hG : ∀ i, BddSmooth 0 (G i))
    (hd : ∀ x v t, HasDerivAt (fun s : ℝ => A (x+s • v))
      (∑ i, v i*G i (x+t • v)) t) : ∃ C, LipschitzWith C A := by
  choose K hK bK using fun i => (hG i).bound
  let C : ℝ≥0 := ⟨∑ i, K i, Finset.sum_nonneg fun i _ => hK i⟩
  refine ⟨C,lipschitzWith_iff_norm_sub_le.mpr fun x y => ?_⟩
  have hbound (z v : ι → ℝ) : |∑ i, v i*G i z| ≤ (C:ℝ)*‖v‖ := by
    calc
      _ ≤ ∑ i, |v i*G i z| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, K i*‖v‖ := Finset.sum_le_sum fun i _ => by
        rw [abs_mul,mul_comm (K i)]
        exact mul_le_mul (norm_le_pi_norm v i) (bK i z) (abs_nonneg _) (norm_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; rfl
  have hL : LipschitzWith ⟨(C:ℝ)*‖x-y‖,by positivity⟩ (fun s : ℝ => A (y+s • (x-y))) :=
    lipschitzWith_of_nnnorm_deriv_le (fun s => (hd y (x-y) s).differentiableAt)
      (fun s => by
        rw [(hd y (x-y) s).deriv]
        show |∑ i, (x-y) i*G i (y+s • (x-y))| ≤ (C:ℝ)*‖x-y‖
        exact hbound _ _)
  have hh := hL.norm_sub_le 1 0
  change ‖A (y+(1:ℝ) • (x-y))-A (y+(0:ℝ) • (x-y))‖ ≤ ((C:ℝ)*‖x-y‖)*‖(1:ℝ)-0‖ at hh
  simpa using hh

 

theorem hasDerivAt_integral_tested_scaledSource {n : ℕ} (J : HeatJet n)
    {a a' : ℝ → (Fin (n+1) → ℝ)} {l r A B t : ℝ} (ht : t ∈ Ioo l r)
    (ha : ∀ s ∈ Ioo l r, HasDerivAt a (a' s) s)
    (hA : ∀ s ∈ Ioo l r, ‖a s‖ ≤ A) (hB : ∀ s ∈ Ioo l r, ‖a' s‖ ≤ B)
    (m : ℝ) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => ∫ z, J.A (x+a s*z)*Real.exp (m*J.F (x+a s*z))
        ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1))
      (∫ z, (∑ i, (a' t*z) i*(J.A₁ i (x+a t*z)+m*J.A (x+a t*z)*J.G i (x+a t*z)))*
        Real.exp (m*J.F (x+a t*z))
        ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) t := by
  let ν := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
  have hν : ExponentialIncrement ν := exponentialIncrement_gaussian (fun _ => 1)
  obtain ⟨CA,hCA⟩ := lipschitz_of_sourceJet J.smoothA₁ J.derivA
  obtain ⟨KA,hKA,bKA⟩ := J.smoothA.bound
  choose K₁ hK₁ bK₁ using fun i => (J.smoothA₁ i).bound
  choose KG hKG bKG using fun i => (J.smoothG i).bound
  let K : ℝ := ∑ i, (K₁ i + |m| * KA * KG i)
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ =>
    add_nonneg (hK₁ i) (mul_nonneg (mul_nonneg (abs_nonneg m) hKA) (hKG i))
  have hBn : 0 ≤ B := (norm_nonneg _).trans (hB t ht)
  have hdF (s) (hs : s ∈ Ioo l r) (z : Fin (n+1) → ℝ) :
      HasDerivAt (fun u => J.F (x+a u*z)) (∑ i, (a' s*z) i*J.G i (x+a s*z)) s := by
    apply LipschitzWith.hasDerivAt_curve J.lipschitz (HasDerivAt.const_add x ((ha s hs).mul_const z))
    simpa only [zero_smul,add_zero] using J.derivF (x+a s*z) (a' s*z) 0
  have hdA (s) (hs : s ∈ Ioo l r) (z : Fin (n+1) → ℝ) :
      HasDerivAt (fun u => J.A (x+a u*z)) (∑ i, (a' s*z) i*J.A₁ i (x+a s*z)) s := by
    apply LipschitzWith.hasDerivAt_curve hCA (HasDerivAt.const_add x ((ha s hs).mul_const z))
    simpa only [zero_smul,add_zero] using J.derivA (x+a s*z) (a' s*z) 0
  have hb (s) (hs : s ∈ Ioo l r) (z : Fin (n+1) → ℝ) :
      |∑ i, (a' s*z) i*(J.A₁ i (x+a s*z)+m*J.A (x+a s*z)*J.G i (x+a s*z))| ≤ K*B*‖z‖ := by
    calc
      _ ≤ ∑ i, |(a' s*z) i| *|J.A₁ i (x+a s*z)+m*J.A (x+a s*z)*J.G i (x+a s*z)| := by
        simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (s := Finset.univ)
          (fun i => (a' s*z) i*(J.A₁ i (x+a s*z)+m*J.A (x+a s*z)*J.G i (x+a s*z)))
      _ ≤ ∑ i, B*‖z‖*(K₁ i+|m| *KA*KG i) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul _ _ (abs_nonneg _) (by positivity)
        · exact (norm_le_pi_norm (a' s*z) i).trans ((norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (hB s hs) (norm_nonneg _)))
        · apply (abs_add_le _ _).trans
          rw [abs_mul,abs_mul]
          exact add_le_add (bK₁ i _) (mul_le_mul (mul_le_mul_of_nonneg_left (bKA _) (abs_nonneg _))
            (bKG i _) (abs_nonneg _) (by positivity))
      _ = _ := by rw [← Finset.mul_sum]; dsimp [K]; ring
  have hP : ExpNormBounded (fun y => J.A y*Real.exp (m*J.F y)) :=
    (ExpNormBounded.exp_lipschitz J.lipschitz m).bdd_mul J.smoothA
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo l r) (bound := fun z => K*B*Real.exp (|m| *|J.F x|)*Real.exp ((|m| *J.C*A+1)*‖z‖))
    (Ioo_mem_nhds ht.1 ht.2) _ (hP.diagonal_integrable hν x (a t)) _ _ _ _).2
  · exact Eventually.of_forall fun s =>
      ((J.smoothA.continuous.comp (continuous_const.add (continuous_const.mul continuous_id))).mul
        ((J.lipschitz.continuous.comp (continuous_const.add (continuous_const.mul continuous_id))).const_mul m).rexp).aestronglyMeasurable
  · exact ((continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).const_mul (a' t i)).mul
        (((J.smoothA₁ i).continuous.comp (continuous_const.add (continuous_const.mul continuous_id))).add
          (((J.smoothA.continuous.comp (continuous_const.add (continuous_const.mul continuous_id))).const_mul m).mul
            ((J.smoothG i).continuous.comp (continuous_const.add (continuous_const.mul continuous_id)))))).mul
      ((J.lipschitz.continuous.comp (continuous_const.add (continuous_const.mul continuous_id))).const_mul m).rexp).aestronglyMeasurable
  · exact Eventually.of_forall fun z s hs => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
      have hE := exp_scaledSource_bound J.lipschitz m x (a s) z (hA s hs)
      have hz : ‖z‖ ≤ Real.exp ‖z‖ := by linarith [Real.add_one_le_exp ‖z‖]
      calc
        _ ≤ K*B*‖z‖*(Real.exp (|m| *|J.F x|)*Real.exp (|m| *J.C*A*‖z‖)) :=
          mul_le_mul (hb s hs z) hE (Real.exp_nonneg _) (by positivity)
        _ ≤ K*B*Real.exp ‖z‖*(Real.exp (|m| *|J.F x|)*Real.exp (|m| *J.C*A*‖z‖)) := by gcongr
        _ = _ := by rw [show (|m| *J.C*A+1)*‖z‖ = ‖z‖+|m| *J.C*A*‖z‖ by ring,Real.exp_add]; ring
  · exact (hν _).const_mul _
  · exact Eventually.of_forall fun z s hs => by
      apply ((hdA s hs z).mul (((hdF s hs z).const_mul m).exp)).congr_deriv
      simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

end SKFluctuations.GaussianCalculus

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 
def HeatJet.one {n : ℕ} (J : HeatJet n) : HeatJet n where
  F := J.F
  A := fun _ => 1
  G := J.G
  H := J.H
  A₁ := fun _ _ => 0
  A₂ := fun _ _ => 0
  C := J.C
  lipschitz := J.lipschitz
  smoothA := BddSmooth.const 0 1
  smoothG := J.smoothG
  smoothH := J.smoothH
  smoothA₁ := fun _ => BddSmooth.const 0 0
  smoothA₂ := fun _ => BddSmooth.const 0 0
  derivF := J.derivF
  derivG := J.derivG
  derivA := by intro x v t; simpa using hasDerivAt_const t (1:ℝ)
  derivA₁ := by intro i x t; exact hasDerivAt_const t 0

 

def HeatJet.testedInsertion {n : ℕ} (J : HeatJet n) (m : ℝ) (i : Fin (n+1))
    (y : Fin (n+1) → ℝ) : ℝ :=
  J.A₂ i y + 2*m*J.A₁ i y*J.G i y + J.A y*(m*J.H i y+m^2*(J.G i y)^2)

theorem HeatJet.smooth_testedInsertion {n : ℕ} (J : HeatJet n) (m : ℝ) (i : Fin (n+1)) :
    BddSmooth 0 (J.testedInsertion m i) := by
  unfold HeatJet.testedInsertion
  simpa only [pow_two] using
    ((J.smoothA₂ i).add (((J.smoothA₁ i).const_mul (2*m)).mul (J.smoothG i))).add
      (J.smoothA.mul (((J.smoothH i).const_mul m).add (((J.smoothG i).mul (J.smoothG i)).const_mul (m*m))))

end SKFluctuations.Hierarchy

namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem hasDerivAt_integral_diagonal_tested_heat {n : ℕ} (J : HeatJet n)
    {a a' : ℝ → (Fin (n+1) → ℝ)} {l r A B t : ℝ} (ht : t ∈ Ioo l r)
    (ha : ∀ s ∈ Ioo l r, HasDerivAt a (a' s) s)
    (hA : ∀ s ∈ Ioo l r, ‖a s‖ ≤ A) (hB : ∀ s ∈ Ioo l r, ‖a' s‖ ≤ B)
    (m : ℝ) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => ∫ z, J.A (x+a s*z)*Real.exp (m*J.F (x+a s*z))
        ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1))
      (∑ i, a t i*a' t i * (∫ z, J.testedInsertion m i (x+a t*z)*Real.exp (m*J.F (x+a t*z))
        ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1))) t := by
  let ν := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
  let P := fun y => Real.exp (m*J.F y)
  let P₁ := fun i y => (J.A₁ i y + m*J.A y*J.G i y)*P y
  let P₂ := fun i y => J.testedInsertion m i y*P y
  have hP : ExpNormBounded P := ExpNormBounded.exp_lipschitz J.lipschitz m
  have hB₁ (i) : BddSmooth 0 (fun y => J.A₁ i y + m*J.A y*J.G i y) :=
    (J.smoothA₁ i).add ((J.smoothA.const_mul m).mul (J.smoothG i))
  have hdP₁ (i) (y : Fin (n+1) → ℝ) (s : ℝ) :
      HasDerivAt (fun r : ℝ => P₁ i (y+r • Pi.single i 1))
        (P₂ i (y+s • Pi.single i 1)) s := by
    apply (((J.derivA₁ i y s).add (((J.derivA_coord i y s).const_mul m).mul (J.derivG i y s))).mul
      (((J.derivF_coord i y s).const_mul m).exp)).congr_deriv
    dsimp [P₂,P,HeatJet.testedInsertion]
    ring
  have hs (i) : (∫ z, z i*P₁ i (x+a t*z) ∂ν) =
      a t i*∫ z, P₂ i (x+a t*z) ∂ν :=
    standardGaussianVector_diagonal_stein i (hP.bdd_mul (hB₁ i))
      (hP.bdd_mul (J.smooth_testedInsertion m i)) (hdP₁ i) x (a t)
  have he : (∫ z, (∑ i, (a' t*z) i*(J.A₁ i (x+a t*z)+m*J.A (x+a t*z)*J.G i (x+a t*z)))*P (x+a t*z) ∂ν) =
      ∑ i, a' t i*(∫ z, z i*P₁ i (x+a t*z) ∂ν) := by
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ (fun i _ =>
      ((hP.bdd_mul (hB₁ i)).diagonal_coord_integrable (fun _ => 1) x (a t) i).const_mul (a' t i))]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      dsimp only
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [P₁]
      ring
  apply (hasDerivAt_integral_tested_scaledSource J ht ha hA hB m x).congr_deriv
  change (∫ z, (∑ i, (a' t*z) i*(J.A₁ i (x+a t*z)+m*J.A (x+a t*z)*J.G i (x+a t*z)))*P (x+a t*z) ∂ν) = _
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  rw [hs]
  dsimp [P₂,P,ν]
  ring

 

theorem hasDerivAt_diagonal_heat_test {n : ℕ} (J : HeatJet n)
    {a a' : ℝ → (Fin (n+1) → ℝ)} {l r A B t : ℝ} (ht : t ∈ Ioo l r)
    (ha : ∀ s ∈ Ioo l r, HasDerivAt a (a' s) s)
    (hA : ∀ s ∈ Ioo l r, ‖a s‖ ≤ A) (hB : ∀ s ∈ Ioo l r, ‖a' s‖ ≤ B)
    (m : ℝ) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m
        (fun z => J.F (x+a s*z)) (fun z => J.A (x+a s*z)))
      (∑ i, a t i*a' t i *
        (tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m
          (fun z => J.F (x+a t*z)) (fun z => J.testedInsertion m i (x+a t*z)) -
         tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m
          (fun z => J.F (x+a t*z)) (fun z => J.A (x+a t*z)) *
         tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m
          (fun z => J.F (x+a t*z)) (fun z => m*J.H i (x+a t*z)+m^2*(J.G i (x+a t*z))^2))) t := by
  let ν := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
  have hν : ExponentialIncrement ν := exponentialIncrement_gaussian (fun _ => 1)
  have hP : ExpNormBounded (fun y => Real.exp (m*J.F y)) := ExpNormBounded.exp_lipschitz J.lipschitz m
  have hpos : 0 < ∫ z, Real.exp (m*J.F (x+a t*z)) ∂ν :=
    partition_pos m (hP.diagonal_integrable hν x (a t))
  have hd := hasDerivAt_integral_diagonal_tested_heat J.one ht ha hA hB m x
  simp only [HeatJet.one,HeatJet.testedInsertion,one_mul,mul_zero,zero_mul,zero_add] at hd
  apply ((hasDerivAt_integral_diagonal_tested_heat J ht ha hA hB m x).div hd hpos.ne').congr_deriv
  unfold tiltedMean
  rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_sub_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [ν] at hpos
  field_simp

end SKFluctuations.GaussianCalculus

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 
def HeatJet.potentialInsertion {n : ℕ} (J : HeatJet n) (m : ℝ) (i : Fin (n+1))
    (y : Fin (n+1) → ℝ) : ℝ := m*J.H i y+m^2*(J.G i y)^2

theorem HeatJet.smooth_potentialInsertion {n : ℕ} (J : HeatJet n) (m : ℝ) (i : Fin (n+1)) :
    BddSmooth 0 (J.potentialInsertion m i) := by
  unfold HeatJet.potentialInsertion
  simpa only [pow_two] using ((J.smoothH i).const_mul m).add
    (((J.smoothG i).mul (J.smoothG i)).const_mul (m*m))

def HeatJet.signedVarianceRate {n : ℕ} (J : HeatJet n) (m : ℝ) (d q : Fin (n+1) → ℝ)
    (x : Fin (n+1) → ℝ) : ℝ :=
  ∑ i, (d i/2)*(varianceTest m J.F (J.testedInsertion m i) q x -
    varianceTest m J.F J.A q x * varianceTest m J.F (J.potentialInsertion m i) q x)

 

theorem hasDerivAt_signed_variance_test {n : ℕ} (J : HeatJet n)
    (q d : Fin (n+1) → ℝ) {t : ℝ} (ht : ∀ i, 0 < q i+t*d i)
    (m : ℝ) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => varianceTest m J.F J.A (fun i => q i+s*d i) x)
      (J.signedVarianceRate m d (fun i => q i+t*d i) x) t := by
  let a := fun s i => Real.sqrt (q i+s*d i)
  let a' := fun s i => d i/(2*Real.sqrt (q i+s*d i))
  have ha : Continuous a := continuous_pi fun i => (continuous_const.add (continuous_id.mul continuous_const)).sqrt
  have ha' : ContinuousAt a' t := continuousAt_pi.mpr fun i =>
    continuousAt_const.div (continuousAt_const.mul
      (continuousAt_const.add (continuousAt_id.mul continuousAt_const)).sqrt)
      (mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr (ht i)))
  have hp : ∀ᶠ s in 𝓝 t, ∀ i, 0 < q i+s*d i := by
    rw [eventually_all]
    intro i
    exact (continuousAt_const.add (continuousAt_id.mul continuousAt_const)).eventually
      (eventually_gt_nhds (ht i))
  have hA : ∀ᶠ s in 𝓝 t, ‖a s‖ ≤ ‖a t‖+1 :=
    (ha.continuousAt.norm.eventually (eventually_lt_nhds (lt_add_one _))).mono fun _ h => h.le
  have hB : ∀ᶠ s in 𝓝 t, ‖a' s‖ ≤ ‖a' t‖+1 :=
    (ha'.norm.eventually (eventually_lt_nhds (lt_add_one _))).mono fun _ h => h.le
  obtain ⟨l,r,htr,hlr⟩ := (hp.and (hA.and hB)).exists_Ioo_subset
  have haD (s) (hs : s ∈ Ioo l r) : HasDerivAt a (a' s) s := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa only [a, a', id_eq, one_mul] using
      (((hasDerivAt_id s).mul_const (d i)).const_add (q i)).sqrt ((hlr hs).1 i).ne'
  have hh := hasDerivAt_diagonal_heat_test J htr haD
    (fun s hs => (hlr hs).2.1) (fun s hs => (hlr hs).2.2) m x
  have he : (fun s => varianceTest m J.F J.A (fun i => q i+s*d i) x) =ᶠ[𝓝 t]
      (fun s => tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m
        (fun z => J.F (x+a s*z)) (fun z => J.A (x+a s*z))) := by
    filter_upwards [hp] with s hs
    exact varianceTest_eq J.lipschitz.continuous J.smoothA.continuous m (fun i => (hs i).le) x
  apply (hh.congr_of_eventuallyEq he).congr_deriv
  unfold HeatJet.signedVarianceRate
  apply Finset.sum_congr rfl
  intro i _
  rw [varianceTest_eq J.lipschitz.continuous (J.smooth_testedInsertion m i).continuous m (fun i => (ht i).le),
    varianceTest_eq J.lipschitz.continuous J.smoothA.continuous m (fun i => (ht i).le),
    varianceTest_eq J.lipschitz.continuous (J.smooth_potentialInsertion m i).continuous m (fun i => (ht i).le)]
  dsimp [a,a',HeatJet.potentialInsertion]
  rw [show Real.sqrt (q i+t*d i)*(d i/(2*Real.sqrt (q i+t*d i))) = d i/2 by
    field_simp [Real.sqrt_ne_zero'.mpr (ht i)]]

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem HeatJetFamily.continuous_testedInsertion {n : ℕ} (V : HeatJetFamily n) (m : ℝ)
    (i : Fin (n+1)) :
    Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => (V.J p.1).testedInsertion m i p.2) := by
  exact ((V.continuousA₂ i).add (((V.continuousA₁ i).const_mul (2*m)).mul (V.continuousG i))).add
    (V.continuousA.mul (((V.continuousH i).const_mul m).add (((V.continuousG i).pow 2).const_mul (m^2))))

theorem HeatJetFamily.bounded_testedInsertion {n : ℕ} (V : HeatJetFamily n) (m : ℝ)
    (i : Fin (n+1)) :
    AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => (V.J p.1).testedInsertion m i p.2) := by
  unfold HeatJet.testedInsertion
  simpa only [pow_two] using
    ((V.boundedA₂ i).add (((V.boundedA₁ i).const_mul (2*m)).mul (V.boundedG i))).add
      (V.boundedA.mul (((V.boundedH i).const_mul m).add (((V.boundedG i).mul (V.boundedG i)).const_mul (m*m))))

theorem HeatJetFamily.continuous_potentialInsertion {n : ℕ} (V : HeatJetFamily n) (m : ℝ)
    (i : Fin (n+1)) :
    Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => (V.J p.1).potentialInsertion m i p.2) := by
  exact ((V.continuousH i).const_mul m).add (((V.continuousG i).pow 2).const_mul (m^2))

theorem HeatJetFamily.bounded_potentialInsertion {n : ℕ} (V : HeatJetFamily n) (m : ℝ)
    (i : Fin (n+1)) :
    AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => (V.J p.1).potentialInsertion m i p.2) := by
  unfold HeatJet.potentialInsertion
  simpa only [pow_two] using ((V.boundedH i).const_mul m).add
    (((V.boundedG i).mul (V.boundedG i)).const_mul (m*m))

 

theorem hasDerivAt_dynamic_varianceTest {n : ℕ} (V : HeatJetFamily n)
    {D B : ℝ → (Fin (n+1) → ℝ) → ℝ}
    (hcD : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => D p.1 p.2))
    (hcB : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => B p.1 p.2))
    (hbD : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => D p.1 p.2))
    (hbB : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => B p.1 p.2))
    {l r : ℝ}
    (hdF : ∀ s ∈ Ioo l r, ∀ y, HasDerivAt (fun q => (V.J q).F y) (D s y) s)
    (hdA : ∀ s ∈ Ioo l r, ∀ y, HasDerivAt (fun q => (V.J q).A y) (B s y) s)
    (q d : Fin (n+1) → ℝ) {m t : ℝ} (ht : t ∈ Ioo l r)
    (hqt : ∀ i, 0 < q i+t*d i) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => varianceTest m (V.J s).F (V.J s).A (fun i => q i+s*d i) x)
      ((V.J t).signedVarianceRate m d (fun i => q i+t*d i) x +
        varianceTest m (V.J t).F (B t) (fun i => q i+t*d i) x +
        m*(varianceTest m (V.J t).F (fun y => (V.J t).A y*D t y) (fun i => q i+t*d i) x -
          varianceTest m (V.J t).F (V.J t).A (fun i => q i+t*d i) x *
            varianceTest m (V.J t).F (D t) (fun i => q i+t*d i) x)) t := by
  obtain ⟨KD,hKD,bD⟩ := hbD
  obtain ⟨KB,hKB,bB⟩ := hbB
  obtain ⟨KA,hKA,bA⟩ := V.boundedA
  let Q : ℝ × ℝ → Fin (n+1) → ℝ := fun p i => q i+p.1*d i
  have hQ : Continuous Q := continuous_pi fun i => continuous_const.add (continuous_fst.mul continuous_const)
  have hF' : ∀ p : ℝ × ℝ, LipschitzWith V.C (V.J p.2).F := fun p => V.lipschitz p.2
  have hcF' : Continuous (fun p : (ℝ × ℝ) × (Fin (n+1) → ℝ) => (V.J p.1.2).F p.2) :=
    V.continuousF.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hcont (A : ℝ → (Fin (n+1) → ℝ) → ℝ)
      (hcA : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => A p.1 p.2))
      (hbA : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => A p.1 p.2)) :
      Continuous (fun p : ℝ × ℝ => varianceTest m (V.J p.2).F (A p.2) (Q p) x) := by
    obtain ⟨K,_,hb⟩ := hbA
    exact dynamic_varianceTest_continuous hF' hcF'
      (hcA.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
      (fun p y => hb (p.2,y)) m hQ continuous_const
  have hc₁ : Continuous (fun p : ℝ × ℝ => (V.J p.2).signedVarianceRate m d (Q p) x) := by
    apply continuous_finsetSum
    intro i _
    exact ((hcont (fun t => (V.J t).testedInsertion m i) (V.continuous_testedInsertion m i) (V.bounded_testedInsertion m i)).sub
      ((hcont (fun t => (V.J t).A) V.continuousA V.boundedA).mul
        (hcont (fun t => (V.J t).potentialInsertion m i) (V.continuous_potentialInsertion m i) (V.bounded_potentialInsertion m i)))).const_mul _
  have hc₂ : Continuous (fun p : ℝ × ℝ =>
      varianceTest m (V.J p.2).F (B p.2) (Q p) x+
        m*(varianceTest m (V.J p.2).F (fun y => (V.J p.2).A y*D p.2 y) (Q p) x-
          varianceTest m (V.J p.2).F (V.J p.2).A (Q p) x *
            varianceTest m (V.J p.2).F (D p.2) (Q p) x)) := by
    exact (hcont B hcB ⟨KB,hKB,bB⟩).add
      (((hcont (fun t y => (V.J t).A y*D t y) (V.continuousA.mul hcD) (V.boundedA.mul ⟨KD,hKD,bD⟩)).sub
        ((hcont (fun t => (V.J t).A) V.continuousA V.boundedA).mul (hcont D hcD ⟨KD,hKD,bD⟩))).const_mul m)
  have hp : ∀ᶠ s in 𝓝 t, ∀ i, 0 < q i+s*d i := by
    rw [eventually_all]
    intro i
    exact (continuousAt_const.add (continuousAt_id.mul continuousAt_const)).eventually
      (eventually_gt_nhds (hqt i))
  have hc₃ : ∀ᶠ p : ℝ × ℝ in 𝓝 (t,t),
      HasDerivAt (fun s => varianceTest m (V.J p.2).F (V.J p.2).A (fun i => q i+s*d i) x)
        ((V.J p.2).signedVarianceRate m d (Q p) x) p.1 := by
    filter_upwards [continuous_fst.continuousAt.tendsto.eventually hp] with p hp
    exact hasDerivAt_signed_variance_test (V.J p.2) q d hp m x
  have hc₄ : ∀ᶠ p : ℝ × ℝ in 𝓝 (t,t),
      HasDerivAt (fun s => varianceTest m (V.J s).F (V.J s).A (Q p) x)
        (varianceTest m (V.J p.2).F (B p.2) (Q p) x+
          m*(varianceTest m (V.J p.2).F (fun y => (V.J p.2).A y*D p.2 y) (Q p) x-
            varianceTest m (V.J p.2).F (V.J p.2).A (Q p) x *
              varianceTest m (V.J p.2).F (D p.2) (Q p) x)) p.2 := by
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds ht)] with p hp
    exact hasDerivAt_tiltedMean_local hp hKD (add_nonneg hKA hKB)
      (fun s _ => ((V.lipschitz s).continuous.comp (continuous_const.add continuous_id)).measurable)
      ((hcD.comp (continuous_const.prodMk (continuous_const.add continuous_id))).measurable)
      (fun s _ => ((V.J s).smoothA.continuous.comp (continuous_const.add continuous_id)).measurable)
      ((hcB.comp (continuous_const.prodMk (continuous_const.add continuous_id))).measurable)
      (fun s hs z => hdF s hs (x+z)) (fun s hs z => hdA s hs (x+z))
      (fun s _ z => bD (s,x+z))
      (fun s _ z => (bA (s,x+z)).trans (le_add_of_nonneg_right hKB))
      (fun s _ z => (bB (s,x+z)).trans (le_add_of_nonneg_left hKA)) m
      ((exponentialIncrement_gaussian (fun i => Real.toNNReal (Q p i))).integrable_shift (V.lipschitz p.2) m x)
  have hchain := hasDerivAt_bivariate_chain
    (f := fun a b => varianceTest m (V.J b).F (V.J b).A (fun i => q i+a*d i) x)
    (f₁ := fun a b => (V.J b).signedVarianceRate m d (fun i => q i+a*d i) x)
    (f₂ := fun a b => varianceTest m (V.J b).F (B b) (fun i => q i+a*d i) x+
      m*(varianceTest m (V.J b).F (fun y => (V.J b).A y*D b y) (fun i => q i+a*d i) x-
        varianceTest m (V.J b).F (V.J b).A (fun i => q i+a*d i) x *
          varianceTest m (V.J b).F (D b) (fun i => q i+a*d i) x))
    hc₃ hc₄ hc₁.continuousAt hc₂.continuousAt (hasDerivAt_id t) (hasDerivAt_id t)
  simpa only [id_eq,mul_one,add_assoc] using hchain

end SKFluctuations.Hierarchy

end

end OAI
