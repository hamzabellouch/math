import OAI.Analysis.PlaneSpectrum.RadialEnergy
import OAI.Analysis.PlaneSpectrum.SpectralMeasure

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable

def normF (z : E) : F := ⟨‖(z:ℂ)‖,mem_algebraicClosure_iff.mpr (by
  apply IsAlgebraic.of_pow (n := 2) (by decide)
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  have hr := mem_algebraicClosure_iff.mp (reF z).property
  have hi := mem_algebraicClosure_iff.mp (imF z).property
  exact (hr.mul hr).add (hi.mul hi))⟩
@[simp] lemma normF_coe (z : E) : ((normF z : F):ℝ) = ‖(z:ℂ)‖ := rfl
lemma normF_pos {z : E} (hz : z ≠ 0) : 0 < normF z := by
  change 0 < ‖(z:ℂ)‖
  exact norm_pos_iff.mpr (fun h => hz (Subtype.ext h))

variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
  (q : D → Y) (hq : Measurable q)
  [MulAction K Y] [MeasurableConstSMul K Y]
  (hqcov : ∀ k : K, ∀ᵐ d ∂μ, q (k • d) = k • q d)
  [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)]
include hq hqcov in
lemma projectedMass_vanish (hw : IsWild (DifferenceFourier.differenceLaw (μ.map q) (condDistrib id q μ)))
    (z : E) (hz : z ≠ 0) : projectedMass μ q z = 0 := by
  have hn : ‖(z:ℂ)‖ = ‖((ofF (normF z):E):ℂ)‖ := by
    rw [norm_ofF,normF_coe,abs_of_nonneg (norm_nonneg _)]
  rw [projectedMass_radial μ q hq hqcov hn]
  exact massReal_vanish μ q hq hqcov hw (normF z) (normF_pos hz)
include hq hqcov in
lemma fourier_vanish_of_terminal (hw : IsWild (DifferenceFourier.differenceLaw (μ.map q) (condDistrib id q μ)))
    (z : E) (hz : z ≠ 0) : ∫ d, (eval z d : ℂ) ∂μ = 0 := by
  have hn : ‖l2 μ (project μ q hq (char z))‖ = 0 := by
    rw [norm_project_l2]
    have he := projectedMass_vanish μ q hq hqcov hw z hz
    change ‖l2 (μ.map q) (conditional μ q (char z))‖^2 = 0 at he
    nlinarith [norm_nonneg (l2 (μ.map q) (conditional μ q (char z)))]
  have he : project μ q hq (char z) =ᵐ[μ] (0:Func D) :=
    (l2_eq_iff μ _ _).mp (by rw [map_zero]; exact norm_eq_zero.mp hn)
  change (∫ d, char z d ∂μ) = 0
  rw [← project_integral μ q hq]
  calc
    _ = ∫ d, (0:Func D) d ∂μ := integral_congr_ae he
    _ = 0 := by simp

lemma ergodic_wild_fourier (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
    (hw : IsWild μ) (z : E) (hz : z ≠ 0) : ∫ d, (eval z d : ℂ) ∂μ = 0 := by
  obtain ⟨q,hq,hqc,hgood,hmix⟩ := exists_terminal_factor μ
  have := hmix
  have hd : IsWild (DifferenceFourier.differenceLaw (μ.map q) (condDistrib id q μ)) := by
    refine ⟨relative_difference_invariant μ id q measurable_id hq (fun k => Eventually.of_forall (fun d => rfl)) hqc,?_⟩
    exact hgood id measurable_id (fun k => Eventually.of_forall (fun d => rfl)) (by simpa using hw)
  exact fourier_vanish_of_terminal μ q hq hqc hd z hz
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.Amenable.Mean
variable {G H : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
lemma vector_mem_closedConvexHull (M : Amenable.Mean G) (V : G →ᵇ H) :
    M.vector V ∈ closedConvexHull ℝ (Set.range V) := by
  by_contra hn
  obtain ⟨L,c,hL,hc⟩ := geometric_hahn_banach_closed_point convex_closedConvexHull isClosed_closedConvexHull hn
  have he : L (M.vector V) = M.map (L.compLeftContinuousBounded G V) := by
    rw [← M.vector_map]
    apply ext_inner_right ℝ
    intro x
    simp only [M.vector_pair, RCLike.inner_apply, conj_trivial]
    change M.map (pairing (L.compLeftContinuousBounded G V) x) = x * M.map (L.compLeftContinuousBounded G V)
    have hp : pairing (L.compLeftContinuousBounded G V) x = x • L.compLeftContinuousBounded G V := by
      ext g; simp [pairing_apply]
    rw [hp,map_smul]; rfl
  have hb : M.map (L.compLeftContinuousBounded G V) ≤ c := by
    rw [← M.map_const c]
    apply M.mono
    intro g
    exact le_of_lt (hL _ (subset_closedConvexHull (𝕜 := ℝ) (Set.mem_range_self g)))
  linarith
end EuclideanFiveColor.Amenable.Mean
namespace EuclideanFiveColor
structure ConvexAverage (G : Type*) where
  n : ℕ
  pt : Fin n → G
  weight : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  total : ∑ i, weight i = 1
namespace ConvexAverage
variable {G H : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
def apply (A : ConvexAverage G) (f : G → H) : H := ∑ i, A.weight i • f (A.pt i)
lemma norm_le (A : ConvexAverage G) (f : G → H) {C : ℝ} (hf : ∀ g, ‖f g‖ ≤ C) : ‖A.apply f‖ ≤ C := by
  calc
    _ ≤ ∑ i, ‖A.weight i • f (A.pt i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, A.weight i * C := Finset.sum_le_sum fun i _ => by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (A.nonneg i)]
      exact mul_le_mul_of_nonneg_left (hf _) (A.nonneg i)
    _ = C := by rw [← Finset.sum_mul,A.total,one_mul]
lemma of_mem_convexHull {f : G → H} {v : H} (hv : v ∈ convexHull ℝ (Set.range f)) :
    ∃ A : ConvexAverage G, A.apply f = v := by
  classical
  obtain ⟨ι,hi,w,z,hw,ht,hz,he⟩ := mem_convexHull_iff_exists_fintype.mp hv
  choose g hg using hz
  let e := (Fintype.equivFin ι).symm
  refine ⟨⟨Fintype.card ι,g ∘ e,w ∘ e,fun i => hw _,?_⟩,?_⟩
  · simpa only [Function.comp_apply] using (e.sum_comp w).trans ht
  · dsimp [apply]
    simp only [hg]
    exact (e.sum_comp (fun i => w i • z i)).trans he
end ConvexAverage
namespace Amenable.Mean
variable {G H : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
lemma exists_finite_approx (M : Mean G) (V : G →ᵇ H) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ConvexAverage G, ‖A.apply V - M.vector V‖ < ε := by
  have h := M.vector_mem_closedConvexHull V
  rw [closedConvexHull_eq_closure_convexHull] at h
  obtain ⟨v,hv,he⟩ := Metric.mem_closure_iff.mp h ε hε
  obtain ⟨A,rfl⟩ := ConvexAverage.of_mem_convexHull hv
  exact ⟨A,by simpa [dist_eq_norm,norm_sub_rev] using (show dist (M.vector V) (A.apply V) < ε from he)⟩
end Amenable.Mean
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor
namespace ConvexAverage
open BoundedMeasurable
variable {G X : Type*} [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X]
def bm (A : ConvexAverage G) (f : Func X) : Func X := ∑ i, A.weight i • act (A.pt i) f
lemma bm_apply (A : ConvexAverage G) (f : Func X) (x : X) : A.bm f x = A.apply (fun g => f (g +ᵥ x)) := by
  simp [bm,apply,Func,Finset.sum_apply]
lemma bm_bound (A : ConvexAverage G) (f : Func X) (x : X) : ‖A.bm f x‖ ≤ bound f := by
  rw [bm_apply]; exact A.norm_le _ (fun g => norm_le_bound f _)
variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
lemma l2_bm (A : ConvexAverage G) (f : Func X) :
    l2 μ (A.bm f) = A.apply (fun g => Amenable.Koopman.action μ g (l2 μ f)) := by
  simp only [bm,apply,map_sum,map_smul,l2_act]
end ConvexAverage
namespace InvariantSequence
open BoundedMeasurable
variable {G X : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [AddAction G X] [MeasurableConstVAdd G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
  (M : Amenable.Mean G)
def limit (f : Func X) : Lp ℂ 2 μ := M.vector (Amenable.Mean.orbit (Amenable.Koopman.action μ) (l2 μ f))
lemma limit_measurable (f : Func X) : Measurable (limit μ M f : X → ℂ) := (Lp.stronglyMeasurable _).measurable
lemma limit_fixed (f : Func X) (g : G) :
    (fun x => limit μ M f (g +ᵥ x)) =ᵐ[μ] (limit μ M f : X → ℂ) := by
  have h := M.vector_orbit_invariant (Amenable.Koopman.action μ) (Amenable.Koopman.action_add μ) (l2 μ f) g
  exact (Amenable.Koopman.coe_action μ g _).symm.trans (by rw [show Amenable.Koopman.action μ g (limit μ M f) = limit μ M f from h])
lemma exists_averages (f : Func X) : ∃ A : ℕ → ConvexAverage G,
    ∀ᵐ x ∂μ, Tendsto (fun n => A n |>.bm f x) atTop (𝓝 (limit μ M f x)) := by
  classical
  let V := Amenable.Mean.orbit (Amenable.Koopman.action (G := G) μ) (l2 μ f)
  choose A hA using (fun n : ℕ => M.exists_finite_approx V (show (0:ℝ) < 1/(n+1:ℝ) by positivity))
  have ht : Tendsto (fun n => l2 μ ((A n).bm f)) atTop (𝓝 (limit μ M f)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => le_of_lt ?_) (tendsto_one_div_add_atTop_nhds_zero_nat)
    simpa only [ConvexAverage.l2_bm, ConvexAverage.apply, V, limit, Amenable.Mean.orbit_apply] using hA n
  have hm := (tendstoInMeasure_of_tendsto_Lp ht).congr_left (fun n => l2_ae μ ((A n).bm f))
  obtain ⟨r,_,hr⟩ := hm.exists_seq_tendsto_ae
  exact ⟨fun n => A (r n),hr⟩
end InvariantSequence
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
namespace EuclideanFiveColor
open BoundedMeasurable
namespace ConvexAverage
variable {G X : Type*} [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
lemma setIntegral_bm (A : ConvexAverage G) (f : Func X) (s : Set X) (hs : MeasurableSet s)
    (hinv : ∀ g : G, (fun x => g +ᵥ x) ⁻¹' s =ᵐ[μ] s) :
    ∫ x in s, A.bm f x ∂μ = ∫ x in s, f x ∂μ := by
  have hpres (g : G) : MeasurePreserving (fun x : X => g +ᵥ x) (μ.restrict s) (μ.restrict s) := by
    convert (measurePreserving_vadd g μ).restrict_preimage hs using 1
    exact (Measure.restrict_congr_set (hinv g)).symm
  simp only [bm_apply,apply]
  rw [integral_finsetSum _ (fun i _ => by
    have hh : Integrable (fun x => f (A.pt i +ᵥ x)) μ := integrable μ (act (A.pt i) f)
    exact hh.restrict.smul (A.weight i))]
  simp only [integral_smul]
  have he (i : Fin A.n) : ∫ x in s, f (A.pt i +ᵥ x) ∂μ = ∫ x in s, f x ∂μ :=
    (hpres _).integral_comp (MeasurableEquiv.vadd _).measurableEmbedding _
  simp only [he,← Finset.sum_smul,A.total,one_smul]
lemma setIntegral_of_limit (f : Func X) (A : ℕ → ConvexAverage G) (c : ℂ)
    (hc : ∀ᵐ x ∂μ, Tendsto (fun n => (A n).bm f x) atTop (𝓝 c))
    (s : Set X) (hs : MeasurableSet s)
    (hinv : ∀ g : G, (fun x => g +ᵥ x) ⁻¹' s =ᵐ[μ] s) :
    ∫ x in s, f x ∂μ = μ.real s • c := by
  have ht := tendsto_integral_of_dominated_convergence (fun _ : X => (bound f : ℝ))
    (fun n => (measurable ((A n).bm f)).aestronglyMeasurable)
    (integrable_const (bound f : ℝ) : Integrable (fun _ : X => (bound f : ℝ)) (μ.restrict s))
    (fun n => Eventually.of_forall (fun x => (A n).bm_bound f x)) (ae_restrict_of_ae hc)
  simp only [setIntegral_bm μ _ _ s hs hinv,integral_const,Measure.real,Measure.restrict_apply_univ] at ht
  exact tendsto_nhds_unique tendsto_const_nhds ht
end ConvexAverage
namespace ErgodicCriterion
variable (X : Type*) [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]
def testSet (s : Finset ℕ) : Set X := ⋂ n ∈ s, MeasurableSpace.natGeneratingSequence X n
lemma measurable_testSet (s : Finset ℕ) : MeasurableSet (testSet X s) :=
  Finset.measurableSet_biInter s (fun n _ => MeasurableSpace.measurableSet_natGeneratingSequence n)
lemma testSet_union (s t : Finset ℕ) : testSet X (s ∪ t) = testSet X s ∩ testSet X t := by
  ext x; simp [testSet]; aesop
lemma pi_testSet : IsPiSystem (Set.range (testSet X)) := by
  rintro a ⟨s,rfl⟩ b ⟨t,rfl⟩ _
  exact ⟨s ∪ t,testSet_union X s t⟩
lemma generate_testSet : MeasurableSpace.generateFrom (Set.range (testSet X)) = ‹MeasurableSpace X› := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro _ ⟨s,rfl⟩; exact measurable_testSet X s
  · conv_lhs => rw [← MeasurableSpace.generateFrom_natGeneratingSequence X]
    apply MeasurableSpace.generateFrom_mono
    rintro _ ⟨n,rfl⟩
    exact ⟨{n},by simp [testSet]⟩
def test (s : Finset ℕ) : Func X :=
  ⟨(testSet X s).indicator (fun _ => 1),(measurable_const.indicator (measurable_testSet X s)),1,
    fun x => by by_cases hx : x ∈ testSet X s <;> simp [hx]⟩
lemma test_apply (s : Finset ℕ) (x : X) : test X s x = (testSet X s).indicator (fun _ => (1:ℂ)) x := rfl
variable {X}
variable {G : Type*} [AddCommGroup G] [AddAction G X] [MeasurableConstVAdd G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
lemma ergodic_of_test_limits (A : Finset ℕ → ℕ → ConvexAverage G) (c : Finset ℕ → ℂ)
    (hA : ∀ i, ∀ᵐ x ∂μ, Tendsto (fun n => (A i n).bm (test X i) x) atTop (𝓝 (c i))) :
    ErgodicVAdd G X μ := by
  refine ⟨fun {s} hs hinv => ?_⟩
  have hall (i : Finset ℕ) : ∫ x, test X i x ∂μ = c i := by
    simpa using ConvexAverage.setIntegral_of_limit μ (test X i) (A i) (c i) (hA i)
      Set.univ MeasurableSet.univ (fun _ => Eventually.of_forall (fun _ => rfl))
  have htest (i : Finset ℕ) : (μ.restrict s).real (testSet X i) = μ.real s * μ.real (testSet X i) := by
    have he := ConvexAverage.setIntegral_of_limit μ (test X i) (A i) (c i) (hA i) s hs hinv
    rw [← hall i] at he
    simp only [test_apply] at he
    rw [integral_indicator_const _ (measurable_testSet X i),
      integral_indicator_const _ (measurable_testSet X i)] at he
    simpa using congrArg Complex.re he
  have he : μ.restrict s = μ s • μ := by
    apply ext_of_generate_finite (Set.range (testSet X)) (generate_testSet X).symm (pi_testSet X)
    · rintro _ ⟨i,rfl⟩
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by simp; finiteness)).mp
      simpa [Measure.real,Measure.smul_apply,ENNReal.toReal_mul] using htest i
    · simp
  have hr : μ.real s = μ.real s * μ.real s := by
    have hh := congrArg (fun ν : Measure X => ν.real s) he
    simpa [Measure.real,Measure.restrict_apply hs,Set.inter_self] using hh
  have hz : μ.real s = 0 ∨ μ.real s = 1 := by
    have hh : μ.real s * (μ.real s-1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hh with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rw [eventuallyEmptyOrUniv_iff]
  rcases hz with h | h
  · right
    rw [ae_iff]
    simpa using (show μ s = 0 by rw [← ofReal_measureReal]; simp [h])
  · left
    apply (ae_iff_measure_eq hs.nullMeasurableSet).mpr
    change μ s = μ Set.univ
    rw [← ofReal_measureReal (μ := μ) (s := s)]
    simp [h]
end ErgodicCriterion
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
namespace EuclideanFiveColor.InvariantDecomposition
open BoundedMeasurable ErgodicCriterion
variable {G X : Type*} [AddCommGroup G] [Countable G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [AddAction G X] [MeasurableConstVAdd G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
  (M : Amenable.Mean G)
def code (x : X) : Finset ℕ → ℂ := fun i => InvariantSequence.limit μ M (test X i) x
omit [Countable G] [Nonempty X] in
lemma code_measurable : Measurable (code μ M) :=
  Measurable.of_eval (fun i => InvariantSequence.limit_measurable μ M (test X i))
omit [Countable G] [Nonempty X] in
lemma code_fixed (g : G) : (fun x => code μ M (g +ᵥ x)) =ᵐ[μ] code μ M := by
  have h := (ae_all_iff.mpr (fun i => InvariantSequence.limit_fixed μ M (test X i) g))
  exact h.mono fun x hx => funext hx
lemma fiber_invariant : ∀ᵐ y ∂μ.map (code μ M), VAddInvariantMeasure G X (condDistrib id (code μ M) μ y) := by
  have h (g : G) : ∀ᵐ y ∂μ.map (code μ M),
      (condDistrib id (code μ M) μ y).map (fun x => g +ᵥ x) = condDistrib id (code μ M) μ y := by
    have h := KernelSupport.condDistrib_equivariant μ id (code μ M) measurable_id (code_measurable μ M)
      (MeasurableEquiv.vadd g) (MeasurableEquiv.refl _) (fun x => g +ᵥ x)
      (measurable_const_vadd g) (measurePreserving_vadd g μ) (code_fixed μ M g)
      (Eventually.of_forall (fun _ => rfl))
    exact h.mono fun _ hy => hy.symm
  filter_upwards [ae_all_iff.mpr h] with y hy
  constructor
  intro g s hs
  rw [← Measure.map_apply (measurable_const_vadd _) hs,hy]
lemma fiber_ergodic : ∀ᵐ y ∂μ.map (code μ M), ErgodicVAdd G X (condDistrib id (code μ M) μ y) := by
  choose A hA using (fun i => InvariantSequence.exists_averages μ M (test X i))
  have hc := ConditionalFiber.ae_fiber_of_ae μ (code μ M) (code_measurable μ M) (ae_all_iff.mpr hA)
  filter_upwards [fiber_invariant μ M,hc, ConditionalFiber.ae_in_own_fiber μ (code μ M) (code_measurable μ M)] with y hy hlim hcode
  let := hy
  apply ergodic_of_test_limits (condDistrib id (code μ M) μ y) A y
  intro i
  filter_upwards [hlim,hcode] with x hx he
  have hh := hx i
  change Tendsto _ atTop (𝓝 (code μ M x i)) at hh
  rwa [he] at hh
end EuclideanFiveColor.InvariantDecomposition
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open EuclideanFiveColor
namespace PlaneFiveColor.Spectral
instance : Countable Rot := inferInstanceAs (Countable K)
lemma smul_ergodic_of_rot (μ : Measure D) [ErgodicVAdd Rot D μ] : ErgodicSMul K D μ := by
  have : SMulInvariantMeasure K D μ := ⟨fun k s hs => measure_preimage_vadd μ (mulRot k) s⟩
  constructor
  intro s hs hi
  apply ErgodicVAdd.aeconst_of_forall_preimage_vadd_ae_eq (G := Rot) hs
  exact fun g => hi (rotMul g)
/-- The arbitrary invariant wild case, obtained from actual conditional ergodic fibers. -/
lemma wild_fourier (μ : Measure D) [IsProbabilityMeasure μ]
    (hw : IsWild μ) (z : E) (hz : z ≠ 0) : ∫ d, (eval z d : ℂ) ∂μ = 0 := by
  have : SMulInvariantMeasure K D μ := ⟨fun k s hs => (hw.1 k).measure_preimage hs.nullMeasurableSet⟩
  let M : Amenable.Mean Rot := MovingMean.toMean (fun _ => 0)
  let q := InvariantDecomposition.code μ M
  have hq : Measurable q := InvariantDecomposition.code_measurable μ M
  have hc : ∀ᵐ d ∂μ, d ∉ (C : Set D) := by
    rw [ae_iff]
    simpa using hw.2
  have hf := ConditionalFiber.ae_fiber_of_ae μ q hq hc
  have he : ∀ᵐ y ∂μ.map q, ∫ d, (eval z d : ℂ) ∂condDistrib id q μ y = 0 := by
    filter_upwards [InvariantDecomposition.fiber_ergodic μ M, hf] with y hy hC
    let := hy
    have := smul_ergodic_of_rot (condDistrib id q μ y)
    apply ergodic_wild_fourier (condDistrib id q μ y) ?_ z hz
    refine ⟨fun k => measurePreserving_smul k _,?_⟩
    rw [ae_iff] at hC
    simpa using hC
  rw [← ConditionalFiber.integral_fiber μ q hq (fun d => (eval z d : ℂ))
    (BoundedMeasurable.integrable μ (char z))]
  exact integral_eq_zero_of_ae he
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor EuclideanFiveColor.VectorMeasure EuclideanFiveColor.CommutingSpectral
lemma finite_wild_fourier (μ : Measure D) [IsFiniteMeasure μ] (hw : IsWild μ)
    (z : E) (hz : z ≠ 0) : ∫ d, (eval z d:ℂ) ∂μ = 0 := by
  by_cases hμ : μ = 0
  · simp [hμ]
  have hu : μ Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hμ
  let ν := (μ Set.univ)⁻¹ • μ
  have : IsProbabilityMeasure ν := ⟨by
    rw [Measure.smul_apply,smul_eq_mul,ENNReal.inv_mul_cancel hu (measure_ne_top μ Set.univ)]⟩
  have hwν : IsWild ν := ⟨fun k => (hw.1 k).smul_measure _,by simp [ν,Measure.smul_apply,hw.2]⟩
  have hh := wild_fourier ν hwν z hz
  rw [integral_smul_measure] at hh
  exact (smul_eq_zero.mp hh).resolve_left (by
    rw [ENNReal.toReal_inv]
    exact inv_ne_zero ((ENNReal.toReal_pos hu (measure_ne_top μ Set.univ)).ne'))
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : DiscreteE →* unitary (H →L[ℂ] H)) (W : K → unitary (H →L[ℂ] H))
  (hcov : ∀ k z w, (W k : H →L[ℂ] H) (ContinuousVectors.op U z w) =
    ContinuousVectors.op U ((kCoeff k)*z) ((W k : H →L[ℂ] H) w))
include hcov
lemma vectorMeasure_invariant (v : H) (hfix : ∀ k, (W k : H →L[ℂ] H) v = v) :
    ∀ k : K, MeasurePreserving (fun d : D => k • d) (measure (calculus U) v) (measure (calculus U) v) := by
  intro k
  have hm : Measurable (fun d : D => k • d) := (continuous_scalar (kCoeff k)).measurable
  refine ⟨hm,measure_eq_of_fourier _ _ (fun z => ?_)⟩
  change (∫ d, evaluation z d ∂(measure (calculus U) v).map (fun d : D => k • d)) = _
  rw [integral_map hm.aemeasurable ((evaluation z).continuous.measurable.aestronglyMeasurable)]
  change (∫ d, (eval (kCoeff k * Multiplicative.toAdd z) d : ℂ) ∂measure (calculus U) v) = _
  have hc (a : E) : (∫ d, (eval a d:ℂ) ∂measure (calculus U) v) =
      ⟪v,ContinuousVectors.op U a v⟫_ℂ := by
    have hh := integral_complex (calculus U) v (evaluation (G := DiscreteE) (Multiplicative.ofAdd a))
    rw [calculus_evaluation U (Multiplicative.ofAdd a : DiscreteE)] at hh
    exact hh
  change (∫ d, (eval (kCoeff k * Multiplicative.toAdd z) d : ℂ) ∂measure (calculus U) v) =
    ∫ d, (eval (Multiplicative.toAdd z) d:ℂ) ∂measure (calculus U) v
  rw [hc,hc]
  calc
    _ = ⟪(W k : H →L[ℂ] H) v,ContinuousVectors.op U (kCoeff k * Multiplicative.toAdd z) ((W k : H →L[ℂ] H) v)⟫_ℂ := by rw [hfix k]
    _ = ⟪(W k : H →L[ℂ] H) v,(W k : H →L[ℂ] H) (ContinuousVectors.op U (Multiplicative.toAdd z) v)⟫_ℂ := by rw [hcov]
    _ = _ := Unitary.inner_map_map (W k) v (ContinuousVectors.op U (Multiplicative.toAdd z) v)
lemma residual_fourier (v : H) (hv : v ∈ (ContinuousVectors.space U)ᗮ)
    (hfix : ∀ k, (W k : H →L[ℂ] H) v = v) (z : E) (hz : z ≠ 0) :
    ⟪v,ContinuousVectors.op U z v⟫_ℂ = 0 := by
  have hw : IsWild (measure (calculus U) v) :=
    ⟨vectorMeasure_invariant U W hcov v hfix,measure_ordinary_zero_of_orthogonal U v hv⟩
  have hh := finite_wild_fourier (measure (calculus U) v) hw z hz
  have hc := integral_complex (calculus U) v (evaluation (G := DiscreteE) (Multiplicative.ofAdd z))
  rw [calculus_evaluation U (Multiplicative.ofAdd z : DiscreteE)] at hc
  exact hc.symm.trans hh
end PlaneFiveColor.Spectral
end

end OAI
