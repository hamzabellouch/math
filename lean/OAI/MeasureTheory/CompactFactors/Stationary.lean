import OAI.MeasureTheory.CompactFactors.Factors

namespace OAI

noncomputable section

section
open MeasureTheory
open scoped BoundedContinuousFunction
open PlaneFiveColor.InvariantMean
namespace EuclideanFiveColor.StationaryMean
variable {A B X : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [TopologicalSpace X] [CompactSpace X]
  (t : A → X → X) (r : B → X → X) (x₀ : X)
def inner (f : C(X,ℝ)) (b : B) : A →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun a => f (r b (t a x₀)))
    continuous_of_discreteTopology ‖f‖ (fun _ => f.norm_coe_le_norm _)
omit [AddCommGroup A] [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] in
lemma inner_norm (f : C(X,ℝ)) (b : B) : ‖inner t r x₀ f b‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr fun _ => f.norm_coe_le_norm _
def outer (f : C(X,ℝ)) : B →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun b => mean (inner t r x₀ f b))
    continuous_of_discreteTopology ‖f‖ (fun b => (mean_norm_le _).trans (inner_norm t r x₀ f b))
def average (f : C(X,ℝ)) : ℝ := mean (outer t r x₀ f)
omit [AddCommGroup A] [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] in
lemma inner_add (f g : C(X,ℝ)) (b : B) : inner t r x₀ (f+g) b = inner t r x₀ f b + inner t r x₀ g b := by ext; rfl
omit [AddCommGroup A] [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] in
lemma inner_smul (c : ℝ) (f : C(X,ℝ)) (b : B) : inner t r x₀ (c • f) b = c • inner t r x₀ f b := by ext; rfl
omit [AddCommGroup B] in
lemma outer_add (f g : C(X,ℝ)) : outer t r x₀ (f+g) = outer t r x₀ f + outer t r x₀ g := by
  ext b
  exact (congrArg mean (inner_add t r x₀ f g b)).trans (mean_add _ _)
omit [AddCommGroup B] in
lemma outer_smul (c : ℝ) (f : C(X,ℝ)) : outer t r x₀ (c • f) = c • outer t r x₀ f := by
  ext b
  exact (congrArg mean (inner_smul t r x₀ c f b)).trans (mean_smul _ _)
lemma average_add (f g : C(X,ℝ)) : average t r x₀ (f+g) = average t r x₀ f + average t r x₀ g := by
  simp only [average,outer_add,mean_add]
lemma average_smul (c : ℝ) (f : C(X,ℝ)) : average t r x₀ (c • f) = c * average t r x₀ f := by
  simp only [average,outer_smul,mean_smul]
lemma average_mono {f g : C(X,ℝ)} (h : f ≤ g) : average t r x₀ f ≤ average t r x₀ g := by
  have hp : 0 ≤ average t r x₀ (g-f) := mean_nonneg _ fun b => mean_nonneg _ fun a => sub_nonneg.mpr (h _)
  have he : average t r x₀ (g-f) = average t r x₀ g - average t r x₀ f := by
    rw [sub_eq_add_neg,average_add,← neg_one_smul ℝ f,average_smul]; ring
  linarith
lemma average_const (c : ℝ) : average t r x₀ (ContinuousMap.const X c) = c := by
  have hi (b : B) : inner t r x₀ (ContinuousMap.const X c) b = BoundedContinuousFunction.const A c := by ext; rfl
  have ho : outer t r x₀ (ContinuousMap.const X c) = BoundedContinuousFunction.const B c := by
    ext b
    change mean (inner t r x₀ _ b) = c
    rw [hi,mean_const]
  rw [average,ho,mean_const]
lemma average_translation (ht : ∀ a b x, t a (t b x) = t (a+b) x)
    (φ : B → A → A) (hc : ∀ a b x, t a (r b x) = r b (t (φ b a) x))
    (a : A) (f : C(X,ℝ)) (ha : Continuous (t a)) :
    average t r x₀ (f.comp ⟨t a,ha⟩) = average t r x₀ f := by
  unfold average
  congr 1
  ext b
  change mean (inner t r x₀ (f.comp _) b) = mean (inner t r x₀ f b)
  have he : inner t r x₀ (f.comp ⟨t a,ha⟩) b = shift (φ b a) (inner t r x₀ f b) := by
    ext z
    change f (t a (r b (t z x₀))) = f (r b (t (z+φ b a) x₀))
    rw [hc,ht,add_comm]
  rw [he,mean_shift]
lemma average_rotation (hr : ∀ a b x, r a (r b x) = r (a+b) x)
    (b : B) (f : C(X,ℝ)) (hb : Continuous (r b)) :
    average t r x₀ (f.comp ⟨r b,hb⟩) = average t r x₀ f := by
  unfold average
  have he : outer t r x₀ (f.comp ⟨r b,hb⟩) = shift b (outer t r x₀ f) := by
    ext c
    change mean (inner t r x₀ (f.comp _) c) = mean (inner t r x₀ f (c+b))
    congr 1
    ext z
    change f (r b (r c (t z x₀))) = f (r (c+b) (t z x₀))
    rw [hr,add_comm]
  rw [he,mean_shift]
variable [T2Space X] [MeasurableSpace X] [BorelSpace X]
def functional : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ where
  toFun f := average t r x₀ f.toContinuousMap
  map_add' := fun f g => average_add t r x₀ f.toContinuousMap g.toContinuousMap
  map_smul' := fun c f => average_smul t r x₀ c f.toContinuousMap
  monotone' := fun _ _ h => average_mono t r x₀ h
def measure : Measure X := RealRMK.rieszMeasure (functional t r x₀)
instance : IsFiniteMeasure (measure t r x₀) := by dsimp [measure]; infer_instance
instance : (measure t r x₀).Regular := by dsimp [measure]; infer_instance
lemma integral (f : C(X,ℝ)) : ∫ x, f x ∂measure t r x₀ = average t r x₀ f :=
  RealRMK.integral_rieszMeasure (functional t r x₀) (CompactlySupportedContinuousMap.continuousMapEquiv f)
instance : IsProbabilityMeasure (measure t r x₀) := by
  have he := integral t r x₀ (ContinuousMap.const X 1)
  rw [average_const] at he
  change (∫ _ : X, (1:ℝ) ∂measure t r x₀) = 1 at he
  simp only [integral_const,smul_eq_mul,mul_one] at he
  constructor
  exact (ENNReal.toReal_eq_one_iff _).mp he
lemma preserving_of_average (s : X ≃ₜ X)
    (hav : ∀ f : C(X,ℝ), average t r x₀ (f.comp ⟨s,s.continuous⟩) = average t r x₀ f) :
    MeasurePreserving s (measure t r x₀) (measure t r x₀) := by
  refine ⟨s.continuous.measurable,?_⟩
  have : (Measure.map s (measure t r x₀)).Regular := Measure.Regular.map s
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  change (∫ x, f.toContinuousMap x ∂(measure t r x₀).map s) = ∫ x, f.toContinuousMap x ∂measure t r x₀
  rw [integral_map s.continuous.measurable.aemeasurable f.continuous.measurable.aestronglyMeasurable]
  exact (integral t r x₀ (f.toContinuousMap.comp ⟨s,s.continuous⟩)).trans ((hav f.toContinuousMap).trans (integral t r x₀ f.toContinuousMap).symm)
end EuclideanFiveColor.StationaryMean
end

namespace PlaneFiveColor.Spectral
open MeasureTheory ProbabilityTheory EuclideanFiveColor
instance K_countable : Countable K := by
  let f : K → E := fun k => ⟨(k.val : ℂ), mem_algebraicClosure_iff.mpr k.property⟩
  apply Function.Injective.countable (f := f)
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : E => (z : ℂ)) h

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MulAction K X] [MeasurableConstSMul K X]

/-- An actual standard Borel factor with universal relative spectral
singularity and an ergodic conditional square. Maximality is countable,
inside the separable ambient L² space. -/
theorem exists_terminal_factor (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ] :
    ∃ p : X → OrbitSpace K, ∃ hp : Measurable p,
      (∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x) ∧ UniversalGood μ p ∧
      ErgodicSMul K (X × X) (RelativeProduct.law μ p hp) := by
  classical
  let z₀ : OrbitSpace K := ⟨fun _ => 0⟩
  have hbase : Nonempty (CodedMax.Model (K := K) μ (UniversalGood μ)) := by
    refine ⟨⟨fun _ => z₀, measurable_const, ?_, ?_⟩⟩
    · intro k
      exact Filter.Eventually.of_forall fun x => by ext l; rfl
    · intro d hd _hw hw
      exact relative_singularity_base μ d hd z₀ hw
  have hjoin : ∀ q : ℕ → X → OrbitSpace K, (∀ n, Measurable (q n)) →
      (∀ n (k : K), ∀ᵐ x ∂μ, q n (k • x) = k • q n x) →
      (∀ n, UniversalGood μ (q n)) →
      (∀ i j, FactorLp.space μ (q i) ≤ FactorLp.space μ (q j) ∨
        FactorLp.space μ (q j) ≤ FactorLp.space μ (q i)) → UniversalGood μ (ChainJoin.code (K := K) q) := by
    intro q hq hqe hg hc d hd hde hw
    apply relative_singularity_approximation (W := OrbitSpace K) μ d (ChainJoin.code (K := K) q) hd
      (ChainJoin.code_measurable q hq) hde
      (fun k => Filter.Eventually.of_forall (ChainJoin.code_equivariant q k)) hw
    intro m H hH hB ε hε
    obtain ⟨j, H₀, hH₀, hB₀, hi, he⟩ := ChainJoin.approximation μ q hq hqe hc m H hH hB ε hε
    exact ⟨q j, hq j, hqe j, hg j, H₀, hH₀, hB₀, hi, he⟩
  obtain ⟨a, hamax⟩ := CodedMax.exists_maximal (K := K) μ (UniversalGood μ) hbase hjoin
  refine ⟨a.map, a.measurable, a.equivariant, a.good, ?_⟩
  by_contra hn
  obtain ⟨H, hH, hB, hnot, hc⟩ := CompactTower.strict_compact_successor μ a.map
    a.measurable a.equivariant hn
  let u := OrbitFactor.extend (K := K) a.map H
  have hum : Measurable u := OrbitFactor.measurable_extend a.measurable hH
  have hue (k : K) : ∀ᵐ x ∂μ, u (k • x) = k • u x :=
    OrbitFactor.extend_equivariant μ H a.equivariant k
  have hug : UniversalGood μ u := by
    intro d hd hde hw
    apply relative_singularity_successor μ d u Prod.fst hd hum measurable_fst hde hue
      (fun k => Filter.Eventually.of_forall fun y => rfl) hw hc
    exact a.good
  let v := FactorCode.encode (K := K) u
  have hvm : Measurable v := FactorCode.encode_measurable hum
  have hve (k : K) : ∀ᵐ x ∂μ, v (k • x) = k • v x :=
    Filter.Eventually.of_forall (FactorCode.encode_equivariant u k)
  have hvg : UniversalGood μ v := universalGood_of_factor μ v u
    (FactorCode.encode (K := K) (id : OrbitSpace K × OrbitSpace K → _)) hvm hum
    (FactorCode.encode_measurable measurable_id) hve hue (FactorCode.encode_as_comp μ u hue) hug
  let b : CodedMax.Model (K := K) μ (UniversalGood μ) := ⟨v, hvm, hve, hvg⟩
  have hab : a ≤ b := by
    apply FactorLp.le_of_factor μ a.map v
      (Prod.fst ∘ FactorCode.decode (K := K) (Y := OrbitSpace K × OrbitSpace K))
      (measurable_fst.comp FactorCode.decode_measurable)
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [Function.comp_apply, v]
      rw [FactorCode.decode_encode]
      rfl
  have hba : FactorLp.space μ v ≤ FactorLp.space μ a.map := hamax hab
  have hHlp : MemLp H 2 μ := MemLp.of_bound hH.aestronglyMeasurable 2
    (Filter.Eventually.of_forall hB)
  let J : OrbitSpace K → ℂ := fun z => (FactorCode.decode
    (K := K) (Y := OrbitSpace K × OrbitSpace K) z).2.val 1
  have hJ : Measurable J := (measurable_pi_apply 1).comp
    (OrbitSpace.measurable_val.comp (measurable_snd.comp FactorCode.decode_measurable))
  have hHv : hHlp.toLp H ∈ FactorLp.space μ v := by
    apply FactorLp.mem_of_rep μ v _ J hJ
    filter_upwards [hHlp.coeFn_toLp] with x hx
    rw [hx]
    dsimp only [Function.comp_apply, J, v]
    rw [FactorCode.decode_encode]
    exact (OrbitFactor.orbit_one H x).symm
  obtain ⟨g, hg, hhe⟩ := FactorLp.exists_rep μ a.map _ (hba hHv)
  exact hnot ⟨g, hg, hHlp.coeFn_toLp.symm.trans hhe⟩

end PlaneFiveColor.Spectral

end

end OAI
