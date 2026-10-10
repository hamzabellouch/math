import OAI.Probability.DilutedSpin.ConcreteHistory
import OAI.Probability.DilutedSpin.ShapeRoot

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree
  ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {L p k : ℕ}

/-- Literal exact prescribed-shape covariance, using the original physical
site mean at every signed extension of the complete tilted reservoir. -/
noncomputable def physicalShapeCovariance (m : Fin (L+1) → ℝ)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (M : Model p) (C H : ℝ) (N : ℕ) (u : Spec L×ℕ → ℝ)
    (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath (Fin N → Spin) (L+1)) → ℝ) : ℝ :=
  shapeCovariance (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
    (markLaw (weights L) N) (siteLaw N) (M.alpha*N) (scoreRate N) S anchorLeaf
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (Fin.cons 0 m) (physicalBase M C H N)
    (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    (fun v x => readSpin (KernelTower.terminalState L x) v) F spinAnchor f

lemma physicalShape_expansion (hk : 0 < k) (m : Fin (L+1) → ℝ)
    (hm : ∀ j, 0 < m j) (hmono : Monotone m) (hend : m (Fin.last L) = 1)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (M : Model p) (C H : ℝ) (N : ℕ) (u : Spec L×ℕ → ℝ)
    (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath (Fin N → Spin) (L+1)) → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B) :
    physicalShapeCovariance m S anchorLeaf M C H N u F spinAnchor f =
      ∑ s : Finset (SharingIndex L (Option (Fin k))),
        BooleanPolynomial.coefficient (fun y => F (splitFromProfile y)) s *
        physicalHistoryCovariance m S anchorLeaf M C H N u
          (fun j => (requirementMap s j).1) (fun j => (requirementMap s j).2.1)
          (fun j => (requirementMap s j).2.2) spinAnchor f := by
  exact shapeCovariance_expansion (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
    (markLaw (weights L) N) (siteLaw N) (M.alpha*N) (scoreRate N) S anchorLeaf
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (Fin.cons 0 m) (physicalBase M C H N)
    (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    (fun v x => readSpin (KernelTower.terminalState L x) v) F spinAnchor f
    (measurable_physicalBase M C H N) (fun j => (hm j).ne')
    (exponent_cons_monotone m (fun j => (hm j).le) hmono)
    (exponent_cons_nonneg m (fun j => (hm j).le)) (by simp) hend hB hf hk

/-- All exact finite prescribed constraints, not just pairwise sharing,
hold on ONE physical low-increment sequence. The dictionary and its positive
weights are fixed before selection and never changed by the tested shape. -/
theorem universal_shape_selection (m : Fin (L+1) → ℝ)
    (M : Model p) {C H c : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H) (hc : 0 < c)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ| ≤ C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h| ≤ H)
    (hθi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hhi : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (hm : ∀ l, c ≤ m l) (hmono : Monotone m) (hend : m (Fin.last L) = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ), StrictMono Ns ∧
      (∀ n i, us n i ∈ Icc (probeLow i.2) (probeHigh i.2)) ∧
      (∀ n, ConcreteReservoir.increment (weights L) prior m direction anchor M (Ns n) (us n) ≤
        liminf (pressure M) atTop+ε) ∧
      (∀ (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
        (f : (n : ℕ) → (S.Leaf → FinitePath (Fin (Ns n+1) → Spin) (L+1)) → ℝ)
        (B : ℝ), 0 ≤ B → (∀ n x, |f n x| ≤ B) →
        ∀ (k : ℕ), 0 < k → ∀ (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ)
          (spinAnchor : Bool),
        Tendsto (fun n => physicalShapeCovariance m S anchorLeaf M C H (Ns n+1) (us n)
          F spinAnchor (f n)) atTop (𝓝 0)) := by
  obtain ⟨Ns,us,hNs,hus,hinc,hhist⟩ := universal_history_selection m M hC hH hc
    hθ hh hθi hhi hm hmono hend hε
  refine ⟨Ns,us,hNs,hus,hinc,?_⟩
  intro S anchorLeaf f B hB hf k hk F spinAnchor
  simp_rw [physicalShape_expansion hk m (fun j => hc.trans_le (hm j)) hmono hend
    S anchorLeaf M C H _ _ F spinAnchor _ hB (hf _)]
  have ht := tendsto_finsetSum (Finset.univ : Finset (Finset (SharingIndex L (Option (Fin k)))))
    (fun s _ => (hhist S anchorLeaf f B hB hf _ k hk
        (fun j => (requirementMap s j).1) (fun j => (requirementMap s j).2.1)
        (fun j => (requirementMap s j).2.2) spinAnchor).const_mul
      (BooleanPolynomial.coefficient (fun y => F (splitFromProfile y)) s))
  simpa using ht

end DilutedSpinGlass.UniversalDictionary
end

end

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree
open scoped NNReal BigOperators
variable {Ω Z : Type} [Fintype Ω] {L n : ℕ}

def zeroSpec (L : ℕ) (spinAnchor : Bool) : Spec L :=
  ⟨0, ⟨fun _ => 0,by simp⟩, ⟨fun _ => 1,by simp⟩, spinAnchor⟩

@[simp] lemma zeroSpec_anchor (spinAnchor : Bool) (σ : Spin)
    (y : FinitePath (Alphabet (zeroSpec L spinAnchor)) (L+1)) :
    anchor (zeroSpec L spinAnchor) σ y = if spinAnchor then spin σ else 1 := by
  simp [anchor,zeroSpec]
  rfl

lemma shapeHistory_zero (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (F : (Option (Fin 0) → Option (Fin 0) → ℕ) → ℝ)
    (spinColor : Option (Fin 0) → FinitePath Ω (L+1) → ℝ)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (f : Sample Ω S → ℝ) :
    shapeHistory T m F spinColor S a f = F (fun _ _ => L+1) *
      (S.sampleLaw T).expect (fun x => f x * spinColor none (S.pathAt a x)) := by
  classical
  simp only [shapeHistory,List.ofFn_zero,List.reverse_nil,labeledHistory]
  have he : (fun a_1 b => splitDepth S ((fun _ => a) a_1) ((fun _ => a) b)) =
      (fun _ _ : Option (Fin 0) => L+1) := by funext i j; exact splitDepth_self S a
  rw [he]
  have hp (x : Sample Ω S) : (∏ c : Option (Fin 0), spinColor c (S.pathAt a x)) =
      spinColor none (S.pathAt a x) := by
    rw [Fintype.prod_option]
    simp
  simp_rw [hp]
  exact mul_comm _ _

lemma externalShapeHistory_zero (S : PrescribedTree (L+1)) (a : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (hm : ∀ j : Fin (L+1), m j.succ ≠ 0)
    (base : FinitePath Ω (L+1) → ℝ) (roots : Fin n → Labels L Z)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin) (v : Z)
    (F : (Option (Fin 0) → Option (Fin 0) → ℕ) → ℝ) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ) :
    externalShapeHistory S a T m base roots old read v F spinAnchor f =
      F (fun _ _ => L+1) * externalCoefficient S a T (fun i => prior i.1.1) m base roots
        ((zeroSpec L spinAnchor,0),v) old
        (fun x y => direction (zeroSpec L spinAnchor) (read v x) y)
        (fun x y => anchor (zeroSpec L spinAnchor) (read v x) y) f 0 := by
  unfold externalShapeHistory
  rw [shapeHistory_zero]
  congr 1
  unfold externalCoefficient anchorCoefficient
  simp only [anchorIterate,anchorEval_zero _ _ m hm,Nat.factorial_zero,Nat.cast_one,div_one,
    zeroSpec_anchor]
  rw [sampleExpect_prod]
  congr 1
  funext x
  have hp (y : Sample (Alphabet (zeroSpec L spinAnchor)) S) (b : S.Leaf) :
      KernelTower.pathFst (L+1) (S.pathAt b (samplePair S x y)) = S.pathAt b x := by
    rw [← pathAt_sampleFst,sampleFst_pair]
  simp_rw [hp]
  rw [FiniteLaw.expect_const]

end DilutedSpinGlass.UniversalDictionary

namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree
open scoped NNReal BigOperators
variable {Ω X Y Z : Type} [Fintype Ω]
    [MeasurableSpace X] [MeasurableSpace Y]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] {L M : ℕ}
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure (Labels L Z)) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (rate score : ℝ≥0)
    (S : PrescribedTree (L+1)) (a : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin)
    (F : (Option (Fin 0) → Option (Fin 0) → ℕ) → ℝ) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ)
    (hb : ∀ n y, Measurable (fun z : RootPath Y M × RootPath X n => base z.1 n z.2 y))
    (hm : ∀ j : Fin (L+1), m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last (L+1)) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
include hb hm hmono hpos hroot hend hB hf

lemma shapeAverage_zero :
    shapeAverage ξ μ ν τ rate score S a T m base old read F spinAnchor f =
      F (fun _ _ => L+1) *
        externalCoefficientAverage ξ μ ν (τ.map (fun v => ((zeroSpec L spinAnchor,0),v)))
          rate score S a T (fun i => prior i.1.1) m base old
          (fun i x y => direction i.1.1 (read i.2 x) y)
          (fun i x y => anchor i.1.1 (read i.2 x) y) f 0 := by
  unfold shapeAverage rootShapeHistory
  simp only [packRoot]
  simp_rw [externalShapeHistory_zero S a T m hm]
  rw [integral_const_mul]
  congr 1
  symm
  exact externalCoefficientAverage_fresh_label ξ μ ν τ rate score S a T
    (fun i => prior i.1.1) m base old
    (fun i x y => direction i.1.1 (read i.2 x) y)
    (fun i x y => anchor i.1.1 (read i.2 x) y) f hb hm hmono hpos hroot hend hB hf
    (fun _ _ _ => direction_bound _ _ _) (fun _ _ _ => anchor_bound _ _ _)
    (fun v => ((zeroSpec L spinAnchor,0),v)) (measurable_const.prodMk measurable_id) 0

lemma shapeCovariance_zero :
    shapeCovariance ξ μ ν τ rate score S a T m base old read F spinAnchor f =
      F (fun _ _ => L+1) *
        covarianceCoefficient ξ μ ν (τ.map (fun v => ((zeroSpec L spinAnchor,0),v)))
          rate score S a T (fun i => prior i.1.1) m base old
          (fun i x y => direction i.1.1 (read i.2 x) y)
          (fun i x y => anchor i.1.1 (read i.2 x) y) f 0 := by
  unfold shapeCovariance
  rw [shapeAverage_zero ξ μ ν τ rate score S a T m base old read F spinAnchor f
      hb hm hmono hpos hroot hend hB hf,
    shapeAverage_zero ξ μ ν τ rate score S a T m base old read F spinAnchor (fun _ => 1)
      hb hm hmono hpos hroot hend (B := 1) (by norm_num) (by intro; norm_num)]
  unfold covarianceCoefficient
  ring

end DilutedSpinGlass.UniversalDictionary
end

end

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree
open scoped NNReal BigOperators
variable {Ω X Y Z : Type} [Fintype Ω]
    [MeasurableSpace X] [MeasurableSpace Y]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] {L M n k : ℕ}

omit [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
lemma externalShapeHistory_singleton (hk : 0 < k)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (hm : ∀ j : Fin (L+1), m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last (L+1)) = 1)
    (base : FinitePath Ω (L+1) → ℝ) (roots : Fin n → Labels L Z)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin) (v : Z)
    (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ) (spinAnchor : Bool) :
    externalShapeHistory S anchorLeaf T m base roots old read v F spinAnchor (fun _ => 1) =
      externalShapeHistory (single (L+1)) (firstLeaf (single (L+1))) T m base roots old read v F spinAnchor (fun _ => 1) := by
  rw [externalShapeHistory_expansion,externalShapeHistory_expansion]
  apply Finset.sum_congr rfl
  intro s _
  rw [externalHistory_singleton hk S anchorLeaf T m hm hroot hend]

omit [Countable Z] [MeasurableSingletonClass Z] in
lemma shapeAverage_singleton (hk : 0 < k)
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure (Labels L Z)) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (rate score : ℝ≥0)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (hm : ∀ j : Fin (L+1), m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last (L+1)) = 1)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin)
    (F : (Option (Fin k) → Option (Fin k) → ℕ) → ℝ) (spinAnchor : Bool) :
    shapeAverage ξ μ ν τ rate score S anchorLeaf T m base old read F spinAnchor (fun _ => 1) =
      shapeAverage ξ μ ν τ rate score (single (L+1)) (firstLeaf (single (L+1))) T m base old read F spinAnchor (fun _ => 1) := by
  unfold shapeAverage
  apply integral_congr_ae
  filter_upwards [] with z
  exact externalShapeHistory_singleton hk S anchorLeaf T m hm hroot hend
    (base z.1.1 z.1.2.1.1 z.1.2.1.2) (rootArray z.1.2.2.1 z.1.2.2.2) old read z.2 F spinAnchor

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
