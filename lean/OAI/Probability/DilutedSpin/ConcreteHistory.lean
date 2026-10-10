import OAI.Probability.DilutedSpin.FullSelectedThermal
import OAI.Probability.DilutedSpin.PrefixProjection
import OAI.Probability.DilutedSpin.RootMultileafMatrix

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree
open scoped NNReal BigOperators
variable {Ω X Y Z : Type} [Fintype Ω]
    [MeasurableSpace X] [MeasurableSpace Y]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] {L M r k : ℕ}

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure (Labels L Z)) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (rate score : ℝ≥0)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ)

variable (hb : ∀ n y, Measurable (fun z : RootPath Y M × RootPath X n => base z.1 n z.2 y))
    (hm : ∀ j : Fin (L+1), m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last (L+1)) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)

include hb hm hmono hpos hroot hend hB hf

lemma integrable_rootHistory (hk : 0 < k) :
    Integrable (fun z : FullRootState Y X (Labels L Z) M × Z =>
      rootHistory S anchorLeaf T m base old read a b d spinAnchor f z.1 z.2)
      ((fullRootLaw ξ μ ν rate score).prod τ) := by
  have hi (ε : Fin k → Bool) := integrable_rootExternalCoefficient_label ξ μ ν τ rate score
    S anchorLeaf T (fun i => prior i.1.1) m base old
    (fun i x y => direction i.1.1 (read i.2 x) y)
    (fun i x y => anchor i.1.1 (read i.2 x) y) f hb hm hmono hpos hroot hend hB hf
    (fun _ _ _ => direction_bound _ _ _) (fun _ _ _ => anchor_bound _ _ _)
    (fun v => ((polarizedSpec hk ε a b d spinAnchor,0),v))
    (measurable_const.prodMk measurable_id) k
  simp_rw [rootHistory_polarization hk S anchorLeaf T m hm hroot hend base old read a b d spinAnchor f]
  exact (integrable_finsetSum _ (fun ε _ => (hi ε).const_mul _)).const_mul _

end DilutedSpinGlass.UniversalDictionary
end

end

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree
  ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {L p r k : ℕ}

/-- The actual charge-weighted, sharing-constrained overlap history in the
complete prescribed-tree physical reservoir, centered by its old test. -/
noncomputable def physicalHistoryCovariance (m : Fin (L+1) → ℝ)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (M : Model p) (C H : ℝ) (N : ℕ) (u : Spec L×ℕ → ℝ)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath (Fin N → Spin) (L+1)) → ℝ) : ℝ :=
  historyCovariance (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
    (markLaw (weights L) N) (siteLaw N) (M.alpha*N) (scoreRate N) S anchorLeaf
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (Fin.cons 0 m) (physicalBase M C H N)
    (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    (fun v x => readSpin (KernelTower.terminalState L x) v) a b d spinAnchor f

lemma physicalHistory_polarization (hk : 0 < k) (m : Fin (L+1) → ℝ)
    (hm : ∀ j, 0 < m j) (hmono : Monotone m) (hend : m (Fin.last L) = 1)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (M : Model p) (C H : ℝ) (N : ℕ) (u : Spec L×ℕ → ℝ)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath (Fin N → Spin) (L+1)) → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B) :
    physicalHistoryCovariance m S anchorLeaf M C H N u a b d spinAnchor f =
      ((k:ℝ)^k / 2^k) * ∑ ε : Fin k → Bool, (∏ j, Polarization.sign (ε j)) *
        physicalCoefficient (weights L) prior m direction anchor S anchorLeaf M C H N u f
          (polarizedSpec hk ε a b d spinAnchor) k := by
  exact historyCovariance_polarization (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
    (markLaw (weights L) N) (siteLaw N) (M.alpha*N) (scoreRate N) S anchorLeaf
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (Fin.cons 0 m) (physicalBase M C H N)
    (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    (fun v x => readSpin (KernelTower.terminalState L x) v) a b d spinAnchor f
    (measurable_physicalBase M C H N) (fun j => (hm j).ne')
    (exponent_cons_monotone m (fun j => (hm j).le) hmono)
    (exponent_cons_nonneg m (fun j => (hm j).le)) (by simp) hend hB hf hk

/-- The same selected physical sequence satisfies every finite sharing
constraint and both anchor kinds, with no assumed identity producer. -/
theorem universal_history_selection (m : Fin (L+1) → ℝ)
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
        ∀ (r k : ℕ), 0 < k → ∀ (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L)
          (spinAnchor : Bool),
        Tendsto (fun n => physicalHistoryCovariance m S anchorLeaf M C H (Ns n+1) (us n)
          a b d spinAnchor (f n)) atTop (𝓝 0)) := by
  obtain ⟨Ns,us,hNs,hus,hinc,he,hhist⟩ := universal_analytic_selection m M hC hH hc
    hθ hh hθi hhi hm hmono hend hε
  refine ⟨Ns,us,hNs,hus,hinc,?_⟩
  intro S anchorLeaf f B hB hf r k hk a b d spinAnchor
  simp_rw [physicalHistory_polarization hk m (fun j => hc.trans_le (hm j)) hmono hend
    S anchorLeaf M C H _ _ a b d spinAnchor _ hB (hf _)]
  have ht := tendsto_finsetSum (Finset.univ : Finset (Fin k → Bool))
    (fun e _ => (hhist S anchorLeaf f B hB hf (polarizedSpec hk e a b d spinAnchor) k).const_mul
      (∏ j, Polarization.sign (e j)))
  simpa using ht.const_mul ((k:ℝ)^k / 2^k)

end DilutedSpinGlass.UniversalDictionary
end

end

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open PrescribedTree
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {L n : ℕ}

lemma externalCoefficient_singleton (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ j : Fin L, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last L) = 1)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (D E : FinitePath Ω L → FinitePath (A i) L → ℝ) (k : ℕ) :
    externalCoefficient S a T Q m base roots i old D E (fun _ => 1) k =
      externalCoefficient (single L) (firstLeaf (single L)) T Q m base roots i old D E (fun _ => 1) k := by
  unfold externalCoefficient
  simp only [one_mul]
  exact anchorCoefficient_leaf (Ω := (Ω × Row (A := A) roots) × A i) S
    (KernelTower.prod L (KernelTower.tilt L (tower roots L T Q) (fun j => m j.succ)
      (logWeight base roots old)) (markPrior L (Q i))) m hm hroot hend a
    (fun y => D (physical roots L (KernelTower.pathFst L y)) (KernelTower.pathSnd L y))
    (fun y => E (physical roots L (KernelTower.pathFst L y)) (KernelTower.pathSnd L y)) k

end DilutedSpinGlass.HeterogeneousMarks

namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree
open scoped NNReal BigOperators
variable {Ω X Y Z : Type} [Fintype Ω]
    [MeasurableSpace X] [MeasurableSpace Y]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] {L M n r k : ℕ}

omit [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
lemma externalHistory_singleton (hk : 0 < k)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (hm : ∀ j : Fin (L+1), m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last (L+1)) = 1)
    (base : FinitePath Ω (L+1) → ℝ) (roots : Fin n → Labels L Z)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin) (v : Z)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool) :
    externalHistory S anchorLeaf T m base roots old read v a b d spinAnchor (fun _ => 1) =
      externalHistory (single (L+1)) (firstLeaf (single (L+1))) T m base roots old read v a b d spinAnchor (fun _ => 1) := by
  exact constrainedHistory_singleton hk
    (KernelTower.tilt (L+1) (tower roots (L+1) T (fun i => prior i.1.1)) (fun j => m j.succ)
      (HeterogeneousMarks.logWeight base roots old)) m hm hroot hend a b
    (fun j => (d j).castSucc)
    (fun c x => match c with
      | none => if spinAnchor then spin (read v (physical roots (L+1) x)) else 1
      | some _ => spin (read v (physical roots (L+1) x))) S anchorLeaf

omit [Countable Z] [MeasurableSingletonClass Z] in
lemma historyAverage_singleton (hk : 0 < k)
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure (Labels L Z)) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (rate score : ℝ≥0)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (hm : ∀ j : Fin (L+1), m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last (L+1)) = 1)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool) :
    historyAverage ξ μ ν τ rate score S anchorLeaf T m base old read a b d spinAnchor (fun _ => 1) =
      historyAverage ξ μ ν τ rate score (single (L+1)) (firstLeaf (single (L+1))) T m base old read a b d spinAnchor (fun _ => 1) := by
  unfold historyAverage
  apply integral_congr_ae
  filter_upwards [] with z
  exact externalHistory_singleton hk S anchorLeaf T m hm hroot hend
    (base z.1.1 z.1.2.1.1 z.1.2.1.2) (rootArray z.1.2.2.1 z.1.2.2.2) old read z.2 a b d spinAnchor

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
