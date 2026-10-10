import OAI.Probability.DilutedSpin.ExternalCoefficientLaw
import OAI.Probability.DilutedSpin.MultileafMatrixPointwise
import OAI.Probability.DilutedSpin.RootMatrixTriple

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree
open scoped NNReal BigOperators
variable {Ω X Y Z : Type} [Fintype Ω]
    [MeasurableSpace X] [MeasurableSpace Y]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] {L M r k : ℕ}

abbrev Labels (L : ℕ) (Z : Type) := (Spec L × ℕ) × Z

noncomputable def rootHistory (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ) (z : FullRootState Y X (Labels L Z) M) (v : Z) : ℝ :=
  packRoot (fun h n x t y => externalHistory S anchorLeaf T m (base h n x)
    (rootArray t y) old read v a b d spinAnchor f) z

omit [MeasurableSpace X] [MeasurableSpace Y] [Countable Z] [MeasurableSpace Z]
    [MeasurableSingletonClass Z] in
lemma rootHistory_polarization (hk : 0 < k)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (hm : ∀ j : Fin (L+1), m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last (L+1)) = 1)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ) (z : FullRootState Y X (Labels L Z) M) (v : Z) :
    rootHistory S anchorLeaf T m base old read a b d spinAnchor f z v =
      ((k:ℝ)^k / 2^k) * ∑ ε : Fin k → Bool, (∏ j, Polarization.sign (ε j)) *
        rootExternalCoefficient S anchorLeaf T (fun i => prior i.1.1) m base old
          (fun i x y => direction i.1.1 (read i.2 x) y)
          (fun i x y => anchor i.1.1 (read i.2 x) y) f k z
          ((polarizedSpec hk ε a b d spinAnchor,0),v) := by
  exact externalHistory_polarization hk S anchorLeaf T m hm hroot hend
    (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) old read v a b d spinAnchor f

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

noncomputable def historyAverage : ℝ :=
  ∫ z : FullRootState Y X (Labels L Z) M × Z,
    rootHistory S anchorLeaf T m base old read a b d spinAnchor f z.1 z.2
      ∂(fullRootLaw ξ μ ν rate score).prod τ

noncomputable def historyCovariance : ℝ :=
  historyAverage ξ μ ν τ rate score S anchorLeaf T m base old read a b d spinAnchor f -
    oldTreeAverage ξ μ ν rate score S T (fun i => prior i.1.1) (fun j => m j.succ) base old f *
      historyAverage ξ μ ν τ rate score S anchorLeaf T m base old read a b d spinAnchor (fun _ => 1)

variable (hb : ∀ n y, Measurable (fun z : RootPath Y M × RootPath X n => base z.1 n z.2 y))
    (hm : ∀ j : Fin (L+1), m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last (L+1)) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)

include hb hm hmono hpos hroot hend hB hf

lemma historyAverage_polarization (hk : 0 < k) :
    historyAverage ξ μ ν τ rate score S anchorLeaf T m base old read a b d spinAnchor f =
      ((k:ℝ)^k / 2^k) * ∑ ε : Fin k → Bool, (∏ j, Polarization.sign (ε j)) *
        externalCoefficientAverage ξ μ ν (τ.map (fun v => ((polarizedSpec hk ε a b d spinAnchor,0),v)))
          rate score S anchorLeaf T (fun i => prior i.1.1) m base old
          (fun i x y => direction i.1.1 (read i.2 x) y)
          (fun i x y => anchor i.1.1 (read i.2 x) y) f k := by
  have hi (ε : Fin k → Bool) := integrable_rootExternalCoefficient_label ξ μ ν τ rate score
    S anchorLeaf T (fun i => prior i.1.1) m base old
    (fun i x y => direction i.1.1 (read i.2 x) y)
    (fun i x y => anchor i.1.1 (read i.2 x) y) f hb hm hmono hpos hroot hend hB hf
    (fun _ _ _ => direction_bound _ _ _) (fun _ _ _ => anchor_bound _ _ _)
    (fun v => ((polarizedSpec hk ε a b d spinAnchor,0),v))
    (measurable_const.prodMk measurable_id) k
  unfold historyAverage
  simp_rw [rootHistory_polarization hk S anchorLeaf T m hm hroot hend]
  rw [integral_const_mul,integral_finsetSum _ (fun ε _ => (hi ε).const_mul _)]
  congr 1
  apply Finset.sum_congr rfl
  intro ε _
  rw [integral_const_mul]
  congr 1
  symm
  exact externalCoefficientAverage_fresh_label ξ μ ν τ rate score S anchorLeaf T
    (fun i => prior i.1.1) m base old
    (fun i x y => direction i.1.1 (read i.2 x) y)
    (fun i x y => anchor i.1.1 (read i.2 x) y) f hb hm hmono hpos hroot hend hB hf
    (fun _ _ _ => direction_bound _ _ _) (fun _ _ _ => anchor_bound _ _ _)
    (fun v => ((polarizedSpec hk ε a b d spinAnchor,0),v))
    (measurable_const.prodMk measurable_id) k

lemma historyCovariance_polarization (hk : 0 < k) :
    historyCovariance ξ μ ν τ rate score S anchorLeaf T m base old read a b d spinAnchor f =
      ((k:ℝ)^k / 2^k) * ∑ ε : Fin k → Bool, (∏ j, Polarization.sign (ε j)) *
        covarianceCoefficient ξ μ ν (τ.map (fun v => ((polarizedSpec hk ε a b d spinAnchor,0),v)))
          rate score S anchorLeaf T (fun i => prior i.1.1) m base old
          (fun i x y => direction i.1.1 (read i.2 x) y)
          (fun i x y => anchor i.1.1 (read i.2 x) y) f k := by
  unfold historyCovariance
  rw [historyAverage_polarization ξ μ ν τ rate score S anchorLeaf T m base old read a b d spinAnchor f
    hb hm hmono hpos hroot hend hB hf hk,
    historyAverage_polarization ξ μ ν τ rate score S anchorLeaf T m base old read a b d spinAnchor (fun _ => 1)
    hb hm hmono hpos hroot hend (B := 1) (by norm_num) (by intro; norm_num) hk]
  simp only [covarianceCoefficient,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  ring_nf

end DilutedSpinGlass.UniversalDictionary
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I] {n N : ℕ}

omit [DecidableEq I] in
/-- Exact conversion of the color-indexed matrix projection to the old
all-leaf projection error in the SAME sampled tree. -/
lemma matrixProjectionError_treeOverlap (S : PrescribedTree n)
    (q : I → S.Leaf) (hq : Function.Bijective q) (T : KernelTower Ω n)
    (a c : I) (f X : FinitePath Ω n → Fin N → ℝ) :
    matrixProjectionError S q T a c (spatialProduct (fun _ : I => f)) X=
      oldProjectionError S T (q a) (q c) (treeOverlap S f) X := by
  unfold matrixProjectionError oldProjectionError FiniteLaw.l2
  congr 1
  apply FiniteLaw.expect_congr
  intro z
  have he := spatialProduct_leafProduct S q hq f z
  change spatialProduct (fun _ : I => f) (fun j => S.pathAt (q j) z)=treeOverlap S f z at he
  dsimp only
  rw [he]
  exact sub_sq_comm _ _

omit [DecidableEq I] in
/-- The target's actual own-projector error, for arbitrary initial prefix
and later first split, is controlled only by genuine proper children. -/
theorem matrixProjectionError_prefixed_le (k : ℕ+) (C : Fin k → PrescribedTree n)
    (b : (PrescribedTree.node k C).Leaf) (r d : ℕ)
    (q : I → (splitFrame (.node k C) r d).Leaf) (hq : Function.Bijective q)
    (T : KernelTower Ω (n+1+r+1+d)) (a c : I)
    (ha : q a=splitFrameLeaf (.node k C) r d 0 b)
    (hc : q c=splitFrameLeaf (.node k C) r d 1 b)
    (f : FinitePath Ω (n+1+r+1+d) → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    matrixProjectionError (splitFrame (.node k C) r d) q T a c
      (spatialProduct (fun _ : I => f))
      (fun x i => splitProjector (.node k C) r d T (fun y => f y i) x) ≤
       2*Real.sqrt ((k:ℝ)*∑ i, Real.sqrt (descendantEnergyAt (C i) r d T f)) := by
  rw [matrixProjectionError_treeOverlap _ q hq T a c,ha,hc]
  exact prefixed_stem_old_error_le k C b r d T f hf

omit [DecidableEq I] in
/-- The actual target-side shifted projection error splits into proper-child
covariances and a single-path squared-norm comparison. This includes every
prefix and never asks for independent target leaves after marginalizing. -/
theorem matrixProjectionError_prefixed_change_le (k : ℕ+) (C : Fin k → PrescribedTree n)
    (b : (PrescribedTree.node k C).Leaf) (r d : ℕ)
    (q : I → (splitFrame (.node k C) r d).Leaf) (hq : Function.Bijective q)
    (T : KernelTower Ω (n+1+r+1+d)) (a c : I)
    (ha : q a=splitFrameLeaf (.node k C) r d 0 b)
    (hc : q c=splitFrameLeaf (.node k C) r d 1 b)
    (f X : FinitePath Ω (n+1+r+1+d) → Fin N → ℝ)
    (hf : ∀ x i, |f x i|≤1) (hX : ∀ x i, |X x i|≤1) :
    matrixProjectionError (splitFrame (.node k C) r d) q T a c
      (spatialProduct (fun _ : I => f)) X ≤
       2*Real.sqrt ((k:ℝ)*∑ i, Real.sqrt (descendantEnergyAt (C i) r d T f))+
       2*Real.sqrt ((KernelTower.law (n+1+r+1+d) T).expect (fun x => FiniteLaw.spatialSq (fun i =>
         splitProjector (.node k C) r d T (fun y => f y i) x-X x i))) := by
  have h := matrixProjectionError_change_spatial (splitFrame (.node k C) r d) q T a c
    (spatialProduct (fun _ : I => f)) X
    (fun x i => splitProjector (.node k C) r d T (fun y => f y i) x) hX
    (fun x i => splitProjector_bound (.node k C) r d T (fun y => f y i) (fun y => hf y i) x)
  exact h.trans (add_le_add (matrixProjectionError_prefixed_le k C b r d q hq T a c ha hc f hf) le_rfl)

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {I : Type} [Fintype I] [DecidableEq I] {n N : ℕ}

/-- The entire multileaf covariance, after averaging the genuine root law,
is controlled by the SAME signed centered matrix history and the literal
proper-child covariances. No conditional concentration is assumed. -/
theorem root_multileaf_matrix {Z : Type} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (k : ℕ+) (C : Fin k → PrescribedTree n) (b : (PrescribedTree.node k C).Leaf) (r d : ℕ)
    (Target : PrescribedTree (n+1+r+1+d)) (q : I → Target.Leaf) (hq : Function.Bijective q)
    (Q : Finset ℕ) (hS : branchingCount (splitFrame (.node k C) r d) (· ∈ Q)=0)
    (K : (z : Z) → KernelTower (Ω z) (n+1+r+1+d)) (a c : I) (hac : a≠c)
    (cs : List I) (hcs : cs.Nodup) (hdis : ∀ j ∈ cs, j ∉ insert c ({a}:Finset I))
    (hfull : insert c ({a}:Finset I) ∪ cs.toFinset=Finset.univ)
    (hqd : splitDepth Target (q a) (q c)=d)
    (f : (z : Z) → FinitePath (Ω z) (n+1+r+1+d) → Fin N → ℝ) (hf : ∀ z x i, |f z x i| ≤ 1) :
    let L := n+1+r+1+d
    let S := splitFrame (.node k C) r d
    let x := splitFrameLeaf (.node k C) r d 0 b
    let y := splitFrameLeaf (.node k C) r d 1 b
    let m := grid L 0 L
    let J := partialKappa Target m (Finset.univ.image q)/
      partialKappa Target m ((insert c ({a}:Finset I)).image q)
    let X := fun z x i => splitProjector (.node k C) r d (K z) (fun y => f z y i) x
    let A := fun z => spatialProduct (fun _ : I => f z)
    let W := fun z => (k:ℝ)*∑ i, Real.sqrt (descendantEnergyAt (C i) r d (K z) (f z))
    Integrable (fun z => shapeEnergyAt (stem (.node k C) r) d (K z) (f z)) μ →
    Integrable (fun z => KernelTower.halfTripleDifferenceAt L (K z) d (X z)) μ →
    Integrable (fun z => matrixObservableHistory Target q (K z) m (c::cs) S x (A z) (treeOverlap S (f z))) μ →
    Integrable (fun z => matrixProjectionError Target q (K z) a c (A z) (X z)) μ →
    Integrable (fun z => oldProjectionError S (K z) x y (treeOverlap S (f z)) (X z)) μ →
    Integrable (fun z => (Target.sampleLaw (K z)).expect (fun w => A z (fun j => Target.pathAt (q j) w))) μ →
    Integrable W μ → Integrable (fun z => Real.sqrt (W z)) μ →
    (((d:ℝ)+2)/(L:ℝ))*(∫ z, shapeEnergyAt (stem (.node k C) r) d (K z) (f z) ∂μ) ≤
      2*(2*(L:ℝ)⁻¹ + |matrixRootCovariance μ Ω Target S q K m (c::cs) x A (fun z => treeOverlap S (f z))|/|J|+
        (∫ z, matrixProjectionError Target q (K z) a c (A z) (X z) ∂μ)*shiftedCharge Q Target S (c::cs).length/|J|+
        pairHistoryMass S m x*(2*(∫ z, Real.sqrt (W z) ∂μ)))+
      (((d:ℝ)+2)/(L:ℝ))*(16*(∫ z, W z ∂μ)) := by
  dsimp only
  let L := n+1+r+1+d
  let S := splitFrame (.node k C) r d
  let x := splitFrameLeaf (.node k C) r d 0 b
  let y := splitFrameLeaf (.node k C) r d 1 b
  let v := splitFrameVertex (.node k C) r d
  let m := grid L 0 L
  let J := partialKappa Target m (Finset.univ.image q)/
    partialKappa Target m ((insert c ({a}:Finset I)).image q)
  let X := fun z x i => splitProjector (.node k C) r d (K z) (fun y => f z y i) x
  let A := fun z => spatialProduct (fun _ : I => f z)
  let W := fun z => (k:ℝ)*∑ i, Real.sqrt (descendantEnergyAt (C i) r d (K z) (f z))
  intro hV hT hH hEt hEo hMean hW hSqrtW
  have hL : 0<L := by dsimp [L]; omega
  have hd : d<L := by dsimp [L]; omega
  have h := root_matrix_three_copy μ Ω hL Q Target S q hq hS K a c hac cs hcs hdis hfull
    x y v d hd hqd (splitFrame_split (.node k C) r d b)
    (splitFrame_fresh_split (.node k C) r d 0 b) (splitFrame_fresh_split (.node k C) r d 1 b)
    X (fun z w i => splitProjector_bound (.node k C) r d (K z) (fun w => f z w i)
      (fun w => hf z w i) w)
    (fun z w hz t => stem_doubled_projector_old_side (.node k C) r d
      (stemLeaf (.node k C) r b) (stemLeaf (.node k C) r b) (K z) (f z) w hz t)
    A (fun z w => spatialProduct_bound (fun _ : I => f z) (fun _ => hf z) w)
    (fun z => treeOverlap S (f z)) (fun z => treeOverlap_bound S (f z) (hf z))
    hT hH hEt hEo hMean
  dsimp only at h
  have hv : (∫ z, shapeEnergyAt (stem (.node k C) r) d (K z) (f z) ∂μ) ≤
      2*(∫ z, KernelTower.halfTripleDifferenceAt L (K z) d (X z) ∂μ)+16*(∫ z, W z ∂μ) := by
    have hh := integral_mono hV ((hT.const_mul 2).add (hW.const_mul 16)) (fun z =>
      (prefixed_stem_covariance_three_copy_le k C b r d (K z) (f z) (hf z)).trans_eq (by dsimp [W]; ring))
    simp only [Pi.add_apply] at hh
    rw [integral_add (hT.const_mul 2) (hW.const_mul 16),integral_const_mul,integral_const_mul] at hh
    exact hh
  have ho : (∫ z, oldProjectionError S (K z) x y (treeOverlap S (f z)) (X z) ∂μ) ≤
      2*(∫ z, Real.sqrt (W z) ∂μ) := by
    have hh := integral_mono hEo (hSqrtW.const_mul 2) (fun z =>
      prefixed_stem_old_error_le k C b r d (K z) (f z) (hf z))
    rw [integral_const_mul] at hh
    exact hh
  have hc0 : 0 ≤ ((d:ℝ)+2)/(L:ℝ) := by positivity
  have hv' := mul_le_mul_of_nonneg_left hv hc0
  have hmass : 0 ≤ pairHistoryMass S m x := by unfold pairHistoryMass; positivity
  have ho' := mul_le_mul_of_nonneg_left ho hmass
  have hg : -gamma S m v=((d:ℝ)+2)/(L:ℝ) := splitFrame_gamma_grid (.node k C) r d
  have hdelta : m ⟨d+1,by omega⟩-m ⟨d,by omega⟩=(L:ℝ)⁻¹ := by
    dsimp [m,grid]
    push_cast
    ring
  change (-gamma S m v)*(∫ z, KernelTower.halfTripleDifferenceAt L (K z) d (X z) ∂μ) ≤
    2*(m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)+
    |matrixRootCovariance μ Ω Target S q K m (c::cs) x A (fun z => treeOverlap S (f z))|/|J|+
    (∫ z, matrixProjectionError Target q (K z) a c (A z) (X z) ∂μ)*shiftedCharge Q Target S (c::cs).length/|J|+
    pairHistoryMass S m x*(∫ z, oldProjectionError S (K z) x y (treeOverlap S (f z)) (X z) ∂μ) at h
  rw [hg,hdelta] at h
  let B := 2*(L:ℝ)⁻¹ + |matrixRootCovariance μ Ω Target S q K m (c::cs) x A (fun z => treeOverlap S (f z))|/|J|+
    (∫ z, matrixProjectionError Target q (K z) a c (A z) (X z) ∂μ)*shiftedCharge Q Target S (c::cs).length/|J|
  change ((d:ℝ)+2)/(L:ℝ)*(∫ z, KernelTower.halfTripleDifferenceAt L (K z) d (X z) ∂μ) ≤
    B+pairHistoryMass S m x*(∫ z, oldProjectionError S (K z) x y (treeOverlap S (f z)) (X z) ∂μ) at h
  have hh := h.trans (add_le_add le_rfl ho')
  change ((d:ℝ)+2)/(L:ℝ)*(∫ z, shapeEnergyAt (stem (.node k C) r) d (K z) (f z) ∂μ) ≤
    2*(B+pairHistoryMass S m x*(2*(∫ z, Real.sqrt (W z) ∂μ)))+((d:ℝ)+2)/(L:ℝ)*(16*(∫ z, W z ∂μ))
  calc
    _ ≤ ((d:ℝ)+2)/(L:ℝ)*(2*(∫ z, KernelTower.halfTripleDifferenceAt L (K z) d (X z) ∂μ)+16*(∫ z, W z ∂μ)) := hv'
    _ = 2*(((d:ℝ)+2)/(L:ℝ)*(∫ z, KernelTower.halfTripleDifferenceAt L (K z) d (X z) ∂μ))+
        ((d:ℝ)+2)/(L:ℝ)*(16*(∫ z, W z ∂μ)) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hh (by norm_num)) le_rfl

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
