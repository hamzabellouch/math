import OAI.Probability.DilutedSpin.PrefixProjection
import OAI.Probability.DilutedSpin.ShapeEmbedding

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open HeterogeneousMarks PrescribedTree
open scoped BigOperators
variable {Ω Z : Type} [Fintype Ω] {L n r k : ℕ}

/-- The actual old full reservoir is tilted first; the constrained history
then samples only its physical paths, with no fresh prior marks left. -/
noncomputable def externalHistory (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (base : FinitePath Ω (L+1) → ℝ) (roots : Fin n → (Spec L×ℕ)×Z)
    (old : (i : (Spec L×ℕ)×Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin) (v : Z)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ) : ℝ :=
  constrainedHistory
    (KernelTower.tilt (L+1) (tower roots (L+1) T (fun i => prior i.1.1)) (fun j => m j.succ)
      (HeterogeneousMarks.logWeight base roots old)) m a b (fun j => (d j).castSucc)
    (fun c x => match c with
      | none => if spinAnchor then spin (read v (physical roots (L+1) x)) else 1
      | some _ => spin (read v (physical roots (L+1) x))) S anchorLeaf
    (fun x => f (fun a => physical roots (L+1) (S.pathAt a x)))

theorem externalHistory_polarization (hk : 0 < k)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (hm : ∀ j : Fin (L+1), m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last (L+1)) = 1)
    (base : FinitePath Ω (L+1) → ℝ) (roots : Fin n → (Spec L×ℕ)×Z)
    (old : (i : (Spec L×ℕ)×Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin) (v : Z)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ) :
    externalHistory S anchorLeaf T m base roots old read v a b d spinAnchor f =
      ((k:ℝ)^k / 2^k) * ∑ ε : Fin k → Bool, (∏ j, Polarization.sign (ε j)) *
        externalCoefficient S anchorLeaf T (fun i => prior i.1.1) m base roots
          ((polarizedSpec hk ε a b d spinAnchor,0),v) old
          (fun x y => direction (polarizedSpec hk ε a b d spinAnchor) (read v x) y)
          (fun x y => anchor (polarizedSpec hk ε a b d spinAnchor) (read v x) y) f k := by
  unfold externalHistory
  erw [universal_constrained_polarization hk _ m hm hroot hend a b d spinAnchor
    (fun x => read v (physical roots (L+1) x)) S anchorLeaf
    (fun x => f (fun a => physical roots (L+1) (S.pathAt a x)))]
  congr 1
  apply Finset.sum_congr rfl
  intro ε _
  congr 1
  unfold externalCoefficient
  congr 1
  funext x
  congr 1
  congr 1
  funext a
  rw [pathAt_sampleFst]

end DilutedSpinGlass.UniversalDictionary
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I] {n N : ℕ}

/-- The complete old experiment: two entire sides separating at depth d,
with their first internal split after another r unary transitions. -/
def splitFrame (S : PrescribedTree n) (r d : ℕ) : PrescribedTree (n+r+1+d) :=
  stem (doubled (stem S r)) d

def splitFrameLeaf (S : PrescribedTree n) (r d : ℕ) (j : Fin 2) (a : S.Leaf) :
    (splitFrame S r d).Leaf := stemLeaf (doubled (stem S r)) d ⟨j,stemLeaf S r a⟩

def splitFrameVertex (S : PrescribedTree n) (r d : ℕ) : (splitFrame S r d).Internal :=
  stemInternal (doubled (stem S r)) d none

lemma splitFrame_split (S : PrescribedTree n) (r d : ℕ) (a : S.Leaf) :
    splitDepth (splitFrame S r d) (splitFrameLeaf S r d 0 a) (splitFrameLeaf S r d 1 a)=d := by
  exact (splitDepth_stem (doubled (stem S r)) d
    ⟨0,stemLeaf S r a⟩ ⟨1,stemLeaf S r a⟩).trans
    (by
      exact (congrArg (fun x => x+d)
        (splitDepth_diff_child (fun _ : Fin (2:ℕ+) => stem S r) 0 1 (by decide)
          (a := stemLeaf S r a) (b := stemLeaf S r a))).trans (Nat.zero_add d))

lemma splitFrame_fresh_split (S : PrescribedTree n) (r d : ℕ) (j : Fin 2) (a : S.Leaf) :
    freshSplitDepth (splitFrame S r d) (splitFrameVertex S r d) (splitFrameLeaf S r d j a)=d := by
  exact (freshSplitDepth_stem (doubled (stem S r)) d none ⟨j,stemLeaf S r a⟩).trans (by exact Nat.zero_add d)

lemma splitFrame_gamma (S : PrescribedTree n) (r d : ℕ) (m : Fin (n+r+1+d+1) → ℝ) :
    gamma (splitFrame S r d) m (splitFrameVertex S r d)=
      m ⟨d,by omega⟩-2*m ⟨d+1,by omega⟩ := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih (fun j => m j.succ)

lemma splitFrame_gamma_grid (S : PrescribedTree n) (r d : ℕ) :
    -gamma (splitFrame S r d) (grid (n+r+1+d) 0 (n+r+1+d)) (splitFrameVertex S r d)=
      ((d:ℝ)+2)/(n+r+1+d:ℕ) := by
  rw [splitFrame_gamma]
  simp only [grid,zero_add,Nat.cast_add,Nat.cast_one]
  ring

/-- Literal multileaf covariance estimate with the FULL signed matrix
history. Every old path, every allowed history, the protected charge J and
both physical projection errors are retained. The only remaining target
error is its explicitly coupled single-copy matrixProjectionError. -/
theorem multileaf_matrix_pointwise (k : ℕ+) (C : Fin k → PrescribedTree n)
    (b : (PrescribedTree.node k C).Leaf) (r d : ℕ)
    (Target : PrescribedTree (n+1+r+1+d)) (q : I → Target.Leaf) (hq : Function.Bijective q)
    (Q : Finset ℕ) (hS : branchingCount (splitFrame (.node k C) r d) (· ∈ Q)=0)
    (K : KernelTower Ω (n+1+r+1+d)) (a c : I) (hac : a≠c)
    (cs : List I) (hcs : cs.Nodup) (hdis : ∀ j ∈ cs, j ∉ insert c ({a}:Finset I))
    (hfull : insert c ({a}:Finset I) ∪ cs.toFinset=Finset.univ)
    (hqd : splitDepth Target (q a) (q c)=d)
    (f : FinitePath Ω (n+1+r+1+d) → Fin N → ℝ) (hf : ∀ x i, |f x i| ≤ 1) :
    let L := n+1+r+1+d
    let S := splitFrame (.node k C) r d
    let x := splitFrameLeaf (.node k C) r d 0 b
    let m := grid L 0 L
    let J := partialKappa Target m (Finset.univ.image q)/
      partialKappa Target m ((insert c ({a}:Finset I)).image q)
    let X := fun x i => splitProjector (.node k C) r d K (fun y => f y i) x
    let W := (k:ℝ)*∑ i, Real.sqrt (descendantEnergyAt (C i) r d K f)
    (((d:ℝ)+2)/(L:ℝ))*shapeEnergyAt (stem (.node k C) r) d K f ≤
      2*((L:ℝ)⁻¹ +
        matrixObservableHistory Target q K m (c::cs) S x (spatialProduct (fun _ : I => f)) (treeOverlap S f)/J+
        matrixProjectionError Target q K a c (spatialProduct (fun _ : I => f)) X *
          shiftedCharge Q Target S (c::cs).length/|J|+
        pairHistoryMass S m x*(2*Real.sqrt W))+
      (((d:ℝ)+2)/(L:ℝ))*(16*W) := by
  dsimp only
  let L := n+1+r+1+d
  let S := splitFrame (.node k C) r d
  let x := splitFrameLeaf (.node k C) r d 0 b
  let y := splitFrameLeaf (.node k C) r d 1 b
  let v := splitFrameVertex (.node k C) r d
  let m := grid L 0 L
  let X := fun x i => splitProjector (.node k C) r d K (fun y => f y i) x
  let A := spatialProduct (fun _ : I => f)
  have hL : 0<L := by dsimp [L]; omega
  have hd : d<L := by dsimp [L]; omega
  have h := matrix_three_copy_pointwise hL Q Target S q hq hS K a c hac cs hcs hdis hfull
    x y v d hd hqd (splitFrame_split (.node k C) r d b)
    (splitFrame_fresh_split (.node k C) r d 0 b) (splitFrame_fresh_split (.node k C) r d 1 b)
    X (fun z i => splitProjector_bound (.node k C) r d K (fun z => f z i) (fun z => hf z i) z)
    (fun z hz w => stem_doubled_projector_old_side (.node k C) r d
      (stemLeaf (.node k C) r b) (stemLeaf (.node k C) r b) K f z hz w)
    A (treeOverlap S f) (treeOverlap_bound S f hf)
  dsimp only at h
  have hv := prefixed_stem_covariance_three_copy_le k C b r d K f hf
  have ho := prefixed_stem_old_error_le k C b r d K f hf
  have hmass : 0 ≤ pairHistoryMass S m x := by unfold pairHistoryMass; positivity
  have ho' := mul_le_mul_of_nonneg_left ho hmass
  have hc0 : 0 ≤ ((d:ℝ)+2)/(L:ℝ) := by positivity
  have hv' := mul_le_mul_of_nonneg_left hv hc0
  have hg : -gamma S m v=((d:ℝ)+2)/(L:ℝ) := splitFrame_gamma_grid (.node k C) r d
  have hdelta : m ⟨d+1,by omega⟩-m ⟨d,by omega⟩=(L:ℝ)⁻¹ := by
    dsimp [m,grid]
    push_cast
    ring
  change (-gamma S m v)*KernelTower.halfTripleDifferenceAt L K d X ≤
    (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)+
    matrixObservableHistory Target q K m (c::cs) S x A (treeOverlap S f)/_+
    matrixProjectionError Target q K a c A X*shiftedCharge Q Target S (c::cs).length/_+
    pairHistoryMass S m x*oldProjectionError S K x y (treeOverlap S f) X at h
  rw [hg,hdelta] at h
  let W := (k:ℝ)*∑ i, Real.sqrt (descendantEnergyAt (C i) r d K f)
  let Z := KernelTower.halfTripleDifferenceAt L K d X
  let J := partialKappa Target m (Finset.univ.image q)/
    partialKappa Target m ((insert c ({a}:Finset I)).image q)
  let R := (L:ℝ)⁻¹ + matrixObservableHistory Target q K m (c::cs) S x A (treeOverlap S f)/J+
    matrixProjectionError Target q K a c A X*shiftedCharge Q Target S (c::cs).length/|J|
  change ((d:ℝ)+2)/(L:ℝ)*Z ≤ R+pairHistoryMass S m x*oldProjectionError S K x y (treeOverlap S f) X at h
  change pairHistoryMass S m x*oldProjectionError S K x y (treeOverlap S f) X ≤
    pairHistoryMass S m x*(2*Real.sqrt W) at ho'
  simp only [mul_assoc] at hv'
  change ((d:ℝ)+2)/(L:ℝ)*shapeEnergyAt (stem (.node k C) r) d K f ≤
    ((d:ℝ)+2)/(L:ℝ)*(2*Z+16*W) at hv'
  change ((d:ℝ)+2)/(L:ℝ)*shapeEnergyAt (stem (.node k C) r) d K f ≤
    2*(R+pairHistoryMass S m x*(2*Real.sqrt W))+((d:ℝ)+2)/(L:ℝ)*(16*W)
  have hh := h.trans (add_le_add le_rfl ho')
  calc
    _ ≤ ((d:ℝ)+2)/(L:ℝ)*(2*Z+16*W) := hv'
    _ = 2*(((d:ℝ)+2)/(L:ℝ)*Z)+((d:ℝ)+2)/(L:ℝ)*(16*W) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hh (by norm_num)) le_rfl

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
