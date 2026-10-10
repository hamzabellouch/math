import OAI.Probability.DilutedSpin.CoordinateFiber
import OAI.Probability.DilutedSpin.DoubledStemProjection
import OAI.Probability.DilutedSpin.SelectorPolarization
import OAI.Probability.DilutedSpin.StemCovarianceTransfer
import OAI.Probability.DilutedSpin.UniversalDictionary

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open scoped BigOperators

noncomputable def polarizedSpec {L r k : ℕ} (hk : 0 < k) (ε : Fin k → Bool)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool) : Spec L :=
  ⟨r, average hk ε (fun j => selector a b d (some j)), selector a b d none, spinAnchor⟩

lemma cast_average {L r k : ℕ} (hk : 0 < k) (ε : Fin k → Bool)
    (g : Fin k → Table L r) (y : Fin L → Fin r → Bool) :
    ((average hk ε g).1 y : ℝ) = (k:ℝ)⁻¹ * ∑ j, MarkSelector.sign (ε j) * ((g j).1 y : ℝ) := by
  simp only [average, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, Rat.cast_sum, cast_signQ]

lemma polarized_direction {L r k : ℕ} (hk : 0 < k) (ε : Fin k → Bool)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
    (σ : Spin) (y : FinitePath (Fin r → Bool) (L+1)) :
    direction (polarizedSpec hk ε a b d spinAnchor) σ y =
      (k:ℝ)⁻¹ * ∑ j, MarkSelector.sign (ε j) *
        (spin σ * MarkSelector.pathColor a b (fun t => (d t).castSucc) (some j) y) := by
  simp only [direction,polarizedSpec,cast_average,selector_eq_pathColor]
  rw [mul_assoc,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma polarized_anchor {L r k : ℕ} (hk : 0 < k) (ε : Fin k → Bool)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
    (σ : Spin) (y : FinitePath (Fin r → Bool) (L+1)) :
    anchor (polarizedSpec hk ε a b d spinAnchor) σ y =
      (if spinAnchor then spin σ else 1) *
        MarkSelector.pathColor a b (fun t => (d t).castSucc) none y := by
  change ((selector a b d none).1 (interior y) : ℝ) * (if spinAnchor then spin σ else 1) = _
  rw [selector_eq_pathColor,mul_comm]

/-- Every prescribed sharing history is a finite linear combination of the
literal universal dictionary coefficients, with the same old kernel. -/
theorem universal_constrained_polarization {Ω : Type} [Fintype Ω] {L r k : ℕ}
    (hk : 0 < k) (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (hm : ∀ j : Fin (L+1), m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last (L+1)) = 1)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
    (read : FinitePath Ω (L+1) → Spin)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf) (f : PrescribedTree.Sample Ω S → ℝ) :
    PrescribedTree.constrainedHistory T m a b (fun j => (d j).castSucc)
      (fun c x =>
        match c with
        | none => if spinAnchor then spin (read x) else 1
        | some _ => spin (read x)) S anchorLeaf f =
    ((k:ℝ)^k / 2^k) * ∑ ε : Fin k → Bool, (∏ j, Polarization.sign (ε j)) *
      PrescribedTree.anchorCoefficient S
        (KernelTower.prod (L+1) T (markPrior (L+1) (prior (polarizedSpec hk ε a b d spinAnchor)))) m
        (fun y => direction (polarizedSpec hk ε a b d spinAnchor)
          (read (KernelTower.pathFst (L+1) y)) (KernelTower.pathSnd (L+1) y)) anchorLeaf
        (fun x => f (PrescribedTree.sampleFst S x) *
          anchor (polarizedSpec hk ε a b d spinAnchor)
            (read (KernelTower.pathFst (L+1) (S.pathAt anchorLeaf x)))
            (KernelTower.pathSnd (L+1) (S.pathAt anchorLeaf x))) k := by
  rw [PrescribedTree.constrainedHistory_polarization hk T m hm hroot hend]
  congr 1
  apply Finset.sum_congr rfl
  intro ε _
  congr 1
  apply congrArg₂ (fun D G => PrescribedTree.anchorCoefficient S
    (KernelTower.prod (L+1) T (markPrior (L+1) (prior (polarizedSpec hk ε a b d spinAnchor)))) m D anchorLeaf G k)
  · funext y
    erw [polarized_direction]
    simp only [Polarization.averageDirection,Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
    rfl
  · funext x
    erw [polarized_anchor]
    rfl

end DilutedSpinGlass.UniversalDictionary
end

end

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

/-- The physical family is now fixed once and for all. Its rational auxiliary
mark dictionary simultaneously contains every finite signed polarization and
both spin and marker anchors, without changing any old reservoir for new probes. -/
theorem universal_analytic_selection {L p : ℕ} (m : Fin (L+1) → ℝ)
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
      (∀ j, Tendsto (fun n => ConcreteReservoir.scoreError (weights L) prior m direction anchor
        M C H j (Ns n+1) (us n)) atTop (𝓝 0)) ∧
      (∀ (S : PrescribedTree (L+1)) (a : S.Leaf)
        (f : (n : ℕ) → (S.Leaf → FinitePath (Fin (Ns n+1) → Spin) (L+1)) → ℝ)
        (B : ℝ), 0 ≤ B → (∀ n x, |f n x| ≤ B) → ∀ q k,
        Tendsto (fun n => ConcreteReservoir.physicalCoefficient (weights L) prior m direction anchor
          S a M C H (Ns n+1) (us n) (f n) q k) atTop (𝓝 0)) := by
  exact ConcreteReservoir.actual_analytic_selection (weights L) prior m direction anchor M hC hH hc
    hθ hh hθi hhi hm hmono hend weights_pos direction_bound anchor_bound hε

end DilutedSpinGlass.UniversalDictionary
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I] {n N : ℕ}

/-- The normalized product of all leaves, with the exact zero-size convention. -/
noncomputable def treeOverlap (S : PrescribedTree n) (f : FinitePath Ω n → Fin N → ℝ)
    (z : Sample Ω S) : ℝ := (∑ i, leafProduct S (fun x => f x i) z)/(N:ℝ)

omit [Fintype Ω] in
lemma treeOverlap_bound (S : PrescribedTree n) (f : FinitePath Ω n → Fin N → ℝ)
    (hf : ∀ x i, |f x i| ≤ 1) (z : Sample Ω S) : |treeOverlap S f z| ≤ 1 := by
  unfold treeOverlap
  have h := FiniteLaw.abs_dot_le_one (fun i => leafProduct S (fun x => f x i) z)
    (fun _ => (1:ℝ)) (fun i => leafProduct_bound S (fun x => hf x i) z) (fun _ => by norm_num)
  simpa only [FiniteLaw.dot,mul_one] using h

omit [Fintype Ω] in
lemma treeOverlap_unary (S : PrescribedTree n) (f : FinitePath Ω (n+1) → Fin N → ℝ)
    (z : Sample Ω (unary S)) :
    treeOverlap (unary S) f z=treeOverlap S (fun y => f ((z 0).1,y)) (z 0).2 := by
  simp only [treeOverlap,leafProduct_unary]

/-- Proper-child covariance at the later first split, retaining the entire
original evaluation prefix. These are genuine iterated kernel expectations. -/
noncomputable def descendantEnergyAt (C : PrescribedTree n) (r : ℕ) : (d : ℕ) →
    KernelTower Ω (n+1+r+1+d) → (FinitePath Ω (n+1+r+1+d) → Fin N → ℝ) → ℝ
  | 0,T,f => shapeEnergyAt C (r+1) T f
  | d+1,T,f => T.1.expect (fun x => descendantEnergyAt C r d (T.2 x) (fun y => f (x,y)))

lemma descendantEnergyAt_nonneg (C : PrescribedTree n) (r d : ℕ)
    (T : KernelTower Ω (n+1+r+1+d)) (f : FinitePath Ω (n+1+r+1+d) → Fin N → ℝ) :
    0 ≤ descendantEnergyAt C r d T f := by
  induction d with
  | zero => exact shapeEnergyAt_nonneg C (r+1) T f
  | succ d ih => exact T.1.expect_nonneg (fun x => ih (T.2 x) (fun y => f (x,y)))

/-- Exact identification of the old error in the signed identity with the
conditional two-copy error of the whole multileaf shape, at arbitrary d. -/
lemma oldProjectionError_prefixed_sq (S : PrescribedTree n) (a : S.Leaf) (d : ℕ)
    (T : KernelTower Ω (n+1+d)) (f X : FinitePath Ω (n+1+d) → Fin N → ℝ) :
    (oldProjectionError (stem (doubled S) d) T (stemLeaf (doubled S) d ⟨0,a⟩)
      (stemLeaf (doubled S) d ⟨1,a⟩) (treeOverlap (stem (doubled S) d) f) X)^2 =
      shapeProjectionSqAt S a d T f X := by
  induction d with
  | zero =>
    have h := oldProjectionError_doubled_sq S a T f X
    have he : doubledOverlap S f=treeOverlap (doubled S) f := funext (doubledOverlap_eq S f)
    rw [he] at h
    exact h
  | succ d ih =>
    rw [oldProjectionError,FiniteLaw.l2_sq]
    let F := fun z : Ω × Sample Ω (stem (doubled S) d) =>
      (FiniteLaw.dot (X (z.1, (stem (doubled S) d).pathAt (stemLeaf (doubled S) d ⟨0,a⟩) z.2))
        (X (z.1, (stem (doubled S) d).pathAt (stemLeaf (doubled S) d ⟨1,a⟩) z.2))-
        treeOverlap (stem (doubled S) d) (fun y => f (z.1,y)) z.2)^2
    have he : (sampleLaw (stem (doubled S) (d+1)) T).expect (fun z =>
        (FiniteLaw.dot (X ((stem (doubled S) (d+1)).pathAt (stemLeaf (doubled S) (d+1) ⟨0,a⟩) z))
          (X ((stem (doubled S) (d+1)).pathAt (stemLeaf (doubled S) (d+1) ⟨1,a⟩) z))-
          treeOverlap (stem (doubled S) (d+1)) f z)^2)=
        T.1.expect (fun x => (sampleLaw (stem (doubled S) d) (T.2 x)).expect (fun z => F (x,z))) := by
      refine Eq.trans ?_ (sampleLaw_unary_expect (stem (doubled S) d) T F)
      apply FiniteLaw.expect_congr
      intro z
      dsimp only [F]
      rw [show treeOverlap (stem (doubled S) (d+1)) f z=
        treeOverlap (stem (doubled S) d) (fun y => f ((z 0).1,y)) (z 0).2 from treeOverlap_unary _ f z]
      rfl
    rw [he]
    apply FiniteLaw.expect_congr
    intro x
    have h := ih (T.2 x) (fun y => f (x,y)) (fun y => X (x,y))
    rw [oldProjectionError,FiniteLaw.l2_sq] at h
    exact h

/-- The projection energy uses only proper-child energies even when the
first evaluation depth is not the root. No prefix is discarded. -/
theorem prefixed_stem_projection_sq_le (k : ℕ+) (C : Fin k → PrescribedTree n)
    (a : (PrescribedTree.node k C).Leaf) (r d : ℕ) (T : KernelTower Ω (n+1+r+1+d))
    (f : FinitePath Ω (n+1+r+1+d) → Fin N → ℝ) (hf : ∀ x i, |f x i| ≤ 1) :
    shapeProjectionSqAt (stem (.node k C) r) (stemLeaf (.node k C) r a) d T f
      (fun x i => splitProjector (.node k C) r d T (fun y => f y i) x) ≤
      4*(k:ℝ)*∑ i, Real.sqrt (descendantEnergyAt (C i) r d T f) := by
  induction d with
  | zero => exact branchProjectionSq_stem_le k C a r T f hf
  | succ d ih =>
    change T.1.expect (fun x => shapeProjectionSqAt (stem (.node k C) r)
      (stemLeaf (.node k C) r a) d (T.2 x) (fun y => f (x,y))
        (fun y i => splitProjector (.node k C) r d (T.2 x) (fun z => f (x,z) i) y)) ≤ _
    have h := T.1.expect_mono (fun x => ih (T.2 x) (fun y => f (x,y)) (fun y => hf (x,y)))
    rw [FiniteLaw.expect_mul_left,FiniteLaw.expect_fintype_sum] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro i _
    exact T.1.expect_sqrt_le _ (fun x => descendantEnergyAt_nonneg (C i) r d (T.2 x) (fun y => f (x,y)))

/-- The exact actual whole-shape covariance with both evaluation and first
split at arbitrary depths, bounded by the full projected three-copy term. -/
theorem prefixed_stem_covariance_three_copy_le (k : ℕ+) (C : Fin k → PrescribedTree n)
    (a : (PrescribedTree.node k C).Leaf) (r d : ℕ) (T : KernelTower Ω (n+1+r+1+d))
    (f : FinitePath Ω (n+1+r+1+d) → Fin N → ℝ) (hf : ∀ x i, |f x i| ≤ 1) :
    shapeEnergyAt (stem (.node k C) r) d T f ≤
      2*KernelTower.halfTripleDifferenceAt (n+1+r+1+d) T d
        (fun x i => splitProjector (.node k C) r d T (fun y => f y i) x)+
      16*(k:ℝ)*∑ i, Real.sqrt (descendantEnergyAt (C i) r d T f) := by
  have h := shape_energy_projection_transfer (stem (.node k C) r)
    (stemLeaf (.node k C) r a) d T f
    (fun x i => splitProjector (.node k C) r d T (fun y => f y i) x)
  have he := prefixed_stem_projection_sq_le k C a r d T f hf
  linarith

/-- The L2 old-test error in the prescribed-tree identity, not merely a
projected covariance, now has its explicit proper-child bound. -/
theorem prefixed_stem_old_error_le (k : ℕ+) (C : Fin k → PrescribedTree n)
    (a : (PrescribedTree.node k C).Leaf) (r d : ℕ) (T : KernelTower Ω (n+1+r+1+d))
    (f : FinitePath Ω (n+1+r+1+d) → Fin N → ℝ) (hf : ∀ x i, |f x i| ≤ 1) :
    let S := stem (.node k C) r
    oldProjectionError (stem (doubled S) d) T (stemLeaf (doubled S) d ⟨0,stemLeaf (.node k C) r a⟩)
      (stemLeaf (doubled S) d ⟨1,stemLeaf (.node k C) r a⟩)
      (treeOverlap (stem (doubled S) d) f)
      (fun x i => splitProjector (.node k C) r d T (fun y => f y i) x) ≤
      2*Real.sqrt ((k:ℝ)*∑ i, Real.sqrt (descendantEnergyAt (C i) r d T f)) := by
  dsimp only
  have h := prefixed_stem_projection_sq_le k C a r d T f hf
  rw [← oldProjectionError_prefixed_sq] at h
  have hn : 0 ≤ (k:ℝ)*∑ i, Real.sqrt (descendantEnergyAt (C i) r d T f) := by positivity
  have he : (2*Real.sqrt ((k:ℝ)*∑ i, Real.sqrt (descendantEnergyAt (C i) r d T f)))^2=
      4*(k:ℝ)*∑ i, Real.sqrt (descendantEnergyAt (C i) r d T f) := by
    rw [mul_pow,Real.sq_sqrt hn]
    ring
  have hn2 : 0 ≤ 2*Real.sqrt ((k:ℝ)*∑ i, Real.sqrt (descendantEnergyAt (C i) r d T f)) := by positivity
  nlinarith

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
