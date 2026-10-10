import OAI.Probability.DilutedSpin.KernelTower

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

/-- Prescribed trees include a vertex at every depth, including unary vertices.
Every internal vertex has at least one child; every leaf has the given height. -/
inductive PrescribedTree : ℕ → Type
  | leaf : PrescribedTree 0
  | node {n : ℕ} (k : ℕ+) (children : Fin k → PrescribedTree n) : PrescribedTree (n+1)

namespace PrescribedTree

noncomputable def leaves : {n : ℕ} → PrescribedTree n → ℕ
  | 0, .leaf => 1
  | _+1, .node _ T => ∑ i, leaves (T i)

/-- Sum of the fresh-extension coefficients gamma_beta. -/
noncomputable def freshTotal (m : ℕ → ℝ) (d : ℕ) : {n : ℕ} → PrescribedTree n → ℝ
  | 0, .leaf => 0
  | _+1, .node k T => m d - (k : ℝ) * m (d+1) + ∑ i, freshTotal m (d+1) (T i)

/-- Sum of their absolute values. -/
noncomputable def freshAbsolute (m : ℕ → ℝ) (d : ℕ) : {n : ℕ} → PrescribedTree n → ℝ
  | 0, .leaf => 0
  | _+1, .node k T => |m d - (k : ℝ) * m (d+1)| +
      ∑ i, freshAbsolute m (d+1) (T i)

/-- The exact telescoping normalization before specializing m_L=1. -/
theorem fresh_total {n : ℕ} (T : PrescribedTree n) (m : ℕ → ℝ) (d : ℕ) :
    freshTotal m d T = m d - leaves T * m (d+n) := by
  induction T generalizing d with
  | leaf => simp [freshTotal, leaves]
  | @node n k T ih =>
    simp only [freshTotal, leaves, ih, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sum]
    rw [← Finset.sum_mul]
    have hdepth : d+1+n = d+(n+1) := by omega
    rw [hdepth]
    ring

theorem fresh_absolute_eq_neg {n : ℕ} (T : PrescribedTree n) (m : ℕ → ℝ)
    (hm : Monotone m) (hpos : ∀ d, 0 ≤ m d) (d : ℕ) :
    freshAbsolute m d T = -freshTotal m d T := by
  induction T generalizing d with
  | leaf => simp [freshAbsolute, freshTotal]
  | @node n k T ih =>
    have hk : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast k.property
    have hstep := hm (Nat.le_succ d)
    have hg : m d - (k : ℝ) * m (d+1) ≤ 0 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hk) (hpos (d+1))]
    simp only [freshAbsolute, freshTotal, abs_of_nonpos hg, ih, Finset.sum_neg_distrib]
    ring

/-- tree:telescoping. At root depth zero the absolute fresh-choice budget is
exactly the number of old leaves, uniformly over the number of levels. -/
theorem fresh_absolute_root {n : ℕ} (T : PrescribedTree n) (m : ℕ → ℝ)
    (hm : Monotone m) (hpos : ∀ d, 0 ≤ m d) (hzero : m 0 = 0) (hend : m n = 1) :
    freshAbsolute m 0 T = leaves T := by
  rw [fresh_absolute_eq_neg T m hm hpos, fresh_total]
  simp only [hzero, zero_add, hend, mul_one, zero_sub, neg_neg]

/-- The sum of old-leaf and fresh choices in a reference-free subtree is
m at its incoming depth. This is the nontrivial cancellation used to sum
reference-constrained extensions, not their absolute values. -/
theorem unused_subtree_total {n : ℕ} (T : PrescribedTree n) (m : ℕ → ℝ)
    (d : ℕ) (hend : m (d+n) = 1) :
    (leaves T : ℝ) + freshTotal m d T = m d := by
  rw [fresh_total, hend]
  ring

/-- The next color must avoid precisely the reference-containing children.
All unused subtrees cancel to m_(d+1), giving the required local coefficient. -/
theorem reference_total {n : ℕ} (k : ℕ+) (T : Fin k → PrescribedTree n)
    (m : ℕ → ℝ) (d : ℕ) (J : Finset (Fin k)) (hend : m (d+1+n) = 1) :
    m d - (k : ℝ) * m (d+1) +
      (∑ i ∈ Finset.univ \ J, ((leaves (T i) : ℝ) + freshTotal m (d+1) (T i))) =
        m d - (J.card : ℝ) * m (d+1) := by
  classical
  simp only [unused_subtree_total _ m (d+1) hend, Finset.sum_const, nsmul_eq_mul]
  have hsub : J ⊆ Finset.univ := Finset.subset_univ _
  rw [Finset.card_sdiff, Finset.inter_univ, Nat.cast_sub (Finset.card_le_card hsub)]
  simp only [Finset.card_univ, Fintype.card_fin]
  ring

end PrescribedTree
end DilutedSpinGlass

namespace DilutedSpinGlass.PrescribedTree

/-- Samples at separate sibling vertices are independent; repeated values are
allowed. The full unary parts of each prescribed tree are retained. -/
def Sample (Ω : Type) : {n : ℕ} → PrescribedTree n → Type
  | 0, .leaf => Unit
  | _+1, .node k C => (i : Fin k) → Ω × Sample Ω (C i)

instance sampleFintype (Ω : Type) [Fintype Ω] : {n : ℕ} →
    (S : PrescribedTree n) → Fintype (Sample Ω S)
  | 0, .leaf => inferInstanceAs (Fintype Unit)
  | _+1, .node k C => by
      letI : ∀ i, Fintype (Sample Ω (C i)) := fun i => sampleFintype Ω (C i)
      exact inferInstanceAs (Fintype ((i : Fin k) → Ω × Sample Ω (C i)))

variable {Ω : Type} [Fintype Ω]

noncomputable def sampleLaw : {n : ℕ} → (S : PrescribedTree n) →
    KernelTower Ω n → FiniteLaw (Sample Ω S)
  | 0, .leaf, _ => KernelTower.unitLaw
  | _+1, .node _ C, T => FiniteLaw.pi (fun i => T.1.bind (fun x => sampleLaw (C i) (T.2 x)))

/-- The logarithm of the vertex product in tree:density. The first entry of
m is the incoming edge exponent (zero at the root); the final entry equals
one in the manuscript applications. -/
noncomputable def vertexPotential : {n : ℕ} → (S : PrescribedTree n) →
    KernelTower Ω n → (Fin (n+1) → ℝ) → (FinitePath Ω n → ℝ) → Sample Ω S → ℝ
  | 0, .leaf, _, m, f, _ => m 0 * f ()
  | n+1, .node k C, T, m, f, x =>
      (m 0 - (k : ℝ) * m 1) * KernelTower.backwardLog (n+1) T (fun j => m j.succ) f +
      ∑ i, vertexPotential (C i) (T.2 (x i).1) (fun j => m j.succ)
        (fun y => f ((x i).1,y)) (x i).2

/-- Exact joint law after insertion, expressed without division by the old
weight. This handles zero-probability paths and every prescribed tree. -/
theorem sampleLaw_tilt_weight {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (f : FinitePath Ω n → ℝ)
    (x : Sample Ω S) :
    (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) f)).weight x =
      (sampleLaw S T).weight x * Real.exp
        (vertexPotential S T m f x - m 0 * KernelTower.backwardLog n T (fun j => m j.succ) f) := by
  induction S with
  | leaf => simp [sampleLaw, vertexPotential, KernelTower.unitLaw, KernelTower.backwardLog]
  | @node n k C ih =>
    let F := fun z => KernelTower.backwardLog n (T.2 z)
      (fun j => m j.succ.succ) (fun y => f (z,y))
    let B := KernelTower.backwardLog (n+1) T (fun j => m j.succ) f
    let V := fun i => vertexPotential (C i) (T.2 (x i).1) (fun j => m j.succ)
      (fun y => f ((x i).1,y)) (x i).2
    have hedge : ∀ i, ((T.1.tilt (m 1) F).bind (fun z => sampleLaw (C i)
        (KernelTower.tilt n (T.2 z) (fun j => m j.succ.succ) (fun y => f (z,y))))).weight (x i) =
        (T.1.bind (fun z => sampleLaw (C i) (T.2 z))).weight (x i) *
          Real.exp (V i - m 1 * B) := by
      intro i
      simp only [FiniteLaw.bind]
      rw [FiniteLaw.tilt_weight _ (show m 1 ≠ 0 by simpa using hm 0), ih i (T.2 (x i).1) (fun j => m j.succ)
        (fun j => hm j.succ) (fun y => f ((x i).1,y)) (x i).2]
      change (_ * Real.exp (m 1 * (F (x i).1 - B))) *
        (_ * Real.exp (V i - m 1 * F (x i).1)) = _
      rw [mul_mul_mul_comm, ← Real.exp_add]
      congr 2
      ring
    change (∏ i, ((T.1.tilt (m 1) F).bind (fun z => sampleLaw (C i)
        (KernelTower.tilt n (T.2 z) (fun j => m j.succ.succ) (fun y => f (z,y))))).weight (x i)) = _
    simp_rw [hedge]
    rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    change (_ * Real.exp (∑ i, (V i - m 1 * B))) =
      _ * Real.exp (((m 0 - (k : ℝ) * m 1) * B + ∑ i, V i) - m 0 * B)
    congr 2
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring

/-- At the tree root there is no incoming edge. This is the self-contained,
finite-kernel version of tree:density, with exactly its vertex exponents. -/
theorem sampleLaw_tilt_density {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0)
    (f : FinitePath Ω n → ℝ) (x : Sample Ω S) :
    (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) f)).weight x =
      (sampleLaw S T).weight x * Real.exp (vertexPotential S T m f x) := by
  rw [sampleLaw_tilt_weight S T m hm f x, hroot, zero_mul, sub_zero]

/-- First variation of the vertex product: one score for every uncontracted
leaf, and gamma_beta times the score of a fresh path at every internal vertex. -/
noncomputable def vertexScore : {n : ℕ} → (S : PrescribedTree n) →
    KernelTower Ω n → (Fin (n+1) → ℝ) → (FinitePath Ω n → ℝ) →
      (FinitePath Ω n → ℝ) → Sample Ω S → ℝ
  | 0, .leaf, _, m, _, f', _ => m 0 * f' ()
  | n+1, .node k C, T, m, f, f', x =>
      (m 0 - (k : ℝ) * m 1) *
        (KernelTower.law (n+1) (KernelTower.tilt (n+1) T (fun j => m j.succ) f)).expect f' +
        ∑ i, vertexScore (C i) (T.2 (x i).1) (fun j => m j.succ)
          (fun y => f ((x i).1,y)) (fun y => f' ((x i).1,y)) (x i).2

/-- Differentiate the entire prescribed tree density, without assuming all
sampled prefixes are distinct or all original kernel weights positive. -/
theorem hasDerivAt_vertexPotential {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0)
    {f : ℝ → FinitePath Ω n → ℝ} {f' : FinitePath Ω n → ℝ} {u : ℝ}
    (hf : ∀ y, HasDerivAt (fun t => f t y) (f' y) u) (x : Sample Ω S) :
    HasDerivAt (fun t => vertexPotential S T m (f t) x)
      (vertexScore S T m (f u) f' x) u := by
  induction S with
  | leaf => exact (hf ()).const_mul (m 0)
  | @node n k C ih =>
    have ha := (KernelTower.hasDerivAt_backwardLog (n+1) T (fun j => m j.succ) hm hf).const_mul
      (m 0 - (k : ℝ) * m 1)
    have hb := HasDerivAt.sum (u := Finset.univ) (fun i _ => ih i (T.2 (x i).1)
      (fun j => m j.succ) (fun j => hm j.succ) (fun y => hf ((x i).1,y)) (x i).2)
    have heq : (∑ i, (fun t => vertexPotential (C i) (T.2 (x i).1) (fun j => m j.succ)
        (fun y => f t ((x i).1,y)) (x i).2)) =
        (fun t => ∑ i, vertexPotential (C i) (T.2 (x i).1) (fun j => m j.succ)
          (fun y => f t ((x i).1,y)) (x i).2) := by
      funext t
      simp only [Finset.sum_apply]
    rw [heq] at hb
    exact ha.add hb

/-- Joint-law density in expectation form; physical root remains fixed. -/
theorem sampleLaw_tilt_expect {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0)
    (f : FinitePath Ω n → ℝ) (G : Sample Ω S → ℝ) :
    (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) f)).expect G =
      (sampleLaw S T).expect (fun x => G x * Real.exp (vertexPotential S T m f x)) := by
  unfold FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro x _
  rw [sampleLaw_tilt_density S T m hm hroot]
  ring

/-- Tree differentiation rule, including a parameter-dependent test. Choosing
G as a product of canceled replica factors yields the protected-leaf rule. -/
theorem hasDerivAt_sampleLaw_tilt_expect {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0)
    {f : ℝ → FinitePath Ω n → ℝ} {f' : FinitePath Ω n → ℝ}
    {G : ℝ → Sample Ω S → ℝ} {G' : Sample Ω S → ℝ} {u : ℝ}
    (hf : ∀ y, HasDerivAt (fun t => f t y) (f' y) u)
    (hG : ∀ x, HasDerivAt (fun t => G t x) (G' x) u) :
    HasDerivAt (fun t => (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f t))).expect (G t))
      ((sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f u))).expect
        (fun x => G' x + G u x * vertexScore S T m (f u) f' x)) u := by
  simp_rw [sampleLaw_tilt_expect S T m hm hroot]
  have hd := (sampleLaw S T).hasDerivAt_expect (fun x =>
    (hG x).mul (hasDerivAt_vertexPotential S T m hm hf x).exp)
  apply hd.congr_deriv
  apply (sampleLaw S T).expect_congr
  intro x
  ring

/-- A leaf label is a vertex, not its sampled spin value. -/
def Leaf : {n : ℕ} → PrescribedTree n → Type
  | 0, .leaf => Unit
  | _+1, .node k C => (i : Fin k) × Leaf (C i)

instance leafFintype : {n : ℕ} → (S : PrescribedTree n) → Fintype (Leaf S)
  | 0, .leaf => inferInstanceAs (Fintype Unit)
  | _+1, .node k C => by
    letI : ∀ i, Fintype (Leaf (C i)) := fun i => leafFintype (C i)
    exact inferInstanceAs (Fintype ((i : Fin k) × Leaf (C i)))

/-- Recover a whole path from a labeled leaf in a sampled tree. -/
def pathAt : {n : ℕ} → (S : PrescribedTree n) → Leaf S → Sample Ω S → FinitePath Ω n
  | 0, .leaf, _, _ => ()
  | _+1, .node _ C, a, x => ((x a.1).1, pathAt (C a.1) a.2 (x a.1).2)

/-- Exactly the denominator cancellation at the selected protected leaves,
written in logarithmic form. -/
noncomputable def protectedLog {n : ℕ} (S : PrescribedTree n) (C : Finset (Leaf S))
    (f : FinitePath Ω n → ℝ) (x : Sample Ω S) : ℝ :=
  ∑ a ∈ C, f (pathAt S a x)

omit [Fintype Ω] in
theorem hasDerivAt_protectedLog {n : ℕ} (S : PrescribedTree n) (C : Finset (Leaf S))
    {f : ℝ → FinitePath Ω n → ℝ} {f' : FinitePath Ω n → ℝ} {u : ℝ}
    (hf : ∀ y, HasDerivAt (fun t => f t y) (f' y) u) (x : Sample Ω S) :
    HasDerivAt (fun t => protectedLog S C (f t) x) (protectedLog S C f' x) u := by
  have hd := HasDerivAt.sum (u := C) (fun a _ => hf (pathAt S a x))
  have heq : (∑ a ∈ C, (fun t => f t (pathAt S a x))) =
      (fun t => protectedLog S C (f t) x) := by
    funext t
    simp only [Finset.sum_apply, protectedLog]
  rw [heq] at hd
  exact hd

 
theorem hasDerivAt_protected_expect {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0)
    (C : Finset (Leaf S)) (G : Sample Ω S → ℝ)
    {f : ℝ → FinitePath Ω n → ℝ} {f' : FinitePath Ω n → ℝ} {u : ℝ}
    (hf : ∀ y, HasDerivAt (fun t => f t y) (f' y) u) :
    HasDerivAt (fun t => (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f t))).expect
      (fun x => G x * Real.exp (-protectedLog S C (f t) x)))
      ((sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f u))).expect
        (fun x => (G x * Real.exp (-protectedLog S C (f u) x)) *
          (vertexScore S T m (f u) f' x - protectedLog S C f' x))) u := by
  have hg := fun x => ((hasDerivAt_protectedLog S C hf x).neg.exp).const_mul (G x)
  have hd := hasDerivAt_sampleLaw_tilt_expect S T m hm hroot hf hg
  apply hd.congr_deriv
  apply FiniteLaw.expect_congr
  intro x
  change G x * (Real.exp (-protectedLog S C (f u) x) * -protectedLog S C f' x) +
    G x * Real.exp (-protectedLog S C (f u) x) * vertexScore S T m (f u) f' x = _
  ring

/-- For positive affine insertions, the logarithmic score is D/A, with the
actual (not a formal or assumed) analytic derivative. -/
theorem hasDerivAt_log_affine {D u : ℝ} (hu : 1 + u*D ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log (1+t*D)) (D/(1+u*D)) u := by
  simpa using (((hasDerivAt_id u).mul_const D).const_add 1).log hu

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

/-- Internal vertices refer to labeled genealogy, not coincident sampled values. -/
def Internal : {n : ℕ} → PrescribedTree n → Type
  | 0, .leaf => Empty
  | _+1, .node _ C => Option ((i : _) × Internal (C i))

instance internalFintype : {n : ℕ} → (S : PrescribedTree n) → Fintype (Internal S)
  | 0, .leaf => inferInstanceAs (Fintype Empty)
  | _+1, .node k C => by
    letI : ∀ i, Fintype (Internal (C i)) := fun i => internalFintype (C i)
    exact inferInstanceAs (Fintype (Option ((i : Fin k) × Internal (C i))))

/-- The signed coefficient at the exact uncontracted divergence vertex. -/
noncomputable def gamma : {n : ℕ} → (S : PrescribedTree n) →
    (Fin (n+1) → ℝ) → Internal S → ℝ
  | 0, .leaf, _, v => nomatch v
  | _+1, .node k C, m, v =>
      match (v : Option ((i : Fin k) × Internal (C i))) with
      | none => m 0 - (k : ℝ) * m 1
      | some ⟨i,v⟩ => gamma (C i) (fun j => m j.succ) v

variable {Ω : Type} [Fintype Ω]

/-- Conditional expectation on a completely new path below the chosen vertex.
Old sampled descendants are NOT reused, even if their values happen to agree. -/
noncomputable def freshEval : {n : ℕ} → (S : PrescribedTree n) →
    KernelTower Ω n → Internal S → (FinitePath Ω n → ℝ) → Sample Ω S → ℝ
  | 0, .leaf, _, v, _, _ => nomatch v
  | n+1, .node k C, T, v, D, x =>
      match (v : Option ((i : Fin k) × Internal (C i))) with
      | none => (KernelTower.law (n+1) T).expect D
      | some ⟨i,v⟩ => freshEval (C i) (T.2 (x i).1) v (fun y => D ((x i).1,y)) (x i).2

/-- Resolves the differentiated density into terminal contributions and actual
fresh conditional path expectations. No diagonal identification is made. -/
theorem vertexScore_decomposition {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (f D : FinitePath Ω n → ℝ) (x : Sample Ω S) :
    vertexScore S T m f D x =
      m (Fin.last n) * (∑ a : Leaf S, D (pathAt S a x)) +
      ∑ v : Internal S, gamma S m v *
        freshEval S (KernelTower.tilt n T (fun j => m j.succ) f) v D x := by
  induction S with
  | leaf =>
    change m 0 * D () = m 0 * (∑ a : Unit, D ()) + ∑ v : Empty, _
    simp
  | @node n k C ih =>
    let T' := KernelTower.tilt (n+1) T (fun j => m j.succ) f
    have hL : (∑ a : Leaf (.node k C), D (pathAt (.node k C) a x)) =
        ∑ i, ∑ a : Leaf (C i), D ((x i).1, pathAt (C i) a (x i).2) :=
      Fintype.sum_sigma _
    have hI : (∑ v : Internal (.node k C), gamma (.node k C) m v *
        freshEval (.node k C) T' v D x) =
        (m 0 - (k : ℝ) * m 1) * (KernelTower.law (n+1) T').expect D +
        ∑ i, ∑ v : Internal (C i), gamma (C i) (fun j => m j.succ) v *
          freshEval (C i) (KernelTower.tilt n (T.2 (x i).1)
            (fun j => m j.succ.succ) (fun y => f ((x i).1,y))) v
              (fun y => D ((x i).1,y)) (x i).2 := by
      change (∑ v : Option ((i : Fin k) × Internal (C i)), _) = _
      rw [Fintype.sum_option, Fintype.sum_sigma]
      rfl
    change (m 0 - (k : ℝ) * m 1) * (KernelTower.law (n+1) T').expect D +
      (∑ i, vertexScore (C i) (T.2 (x i).1) (fun j => m j.succ)
        (fun y => f ((x i).1,y)) (fun y => D ((x i).1,y)) (x i).2) = _
    rw [hL, hI]
    simp_rw [ih]
    simp only [Finset.sum_add_distrib, Fin.succ_last, Finset.mul_sum]
    ring

/-- Exact finite-kernel form of the protected-leaf differentiation rule.
The second line is the expectation on a fresh extended path, conditional on
its shared prefix. The canceled leaves are removed, not merely bounded. -/
theorem protected_leaf_extension_rule {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    [DecidableEq (Leaf S)] (C : Finset (Leaf S)) (G : Sample Ω S → ℝ)
    {f : ℝ → FinitePath Ω n → ℝ} {D : FinitePath Ω n → ℝ} {u : ℝ}
    (hf : ∀ y, HasDerivAt (fun t => f t y) (D y) u) :
    HasDerivAt (fun t => (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f t))).expect
      (fun x => G x * Real.exp (-protectedLog S C (f t) x)))
      ((sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f u))).expect
        (fun x => (G x * Real.exp (-protectedLog S C (f u) x)) *
          ((∑ a ∈ Finset.univ \ C, D (pathAt S a x)) +
            ∑ v : Internal S, gamma S m v *
              freshEval S (KernelTower.tilt n T (fun j => m j.succ) (f u)) v D x))) u := by
  classical
  apply (hasDerivAt_protected_expect S T m hm hroot C G hf).congr_deriv
  apply FiniteLaw.expect_congr
  intro x
  rw [vertexScore_decomposition, hend, one_mul]
  simp only [protectedLog]
  have hh : (∑ a ∈ Finset.univ \ C, D (pathAt S a x)) +
      (∑ a ∈ C, D (pathAt S a x)) = ∑ a, D (pathAt S a x) :=
    Finset.sum_sdiff (Finset.subset_univ C)
  rw [← hh]
  ring

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

def single : (n : ℕ) → PrescribedTree n
  | 0 => .leaf
  | n+1 => .node 1 (fun _ => single n)

/-- Attach a genuinely new child at the divergence vertex; keep every old
child and every unary level. Child 0 is the new child for root attachment. -/
def grow : {n : ℕ} → (S : PrescribedTree n) → Internal S → PrescribedTree n
  | 0, .leaf, v => nomatch v
  | n+1, .node k C, v =>
    match (v : Option ((i : Fin k) × Internal (C i))) with
    | none => .node (k+1) (Fin.cases (single n) C)
    | some ⟨i,v⟩ => .node k (Function.update C i (grow (C i) v))

variable {Ω : Type}

def singlePath : (n : ℕ) → Sample Ω (single n) → FinitePath Ω n
  | 0, _ => ()
  | n+1, x => ((x 0).1, singlePath n (x 0).2)

/-- The projection forgets the new branch but preserves every old value. -/
def oldSample : {n : ℕ} → (S : PrescribedTree n) → (v : Internal S) →
    Sample Ω (grow S v) → Sample Ω S
  | 0, .leaf, v => nomatch v
  | n+1, .node k C, v => by
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      intro x i
      exact x i.succ
    | some v =>
      obtain ⟨i,v⟩ := v
      intro x j
      by_cases h : j = i
      · subst j
        have y : Ω × Sample Ω (grow (C i) v) := by
          simpa only [grow, Function.update_self] using x i
        exact (y.1, oldSample (C i) v y.2)
      · have y : Ω × Sample Ω (C j) := by
          simpa only [grow, Function.update_of_ne h] using x j
        exact y

/-- The new path shares just its prescribed prefix, even for repeated values. -/
def newPath : {n : ℕ} → (S : PrescribedTree n) → (v : Internal S) →
    Sample Ω (grow S v) → FinitePath Ω n
  | 0, .leaf, v => nomatch v
  | n+1, .node k C, v => by
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      intro x
      exact ((x 0).1, singlePath n (x 0).2)
    | some v =>
      obtain ⟨i,v⟩ := v
      intro x
      have y : Ω × Sample Ω (grow (C i) v) := by
        simpa only [grow, Function.update_self] using x i
      exact (y.1, newPath (C i) v y.2)

end DilutedSpinGlass.PrescribedTree

end

end OAI
