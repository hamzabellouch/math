import OAI.Probability.DilutedSpin.FiniteAnalytic
import OAI.Probability.DilutedSpin.TreeMarkLaw

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

/-- All leaves protected, at a general positive insertion, not just along a
single direction. This retains the original finite-kernel law. -/
noncomputable def protectedAt {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) (G : Sample Ω S → ℝ)
    (A : FinitePath Ω n → ℝ) : ℝ :=
  (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ)
    (fun y => Real.log (A y)))).expect (fun x => G x *
      Real.exp (-leafSum S (fun y => Real.log (A y)) x))

lemma hasDerivAt_protectedAt {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (G : Sample Ω S → ℝ) {A : ℝ → FinitePath Ω n → ℝ} {D : FinitePath Ω n → ℝ} {u : ℝ}
    (hA : ∀ y, 0 < A u y) (hdA : ∀ y, HasDerivAt (fun t => A t y) (D y) u) :
    HasDerivAt (fun t => protectedAt S T m G (A t))
      (∑ v : Internal S, gamma S m v * protectedAt (grow S v) T m
        (fun x => G (oldSample S v x) * D (newPath S v x)) (A u)) u := by
  classical
  let f (t : ℝ) (y : FinitePath Ω n) := Real.log (A t y)
  let DL (y : FinitePath Ω n) := D y / A u y
  let T' := KernelTower.tilt n T (fun j => m j.succ) (f u)
  have hf (y : FinitePath Ω n) : HasDerivAt (fun t => f t y) (DL y) u :=
    (hdA y).log (hA y).ne'
  have hd := protected_leaf_extension_rule S T m hm hroot hend Finset.univ G hf
  have hfun : (fun t => (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f t))).expect
      (fun x => G x * Real.exp (-protectedLog S Finset.univ (f t) x))) =
      (fun t => protectedAt S T m G (A t)) := by
    funext t
    apply FiniteLaw.expect_congr
    intro x
    rw [leafSum_eq_sum]
    rfl
  rw [hfun] at hd
  apply hd.congr_deriv
  simp only [Finset.sdiff_self, Finset.sum_empty, zero_add]
  have hsum : (sampleLaw S T').expect (fun x =>
      (G x * Real.exp (-protectedLog S Finset.univ (f u) x)) *
      ∑ v : Internal S, gamma S m v * freshEval S T' v DL x) =
      ∑ v : Internal S, gamma S m v *
        (sampleLaw S T').expect (fun x =>
          (G x * Real.exp (-leafSum S (f u) x)) * freshEval S T' v DL x) := by
    simp only [Finset.mul_sum, FiniteLaw.expect_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [← FiniteLaw.expect_mul_left]
    apply FiniteLaw.expect_congr
    intro x
    rw [leafSum_eq_sum]
    change (G x * Real.exp (-∑ a, f u (pathAt S a x))) *
      (gamma S m v * freshEval S T' v DL x) = _
    ring
  refine hsum.trans (Finset.sum_congr rfl ?_)
  intro v _
  apply congrArg (gamma S m v * ·)
  rw [← extension_sampling S T' v (fun x => G x * Real.exp (-leafSum S (f u) x)) DL]
  apply FiniteLaw.expect_congr
  intro x
  change (G (oldSample S v x) * Real.exp (-leafSum S (f u) (oldSample S v x))) *
    (D (newPath S v x) / A u (newPath S v x)) =
    (G (oldSample S v x) * D (newPath S v x)) * Real.exp (-leafSum (grow S v) (f u) x)
  rw [leafSum_grow, neg_add, Real.exp_add]
  change _ = _ * (Real.exp (-leafSum S (f u) (oldSample S v x)) *
    Real.exp (-Real.log (A u (newPath S v x))))
  rw [Real.exp_neg (Real.log (A u (newPath S v x))), Real.exp_log (hA _)]
  ring

lemma hasDerivAt_protectedAt_varying {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    {G : ℝ → Sample Ω S → ℝ} {G' : Sample Ω S → ℝ}
    {A : ℝ → FinitePath Ω n → ℝ} {D : FinitePath Ω n → ℝ} {u : ℝ}
    (hA : ∀ y, 0 < A u y) (hdA : ∀ y, HasDerivAt (fun t => A t y) (D y) u)
    (hG : ∀ x, HasDerivAt (fun t => G t x) (G' x) u) :
    HasDerivAt (fun t => protectedAt S T m (G t) (A t))
      (protectedAt S T m G' (A u) +
       ∑ v : Internal S, gamma S m v * protectedAt (grow S v) T m
        (fun x => G u (oldSample S v x) * D (newPath S v x)) (A u)) u := by
  let f t y := Real.log (A t y)
  let DL y := D y / A u y
  have hf y : HasDerivAt (fun t => f t y) (DL y) u := (hdA y).log (hA y).ne'
  have hproto := hasDerivAt_protected_expect S T m hm hroot Finset.univ (G u) hf
  have hvar := hasDerivAt_protected_expect_varying S T m hm hroot Finset.univ hf hG
  have hfull := hasDerivAt_protectedAt S T m hm hroot hend (G u) hA hdA
  have heq (H : Sample Ω S → ℝ) (t : ℝ) :
      (sampleLaw S (KernelTower.tilt n T (fun j => m j.succ) (f t))).expect
        (fun x => H x * Real.exp (-protectedLog S Finset.univ (f t) x)) =
        protectedAt S T m H (A t) := by
    apply FiniteLaw.expect_congr
    intro x
    rw [leafSum_eq_sum]
    rfl
  simp_rw [heq] at hproto hvar
  rw [hproto.unique hfull] at hvar
  exact hvar

/-- A subset of old positions remains unused. Every used old position and
all fresh colored positions are canceled. -/
noncomputable def anchorAt {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) {ι : Type} (U : Finset ι)
    (paths : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ)
    (A : FinitePath Ω n → ℝ) : ℝ :=
  protectedAt S T m (fun x => G x * ∏ i ∈ U, A (paths i x)) A

lemma protectedAt_sum {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ) {ι : Type} (U : Finset ι)
    (G : ι → Sample Ω S → ℝ) (A : FinitePath Ω n → ℝ) :
    protectedAt S T m (fun x => ∑ i ∈ U, G i x) A = ∑ i ∈ U, protectedAt S T m (G i) A := by
  unfold protectedAt
  simp only [Finset.sum_mul, FiniteLaw.expect_sum]

lemma hasDerivAt_anchorAt {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    {ι : Type} [DecidableEq ι] (U : Finset ι)
    (paths : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ)
    {A : ℝ → FinitePath Ω n → ℝ} {D : FinitePath Ω n → ℝ} {u : ℝ}
    (hA : ∀ y, 0 < A u y) (hdA : ∀ y, HasDerivAt (fun t => A t y) (D y) u) :
    HasDerivAt (fun t => anchorAt S T m U paths G (A t))
      ((∑ i ∈ U, anchorAt S T m (U.erase i) paths (fun x => G x * D (paths i x)) (A u)) +
       ∑ v : Internal S, gamma S m v * anchorAt (grow S v) T m U
        (fun i x => paths i (oldSample S v x))
        (fun x => G (oldSample S v x) * D (newPath S v x)) (A u)) u := by
  have hprod (x : Sample Ω S) :
      HasDerivAt (fun t : ℝ => G x * ∏ i ∈ U, A t (paths i x))
        (∑ i ∈ U, (G x * D (paths i x)) * ∏ j ∈ U.erase i, A u (paths j x)) u := by
    have hh := (HasDerivAt.fun_finsetProd (u := U) (fun i _ => hdA (paths i x))).const_mul (G x)
    apply hh.congr_deriv
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [smul_eq_mul]
    ring
  have hd := hasDerivAt_protectedAt_varying S T m hm hroot hend hA hdA hprod
  apply hd.congr_deriv
  rw [protectedAt_sum]
  apply congrArg₂ (· + ·)
  · rfl
  · apply Finset.sum_congr rfl
    intro v _
    apply congrArg (gamma S m v * ·)
    apply FiniteLaw.expect_congr
    intro x
    change ((G (oldSample S v x) * ∏ i ∈ U, A u (paths i (oldSample S v x))) *
      D (newPath S v x)) * _ = _
    ring

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass

def pathCoordinate {Ω : Type} : (n : ℕ) → FinitePath Ω n → Fin n → Ω
  | 0, _, i => Fin.elim0 i
  | n+1, x, i => Fin.cases x.1 (pathCoordinate n x.2) i

namespace PrescribedTree

def leafEdge : {n : ℕ} → (S : PrescribedTree n) → Leaf S → Fin n → Edge S
  | 0, .leaf, _, i => Fin.elim0 i
  | _+1, .node _ C, a, i => Fin.cases ⟨a.1,none⟩
      (fun j => ⟨a.1,some (leafEdge (C a.1) a.2 j)⟩) i

@[simp] lemma edgeDepth_leafEdge {n : ℕ} (S : PrescribedTree n) (a : S.Leaf) (i : Fin n) :
    edgeDepth S (leafEdge S a i) = i := by
  induction S with
  | leaf => exact Fin.elim0 i
  | node k C ih =>
    refine Fin.cases rfl (fun j => ?_) i
    exact congrArg Fin.succ (ih a.1 a.2 j)

lemma coordinate_pathAt {Ω : Type} {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (x : Sample Ω S) (i : Fin n) :
    pathCoordinate n (S.pathAt a x) i = vertexValues S x (leafEdge S a i) := by
  induction S with
  | leaf => exact Fin.elim0 i
  | node k C ih =>
    refine Fin.cases rfl (fun j => ?_) i
    exact ih a.1 a.2 (x a.1).2 j

/-- Sharing the actual depth-(i+1) vertex is exactly the split-depth inequality.
Equality of sampled spin/mark values plays no role in this fact. -/
lemma leafEdge_eq_iff {n : ℕ} (S : PrescribedTree n) (a b : S.Leaf) (i : Fin n) :
    leafEdge S a i = leafEdge S b i ↔ i.val+1 ≤ splitDepth S a b := by
  induction S with
  | leaf => exact Fin.elim0 i
  | @node n k C ih =>
    obtain ⟨a,x⟩ := a
    obtain ⟨b,y⟩ := b
    by_cases h : a = b
    · subst b
      refine Fin.cases ?_ (fun j => ?_) i
      · change (Sigma.mk a none : (a : Fin k) × Option (Edge (C a))) = ⟨a,none⟩ ↔
          1 ≤ splitDepth (.node k C) ⟨a,x⟩ ⟨a,y⟩
        rw [splitDepth_same_child]
        simp
      · change (Sigma.mk a (some (leafEdge (C a) x j)) : (a : Fin k) × Option (Edge (C a))) =
          ⟨a,some (leafEdge (C a) y j)⟩ ↔ j.val+1+1 ≤ splitDepth (.node k C) ⟨a,x⟩ ⟨a,y⟩
        rw [splitDepth_same_child]
        simp only [Sigma.mk.inj_iff,heq_eq_eq,true_and,Option.some.injEq,ih]
        omega
    · have he : ∀ j : Fin (n+1), (leafEdge (.node k C) ⟨a,x⟩ j).1 = a := by
        intro j
        exact Fin.cases rfl (fun _ => rfl) j
      have hf : ∀ j : Fin (n+1), (leafEdge (.node k C) ⟨b,y⟩ j).1 = b := by
        intro j
        exact Fin.cases rfl (fun _ => rfl) j
      have hne : leafEdge (.node k C) ⟨a,x⟩ i ≠ leafEdge (.node k C) ⟨b,y⟩ i := by
        intro hh
        exact h (by simpa only [he,hf] using congrArg Sigma.fst hh)
      rw [splitDepth_diff_child C a b h]
      simp only [hne,false_iff]
      omega

end PrescribedTree
end DilutedSpinGlass
end

end

end OAI
