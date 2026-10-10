import OAI.Probability.DilutedSpin.MarkedPoisson

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass.FiniteLaw
variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]

/-- Relabeling outcomes does not change a finite conditional probability law. -/
noncomputable def transport (e : Ω ≃ Λ) (P : FiniteLaw Ω) : FiniteLaw Λ where
  weight y := P.weight (e.symm y)
  nonneg y := P.nonneg _
  total := by
    exact (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).trans P.total

@[simp] theorem expect_transport (e : Ω ≃ Λ) (P : FiniteLaw Ω) (f : Λ → ℝ) :
    (P.transport e).expect f = P.expect (f ∘ e) := by
  unfold expect transport
  exact Fintype.sum_equiv e.symm _ _ (fun y => by
    simp only [Function.comp_apply, Equiv.apply_symm_apply])

@[simp] theorem expMoment_transport (e : Ω ≃ Λ) (P : FiniteLaw Ω)
    (m : ℝ) (f : Λ → ℝ) :
    (P.transport e).expMoment m f = P.expMoment m (f ∘ e) := by
  exact expect_transport e P _

@[simp] theorem logMean_transport (e : Ω ≃ Λ) (P : FiniteLaw Ω)
    (m : ℝ) (f : Λ → ℝ) :
    (P.transport e).logMean m f = P.logMean m (f ∘ e) := by
  simp only [logMean, expMoment_transport]

theorem tilted_expect_transport (e : Ω ≃ Λ) (P : FiniteLaw Ω)
    (m : ℝ) (f g : Λ → ℝ) :
    ((P.transport e).tilt m f).expect g =
      (P.tilt m (f ∘ e)).expect (g ∘ e) := by
  simp only [tilt_expect, expect_transport, expMoment_transport, Function.comp_def]

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

def pathEquiv (e : Ω ≃ Λ) : (n : ℕ) → FinitePath Ω n ≃ FinitePath Λ n
  | 0 => Equiv.refl _
  | n+1 => e.prodCongr (pathEquiv e n)

omit [Fintype Ω] [Fintype Λ] in
@[simp] theorem pathEquiv_cons (e : Ω ≃ Λ) (n : ℕ) (a : Ω) (x : FinitePath Ω n) :
    pathEquiv e (n+1) (a,x) = (e a, pathEquiv e n x) := rfl

noncomputable def transport (e : Ω ≃ Λ) : (n : ℕ) → KernelTower Ω n → KernelTower Λ n
  | 0, _ => ()
  | n+1, T => (T.1.transport e, fun a => transport e n (T.2 (e.symm a)))

/-- Conditional power means commute with literal relabeling of every hidden
mark variable. This is needed for the physical Palm exchangeability. -/
theorem backwardLog_transport (e : Ω ≃ Λ) (n : ℕ) (T : KernelTower Ω n)
    (m : Fin n → ℝ) (f : FinitePath Λ n → ℝ) :
    backwardLog n (transport e n T) m f =
      backwardLog n T m (f ∘ pathEquiv e n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardLog, transport]
    have he : (fun a : Λ => backwardLog n (transport e n (T.2 (e.symm a)))
        (fun j => m j.succ) (fun y => f (a,y))) =
      (fun a : Λ => backwardLog n (T.2 (e.symm a))
        (fun j => m j.succ) ((fun y => f (a,y)) ∘ pathEquiv e n)) :=
      funext (fun a => ih (T.2 (e.symm a)) (fun j => m j.succ) (fun y => f (a,y)))
    rw [he, FiniteLaw.logMean_transport]
    congr 1
    funext a
    simp only [Function.comp_def, Equiv.symm_apply_apply, pathEquiv_cons]

/-- The tilted expectation of any terminal observable is transported along
with the quenched log weight. No symmetry assumptions on the weight are used. -/
theorem tiltedExpect_transport (e : Ω ≃ Λ) (n : ℕ) (T : KernelTower Ω n)
    (m : Fin n → ℝ) (f g : FinitePath Λ n → ℝ) :
    (law n (tilt n (transport e n T) m f)).expect g =
      (law n (tilt n T m (f ∘ pathEquiv e n))).expect (g ∘ pathEquiv e n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [law_succ_expect, law_succ_expect]
    simp only [tilt, transport]
    rw [FiniteLaw.tilted_expect_transport]
    simp only [Function.comp_def, Equiv.symm_apply_apply,
      backwardLog_transport, ih, pathEquiv_cons]

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.FiniteLaw
variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]

theorem eq_of_weights {P Q : FiniteLaw Ω} (h : ∀ x, P.weight x = Q.weight x) : P = Q := by
  cases P
  cases Q
  congr
  exact funext h

theorem tilt_transport (e : Ω ≃ Λ) (P : FiniteLaw Ω) (m : ℝ) (f : Λ → ℝ) :
    (P.transport e).tilt m f = (P.tilt m (f ∘ e)).transport e := by
  apply eq_of_weights
  intro y
  change P.weight (e.symm y) * Real.exp (m * f y) /
    (P.transport e).expMoment m f =
      P.weight (e.symm y) * Real.exp (m * f (e (e.symm y))) / P.expMoment m (f ∘ e)
  rw [expMoment_transport, Equiv.apply_symm_apply]

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

theorem tilt_transport (e : Ω ≃ Λ) (n : ℕ) (T : KernelTower Ω n)
    (m : Fin n → ℝ) (f : FinitePath Λ n → ℝ) :
    tilt n (transport e n T) m f =
      transport e n (tilt n T m (f ∘ pathEquiv e n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext
    · simp only [tilt, transport, FiniteLaw.tilt_transport]
      congr 2
      funext a
      simp only [Function.comp_def, Equiv.symm_apply_apply, backwardLog_transport,
        pathEquiv_cons]
    · funext a
      simp only [tilt, transport, ih, Function.comp_def, pathEquiv_cons, Equiv.apply_symm_apply]

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

/-- Relabel every sampled vertex without identifying distinct replica paths. -/
def sampleEquiv (e : Ω ≃ Λ) : {n : ℕ} → (S : PrescribedTree n) → Sample Ω S ≃ Sample Λ S
  | 0, .leaf => Equiv.refl _
  | _+1, .node _ C => Equiv.piCongrRight (fun i => e.prodCongr (sampleEquiv e (C i)))

omit [Fintype Ω] [Fintype Λ] in
@[simp] theorem sampleEquiv_node (e : Ω ≃ Λ) {n : ℕ} (k : ℕ+)
    (C : Fin k → PrescribedTree n) (x : Sample Ω (.node k C)) (j : Fin k) :
    sampleEquiv e (.node k C) x j = (e (x j).1, sampleEquiv e (C j) (x j).2) := rfl

theorem sampleWeight_transport (e : Ω ≃ Λ) {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (x : Sample Ω S) :
    (sampleLaw S (KernelTower.transport e n T)).weight (sampleEquiv e S x) =
      (sampleLaw S T).weight x := by
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    rcases T with ⟨P, T⟩
    change (∏ i, P.weight (e.symm (e (x i).1)) *
      (sampleLaw (C i) (KernelTower.transport e n (T (e.symm (e (x i).1))))).weight
        (sampleEquiv e (C i) (x i).2)) =
      ∏ i, P.weight (x i).1 * (sampleLaw (C i) (T (x i).1)).weight (x i).2
    simp only [Equiv.symm_apply_apply]
    apply Finset.prod_congr rfl
    intro i _
    rw [ih]

theorem sampleExpect_transport (e : Ω ≃ Λ) {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (f : Sample Λ S → ℝ) :
    (sampleLaw S (KernelTower.transport e n T)).expect f =
      (sampleLaw S T).expect (f ∘ sampleEquiv e S) := by
  unfold FiniteLaw.expect
  apply (Fintype.sum_equiv (sampleEquiv e S) _ _ ?_).symm
  intro x
  simp only [sampleWeight_transport, Function.comp_apply]

theorem tiltedSampleExpect_transport (e : Ω ≃ Λ) {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin n → ℝ) (f : FinitePath Λ n → ℝ)
    (g : Sample Λ S → ℝ) :
    (sampleLaw S (KernelTower.tilt n (KernelTower.transport e n T) m f)).expect g =
      (sampleLaw S (KernelTower.tilt n T m (f ∘ KernelTower.pathEquiv e n))).expect
        (g ∘ sampleEquiv e S) := by
  rw [KernelTower.tilt_transport, sampleExpect_transport]

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
variable {Ω Λ : Type}

/-- A leaf keeps its label under relabeling, even when two sampled paths agree. -/
theorem pathAt_sampleEquiv (e : Ω ≃ Λ) {n : ℕ} (S : PrescribedTree n)
    (a : Leaf S) (x : Sample Ω S) :
    pathAt S a (sampleEquiv e S x) = KernelTower.pathEquiv e n (pathAt S a x) := by
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    change (e (x a.1).1, pathAt (C a.1) a.2 (sampleEquiv e (C a.1) (x a.1).2)) =
      (e (x a.1).1, KernelTower.pathEquiv e n (pathAt (C a.1) a.2 (x a.1).2))
    rw [ih]

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.FiniteLaw
variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]

@[ext] theorem ext {P Q : FiniteLaw Ω} (h : ∀ x, P.weight x = Q.weight x) : P = Q := by
  cases P
  cases Q
  congr
  exact funext h

/-- A mark block not present in a log weight integrates out, before or after
any one power-mean tilt. -/
theorem logMean_bind_fst (P : FiniteLaw Ω) (Q : FiniteLaw Λ) (m : ℝ) (f : Ω → ℝ) :
    (P.bind (fun _ => Q)).logMean m (fun z => f z.1) = P.logMean m f := by
  simp [logMean, expMoment]

theorem tilt_bind_fst (P : FiniteLaw Ω) (Q : FiniteLaw Λ) (m : ℝ) (f : Ω → ℝ) :
    (P.bind (fun _ => Q)).tilt m (fun z => f z.1) =
      (P.tilt m f).bind (fun _ => Q) := by
  ext z
  change P.weight z.1 * Q.weight z.2 * Real.exp (m*f z.1) /
      (P.bind (fun _ => Q)).expMoment m (fun z => f z.1) =
      (P.weight z.1 * Real.exp (m*f z.1) / P.expMoment m f) * Q.weight z.2
  have hh : (P.bind (fun _ => Q)).expMoment m (fun z => f z.1) = P.expMoment m f := by
    simp [expMoment]
  rw [hh]
  ring
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

/-- Independent auxiliary mark kernels are joined at each depth, not added
as separately normalized replicas. -/
noncomputable def prod : (n : ℕ) → KernelTower Ω n → KernelTower Λ n →
    KernelTower (Ω × Λ) n
  | 0, _, _ => ()
  | n+1, T, U => (T.1.bind (fun _ => U.1), fun z => prod n (T.2 z.1) (U.2 z.2))

def pathFst : (n : ℕ) → FinitePath (Ω × Λ) n → FinitePath Ω n
  | 0, _ => ()
  | n+1, x => (x.1.1, pathFst n x.2)

def pathSnd : (n : ℕ) → FinitePath (Ω × Λ) n → FinitePath Λ n
  | 0, _ => ()
  | n+1, x => (x.1.2, pathSnd n x.2)

theorem backwardLog_prod_fst (n : ℕ) (T : KernelTower Ω n) (U : KernelTower Λ n)
    (m : Fin n → ℝ) (f : FinitePath Ω n → ℝ) :
    backwardLog n (prod n T U) m (fun y => f (pathFst n y)) = backwardLog n T m f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardLog, prod, pathFst]
    have hh : (fun z : Ω × Λ => backwardLog n
        (prod n (T.2 z.1) (U.2 z.2)) (fun j => m j.succ)
        (fun y => f (z.1, pathFst n y))) =
        (fun z : Ω × Λ => backwardLog n (T.2 z.1) (fun j => m j.succ)
          (fun y => f (z.1,y))) := by
      funext z
      exact ih (T.2 z.1) (U.2 z.2) (fun j => m j.succ) (fun y => f (z.1,y))
    rw [hh]
    exact FiniteLaw.logMean_bind_fst T.1 U.1 (m 0)
      (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))

theorem tilt_prod_fst (n : ℕ) (T : KernelTower Ω n) (U : KernelTower Λ n)
    (m : Fin n → ℝ) (f : FinitePath Ω n → ℝ) :
    tilt n (prod n T U) m (fun y => f (pathFst n y)) = prod n (tilt n T m f) U := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext
    · change (T.1.bind (fun _ => U.1)).tilt (m 0)
        (fun z => backwardLog n (prod n (T.2 z.1) (U.2 z.2)) (fun j => m j.succ)
          (fun y => f (z.1,pathFst n y))) =
        (T.1.tilt (m 0) (fun x => backwardLog n (T.2 x) (fun j => m j.succ)
          (fun y => f (x,y)))).bind (fun _ => U.1)
      have hh : (fun z : Ω × Λ => backwardLog n
          (prod n (T.2 z.1) (U.2 z.2)) (fun j => m j.succ)
          (fun y => f (z.1, pathFst n y))) =
          (fun z : Ω × Λ => backwardLog n (T.2 z.1) (fun j => m j.succ)
            (fun y => f (z.1,y))) := by
        funext z
        exact backwardLog_prod_fst n (T.2 z.1) (U.2 z.2) (fun j => m j.succ)
          (fun y => f (z.1,y))
      rw [hh]
      exact FiniteLaw.tilt_bind_fst T.1 U.1 (m 0)
        (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))
    · funext z
      exact ih (T.2 z.1) (U.2 z.2) (fun j => m j.succ) (fun y => f (z.1,y))
end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω]

/-- Exchangeability of independent identically distributed root marks. -/
theorem expect_pi_perm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : FiniteLaw Ω) (σ : Equiv.Perm ι) (F : (ι → Ω) → ℝ) :
    (pi (fun _ : ι => P)).expect (fun x => F (x ∘ σ)) =
      (pi (fun _ : ι => P)).expect F := by
  classical
  let e : (ι → Ω) ≃ (ι → Ω) :=
    { toFun := fun x => x ∘ σ
      invFun := fun x => x ∘ σ.symm
      left_inv := by intro x; funext i; simp
      right_inv := by intro x; funext i; simp }
  unfold expect
  apply Fintype.sum_equiv e
  intro x
  dsimp [e, pi]
  congr 1
  exact (Fintype.prod_equiv σ _ _ (fun i => rfl)).symm

/-- All summands of an equivariant marked score have the same mean. This
is proved from iid sampling, rather than being a Palm hypothesis. -/
theorem expect_pi_equivariant {n : ℕ} (P : FiniteLaw Ω)
    (F : (Fin n → Ω) → Fin n → ℝ)
    (hF : ∀ (σ : Equiv.Perm (Fin n)) x i, F (x ∘ σ) i = F x (σ i))
    (i j : Fin n) :
    (pi (fun _ : Fin n => P)).expect (fun x => F x i) =
      (pi (fun _ : Fin n => P)).expect (fun x => F x j) := by
  classical
  rw [← expect_pi_perm P (Equiv.swap i j) (fun x => F x i)]
  apply expect_congr
  intro x
  rw [hF, Equiv.swap_apply_left]

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {Ω : Type*} [Fintype Ω]

/-- The marked Poisson identity used in pert:palm. Each score component may
depend on all other marks; only the actual permutation covariance is needed.
The new mark is sampled independently with its original prior. -/
theorem poisson_marked_add_one (r : ℝ≥0) (P : FiniteLaw Ω)
    (F : (n : ℕ) → (Fin n → Ω) → Fin n → ℝ) {B : ℝ}
    (hB : ∀ n x i, |F n x i| ≤ B)
    (hF : ∀ n (σ : Equiv.Perm (Fin n)) x i, F n (x ∘ σ) i = F n x (σ i)) :
    (∫ n : ℕ, (FiniteLaw.pi (fun _ : Fin n => P)).expect (fun x => ∑ i, F n x i)
      ∂poissonMeasure r) =
    (r : ℝ) * ∫ n : ℕ, P.expect (fun y =>
      (FiniteLaw.pi (fun _ : Fin n => P)).expect (fun x => F (n+1) (Fin.cons y x) 0))
      ∂poissonMeasure r := by
  let a : ℕ → ℝ := fun n => if h : 0 < n then
    (FiniteLaw.pi (fun _ : Fin n => P)).expect (fun x => F n x ⟨0,h⟩) else 0
  have ha (n : ℕ) : a (n+1) =
      (FiniteLaw.pi (fun _ : Fin (n+1) => P)).expect (fun x => F (n+1) x 0) := by
    simp [a]
  have hsum (n : ℕ) :
      (FiniteLaw.pi (fun _ : Fin n => P)).expect (fun x => ∑ i, F n x i) = (n : ℝ)*a n := by
    rw [FiniteLaw.expect_fintype_sum]
    by_cases hn : 0 < n
    · simp only [a, dite_eq_left hn]
      rw [show (fun i : Fin n =>
        (FiniteLaw.pi (fun _ : Fin n => P)).expect (fun x => F n x i)) =
        (fun _ : Fin n => (FiniteLaw.pi (fun _ : Fin n => P)).expect (fun x => F n x ⟨0,hn⟩)) from
          funext fun i => FiniteLaw.expect_pi_equivariant P (F n) (hF n) i ⟨0,hn⟩]
      simp
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      simp
  have hi : Integrable (fun n => a (n+1)) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := B) (B := 0)
    intro n
    rw [ha]
    simpa only [zero_mul, add_zero] using
      (FiniteLaw.pi (fun _ : Fin (n+1) => P)).abs_expect_le (fun x => hB (n+1) x 0)
  simp_rw [hsum]
  rw [poisson_add_one r a hi]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun n => by
    change a (n+1) = _
    rw [ha, FiniteLaw.expect_pi_cons])

end DilutedSpinGlass

namespace DilutedSpinGlass
open scoped BigOperators
variable {Ω A : Type} [Fintype Ω] [Fintype A]

/-- Permute selected-type mark labels without permuting spins or other types. -/
def markPerm {k : ℕ} (σ : Equiv.Perm (Fin k)) : (Fin k → A) ≃ (Fin k → A) where
  toFun x := x ∘ σ
  invFun x := x ∘ σ.symm
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

def rowPerm {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    (Ω × (Fin k → A)) ≃ (Ω × (Fin k → A)) :=
  (Equiv.refl Ω).prodCongr (markPerm σ)

/-- The literal product-prior tower for k independent copies of a mark process.
The physical tower includes every other type in the reservoir. -/
noncomputable def markedTower (k : ℕ) : (L : ℕ) → KernelTower Ω L →
    (Fin L → FiniteLaw A) → KernelTower (Ω × (Fin k → A)) L
  | 0, _, _ => ()
  | L+1, T, Q => (T.1.bind (fun _ => FiniteLaw.pi (fun _ : Fin k => Q 0)),
      fun y => markedTower k L (T.2 y.1) (fun j => Q j.succ))

/-- An actual selected-type replica-row prior is permutation invariant. -/
theorem markedTower_transport {k : ℕ} (σ : Equiv.Perm (Fin k)) (L : ℕ)
    (T : KernelTower Ω L) (Q : Fin L → FiniteLaw A) :
    KernelTower.transport (rowPerm σ) L (markedTower k L T Q) = markedTower k L T Q := by
  induction L with
  | zero => rfl
  | succ L ih =>
    apply Prod.ext
    · apply FiniteLaw.eq_of_weights
      intro x
      change T.1.weight x.1 * (∏ i, (Q 0).weight (x.2 (σ.symm i))) =
        T.1.weight x.1 * ∏ i, (Q 0).weight (x.2 i)
      congr 1
      exact Fintype.prod_equiv σ.symm _ _ (fun _ => rfl)
    · funext x
      exact ih (T.2 x.1) (fun j => Q j.succ)

/-- Forget the selected auxiliary mark rows. -/
def physicalPath (k : ℕ) : (L : ℕ) → FinitePath (Ω × (Fin k → A)) L → FinitePath Ω L
  | 0, _ => ()
  | L+1, y => (y.1.1, physicalPath k L y.2)

/-- Read one complete independent mark process from a latent path. -/
def markPath {k : ℕ} (q : Fin k) : (L : ℕ) →
    FinitePath (Ω × (Fin k → A)) L → FinitePath A L
  | 0, _ => ()
  | L+1, y => (y.1.2 q, markPath q L y.2)

omit [Fintype Ω] [Fintype A] in
theorem physicalPath_rowPerm {k : ℕ} (σ : Equiv.Perm (Fin k)) (L : ℕ)
    (y : FinitePath (Ω × (Fin k → A)) L) :
    physicalPath k L (KernelTower.pathEquiv (rowPerm σ) L y) = physicalPath k L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.1, physicalPath k L (KernelTower.pathEquiv (rowPerm σ) L y.2)) =
      (y.1.1, physicalPath k L y.2)
    rw [ih]

omit [Fintype Ω] [Fintype A] in
theorem markPath_rowPerm {k : ℕ} (σ : Equiv.Perm (Fin k)) (L : ℕ)
    (y : FinitePath (Ω × (Fin k → A)) L) (q : Fin k) :
    markPath q L (KernelTower.pathEquiv (rowPerm σ) L y) = markPath (σ q) L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.2 (σ q), markPath q L (KernelTower.pathEquiv (rowPerm σ) L y.2)) =
      (y.1.2 (σ q), markPath (σ q) L y.2)
    rw [ih]

variable {I : Type} {k L : ℕ}

/-- All k selected factors at a terminal leaf, tilting the complete base log weight. -/
noncomputable def markedLog (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : I → FinitePath Ω L → FinitePath A L → ℝ)
    (y : FinitePath (Ω × (Fin k → A)) L) : ℝ :=
  base (physicalPath k L y) + ∑ q, Real.log (factor (roots q) (physicalPath k L y) (markPath q L y))

omit [Fintype Ω] [Fintype A] in
theorem markedLog_rowPerm (σ : Equiv.Perm (Fin k))
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : I → FinitePath Ω L → FinitePath A L → ℝ)
    (y : FinitePath (Ω × (Fin k → A)) L) :
    markedLog base (roots ∘ σ) factor (KernelTower.pathEquiv (rowPerm σ) L y) =
      markedLog base roots factor y := by
  simp only [markedLog, physicalPath_rowPerm, markPath_rowPerm, Function.comp_apply]
  congr 1
  exact Fintype.sum_equiv σ _ _ (fun _ => rfl)


/-- The actual tree score of a specified selected-type term, with an arbitrary
old physical replica test. The terminal numerator includes the spin-or-marker
anchor from the manuscript, and the factor is its original denominator. -/
noncomputable def markedTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : Fin L → FiniteLaw A) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor numerator : I → FinitePath Ω L → FinitePath A L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (q : Fin k) : ℝ :=
  (S.sampleLaw (KernelTower.tilt L (markedTower k L T Q) m
    (markedLog base roots factor))).expect (fun x =>
      f (fun b => physicalPath k L (S.pathAt b x)) *
        (numerator (roots q) (physicalPath k L (S.pathAt a x)) (markPath q L (S.pathAt a x)) /
          factor (roots q) (physicalPath k L (S.pathAt a x)) (markPath q L (S.pathAt a x))))

/-- The equivariance required by Poisson Palm is proved for the physical
tilting statistic; it is not an added hypothesis on the score. -/
theorem markedTreeScore_perm (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : Fin L → FiniteLaw A) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor numerator : I → FinitePath Ω L → FinitePath A L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (σ : Equiv.Perm (Fin k)) (q : Fin k) :
    markedTreeScore S a T Q m base (roots ∘ σ) factor numerator f q =
      markedTreeScore S a T Q m base roots factor numerator f (σ q) := by
  have h := PrescribedTree.tiltedSampleExpect_transport (rowPerm σ) S (markedTower k L T Q) m
    (markedLog base (roots ∘ σ) factor) (fun x =>
      f (fun b => physicalPath k L (S.pathAt b x)) *
        (numerator (roots (σ q)) (physicalPath k L (S.pathAt a x)) (markPath q L (S.pathAt a x)) /
          factor (roots (σ q)) (physicalPath k L (S.pathAt a x)) (markPath q L (S.pathAt a x))))
  have heq : markedLog base (roots ∘ σ) factor ∘ KernelTower.pathEquiv (rowPerm σ) L =
      markedLog base roots factor := funext (fun y => markedLog_rowPerm σ base roots factor y)
  rw [heq] at h
  simpa only [markedTower_transport, Function.comp_def,
    PrescribedTree.pathAt_sampleEquiv, physicalPath_rowPerm, markPath_rowPerm,
    markedTreeScore] using h

/-- The score component remains uniformly bounded in the Poisson count.
This is the integrability needed for the literal Palm identity. -/
theorem abs_markedTreeScore_le (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : Fin L → FiniteLaw A) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor numerator : I → FinitePath Ω L → FinitePath A L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (q : Fin k) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (hn : ∀ i y z, |numerator i y z| ≤ 1)
    (hA : ∀ i y z, 1/2 ≤ factor i y z) :
    |markedTreeScore S a T Q m base roots factor numerator f q| ≤ 2*B := by
  apply FiniteLaw.abs_expect_le
  intro x
  rw [abs_mul, abs_div, abs_of_pos (lt_of_lt_of_le (by norm_num) (hA _ _ _))]
  have hd : |numerator (roots q) (physicalPath k L (S.pathAt a x))
      (markPath q L (S.pathAt a x))| /
      factor (roots q) (physicalPath k L (S.pathAt a x)) (markPath q L (S.pathAt a x)) ≤ 2 := by
    rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) (hA _ _ _))]
    linarith [hn (roots q) (physicalPath k L (S.pathAt a x)) (markPath q L (S.pathAt a x)),
      hA (roots q) (physicalPath k L (S.pathAt a x)) (markPath q L (S.pathAt a x))]
  calc
    _ ≤ |f (fun b => physicalPath k L (S.pathAt b x))| * 2 :=
      mul_le_mul_of_nonneg_left hd (abs_nonneg _)
    _ ≤ B * 2 := mul_le_mul_of_nonneg_right (hf _) (by norm_num)
    _ = 2 * B := mul_comm _ _

end DilutedSpinGlass

end

end OAI
