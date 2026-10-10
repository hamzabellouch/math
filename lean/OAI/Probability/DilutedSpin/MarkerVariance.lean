import OAI.Probability.DilutedSpin.MarkerConcrete

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

/-- The complete overlap in one of two conditionally independent descendants
of an actually sampled stem. -/
noncomputable def forkOverlap (A : PrescribedTree n) : (r : ℕ) →
    (FinitePath Ω (n+1+r) → Fin N → ℝ) → Fin 2 → Sample Ω (stem (doubled A) r) → ℝ
  | 0, V, j, w => treeOverlap A (fun y => V ((w j).1,y)) (w j).2
  | r+1, V, j, w => forkOverlap A r (fun y => V ((w 0).1,y)) j (w 0).2

omit [Fintype Ω] in
lemma forkOverlap_paths (A : PrescribedTree n) (r : ℕ)
    (V : FinitePath Ω (n+1+r) → Fin N → ℝ) (j : Fin 2)
    (w : Sample Ω (stem (doubled A) r)) :
    forkOverlap A r V j w = spatialProduct (fun _ : A.Leaf => V)
      (fun a => (stem (doubled A) r).pathAt (stemLeaf (doubled A) r ⟨j,a⟩) w) := by
  induction r with
  | zero =>
    unfold forkOverlap treeOverlap spatialProduct
    congr 1
    apply Finset.sum_congr rfl
    intro _ _
    rw [leafProduct_eq_prod]
    rfl
  | succ r ih =>
    rw [forkOverlap,ih]
    rfl

noncomputable def forkPairMean (A : PrescribedTree n) (r : ℕ)
    (K : KernelTower Ω (n+1+r)) (V : FinitePath Ω (n+1+r) → Fin N → ℝ) : ℝ :=
  ((stem (doubled A) r).sampleLaw K).expect (fun w => forkOverlap A r V 0 w * forkOverlap A r V 1 w)

noncomputable def unarySquareMean (A : PrescribedTree n) (r : ℕ)
    (K : KernelTower Ω (n+1+r)) (V : FinitePath Ω (n+1+r) → Fin N → ℝ) : ℝ :=
  ((stem (unary A) r).sampleLaw K).expect (fun w => (treeOverlap (stem (unary A) r) V w)^2)

lemma forkPairMean_zero (A : PrescribedTree n) (K : KernelTower Ω (n+1))
    (V : FinitePath Ω (n+1) → Fin N → ℝ) :
    forkPairMean A 0 K V = ((K.1.bind (fun x => A.sampleLaw (K.2 x))).expect
      (fun w => treeOverlap A (fun y => V (w.1,y)) w.2))^2 := by
  classical
  unfold forkPairMean
  change (FiniteLaw.pi (fun _ : Fin 2 => K.1.bind (fun x => A.sampleLaw (K.2 x)))).expect
    (fun w => treeOverlap A (fun y => V ((w 0).1,y)) (w 0).2 *
      treeOverlap A (fun y => V ((w 1).1,y)) (w 1).2)=_
  have h := FiniteLaw.expect_pi_pair (fun _ : Fin 2 => K.1.bind (fun x => A.sampleLaw (K.2 x)))
    0 1 (by decide) (fun x y => treeOverlap A (fun z => V (x.1,z)) x.2 * treeOverlap A (fun z => V (y.1,z)) y.2)
  refine h.trans ?_
  simp only [FiniteLaw.expect_mul_left,FiniteLaw.expect_mul_right,pow_two]

lemma forkPairMean_succ (A : PrescribedTree n) (r : ℕ) (K : KernelTower Ω (n+1+r+1))
    (V : FinitePath Ω (n+1+r+1) → Fin N → ℝ) :
    forkPairMean A (r+1) K V = K.1.expect (fun x => forkPairMean A r (K.2 x) (fun y => V (x,y))) := by
  unfold forkPairMean
  exact sampleLaw_unary_expect (stem (doubled A) r) K
    (fun w => forkOverlap A r (fun y => V (w.1,y)) 0 w.2 * forkOverlap A r (fun y => V (w.1,y)) 1 w.2)

lemma unarySquareMean_succ (A : PrescribedTree n) (r : ℕ) (K : KernelTower Ω (n+1+r+1))
    (V : FinitePath Ω (n+1+r+1) → Fin N → ℝ) :
    unarySquareMean A (r+1) K V = K.1.expect (fun x => unarySquareMean A r (K.2 x) (fun y => V (x,y))) := by
  unfold unarySquareMean
  simp_rw [show ∀ w : Sample Ω (stem (unary A) (r+1)),
    treeOverlap (stem (unary A) (r+1)) V w = treeOverlap (stem (unary A) r) (fun y => V ((w 0).1,y)) (w 0).2
    from fun w => treeOverlap_unary _ V w]
  exact sampleLaw_unary_expect (stem (unary A) r) K
    (fun w => (treeOverlap (stem (unary A) r) (fun y => V (w.1,y)) w.2)^2)

lemma unarySquareMean_zero (A : PrescribedTree n) (K : KernelTower Ω (n+1))
    (V : FinitePath Ω (n+1) → Fin N → ℝ) :
    unarySquareMean A 0 K V=(K.1.bind (fun x => A.sampleLaw (K.2 x))).expect
      (fun w => (treeOverlap A (fun y => V (w.1,y)) w.2)^2) := by
  let F := fun w : Ω × Sample Ω A => (treeOverlap A (fun y => V (w.1,y)) w.2)^2
  have h := sampleLaw_unary_expect A K F
  have hh := FiniteLaw.expect_bind K.1 (fun x => A.sampleLaw (K.2 x)) F
  refine Eq.trans ?_ (h.trans hh.symm)
  apply FiniteLaw.expect_congr
  intro w
  exact congrArg (fun x : ℝ => x^2) (treeOverlap_unary A V w)

lemma marker_conditional_variance_zero (A : PrescribedTree n)
    (K : KernelTower Ω (n+1)) (V : FinitePath Ω (n+1) → Fin N → ℝ) :
    unarySquareMean A 0 K V - forkPairMean A 0 K V ≤ Real.sqrt (shapeEnergyAt A 0 K V) := by
  let P := K.1.bind (fun x => A.sampleLaw (K.2 x))
  let X := fun w : Ω × Sample Ω A => fun i => leafProduct A (fun y => V (w.1,y) i) w.2
  let R := fun w : Ω × Sample Ω A => treeOverlap A (fun y => V (w.1,y)) w.2
  have h := P.centered_contraction_bound X (fun _ => 1) (fun _ => by norm_num)
  have he (w : Ω × Sample Ω A) :
      FiniteLaw.dot (fun i => X w i-P.expect (fun y => X y i)) (fun _ => 1)=R w-P.expect R := by
    simp only [FiniteLaw.dot,mul_one,Finset.sum_sub_distrib,sub_div,R,treeOverlap,
      FiniteLaw.expect_div,FiniteLaw.expect_fintype_sum,X]
  simp_rw [he] at h
  rw [FiniteLaw.expect_sq_sub_expect] at h
  rw [forkPairMean_zero,unarySquareMean_zero]
  exact h

/-- Whole-shape conditional variance is controlled by the whole-shape
covariance energy. There is no missing projection or independence premise. -/
theorem marker_conditional_variance_le (A : PrescribedTree n) (r : ℕ)
    (K : KernelTower Ω (n+1+r)) (V : FinitePath Ω (n+1+r) → Fin N → ℝ) :
    unarySquareMean A r K V - forkPairMean A r K V ≤ Real.sqrt (shapeEnergyAt A r K V) := by
  induction r with
  | zero => exact marker_conditional_variance_zero A K V
  | succ r ih =>
    rw [unarySquareMean_succ,forkPairMean_succ,← FiniteLaw.expect_sub]
    apply (K.1.expect_mono (fun x => ih (K.2 x) (fun y => V (x,y)))).trans
    exact K.1.expect_sqrt_le _ (fun x => shapeEnergyAt_nonneg A r (K.2 x) (fun y => V (x,y)))

omit [Fintype Ω] in
lemma markerOld_overlap (A : PrescribedTree n) (r : ℕ)
    (V : FinitePath Ω (n+1+r) → Fin N → ℝ) (w : Sample Ω (stem (doubled A) r)) :
    spatialProduct (fun _ : (stem (unary A) r).Leaf => V)
      (fun a => (stem (doubled A) r).pathAt (markerOld A r a) w)=forkOverlap A r V 0 w := by
  rw [forkOverlap_paths]
  unfold spatialProduct
  congr 1
  apply Finset.sum_congr rfl
  intro _ _
  exact Fintype.prod_equiv (markerOldIndex A r) _ _ (fun a => rfl)

omit [Fintype Ω] in
lemma markerFresh_overlap (A : PrescribedTree n) (r : ℕ)
    (V : FinitePath Ω (n+1+r) → Fin N → ℝ) (w : Sample Ω (stem (doubled A) r)) :
    spatialProduct (fun _ : (stem (unary A) r).Leaf => V)
      (fun a => (stem (doubled A) r).pathAt (markerColorFresh A r ((markerColorOld A r).symm a)) w)=
      forkOverlap A r V 1 w := by
  rw [forkOverlap_paths]
  unfold spatialProduct
  congr 1
  apply Finset.sum_congr rfl
  intro _ _
  refine Fintype.prod_equiv (markerOldIndex A r) _ _ (fun a => ?_)
  have he : markerColorEquiv A ((markerColorOld A r).symm a)=markerOldIndex A r a := by
    change markerColorEquiv A ((markerColorEquiv A).symm (markerOldIndex A r a))=_
    exact (markerColorEquiv A).apply_symm_apply _
  simp only [markerColorFresh,Function.comp_apply,he,markerFresh]
  rfl

end DilutedSpinGlass.PrescribedTree

end

end OAI
