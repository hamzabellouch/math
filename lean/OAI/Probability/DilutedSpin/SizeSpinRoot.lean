import OAI.Probability.DilutedSpin.HeterogeneousProjection
import OAI.Probability.DilutedSpin.SplitDepthContinuity
import OAI.Probability.DilutedSpin.TreeMarkLaw
import OAI.Probability.DilutedSpin.UniformIndexCoupling

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

/-- Fresh insertion with a genuinely arbitrary retained-old/test-new joint
observable, derived from the actual extension law by finite disintegration. -/
theorem extension_sampling_dependent {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (v : S.Internal)
    (F : Sample Ω S → FinitePath Ω n → ℝ) :
    ((grow S v).sampleLaw T).expect (fun x => F (oldSample S v x) (newPath S v x)) =
      (S.sampleLaw T).expect (fun x => freshEval S T v (F x) x) := by
  classical
  have he (x : Sample Ω (grow S v)) : F (oldSample S v x) (newPath S v x) =
      ∑ z : Sample Ω S, (if oldSample S v x = z then (1:ℝ) else 0) * F z (newPath S v x) := by
    simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  simp_rw [he,FiniteLaw.expect_fintype_sum]
  calc
    _ = ∑ z : Sample Ω S, (S.sampleLaw T).expect
        (fun x => (if x = z then (1:ℝ) else 0) * freshEval S T v (F z) x) := by
      apply Finset.sum_congr rfl
      intro z _
      exact extension_sampling S T v (fun x => if x = z then (1:ℝ) else 0) (F z)
    _ = _ := by
      rw [← FiniteLaw.expect_fintype_sum]
      apply FiniteLaw.expect_congr
      intro x
      simp

/-- Squared old/new difference: the same arbitrary old joint law is retained. -/
lemma fresh_square_difference {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (v : S.Internal) (F : Sample Ω S → ℝ)
    (D : Sample Ω S → FinitePath Ω n → ℝ) :
    ((grow S v).sampleLaw T).expect
      (fun x => (F (oldSample S v x) - D (oldSample S v x) (newPath S v x))^2) =
      (S.sampleLaw T).expect (fun x => freshEval S T v (fun y => (F x-D x y)^2) x) :=
  extension_sampling_dependent S T v (fun x y => (F x-D x y)^2)

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.SizeCoupling
open scoped BigOperators
open HeterogeneousMarks

/-- Literal finite perturbed spin root with one independent mark prior for each
realized perturbation. The final spin prior is uniform; earlier spin kernels
are dummy point masses. No physical or mark law is replaced. -/
noncomputable def spinRoot {N p k l r : ℕ} {A : Fin l → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (theta : Fin k → InteractionSample p) (h : Fin N → ℝ)
    (indices : Fin k → Fin p → Fin N) (sites : Fin l → Fin N)
    (ψ : (i : Fin l) → Spin → FinitePath (A i) (r+1) → ℝ) : ℝ :=
  root (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform r) Q m
    (fun x => logWeight theta h indices (KernelTower.terminalState r x)) id
    (fun i x a => ψ i (KernelTower.terminalState r x (sites i)) a)

lemma indicator_sum_ge_one {ι : Type*} [Fintype ι] {b : ι → Bool} {i : ι}
    (hi : b i = true) : (1:ℝ) ≤ ∑ j, if b j then 1 else 0 := by
  classical
  have hh := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
    show (0:ℝ) ≤ (if b j then 1 else 0) by split <;> norm_num)
    (Finset.mem_univ i)
  simpa only [hi,Bool.true_eq,ite_true] using hh

lemma interaction_coupling_bound {N p : ℕ} (θ : Interaction p) {C : ℝ}
    (hC : 0 ≤ C) (hθ : ∀ σ, |θ σ| ≤ C)
    (z : Fin p → Fin (N+1) × Fin N) (σ : Fin (N+1) → Spin) :
    |θ (fun j => σ (newIndex (z j))) - θ (fun j => σ (oldIndex (z j)).succ)| ≤
      2*C*∑ j, if (z j).1 = 0 then (1:ℝ) else 0 := by
  classical
  by_cases hz : ∀ j, (z j).1 ≠ 0
  · have he : (fun j => σ (newIndex (z j))) = (fun j => σ (oldIndex (z j)).succ) := by
      funext j; rw [same_index_off_new (z j) (hz j)]
    rw [he,sub_self,abs_zero]
    positivity
  · push Not at hz
    rcases hz with ⟨j,hj⟩
    have hs : (1:ℝ) ≤ ∑ i, if (z i).1 = 0 then (1:ℝ) else 0 := by
      have hh := Finset.single_le_sum
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin p))) =>
          show (0:ℝ) ≤ (if (z i).1 = 0 then 1 else 0) by split <;> norm_num)
        (Finset.mem_univ j)
      simpa only [hj,ite_true] using hh
    exact (abs_sub _ _).trans ((add_le_add (hθ _) (hθ _)).trans (by nlinarith))

lemma energy_coupling_bound {N p k : ℕ} (θ : Fin k → InteractionSample p)
    (h : Fin (N+1) → ℝ) {C : ℝ} (hC : 0 ≤ C) (hθ : ∀ j σ, |(θ j).1 σ| ≤ C)
    (z : Fin k → Fin p → Fin (N+1) × Fin N) (σ : Fin (N+1) → Spin) :
    |logWeight θ h (fun j q => newIndex (z j q)) σ -
      logWeight θ (fun i => h i.succ) (fun j q => oldIndex (z j q)) (fun i => σ i.succ)| ≤
      |h 0|+2*C*∑ j, ∑ q, if (z j q).1 = 0 then (1:ℝ) else 0 := by
  have hspin : |spin (σ 0)| = 1 := by cases σ 0 <;> norm_num [spin]
  unfold logWeight
  rw [Fin.sum_univ_succ (fun i => h i * spin (σ i))]
  have he : ((∑ j, (θ j).1 (fun q => σ (newIndex (z j q)))) +
      (h 0*spin (σ 0)+∑ i : Fin N, h i.succ*spin (σ i.succ)))-
      ((∑ j, (θ j).1 (fun q => σ (oldIndex (z j q)).succ))+
        ∑ i : Fin N, h i.succ*spin (σ i.succ)) =
      h 0*spin (σ 0)+∑ j, ((θ j).1 (fun q => σ (newIndex (z j q)))-
        (θ j).1 (fun q => σ (oldIndex (z j q)).succ)) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,hspin,mul_one]
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ j, |(θ j).1 (fun q => σ (newIndex (z j q)))-
        (θ j).1 (fun q => σ (oldIndex (z j q)).succ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, 2*C*∑ q, if (z j q).1 = 0 then (1:ℝ) else 0 :=
      Finset.sum_le_sum (fun j _ => interaction_coupling_bound _ hC (hθ j) _ _)
    _ = _ := by rw [Finset.mul_sum]

/-- Keeping exactly the same realized physical and mark samples, only the
uniformly coupled sites that hit the new spin can change the root. -/
theorem spinRoot_size_coupling {N p k l r : ℕ} {A : Fin l → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (theta : Fin k → InteractionSample p) (h : Fin (N+1) → ℝ)
    (z : Fin k → Fin p → Fin (N+1) × Fin N) (w : Fin l → Fin (N+1) × Fin N)
    (ψ : (i : Fin l) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hθ : ∀ j σ, |(theta j).1 σ| ≤ C) (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) :
    |spinRoot Q m theta h (fun j q => newIndex (z j q)) (fun i => newIndex (w i)) ψ -
      spinRoot Q m theta (fun i => h i.succ) (fun j q => oldIndex (z j q))
        (fun i => oldIndex (w i)) ψ| ≤
      |h 0|+2*C*(∑ j, ∑ q, if (z j q).1 = 0 then (1:ℝ) else 0)+
        2*D*(∑ i, if (w i).1 = 0 then (1:ℝ) else 0) := by
  let π : (Fin (N+1) → Spin) → (Fin N → Spin) := fun σ i => σ i.succ
  have hp := KernelTower.terminalTower_projects π (fun _ : Fin (N+1) => false)
    (FiniteLaw.uniform_spin_projection N) r
  have hh := root_projection_stability π (id : Fin l → Fin l) _ _ hp Q m hm
    (fun x => logWeight theta (fun i => h i.succ) (fun j q => oldIndex (z j q)) (KernelTower.terminalState r x))
    (fun x => logWeight theta h (fun j q => newIndex (z j q)) (KernelTower.terminalState r x))
    (fun i x a => ψ i (KernelTower.terminalState r x (oldIndex (w i))) a)
    (fun i x a => ψ i (KernelTower.terminalState r x (newIndex (w i))) a)
    (fun i => 2*D*(if (w i).1 = 0 then (1:ℝ) else 0))
    (fun x => by
      rw [KernelTower.terminalState_pathMap]
      exact energy_coupling_bound theta h hC hθ z (KernelTower.terminalState r x))
    (fun i x a => by
      rw [KernelTower.terminalState_pathMap]
      by_cases hw : (w i).1 = 0
      · simp only [hw,ite_true,mul_one]
        exact (abs_sub _ _).trans ((add_le_add (hψ i _ a) (hψ i _ a)).trans (by linarith))
      · simp only [hw,ite_false,π]
        rw [same_index_off_new (w i) hw,sub_self,abs_zero]
        exact mul_nonneg (mul_nonneg (by norm_num) hD) (le_refl 0))
  simpa only [spinRoot,id_eq,← Finset.mul_sum] using hh

end DilutedSpinGlass.SizeCoupling
end

end

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open scoped BigOperators
variable {Ω I J : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]

lemma tower_pullback (f : J → I) {k : ℕ} (roots : Fin k → J) (L : ℕ)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) :
    tower (A := fun j => A (f j)) roots L T (fun j => Q (f j)) =
      tower (f ∘ roots) L T Q := by
  induction L with
  | zero => rfl
  | succ L ih =>
    apply Prod.ext
    · rfl
    · funext y
      exact ih (T.2 y.1) (fun i j => Q i j.succ)

omit [Fintype Ω] [∀ i, Fintype (A i)] in
lemma physical_pullback (f : J → I) {k : ℕ} (roots : Fin k → J) (L : ℕ)
    (y : FinitePath (Ω × Row (A := fun j => A (f j)) roots) L) :
    physical roots L y = physical (f ∘ roots) L y := by
  induction L with
  | zero => rfl
  | succ L ih => exact congrArg (fun z => (y.1.1,z)) (ih y.2)

omit [Fintype Ω] [∀ i, Fintype (A i)] in
lemma mark_pullback (f : J → I) {k : ℕ} (roots : Fin k → J) (q : Fin k) (L : ℕ)
    (y : FinitePath (Ω × Row (A := fun j => A (f j)) roots) L) :
    mark (A := fun j => A (f j)) q L y = mark (A := A) (roots := f ∘ roots) q L y := by
  induction L with
  | zero => rfl
  | succ L ih => exact congrArg (fun z => (y.1.2 q,z)) (ih y.2)

/-- Mere relabeling preserves every realized heterogeneous prior and factor.
This is used to identify per-occurrence and dictionary-label presentations. -/
theorem root_pullback (f : J → I) {k L : ℕ} (roots : Fin k → J)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) :
    root T (fun j => Q (f j)) m base roots (fun j => factor (f j)) =
      root T Q m base (f ∘ roots) factor := by
  unfold root
  rw [tower_pullback]
  congr 1
  funext y
  simp only [logWeight,physical_pullback,mark_pullback,Function.comp_apply]

end DilutedSpinGlass.HeterogeneousMarks
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

/-- The literal spatial squared norm of the change when this one split
moves from d to d+1. -/
noncomputable def spatialSplitChange (k : ℕ+) (C : Fin k → PrescribedTree n)
    (r : ℕ) (T : KernelTower Ω (n+r+1)) (f : FinitePath Ω (n+r+1) → Fin N → ℝ)
    (d : Fin r) : ℝ :=
  (∑ i : Fin N, (treeMean (splitFamily k C r d.castSucc) T (fun x => f x i)-
    treeMean (splitFamily k C r d.succ) T (fun x => f x i))^2)/(N:ℝ)

lemma spatialSplitChange_nonneg (k : ℕ+) (C : Fin k → PrescribedTree n)
    (r : ℕ) (T : KernelTower Ω (n+r+1)) (f : FinitePath Ω (n+r+1) → Fin N → ℝ)
    (d : Fin r) : 0 ≤ spatialSplitChange k C r T f d := by
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg N)

theorem sum_spatialSplitChange_le (k : ℕ+) (C : Fin k → PrescribedTree n)
    (r : ℕ) (T : KernelTower Ω (n+r+1)) (f : FinitePath Ω (n+r+1) → Fin N → ℝ)
    (hf : ∀ x i, |f x i| ≤ 1) : (∑ d, spatialSplitChange k C r T f d) ≤ (k:ℝ)^2 := by
  classical
  unfold spatialSplitChange
  rw [← Finset.sum_div,Finset.sum_comm]
  by_cases hN : N=0
  · subst N
    simp
  · apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))).mpr
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      splitShiftEnergy_le k C r T (fun x => f x i) (fun x => hf x i))
    simp only [splitShiftEnergy,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
    nlinarith [h]

 
theorem averaged_spatialSplitChange_le (k : ℕ+) (C : Fin k → PrescribedTree n)
    (r L : ℕ) (hL : 0 < L) (U : Finset (Fin r))
    (T : KernelTower Ω (n+r+1)) (f : FinitePath Ω (n+r+1) → Fin N → ℝ)
    (hf : ∀ x i, |f x i| ≤ 1) :
    (∑ d ∈ U, spatialSplitChange k C r T f d)/(L:ℝ) ≤ (k:ℝ)^2/(L:ℝ) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_pos.mpr hL).le
  calc
    _ ≤ ∑ d, spatialSplitChange k C r T f d :=
      Finset.sum_le_univ_sum_of_nonneg (fun d => spatialSplitChange_nonneg k C r T f d)
    _ ≤ _ := sum_spatialSplitChange_le k C r T f hf

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n : ℕ}

/-- On the SAME full sampled path, the true conditional mean of a fixed
later tree at each depth of its initial unary stretch. -/
noncomputable def stemMeanAt (S : PrescribedTree n) : (r : ℕ) → Fin (r+1) →
    KernelTower Ω (n+r) → (FinitePath Ω (n+r) → ℝ) → FinitePath Ω (n+r) → ℝ
  | 0, _, T, f, _ => treeMean S T f
  | r+1, d, T, f, x => Fin.cases (treeMean (stem S (r+1)) T f)
      (fun e => stemMeanAt S r e (T.2 x.1) (fun y => f (x.1,y)) x.2) d

@[simp] lemma stemMeanAt_zero (S : PrescribedTree n) (r : ℕ) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → ℝ) (x : FinitePath Ω (n+r)) :
    stemMeanAt S r 0 T f x=treeMean (stem S r) T f := by cases r <;> rfl

@[simp] lemma stemMeanAt_succ (S : PrescribedTree n) (r : ℕ) (d : Fin (r+1))
    (T : KernelTower Ω (n+r+1)) (f : FinitePath Ω (n+r+1) → ℝ)
    (x : FinitePath Ω (n+r+1)) :
    stemMeanAt S (r+1) d.succ T f x=
      stemMeanAt S r d (T.2 x.1) (fun y => f (x.1,y)) x.2 := rfl

/-- The actual squared L2 martingale increment at depth d. -/
noncomputable def stemIncrementSq (S : PrescribedTree n) (r : ℕ)
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → ℝ) (d : Fin r) : ℝ :=
  (KernelTower.law (n+r) T).expect (fun x =>
    (stemMeanAt S r d.succ T f x-stemMeanAt S r d.castSucc T f x)^2)

lemma stemIncrementSq_nonneg (S : PrescribedTree n) (r : ℕ)
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → ℝ) (d : Fin r) :
    0 ≤ stemIncrementSq S r T f d := FiniteLaw.expect_nonneg _ (fun _ => sq_nonneg _)

lemma stemIncrementSq_zero (S : PrescribedTree n) (r : ℕ)
    (T : KernelTower Ω (n+r+1)) (f : FinitePath Ω (n+r+1) → ℝ) :
    stemIncrementSq S (r+1) T f 0=
      T.1.covariance (fun a => treeMean (stem S r) (T.2 a) (fun y => f (a,y)))
        (fun a => treeMean (stem S r) (T.2 a) (fun y => f (a,y))) := by
  unfold stemIncrementSq
  refine (KernelTower.law_succ_expect (Ω := Ω) (n+r) T _).trans ?_
  change T.1.expect (fun a => (KernelTower.law (n+r) (T.2 a)).expect (fun y =>
    (stemMeanAt S r 0 (T.2 a) (fun z => f (a,z)) y-
      treeMean (stem S (r+1)) T f)^2)) = _
  simp only [stemMeanAt_zero,FiniteLaw.expect_const,stem,treeMean_unary]
  rw [FiniteLaw.covariance_centered]
  apply FiniteLaw.expect_congr
  intro a
  simp only [pow_two]
  rfl

lemma stemIncrementSq_succ (S : PrescribedTree n) (r : ℕ) (d : Fin r)
    (T : KernelTower Ω (n+r+1)) (f : FinitePath Ω (n+r+1) → ℝ) :
    stemIncrementSq S (r+1) T f d.succ=
      T.1.expect (fun a => stemIncrementSq S r (T.2 a) (fun y => f (a,y)) d) := by
  unfold stemIncrementSq
  refine (KernelTower.law_succ_expect (Ω := Ω) (n+r) T _).trans ?_
  simp only [Fin.castSucc_succ]
  rfl

/-- Exact orthogonality/telescoping identity for the literal conditional
means. Increments are compared on the same sampled prefix. -/
theorem sum_stemIncrementSq_eq (S : PrescribedTree n) (r : ℕ)
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → ℝ) :
    (∑ d : Fin r, stemIncrementSq S r T f d)=tailVariance S r T f := by
  induction r with
  | zero => simp [tailVariance,tailMean,FiniteLaw.covariance]
  | succ r ih =>
    rw [Fin.sum_univ_succ,stemIncrementSq_zero,tailVariance_step]
    congr 1
    simp_rw [stemIncrementSq_succ]
    rw [← FiniteLaw.expect_fintype_sum]
    exact T.1.expect_congr (fun a => ih (T.2 a) (fun y => f (a,y)))

/-- Scalar decor:martingale-energy, with no kernel or population-size
constant and no assumed filtration theorem. -/
theorem sum_stemIncrementSq_le_one (S : PrescribedTree n) (r : ℕ)
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → ℝ) (hf : ∀ x, |f x|≤1) :
    (∑ d : Fin r, stemIncrementSq S r T f d) ≤ 1 := by
  rw [sum_stemIncrementSq_eq]
  exact tailVariance_le_one S r T f hf

/-- Any regular subdomain may be used with the exact 1/L ranged-depth
normalization. Directions outside it are not renormalized. -/
theorem averaged_stemIncrementSq_le (S : PrescribedTree n) (r L : ℕ)
    (U : Finset (Fin r)) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → ℝ) (hf : ∀ x, |f x|≤1) :
    (∑ d ∈ U, stemIncrementSq S r T f d)/(L:ℝ) ≤ 1/(L:ℝ) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (Finset.sum_le_univ_sum_of_nonneg (stemIncrementSq_nonneg S r T f)).trans
    (sum_stemIncrementSq_le_one S r T f hf)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
