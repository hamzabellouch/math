import OAI.Probability.DilutedSpin.MatrixRoot

namespace OAI

section
section
namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω] {N : ℕ}

/-- The actual half squared three-copy contraction difference. Unlike
covariance energy this retains the positive conditional-mean contribution. -/
noncomputable def halfTripleDifferenceAt (n : ℕ) (T : KernelTower Ω n) (d : ℕ)
    (X : FinitePath Ω n → Fin N → ℝ) : ℝ :=
  (1/2:ℝ)*tripleExpectAt n T d
    (fun x y z => (FiniteLaw.dot (X x) (X y)-FiniteLaw.dot (X x) (X z))^2)

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N : ℕ}

/-- The nonnegative three-copy argument on an ARBITRARY old tree. Only the
geometric grouping of eligible paths is needed; all old paths and the test
are retained. This applies to the projected means of multi-leaf shapes. -/
theorem general_three_copy_bound_at (n d : ℕ) (hd : d < n) (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hp : ∀ j, 0 ≤ m j)
    (hend : m (Fin.last n) = 1)
    (S : PrescribedTree n) (a b : S.Leaf) (v : S.Internal)
    (hab : splitDepth S a b = d)
    (hav : freshSplitDepth S v a = d) (hbv : freshSplitDepth S v b = d)
    (X : FinitePath Ω n → Fin N → ℝ)
    (hOld : ∀ c, splitDepth S a c = d → ∀ x : Sample Ω S,
      X (S.pathAt c x) = X (S.pathAt b x)) :
    (-gamma S m v)*KernelTower.halfTripleDifferenceAt n T d X ≤
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) *
        (S.sampleLaw T).expect (fun x =>
          FiniteLaw.dot (X (S.pathAt a x)) (X (S.pathAt b x))^2) +
      pairObservableHistory T m S a d (fun x y => FiniteLaw.dot (X x) (X y))
        (fun x => FiniteLaw.dot (X (S.pathAt a x)) (X (S.pathAt b x))) := by
  classical
  let R := fun x y => FiniteLaw.dot (X x) (X y)
  let D := fun w : S.Internal => ((grow S w).sampleLaw T).expect (fun x =>
    (R (S.pathAt a (oldSample S w x)) (S.pathAt b (oldSample S w x)) -
      R ((grow S w).pathAt (oldLeaf S w a) x) ((grow S w).pathAt (newLeaf S w) x))^2)
  have hsum := pair_square_identity_general T m hend S a b d (by omega) hab R
    (fun c hc x => congrArg (FiniteLaw.dot (X (S.pathAt a x))) (hOld c hc x))
  have hnonneg (w : S.Internal) : 0 ≤ pairFreshCost S m a d w * D w :=
    mul_nonneg (pairFreshCost_nonneg S m hm hp a d w)
      (FiniteLaw.expect_nonneg _ (fun _ => sq_nonneg _))
  have hone : pairFreshCost S m a d v * D v ≤ ∑ w : S.Internal, pairFreshCost S m a d w * D w :=
    Finset.single_le_sum (fun w _ => hnonneg w) (Finset.mem_univ v)
  have hcost : pairFreshCost S m a d v = -gamma S m v := by
    unfold pairFreshCost
    rw [splitDepth_symm,splitDepth_new_old,hav,ite_eq_left rfl]
  have hD : D v = KernelTower.tripleExpectAt n T d
      (fun x y z => (FiniteLaw.dot (X x) (X y)-FiniteLaw.dot (X x) (X z))^2) := by
    have q := triple_marginal (grow S v) T (oldLeaf S v a) (oldLeaf S v b) (newLeaf S v)
      d (by omega) (by simpa only [splitDepth_old_old] using hab)
      (by simpa only [splitDepth_symm (grow S v) (oldLeaf S v a),splitDepth_new_old] using hav)
      (by simpa only [splitDepth_symm (grow S v) (oldLeaf S v b),splitDepth_new_old] using hbv)
      (fun x y z => (FiniteLaw.dot (X x) (X y)-FiniteLaw.dot (X x) (X z))^2)
    simpa only [D,R,pathAt_oldLeaf,pathAt_newLeaf] using q
  rw [hcost,hD] at hone

  change (1/2:ℝ)*(∑ w : S.Internal, pairFreshCost S m a d w * D w) = _ at hsum
  unfold KernelTower.halfTripleDifferenceAt
  linarith


end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance matrixTripleDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {L N : ℕ}

omit [Fintype C] [DecidableEq C] in
/-- The old test may be the physical overlap, rather than the projected
one. Its replacement costs precisely its L2 projection error. -/
theorem pair_three_copy_test_bound (n d : ℕ) (hd : d < n) (K : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hp : ∀ j, 0 ≤ m j)
    (hend : m (Fin.last n) = 1) (S : PrescribedTree n) (x y : S.Leaf) (v : S.Internal)
    (hxy : splitDepth S x y = d) (hxv : freshSplitDepth S v x = d) (hyv : freshSplitDepth S v y = d)
    (X : FinitePath Ω n → Fin N → ℝ) (hX : ∀ z i, |X z i| ≤ 1)
    (hOld : ∀ z, splitDepth S x z = d → ∀ w : Sample Ω S, X (S.pathAt z w) = X (S.pathAt y w))
    (f : Sample Ω S → ℝ) :
    (-gamma S m v)*KernelTower.halfTripleDifferenceAt n K d X ≤
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) +
      pairObservableHistory K m S x d (fun z w => FiniteLaw.dot (X z) (X w)) f +
      pairHistoryMass S m x * (S.sampleLaw K).l2
        (fun z => FiniteLaw.dot (X (S.pathAt x z)) (X (S.pathAt y z))-f z) := by
  let R := fun z w => FiniteLaw.dot (X z) (X w)
  let F := fun z : Sample Ω S => R (S.pathAt x z) (S.pathAt y z)
  have hR : ∀ z w, |R z w| ≤ 1 := fun z w => FiniteLaw.abs_dot_le_one _ _ (hX z) (hX w)
  have hδ : 0 ≤ m ⟨d+1,by omega⟩-m ⟨d,by omega⟩ := sub_nonneg.mpr (hm (by simp))
  have hF : (S.sampleLaw K).expect (fun z => F z^2) ≤ 1 := by
    calc
      _ ≤ (S.sampleLaw K).expect (fun _ => 1) := FiniteLaw.expect_mono _ (fun z =>
        (sq_le_one_iff_abs_le_one _).mpr (hR _ _))
      _ = _ := FiniteLaw.expect_const _ _
  have henergy := general_three_copy_bound_at n d hd K m hm hp hend S x y v
    hxy hxv hyv X hOld
  have htest := pairObservableHistory_l2 K m S x d R (fun z => F z-f z) hR
  rw [pairObservableHistory_sub_test] at htest
  have htest' := (le_abs_self _).trans htest
  have hsq := mul_le_mul_of_nonneg_left hF hδ
  change (-gamma S m v)*KernelTower.halfTripleDifferenceAt n K d X ≤
    (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)*(S.sampleLaw K).expect (fun z => F z^2)+
      pairObservableHistory K m S x d R F at henergy
  change (-gamma S m v)*KernelTower.halfTripleDifferenceAt n K d X ≤
    (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)+pairObservableHistory K m S x d R f+
      pairHistoryMass S m x*(S.sampleLaw K).l2 (fun z => F z-f z)
  linarith

/-- Pointwise-in-the-root crux of the shifted-shape induction. The first term
is SIGNED (not the expectation of its absolute value), so the physical
perturbation identity can be used after root averaging. Every error is an
actual single-copy L2 error and has the literal protected-history charge. -/
theorem matrix_three_copy_pointwise (hL : 0 < L) (Q : Finset ℕ)
    (T S : PrescribedTree L) (q : C → T.Leaf) (hq : Function.Bijective q)
    (hS : branchingCount S (· ∈ Q) = 0) (K : KernelTower Ω L)
    (a c : C) (hac : a ≠ c) (cs : List C) (hcs : cs.Nodup)
    (hdis : ∀ d ∈ cs, d ∉ insert c ({a} : Finset C))
    (hfull : insert c ({a} : Finset C) ∪ cs.toFinset = Finset.univ)
    (x y : S.Leaf) (v : S.Internal) (d : ℕ) (hd : d < L)
    (hqd : splitDepth T (q a) (q c) = d) (hxy : splitDepth S x y = d)
    (hxv : freshSplitDepth S v x = d) (hyv : freshSplitDepth S v y = d)
    (X : FinitePath Ω L → Fin N → ℝ) (hX : ∀ z i, |X z i| ≤ 1)
    (hOld : ∀ z, splitDepth S x z = d → ∀ w : Sample Ω S, X (S.pathAt z w) = X (S.pathAt y w))
    (A : (C → FinitePath Ω L) → ℝ) (f : Sample Ω S → ℝ) (hf : ∀ z, |f z| ≤ 1) :
    let m := grid L 0 L
    let J := partialKappa T m (Finset.univ.image q) /
      partialKappa T m ((insert c ({a} : Finset C)).image q)
    let H := weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect (fun z => g z*A (fun b => D.pathAt (pos b) z)))
      m (c::cs) S (Finset.univ.erase x) id (fun _ => x) f
    let E := (T.sampleLaw K).l2 (fun z => A (fun b => T.pathAt (q b) z)-
      FiniteLaw.dot (X (T.pathAt (q a) z)) (X (T.pathAt (q c) z)))
    let B := chargeBound (2*(leaves S+(c::cs).length:ℕ))
      ((Q.card:ℝ)*(leaves S+(c::cs).length:ℕ)) (c::cs).length (branchingCount T (· ∈ Q)) *
      (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))
    (-gamma S m v)*KernelTower.halfTripleDifferenceAt L K d X ≤
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) + H/J + E*B/|J| +
      pairHistoryMass S m x * (S.sampleLaw K).l2
        (fun z => FiniteLaw.dot (X (S.pathAt x z)) (X (S.pathAt y z))-f z) := by
  dsimp only
  let m := grid L 0 L
  let J := partialKappa T m (Finset.univ.image q) /
      partialKappa T m ((insert c ({a} : Finset C)).image q)
  let R := fun z w => FiniteLaw.dot (X z) (X w)
  let F := fun z : Sample Ω S => R (S.pathAt x z) (S.pathAt y z)
  let H := weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect (fun z => g z*A (fun b => D.pathAt (pos b) z)))
      m (c::cs) S (Finset.univ.erase x) id (fun _ => x) f
  let HP := weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect (fun z => g z*R (D.pathAt (pos a) z) (D.pathAt (pos c) z)))
      m (c::cs) S (Finset.univ.erase x) id (fun _ => x) f
  let E := (T.sampleLaw K).l2 (fun z => A (fun b => T.pathAt (q b) z)-R (T.pathAt (q a) z) (T.pathAt (q c) z))
  let B := chargeBound (2*(leaves S+(c::cs).length:ℕ))
      ((Q.card:ℝ)*(leaves S+(c::cs).length:ℕ)) (c::cs).length (branchingCount T (· ∈ Q)) *
      (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))
  have hm := grid_strictMono hL
  have hp : ∀ j, 0 ≤ m j := grid_nonneg
  have hend : m (Fin.last L) = 1 := grid_last hL
  have hJ : J ≠ 0 := div_ne_zero (partialKappa_ne_zero T m hm hp _)
    (partialKappa_ne_zero T m hm hp _)
  have henergy := pair_three_copy_test_bound L d hd K m hm.monotone hp hend S x y v
    hxy hxv hyv X hX hOld f
  have hU : (Finset.univ.erase x).card ≤ leaves S := by
    exact (Finset.card_erase_le).trans (by simp only [Finset.card_univ, card_leaf]; rfl)
  have hproj : |H-HP| ≤ E*B := by
    simpa only [H, HP, E, B, m, weightedMatrixHistory] using
      (projection_history_difference hL Q T S q hq.2 hS K A
        (fun z => R (z a) (z c)) (c::cs) (Finset.univ.erase x) id (fun _ => x) f hf hU)
  have hpair : HP = J*pairObservableHistory K m S x d R f := by
    have h := matrixHistory_first_pair T q hq.1 K m hm hp hend a c hac cs hcs hdis hfull S x R f
    simpa only [hqd] using h
  have happrox := signed_approximation hJ hproj
  rw [hpair,mul_div_cancel_left₀ _ hJ] at happrox
  change (-gamma S m v)*KernelTower.halfTripleDifferenceAt L K d X ≤
    (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)+H/J+E*B/|J|+
      pairHistoryMass S m x*(S.sampleLaw K).l2 (fun z => F z-f z)
  change (-gamma S m v)*KernelTower.halfTripleDifferenceAt L K d X ≤
    (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)+pairObservableHistory K m S x d R f+
      pairHistoryMass S m x*(S.sampleLaw K).l2 (fun z => F z-f z) at henergy
  linarith

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance kappaLowerDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
noncomputable local instance kappaLowerLeafDecidableEq {depth : ℕ} (tree : PrescribedTree depth) :
    DecidableEq tree.Leaf := Classical.decEq _

/-- Higher-degree factors, after removing the one grid increment per branching vertex. -/
noncomputable def branchExcess : {n : ℕ} → PrescribedTree n → ℕ
  | 0, .leaf => 0
  | _+1, .node k C => (k:ℕ)-2 + ∑ i, branchExcess (C i)

lemma branchProduct_lower {x y η : ℝ} (hxy : x ≤ y) (hη : 0 ≤ η) (hy : η ≤ y) (k : ℕ) :
    (y-x)*η^k ≤ |branchProduct x y (k+2)| := by
  classical
  induction k with
  | zero =>
    simp only [pow_zero,mul_one,branchProduct,show (2:ℕ)-1 = 1 from rfl,Finset.prod_range_one,Nat.cast_zero,zero_add,one_mul]
    rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith
  | succ k ih =>
    rw [show k+1+2 = (k+2)+1 by omega,branchProduct_succ x y (by omega),abs_mul,pow_succ]
    have hh : η ≤ |x-((k+2:ℕ):ℝ)*y| := by
      have hY : 0 ≤ y := hη.trans hy
      have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
      have hmul := mul_nonneg hk hY
      have hn : x-((k+2:ℕ):ℝ)*y ≤ 0 := by push_cast; nlinarith
      rw [abs_of_nonpos hn]
      push_cast
      nlinarith
    simpa only [mul_assoc] using mul_le_mul ih hh hη (abs_nonneg _)

lemma branchProduct_lower_pos {x y η : ℝ} (hxy : x ≤ y) (hη : 0 ≤ η) (hy : η ≤ y)
    (k : ℕ+) :
    (y-x)^(if 1 < (k:ℕ) then 1 else 0)*η^((k:ℕ)-2) ≤ |branchProduct x y k| := by
  classical
  have hk := k.property
  by_cases h : 1 < (k:ℕ)
  · obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le (show 2 ≤ (k:ℕ) by omega)
    have hkj : (k:ℕ) = j+2 := by omega
    simp only [ite_eq_left h,pow_one]
    rw [hkj]
    simp only [Nat.add_sub_cancel]
    exact branchProduct_lower hxy hη hy j
  · have hle : (k:ℕ) ≤ 1 := le_of_not_gt h
    have he : (k:ℕ) = 1 := Nat.le_antisymm hle (Nat.succ_le_of_lt hk)
    simp [he]

lemma leaf_nonempty {n : ℕ} (S : PrescribedTree n) : Nonempty S.Leaf := by
  induction S with
  | leaf => exact ⟨()⟩
  | @node n k C ih =>
    obtain ⟨a⟩ := ih ⟨0,k.property⟩
    exact ⟨⟨⟨0,k.property⟩,a⟩⟩

lemma childRefs_univ {n : ℕ} {k : ℕ+} (C : Fin k → PrescribedTree n) (i : Fin k) :
    childRefs (C := C) Finset.univ i = Finset.univ := by
  classical
  ext a
  rw [mem_childRefs]
  exact iff_of_true (Finset.mem_univ _) (Finset.mem_univ _)

lemma partialKappa_univ_node {n : ℕ} (k : ℕ+) (C : Fin k → PrescribedTree n)
    (m : Fin (n+2) → ℝ) :
    partialKappa (.node k C) m Finset.univ = branchProduct (m 0) (m 1) k *
      ∏ i, partialKappa (C i) (fun j => m j.succ) Finset.univ := by
  classical
  rw [partialKappa]
  have he : Finset.image (fun a : Leaf (.node k C) => a.1) Finset.univ = Finset.univ := by
    ext i
    simp only [Finset.mem_image,Finset.mem_univ,true_and,iff_true]
    obtain ⟨a⟩ := leaf_nonempty (C i)
    exact ⟨⟨i,a⟩,rfl⟩
  rw [he]
  simp only [Finset.card_univ,Fintype.card_fin,childRefs_univ]

/-- Every vertex with at least three children has its higher-degree reference
factors bounded away from zero. Binary vertices need only the grid increment. -/
noncomputable def BranchRegular : {n : ℕ} → PrescribedTree n → (Fin (n+1) → ℝ) → ℝ → Prop
  | 0, .leaf, _, _ => True
  | _+1, .node k C, m, η => (2 < (k:ℕ) → η ≤ m 1) ∧
      ∀ i, BranchRegular (C i) (fun j => m j.succ) η

lemma branchProduct_lower_regular {x y η : ℝ} (hxy : x ≤ y) (hη : 0 ≤ η) (k : ℕ+)
    (hy : 2 < (k:ℕ) → η ≤ y) :
    (y-x)^(if 1 < (k:ℕ) then 1 else 0)*η^((k:ℕ)-2) ≤ |branchProduct x y k| := by
  classical
  by_cases hk : 2 < (k:ℕ)
  · exact branchProduct_lower_pos hxy hη (hy hk) k
  · have hp := k.property
    have hle : (k:ℕ) ≤ 2 := le_of_not_gt hk
    have he : (k:ℕ) = 1 ∨ (k:ℕ) = 2 := by
      rcases Nat.lt_or_eq_of_le hle with hs | hs
      · exact Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ hs) (Nat.succ_le_of_lt hp))
      · exact Or.inr hs
    rcases he with he|he
    · simp [he]
    · simp only [he,show 1 < (2:ℕ) from by omega,ite_true,pow_one,Nat.sub_self,pow_zero,mul_one]
      simp only [branchProduct,show (2:ℕ)-1 = 1 from rfl,Finset.prod_range_one,Nat.cast_zero,zero_add,one_mul]
      rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
      linarith

 
theorem partialKappa_grid_lower {n : ℕ} (S : PrescribedTree n) (d L : ℕ)
    (η : ℝ) (hη : 0 ≤ η) (hr : BranchRegular S (grid n d L) η) :
    (L:ℝ)⁻¹^(branchingCount S (fun _ => True))*η^(branchExcess S) ≤
      |partialKappa S (grid n d L) Finset.univ| := by
  classical
  induction S generalizing d with
  | leaf => simp [partialKappa,branchingCount,branchExcess]
  | @node n k C ih =>
    have he : (fun j : Fin (n+1) => grid (n+1) d L j.succ) = grid n (d+1) L := by
      funext j
      simp [grid,Fin.val_succ,Nat.add_comm,Nat.add_left_comm]
    have hr' : (2 < (k:ℕ) → η ≤ grid (n+1) d L 1) ∧
        ∀ i, BranchRegular (C i) (grid n (d+1) L) η := by
      simpa only [BranchRegular,he] using hr
    have hδ : grid (n+1) d L 1-grid (n+1) d L 0 = (L:ℝ)⁻¹ := by
      simp [grid,Nat.cast_add,add_div]
    have hle : grid (n+1) d L 0 ≤ grid (n+1) d L 1 := by
      have hnonneg : (0:ℝ) ≤ (L:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg L)
      linarith
    have hroot := branchProduct_lower_regular hle hη k hr'.1
    rw [hδ] at hroot
    have hchild := Finset.prod_le_prod₀ (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) =>
      mul_nonneg (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg L)) _) (pow_nonneg hη _))
      (fun i _ => ih i (d+1) (hr'.2 i))
    have h := mul_le_mul hroot hchild
      (Finset.prod_nonneg (fun i _ => mul_nonneg
        (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg L)) _) (pow_nonneg hη _))) (abs_nonneg _)
    rw [partialKappa_univ_node,abs_mul,Finset.abs_prod,he]
    convert h using 1
    simp only [branchingCount,branchExcess,true_and,pow_add,Finset.prod_mul_distrib,← Finset.prod_pow_eq_pow_sum]
    ring

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
