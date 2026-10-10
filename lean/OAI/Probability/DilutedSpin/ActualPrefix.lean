import OAI.Probability.DilutedSpin.RetainedHistory
import OAI.Probability.DilutedSpin.SizeSpinRoot

namespace OAI

section
section
namespace DilutedSpinGlass.FinitePath

/-- Equality of the first e sampled coordinates (root variables are held fixed). -/
def Agree {Ω : Type} : (e : ℕ) → {n : ℕ} → FinitePath Ω n → FinitePath Ω n → Prop
  | 0, _, _, _ => True
  | _+1, 0, _, _ => True
  | e+1, _+1, x, y => x.1 = y.1 ∧ Agree e x.2 y.2

@[refl] theorem Agree.refl {Ω : Type} (e : ℕ) {n : ℕ} (x : FinitePath Ω n) :
    Agree e x x := by
  induction e generalizing n with
  | zero => trivial
  | succ e ih =>
    cases n with
    | zero => trivial
    | succ n => exact ⟨rfl,ih x.2⟩

def PrefixFunction {Ω : Type} {n : ℕ} (e : ℕ) (D : FinitePath Ω n → ℝ) : Prop :=
  ∀ x y, Agree e x y → D x = D y

end DilutedSpinGlass.FinitePath

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance actualPrefixPropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω : Type}

/-- Shared labeled prefixes have identical samples even when leaf values collide
elsewhere. This is only an implication from POSITION to sampled values. -/
theorem paths_agree {n : ℕ} (S : PrescribedTree n) (a b : Leaf S)
    (x : Sample Ω S) (e : ℕ) (he : e ≤ splitDepth S a b) :
    FinitePath.Agree e (pathAt S a x) (pathAt S b x) := by
  induction S generalizing e with
  | leaf =>
    have : e = 0 := by change e ≤ 0 at he; omega
    subst e
    trivial
  | @node n k C ih =>
    cases e with
    | zero => trivial
    | succ e =>
      obtain ⟨i,a⟩ := a
      obtain ⟨j,b⟩ := b
      by_cases hij : i = j
      · subst j
        rw [splitDepth_same_child] at he
        exact ⟨rfl,ih i a b (x i).2 e (by omega)⟩
      · rw [splitDepth_diff_child C i j hij] at he
        omega

/-- The fresh path shares precisely the retained old prefix stipulated by its
uncontracted divergence vertex. -/
theorem fresh_path_agrees {n : ℕ} (S : PrescribedTree n) (v : Internal S)
    (a : Leaf S) (x : Sample Ω (grow S v)) (e : ℕ)
    (he : e ≤ freshSplitDepth S v a) :
    FinitePath.Agree e (newPath S v x) (pathAt S a (oldSample S v x)) := by
  have h := paths_agree (grow S v) (newLeaf S v) (oldLeaf S v a) x e
    (by simpa only [splitDepth_new_old] using he)
  simpa only [pathAt_newLeaf,pathAt_oldLeaf] using h

/-- All old-or-fresh choices following an old prefix through depth e have total
coefficient m_e. This includes all descendants, not only fresh unary branches. -/
theorem prefix_choices_total {n : ℕ} (S : PrescribedTree n) (a : Leaf S)
    (m : Fin (n+1) → ℝ) (hend : m (Fin.last n) = 1)
    (e : ℕ) (he : e ≤ n) :
    (∑ b : Leaf S, if e ≤ splitDepth S b a then (1:ℝ) else 0) +
      (∑ v : Internal S, if e ≤ freshSplitDepth S v a then gamma S m v else 0) =
        m ⟨e,by omega⟩ := by
  induction S generalizing e with
  | leaf =>
    have : e = 0 := by omega
    subst e
    have h := all_choices_total (.leaf : PrescribedTree 0) m hend
    simpa only [Nat.zero_le,ite_true,Fin.zero_eta] using h
  | @node n k C ih =>
    cases e with
    | zero =>
      simpa only [Nat.zero_le,ite_true,Fin.zero_eta] using all_choices_total (.node k C) m hend
    | succ e =>
      obtain ⟨i,a⟩ := a
      change (∑ b : (j : Fin k) × Leaf (C j), _) +
        (∑ v : Option ((j : Fin k) × Internal (C j)), _) = _
      rw [Fintype.sum_sigma,Fintype.sum_option,Fintype.sum_sigma]
      have ho (j : Fin k) :
          (∑ b : Leaf (C j), if e+1 ≤ splitDepth (.node k C) ⟨j,b⟩ ⟨i,a⟩ then (1:ℝ) else 0) =
          if j = i then ∑ b : Leaf (C i), if e ≤ splitDepth (C i) b a then (1:ℝ) else 0 else 0 := by
        by_cases h : j = i
        · subst j
          simp only [ite_true,splitDepth_same_child,show ∀ t:ℕ, e+1 ≤ 1+t ↔ e≤t by omega]
        · simp [h,splitDepth_diff_child C j i h]
      have hf (j : Fin k) :
          (∑ v : Internal (C j), if e+1 ≤ freshSplitDepth (.node k C) (some ⟨j,v⟩) ⟨i,a⟩ then
            gamma (.node k C) m (some ⟨j,v⟩) else 0) =
          if j = i then ∑ v : Internal (C i), if e ≤ freshSplitDepth (C i) v a then
            gamma (C i) (fun q => m q.succ) v else 0 else 0 := by
        by_cases h : j = i
        · subst j
          simp only [ite_true,freshSplitDepth_same_child,gamma,
            show ∀ t:ℕ, e+1 ≤ 1+t ↔ e≤t by omega]
        · simp [h,freshSplitDepth_diff_child C j i (Ne.symm h)]
      simp_rw [ho,hf]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      have hz : freshSplitDepth (.node k C) none ⟨i,a⟩ = 0 := rfl
      rw [hz,ite_eq_right (by omega : ¬ e+1 ≤ 0),zero_add]
      exact ih i a (fun q => m q.succ) hend e (by omega)

variable [Fintype Ω]

/-- Exact joint marginal for the prefix-through-e class. Multiplication by an
arbitrary old test is retained throughout, as required in decorrelation: the
new path may be a reused old leaf or any fresh descendant of the prefix. -/
theorem prefix_choices_expectation {n : ℕ} (S : PrescribedTree n) (K : KernelTower Ω n)
    (a : Leaf S) (m : Fin (n+1) → ℝ) (hend : m (Fin.last n) = 1)
    (e : ℕ) (he : e ≤ n) (D : FinitePath Ω n → ℝ) (hD : FinitePath.PrefixFunction e D)
    (H : Sample Ω S → ℝ) :
    (∑ b : Leaf S, if e ≤ splitDepth S b a then
      (sampleLaw S K).expect (fun x => H x * D (pathAt S b x)) else 0) +
    (∑ v : Internal S, if e ≤ freshSplitDepth S v a then
      gamma S m v * (sampleLaw (grow S v) K).expect
        (fun x => H (oldSample S v x) * D (newPath S v x)) else 0) =
    m ⟨e,by omega⟩ * (sampleLaw S K).expect (fun x => H x * D (pathAt S a x)) := by
  let Z := (sampleLaw S K).expect (fun x => H x * D (pathAt S a x))
  have ho (b : Leaf S) :
      (if e ≤ splitDepth S b a then (sampleLaw S K).expect (fun x => H x * D (pathAt S b x)) else 0) =
      (if e ≤ splitDepth S b a then (1:ℝ) else 0) * Z := by
    split_ifs with hb
    · rw [one_mul]
      apply FiniteLaw.expect_congr
      intro x
      rw [hD _ _ (paths_agree S b a x e hb)]
    · simp
  have hf (v : Internal S) :
      (if e ≤ freshSplitDepth S v a then gamma S m v * (sampleLaw (grow S v) K).expect
        (fun x => H (oldSample S v x) * D (newPath S v x)) else 0) =
      (if e ≤ freshSplitDepth S v a then gamma S m v else 0) * Z := by
    split_ifs with hv
    · congr 1
      calc
        _ = (sampleLaw (grow S v) K).expect (fun x =>
            H (oldSample S v x) * D (pathAt S a (oldSample S v x))) := by
          apply FiniteLaw.expect_congr
          intro x
          rw [hD _ _ (fresh_path_agrees S v a x e hv)]
        _ = Z := grow_projectivity S K v (fun x => H x * D (pathAt S a x))
    · simp
  simp_rw [ho,hf]
  rw [← Finset.sum_mul,← Finset.sum_mul,← add_mul,prefix_choices_total S a m hend e he]

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω]

theorem abs_expect_le_expect_abs (P : FiniteLaw Ω) (f : Ω → ℝ) :
    |P.expect f| ≤ P.expect (fun x => |f x|) := by
  unfold expect
  exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
    apply Finset.sum_congr rfl
    intro x _
    rw [abs_mul,abs_of_nonneg (P.nonneg x)])

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.SizeCoupling
open scoped BigOperators

noncomputable def spinMean {N p k l r : ℕ} [NeZero N] {A : Fin l → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (theta : Fin k → InteractionSample p) (h : Fin N → ℝ)
    (ψ : (i : Fin l) → Spin → FinitePath (A i) (r+1) → ℝ) : ℝ :=
  (FiniteLaw.pi (fun _ : Fin k => FiniteLaw.pi (fun _ : Fin p =>
      (FiniteLaw.uniform : FiniteLaw (Fin N))))).expect (fun indices =>
    (FiniteLaw.pi (fun _ : Fin l => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect
      (fun sites => spinRoot Q m theta h indices sites ψ))

theorem expected_total_new_count (N k p : ℕ) [NeZero N] :
    (FiniteLaw.pi (fun _ : Fin k => FiniteLaw.pi (fun _ : Fin p => indexLaw N))).expect
      (fun z => ∑ j, ∑ q, if (z j q).1 = 0 then (1:ℝ) else 0) = (k:ℝ)*p/(N+1) := by
  rw [FiniteLaw.expect_fintype_sum]
  have hm (j : Fin k) :
      (FiniteLaw.pi (fun _ : Fin k => FiniteLaw.pi (fun _ : Fin p => indexLaw N))).expect
        (fun z => ∑ q, if (z j q).1 = 0 then (1:ℝ) else 0) = (p:ℝ)/(N+1) := by
    exact (FiniteLaw.expect_pi_marginal (fun _ : Fin k => FiniteLaw.pi (fun _ : Fin p => indexLaw N)) j
      (fun z => ∑ q, if (z q).1 = 0 then (1:ℝ) else 0)).trans (expected_new_count N p)
  simp only [hm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- Exact with-replacement uniform-site coupling estimate before averaging
physical disorder or mark specifications. Both finite-size marginals are the
actual independent index laws. -/
theorem spinMean_size_coupling {N p k l r : ℕ} [NeZero N] {A : Fin l → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (theta : Fin k → InteractionSample p) (h : Fin (N+1) → ℝ)
    (ψ : (i : Fin l) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hθ : ∀ j σ, |(theta j).1 σ| ≤ C) (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) :
    |spinMean Q m theta h ψ-spinMean Q m theta (fun i => h i.succ) ψ| ≤
      |h 0|+2*C*k*p/(N+1)+2*D*l/(N+1) := by
  let P := FiniteLaw.pi (fun _ : Fin k => FiniteLaw.pi (fun _ : Fin p => indexLaw N))
  let R := FiniteLaw.pi (fun _ : Fin l => indexLaw N)
  have po := FiniteLaw.Projects.pi (fun _ : Fin k =>
    FiniteLaw.Projects.pi (fun _ : Fin p => oldIndex_projects N))
  have pn := FiniteLaw.Projects.pi (fun _ : Fin k =>
    FiniteLaw.Projects.pi (fun _ : Fin p => newIndex_projects N))
  have ro := FiniteLaw.Projects.pi (fun _ : Fin l => oldIndex_projects N)
  have rn := FiniteLaw.Projects.pi (fun _ : Fin l => newIndex_projects N)
  let f := fun (z : Fin k → Fin p → Fin (N+1) × Fin N) (w : Fin l → Fin (N+1) × Fin N) => spinRoot Q m theta h (fun j q => newIndex (z j q)) (fun i => newIndex (w i)) ψ
  let g := fun (z : Fin k → Fin p → Fin (N+1) × Fin N) (w : Fin l → Fin (N+1) × Fin N) => spinRoot Q m theta (fun i => h i.succ)
    (fun j q => oldIndex (z j q)) (fun i => oldIndex (w i)) ψ
  have hn : P.expect (fun z => R.expect (f z)) = spinMean Q m theta h ψ := by
    unfold spinMean
    calc
      _ = P.expect (fun z => (FiniteLaw.pi (fun _ : Fin l =>
          (FiniteLaw.uniform : FiniteLaw (Fin (N+1))))).expect
            (fun w => spinRoot Q m theta h (fun j q => newIndex (z j q)) w ψ)) :=
        P.expect_congr (fun z => rn (fun w => spinRoot Q m theta h (fun j q => newIndex (z j q)) w ψ))
      _ = _ := pn (fun indices =>
        (FiniteLaw.pi (fun _ : Fin l => (FiniteLaw.uniform : FiniteLaw (Fin (N+1))))).expect
          (fun sites => spinRoot Q m theta h indices sites ψ))
  have ho : P.expect (fun z => R.expect (g z)) = spinMean Q m theta (fun i => h i.succ) ψ := by
    unfold spinMean
    calc
      _ = P.expect (fun z => (FiniteLaw.pi (fun _ : Fin l =>
          (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect
            (fun w => spinRoot Q m theta (fun i => h i.succ) (fun j q => oldIndex (z j q)) w ψ)) :=
        P.expect_congr (fun z => ro (fun w => spinRoot Q m theta (fun i => h i.succ) (fun j q => oldIndex (z j q)) w ψ))
      _ = _ := po (fun indices =>
        (FiniteLaw.pi (fun _ : Fin l => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect
          (fun sites => spinRoot Q m theta (fun i => h i.succ) indices sites ψ))
  rw [← hn,← ho,← FiniteLaw.expect_sub]
  calc
    _ ≤ P.expect (fun z => |R.expect (f z)-R.expect (g z)|) := P.abs_expect_le_expect_abs _
    _ ≤ P.expect (fun z => R.expect (fun w => |f z w-g z w|)) := P.expect_mono (fun z => by
      rw [← FiniteLaw.expect_sub]
      exact R.abs_expect_le_expect_abs _)
    _ ≤ P.expect (fun z => R.expect (fun w =>
        |h 0|+2*C*(∑ j, ∑ q, if (z j q).1 = 0 then (1:ℝ) else 0)+
          2*D*(∑ i, if (w i).1 = 0 then (1:ℝ) else 0))) :=
      P.expect_mono (fun z => R.expect_mono (fun w => spinRoot_size_coupling Q m hm theta h z w ψ hC hD hθ hψ))
    _ = _ := by
      simp only [FiniteLaw.expect_add,FiniteLaw.expect_const,FiniteLaw.expect_mul_left,
        R,P,expected_new_count,expected_total_new_count]
      ring

end DilutedSpinGlass.SizeCoupling
end

end

section
section
namespace DilutedSpinGlass
open scoped BigOperators

lemma bounded_product_one_difference_sq {ι : Type*} [Fintype ι]
    (F G : ι → ℝ) (a : ι) (hF : ∀ i, |F i| ≤ 1) (hG : ∀ i, |G i| ≤ 1)
    (he : ∀ i, i ≠ a → F i=G i) : ((∏ i, F i)-(∏ i, G i))^2 ≤ (F a-G a)^2 := by
  classical
  have hb := bounded_product_difference Finset.univ F G (fun i _ => hF i) (fun i _ => hG i)
  have hs : (∑ i, |F i-G i|) = |F a-G a| := by
    apply Finset.sum_eq_single a
    · intro b _ hba
      rw [he b hba, sub_self,abs_zero]
    · simp
  rw [hs] at hb
  exact sq_le_sq.mpr hb

namespace PrescribedTree
variable {Ω : Type} [Fintype Ω] {n : ℕ}

theorem treeMean_node_one_difference_sq (k : ℕ+) (C D : Fin k → PrescribedTree n)
    (i : Fin k) (he : ∀ j, j ≠ i → C j=D j) (T : KernelTower Ω (n+1))
    (f : FinitePath Ω (n+1) → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    (treeMean (.node k C) T f-treeMean (.node k D) T f)^2 ≤ T.1.expect (fun a =>
      (treeMean (C i) (T.2 a) (fun y => f (a,y))-treeMean (D i) (T.2 a) (fun y => f (a,y)))^2) := by
  have h := bounded_product_one_difference_sq
    (fun j => T.1.expect (fun a => treeMean (C j) (T.2 a) (fun y => f (a,y))))
    (fun j => T.1.expect (fun a => treeMean (D j) (T.2 a) (fun y => f (a,y)))) i
    (fun j => T.1.abs_expect_le (fun a => treeMean_bound (C j) (T.2 a) (fun y => hf (a,y))))
    (fun j => T.1.abs_expect_le (fun a => treeMean_bound (D j) (T.2 a) (fun y => hf (a,y))))
    (by intro j hj; rw [he j hj])
  apply h.trans
  have hh := T.1.sq_expect_le_expect_sq (fun a =>
    treeMean (C i) (T.2 a) (fun y => f (a,y))-treeMean (D i) (T.2 a) (fun y => f (a,y)))
  rwa [FiniteLaw.expect_sub] at hh

/-- A literal prescribed-tree context with one designated descendant hole;
sibling branches are retained as genuine shapes, not erased from the test. -/
inductive TreeContext (h : ℕ) : ℕ → Type
  | hole : TreeContext h h
  | node {n : ℕ} (k : ℕ+) (C : Fin k → PrescribedTree n) (i : Fin k)
      (inner : TreeContext h n) : TreeContext h (n+1)

def TreeContext.plug {h : ℕ} : {n : ℕ} → TreeContext h n → PrescribedTree h → PrescribedTree n
  | _, .hole, S => S
  | _, .node k C i inner, S => .node k (Function.update C i (inner.plug S))

/-- Propagation to ANY ancestor contracts the total squared difference.
Precisely one sampled prefix remains after the other branches integrate out.
The uniform family estimate is applied to the actual tower at that prefix. -/
theorem TreeContext.sum_difference_le {h n : ℕ} {ι : Type*} [Fintype ι]
    (ctx : TreeContext h n) (S D : ι → PrescribedTree h) (B : ℝ)
    (hB : ∀ (T : KernelTower Ω h) (f : FinitePath Ω h → ℝ), (∀ x, |f x| ≤ 1) →
      (∑ i, (treeMean (S i) T f-treeMean (D i) T f)^2) ≤ B) :
    ∀ (T : KernelTower Ω n) (f : FinitePath Ω n → ℝ), (∀ x, |f x| ≤ 1) →
      (∑ i, (treeMean (ctx.plug (S i)) T f-treeMean (ctx.plug (D i)) T f)^2) ≤ B := by
  induction ctx with
  | hole => exact hB
  | @node n k C a inner ih =>
    intro T f hf
    calc
      _ ≤ ∑ i, T.1.expect (fun x =>
          (treeMean (inner.plug (S i)) (T.2 x) (fun y => f (x,y))-
            treeMean (inner.plug (D i)) (T.2 x) (fun y => f (x,y)))^2) := by
        apply Finset.sum_le_sum
        intro i _
        have hh := treeMean_node_one_difference_sq k
          (Function.update C a (inner.plug (S i))) (Function.update C a (inner.plug (D i))) a
          (by intro j hj; simp only [Function.update_of_ne hj]) T f hf
        simpa only [TreeContext.plug,Function.update_self] using hh
      _ = T.1.expect (fun x => ∑ i,
          (treeMean (inner.plug (S i)) (T.2 x) (fun y => f (x,y))-
            treeMean (inner.plug (D i)) (T.2 x) (fun y => f (x,y)))^2) :=
        (FiniteLaw.expect_fintype_sum _ _).symm
      _ ≤ T.1.expect (fun _ => B) := T.1.expect_mono (fun x =>
        ih (T.2 x) (fun y => f (x,y)) (fun y => hf (x,y)))
      _ = B := FiniteLaw.expect_const _ _

 
theorem contextual_split_shift_le {h n : ℕ} (k : ℕ+) (C : Fin k → PrescribedTree h)
    (r : ℕ) (ctx : TreeContext (h+r+1) n) (T : KernelTower Ω n)
    (f : FinitePath Ω n → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    (∑ d : Fin r, (treeMean (ctx.plug (splitFamily k C r d.castSucc)) T f -
      treeMean (ctx.plug (splitFamily k C r d.succ)) T f)^2) ≤ (k:ℝ)^2 := by
  exact ctx.sum_difference_le (Ω := Ω) (ι := Fin r) (fun d => splitFamily k C r d.castSucc)
    (fun d => splitFamily k C r d.succ) ((k:ℝ)^2)
    (fun K F hF => splitShiftEnergy_le k C r K F hF) T f hf

end PrescribedTree
end DilutedSpinGlass
end

end

end OAI
