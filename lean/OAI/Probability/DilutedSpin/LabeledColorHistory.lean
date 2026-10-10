import OAI.Probability.DilutedSpin.ActualTreeSelector
import OAI.Probability.DilutedSpin.ColorPolarization
import OAI.Probability.DilutedSpin.ShapeEmbedding

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

lemma anchorAt_one {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n, m j.succ ≠ 0)
    {ι : Type} (U : Finset ι) (paths : ι → Sample Ω S → FinitePath Ω n)
    (G : Sample Ω S → ℝ) :
    anchorAt S T m U paths G (fun _ => 1) = (sampleLaw S T).expect G := by
  have h := anchorEval_zero S T m hm (fun _ => 0) U paths G
  simpa only [anchorEval,fullyProtected,anchorAt,protectedAt,mul_zero,add_zero,zero_mul] using h

/-- The signed ordered history sum, retaining every actual old position and
new branch. The terminal observable may inspect all assigned color positions.
This is only an explicit finite expansion, not an assumed identity. -/
noncomputable def labeledHistory {n : ℕ} {C ι : Type} [DecidableEq C] [DecidableEq ι]
    (m : Fin (n+1) → ℝ)
    (V : (S : PrescribedTree n) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ) :
    List C → (S : PrescribedTree n) → Finset ι → (ι → S.Leaf) →
      (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ
  | [], S, _, _, pos, f => V S pos f
  | c::cs, S, U, loc, pos, f =>
      (∑ i ∈ U, labeledHistory m V cs S (U.erase i) loc
        (Function.update pos c (loc i)) f) +
      ∑ v : Internal S, gamma S m v * labeledHistory m V cs (grow S v) U
        (fun i => oldLeaf S v (loc i))
        (Function.update (fun c => oldLeaf S v (pos c)) c (newLeaf S v))
        (fun x => f (oldSample S v x))

/-- The genuine mixed derivative has precisely the signed labeled-history
expansion. No factorial, unsigned normalization, or law is substituted. -/
theorem coloredAt_labeledHistory {n : ℕ} {C ι : Type} [Fintype C]
    [DecidableEq C] [DecidableEq ι] (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n, m j.succ ≠ 0)
    (D : C → FinitePath Ω n → ℝ) (cs : List C) (hcs : cs.Nodup)
    (P : Finset C) (hdis : ∀ c ∈ cs, c ∉ P) (hfull : P ∪ cs.toFinset = Finset.univ)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    coloredAt T m (cs.map D) S U (fun i => S.pathAt (loc i))
      (fun x => f x * ∏ c ∈ P, D c (S.pathAt (pos c) x)) (fun _ => 1) =
    labeledHistory m (fun S pos f => (S.sampleLaw T).expect
      (fun x => f x * ∏ c, D c (S.pathAt (pos c) x))) cs S U loc pos f := by
  induction cs generalizing P S U with
  | nil =>
    have hP : P = Finset.univ := by simpa using hfull
    simp only [List.map_nil,coloredAt,labeledHistory,anchorAt_one S T m hm,hP]
  | cons c cs ih =>
    have hcP : c ∉ P := hdis c (by simp)
    have hc : c ∉ cs := (List.nodup_cons.mp hcs).1
    have hcs' := (List.nodup_cons.mp hcs).2
    have hdis' : ∀ d ∈ cs, d ∉ insert c P := by
      intro d hd
      simp only [Finset.mem_insert,not_or]
      exact ⟨fun he => hc (he ▸ hd), hdis d (by simp [hd])⟩
    have hfull' : insert c P ∪ cs.toFinset = Finset.univ := by
      simpa only [List.toFinset_cons,Finset.insert_union,Finset.union_insert] using hfull
    simp only [List.map_cons,coloredAt,labeledHistory]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      have he : (fun x => (f x * ∏ d ∈ P, D d (S.pathAt (pos d) x)) * D c (S.pathAt (loc i) x)) =
          (fun x => f x * ∏ d ∈ insert c P, D d (S.pathAt (Function.update pos c (loc i) d) x)) := by
        funext x
        rw [Finset.prod_insert hcP,Function.update_self]
        have hp : (∏ d ∈ P, D d (S.pathAt (Function.update pos c (loc i) d) x)) =
            ∏ d ∈ P, D d (S.pathAt (pos d) x) := by
          apply Finset.prod_congr rfl
          intro d hd
          rw [Function.update_of_ne (fun h : d = c => hcP (h ▸ hd))]
        rw [hp]
        ring
      rw [he]
      exact ih hcs' (insert c P) hdis' hfull' S (U.erase i) loc
        (Function.update pos c (loc i)) f
    · apply Finset.sum_congr rfl
      intro v _
      apply congrArg (gamma S m v * ·)
      have hp : (fun i (x : Sample Ω (grow S v)) => S.pathAt (loc i) (oldSample S v x)) =
          (fun i => (grow S v).pathAt (oldLeaf S v (loc i))) := by
        funext i x
        exact (pathAt_oldLeaf S v (loc i) x).symm
      have he : (fun x => (f (oldSample S v x) * ∏ d ∈ P,
          D d (S.pathAt (pos d) (oldSample S v x))) * D c (newPath S v x)) =
          (fun x => f (oldSample S v x) * ∏ d ∈ insert c P,
            D d ((grow S v).pathAt
              (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v) d) x)) := by
        funext x
        rw [Finset.prod_insert hcP,Function.update_self,pathAt_newLeaf]
        have hh : (∏ d ∈ P, D d ((grow S v).pathAt
            (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v) d) x)) =
            ∏ d ∈ P, D d (S.pathAt (pos d) (oldSample S v x)) := by
          apply Finset.prod_congr rfl
          intro d hd
          rw [Function.update_of_ne (fun h : d = c => hcP (h ▸ hd)),pathAt_oldLeaf]
        rw [hh]
        ring
      rw [hp,he]
      exact ih hcs' (insert c P) hdis' hfull' (grow S v) U
        (fun i => oldLeaf S v (loc i))
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
        (fun x => f (oldSample S v x))

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.FiniteLaw
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]

lemma expect_pi_pair (P : (i : ι) → FiniteLaw (α i)) (i j : ι) (hij : j ≠ i)
    (f : α i → α j → ℝ) :
    (pi P).expect (fun x => f (x i) (x j)) =
      (P i).expect (fun x => (P j).expect (f x)) := by
  rw [expect_pi_split P i]
  apply expect_congr
  intro x
  simp only [Equiv.piSplitAt_symm_apply,dite_true,dite_eq_right hij]
  exact expect_pi_marginal (fun k : {k // k ≠ i} => P k) ⟨j,hij⟩ (f x)

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]

/-- Two kernel paths share exactly their first d coordinates; the definition
also includes the diagonal endpoint d=n. -/
noncomputable def pairExpect : (n : ℕ) → KernelTower Ω n → ℕ →
    (FinitePath Ω n → FinitePath Ω n → ℝ) → ℝ
  | 0, _, _, f => f () ()
  | n+1, T, 0, f => (law (n+1) T).expect (fun x => (law (n+1) T).expect (f x))
  | n+1, T, d+1, f => T.1.expect (fun x => pairExpect n (T.2 x) d (fun y z => f (x,y) (x,z)))

lemma pairExpect_zero (n : ℕ) (T : KernelTower Ω n)
    (f : FinitePath Ω n → FinitePath Ω n → ℝ) :
    pairExpect n T 0 f = (law n T).expect (fun x => (law n T).expect (f x)) := by
  cases n with
  | zero => simp [pairExpect,law_zero_expect]
  | succ n => rfl

lemma pairExpect_diagonal (n : ℕ) (T : KernelTower Ω n)
    (f : FinitePath Ω n → FinitePath Ω n → ℝ) :
    pairExpect n T n f = (law n T).expect (fun x => f x x) := by
  induction n with
  | zero => simp [pairExpect,law_zero_expect]
  | succ n ih => simp only [pairExpect,ih,law_succ_expect]

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

/-- The complete TWO-path joint law is determined by geometric splitting,
not by coincidences of configurations. Unused branches are marginalized. -/
theorem pair_marginal {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (a b : S.Leaf) (f : FinitePath Ω n → FinitePath Ω n → ℝ) :
    (S.sampleLaw T).expect (fun x => f (S.pathAt a x) (S.pathAt b x)) =
      KernelTower.pairExpect n T (splitDepth S a b) f := by
  induction S with
  | leaf =>
    change KernelTower.unitLaw.expect (fun _ => f () ()) = f () ()
    exact FiniteLaw.expect_const _ _
  | @node n k C ih =>
    rcases T with ⟨μ,K⟩
    rcases a with ⟨i,a⟩
    rcases b with ⟨j,b⟩
    by_cases hji : j = i
    · subst j
      rw [splitDepth_same_child]
      change (FiniteLaw.pi (fun t => μ.bind (fun z => sampleLaw (C t) (K z)))).expect
        (fun x => f ((x i).1,(C i).pathAt a (x i).2) ((x i).1,(C i).pathAt b (x i).2)) = _
      refine (FiniteLaw.expect_pi_marginal
        (fun t => μ.bind (fun z => sampleLaw (C t) (K z))) i
        (fun x => f (x.1,(C i).pathAt a x.2) (x.1,(C i).pathAt b x.2))).trans ?_
      erw [FiniteLaw.expect_bind]
      simp only [Nat.add_comm 1,KernelTower.pairExpect]
      apply FiniteLaw.expect_congr
      intro z
      exact ih i (K z) a b (fun x y => f (z,x) (z,y))
    · rw [splitDepth_diff_child C i j (Ne.symm hji)]
      change (FiniteLaw.pi (fun t => μ.bind (fun z => sampleLaw (C t) (K z)))).expect
        (fun x => f ((x i).1,(C i).pathAt a (x i).2) ((x j).1,(C j).pathAt b (x j).2)) = _
      refine (FiniteLaw.expect_pi_pair
        (fun t => μ.bind (fun z => sampleLaw (C t) (K z))) i j hji
        (fun x y => f (x.1,(C i).pathAt a x.2) (y.1,(C j).pathAt b y.2))).trans ?_
      erw [FiniteLaw.expect_bind]
      simp only [FiniteLaw.expect_bind,KernelTower.pairExpect]
      erw [KernelTower.law_succ_expect n (μ,K)]
      simp_rw [KernelTower.law_succ_expect n (μ,K)]
      apply FiniteLaw.expect_congr
      intro x
      rw [← leaf_marginal (C i) (K x) a]
      apply FiniteLaw.expect_congr
      intro y
      apply FiniteLaw.expect_congr
      intro z
      exact leaf_marginal (C j) (K z) b (fun w => f (x,(C i).pathAt a y) (z,w))

lemma pair_marginal_eq {n : ℕ} (S R : PrescribedTree n) (T : KernelTower Ω n)
    (a b : S.Leaf) (c d : R.Leaf) (h : splitDepth S a b = splitDepth R c d)
    (f : FinitePath Ω n → FinitePath Ω n → ℝ) :
    (S.sampleLaw T).expect (fun x => f (S.pathAt a x) (S.pathAt b x)) =
      (R.sampleLaw T).expect (fun x => f (R.pathAt c x) (R.pathAt d x)) := by
  rw [pair_marginal,pair_marginal,h]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
