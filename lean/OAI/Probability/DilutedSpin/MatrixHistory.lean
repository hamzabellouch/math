import OAI.Probability.DilutedSpin.ActualCharging
import OAI.Probability.DilutedSpin.ProfileHistory

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance matrixHistoryDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {Ω C ι : Type} [Fintype Ω] [Fintype C] [DecidableEq C] [DecidableEq ι] {n : ℕ}

/-- The constant-observable component of the analytic COMPLETE-matrix history.
It is the original old-erase/fresh-grow recursion, not the reference recursion. -/
noncomputable def matrixHistory (T : PrescribedTree n) (q : C → T.Leaf)
    (K : KernelTower Ω n) (m : Fin (n+1) → ℝ) (cs : List C)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) : ℝ :=
  labeledHistory m (fun R pos g => if ∀ a b,
    splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
    then (R.sampleLaw K).expect g else 0) cs S U loc pos f

/-- Once two assigned colors have the wrong split, no future legal extension
can repair it. This justifies enforcing the matrix constraints successively. -/
lemma matrixHistory_mismatch (T : PrescribedTree n) (q : C → T.Leaf)
    (K : KernelTower Ω n) (m : Fin (n+1) → ℝ) (cs : List C)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ)
    (a b : C) (ha : a ∉ cs) (hb : b ∉ cs)
    (he : splitDepth S (pos a) (pos b) ≠ splitDepth T (q a) (q b)) :
    matrixHistory T q K m cs S U loc pos f = 0 := by
  induction cs generalizing S U with
  | nil =>
    exact ite_eq_right (fun h => he (h a b))
  | cons c cs ih =>
    have hac : a ≠ c := fun h => ha (by simp [h])
    have hbc : b ≠ c := fun h => hb (by simp [h])
    have ha' : a ∉ cs := fun h => ha (by simp [h])
    have hb' : b ∉ cs := fun h => hb (by simp [h])
    change (∑ i ∈ U, matrixHistory T q K m cs S (U.erase i) loc
      (Function.update pos c (loc i)) f) +
      ∑ v : S.Internal, gamma S m v * matrixHistory T q K m cs (grow S v) U
        (fun i => oldLeaf S v (loc i))
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
        (fun x => f (oldSample S v x)) = 0
    have ho (i : ι) : matrixHistory T q K m cs S (U.erase i) loc
        (Function.update pos c (loc i)) f = 0 := by
      apply ih S (U.erase i) loc _ f ha' hb'
      simpa only [Function.update_of_ne hac,Function.update_of_ne hbc] using he
    have hfresh (v : S.Internal) : matrixHistory T q K m cs (grow S v) U
        (fun i => oldLeaf S v (loc i))
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
        (fun x => f (oldSample S v x)) = 0 := by
      apply ih (grow S v) U _ _ _ ha' hb'
      simpa only [Function.update_of_ne hac,Function.update_of_ne hbc,splitDepth_old_old] using he
    simp only [ho,hfresh,mul_zero,Finset.sum_const_zero,add_zero]

/-- Exact sequential enforcement of the full split matrix inside the
protected signed history. Impossible branches vanish, rather than being
silently dropped or replaced by a reference law. -/
theorem matrixHistory_step (T : PrescribedTree n) (q : C → T.Leaf)
    (K : KernelTower Ω n) (m : Fin (n+1) → ℝ) (c : C) (cs : List C)
    (P : Finset C) (hc : c ∉ P) (hdis : ∀ d ∈ cs, d ∉ insert c P)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    matrixHistory T q K m (c::cs) S U loc pos f =
    (∑ i ∈ U, if ∀ d ∈ P, splitDepth S (loc i) (pos d) = splitDepth T (q c) (q d)
      then matrixHistory T q K m cs S (U.erase i) loc (Function.update pos c (loc i)) f else 0) +
    ∑ v : S.Internal, if ∀ d ∈ P, freshSplitDepth S v (pos d) = splitDepth T (q c) (q d)
      then gamma S m v * matrixHistory T q K m cs (grow S v) U
        (fun i => oldLeaf S v (loc i))
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
        (fun x => f (oldSample S v x)) else 0 := by
  have hc' : c ∉ cs := fun h => hdis c h (Finset.mem_insert_self _ _)
  have hd' : ∀ d ∈ P, d ∉ cs := fun d hd h => hdis d h (Finset.mem_insert_of_mem hd)
  change (_ + _) = _
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    split_ifs with h
    · rfl
    · push Not at h
      obtain ⟨d,hd,he⟩ := h
      apply matrixHistory_mismatch T q K m cs S (U.erase i) loc _ f c d hc' (hd' d hd)
      simpa only [Function.update_self,Function.update_of_ne (fun e : d = c => hc (e ▸ hd))] using he
  · apply Finset.sum_congr rfl
    intro v _
    split_ifs with h
    · rfl
    · push Not at h
      obtain ⟨d,hd,he⟩ := h
      suffices hh : matrixHistory T q K m cs (grow S v) U
          (fun i => oldLeaf S v (loc i))
          (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
          (fun x => f (oldSample S v x)) = 0 by
        simpa only [matrixHistory,mul_zero] using congrArg (gamma S m v * ·) hh
      apply matrixHistory_mismatch T q K m cs (grow S v) U _ _ _ c d hc' (hd' d hd)
      simpa only [Function.update_self,Function.update_of_ne (fun e : d = c => hc (e ▸ hd)),
        splitDepth_new_old] using he

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance kappaRegularDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
noncomputable local instance kappaRegularLeafDecidableEq {n : ℕ} (S : PrescribedTree n) :
    DecidableEq S.Leaf := Classical.decEq _

lemma branchProduct_ne_zero {x y : ℝ} (hxy : x < y) (hy : 0 ≤ y) (k : ℕ) :
    branchProduct x y k ≠ 0 := by
  unfold branchProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  apply ne_of_lt
  have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
  have hmul := mul_nonneg hj hy
  nlinarith

theorem partialKappa_ne_zero {n : ℕ} (S : PrescribedTree n)
    (m : Fin (n+1) → ℝ) (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (P : Finset S.Leaf) :
    partialKappa S m P ≠ 0 := by
  induction S with
  | leaf => exact one_ne_zero
  | @node n k C ih =>
    apply mul_ne_zero
    · exact branchProduct_ne_zero (hm (by simp : (0 : Fin (n+1+1)) < 1)) (hp 1) _
    · exact Finset.prod_ne_zero_iff.mpr (fun i _ => ih i _
        (fun a b h => hm (Fin.succ_lt_succ_iff.mpr h)) (fun j => hp j.succ) _)

variable {n : ℕ} {C ι : Type} [Fintype C] [DecidableEq C] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The actual one-step protected extension total is the ratio of the two
unordered branching products. Complete split constraints, not a surrogate
probability mechanism, determine this coefficient. -/
theorem matrix_choice_kappa (T S : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Injective q) (P : Finset C) (hP : P.Nonempty)
    (c : C) (hc : c ∉ P) (pos : C → S.Leaf) (U : Finset ι) (loc : ι → S.Leaf)
    (hcover : HistoryCover S U loc P pos)
    (hsplit : ∀ a ∈ P, ∀ b ∈ P,
      splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (m : Fin (n+1) → ℝ) (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j)
    (hend : m (Fin.last n) = 1) :
    (∑ i ∈ U, if ∀ d ∈ P, splitDepth S (loc i) (pos d) = splitDepth T (q c) (q d)
      then (1:ℝ) else 0) +
    (∑ v : S.Internal, if ∀ d ∈ P, freshSplitDepth S v (pos d) = splitDepth T (q c) (q d)
      then gamma S m v else 0) =
    partialKappa T m ((insert c P).image q) / partialKappa T m (P.image q) := by
  classical
  obtain ⟨a,ha,hmax⟩ := Finset.exists_max_image P (fun a => splitDepth T (q c) (q a)) hP
  let r : P → S.Leaf := fun a => pos a
  let s : P → T.Leaf := fun a => q a
  have himage : Finset.univ.image s = P.image q := by
    ext x
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨b,hb⟩
      exact ⟨b,b.property,hb⟩
    · rintro ⟨b,hb,he⟩
      exact ⟨⟨b,hb⟩,he⟩
  have hqa : q c ≠ q a := fun h => hc (hq h ▸ ha)
  have hn : q c ∉ P.image q := by
    rintro h
    obtain ⟨d,hd,he⟩ := Finset.mem_image.mp h
    exact hc (hq he ▸ hd)
  have he := labeled_choice_total S T r s (q c) ⟨a,ha⟩
    (fun a b => hsplit a a.property b b.property) hqa (fun b => hmax b b.property) m hend
  have ho (b : S.Leaf) : labeledOldMatch S T r s (q c) b ↔
      ∀ d ∈ P, splitDepth S b (pos d) = splitDepth T (q c) (q d) := by
    simp only [labeledOldMatch,r,s,Subtype.forall]
  have hf (v : S.Internal) : labeledFreshMatch S T r s (q c) v ↔
      ∀ d ∈ P, freshSplitDepth S v (pos d) = splitDepth T (q c) (q d) := by
    simp only [labeledFreshMatch,r,s,Subtype.forall]
  simp_rw [ho,hf] at he
  have hav := hcover.sum_available
    (fun b => if ∀ d ∈ P, splitDepth S b (pos d) = splitDepth T (q c) (q d) then (1:ℝ) else 0)
    (by
      intro d hd
      apply ite_eq_right
      intro h
      have hh := h d hd
      rw [splitDepth_self] at hh
      exact hc (hq ((splitDepth_eq_height T (q c) (q d)).mp hh.symm) ▸ hd))
  rw [hav,he]
  have hk := partialKappa_insert T m (P.image q) (q a) (q c)
    (Finset.mem_image.mpr ⟨a,ha,rfl⟩) hn
    (by rintro t ht; obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ht; exact hmax d hd)
  rw [Finset.image_insert,hk]
  rw [mul_div_cancel_right₀ _ (partialKappa_ne_zero T m hm hp _)]
  simp only [himage,s]

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {L : ℕ}

/-- One prescribed pair constraint, retaining the COMPLETE old law. -/
noncomputable def pairHistory (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (d : ℕ)
    (E D : FinitePath Ω (L+1) → ℝ) (f : Sample Ω S → ℝ) : ℝ := by
  classical
  exact (∑ b ∈ Finset.univ.erase a,
    if splitDepth S a b = d then (S.sampleLaw T).expect
      (fun x => f x * (E (S.pathAt a x) * D (S.pathAt b x))) else 0) +
    ∑ v : S.Internal, if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then
      gamma S m v * ((grow S v).sampleLaw T).expect
        (fun x => f (oldSample S v x) *
          (E ((grow S v).pathAt (oldLeaf S v a) x) *
            D ((grow S v).pathAt (newLeaf S v) x))) else 0

lemma shapeHistory_one (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (d : ℕ)
    (E D : FinitePath Ω (L+1) → ℝ) (f : Sample Ω S → ℝ) :
    shapeHistory T m (fun M : Option (Fin 1) → Option (Fin 1) → ℕ =>
        if M none (some 0) = d then 1 else 0)
      (fun c => match c with | none => E | some _ => D) S a f =
      pairHistory T m S a d E D f := by
  classical
  simp only [shapeHistory,List.ofFn_succ,List.ofFn_zero,List.reverse_cons,List.reverse_nil,
    List.nil_append,labeledHistory]
  unfold pairHistory
  congr 1
  · apply Finset.sum_congr rfl
    intro b hb
    simp only [Fintype.prod_option,Fin.prod_univ_one,Function.update_of_ne (by simp : (none : Option (Fin 1)) ≠ some 0),Function.update_self,id_eq]
    split_ifs <;> simp
  · apply Finset.sum_congr rfl
    intro v _
    simp only [Fintype.prod_option,Fin.prod_univ_one,Function.update_of_ne (by simp : (none : Option (Fin 1)) ≠ some 0),Function.update_self]
    split_ifs <;> simp

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
