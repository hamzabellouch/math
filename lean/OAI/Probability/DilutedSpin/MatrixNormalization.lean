import OAI.Probability.DilutedSpin.MatrixHistory
import OAI.Probability.DilutedSpin.TreeMarkLaw

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance matrixNormalizationDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω C ι : Type} [Fintype Ω] [Fintype C] [DecidableEq C] [DecidableEq ι] {n : ℕ}

omit [Fintype C] in
lemma splitOn_pick_old (T S : PrescribedTree n) (q : C → T.Leaf)
    (P : Finset C) (c : C) (hc : c ∉ P) (pos : C → S.Leaf) (x : S.Leaf)
    (hsplit : ∀ a ∈ P, ∀ b ∈ P, splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (hx : ∀ a ∈ P, splitDepth S x (pos a) = splitDepth T (q c) (q a)) :
    ∀ a ∈ insert c P, ∀ b ∈ insert c P,
      splitDepth S (Function.update pos c x a) (Function.update pos c x b) =
        splitDepth T (q a) (q b) := by
  intro a ha b hb
  rcases Finset.mem_insert.mp ha with hac | ha <;> rcases Finset.mem_insert.mp hb with hbc | hb
  · subst a; subst b
    simp only [splitDepth_self]
  · subst a
    simpa only [Function.update_self,Function.update_of_ne (fun he : b = c => hc (he ▸ hb))] using hx b hb
  · subst b
    rw [splitDepth_symm,splitDepth_symm T (q a)]
    simpa only [Function.update_self,Function.update_of_ne (fun he : a = c => hc (he ▸ ha))] using hx a ha
  · simpa only [Function.update_of_ne (fun he : a = c => hc (he ▸ ha)),
      Function.update_of_ne (fun he : b = c => hc (he ▸ hb))] using hsplit a ha b hb

omit [Fintype C] in
lemma splitOn_pick_fresh (T S : PrescribedTree n) (q : C → T.Leaf)
    (P : Finset C) (c : C) (hc : c ∉ P) (pos : C → S.Leaf) (v : S.Internal)
    (hsplit : ∀ a ∈ P, ∀ b ∈ P, splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (hv : ∀ a ∈ P, freshSplitDepth S v (pos a) = splitDepth T (q c) (q a)) :
    ∀ a ∈ insert c P, ∀ b ∈ insert c P,
      splitDepth (grow S v)
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v) a)
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v) b) =
        splitDepth T (q a) (q b) := by
  intro a ha b hb
  rcases Finset.mem_insert.mp ha with hac | ha <;> rcases Finset.mem_insert.mp hb with hbc | hb
  · subst a; subst b
    simp only [splitDepth_self]
  · subst a
    simpa only [Function.update_self,Function.update_of_ne (fun he : b = c => hc (he ▸ hb)),
      splitDepth_new_old] using hv b hb
  · subst b
    rw [splitDepth_symm,splitDepth_symm T (q a)]
    simpa only [Function.update_self,Function.update_of_ne (fun he : a = c => hc (he ▸ ha)),
      splitDepth_new_old] using hv a ha
  · simpa only [Function.update_of_ne (fun he : a = c => hc (he ▸ ha)),
      Function.update_of_ne (fun he : b = c => hc (he ▸ hb)),splitDepth_old_old] using hsplit a ha b hb

/-- Exact normalization of the ACTUAL complete-matrix protected history,
retaining an arbitrary old test. This bridges the analytic history to the
unordered kappa product, without assuming a reference-history identity. -/
theorem matrixHistory_normalization (T : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Injective q) (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
    (cs : List C) (hcs : cs.Nodup) (P : Finset C) (hP : P.Nonempty)
    (hdis : ∀ c ∈ cs, c ∉ P) (hfull : P ∪ cs.toFinset = Finset.univ)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf) (pos : C → S.Leaf)
    (hcover : HistoryCover S U loc P pos)
    (hsplit : ∀ a ∈ P, ∀ b ∈ P,
      splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (f : Sample Ω S → ℝ) :
    matrixHistory T q K m cs S U loc pos f =
      (partialKappa T m (Finset.univ.image q) / partialKappa T m (P.image q)) *
        (S.sampleLaw K).expect f := by
  classical
  induction cs generalizing P S U with
  | nil =>
    have he : P = Finset.univ := by simpa using hfull
    have hall : ∀ a b, splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b) := by
      intro a b
      apply hsplit a (by simp [he]) b (by simp [he])
    simp only [matrixHistory,labeledHistory,ite_eq_left hall,he,
      div_self (partialKappa_ne_zero T m hm hp _),one_mul]
  | cons c cs ih =>
    have hc : c ∉ P := hdis c (by simp)
    have hcs' := (List.nodup_cons.mp hcs).2
    have hdis' : ∀ d ∈ cs, d ∉ insert c P := by
      intro d hd hh
      rcases Finset.mem_insert.mp hh with rfl | hh
      · exact (List.nodup_cons.mp hcs).1 hd
      · exact hdis d (by simp [hd]) hh
    have hfull' : insert c P ∪ cs.toFinset = Finset.univ := by
      simpa only [List.toFinset_cons,Finset.insert_union,Finset.union_insert] using hfull
    let A := partialKappa T m (Finset.univ.image q) / partialKappa T m ((insert c P).image q)
    have ho (i : ι) (hi : i ∈ U) :
        (if ∀ d ∈ P, splitDepth S (loc i) (pos d) = splitDepth T (q c) (q d)
          then matrixHistory T q K m cs S (U.erase i) loc (Function.update pos c (loc i)) f else 0) =
        (if ∀ d ∈ P, splitDepth S (loc i) (pos d) = splitDepth T (q c) (q d) then (1:ℝ) else 0) *
          (A * (S.sampleLaw K).expect f) := by
      split_ifs with hx
      · rw [ih hcs' (insert c P) (Finset.insert_nonempty _ _) hdis' hfull' S (U.erase i) loc _
          (hcover.pick_old hc hi) (splitOn_pick_old T S q P c hc pos (loc i) hsplit hx) f]
        exact (one_mul _).symm
      · simp only [zero_mul]
    have hfresh (v : S.Internal) :
        (if ∀ d ∈ P, freshSplitDepth S v (pos d) = splitDepth T (q c) (q d)
          then gamma S m v * matrixHistory T q K m cs (grow S v) U
            (fun i => oldLeaf S v (loc i))
            (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
            (fun x => f (oldSample S v x)) else 0) =
        (if ∀ d ∈ P, freshSplitDepth S v (pos d) = splitDepth T (q c) (q d)
          then gamma S m v else 0) * (A * (S.sampleLaw K).expect f) := by
      split_ifs with hv
      · rw [ih hcs' (insert c P) (Finset.insert_nonempty _ _) hdis' hfull' (grow S v) U _ _
          (hcover.pick_fresh hc v) (splitOn_pick_fresh T S q P c hc pos v hsplit hv) _,grow_projectivity]
      · simp only [zero_mul]
    rw [matrixHistory_step T q K m c cs P hc hdis']
    have hh : (∑ i ∈ U, if ∀ d ∈ P, splitDepth S (loc i) (pos d) = splitDepth T (q c) (q d)
          then matrixHistory T q K m cs S (U.erase i) loc (Function.update pos c (loc i)) f else 0) =
        ∑ i ∈ U, (if ∀ d ∈ P, splitDepth S (loc i) (pos d) = splitDepth T (q c) (q d)
          then (1:ℝ) else 0) * (A * (S.sampleLaw K).expect f) := Finset.sum_congr rfl ho
    rw [hh]
    simp_rw [hfresh]
    rw [← Finset.sum_mul,← Finset.sum_mul,← add_mul,
      matrix_choice_kappa T S q hq P hP c hc pos U loc hcover hsplit m hm hp hend]
    dsimp only [A]
    rw [← mul_assoc, div_mul_div_cancel₀'
      (partialKappa_ne_zero T m hm hp ((insert c P).image q))]

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance weightedMatrixHistoryDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω C ι : Type} [Fintype Ω] [Fintype C] [DecidableEq C] [DecidableEq ι] {n : ℕ}

/-- A complete-matrix history with a general terminal observable. The full
ordered old-erase/fresh-grow history remains literal. -/
noncomputable def weightedMatrixHistory (T : PrescribedTree n) (q : C → T.Leaf)
    (V : (R : PrescribedTree n) → (C → R.Leaf) → (Sample Ω R → ℝ) → ℝ)
    (m : Fin (n+1) → ℝ) (cs : List C)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) : ℝ :=
  labeledHistory m (fun R pos g => if ∀ a b,
    splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
    then V R pos g else 0) cs S U loc pos f

omit [Fintype Ω] in
/-- Once two assigned colors have the wrong split, no future legal extension
can repair it. This justifies enforcing the matrix constraints successively. -/
lemma weightedMatrixHistory_mismatch (T : PrescribedTree n) (q : C → T.Leaf)
    (V : (R : PrescribedTree n) → (C → R.Leaf) → (Sample Ω R → ℝ) → ℝ) (m : Fin (n+1) → ℝ) (cs : List C)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ)
    (a b : C) (ha : a ∉ cs) (hb : b ∉ cs)
    (he : splitDepth S (pos a) (pos b) ≠ splitDepth T (q a) (q b)) :
    weightedMatrixHistory T q V m cs S U loc pos f = 0 := by
  induction cs generalizing S U with
  | nil =>
    exact ite_eq_right (fun h => he (h a b))
  | cons c cs ih =>
    have hac : a ≠ c := fun h => ha (by simp [h])
    have hbc : b ≠ c := fun h => hb (by simp [h])
    have ha' : a ∉ cs := fun h => ha (by simp [h])
    have hb' : b ∉ cs := fun h => hb (by simp [h])
    change (∑ i ∈ U, weightedMatrixHistory T q V m cs S (U.erase i) loc
      (Function.update pos c (loc i)) f) +
      ∑ v : S.Internal, gamma S m v * weightedMatrixHistory T q V m cs (grow S v) U
        (fun i => oldLeaf S v (loc i))
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
        (fun x => f (oldSample S v x)) = 0
    have ho (i : ι) : weightedMatrixHistory T q V m cs S (U.erase i) loc
        (Function.update pos c (loc i)) f = 0 := by
      apply ih S (U.erase i) loc _ f ha' hb'
      simpa only [Function.update_of_ne hac,Function.update_of_ne hbc] using he
    have hfresh (v : S.Internal) : weightedMatrixHistory T q V m cs (grow S v) U
        (fun i => oldLeaf S v (loc i))
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
        (fun x => f (oldSample S v x)) = 0 := by
      apply ih (grow S v) U _ _ _ ha' hb'
      simpa only [Function.update_of_ne hac,Function.update_of_ne hbc,splitDepth_old_old] using he
    simp only [ho,hfresh,mul_zero,Finset.sum_const_zero,add_zero]

omit [Fintype Ω] in
/-- Exact sequential enforcement of the full split matrix inside the
protected signed history. Impossible branches vanish, rather than being
silently dropped or replaced by a reference law. -/
theorem weightedMatrixHistory_step (T : PrescribedTree n) (q : C → T.Leaf)
    (V : (R : PrescribedTree n) → (C → R.Leaf) → (Sample Ω R → ℝ) → ℝ) (m : Fin (n+1) → ℝ) (c : C) (cs : List C)
    (P : Finset C) (hc : c ∉ P) (hdis : ∀ d ∈ cs, d ∉ insert c P)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    weightedMatrixHistory T q V m (c::cs) S U loc pos f =
    (∑ i ∈ U, if ∀ d ∈ P, splitDepth S (loc i) (pos d) = splitDepth T (q c) (q d)
      then weightedMatrixHistory T q V m cs S (U.erase i) loc (Function.update pos c (loc i)) f else 0) +
    ∑ v : S.Internal, if ∀ d ∈ P, freshSplitDepth S v (pos d) = splitDepth T (q c) (q d)
      then gamma S m v * weightedMatrixHistory T q V m cs (grow S v) U
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
      apply weightedMatrixHistory_mismatch T q V m cs S (U.erase i) loc _ f c d hc' (hd' d hd)
      simpa only [Function.update_self,Function.update_of_ne (fun e : d = c => hc (e ▸ hd))] using he
  · apply Finset.sum_congr rfl
    intro v _
    split_ifs with h
    · rfl
    · push Not at h
      obtain ⟨d,hd,he⟩ := h
      suffices hh : weightedMatrixHistory T q V m cs (grow S v) U
          (fun i => oldLeaf S v (loc i))
          (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
          (fun x => f (oldSample S v x)) = 0 by
        simpa only [weightedMatrixHistory,mul_zero] using congrArg (gamma S m v * ·) hh
      apply weightedMatrixHistory_mismatch T q V m cs (grow S v) U _ _ _ c d hc' (hd' d hd)
      simpa only [Function.update_self,Function.update_of_ne (fun e : d = c => hc (e ▸ hd)),
        splitDepth_new_old] using he

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
