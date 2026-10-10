import OAI.Probability.DilutedSpin.FullRegularSelection

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance markerHistoryDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω C ι : Type} [Fintype Ω] [Fintype C] [DecidableEq C] [DecidableEq ι] {n : ℕ}

omit [Fintype Ω] in
/-- If every requested new color has a different split from a protected
marker than every available old leaf, the old choices vanish in the literal
signed history. Fresh extensions retain this exclusion. -/
theorem weightedMatrixHistory_drop_available (T : PrescribedTree n) (q : C → T.Leaf)
    (V : (R : PrescribedTree n) → (C → R.Leaf) → (Sample Ω R → ℝ) → ℝ)
    (m : Fin (n+1) → ℝ) (a : C) (cs : List C) (hcs : cs.Nodup) (ha : a ∉ cs)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf) (pos : C → S.Leaf)
    (hsep : ∀ c ∈ cs, ∀ i ∈ U,
      splitDepth S (loc i) (pos a) ≠ splitDepth T (q c) (q a))
    (f : Sample Ω S → ℝ) :
    weightedMatrixHistory T q V m cs S U loc pos f =
      weightedMatrixHistory T q V m cs S ∅ loc pos f := by
  induction cs generalizing S U with
  | nil => rfl
  | cons c cs ih =>
    have hnd := List.nodup_cons.mp hcs
    have hac : a ≠ c := fun h => ha (by simp [h])
    have ha' : a ∉ cs := fun h => ha (by simp [h])
    change (∑ i ∈ U, weightedMatrixHistory T q V m cs S (U.erase i) loc
      (Function.update pos c (loc i)) f) +
      ∑ v : S.Internal, gamma S m v * weightedMatrixHistory T q V m cs (grow S v) U
        (fun i => oldLeaf S v (loc i))
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
        (fun x => f (oldSample S v x)) = _
    have ho : (∑ i ∈ U, weightedMatrixHistory T q V m cs S (U.erase i) loc
      (Function.update pos c (loc i)) f) = 0 := by
      apply Finset.sum_eq_zero
      intro index hindex
      apply weightedMatrixHistory_mismatch T q V m cs S (U.erase index) loc _ f c a hnd.1 ha'
      simpa only [Function.update_self,Function.update_of_ne hac] using
        hsep c (by simp) index hindex
    rw [ho,zero_add]
    change _ = (∑ i ∈ (∅ : Finset ι), _) + _
    simp only [Finset.sum_empty,zero_add]
    apply Finset.sum_congr rfl
    intro v _
    congr 1
    apply ih hnd.2 ha'
    intro d hd i hi
    simpa only [Function.update_of_ne hac,splitDepth_old_old] using hsep d (by simp [hd]) i hi

/-- General complete-matrix normalization with a whole protected old tree.
All paths, including those used by an old observable, are jointly retained. -/
theorem weightedMatrixHistory_protected_one (T : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Bijective q) (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n)=1)
    (cs : List C) (hcs : cs.Nodup) (P : Finset C) (hP : P.Nonempty)
    (hdis : ∀ c ∈ cs, c ∉ P) (hfull : P ∪ cs.toFinset=Finset.univ)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf) (pos : C → S.Leaf)
    (hcover : HistoryCover S U loc P pos)
    (hsplit : ∀ a ∈ P, ∀ b ∈ P,
      splitDepth S (pos a) (pos b)=splitDepth T (q a) (q b))
    (A : (C → FinitePath Ω n) → ℝ) :
    weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect (fun z => g z*A (fun c => D.pathAt (pos c) z)))
      m cs S U loc pos (fun _ => 1) =
      (partialKappa T m (Finset.univ.image q)/partialKappa T m (P.image q)) *
        (T.sampleLaw K).expect (fun z => A (fun c => T.pathAt (q c) z)) := by
  let B := (T.sampleLaw K).expect (fun z => A (fun c => T.pathAt (q c) z))
  have he := labeledHistory_congr_one m
    (fun D pos g => if ∀ a b, splitDepth D (pos a) (pos b)=splitDepth T (q a) (q b)
      then (D.sampleLaw K).expect (fun z => g z*A (fun c => D.pathAt (pos c) z)) else 0)
    (fun D pos g => B*(if ∀ a b, splitDepth D (pos a) (pos b)=splitDepth T (q a) (q b)
      then (D.sampleLaw K).expect g else 0))
    (by
      intro D pos
      split_ifs with h
      · simp only [one_mul,FiniteLaw.expect_const,mul_one]
        exact matrix_paths_expect T D q hq.2 pos h K A
      · exact (mul_zero B).symm)
    cs S U loc pos
  unfold weightedMatrixHistory
  rw [he,labeledHistory_mul_left]
  change B * matrixHistory T q K m cs S U loc pos (fun _ => 1) = _
  rw [matrixHistory_normalization T q hq.1 K m hm hp hend cs hcs P hP hdis hfull
    S U loc pos hcover hsplit (fun _ => 1)]
  simp only [FiniteLaw.expect_const,mul_one]
  exact mul_comm _ _

omit [Fintype Ω] [Fintype C] in
/-- Split relations among colors which are never reassigned survive all
old and fresh extensions. This transports an exact terminal identity through
the actual signed expansion. -/
theorem labeledHistory_congr_protected_split (m : Fin (n+1) → ℝ)
    (V W : (R : PrescribedTree n) → (C → R.Leaf) → (Sample Ω R → ℝ) → ℝ)
    (P : Finset C) (B : C → C → ℕ)
    (h : ∀ R pos, (∀ a ∈ P, ∀ b ∈ P, splitDepth R (pos a) (pos b)=B a b) →
      ∀ g, V R pos g=W R pos g)
    (cs : List C) (hdis : ∀ c ∈ cs, c ∉ P)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf) (pos : C → S.Leaf)
    (hsplit : ∀ a ∈ P, ∀ b ∈ P, splitDepth S (pos a) (pos b)=B a b)
    (f : Sample Ω S → ℝ) :
    labeledHistory m V cs S U loc pos f=labeledHistory m W cs S U loc pos f := by
  induction cs generalizing S U with
  | nil => exact h S pos hsplit f
  | cons c cs ih =>
    have hc : c ∉ P := hdis c (by simp)
    have hdis' : ∀ d ∈ cs, d ∉ P := fun d hd => hdis d (by simp [hd])
    simp only [labeledHistory]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      apply ih hdis'
      intro a ha b hb
      simpa only [Function.update_of_ne (fun e : a=c => hc (e ▸ ha)),
        Function.update_of_ne (fun e : b=c => hc (e ▸ hb))] using hsplit a ha b hb
    · apply Finset.sum_congr rfl
      intro v _
      congr 1
      apply ih hdis'
      intro a ha b hb
      simpa only [Function.update_of_ne (fun e : a=c => hc (e ▸ ha)),
        Function.update_of_ne (fun e : b=c => hc (e ▸ hb)),splitDepth_old_old] using hsplit a ha b hb

end DilutedSpinGlass.PrescribedTree

end

end OAI
