import OAI.Probability.DilutedSpin.MatrixNormalization

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C ι : Type} [Fintype Ω] [DecidableEq C] [DecidableEq ι] {n : ℕ}

omit [Fintype Ω] in
/-- A function of protected paths is transported jointly with the full old
test through EVERY fresh extension. This is an identity of signed histories. -/
theorem labeledHistory_protected_function (m : Fin (n+1) → ℝ)
    (V : (S : PrescribedTree n) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (P : Finset C) (G : (C → FinitePath Ω n) → ℝ)
    (hG : ∀ x y, (∀ c ∈ P, x c = y c) → G x = G y)
    (cs : List C) (hdis : ∀ c ∈ cs, c ∉ P)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    labeledHistory m (fun R pos g => V R pos (fun x => g x * G (fun c => R.pathAt (pos c) x)))
      cs S U loc pos f =
    labeledHistory m V cs S U loc pos (fun x => f x*G (fun c => S.pathAt (pos c) x)) := by
  induction cs generalizing S U with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ∉ P := hdis c (by simp)
    have hdis' : ∀ d ∈ cs, d ∉ P := fun d hd => hdis d (by simp [hd])
    simp only [labeledHistory]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [ih hdis']
      congr 1
      funext x
      congr 1
      apply hG
      intro d hd
      rw [Function.update_of_ne (fun h : d = c => hc (h ▸ hd))]
    · apply Finset.sum_congr rfl
      intro v _
      congr 1
      rw [ih hdis']
      congr 1
      funext x
      congr 1
      apply hG
      intro d hd
      rw [Function.update_of_ne (fun h : d = c => hc (h ▸ hd)),pathAt_oldLeaf]

variable [Fintype C]
noncomputable local instance historyRetainedPropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

/-- Complete-matrix normalization WITH any observable of the already assigned
paths. Its joint dependence on the old test and the original samples is kept. -/
theorem matrixHistory_retained (T : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Injective q) (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
    (cs : List C) (hcs : cs.Nodup) (P : Finset C) (hP : P.Nonempty)
    (hdis : ∀ c ∈ cs, c ∉ P) (hfull : P ∪ cs.toFinset = Finset.univ)
    (G : (C → FinitePath Ω n) → ℝ)
    (hG : ∀ x y, (∀ c ∈ P, x c = y c) → G x = G y)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf) (pos : C → S.Leaf)
    (hcover : HistoryCover S U loc P pos)
    (hsplit : ∀ a ∈ P, ∀ b ∈ P,
      splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (f : Sample Ω S → ℝ) :
    labeledHistory m (fun R pos g => if ∀ a b,
      splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
      then (R.sampleLaw K).expect (fun x => g x*G (fun c => R.pathAt (pos c) x)) else 0)
      cs S U loc pos f =
    (partialKappa T m (Finset.univ.image q) / partialKappa T m (P.image q)) *
      (S.sampleLaw K).expect (fun x => f x*G (fun c => S.pathAt (pos c) x)) := by
  rw [labeledHistory_protected_function m
    (fun R pos g => if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
      then (R.sampleLaw K).expect g else 0) P G hG cs hdis]
  exact matrixHistory_normalization T q hq K m hm hp hend cs hcs P hP hdis hfull
    S U loc pos hcover hsplit _

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
