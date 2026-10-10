import OAI.Probability.DilutedSpin.HistorySelector
import OAI.Probability.DilutedSpin.MatrixPair

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance matrixConstantDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
variable {Ω C ι : Type} [Fintype Ω] [DecidableEq C] [DecidableEq ι] {n : ℕ}

omit [Fintype Ω] in
lemma labeledHistory_congr_one (m : Fin (n+1) → ℝ)
    (V W : (S : PrescribedTree n) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (h : ∀ S pos, V S pos (fun _ => 1) = W S pos (fun _ => 1))
    (cs : List C) (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf) (pos : C → S.Leaf) :
    labeledHistory m V cs S U loc pos (fun _ => 1) =
      labeledHistory m W cs S U loc pos (fun _ => 1) := by
  induction cs generalizing S U with
  | nil => exact h S pos
  | cons c cs ih => simp only [labeledHistory,ih]

variable [Fintype C]
/-- The anchor-alone complete matrix history is its exact signed kappa times
the single-target marginal observable. In fact the same identity holds with
any unused old tree, as long as its test is one. -/
theorem weightedMatrixHistory_one (T : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Bijective q) (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
    (a : C) (cs : List C) (hcs : cs.Nodup) (hdis : ∀ c ∈ cs, c ≠ a)
    (hfull : ({a} : Finset C) ∪ cs.toFinset = Finset.univ)
    (S : PrescribedTree n) (x : S.Leaf) (A : (C → FinitePath Ω n) → ℝ) :
    weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect (fun z => g z*A (fun c => D.pathAt (pos c) z)))
      m cs S (Finset.univ.erase x) id (fun _ => x) (fun _ => 1) =
    partialKappa T m (Finset.univ.image q) *
      (T.sampleLaw K).expect (fun z => A (fun c => T.pathAt (q c) z)) := by
  let B := (T.sampleLaw K).expect (fun z => A (fun c => T.pathAt (q c) z))
  have he := labeledHistory_congr_one m
    (fun D pos g => if ∀ a b, splitDepth D (pos a) (pos b) = splitDepth T (q a) (q b)
      then (D.sampleLaw K).expect (fun z => g z*A (fun c => D.pathAt (pos c) z)) else 0)
    (fun D pos g => B * (if ∀ a b, splitDepth D (pos a) (pos b) = splitDepth T (q a) (q b)
      then (D.sampleLaw K).expect g else 0))
    (by
      intro D pos
      split_ifs with h
      · simp only [one_mul,FiniteLaw.expect_const,mul_one]
        exact matrix_paths_expect T D q hq.2 pos h K A
      · exact (mul_zero B).symm)
    cs S (Finset.univ.erase x) id (fun _ => x)
  unfold weightedMatrixHistory
  rw [he,labeledHistory_mul_left]
  rw [show labeledHistory m (fun D pos g => if ∀ a b, splitDepth D (pos a) (pos b) = splitDepth T (q a) (q b)
      then (D.sampleLaw K).expect g else 0) cs S (Finset.univ.erase x) id (fun _ => x) (fun _ => 1) =
      matrixHistory T q K m cs S (Finset.univ.erase x) id (fun _ => x) (fun _ => 1) from rfl]
  rw [matrixHistory_normalization T q hq.1 K m hm hp hend cs hcs {a}
    (Finset.singleton_nonempty _) (by simpa only [Finset.mem_singleton] using hdis) hfull
    S (Finset.univ.erase x) id (fun _ => x) (singleton_history_cover S x a)
    (by intro b hb d hd; have hb' := Finset.mem_singleton.mp hb; have hd' := Finset.mem_singleton.mp hd
        subst b; subst d; simp only [splitDepth_self]) (fun _ => 1)]
  simp only [Finset.image_singleton,partialKappa_singleton,div_one,FiniteLaw.expect_const,mul_one]
  exact mul_comm _ _

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance partialKappaPairDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
variable {n : ℕ}

lemma partialKappa_pair (T : PrescribedTree n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
    (a b : T.Leaf) (hab : a ≠ b) :
    partialKappa T m {b,a} =
      m ⟨splitDepth T a b,by have := splitDepth_lt_of_ne T a b hab; omega⟩-
      m ⟨splitDepth T a b+1,by have := splitDepth_lt_of_ne T a b hab; omega⟩ := by
  classical
  have h := matrix_choice_kappa T T id Function.injective_id {a} (Finset.singleton_nonempty _)
    b (by simpa using hab.symm) (fun _ => a) (Finset.univ.erase a) id
    (singleton_history_cover T a a)
    (by intro c hc d hd; have hc' := Finset.mem_singleton.mp hc; have hd' := Finset.mem_singleton.mp hd
        subst c; subst d; rfl) m hm hp hend
  simp only [Finset.mem_singleton,forall_eq,id_eq,Finset.image_id,partialKappa_singleton,div_one] at h
  simp_rw [splitDepth_symm T _ a] at h
  have he (v : T.Internal) : freshSplitDepth T v a = splitDepth (grow T v) (oldLeaf T v a) (newLeaf T v) := by
    rw [splitDepth_symm,splitDepth_new_old]
  simp_rw [he] at h
  rw [pair_univ_erase T a (splitDepth T a b) (splitDepth_lt_of_ne T a b hab),
    pair_choice_total T a (splitDepth T a b) (splitDepth_lt_of_ne T a b hab) m hend] at h
  exact h.symm

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
