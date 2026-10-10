import OAI.Probability.DilutedSpin.ProductTower

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

noncomputable def branchingMean : {n : ℕ} → (S : PrescribedTree n) →
    KernelTower Ω n → (S.Leaf → FinitePath Ω n → ℝ) → ℝ
  | 0,.leaf,_,F => F () ()
  | _+1,.node _ C,T,F => ∏ j, T.1.expect (fun a =>
      branchingMean (C j) (T.2 a) (fun b y => F ⟨j,b⟩ (a,y)))

def branchingProduct : {n : ℕ} → (S : PrescribedTree n) →
    (S.Leaf → FinitePath Ω n → ℝ) → Sample Ω S → ℝ
  | 0,.leaf,F,_ => F () ()
  | _+1,.node _ C,F,z => ∏ j, branchingProduct (C j)
      (fun b y => F ⟨j,b⟩ ((z j).1,y)) (z j).2

omit [Fintype Ω] in
lemma branchingProduct_eq_prod {n : ℕ} (S : PrescribedTree n)
    (F : S.Leaf → FinitePath Ω n → ℝ) (z : Sample Ω S) :
    branchingProduct S F z=∏ a, F a (pathAt S a z) := by
  induction S with
  | leaf => change F () ()=∏ a : Unit, F a (); simp
  | @node _ k C ih =>
    change (∏ j, branchingProduct (C j) (fun b y => F ⟨j,b⟩ ((z j).1,y)) (z j).2)=_
    change _=(∏ a : (j : Fin k) × (C j).Leaf, F a (pathAt (.node k C) a z))
    rw [Fintype.prod_sigma]
    exact Finset.prod_congr rfl (fun j _ => ih j _ (z j).2)

lemma branchingMean_eq_expect {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (F : S.Leaf → FinitePath Ω n → ℝ) :
    branchingMean S T F=(sampleLaw S T).expect (branchingProduct S F) := by
  induction S with
  | leaf => exact ((sampleLaw .leaf T).expect_const (F () ())).symm
  | @node n k C ih =>
    change FiniteLaw Ω × (Ω → KernelTower Ω n) at T
    rcases T with ⟨P,Q⟩
    change (((j : Fin k) × (C j).Leaf) → (Ω × FinitePath Ω n) → ℝ) at F
    change (∏ i, P.expect (fun a => branchingMean (C i) (Q a) (fun b y => F ⟨i,b⟩ (a,y)))) =
      (FiniteLaw.pi (fun i : Fin k => P.bind (fun a => sampleLaw (C i) (Q a)))).expect
        (fun z => ∏ i, branchingProduct (C i) (fun b y => F ⟨i,b⟩ ((z i).1,y)) (z i).2)
    rw [FiniteLaw.expect_pi_product (fun i : Fin k => P.bind (fun a => sampleLaw (C i) (Q a)))
      (fun i (z : Ω × Sample Ω (C i)) => branchingProduct (C i) (fun b y => F ⟨i,b⟩ (z.1,y)) z.2)]
    apply Finset.prod_congr rfl
    intro i _
    rw [FiniteLaw.expect_bind]
    apply FiniteLaw.expect_congr
    intro a
    exact ih i (Q a) _

variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i, Fintype (α i)]
lemma branchingMean_pi {n : ℕ} (S : PrescribedTree n) (T : (i : ι) → KernelTower (α i) n)
    (F : (i : ι) → S.Leaf → FinitePath (α i) n → ℝ) :
    branchingMean S (KernelTower.pi n T)
      (fun a y => ∏ i, F i a (FinitePath.proj n y i)) =
      ∏ i, branchingMean S (T i) (F i) := by
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    change ((i : ι) → FiniteLaw (α i) × (α i → KernelTower (α i) n)) at T
    change ((i : ι) → ((j : Fin k) × (C j).Leaf) → (α i × FinitePath (α i) n) → ℝ) at F
    change (∏ j, (FiniteLaw.pi (fun i => (T i).1)).expect
      (fun a => branchingMean (C j) (KernelTower.pi n (fun i => (T i).2 (a i)))
        (fun b y => ∏ i, F i ⟨j,b⟩ (a i,FinitePath.proj n y i)))) =
      ∏ i, ∏ j, (T i).1.expect (fun a => branchingMean (C j) ((T i).2 a) (fun b y => F i ⟨j,b⟩ (a,y)))
    have he (j) (a : (i : ι) → α i) := ih j
      (fun i => (T i).2 (a i)) (fun i b y => F i ⟨j,b⟩ (a i,y))
    simp_rw [he]
    have hp (j) := FiniteLaw.expect_pi_product (fun i => (T i).1)
      (fun i a => branchingMean (C j) ((T i).2 a) (fun b y => F i ⟨j,b⟩ (a,y)))
    simp_rw [hp]
    exact Finset.prod_comm

end DilutedSpinGlass.PrescribedTree

end

end OAI
