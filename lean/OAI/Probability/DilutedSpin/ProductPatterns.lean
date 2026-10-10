import OAI.Probability.DilutedSpin.BranchingEvaluation

namespace OAI

section
namespace DilutedSpinGlass
open scoped BigOperators

lemma function_indicator_product {ι : Type} [Fintype ι] {β : ι → Type} [∀ i, DecidableEq (β i)]
    (f g : (i : ι) → β i) :
    (if f=g then (1:ℝ) else 0)=∏ i, if f i=g i then (1:ℝ) else 0 := by
  by_cases h : f=g
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm

namespace PrescribedTree
variable {Ω : Type} [Fintype Ω]
noncomputable def patternMass {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (V : FinitePath Ω n → Spin) (e : S.Leaf → Spin) : ℝ :=
  (sampleLaw S T).expect (fun z => if (fun a => V (pathAt S a z))=e then 1 else 0)

lemma patternMass_eq_branchingMean {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (V : FinitePath Ω n → Spin) (e : S.Leaf → Spin) :
    patternMass S T V e = branchingMean S T (fun a y => if V y=e a then 1 else 0) := by
  rw [branchingMean_eq_expect]
  unfold patternMass
  apply FiniteLaw.expect_congr
  intro z
  rw [branchingProduct_eq_prod]
  exact function_indicator_product (ι := S.Leaf) (fun a => V (pathAt S a z)) e

variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i, Fintype (α i)]

lemma patternMass_pi {n : ℕ} (S : PrescribedTree n) (T : (i : ι) → KernelTower (α i) n)
    (V : (i : ι) → FinitePath (α i) n → Spin) (e : ι → S.Leaf → Spin) :
    (sampleLaw S (KernelTower.pi n T)).expect (fun z =>
      if (fun i a => V i (FinitePath.proj n (pathAt S a z) i))=e then 1 else 0) =
      ∏ i, patternMass S (T i) (V i) (e i) := by
  have hid (z : Sample ((i : ι) → α i) S) :
      (if (fun i a => V i (FinitePath.proj n (pathAt S a z) i))=e then (1:ℝ) else 0) =
      branchingProduct S
        (fun a y => ∏ i, if V i (FinitePath.proj n y i)=e i a then (1:ℝ) else 0) z := by
    rw [function_indicator_product (ι := ι) (fun i a => V i (FinitePath.proj n (pathAt S a z) i)) e]
    simp_rw [function_indicator_product (ι := S.Leaf)]
    rw [branchingProduct_eq_prod]
    exact Finset.prod_comm
  simp_rw [hid]
  rw [← branchingMean_eq_expect]
  have hp := branchingMean_pi S T (fun i a y => if V i y=e i a then (1:ℝ) else 0)
  rw [hp]
  exact Finset.prod_congr rfl (fun i _ => (patternMass_eq_branchingMean S (T i) (V i) (e i)).symm)

lemma expect_pi_patterns {n : ℕ} (S : PrescribedTree n) (T : (i : ι) → KernelTower (α i) n)
    (V : (i : ι) → FinitePath (α i) n → Spin) (F : (ι → S.Leaf → Spin) → ℝ) :
    (sampleLaw S (KernelTower.pi n T)).expect
      (fun z => F (fun i a => V i (FinitePath.proj n (pathAt S a z) i))) =
      ∑ e : ι → S.Leaf → Spin, (∏ i, patternMass S (T i) (V i) (e i))*F e := by
  have hid (z : Sample ((i : ι) → α i) S) :
      F (fun i a => V i (FinitePath.proj n (pathAt S a z) i)) =
      ∑ e, (if (fun i a => V i (FinitePath.proj n (pathAt S a z) i))=e then (1:ℝ) else 0)*F e := by
    simp
  calc
    _ = (sampleLaw S (KernelTower.pi n T)).expect (fun z => ∑ e,
      (if (fun i a => V i (FinitePath.proj n (pathAt S a z) i))=e then (1:ℝ) else 0)*F e) :=
      FiniteLaw.expect_congr _ hid
    _ = _ := by simp only [FiniteLaw.expect_fintype_sum,FiniteLaw.expect_mul_right,patternMass_pi]

lemma treeMean_pi_patterns {n : ℕ} (S : PrescribedTree n) (T : (i : ι) → KernelTower (α i) n)
    (V : (i : ι) → FinitePath (α i) n → Spin) (f : (ι → Spin) → ℝ) :
    treeMean S (KernelTower.pi n T) (fun y => f (fun i => V i (FinitePath.proj n y i))) =
      ∑ e : ι → S.Leaf → Spin, (∏ i, patternMass S (T i) (V i) (e i))*(∏ a, f (fun i => e i a)) := by
  rw [treeMean_eq_expect]
  have hh := expect_pi_patterns S T V (fun e => ∏ a, f (fun i => e i a))
  rw [← hh]
  apply FiniteLaw.expect_congr
  intro z
  exact leafProduct_eq_prod S _ z

end PrescribedTree
end DilutedSpinGlass

end

end OAI
