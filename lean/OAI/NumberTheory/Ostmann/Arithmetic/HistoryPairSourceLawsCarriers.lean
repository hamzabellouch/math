import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationMomentSources
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsFinite

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairSourceLaws
open Construction CompensationEqualityPatterns

def integerSupport {κ : Type*} [Fintype κ] (value : κ → ℤ) : Finset ℤ :=
  Finset.univ.image value

def integerWeight {κ : Type*} [Fintype κ] (value : κ → ℤ) (w : κ → ℝ) (z : ℤ) : ℝ :=
  ∑ a, if value a = z then w a else 0

@[simp] theorem integerWeight_apply {κ : Type*} [Fintype κ]
    (value : κ → ℤ) (hinj : Function.Injective value) (w : κ → ℝ) (a : κ) :
    integerWeight value w (value a) = w a := by
  classical
  unfold integerWeight
  rw [Finset.sum_eq_single a]
  · simp only [ite_true]
  · intro b hb hba
    simp only [show value b ≠ value a from fun h => hba (hinj h), ite_false]
  · simp

theorem integerWeight_mass {κ : Type*} [Fintype κ]
    (value : κ → ℤ) (hinj : Function.Injective value) (w : κ → ℝ) :
    (∑ z ∈ integerSupport value, integerWeight value w z) = ∑ a, w a := by
  classical
  unfold integerSupport
  rw [Finset.sum_image (fun a ha b hb h => hinj h)]
  simp only [integerWeight_apply value hinj]

theorem source_integerWeight_mass (S : PrimeSource) :
    (∑ z ∈ integerSupport (fun a : S.Sample => (a.val : ℤ)),
      integerWeight (fun a : S.Sample => (a.val : ℤ)) S.law.mass z) = 1 := by
  rw [integerWeight_mass]
  · exact S.law.mass_total
  · intro a b h
    exact Subtype.ext (Int.ofNat_injective h)

theorem common_source_integerWeight_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sources : SourceFamily) (origin : ι → ℕ) (i : ι) :
    (∑ z ∈ integerSupport (fun a : CommonSample sources origin => (a.val : ℤ)),
      integerWeight (fun a : CommonSample sources origin => (a.val : ℤ))
        (sourceWeight sources origin i) z) = 1 := by
  rw [integerWeight_mass]
  · exact HistoryCompensationMoment.sourceWeight_sum sources origin i
  · intro a b h
    exact Subtype.ext (Int.ofNat_injective h)

theorem product_sum_integer {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ι → Type*) [∀ i, Fintype (κ i)]
    (value : ∀ i, κ i → ℤ) (hinj : ∀ i, Function.Injective (value i))
    (w : ∀ i, κ i → ℝ) (F : (ι → ℤ) → ℝ) :
    (∑ x : ∀ i, κ i, (∏ i, w i (x i))*F (fun i => value i (x i))) =
      ∑ y ∈ Fintype.piFinset (fun i => integerSupport (value i)),
        (∏ i, integerWeight (value i) (w i) (y i))*F y :=
  product_sum_embed κ value hinj w (fun i => integerWeight (value i) (w i))
    (fun i => integerWeight_apply (value i) (hinj i) (w i)) F

theorem product_sum_integer_reindex {ι η : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype η] [DecidableEq η] (e : ι ≃ η)
    (κ : ι → Type*) [∀ i, Fintype (κ i)]
    (value : ∀ i, κ i → ℤ) (hinj : ∀ i, Function.Injective (value i))
    (w : ∀ i, κ i → ℝ) (F : (η → ℤ) → ℝ) :
    (∑ x : ∀ i, κ i, (∏ i, w i (x i))*F (fun j => value (e.symm j) (x (e.symm j)))) =
      ∑ y ∈ Fintype.piFinset (fun j => integerSupport (value (e.symm j))),
        (∏ j, integerWeight (value (e.symm j)) (w (e.symm j)) (y j))*F y := by
  have hi := product_sum_integer κ value hinj w (fun x => F (x ∘ e.symm))
  have he := PolynomialFlagReplacementFinite.product_sum_reindex e
    (fun i => integerSupport (value i)) (fun i => integerWeight (value i) (w i))
    (fun x => F (x ∘ e.symm))
  have hr := hi.trans he.symm
  simpa only [Function.comp_def, Equiv.symm_apply_apply, Equiv.apply_symm_apply] using hr

end Ostmann.Arithmetic.HistoryPairSourceLaws

end

end OAI
