import OAI.NumberTheory.Ostmann.Supply.KernelProducts

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators

def enumeratePrimes (P : Finset ℕ) (i : ℕ) : ℕ :=
  if hi : i<P.card then P.orderEmbOfFin rfl ⟨i,hi⟩ else 2

@[simp] theorem enumeratePrimes_lt (P : Finset ℕ) {i : ℕ} (hi : i<P.card) :
    enumeratePrimes P i=P.orderEmbOfFin rfl ⟨i,hi⟩ := dite_eq_left hi

theorem enumeratePrimes_mem (P : Finset ℕ) {i : ℕ} (hi : i<P.card) :
    enumeratePrimes P i∈P := by rw [enumeratePrimes_lt P hi]; exact P.orderEmbOfFin_mem rfl _

theorem enumeratePrimes_prime (P : Finset ℕ) (hp : ∀p∈P,p.Prime) (i : ℕ) :
    (enumeratePrimes P i).Prime := by
  by_cases hi : i<P.card
  · exact hp _ (enumeratePrimes_mem P hi)
  · simp only [enumeratePrimes,dite_eq_right hi]
    norm_num

instance enumeratePrimes_neZero (P : Finset ℕ) [hp : Fact (∀p∈P,p.Prime)] (i : ℕ) :
    NeZero (enumeratePrimes P i) := ⟨(enumeratePrimes_prime P hp.out i).ne_zero⟩

theorem enumeratePrimes_injective (P : Finset ℕ) :
    Set.InjOn (enumeratePrimes P) (Finset.range P.card:Set ℕ) := by
  intro i hi j hj hij
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  rw [enumeratePrimes_lt P hi',enumeratePrimes_lt P hj'] at hij
  exact congrArg Fin.val ((P.orderEmbOfFin rfl).injective hij)

theorem enumeratePrimes_image (P : Finset ℕ) :
    (Finset.range P.card).image (enumeratePrimes P)=P := by
  ext p
  constructor
  · intro hp
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    exact enumeratePrimes_mem P (Finset.mem_range.mp hi)
  · intro hp
    let i := (P.orderIsoOfFin rfl).symm ⟨p,hp⟩
    refine Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr i.isLt,?_⟩
    rw [enumeratePrimes_lt P i.isLt]
    exact congrArg Subtype.val ((P.orderIsoOfFin rfl).apply_symm_apply ⟨p,hp⟩)

theorem sum_enumeratePrimes {M : Type*} [AddCommMonoid M] (P : Finset ℕ) (f : ℕ→M) :
    (∑i∈Finset.range P.card,f (enumeratePrimes P i))=∑p∈P,f p := by
  calc
    _ = ∑q∈(Finset.range P.card).image (enumeratePrimes P),f q :=
      (Finset.sum_image (enumeratePrimes_injective P)).symm
    _ = _ := by rw [enumeratePrimes_image P]

theorem reciprocalMass_enumeratePrimes (P : Finset ℕ) :
    reciprocalMass (Finset.range P.card) (enumeratePrimes P)=∑p∈P,(1:ℝ)/p :=
  sum_enumeratePrimes P (fun p => (1:ℝ)/p)

end Ostmann.Supply

end

end OAI
