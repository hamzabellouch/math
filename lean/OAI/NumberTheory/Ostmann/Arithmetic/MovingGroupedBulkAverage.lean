import OAI.NumberTheory.Ostmann.Arithmetic.GroupedBulkSymmetrization
import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeIndex

namespace OAI

/-! # Averaging the regular bulk inside the full giant and frequency fibre -/

namespace Ostmann
open scoped Classical BigOperators

theorem grouped_three_bulk_average {B A X S K : Type*}
    [Fintype B] [Fintype A] [Fintype X] [Fintype S]
    (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (ν : B → A → ℝ) (hν : ∀ j k, ν (slot j) = ν (slot k)) (ρ : X → ℝ)
    (key : X → (B → A) → S → K)
    (hkey : ∀ x s e y, key x (selectedBulkSample slot e y) s = key x y s)
    (W : X → (B → A) → S → ℂ) (k : K) :
    groupedCoefficient (fun a : X × ((B → A) × S) => key a.1 a.2.1 a.2.2)
      (fun a => ((ρ a.1 * ∏ i, ν i (a.2.1 i) : ℝ) : ℂ) *
        mixedBulkSymmetrize n m slot (fun _ y _ _ => W a.1 y a.2.2) 0 a.2.1 0 0) k =
    groupedCoefficient (fun a : X × ((B → A) × S) => key a.1 a.2.1 a.2.2)
      (fun a => ((ρ a.1 * ∏ i, ν i (a.2.1 i) : ℝ) : ℂ) * W a.1 a.2.1 a.2.2) k := by
  unfold groupedCoefficient
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun y s => if key x y s = k then _ else 0)]
  apply Finset.sum_congr rfl
  intro s _
  have h := groupedCoefficient_bulk_average n m slot ν hν (fun y => key x y s)
    (hkey x s) (fun y => W x y s) k
  have hh := congrArg (fun z : ℂ => (ρ x : ℂ) * z) h
  simpa only [groupedCoefficient, Complex.ofReal_mul, Finset.mul_sum, mul_ite,
    mul_zero, mul_assoc] using hh

theorem movingAmplitude_grouped_bulk_average
    (P Pg : Finset ℕ) (n r m : ℕ) (V : ℕ → ℕ)
    (ρ : Pg → ℝ) (ν : MovingRegularSlot n r m → P → ℝ)
    (hν : ∀ j k : TreeLeafIndex n × Fin m,
      ν (movingTemplateBulk n r m j) = ν (movingTemplateBulk n r m k))
    (W : MovingAmplitudeIndex P Pg n r m V → ℂ) (k : ℕ × ℕ × ℤ) :
    groupedCoefficient
      (fun a : MovingAmplitudeIndex P Pg n r m V => ((a.1 : ℕ), (∏ i, (a.2.1 i : ℕ)), a.2.2.val))
      (fun a => (movingAmplitudePrior Pg n r m V ρ ν a : ℂ) *
        mixedBulkSymmetrize n m (movingTemplateBulk n r m)
          (fun _ y _ _ => W (a.1, y, a.2.2)) 0 a.2.1 0 0) k =
    groupedCoefficient
      (fun a : MovingAmplitudeIndex P Pg n r m V => ((a.1 : ℕ), (∏ i, (a.2.1 i : ℕ)), a.2.2.val))
      (fun a => (movingAmplitudePrior Pg n r m V ρ ν a : ℂ) * W a) k := by
  have hkey (x : Pg) (s : transferFrequencyRange (V n))
      (e : Equiv.Perm (TreeLeafIndex n × Fin m)) (y : MovingRegularSlot n r m → P) :
      ((x : ℕ), (∏ i, (selectedBulkSample (A := P) (movingTemplateBulk n r m) e y i : ℕ)), s.val) =
        ((x : ℕ), (∏ i, (y i : ℕ)), s.val) := by
    exact Prod.ext rfl (Prod.ext
      ((selectedBulkPerm (movingTemplateBulk n r m) e).symm.prod_comp (fun i => (y i : ℕ))) rfl)
  have h := grouped_three_bulk_average
    (B := MovingRegularSlot n r m) (A := P) (X := Pg)
    (S := transferFrequencyRange (V n)) (K := ℕ × ℕ × ℤ)
    n m (movingTemplateBulk n r m) ν hν ρ
    (fun x y s => ((x : ℕ), (∏ i, (y i : ℕ)), s.val)) hkey
    (fun x y s => W (x, y, s)) k
  convert h using 1 <;> simp only [movingAmplitudePrior, groupedCoefficient, MovingAmplitudeIndex, finite_univ_canonical, Prod.eta]

end Ostmann

end OAI
