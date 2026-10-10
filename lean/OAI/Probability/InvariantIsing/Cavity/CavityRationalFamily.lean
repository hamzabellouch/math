import OAI.Probability.InvariantIsing.Cavity.CavityRationalCounts

namespace OAI

/-! One spectral family on all dimensions, whose divisible dimensions
are precisely the ordered rational-multiplicity models used in telescoping. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def cavityRationalLabel {m n : ℕ} (hm : 0 < m) (s : Fin m → ℕ) (hsum : ∑ a, s a=n)
    (N : ℕ) : Fin N → Fin m :=
  if h : n∣N then
    cavityOrderedGroup (fun a => N/n*s a) (by
      rw [← Finset.mul_sum, hsum, Nat.div_mul_cancel h])
  else fun _ => ⟨0,hm⟩

lemma cavityRationalLabel_progression {m n : ℕ} (hm : 0 < m)
    (s : Fin m → ℕ) (hsum : ∑ a, s a=n) (hn : 0 < n) (q r : ℕ) :
    cavityRationalLabel hm s hsum ((r+q)*n)=
      cavityOrderedGroup (cavityRationalCount s q r) (cavityRationalCount_sum s hsum q r) := by
  have hd : n∣(r+q)*n := dvd_mul_left n (r+q)
  have hdiv : (r+q)*n/n=r+q := by
    have he := Nat.div_mul_cancel hd
    nlinarith
  simp only [cavityRationalLabel, dite_eq_left hd]
  apply cavityOrderedGroup_congr
  funext a
  rw [hdiv]
  rfl

lemma cavityRationalLabel_eq_ordered {m n : ℕ} (hm : 0 < m)
    (s : Fin m → ℕ) (hsum : ∑ a, s a=n) (hn : 0 < n)
    (N v : ℕ) (hN : N=v*n) (hc : ∑ a, v*s a=N) :
    cavityRationalLabel hm s hsum N=cavityOrderedGroup (fun a => v*s a) hc := by
  have hd : n∣N := hN ▸ dvd_mul_left n v
  have hv : N/n=v := Nat.eq_of_mul_eq_mul_right hn ((Nat.div_mul_cancel hd).trans hN)
  simp only [cavityRationalLabel, dite_eq_left hd]
  apply cavityOrderedGroup_congr
  funext a
  rw [hv]

end InvariantIsing

end

end OAI
