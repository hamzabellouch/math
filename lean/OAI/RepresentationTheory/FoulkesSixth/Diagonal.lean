import Mathlib

namespace OAI

noncomputable section

namespace Foulkes.Diagonal
open MvPolynomial

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℂ V]

def exponent (f : ι → ι) : ι →₀ ℕ := ∑ i, Finsupp.single (f i) 1

lemma exponent_id : exponent (id : ι → ι) = ∑ i, Finsupp.single i 1 := rfl

lemma bijective_of_exponent_eq (f : ι → ι)
    (h : exponent f = exponent (id : ι → ι)) : Function.Bijective f := by
  classical
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  constructor
  · intro k
    by_contra hk
    have hn : ∀ i, f i ≠ k := by simpa using hk
    have hh := congrArg (fun d : ι →₀ ℕ => d k) h
    have hz : exponent f k = 0 := by
      simp [exponent, hn]
    have ho : exponent (id : ι → ι) k = 1 := by
      simp [exponent, Finsupp.single_apply]
    rw [hz, ho] at hh
    omega
  · rfl

def expansion (T : MultilinearMap ℂ (fun _ : ι => V) ℂ) (v : ι → V) :
    MvPolynomial ι ℂ := by
  classical
  exact ∑ f : ι → ι, monomial (exponent f) (T (fun i => v (f i)))

lemma eval_expansion (T : MultilinearMap ℂ (fun _ : ι => V) ℂ)
    (v : ι → V) (x : ι → ℂ) :
    eval x (expansion T v) = T (fun _ => ∑ j, x j • v j) := by
  classical
  rw [T.map_sum]
  simp only [expansion, map_sum]
  apply Finset.sum_congr rfl
  intro f hf
  rw [T.map_smul_univ]
  have hm : (monomial (exponent f) 1 : MvPolynomial ι ℂ) = ∏ i, X (f i) := by
    simpa only [exponent, X] using
      (monomial_sum_one (R := ℂ) Finset.univ (fun i => Finsupp.single (f i) 1))
  calc
    eval x (monomial (exponent f) (T (fun i => v (f i)))) =
        T (fun i => v (f i)) * eval x (monomial (exponent f) 1) := by
      simp [eval_monomial]
    _ = (∏ i, x (f i)) • T (fun i => v (f i)) := by
      rw [hm]
      simp [mul_comm]

theorem eq_zero_of_symmetric_of_diagonal
    (T : MultilinearMap ℂ (fun _ : ι => V) ℂ)
    (hs : ∀ (σ : Equiv.Perm ι) (v : ι → V), T (fun i => v (σ i)) = T v)
    (hd : ∀ v : V, T (fun _ => v) = 0) : T = 0 := by
  classical
  ext v
  have hp : expansion T v = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [eval_expansion, hd, map_zero]
  let G : Finset (ι → ι) := Finset.univ.filter (fun f => exponent f = exponent (id : ι → ι))
  have hG : G.Nonempty := ⟨id, by simp [G]⟩
  have hn : (G.card : ℂ) ≠ 0 := by exact_mod_cast hG.card_pos.ne'
  have hc := congrArg (fun polynomial => polynomial.coeff (exponent (id : ι → ι))) hp
  have he : (expansion T v).coeff (exponent (id : ι → ι)) = (G.card : ℂ) * T v := by
    simp only [expansion, coeff_sum, coeff_monomial]
    rw [← Finset.sum_filter]
    change (∑ f ∈ G, T (fun i => v (f i))) = _
    calc
      _ = ∑ _f ∈ G, T v := by
        apply Finset.sum_congr rfl
        intro f hf
        exact hs (Equiv.ofBijective f (bijective_of_exponent_eq f (Finset.mem_filter.mp hf).2)) v
      _ = (G.card : ℂ) * T v := by simp
  rw [he, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
  exact (mul_eq_zero.mp hc).resolve_left hn

end Foulkes.Diagonal

end

end OAI
