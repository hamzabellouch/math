import OAI.NumberTheory.DirichletL.Detector.LocalSeries
import OAI.NumberTheory.DirichletL.Detector.Euler

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma hasSum_geometric_tail (f : ℕ → ℂ) (a : ℕ) (B V : ℂ) (hV : ‖V‖<1)
    (hz : ∀ m, m<a → f m=0) (hf : ∀ n, f (n+a)=B*V^n) :
    HasSum f (B/(1-V)) := by
  have ht : HasSum (fun n => f (n+a)) (B/(1-V)) := by
    simpa only [hf, div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one hV).mul_left B
  have hs : (∑ i ∈ Finset.range a, f i) = 0 :=
    Finset.sum_eq_zero (fun i hi => hz i (Finset.mem_range.mp hi))
  simpa only [hs, zero_add] using ht.sum_range_add

lemma tsum_two_of_rest_zero (f : ℕ → ℂ) (hf : ∀ k, f (k+2)=0) :
    (∑' k, f k) = f 0+f 1 := by
  rw [tsum_eq_sum (s := {0,1})]
  · simp
  · intro k hk
    have hk2 : 2 ≤ k := by simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk; omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hk2
    simpa only [Nat.add_comm] using hf k

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def principalInner (eta a X W V : ℂ) (e l : ℕ) : ℂ :=
  ∑' k : ℕ, ∑' m : ℕ, principalMarkedTerm p hp hg eta a X W V e l k m

include hc

lemma squarefree_boundary_hasSum (eta a X W V : ℂ) (r : ℕ) :
    HasSum (fun m => principalMarkedTerm p hp hg eta a X W V 1 (2*r) 0 m)
      (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r * (-eta*X)) := by
  apply (hasSum_ite_eq r _).congr
  intro s
  apply Finset.sum_congr rfl
  intro m hmS
  dsimp only
  by_cases hm : m=r
  · subst m
    rw [ite_eq_left rfl, markedTerm_squarefree_boundary p hp hg hc]
  · rw [ite_eq_right hm, markedTerm_squarefree_boundary_off p hp hg hc _ _ _ _ _ _ _ hm]

lemma even_kone_hasSum (eta a X W V : ℂ) (r : ℕ) :
    HasSum (fun m => principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 1 m)
      (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
  apply (hasSum_ite_eq (r+1) _).congr
  intro s
  apply Finset.sum_congr rfl
  intro m hmS
  dsimp only
  by_cases hm : m=r+1
  · subst m
    rw [ite_eq_left rfl, markedTerm_even_kone p hp hg hc]
  · rw [ite_eq_right hm, markedTerm_even_kone_off p hp hg hc _ _ _ _ _ _ _ hm]

lemma even_bulk_hasSum (eta a X W V : ℂ) (hV : ‖V‖<1) (r : ℕ) :
    HasSum (fun m => principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 0 m)
      (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
          (1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)) / (1-V)) := by
  apply hasSum_geometric_tail _ (r+1) _ V hV
  · exact markedTerm_even_bulk_off p hp hg hc eta a X W V r
  · intro n
    rw [Nat.add_comm n (r+1), markedTerm_even_bulk p hp hg hc]
    ring

lemma squarefree_bulk_hasSum (eta a X W V : ℂ) (hV : ‖V‖<1) (r : ℕ) :
    HasSum (fun m => principalMarkedTerm p hp hg eta a X W V 1 (2*r) 1 m)
      (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (-eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W*V) / (1-V)) := by
  apply hasSum_geometric_tail _ (r+1) _ V hV
  · exact markedTerm_squarefree_bulk_off p hp hg hc eta a X W V r
  · intro n
    rw [Nat.add_comm n (r+1), markedTerm_squarefree_bulk p hp hg hc, pow_succ]
    ring

omit hc in
lemma principalInner_two (eta a X W V : ℂ) (e l : ℕ) :
    principalInner p hp hg eta a X W V e l =
      (∑' m, principalMarkedTerm p hp hg eta a X W V e l 0 m) +
      (∑' m, principalMarkedTerm p hp hg eta a X W V e l 1 m) := by
  apply tsum_two_of_rest_zero
  intro k
  simp only [markedTerm_higher_outer p hp hg, tsum_zero]

lemma principalInner_squarefree (eta a X W V : ℂ) (hV : ‖V‖<1) (r : ℕ) :
    principalInner p hp hg eta a X W V 1 (2*r) =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (-eta*X - eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W*V/(1-V)) := by
  rw [principalInner_two p hp hg, (squarefree_boundary_hasSum p hp hg hc _ _ _ _ _ r).tsum_eq,
    (squarefree_bulk_hasSum p hp hg hc _ _ _ _ _ hV r).tsum_eq]
  ring

lemma principalInner_even (eta a X W V : ℂ) (hV : ‖V‖<1) (r : ℕ) :
    principalInner p hp hg eta a X W V 0 (2*r+2) =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
          (1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)/(1-V) +
          W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) := by
  rw [principalInner_two p hp hg, (even_bulk_hasSum p hp hg hc _ _ _ _ _ hV r).tsum_eq,
    (even_kone_hasSum p hp hg hc _ _ _ _ _ r).tsum_eq]
  ring

lemma principalInner_odd (eta a X W V : ℂ) (e r : ℕ) (he : e≤1) :
    principalInner p hp hg eta a X W V e (2*r+1) = 0 := by
  simp only [principalInner, markedTerm_odd p hp hg hc _ _ _ _ _ e r _ _ he, tsum_zero]

omit hc in
@[simp] lemma principalInner_zero (eta a X W V : ℂ) :
    principalInner p hp hg eta a X W V 0 0 = 0 := by
  simp only [principalInner, markedTerm_zero_index p hp hg, tsum_zero]

lemma principalInner_squarefree_hasSum (eta a X W V : ℂ) (hV : ‖V‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1) :
    HasSum (fun l => principalInner p hp hg eta a X W V 1 l)
      ((-eta*X-eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W*V/(1-V)) /
        (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
  let B := -eta*X-eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W*V/(1-V)
  have he : HasSum (fun r => principalInner p hp hg eta a X W V 1 (2*r))
      ((1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)⁻¹ * B) := by
    simpa only [principalInner_squarefree p hp hg hc eta a X W V hV, B] using
      (hasSum_geometric_of_norm_lt_one hR).mul_right B
  have ho : HasSum (fun r => principalInner p hp hg eta a X W V 1 (2*r+1)) 0 := by
    simp only [principalInner_odd p hp hg hc eta a X W V 1 _ (by omega)]
    exact hasSum_zero
  convert he.even_add_odd ho using 1
  simp only [add_zero, div_eq_mul_inv, B]
  ring

lemma principalInner_even_hasSum (eta a X W V : ℂ) (hV : ‖V‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1) :
    HasSum (fun l => principalInner p hp hg eta a X W V 0 l)
      ((evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
          (1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)/(1-V) +
          W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) /
        (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
  let B := evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
          (1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)/(1-V) +
          W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V
  have he : HasSum (fun r => principalInner p hp hg eta a X W V 0 (2*r))
      (B/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    apply hasSum_geometric_tail _ 1 B _ hR
    · intro m hm
      have hm0 : m=0 := by omega
      simp [hm0, principalInner_zero p hp hg]
    · intro r
      rw [show 2*(r+1)=2*r+2 by ring, principalInner_even p hp hg hc _ _ _ _ _ hV]
      ring
  have ho : HasSum (fun r => principalInner p hp hg eta a X W V 0 (2*r+1)) 0 := by
    simp only [principalInner_odd p hp hg hc eta a X W V 0 _ (by omega)]
    exact hasSum_zero
  simpa only [add_zero, B] using he.even_add_odd ho

def principalMarkedSeries (eta a X W V : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l : ℕ, principalInner p hp hg eta a X W V e.val l

theorem principalMarkedSeries_eq (eta a X W V : ℂ) (hV : ‖V‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1) :
    principalMarkedSeries p hp hg eta a X W V =
      markedFactor (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) V
        (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹
        (eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W)
        (-eta*X+W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) 1 := by
  unfold principalMarkedSeries
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  rw [(principalInner_even_hasSum p hp hg hc eta a X W V hV hR).tsum_eq,
    (principalInner_squarefree_hasSum p hp hg hc eta a X W V hV hR).tsum_eq]
  unfold markedFactor
  simp only [pow_one]
  ring

end SevenEighths.ProbeEuler
end

end OAI
