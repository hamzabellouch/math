import Mathlib
import OAI.Probability.SKGap.Terminal.ResidualPairMoments

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

def residualEnergy (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) : ℝ :=
  (vectorNorm (residual j J h k x))^2/(n:ℝ)

lemma residualEnergy_nonneg (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    0≤residualEnergy j J h k x := div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)

lemma residualEnergy_eq (_ : 0<n) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    residualEnergy j J h k x=onsager j J h (k+1) x-onsager j J h k x-
      2*(primaryPair j J h k x/Real.sqrt (n:ℝ)) := by
  have hs : Real.sqrt (n:ℝ)*Real.sqrt (n:ℝ)=(n:ℝ):=Real.mul_self_sqrt (Nat.cast_nonneg n)
  simp only [residualEnergy,vectorNorm_sq,primaryPair,normalizedPair,vectorPair,onsager,siteMean,div_div,hs]
  rw [←sub_div,←mul_div_assoc,←sub_div]
  congr 1
  simp only [Primary.residual,←Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma residualEnergy_sum (hn : 0<n) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (d : ℕ) (x : Spin n) :
    (∑k∈Finset.range d,residualEnergy j J h k x)=onsager j J h d x-
      2*∑k∈Finset.range d,(primaryPair j J h k x/Real.sqrt (n:ℝ)) := by
  induction d with
  | zero=>simp [onsager_zero]
  | succ d ih=>
    rw [Finset.sum_range_succ,Finset.sum_range_succ,ih,residualEnergy_eq hn]
    ring

lemma residualEnergy_sum_le (hn : 0<n) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (d : ℕ) (x : Spin n) {ε : ℝ}
    (hs : ∀k<d,|primaryPair j J h k x|/Real.sqrt (n:ℝ)≤ε) :
    (∑k∈Finset.range d,residualEnergy j J h k x)≤1+2*d*ε := by
  rw [residualEnergy_sum hn]
  have hb:= (onsager_bounds j J h d x).2
  have hp : -(d:ℝ)*ε≤∑k∈Finset.range d,(primaryPair j J h k x/Real.sqrt (n:ℝ)) := by
    calc
      _ = ∑_k∈Finset.range d,-ε := by simp
      _ ≤ _ := Finset.sum_le_sum (fun k hk=>by
        have H:=hs k (Finset.mem_range.mp hk)
        have H' : |primaryPair j J h k x/Real.sqrt (n:ℝ)|≤ε := by
          simpa only [abs_div,abs_of_nonneg (Real.sqrt_nonneg _)] using H
        exact (abs_le.mp H').1)
  nlinarith

lemma sum_range_pairs (E : ℕ→ℝ) (m : ℕ) :
    (∑k∈Finset.range (2*m),E k)=∑k∈Finset.range m,(E (2*k)+E (2*k+1)) := by
  induction m with
  | zero=>simp
  | succ m ih=>
    rw [show 2*(m+1)=2*m+1+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ,ih,
      Finset.sum_range_succ]
    ring

lemma disjoint_small_pair (E : ℕ→ℝ) (hE : ∀k,0≤E k) (m : ℕ) {a K : ℝ}
    (_ : 0≤a) (hm : K<(m:ℝ)*a) (he : (∑k∈Finset.range (2*m),E k)≤K) :
    ∃ k < m,E (2*k)≤a ∧ E (2*k+1)≤a := by
  by_contra hh
  have hb : ∀ k < m,a<E (2*k)+E (2*k+1) := by
    intro k hk
    have H : ¬(E (2*k)≤a ∧ E (2*k+1)≤a):=fun ht=>hh ⟨k,hk,ht⟩
    by_cases h : E (2*k)≤a
    · have ht : a<E (2*k+1):=lt_of_not_ge (fun ht=>H ⟨h,ht⟩)
      linarith [hE (2*k)]
    · have ht:=lt_of_not_ge h
      linarith [hE (2*k+1)]
  have H : (m:ℝ)*a≤∑k∈Finset.range (2*m),E k := by
    rw [sum_range_pairs]
    calc
      _ = ∑_k∈Finset.range m,a := by simp
      _ ≤ _ := Finset.sum_le_sum (fun k hk=>(hb k (Finset.mem_range.mp hk)).le)
  linarith

lemma small_residual_pair (hn : 0<n) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (m : ℕ) (x : Spin n) {ρ ε : ℝ} (hρ : 0<ρ)
    (hm : 2<(m:ℝ)*ρ^2/4) (he : 2*(2*m:ℕ)*ε≤1)
    (hs : ∀k<2*m,|primaryPair j J h k x|/Real.sqrt (n:ℝ)≤ε) :
    ∃ k < m,vectorNorm (residual j J h (2*k) x)≤ρ*Real.sqrt (n:ℝ)/2 ∧
      vectorNorm (residual j J h (2*k+1) x)≤ρ*Real.sqrt (n:ℝ)/2 := by
  obtain ⟨k,hk,h0,h1⟩:=disjoint_small_pair (fun k=>residualEnergy j J h k x)
    (fun k=>residualEnergy_nonneg j J h k x) m (a:=ρ^2/4) (K:=2) (by positivity)
    (by nlinarith) ((residualEnergy_sum_le hn j J h (2*m) x hs).trans (by linarith))
  have hnorm (k : ℕ) (hk : residualEnergy j J h k x≤ρ^2/4) :
      vectorNorm (residual j J h k x)≤ρ*Real.sqrt (n:ℝ)/2 := by
    apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
    simp only [←sq,div_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
    have hnR : (0:ℝ)<n:=Nat.cast_pos.mpr hn
    have H:=(div_le_iff₀ hnR).mp hk
    nlinarith
  exact ⟨k,hk,hnorm _ h0,hnorm _ h1⟩

end SKGapCutoff.Recipe

end
end

end OAI
