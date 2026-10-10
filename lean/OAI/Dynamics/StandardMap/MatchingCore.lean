import OAI.Dynamics.StandardMap.GoodCount

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy

lemma half_unit_crossing (τ : ℕ → ℝ) (N : ℕ) (a : ℝ)
    (hτ : ∀ j, 1≤j → j<N → τ (j+1)-τ j≤1)
    (h1 : τ 1=0) (ha : 1<a) (hN1 : 1≤N) (hN : a≤τ N) :
    ∃ k, 2≤k ∧ k≤N ∧ |τ k-a|≤1/2 := by
  have hex : ∃ k : ℕ, 1≤k ∧ a≤τ k := ⟨N,hN1,hN⟩
  let k := Nat.find hex
  have hk : 1≤k ∧ a≤τ k := Nat.find_spec hex
  have hkle : k≤N := Nat.find_min' hex ⟨hN1,hN⟩
  have hk2 : 2≤k := by
    by_contra hn
    have he : k=1 := by omega
    rw [he,h1] at hk
    linarith
  have hprev : τ (k-1)<a := by
    have hf := Nat.find_min hex (by omega : k-1<k)
    exact lt_of_not_ge (fun h => hf ⟨by omega,h⟩)
  have hstep := hτ (k-1) (by omega) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1≤k)] at hstep
  have hk3 : 3≤k := by
    by_contra hn
    have he : k=2 := by omega
    rw [he] at hstep
    norm_num [h1] at hstep
    have := hk.2
    rw [he] at this
    linarith
  by_cases hnear : τ k-a≤1/2
  · exact ⟨k,hk2,hkle,abs_le.mpr ⟨by linarith [hk.2],hnear⟩⟩
  · exact ⟨k-1,by omega,by omega,abs_le.mpr ⟨by linarith,by linarith⟩⟩
lemma separated_fiber_card (S : Finset ℕ) (τ : ℕ → ℝ) (a c : ℝ)
    (hc : 1/2<c)
    (hsep : ∀ i∈S, ∀ j∈S, i<j → c*((j:ℝ)-(i:ℝ))≤τ j-τ i)
    (hclose : ∀ i∈S, |τ i-a|≤1/2) : S.card≤2 := by
  classical
  by_cases hS : S.Nonempty
  · let m := S.min' hS
    have hm : m∈S := S.min'_mem hS
    have hsub : S⊆Finset.Icc m (m+1) := by
      intro j hj
      have hjm : m≤j := S.min'_le _ hj
      refine Finset.mem_Icc.mpr ⟨hjm,?_⟩
      by_contra hf
      have hd : (m:ℝ)+2≤(j:ℝ) := by exact_mod_cast (by omega : m+2≤j)
      have hs := hsep m hm j hj (by omega)
      have hmi := (abs_le.mp (hclose m hm)).1
      have hji := (abs_le.mp (hclose j hj)).2
      nlinarith
    have hh := Finset.card_le_card hsub
    simp only [Nat.card_Icc] at hh
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS]

lemma discard_bad_matches (S B : Finset ℕ) (τ ρ : ℕ → ℝ) (f : ℕ → ℕ) (c : ℝ)
    (hc : 1/2<c)
    (hsep : ∀ i∈S, ∀ j∈S, i<j → c*((j:ℝ)-(i:ℝ))≤τ j-τ i)
    (hclose : ∀ i∈S, |τ i-ρ (f i)|≤1/2) :
    (S.filter fun i => f i∈B).card≤2*B.card := by
  classical
  have hfiber (b : ℕ) : ((S.filter fun i => f i∈B).filter fun i => f i=b).card≤2 := by
    apply separated_fiber_card _ τ (ρ b) c hc
    · intro i hi j hj hij
      exact hsep i (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
        j (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1 hij
    · intro i hi
      obtain ⟨hi,he⟩ := Finset.mem_filter.mp hi
      simpa only [he] using hclose i (Finset.mem_filter.mp hi).1
  have he := Finset.card_eq_sum_card_fiberwise (f := f) (s := S.filter fun i => f i∈B)
    (t := B) (fun i hi => (Finset.mem_filter.mp hi).2)
  rw [he]
  calc
    _ ≤ ∑ _b∈B, 2 := Finset.sum_le_sum fun b _ => hfiber b
    _ = _ := by simp [mul_comm]

lemma spaced_matched_subset (S : Finset ℕ) (τ ρ : ℕ → ℝ) (f : ℕ → ℕ) (c : ℝ)
    (hc : 1/2<c)
    (hsep : ∀ i∈S, ∀ j∈S, i<j → c*((j:ℝ)-(i:ℝ))≤τ j-τ i)
    (hclose : ∀ i∈S, |τ i-ρ (f i)|≤1/2)
    (horder : ∀ i∈S, ∀ j∈S, f j≤f i → ρ (f j)≤ρ (f i)) :
    ∃ T : Finset ℕ, T⊆S ∧ S.card/3≤T.card ∧
      ∀ i∈T, ∀ j∈T, i<j → f i<f j := by
  classical
  obtain ⟨r,hr,hcard⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := S) (t := Finset.range 3) (f := fun i => i%3)
    (fun i _ => Finset.mem_range.mpr (Nat.mod_lt i (by omega)))
    (by simp) (by simpa using Nat.mul_div_le S.card 3)
  let T:=S.filter fun i => i%3=r
  refine ⟨T,Finset.filter_subset _ _,hcard,?_⟩
  intro i hi j hj hij
  obtain ⟨hi,hir⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj,hjr⟩ := Finset.mem_filter.mp hj
  have hd : i+3≤j := by omega
  have hdr : (i:ℝ)+3≤(j:ℝ) := by exact_mod_cast hd
  have hs := hsep i hi j hj hij
  have hi' := (abs_le.mp (hclose i hi)).1
  have hj' := (abs_le.mp (hclose j hj)).2
  by_contra hf
  have hm := horder i hi j hj (by omega)
  nlinarith
end StandardMapEntropy

end OAI
