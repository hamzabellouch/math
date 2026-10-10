import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughExtremal01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
noncomputable section
end

end
 

section
 
 

noncomputable section
open Finset
open scoped BigOperators
namespace DenseBooleanCubes

def PositiveCube (n : ℕ) (A : Finset ℕ) : Prop :=
  ∃ a : ℕ, ∃ h : Fin n → ℕ, (∀ i, 0 < h i) ∧
    ∀ z : Fin n → Bool, a + ∑ i, (if z i then h i else 0) ∈ A

 
lemma dense_shift (ε : ℝ) (hε : 0 < ε) (K : ℕ) (hK : 0 < K)
    (A : Finset ℕ) (hA : A ⊆ range K) (hden : ε*K ≤ (A.card : ℝ))
    (hlarge : 2 ≤ ε*K) :
    ∃ d : ℕ, 0 < d ∧ d ≤ K ∧
      (ε^2/4)*(K : ℝ) ≤ ((A.filter (fun x => x+d ∈ A)).card : ℝ) := by
  let P := (A ×ˢ A).filter (fun p => p.1 < p.2)
  have hmaps : ∀ p ∈ P, p.2-p.1 ∈ Icc 1 K := by
    intro p hp
    obtain ⟨hp, hlt⟩ := mem_filter.mp hp
    obtain ⟨hx, hy⟩ := mem_product.mp hp
    have hyK : p.2 < K := mem_range.mp (hA hy)
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hcount : (Icc 1 K).card • ((ε^2/4)*(K : ℝ)) ≤ (P.card : ℝ) := by
    have hcard : (Icc 1 K).card = K := by simp
    rw [hcard, nsmul_eq_mul]
    dsimp only [P]
    rw [card_product_filter_lt, Nat.cast_choose_two]
    have ha2 : (2 : ℝ) ≤ A.card := hlarge.trans hden
    have hsquare : (ε*(K : ℝ))^2 ≤ (A.card : ℝ)^2 :=
      pow_le_pow_left₀ (mul_nonneg hε.le (Nat.cast_nonneg K)) hden 2
    have harith : (K : ℝ) * (ε^2/4*K) = (ε*(K : ℝ))^2/4 := by ring
    rw [harith]
    nlinarith
  obtain ⟨d, hd, hdb⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    hmaps (nonempty_Icc.mpr hK) hcount
  obtain ⟨hdpos, hdK⟩ := mem_Icc.mp hd
  refine ⟨d, hdpos, hdK, ?_⟩
  have he : (P.filter (fun p => p.2-p.1=d)).card = (A.filter (fun x => x+d ∈ A)).card := by
    apply card_bij (fun p _ => p.1)
    · intro p hp
      obtain ⟨hp, he⟩ := mem_filter.mp hp
      obtain ⟨hp, hlt⟩ := mem_filter.mp hp
      obtain ⟨hx, hy⟩ := mem_product.mp hp
      apply mem_filter.mpr
      refine ⟨hx, ?_⟩
      have hh : p.1+d=p.2 := by omega
      rwa [hh]
    · intro p hp q hq he
      obtain ⟨hp, hpD⟩ := mem_filter.mp hp
      obtain ⟨hq, hqD⟩ := mem_filter.mp hq
      have hplt := (mem_filter.mp hp).2
      have hqlt := (mem_filter.mp hq).2
      exact Prod.ext he (by omega)
    · intro x hx
      obtain ⟨hx, hxd⟩ := mem_filter.mp hx
      refine ⟨(x,x+d), ?_, rfl⟩
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hx,hxd⟩, by omega⟩, by simp⟩
  rwa [he] at hdb

 
lemma cube_of_shift (n : ℕ) (A : Finset ℕ) (d : ℕ) (hd : 0 < d)
    (h : PositiveCube n (A.filter (fun x => x+d ∈ A))) : PositiveCube (n+1) A := by
  obtain ⟨a, b, hb, hcube⟩ := h
  refine ⟨a, Fin.cons d b, ?_, ?_⟩
  · intro i
    refine Fin.cases hd (fun j => ?_) i
    exact hb j
  · intro z
    have hx := mem_filter.mp (hcube (fun j => z j.succ))
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    cases hz : z 0
    · simpa [hz] using hx.1
    · simpa [hz, add_assoc, add_comm, add_left_comm] using hx.2

theorem dense_positive_cube (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ K : ℕ, N ≤ K → ∀ A : Finset ℕ, A ⊆ range K →
      ε*K ≤ (A.card : ℝ) → PositiveCube n A := by
  induction n generalizing ε with
  | zero =>
    refine ⟨1, by omega, ?_⟩
    intro K hK A hA hden
    have hc : 0 < A.card := by
      have hkr : (0 : ℝ) < K := by exact_mod_cast hK
      have hc : (0 : ℝ) < A.card := (mul_pos hε hkr).trans_le hden
      exact_mod_cast hc
    obtain ⟨a, ha⟩ := card_pos.mp hc
    refine ⟨a, Fin.elim0, (fun i => Fin.elim0 i), ?_⟩
    intro z
    simpa using ha
  | succ n ih =>
    have hδ : 0 < ε^2/4 := by positivity
    obtain ⟨N, hN, hn⟩ := ih (ε^2/4) hδ
    obtain ⟨L, hL⟩ := exists_nat_gt (2/ε)
    refine ⟨max N L, lt_of_lt_of_le hN (le_max_left _ _), ?_⟩
    intro K hK A hA hden
    have hKN : N ≤ K := (le_max_left _ _).trans hK
    have hKL : L ≤ K := (le_max_right _ _).trans hK
    have hKpos : 0 < K := hN.trans_le hKN
    have hlarge : 2 ≤ ε*(K : ℝ) := by
      have hLK : (L : ℝ) ≤ K := by exact_mod_cast hKL
      have hh := (div_lt_iff₀ hε).mp hL
      nlinarith
    obtain ⟨d, hd, hdK, hdb⟩ := dense_shift ε hε K hKpos A hA hden hlarge
    apply cube_of_shift n A d hd
    exact hn K hKN _ ((filter_subset _ _).trans hA) hdb

 

 
def blockResidues (A : Finset ℕ) (K q : ℕ) : Finset ℕ :=
  (A.filter (fun i=>i/K=q)).image (fun i=>i%K)

lemma blockResidues_subset (A : Finset ℕ) {K : ℕ} (hK : 0<K) (q : ℕ) :
    blockResidues A K q⊆range K:=by
  intro a ha
  obtain ⟨i,hi,rfl⟩:=mem_image.mp ha
  exact mem_range.mpr (Nat.mod_lt _ hK)

lemma blockResidues_card (A : Finset ℕ) (K q : ℕ) :
    (blockResidues A K q).card=(A.filter (fun i=>i/K=q)).card:=by
  classical
  apply card_image_iff.mpr
  intro i hi j hj he
  have hiq: i/K=q:=(mem_filter.mp hi).2
  have hjq: j/K=q:=(mem_filter.mp hj).2
  have hh:=Nat.mod_add_div i K
  have hh':=Nat.mod_add_div j K
  change i%K=j%K at he
  rw [hiq] at hh
  rw [hjq] at hh'
  omega

lemma mem_from_residue {A : Finset ℕ} {K q a : ℕ}
    (ha : a∈blockResidues A K q) : q*K+a∈A:=by
  obtain ⟨i,hi,he⟩:=mem_image.mp ha
  obtain ⟨hiA,hiq⟩:=mem_filter.mp hi
  have hx : q*K+a=i:=by nlinarith [Nat.mod_add_div i K]
  rwa [hx]

lemma dense_block (ε : ℝ) (hε : 0 < ε) (K N : ℕ) (_ : 0 < K) (hKN : K ≤ N)
    (A : Finset ℕ) (hA : A ⊆ range N) (hden : ε*N ≤ (A.card : ℝ)) :
    ∃ q : ℕ, (ε/2)*(K : ℝ) ≤ ((blockResidues A K q).card : ℝ) := by
  have hmaps : ∀ i ∈ A, i/K ∈ range (N/K+1) := by
    intro i hi
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_range.mp (hA hi)).le))
  have hcount : (range (N/K+1)).card • ((ε/2)*(K : ℝ)) ≤ (A.card : ℝ) := by
    rw [card_range, nsmul_eq_mul]
    have hdiv : ((N/K : ℕ) : ℝ)*(K : ℝ) ≤ N := by exact_mod_cast Nat.div_mul_le_self N K
    have hkn : (K : ℝ) ≤ N := by exact_mod_cast hKN
    have h := mul_le_mul_of_nonneg_left (add_le_add hdiv hkn) hε.le
    push_cast
    nlinarith
  obtain ⟨q, _, hq⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    hmaps (show (range (N/K+1)).Nonempty from ⟨0, mem_range.mpr (Nat.zero_lt_succ _)⟩) hcount
  refine ⟨q, ?_⟩
  rwa [blockResidues_card]

theorem dense_bounded_positive_cube (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∀ N : ℕ, K ≤ N → ∀ A : Finset ℕ, A ⊆ range N →
      ε*N ≤ (A.card : ℝ) → ∃ a : ℕ, ∃ h : Fin n → ℕ,
        (∀ i, 0 < h i ∧ h i ≤ K) ∧
        ∀ z : Fin n → Bool, a + ∑ i, (if z i then h i else 0) ∈ A := by
  obtain ⟨K, hK, hcube⟩ := dense_positive_cube n (ε/2) (by positivity)
  refine ⟨K, hK, ?_⟩
  intro N hKN A hA hden
  obtain ⟨q, hq⟩ := dense_block ε hε K N hK hKN A hA hden
  obtain ⟨a, h, hh, hverts⟩ := hcube K le_rfl (blockResidues A K q)
    (blockResidues_subset A hK q) hq
  refine ⟨q*K+a, h, ?_, ?_⟩
  · intro i
    refine ⟨hh i, ?_⟩
    have hv := hverts (fun j => decide (j=i))
    have hvK := mem_range.mp (blockResidues_subset A hK q hv)
    have he : (∑ j : Fin n, if decide (j=i) then h j else 0) = h i := by simp
    rw [he] at hvK
    omega
  · intro z
    have hv := mem_from_residue (hverts z)
    simpa only [Nat.add_assoc] using hv

namespace CubeSubspace
open Combinatorics
variable {n N : ℕ} (l : Subspace (Fin n) Bool (Fin N)) (h : Fin N → ℕ)

def offset : ℕ := ∑ i, if l.idxFun i = Sum.inl true then h i else 0

def weight (j : Fin n) : ℕ := ∑ i, if l.idxFun i = Sum.inr j then h i else 0

lemma value (z : Fin n → Bool) :
    (∑ i, if l z i then h i else 0) = offset l h + ∑ j, if z j then weight l h j else 0 := by
  have hs : (∑ j, if z j then weight l h j else 0) =
      ∑ i, ∑ j, if l.idxFun i = Sum.inr j then (if z j then h i else 0) else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    cases hz : z j <;> simp [weight]
  rw [hs, offset, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  cases hi : l.idxFun i with
  | inl b => cases b <;> simp [Subspace.coe_apply, hi]
  | inr j => simp [Subspace.coe_apply, hi]

lemma weight_pos (hh : ∀ i, 0 < h i) (j : Fin n) : 0 < weight l h j := by
  obtain ⟨i, hi⟩ := l.proper j
  have hv : h i ≤ weight l h j := by
    dsimp [weight]
    have hv := single_le_sum (fun k (_ : k ∈ (univ : Finset (Fin N))) =>
      Nat.zero_le (if l.idxFun k = Sum.inr j then h k else 0)) (mem_univ i)
    simpa [hi] using hv
  exact (hh i).trans_le hv

lemma weight_le (K : ℕ) (hh : ∀ i, h i ≤ K) (j : Fin n) : weight l h j ≤ N*K := by
  calc
    _ ≤ ∑ _i : Fin N, K := sum_le_sum (fun i _ => by
      split_ifs
      · exact hh i
      · exact Nat.zero_le _)
    _ = N*K := by simp

end CubeSubspace

 
theorem colored_subcube (n : ℕ) (κ : Type*) [Finite κ] :
    ∃ N : ℕ, ∀ C : (Fin N → Bool) → κ,
      ∃ l : Combinatorics.Subspace (Fin n) Bool (Fin N), l.IsMono C :=
  Combinatorics.Subspace.exists_mono_in_high_dimension_fin Bool κ (Fin n)

theorem dense_colored_bounded_cube (n : ℕ) (κ : Type*) [Finite κ]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∀ N : ℕ, K ≤ N → ∀ A : Finset ℕ, A ⊆ range N →
      ε*N ≤ (A.card : ℝ) → ∀ C : ℕ → κ,
      ∃ a : ℕ, ∃ h : Fin n → ℕ, ∃ c : κ,
        (∀ i, 0 < h i ∧ h i ≤ K) ∧
        ∀ z : Fin n → Bool, a + ∑ i, (if z i then h i else 0) ∈ A ∧
          C (a + ∑ i, (if z i then h i else 0)) = c := by
  obtain ⟨m, hm⟩ := colored_subcube n κ
  obtain ⟨K, hK, hcube⟩ := dense_bounded_positive_cube m ε hε
  refine ⟨(m+1)*K, by positivity, ?_⟩
  intro N hN A hA hden C
  have hKN : K ≤ N := (by nlinarith : K ≤ (m+1)*K).trans hN
  obtain ⟨a, h, hh, hverts⟩ := hcube N hKN A hA hden
  obtain ⟨l, c, hc⟩ := hm (fun z => C (a+∑ i, if z i then h i else 0))
  refine ⟨a+CubeSubspace.offset l h, CubeSubspace.weight l h, c, ?_, ?_⟩
  · intro j
    exact ⟨CubeSubspace.weight_pos l h (fun i => (hh i).1) j,
      (CubeSubspace.weight_le l h K (fun i => (hh i).2) j).trans (by nlinarith)⟩
  · intro z
    have he : a+CubeSubspace.offset l h + ∑ j, (if z j then CubeSubspace.weight l h j else 0) =
        a + ∑ i, if l z i then h i else 0 := by rw [CubeSubspace.value, Nat.add_assoc]
    rw [he]
    exact ⟨hverts (l z), hc z⟩

end DenseBooleanCubes

end
end

end OAI
