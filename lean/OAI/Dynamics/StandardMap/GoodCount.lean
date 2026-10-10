import OAI.Dynamics.StandardMap.SmoothControl

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma pairMagnitude_step_bounds (M : ℝ) (v : ℕ → ℝ) (a b : ℝ) (j : ℕ)
    (hj : 1≤j) (hv : |v j|+1≤M) :
    pairMagnitude (linearSolution v a b) (j+1) ≤ M*pairMagnitude (linearSolution v a b) j ∧
    pairMagnitude (linearSolution v a b) j ≤ M*pairMagnitude (linearSolution v a b) (j+1) := by
  let u:=linearSolution v a b
  have hstep : u (j+1)=v j*u j-u (j-1) := by
    have h:=linearSolution_step v a b (j-1)
    have hidx : j-1+2=j+1 := by omega
    simpa [u,Nat.sub_add_cancel hj,hidx] using h
  have hb := abs_sub (v j*u j) (u (j-1))
  rw [abs_mul] at hb
  have hinv : u (j-1)=v j*u j-u (j+1) := by linarith [hstep]
  have hb' := abs_sub (v j*u j) (u (j+1))
  rw [abs_mul] at hb'
  have hM : 1≤M := by linarith [abs_nonneg (v j)]
  have huj : |u j|≤pairMagnitude u j := le_max_left _ _
  have hup : |u (j-1)|≤pairMagnitude u j := le_max_right _ _
  have hun : |u (j+1)|≤pairMagnitude u (j+1) := le_max_left _ _
  have huj' : |u j|≤pairMagnitude u (j+1) := by simp [pairMagnitude]
  constructor
  · apply max_le
    · change |u (j+1)|≤M*pairMagnitude u j
      rw [hstep]
      calc
        _ ≤ |v j| *|u j|+|u (j-1)| := hb
        _ ≤ (|v j|+1)*pairMagnitude u j := by nlinarith [mul_le_mul_of_nonneg_left huj (abs_nonneg (v j))]
        _ ≤ _ := mul_le_mul_of_nonneg_right hv (pairMagnitude_nonneg _ _)
    · change |u (j+1-1)|≤M*pairMagnitude u j
      simp only [Nat.add_sub_cancel]
      exact huj.trans (le_mul_of_one_le_left (pairMagnitude_nonneg _ _) hM)
  · apply max_le
    · exact huj'.trans (le_mul_of_one_le_left (pairMagnitude_nonneg _ _) hM)
    · change |u (j-1)| ≤ M*pairMagnitude u (j+1)
      rw [hinv]
      calc
        _ ≤ |v j| *|u j|+|u (j+1)| := hb'
        _ ≤ (|v j|+1)*pairMagnitude u (j+1) := by nlinarith [mul_le_mul_of_nonneg_left huj' (abs_nonneg (v j))]
        _ ≤ _ := mul_le_mul_of_nonneg_right hv (pairMagnitude_nonneg _ _)
lemma pairLog_step_abs (M : ℝ) (v : ℕ → ℝ) (a b : ℝ) (j : ℕ)
    (hM : 1<M) (hj : 1≤j) (hv : |v j|+1≤M)
    (hp : 0<pairMagnitude (linearSolution v a b) j)
    (hn : 0<pairMagnitude (linearSolution v a b) (j+1)) :
    |pairLog M (linearSolution v a b) (j+1)-pairLog M (linearSolution v a b) j|≤1 := by
  have hh:=pairMagnitude_step_bounds M v a b j hj hv
  have hm : 0<M := lt_trans zero_lt_one hM
  have hlog : Real.logb M M=1 := by simp [Real.logb,ne_of_gt (Real.log_pos hM)]
  have hi := (Real.logb_le_logb hM hn (mul_pos hm hp)).mpr hh.1
  have hi' := (Real.logb_le_logb hM hp (mul_pos hm hn)).mpr hh.2
  rw [Real.logb_mul (ne_of_gt hm) (ne_of_gt hp),hlog] at hi
  rw [Real.logb_mul (ne_of_gt hm) (ne_of_gt hn),hlog] at hi'
  exact abs_le.mpr ⟨by dsimp [pairLog]; linarith,by dsimp [pairLog]; linarith⟩

lemma shortfall_count_subset (z : ℕ → ℝ) (c : ℝ) (hc : c<1) (N q : ℕ)
    (hN : 1≤N) (hz : ∀ j, 1≤j → j<N → z (j+1)-z j≤1)
    (S : Finset ℕ) (hS : ∀ j∈S, 2≤j+q ∧ j+q≤N ∧
      ∃ l, 1≤l ∧ l<j+q ∧ z (j+q)-z l<c*((j+q : ℕ)-(l : ℝ))) :
    (S.card : ℝ) ≤ ((N : ℝ)-1-(z N-z 1))/(1-c) := by
  classical
  let B := (Finset.range (N-1)).filter fun n => ∃ l<n+1,
    z (n+1+1)-z (l+1)<c*((n+1 : ℕ)-(l : ℝ))
  have hcard : S.card≤B.card := by
    apply Finset.card_le_card_of_injOn (fun j => j+q-2)
    · intro j hj
      obtain ⟨h2,hN',l,hl,hlj,hbad⟩ := hS j hj
      dsimp only
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by omega),l-1,by omega,?_⟩
      have hjq : j+q-2+1+1=j+q := by omega
      have hjq' : (j+q-2+1 : ℕ)=(j+q)-1 := by omega
      rw [hjq,Nat.sub_add_cancel hl]
      have e : ((j+q-2+1 : ℕ):ℝ)-((l-1 : ℕ):ℝ)=((j+q : ℕ):ℝ)-(l : ℝ) := by
        rw [hjq', Nat.cast_sub (by omega : 1≤j+q), Nat.cast_sub hl]
        norm_num
      rw [e]
      exact hbad
    · intro i hi j hj he
      dsimp only at he
      have hi':= (hS i hi).1
      have hj':= (hS j hj).1
      omega
  have hb := shortfall_count (fun j => z (j+1)) c hc (N-1) (fun n hn => hz (n+1) (by omega) (by omega))
  have hNeq : N-1+1=N := Nat.sub_add_cancel hN
  simp only [hNeq,zero_add] at hb
  have hNr : ((N-1 : ℕ):ℝ)=(N:ℝ)-1 := by rw [Nat.cast_sub hN]; norm_num
  rw [hNr] at hb
  exact (Nat.cast_le.mpr hcard).trans hb

lemma good_failures_count (τ σ : ℕ → ℝ) (c : ℝ) (hc : c<1) (N : ℕ) (hN : 2≤N)
    (hτ : ∀ j, 1≤j → j<N → τ (j+1)-τ j≤1)
    (hσ : ∀ j, 1≤j → j<N → σ (j+1)-σ j≤1) :
    (((Finset.Icc (2:ℕ) (N-2)).filter fun j => ¬
      ((∀ l : ℕ, 1≤l → l<j → c*((j : ℝ)-(l : ℝ))≤τ j-τ l) ∧
       c≤τ (j+1)-τ j ∧ c≤σ (j+1)-σ j ∧ c≤σ (j+2)-σ (j+1))).card : ℝ) ≤
      2*(((N : ℝ)-1-(τ N-τ 1))+((N : ℝ)-1-(σ N-σ 1)))/(1-c) := by
  classical
  let S:=Finset.Icc (2:ℕ) (N-2)
  let P0 := fun j : ℕ => ∃ l : ℕ, 1≤l ∧ l<j ∧ τ j-τ l<c*((j : ℝ)-(l : ℝ))
  let P1 := fun j => τ (j+1)-τ j<c
  let P2 := fun j => σ (j+1)-σ j<c
  let P3 := fun j => σ (j+2)-σ (j+1)<c
  have h0:=shortfall_count_subset τ c hc N 0 (by omega) hτ (S.filter P0) (by
    intro j hj
    obtain ⟨hj,hp⟩:=Finset.mem_filter.mp hj
    obtain ⟨hj2,hjN⟩:=Finset.mem_Icc.mp hj
    exact ⟨by omega,by omega,by simpa [P0] using hp⟩)
  have inc (z : ℕ → ℝ) (q : ℕ) (hq : q=1 ∨ q=2)
      (hz : ∀ j, 1≤j → j<N → z (j+1)-z j≤1) :
      ((S.filter fun j => z (j+q)-z (j+q-1)<c).card : ℝ) ≤
        ((N : ℝ)-1-(z N-z 1))/(1-c) := by
    apply shortfall_count_subset z c hc N q (by omega) hz
    intro j hj
    obtain ⟨hj,hp⟩:=Finset.mem_filter.mp hj
    obtain ⟨hj2,hjN⟩:=Finset.mem_Icc.mp hj
    refine ⟨by omega,by omega,j+q-1,by omega,by omega,?_⟩
    have he : ((j+q : ℕ):ℝ)-((j+q-1 : ℕ):ℝ)=1 := by
      rw [Nat.cast_sub (by omega : 1≤j+q)]; simp
    rw [he, mul_one]
    exact hp
  have h1 : ((S.filter P1).card : ℝ)≤((N:ℝ)-1-(τ N-τ 1))/(1-c) := by
    simpa [P1] using inc τ 1 (Or.inl rfl) hτ
  have h2 : ((S.filter P2).card : ℝ)≤((N:ℝ)-1-(σ N-σ 1))/(1-c) := by
    simpa [P2] using inc σ 1 (Or.inl rfl) hσ
  have h3 : ((S.filter P3).card : ℝ)≤((N:ℝ)-1-(σ N-σ 1))/(1-c) := by
    simpa [P3] using inc σ 2 (Or.inr rfl) hσ
  have he : (S.filter fun j => ¬
      ((∀ l : ℕ, 1≤l → l<j → c*((j : ℝ)-(l : ℝ))≤τ j-τ l) ∧
       c≤τ (j+1)-τ j ∧ c≤σ (j+1)-σ j ∧ c≤σ (j+2)-σ (j+1))) =
      ((S.filter P0) ∪ (S.filter P1)) ∪ ((S.filter P2) ∪ (S.filter P3)) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_union,P0,P1,P2,P3]
    simp only [not_and_or, not_forall, not_le, exists_prop]
    simp only [and_or_left,or_assoc]
  rw [he]
  have hh := Finset.card_union_le ((S.filter P0) ∪ (S.filter P1)) ((S.filter P2) ∪ (S.filter P3))
  have hh' := Finset.card_union_le (S.filter P0) (S.filter P1)
  have hh'' := Finset.card_union_le (S.filter P2) (S.filter P3)
  have hcard : (((S.filter P0) ∪ (S.filter P1) ∪ ((S.filter P2) ∪ (S.filter P3))).card : ℝ)≤
      (S.filter P0).card+(S.filter P1).card+(S.filter P2).card+(S.filter P3).card := by exact_mod_cast (by omega : _)
  calc
    _ ≤ _ := hcard
    _ ≤ 2*(((N : ℝ)-1-(τ N-τ 1))+((N : ℝ)-1-(σ N-σ 1)))/(1-c) := by
      calc
        _ ≤ ((N:ℝ)-1-(τ N-τ 1))/(1-c)+((N:ℝ)-1-(τ N-τ 1))/(1-c)+
            ((N:ℝ)-1-(σ N-σ 1))/(1-c)+((N:ℝ)-1-(σ N-σ 1))/(1-c) := by linarith
        _ = _ := by ring
end StandardMapEntropy

end OAI
