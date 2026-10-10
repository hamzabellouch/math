import OAI.Computability.MatchingCount.BinaryParser

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset

def Piece.evalReal (p : Piece) (t : ℝ) : ℝ := (p.slope:ℝ)*t+(p.constant:ℝ)

def selectedReal (k : ℕ) (t : ℝ) : Piece := by
  classical
  exact ((pieces k).argmin (fun p => p.evalReal t)).getD ⟨k,0⟩

def psiReal (k : ℕ) (t : ℝ) : ℝ := (selectedReal k t).evalReal t

def dyadic (j : ℕ) : ℝ := (2:ℝ)⁻¹^j

lemma pieces_nonempty (k : ℕ) : pieces k ≠ [] := by simp [pieces]

lemma selectedPiece_mem_argmin (k : ℕ) (t : ℚ) :
    selectedPiece k t ∈ (pieces k).argmin (fun p => p.eval t) := by
  unfold selectedPiece
  cases he : (pieces k).argmin (fun p => p.eval t) with
  | none => exact (pieces_nonempty k (List.argmin_eq_none.mp he)).elim
  | some p => simp

lemma selectedReal_mem_argmin (k : ℕ) (t : ℝ) :
    selectedReal k t ∈ (pieces k).argmin (fun p => p.evalReal t) := by
  classical
  unfold selectedReal
  cases he : (pieces k).argmin (fun p => p.evalReal t) with
  | none => exact (pieces_nonempty k (List.argmin_eq_none.mp he)).elim
  | some p => simp

lemma psiReal_le_piece (k : ℕ) (t : ℝ) (p : Piece) (hp : p∈pieces k) :
    psiReal k t ≤ p.evalReal t :=
  List.le_of_mem_argmin hp (selectedReal_mem_argmin k t)

lemma le_psiReal (k : ℕ) (t b : ℝ) (h : ∀ p∈pieces k,b≤p.evalReal t) :
    b ≤ psiReal k t := h _ (List.argmin_mem (selectedReal_mem_argmin k t))

lemma realPsi_cast (k : ℕ) (t : ℚ) : psiReal k (t:ℝ)=(psi k t:ℝ) := by
  have cast_eval (p : Piece) : p.evalReal (t:ℝ)=(p.eval t:ℝ) := by
    simp [Piece.eval,Piece.evalReal]
  apply le_antisymm
  · have h := psiReal_le_piece k (t:ℝ) _ (List.argmin_mem (selectedPiece_mem_argmin k t))
    simpa only [cast_eval,psi] using h
  · apply le_psiReal
    intro p hp
    rw [cast_eval]
    exact_mod_cast (List.le_of_mem_argmin hp (selectedPiece_mem_argmin k t))

lemma psiReal_concave (k : ℕ) : ConcaveOn ℝ Set.univ (psiReal k) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  apply le_psiReal
  intro p hp
  have hx := psiReal_le_piece k x p hp
  have hy := psiReal_le_piece k y p hp
  simp only [smul_eq_mul]
  calc
    a*psiReal k x+b*psiReal k y ≤ a*p.evalReal x+b*p.evalReal y := by gcongr
    _ = p.evalReal (a*x+b*y) := by
      simp only [Piece.evalReal]
      have hh := congrArg (fun t => t*(p.constant:ℝ)) hab
      nlinarith [hh]

lemma mem_pieces (k : ℕ) (p : Piece) :
    p∈pieces k ↔ p=⟨k,0⟩ ∨ ∃ j<k,p=⟨(j:ℤ)-1,(2:ℚ)⁻¹^j⟩ := by
  simp only [pieces,List.mem_append,List.mem_map,List.mem_range,List.mem_singleton]
  aesop

lemma first_mem_pieces (k : ℕ) : (⟨k,0⟩:Piece)∈pieces k := (mem_pieces k _).2 (Or.inl rfl)
lemma chord_mem_pieces (k j : ℕ) (hj : j<k) :
    (⟨(j:ℤ)-1,(2:ℚ)⁻¹^j⟩:Piece)∈pieces k := (mem_pieces k _).2 (Or.inr ⟨j,hj,rfl⟩)

lemma chord_eval (j : ℕ) (t : ℝ) :
    (⟨(j:ℤ)-1,(2:ℚ)⁻¹^j⟩:Piece).evalReal t=((j:ℝ)-1)*t+dyadic j := by
  simp [Piece.evalReal,dyadic]

lemma first_eval (k : ℕ) (t : ℝ) : (⟨k,0⟩:Piece).evalReal t=(k:ℝ)*t := by
  simp [Piece.evalReal]

lemma dyadic_pos (j : ℕ) : 0<dyadic j := by unfold dyadic; positivity
lemma dyadic_nonneg (j : ℕ) : 0≤dyadic j := (dyadic_pos j).le
lemma dyadic_succ (j : ℕ) : dyadic (j+1)=dyadic j/2 := by simp [dyadic,pow_succ,div_eq_mul_inv]
lemma dyadic_zero : dyadic 0=1 := by simp [dyadic]
lemma dyadic_mul_pow (j : ℕ) : dyadic j*(2:ℝ)^j=1 := by
  rw [dyadic,←mul_pow]; norm_num

lemma dyadic_scale (j l : ℕ) (h : l≤j) : dyadic l=(2:ℝ)^(j-l)*dyadic j := by
  have hj : j=l+(j-l) := by omega
  conv_rhs => rw [hj,dyadic,pow_add]
  rw [Nat.add_sub_cancel_left]
  change (2:ℝ)⁻¹^l=(2:ℝ)^(j-l)*((2:ℝ)⁻¹^l*(2:ℝ)⁻¹^(j-l))
  calc
    _ = (2:ℝ)⁻¹^l*1 := (mul_one _).symm
    _ = _ := by rw [←dyadic_mul_pow (j-l)]; unfold dyadic; ring

lemma chord_above_knot (l j : ℕ) :
    (j:ℝ)*dyadic j ≤ ((l:ℝ)-1)*dyadic j+dyadic l := by
  rcases lt_trichotomy l j with h|h|h
  · have hp : 1+(j-l:ℕ) ≤ (2:ℕ)^(j-l) := by
      have hh := one_add_mul_le_pow (show (-2:ℝ)≤1 by norm_num) (j-l)
      norm_num at hh
      exact_mod_cast hh
    have hpR : (1:ℝ)+(j:ℝ)-(l:ℝ) ≤ (2:ℝ)^(j-l) := by
      have := Nat.cast_le (α:=ℝ).mpr hp
      push_cast [Nat.cast_sub h.le] at this
      linarith
    rw [dyadic_scale j l h.le]
    nlinarith [mul_le_mul_of_nonneg_right hpR (dyadic_nonneg j)]
  · subst l; ring_nf; rfl
  · have hh : (j:ℝ)+1≤l := by exact_mod_cast h
    nlinarith [dyadic_nonneg j,dyadic_nonneg l]

lemma psiReal_knot (k j : ℕ) (hj : j≤k) : psiReal k (dyadic j)=(j:ℝ)*dyadic j := by
  apply le_antisymm
  · rcases lt_or_eq_of_le hj with h|h
    · have hh := psiReal_le_piece k (dyadic j) _ (chord_mem_pieces k j h)
      rw [chord_eval] at hh
      nlinarith
    · subst j
      simpa only [first_eval] using psiReal_le_piece k (dyadic k) _ (first_mem_pieces k)
  · apply le_psiReal
    intro p hp
    rcases (mem_pieces k p).1 hp with rfl|⟨l,_,rfl⟩
    · rw [first_eval]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (dyadic_nonneg j)
    · rw [chord_eval]; exact chord_above_knot l j

lemma psiReal_zero (k : ℕ) : psiReal k 0=0 := by
  apply le_antisymm
  · simpa only [first_eval,mul_zero] using psiReal_le_piece k 0 _ (first_mem_pieces k)
  · apply le_psiReal
    intro p hp
    rcases (mem_pieces k p).1 hp with rfl|⟨j,_,rfl⟩
    · simp [first_eval]
    · simpa only [chord_eval,mul_zero,zero_add] using dyadic_nonneg j

end
end BinaryMatching.Algorithm
end

end OAI
