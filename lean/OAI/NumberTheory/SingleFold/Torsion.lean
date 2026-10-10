import OAI.NumberTheory.SingleFold.Duplication

namespace OAI

namespace SingleFold.Torsion
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

abbrev E : WeierstrassCurve.Affine ℚ := ⟨0,0,0,-25,0⟩
instance : E.IsElliptic := by
  constructor
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

lemma equation {x y : ℚ} (h : E.Nonsingular x y) : y^2=x^3-25*x := by
  simpa [WeierstrassCurve.Affine.equation_iff,sub_eq_add_neg] using h.1

lemma duplication {x y : ℚ} (h : E.Nonsingular x y) (hy : y ≠ 0) :
    ∃ h' : E.Nonsingular ((x^2+25)^2/(4*y^2)) (E.addY x x y (E.slope x x y y)),
      (2:ℕ) • some x y h = some ((x^2+25)^2/(4*y^2)) (E.addY x x y (E.slope x x y y)) h' := by
  have hy' : y ≠ E.negY x y := by simpa [WeierstrassCurve.Affine.negY] using (show y ≠ -y by intro hh; apply hy; linarith)
  have hs : E.slope x x y y = (3*x^2-25)/(2*y) := by
    rw [slope_of_Y_ne rfl hy']
    simp
    congr 1 <;> ring
  have hx' : E.addX x x (E.slope x x y y) = (x^2+25)^2/(4*y^2) := by
    rw [WeierstrassCurve.Affine.addX,hs]
    dsimp
    field_simp
    have he := equation h
    linear_combination -32*x*he
  rw [two_smul,add_self_of_Y_ne hy']
  have he := E.nonsingular_add h h (by simpa using hy')
  rw [hx'] at he
  exact ⟨he,by simp only [hx']⟩

open DuplicationBound

noncomputable def H : E.Point → ℕ
  | .zero => 1
  | .some x _ _ => height x

def Nondegenerate (P : E.Point) : Prop :=
  ∃ x y h, y ≠ 0 ∧ P = some x y h

lemma double_nondegenerate (P : E.Point) (h : Nondegenerate P) :
    Nondegenerate ((2:ℕ) • P) ∧ H P < H ((2:ℕ) • P) := by
  obtain ⟨x,y,hp,hy,rfl⟩ := h
  obtain ⟨h',hh⟩ := duplication hp hy
  have he := equation hp
  have hx : (x^2+25)^2/(4*y^2) = dupX x := by
    dsimp [dupX]
    congr 1
    linear_combination 4*he
  rw [hh]
  have hu : E.addY x x y (E.slope x x y y) ≠ 0 := by
    intro hz
    have hb := height_y_zero (equation h') hz
    rw [hx] at hb
    exact (not_lt_of_ge hb) (height_dup_gt_five he hy)
  exact ⟨⟨_,_,h',hu,rfl⟩,by simpa only [H,hx] using height_dup_strict he hy⟩

lemma nondegenerate_nontorsion (P : E.Point) (h : Nondegenerate P) : ¬IsOfFinAddOrder P := by
  have hd (n : ℕ) : Nondegenerate ((2^n:ℕ) • P) := by
    induction n with
    | zero => simpa using h
    | succ n hn => simpa [pow_succ',mul_smul] using (double_nondegenerate _ hn).1
  have hmono : StrictMono (fun n : ℕ => H ((2^n:ℕ) • P)) := by
    apply strictMono_nat_of_lt_succ
    intro n
    simpa only [pow_succ',mul_smul] using (double_nondegenerate _ (hd n)).2
  have hi : Function.Injective (fun n : ℕ => (2^n:ℕ) • P) := by
    intro n m he
    exact hmono.injective (congrArg H he)
  intro ht
  have hf : (Set.range (fun n : ℕ => (2^n:ℕ) • P)).Finite :=
    ht.finite_multiples.subset (by rintro _ ⟨n,rfl⟩; exact ⟨2^n,rfl⟩)
  exact (Set.infinite_range_of_injective hi) hf

theorem torsion_doubled (P : E.Point) (h : IsOfFinAddOrder P) : (2:ℕ) • P = 0 := by
  cases P with
  | zero => simp only [←zero_def,nsmul_zero]
  | some x y hp =>
    have hy : y=0 := by
      by_contra hn
      exact nondegenerate_nontorsion _ ⟨x,y,hp,hn,rfl⟩ h
    rw [two_smul,add_self_of_Y_eq (by simp [WeierstrassCurve.Affine.negY,hy])]

theorem torsion_iff (P : E.Point) : IsOfFinAddOrder P ↔ (2:ℕ) • P = 0 := by
  refine ⟨torsion_doubled P,fun h => ?_⟩
  exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨2,by norm_num,h⟩

end SingleFold.Torsion

end OAI
