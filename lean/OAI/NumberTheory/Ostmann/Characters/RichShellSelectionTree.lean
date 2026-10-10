import OAI.NumberTheory.Ostmann.Characters.RichShellSelectionFinite

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters

def shellTreeWidth (M : ℕ) (W : ℝ) (w : List (Fin M)) : ℝ := W / (M:ℝ)^w.length

def shellTreeLeft (M : ℕ) (a W : ℝ) : List (Fin M) → ℝ
  | [] => a
  | i::w => shellTreeLeft M a W w + (i:ℝ) * (shellTreeWidth M W w / M)

@[simp] lemma shellTreeWidth_nil (M : ℕ) (W : ℝ) : shellTreeWidth M W [] = W := by
  simp [shellTreeWidth]

@[simp] lemma shellTreeWidth_cons (M : ℕ) (W : ℝ) (w : List (Fin M)) (i : Fin M) :
    shellTreeWidth M W (i::w) = shellTreeWidth M W w / M := by
  simp only [shellTreeWidth,List.length_cons,pow_succ,div_div]

lemma shellTreeWidth_pos {M : ℕ} (hM : 0 < M) {W : ℝ} (hW : 0 < W) (w : List (Fin M)) :
    0 < shellTreeWidth M W w := div_pos hW (pow_pos (by exact_mod_cast hM) _)

lemma shellTree_bounds {M : ℕ} (hM : 0 < M) (a W : ℝ) (hW : 0 < W) (w : List (Fin M)) :
    a ≤ shellTreeLeft M a W w ∧
      shellTreeLeft M a W w + shellTreeWidth M W w ≤ a+W := by
  induction w with
  | nil => simp [shellTreeLeft]
  | cons i w ih =>
    have hwidth := shellTreeWidth_pos hM hW w
    have hMr : 0 < (M:ℝ) := by exact_mod_cast hM
    have hc : 0 < shellTreeWidth M W w / M := div_pos hwidth hMr
    have hi0 : 0 ≤ (i:ℝ) := Nat.cast_nonneg _
    have hiM : (i:ℝ)+1 ≤ M := by exact_mod_cast i.isLt
    have heq : (M:ℝ)*(shellTreeWidth M W w / M) = shellTreeWidth M W w := by field_simp
    simp only [shellTreeLeft,shellTreeWidth_cons]
    constructor
    · nlinarith [mul_nonneg hi0 hc.le]
    · nlinarith [mul_le_mul_of_nonneg_right hiM hc.le]

lemma shellTreeWidth_ge {M h : ℕ} (hM : 1 ≤ M) (W C : ℝ) (hC : 0 ≤ C)
    (hW : C*(M:ℝ)^(h+1) ≤ W) (w : List (Fin M)) (hw : w.length ≤ h+1) :
    C ≤ shellTreeWidth M W w := by
  have hm : (1:ℝ) ≤ M := by exact_mod_cast hM
  apply (le_div_iff₀ (pow_pos (by linarith : (0:ℝ)<M) _)).mpr
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hm hw) hC).trans hW

lemma harmonic_density_children {M : ℕ} (hM : 0 < M) (E : Finset ℕ) (a W : ℝ)
    (hW : 0 < W) (w : List (Fin M)) :
    (∑ i : Fin M, harmonicIntervalMass E (shellTreeLeft M a W (i::w))
      (shellTreeLeft M a W (i::w)+shellTreeWidth M W (i::w)) / shellTreeWidth M W (i::w)) =
      (M:ℝ) * (harmonicIntervalMass E (shellTreeLeft M a W w)
        (shellTreeLeft M a W w+shellTreeWidth M W w) / shellTreeWidth M W w) := by
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hw := shellTreeWidth_pos hM hW w
  let c := shellTreeWidth M W w / M
  have hc : 0 < c := div_pos hw hMr
  have heq : (M:ℝ)*c = shellTreeWidth M W w := by dsimp [c]; field_simp
  simp only [shellTreeLeft,shellTreeWidth_cons]
  change (∑ i : Fin M, harmonicIntervalMass E (shellTreeLeft M a W w + (i:ℝ)*c)
    (shellTreeLeft M a W w + (i:ℝ)*c+c) / c) = _
  rw [← Finset.sum_div]
  have hsum : (∑ i : Fin M, harmonicIntervalMass E (shellTreeLeft M a W w + (i:ℝ)*c)
      (shellTreeLeft M a W w + (i:ℝ)*c+c)) =
      harmonicIntervalMass E (shellTreeLeft M a W w) (shellTreeLeft M a W w+shellTreeWidth M W w) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => harmonicIntervalMass E
      (shellTreeLeft M a W w+(i:ℝ)*c) (shellTreeLeft M a W w+(i:ℝ)*c+c)) M]
    have hg := harmonicIntervalMass_grid E (shellTreeLeft M a W w) c hc.le M
    convert hg using 1 <;> congr 1
    · funext i
      congr 1
      ring
    · rw [heq]
  rw [hsum]
  dsimp [c]
  field_simp

lemma exists_whole_grid_cell (M : ℕ) (a w x y : ℝ) (hw : 0 < w)
    (hax : a ≤ x) (hxy : x+2*w ≤ y) (hy : y ≤ a+M*w) :
    ∃ i : ℕ, i < M ∧ x ≤ a+i*w ∧ a+(i+1)*w ≤ y := by
  let i := ⌈(x-a)/w⌉₊
  have hdiv : 0 ≤ (x-a)/w := div_nonneg (sub_nonneg.mpr hax) hw.le
  have hlo : x-a ≤ (i:ℝ)*w := (div_le_iff₀ hw).mp (Nat.le_ceil ((x-a)/w))
  have hhi : (i:ℝ)*w < x-a+w := by
    have h := (mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one hdiv) hw)
    simpa only [add_mul,div_mul_cancel₀ _ hw.ne',one_mul] using h
  have hi : (i:ℝ)<M := by nlinarith
  exact ⟨i,by exact_mod_cast hi,by linarith,by nlinarith⟩

end Ostmann.Characters

end

end OAI
