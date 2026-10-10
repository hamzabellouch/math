import OAI.Analysis.StrictMeans.LatticeIndex

namespace OAI

section
namespace StrictInverseFirstPower.Grid
noncomputable section

def lineIndex (p : ℤ → ℝ) (i : ℤ) : ℤ :=
  1-bit (decide (p (i+1)<p i))-bit (decide (p (i-1)≤p i))

lemma convex_line_index (t : ℝ) (i : ℤ) :
    lineIndex (fun j => ((j:ℝ)-t)^2) i = if i=⌈t-1/2⌉ then 1 else 0 := by
  have h₁ := Int.le_ceil (t-1/2)
  have h₂ := Int.ceil_lt_add_one (t-1/2)
  have right_iff : (((i+1:ℤ):ℝ)-t)^2 < ((i:ℝ)-t)^2 ↔ (i:ℝ)<t-1/2 := by
    push_cast
    constructor <;> intro h <;> nlinarith
  have left_iff : (((i-1:ℤ):ℝ)-t)^2 ≤ ((i:ℝ)-t)^2 ↔ t+1/2≤(i:ℝ) := by
    push_cast
    constructor <;> intro h <;> nlinarith
  unfold lineIndex
  simp only [right_iff,left_iff]
  rcases lt_trichotomy i ⌈t-1/2⌉ with hi|hi|hi
  · have hir : (i:ℝ) ≤ (⌈t-1/2⌉:ℝ)-1 := by exact_mod_cast (show i≤⌈t-1/2⌉-1 by omega)
    have hr : (i:ℝ)<t-1/2 := by linarith
    have hl : ¬ t+1/2≤(i:ℝ) := by linarith
    simp only [bit,decide_eq_true_eq,hr,hl,ite_true,ite_false,ne_of_lt hi]; norm_num
  · have hir : (i:ℝ) = (⌈t-1/2⌉:ℝ) := by exact_mod_cast hi
    have hr : ¬ (i:ℝ)<t-1/2 := by linarith
    have hl : ¬ t+1/2≤(i:ℝ) := by linarith
    simp only [bit,decide_eq_true_eq,hr,hl,ite_false]; simp [hi]
  · have hir : (⌈t-1/2⌉:ℝ)+1 ≤ (i:ℝ) := by exact_mod_cast (show ⌈t-1/2⌉ + 1 ≤ i by omega)
    have hr : ¬ (i:ℝ)<t-1/2 := by linarith
    have hl : t+1/2≤(i:ℝ) := by linarith
    simp only [bit,decide_eq_true_eq,hr,hl,ite_true,ite_false,ne_of_gt hi]; norm_num

lemma concave_line_index (t : ℝ) (i : ℤ) :
    lineIndex (fun j => -((j:ℝ)-t)^2) i = if i=⌊t+1/2⌋ then -1 else 0 := by
  have h₁ := Int.floor_le (t+1/2)
  have h₂ := Int.lt_floor_add_one (t+1/2)
  have right_iff : -(((i+1:ℤ):ℝ)-t)^2 < -((i:ℝ)-t)^2 ↔ t-1/2<(i:ℝ) := by
    push_cast
    constructor <;> intro h <;> nlinarith
  have left_iff : -(((i-1:ℤ):ℝ)-t)^2 ≤ -((i:ℝ)-t)^2 ↔ (i:ℝ)≤t+1/2 := by
    push_cast
    constructor <;> intro h <;> nlinarith
  unfold lineIndex
  simp only [right_iff,left_iff]
  rcases lt_trichotomy i ⌊t+1/2⌋ with hi|hi|hi
  · have hir : (i:ℝ) ≤ (⌊t+1/2⌋:ℝ)-1 := by exact_mod_cast (show i≤⌊t+1/2⌋-1 by omega)
    have hr : ¬ t-1/2<(i:ℝ) := by linarith
    have hl : (i:ℝ)≤t+1/2 := by linarith
    simp only [bit,decide_eq_true_eq,hr,hl,ite_true,ite_false,ne_of_lt hi]; norm_num
  · have hir : (i:ℝ) = (⌊t+1/2⌋:ℝ) := by exact_mod_cast hi
    have hr : t-1/2<(i:ℝ) := by linarith
    have hl : (i:ℝ)≤t+1/2 := by linarith
    simp only [bit,decide_eq_true_eq,hr,hl,ite_true]; simp [hi]
  · have hir : (⌊t+1/2⌋:ℝ)+1 ≤ (i:ℝ) := by exact_mod_cast (show ⌊t+1/2⌋ + 1 ≤ i by omega)
    have hr : t-1/2<(i:ℝ) := by linarith
    have hl : ¬ (i:ℝ)≤t+1/2 := by linarith
    simp only [bit,decide_eq_true_eq,hr,hl,ite_true,ite_false,ne_of_gt hi]; norm_num

end
end StrictInverseFirstPower.Grid

end

end OAI
