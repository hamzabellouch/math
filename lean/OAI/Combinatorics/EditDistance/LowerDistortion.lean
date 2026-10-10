import OAI.Combinatorics.EditDistance.BinaryEmbedding
import OAI.Combinatorics.EditDistance.Distortion
import OAI.Combinatorics.EditDistance.Families

namespace OAI

/-!
# Distortion lower bounds from separated finite word families
-/

namespace EditLower
open EditDistortion EditFamily EditCode EditAverage EditFourier

variable {p n A t : ℕ} {α Q : ℝ} (F : Family p n A α Q)
  (label : Fin A ↪ (Fin t → Bool))

def codeWord (z : F.State) : List Bool := encode label (List.ofFn (F.word z))
def codeSet : Set (List Bool) := Set.range (codeWord F label)
def codePoint (z : F.State) : codeSet F label := ⟨codeWord F label z,⟨z,rfl⟩⟩

lemma codeSet_finite : (codeSet F label).Finite := Set.finite_range _
lemma codeSet_nonempty : (codeSet F label).Nonempty := ⟨_,⟨0,rfl⟩⟩
lemma codeSet_length (x : List Bool) (hx : x ∈ codeSet F label) : x.length = width t*n := by
  obtain ⟨z,rfl⟩ := hx
  simp only [codeWord,encode_length,List.length_ofFn]

lemma far_after_code (hp : 1 < p) (z : F.State) :
    (n : ℝ)*α ≤ 4*(edit (codeWord F label z) (codeWord F label (z+F.v)) : ℝ) := by
  have hf := F.far z 1 (by omega) hp
  simp only [one_nsmul] at hf
  have hc := indel_code_lower label label.injective (List.ofFn (F.word z))
    (List.ofFn (F.word (z+F.v))) 0 0
  simp only [padded,List.replicate_zero,List.append_nil] at hc
  have he := indel_le_two_edit (codeWord F label z) (codeWord F label (z+F.v))
  have hcR : (indel (List.ofFn (F.word z)) (List.ofFn (F.word (z+F.v))) : ℝ) ≤
      2*(indel (codeWord F label z) (codeWord F label (z+F.v)) : ℝ) := by exact_mod_cast hc
  have heR : (indel (codeWord F label z) (codeWord F label (z+F.v)) : ℝ) ≤
      2*(edit (codeWord F label z) (codeWord F label (z+F.v)) : ℝ) := by exact_mod_cast he
  linarith

lemma codeSet_nontrivial (hp : 1 < p) (hn : 0 < n) (ha : 0 < α) : Nontrivial (codeSet F label) := by
  have h := far_after_code F label hp 0
  refine ⟨⟨codePoint F label 0,codePoint F label (0+F.v),?_⟩⟩
  intro he
  have he' : codeWord F label 0 = codeWord F label (0+F.v) := congrArg Subtype.val he
  rw [←he',edit_real_diag] at h
  have : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith

theorem family_distortion (hp : 1 < p) (hn : 0 < n) (ha : 0 < α)
    (f : codeSet F label ↪ L1) :
    α ≤ 4*(width t : ℝ)*Q*distortion (fun x y : codeSet F label => (edit x.val y.val : ℝ)) f := by
  classical
  let : Fintype (codeSet F label) := (codeSet_finite F label).fintype
  let : Nontrivial (codeSet F label) := codeSet_nontrivial F label hp hn ha
  let ρ : codeSet F label → codeSet F label → ℝ := fun x y => (edit x.val y.val : ℝ)
  obtain ⟨U,V,hU,hV,hD,hu,hv⟩ := distortion_constants ρ
    (fun x => edit_real_diag x.val)
    (fun x y hxy => edit_real_pos x.val y.val (fun h => hxy (Subtype.ext h))) f
  let C : ℝ := U*(width t : ℝ)*n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hwR : (0 : ℝ) < width t := by exact_mod_cast EditCode.width_pos (t := t)
  have hC : 0 < C := by dsimp [C]; positivity
  let H : F.State → L1 := fun z => C⁻¹ • f (codePoint F label z)
  have hnorm (z e : F.State) : ‖H (z+e)-H z‖ =
      ‖f (codePoint F label (z+e))-f (codePoint F label z)‖/C := by
    simp only [H,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hC),div_eq_mul_inv,mul_comm]
  have hnorm' (z e : F.State) : ‖f (codePoint F label (z+e))-f (codePoint F label z)‖ =
      C*‖H (z+e)-H z‖ := by rw [hnorm]; field_simp
  have hcheap (e : F.State) (r : ℝ) (hr : (e,r) ∈ F.steps) : variation H e ≤ r := by
    unfold variation
    rw [←avg_const (X := F.State) r]
    apply avg_mono
    intro z
    rw [hnorm,div_le_iff₀ hC,norm_sub_rev]
    have h1 := hu (codePoint F label z) (codePoint F label (z+e))
    have h2 := edit_le_indel (codeWord F label z) (codeWord F label (z+e))
    have h3 := indel_code_upper label (List.ofFn (F.word z)) (List.ofFn (F.word (z+e)))
    have h23 : (edit (codeWord F label z) (codeWord F label (z+e)) : ℝ) ≤
        (width t : ℝ)*(indel (List.ofFn (F.word z)) (List.ofFn (F.word (z+e))) : ℝ) := by
      exact_mod_cast h2.trans h3
    have h4 := F.cheap e r hr z
    change ‖f (codePoint F label z)-f (codePoint F label (z+e))‖ ≤
      U*(edit (codeWord F label z) (codeWord F label (z+e)) : ℝ) at h1
    calc
      _ ≤ U*((width t : ℝ)*((n : ℝ)*r)) := h1.trans (mul_le_mul_of_nonneg_left
        (h23.trans (mul_le_mul_of_nonneg_left h4 hwR.le)) hU.le)
      _ = r*C := by dsimp [C]; ring
  have hbound := F.control H hcheap 1 (by omega) hp
  simp only [one_nsmul] at hbound
  have hfar (z : F.State) : (n : ℝ)*α ≤ 4*V*C*‖H (z+F.v)-H z‖ := by
    have h1 := far_after_code F label hp z
    have h2 := hv (codePoint F label z) (codePoint F label (z+F.v))
    change (edit (codeWord F label z) (codeWord F label (z+F.v)) : ℝ) ≤
      V*‖f (codePoint F label z)-f (codePoint F label (z+F.v))‖ at h2
    rw [norm_sub_rev,hnorm'] at h2
    nlinarith
  have havg : (n : ℝ)*α ≤ 4*V*C*variation H F.v := by
    change (n : ℝ)*α ≤ 4*V*C*avg (fun z => ‖H (z+F.v)-H z‖)
    rw [←avg_mul,←avg_const (X := F.State) ((n : ℝ)*α)]
    exact avg_mono hfar
  have hfinal : (n : ℝ)*α ≤ (n : ℝ)*(4*(width t : ℝ)*Q*(U*V)) := by
    calc
      _ ≤ 4*V*C*Q := havg.trans (mul_le_mul_of_nonneg_left hbound (by positivity))
      _ = _ := by dsimp [C]; ring
  have hcancel := (mul_le_mul_iff_right₀ hnR).mp hfinal
  change α ≤ 4*(width t : ℝ)*Q*distortion ρ f
  rw [hD]
  exact hcancel

end EditLower

end OAI
