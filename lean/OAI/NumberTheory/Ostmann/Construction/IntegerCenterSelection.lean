import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Construction

theorem exists_pair_avoiding_bad (B I : Finset ℤ) (T : ℤ) (hcard : 2*B.card<I.card) :
    ∃a∈I,a∉B ∧ T-a∉B := by
  classical
  let D := B∪B.image (fun b => T-b)
  have hD : D.card≤2*B.card := by
    have h₁ := Finset.card_union_le B (B.image (fun b => T-b))
    have h₂ := Finset.card_image_le (s := B) (f := fun b => T-b)
    dsimp [D]
    omega
  have hn : ¬I⊆D := by
    intro hs
    have hc := Finset.card_le_card hs
    omega
  obtain ⟨a,ha,had⟩ := Finset.not_subset.mp hn
  refine ⟨a,ha,?_,?_⟩
  · intro hb
    exact had (Finset.mem_union_left _ hb)
  · intro hb
    apply had
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨T-a,hb,?_⟩
    ring

def integerCenterWindow (μ w : ℝ) : Finset ℤ := Finset.Icc ⌈μ-w⌉ ⌊μ+w⌋

lemma mem_integerCenterWindow (μ w : ℝ) (a : ℤ) :
    a∈integerCenterWindow μ w ↔ |(a:ℝ)-μ|≤w := by
  rw [integerCenterWindow,Finset.mem_Icc,Int.ceil_le,Int.le_floor,abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

lemma integerCenterWindow_card_lower (μ w : ℝ) (hw : 1≤w) :
    2*w-1<((integerCenterWindow μ w).card:ℝ) := by
  have hc := Int.ceil_lt_add_one (μ-w)
  have hf := Int.lt_floor_add_one (μ+w)
  have hle : ⌈μ-w⌉≤⌊μ+w⌋+1 := by
    have h : (⌈μ-w⌉:ℝ)≤(⌊μ+w⌋:ℝ)+1 := by linarith
    exact_mod_cast h
  have he := Int.card_Icc_of_le _ _ hle
  have hr : ((integerCenterWindow μ w).card:ℝ)=(⌊μ+w⌋:ℝ)+1-(⌈μ-w⌉:ℝ) := by
    exact_mod_cast he
  rw [hr]
  linarith

theorem exists_pair_integer_centers (B : Finset ℤ) (T : ℤ) (w : ℝ)
    (hw : 2*(B.card:ℝ)+2≤w) :
    ∃a b : ℤ,a∉B ∧ b∉B ∧ a+b=T ∧
      |(a:ℝ)-(T:ℝ)/2|≤w ∧ |(b:ℝ)-(T:ℝ)/2|≤w := by
  have hc0 : 0≤(B.card:ℝ) := Nat.cast_nonneg _
  have hcard := integerCenterWindow_card_lower ((T:ℝ)/2) w (by linarith)
  have hN : 2*B.card<(integerCenterWindow ((T:ℝ)/2) w).card := by
    have hR : 2*(B.card:ℝ)<((integerCenterWindow ((T:ℝ)/2) w).card:ℝ) := by linarith
    exact_mod_cast hR
  obtain ⟨a,ha,haB,hbB⟩ := exists_pair_avoiding_bad B (integerCenterWindow ((T:ℝ)/2) w) T hN
  have habs := (mem_integerCenterWindow _ _ _).mp ha
  refine ⟨a,T-a,haB,hbB,by ring,habs,?_⟩
  have he : ((T-a:ℤ):ℝ)-(T:ℝ)/2 = -((a:ℝ)-(T:ℝ)/2) := by push_cast; ring
  rw [he,abs_neg]
  exact habs

theorem exists_triple_integer_centers (B : Finset ℤ) (T : ℤ) (w : ℝ)
    (hw : 4*(B.card:ℝ)+4≤w) :
    ∃a b c : ℤ,a∉B ∧ b∉B ∧ c∉B ∧ a+b+c=T ∧
      |(a:ℝ)-(T:ℝ)/3|≤w ∧ |(b:ℝ)-(T:ℝ)/3|≤w ∧ |(c:ℝ)-(T:ℝ)/3|≤w := by
  have hc0 : 0≤(B.card:ℝ) := Nat.cast_nonneg _
  have hcard := integerCenterWindow_card_lower ((T:ℝ)/3) w (by linarith)
  have hN : 2*B.card<(integerCenterWindow ((T:ℝ)/3) w).card := by
    have hR : 2*(B.card:ℝ)<((integerCenterWindow ((T:ℝ)/3) w).card:ℝ) := by linarith
    exact_mod_cast hR
  obtain ⟨a,ha,haB,_⟩ := exists_pair_avoiding_bad B (integerCenterWindow ((T:ℝ)/3) w) 0 hN
  have haabs := (mem_integerCenterWindow _ _ _).mp ha
  obtain ⟨b,c,hbB,hcB,hbc,hb,hc⟩ := exists_pair_integer_centers B (T-a) (w/2) (by linarith)
  refine ⟨a,b,c,haB,hbB,hcB,by omega,haabs,?_,?_⟩
  · have ha' := abs_le.mp haabs
    have hb' := abs_le.mp hb
    push_cast at hb'
    apply abs_le.mpr
    constructor <;> linarith
  · have ha' := abs_le.mp haabs
    have hc' := abs_le.mp hc
    push_cast at hc'
    apply abs_le.mpr
    constructor <;> linarith

end Ostmann.Construction

end

end OAI
