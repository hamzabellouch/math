import OAI.Analysis.StrictMeans.GridLink

namespace OAI

section
namespace StrictInverseFirstPower.Grid
noncomputable section

variable {V L : Type*} [LinearOrder L]

def rankBit (r : V → L) (a b : V) : ℤ := if r a < r b then 1 else 0

lemma rankBit_complement {r : V → L} (hr : Function.Injective r) {a b : V} (hab : a ≠ b) :
    rankBit r a b + rankBit r b a = 1 := by
  have hne := hr.ne hab
  rcases lt_or_gt_of_ne hne with h | h <;> simp [rankBit,h,not_lt_of_gt h]

def topBit (r : V → L) (a b c : V) : ℤ := rankBit r b a * rankBit r c a

lemma topBit_sum {r : V → L} (hr : Function.Injective r) {a b c : V}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    topBit r a b c + topBit r b c a + topBit r c a b = 1 := by
  have hab' := hr.ne hab
  have hbc' := hr.ne hbc
  have hac' := hr.ne hac
  rcases lt_or_gt_of_ne hab' with h₁ | h₁ <;>
    rcases lt_or_gt_of_ne hbc' with h₂ | h₂ <;>
    rcases lt_or_gt_of_ne hac' with h₃ | h₃ <;>
    simp_all [topBit,rankBit,not_lt_of_gt] <;> order

variable [AddCommGroup V]

lemma ne_self_add_of_ne_zero (a : V) {b : V} (hb : b ≠ 0) : a ≠ a+b := by
  intro h
  exact hb (add_left_cancel (show a+b=a+0 by simpa using h.symm))

def edgeFlag (r : V → L) (s v : V) : ℤ := rankBit r (v+s) v

def lowerTop₀ (r : V → L) (x y v : V) : ℤ := topBit r v (v+x) (v+x+y)
def lowerTop₁ (r : V → L) (x y v : V) : ℤ := topBit r (v+x) (v+x+y) v
def lowerTop₂ (r : V → L) (x y v : V) : ℤ := topBit r (v+x+y) v (v+x)
def upperTop₀ (r : V → L) (x y v : V) : ℤ := topBit r v (v+y) (v+x+y)
def upperTop₁ (r : V → L) (x y v : V) : ℤ := topBit r (v+y) (v+x+y) v
def upperTop₂ (r : V → L) (x y v : V) : ℤ := topBit r (v+x+y) v (v+y)

lemma lowerTop_sum {r : V → L} (hr : Function.Injective r) {x y : V}
    (hx : x ≠ 0) (hy : y ≠ 0) (hd : x+y ≠ 0) (v : V) :
    lowerTop₀ r x y v + lowerTop₁ r x y v + lowerTop₂ r x y v = 1 := by
  apply topBit_sum hr
  · exact ne_self_add_of_ne_zero v hx
  · exact ne_self_add_of_ne_zero (v+x) hy
  · simpa only [add_assoc,ne_eq,left_eq_add] using hd

lemma upperTop_sum {r : V → L} (hr : Function.Injective r) {x y : V}
    (hx : x ≠ 0) (hy : y ≠ 0) (hd : x+y ≠ 0) (v : V) :
    upperTop₀ r x y v + upperTop₁ r x y v + upperTop₂ r x y v = 1 := by
  apply topBit_sum hr
  · exact ne_self_add_of_ne_zero v hy
  · simpa only [add_right_comm] using ne_self_add_of_ne_zero (v+y) hx
  · simpa only [add_assoc,ne_eq,left_eq_add] using hd

def meshIndex (r : V → L) (x y v : V) : ℤ :=
  1 - (edgeFlag r x v + rankBit r (v-x) v +
      edgeFlag r y v + rankBit r (v-y) v +
      edgeFlag r (x+y) v + rankBit r (v-(x+y)) v) +
    (lowerTop₀ r x y v + lowerTop₁ r x y (v-x) + lowerTop₂ r x y (v-(x+y)) +
      upperTop₀ r x y v + upperTop₁ r x y (v-y) + upperTop₂ r x y (v-(x+y)))

lemma meshIndex_eq_linkIndex (r : V → L) (x y v : V) :
    meshIndex r x y v = linkIndex
      (decide (r (v+x) < r v)) (decide (r (v+x+y) < r v))
      (decide (r (v+y) < r v)) (decide (r (v-x) < r v))
      (decide (r (v-(x+y)) < r v)) (decide (r (v-y) < r v)) := by
  have ha : v-(x+y)+x = v-y := by abel
  have hc : v-y+x+y = v+x := by abel
  have hd : v-(x+y)+y = v-x := by abel
  simp only [meshIndex,lowerTop₀,lowerTop₁,lowerTop₂,upperTop₀,upperTop₁,upperTop₂,
    topBit,edgeFlag,sub_add_cancel,ha,hc,hd,linkIndex,rankBit,bit,decide_eq_true_eq,add_assoc]
  ring

lemma meshIndex_eq_divergence {r : V → L} (hr : Function.Injective r) {x y : V}
    (hx : x ≠ 0) (hy : y ≠ 0) (hd : x+y ≠ 0) (v : V) :
    meshIndex r x y v =
      (edgeFlag r x (v-x)-edgeFlag r x v) +
      (edgeFlag r y (v-y)-edgeFlag r y v) +
      (edgeFlag r (x+y) (v-(x+y))-edgeFlag r (x+y) v) +
      (lowerTop₁ r x y (v-x)-lowerTop₁ r x y v) +
      (lowerTop₂ r x y (v-(x+y))-lowerTop₂ r x y v) +
      (upperTop₁ r x y (v-y)-upperTop₁ r x y v) +
      (upperTop₂ r x y (v-(x+y))-upperTop₂ r x y v) := by
  have hlow := lowerTop_sum hr hx hy hd v
  have hup := upperTop_sum hr hx hy hd v
  have h₁ : edgeFlag r x (v-x) + rankBit r (v-x) v = 1 := by
    simpa only [edgeFlag,sub_add_cancel] using rankBit_complement hr (show v ≠ v-x by simpa only [sub_eq_add_neg] using ne_self_add_of_ne_zero v (neg_ne_zero.mpr hx))
  have h₂ : edgeFlag r y (v-y) + rankBit r (v-y) v = 1 := by
    simpa only [edgeFlag,sub_add_cancel] using rankBit_complement hr (show v ≠ v-y by simpa only [sub_eq_add_neg] using ne_self_add_of_ne_zero v (neg_ne_zero.mpr hy))
  have h₃ : edgeFlag r (x+y) (v-(x+y)) + rankBit r (v-(x+y)) v = 1 := by
    simpa only [edgeFlag,sub_add_cancel] using rankBit_complement hr (show v ≠ v-(x+y) by simpa only [sub_eq_add_neg] using ne_self_add_of_ne_zero v (neg_ne_zero.mpr hd))
  unfold meshIndex
  omega

end
end StrictInverseFirstPower.Grid

end

end OAI
