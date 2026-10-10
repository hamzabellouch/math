import OAI.Analysis.StrictMeans.HessianLocal

namespace OAI

section
namespace StrictInverseFirstPower.Grid

def bit (b : Bool) : ℤ := if b then 1 else 0

def linkIndex (b₀ b₁ b₂ b₃ b₄ b₅ : Bool) : ℤ :=
  1 - (bit b₀+bit b₁+bit b₂+bit b₃+bit b₄+bit b₅) +
    (bit b₀*bit b₁+bit b₁*bit b₂+bit b₂*bit b₃+
      bit b₃*bit b₄+bit b₄*bit b₅+bit b₅*bit b₀)

def signBound (b : Bool) (t e : ℝ) : Prop := if b then t ≤ e else -e ≤ t

lemma linkIndex_rotate (a b c d e f : Bool) : linkIndex a b c d e f = linkIndex b c d e f a := by
  unfold linkIndex
  ring

lemma regular_link_xpos {gx gy e : ℝ} {b₀ b₁ b₂ b₃ b₄ b₅ : Bool}
    (hx : 2*e < gx) (he : 0 ≤ e)
    (h₀ : signBound b₀ gx e) (h₁ : signBound b₁ (gx+gy) e)
    (h₂ : signBound b₂ gy e) (h₃ : signBound b₃ (-gx) e)
    (h₄ : signBound b₄ (-gx-gy) e) (h₅ : signBound b₅ (-gy) e) :
    linkIndex b₀ b₁ b₂ b₃ b₄ b₅ = 0 := by
  have hb₀ : b₀ = false := by cases b₀ <;> simp_all [signBound]; linarith
  have hb₃ : b₃ = true := by cases b₃ <;> simp_all [signBound]; linarith
  subst b₀; subst b₃
  cases b₁ <;> cases b₂ <;> cases b₄ <;> cases b₅ <;>
    norm_num [linkIndex,bit,signBound] at * <;> linarith

lemma regular_link_xneg {gx gy e : ℝ} {b₀ b₁ b₂ b₃ b₄ b₅ : Bool}
    (hx : gx < -2*e) (he : 0 ≤ e)
    (h₀ : signBound b₀ gx e) (h₁ : signBound b₁ (gx+gy) e)
    (h₂ : signBound b₂ gy e) (h₃ : signBound b₃ (-gx) e)
    (h₄ : signBound b₄ (-gx-gy) e) (h₅ : signBound b₅ (-gy) e) :
    linkIndex b₀ b₁ b₂ b₃ b₄ b₅ = 0 := by
  rw [linkIndex_rotate,linkIndex_rotate,linkIndex_rotate]
  apply regular_link_xpos (gx := -gx) (gy := -gy) (by linarith) he h₃
  · simpa only [sub_eq_add_neg] using h₄
  · exact h₅
  · simpa using h₀
  · simpa using h₁
  · simpa using h₂

lemma linkIndex_reverse (a b c d e f : Bool) : linkIndex a b c d e f = linkIndex c b a f e d := by
  unfold linkIndex
  ring

lemma regular_link {gx gy e : ℝ} {b₀ b₁ b₂ b₃ b₄ b₅ : Bool}
    (hreg : 2*e < |gx| ∨ 2*e < |gy|) (he : 0 ≤ e)
    (h₀ : signBound b₀ gx e) (h₁ : signBound b₁ (gx+gy) e)
    (h₂ : signBound b₂ gy e) (h₃ : signBound b₃ (-gx) e)
    (h₄ : signBound b₄ (-gx-gy) e) (h₅ : signBound b₅ (-gy) e) :
    linkIndex b₀ b₁ b₂ b₃ b₄ b₅ = 0 := by
  have hbase : ∀ {x y : ℝ} {a b c d e' f : Bool}, 2*e < |x| →
      signBound a x e → signBound b (x+y) e → signBound c y e →
      signBound d (-x) e → signBound e' (-x-y) e → signBound f (-y) e →
      linkIndex a b c d e' f = 0 := by
    intro x y a b c d e' f hx ha hb hc hd he' hf
    rcases lt_abs.mp hx with hp | hn
    · exact regular_link_xpos hp he ha hb hc hd he' hf
    · exact regular_link_xneg (by linarith) he ha hb hc hd he' hf
  rcases hreg with hx | hy
  · exact hbase hx h₀ h₁ h₂ h₃ h₄ h₅
  · rw [linkIndex_reverse]
    exact hbase hy h₂ (by simpa [add_comm] using h₁) h₀ h₅
      (by convert h₄ using 1; ring) h₃

end StrictInverseFirstPower.Grid

end

end OAI
