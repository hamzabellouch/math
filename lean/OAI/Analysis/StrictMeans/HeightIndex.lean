import OAI.Analysis.StrictMeans.IndexConservation

namespace OAI

section
open Set Function
namespace StrictInverseFirstPower.Grid
noncomputable section
variable {V : Type*} [LinearOrder V]

def heightRank (u : V → ℝ) (v : V) : Lex (ℝ × V) := toLex (u v,v)

omit [LinearOrder V] in
lemma heightRank_injective (u : V → ℝ) : Injective (heightRank u) := by
  intro a b h
  exact congrArg (fun t : Lex (ℝ × V) => (ofLex t).2) h

lemma heightRank_lt_imp_le {u : V → ℝ} {a b : V} (h : heightRank u a < heightRank u b) : u a ≤ u b := by
  rw [heightRank,heightRank,Prod.Lex.toLex_lt_toLex] at h
  rcases h with h | h
  · exact h.le
  · exact h.1.le

lemma heightRank_not_lt_imp_le {u : V → ℝ} {a b : V} (h : ¬ heightRank u a < heightRank u b) : u b ≤ u a := by
  by_contra hh
  apply h
  rw [heightRank,heightRank,Prod.Lex.toLex_lt_toLex]
  exact Or.inl (lt_of_not_ge hh)

lemma heightRank_signBound {u : V → ℝ} {a b : V} {g e : ℝ}
    (herror : |u a-u b-g| ≤ e) :
    signBound (decide (heightRank u a < heightRank u b)) g e := by
  by_cases h : heightRank u a < heightRank u b
  · have hh := heightRank_lt_imp_le h
    have he := (abs_le.mp herror).1
    simpa [signBound,h] using (show g ≤ e by linarith)
  · have hh := heightRank_not_lt_imp_le h
    have he := (abs_le.mp herror).2
    simpa [signBound,h] using (show -e ≤ g by linarith)

variable [AddCommGroup V]

def heightIndex (u : V → ℝ) (x y v : V) : ℤ := meshIndex (heightRank u) x y v

lemma heightIndex_regular {u : V → ℝ} {x y v : V} {gx gy e : ℝ}
    (hreg : 2*e < |gx| ∨ 2*e < |gy|) (he : 0 ≤ e)
    (h₀ : |u (v+x)-u v-gx| ≤ e)
    (h₁ : |u (v+x+y)-u v-(gx+gy)| ≤ e)
    (h₂ : |u (v+y)-u v-gy| ≤ e)
    (h₃ : |u (v-x)-u v-(-gx)| ≤ e)
    (h₄ : |u (v-(x+y))-u v-(-gx-gy)| ≤ e)
    (h₅ : |u (v-y)-u v-(-gy)| ≤ e) : heightIndex u x y v = 0 := by
  rw [heightIndex,meshIndex_eq_linkIndex]
  exact regular_link hreg he (heightRank_signBound h₀) (heightRank_signBound h₁)
    (heightRank_signBound h₂) (heightRank_signBound h₃) (heightRank_signBound h₄)
    (heightRank_signBound h₅)

lemma heightIndex_finite_change {u w : V → ℝ} (hfin : {v | u v ≠ w v}.Finite)
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (hd : x+y ≠ 0) :
    ∑ᶠ v, (heightIndex u x y v-heightIndex w x y v) = 0 := by
  apply meshIndex_change_finsum_zero (heightRank_injective u) (heightRank_injective w) _ hx hy hd
  exact hfin.subset fun v hv he => hv (by simp only [heightRank,he])

end
end StrictInverseFirstPower.Grid

end

end OAI
