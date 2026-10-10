import OAI.NumberTheory.CubicMoment.Estimates.NoncubeExponents

namespace OAI

/-! Compactness makes the nonexceptional conductor saving uniform. -/

noncomputable section
open Set
namespace CubicFirstMoment

/-- With a positive conductor threshold and fixed neighborhoods of the two
exceptional shapes removed, one of the three sieve bounds saves a single
uniform positive power. -/
theorem uniform_noncube_exponent_gap {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ p q : ℝ, 0 ≤ p → 0 ≤ q → p+2*q ≤ 1 →
      κ ≤ p+2*q → δ ≤ |p-1|+|q| → δ ≤ |p-1/3|+|q-1/3| →
      noncubeSieveExponent p q ≤ -γ := by
  let K : Set (ℝ × ℝ) := (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) ∩
    {x | x.1+2*x.2 ≤ 1 ∧ κ ≤ x.1+2*x.2 ∧
      δ ≤ |x.1-1|+|x.2| ∧ δ ≤ |x.1-1/3|+|x.2-1/3|}
  have h₁ : IsClosed {x : ℝ × ℝ | x.1+2*x.2 ≤ 1} :=
    isClosed_le (by fun_prop) continuous_const
  have h₂ : IsClosed {x : ℝ × ℝ | κ ≤ x.1+2*x.2} :=
    isClosed_le continuous_const (by fun_prop)
  have h₃ : IsClosed {x : ℝ × ℝ | δ ≤ |x.1-1|+|x.2|} :=
    isClosed_le continuous_const (by fun_prop)
  have h₄ : IsClosed {x : ℝ × ℝ | δ ≤ |x.1-1/3|+|x.2-1/3|} :=
    isClosed_le continuous_const (by fun_prop)
  have hclosed := h₁.inter (h₂.inter (h₃.inter h₄))
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).inter_right hclosed
  have hneg : ∀ x ∈ K, noncubeSieveExponent x.1 x.2 < 0 := by
    rintro ⟨p,q⟩ ⟨⟨⟨hp,_⟩,⟨hq,_⟩⟩,hsize,hlarge,hfirst,hbalanced⟩
    apply noncubeSieveExponent_neg hp hq hsize (hκ.trans_le hlarge)
    · by_contra! h
      rcases h with ⟨rfl,rfl⟩
      norm_num at hfirst
      linarith
    · by_contra! h
      rcases h with ⟨rfl,rfl⟩
      norm_num at hbalanced
      linarith
  by_cases hne : K.Nonempty
  · obtain ⟨x,hx,hmax⟩ := hK.exists_isMaxOn hne continuous_noncubeSieveExponent.continuousOn
    refine ⟨-noncubeSieveExponent x.1 x.2/2,by linarith [hneg x hx],?_⟩
    intro p q hp hq hsize hlarge hfirst hbalanced
    have hp1 : p ≤ 1 := by linarith
    have hq1 : q ≤ 1 := by linarith
    have hmem : (p,q) ∈ K := ⟨⟨⟨hp,hp1⟩,⟨hq,hq1⟩⟩,hsize,hlarge,hfirst,hbalanced⟩
    have hm := hmax hmem
    have hn := hneg x hx
    change noncubeSieveExponent p q ≤ noncubeSieveExponent x.1 x.2 at hm
    linarith
  · refine ⟨1,by norm_num,?_⟩
    intro p q hp hq hsize hlarge hfirst hbalanced
    apply False.elim
    apply hne
    exact ⟨(p,q),⟨⟨⟨hp,by linarith⟩,⟨hq,by linarith⟩⟩,hsize,hlarge,hfirst,hbalanced⟩⟩

end CubicFirstMoment

end

end OAI
