import OAI.NumberTheory.CubicMoment.Estimates.NoncubePowerBounds

namespace OAI

/-! The nonexceptional sieve gap persists under the small enlargement of
`P Q² ≤ B` required by the dispersion localization. -/
noncomputable section
open Set
namespace CubicFirstMoment

theorem enlarged_noncube_exponent_gap {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ η γ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < γ ∧
      ∀ p q : ℝ, 0 ≤ p → 0 ≤ q → p+2*q ≤ 1+η →
      κ ≤ p+2*q → δ ≤ |p-1|+|q| → δ ≤ |p-1/3|+|q-1/3| →
      noncubeSieveExponent p q ≤ -γ := by
  obtain ⟨γ,hγ,hgap⟩ := uniform_noncube_exponent_gap hκ hδ
  let K : Set (ℝ × ℝ) := (Icc (0:ℝ) 2 ×ˢ Icc (0:ℝ) 2) ∩
    {x | κ ≤ x.1+2*x.2 ∧ δ ≤ |x.1-1|+|x.2| ∧
      δ ≤ |x.1-1/3|+|x.2-1/3| ∧ -γ/2 ≤ noncubeSieveExponent x.1 x.2}
  have h₁ : IsClosed {x : ℝ × ℝ | κ ≤ x.1+2*x.2} :=
    isClosed_le continuous_const (by fun_prop)
  have h₂ : IsClosed {x : ℝ × ℝ | δ ≤ |x.1-1|+|x.2|} :=
    isClosed_le continuous_const (by fun_prop)
  have h₃ : IsClosed {x : ℝ × ℝ | δ ≤ |x.1-1/3|+|x.2-1/3|} :=
    isClosed_le continuous_const (by fun_prop)
  have h₄ : IsClosed {x : ℝ × ℝ | -γ/2 ≤ noncubeSieveExponent x.1 x.2} :=
    isClosed_le continuous_const continuous_noncubeSieveExponent
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).inter_right
    (h₁.inter (h₂.inter (h₃.inter h₄)))
  have hpositive : ∀ x ∈ K, 0 < x.1+2*x.2-1 := by
    rintro ⟨p,q⟩ ⟨⟨⟨hp,_⟩,⟨hq,_⟩⟩,hlarge,hfirst,hbalanced,hbad⟩
    by_contra! h
    have hg := hgap p q hp hq (by linarith) hlarge hfirst hbalanced
    linarith
  by_cases hne : K.Nonempty
  · obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn hne (show
        Continuous (fun x : ℝ × ℝ => x.1+2*x.2-1) by fun_prop).continuousOn
    let η : ℝ := min 1 ((x.1+2*x.2-1)/2)
    have hη : 0 < η := lt_min (by norm_num) (by linarith [hpositive x hx])
    refine ⟨η,γ/2,hη,min_le_left _ _,by positivity,?_⟩
    intro p q hp hq hsize hlarge hfirst hbalanced
    by_contra! hbad
    have hmem : (p,q) ∈ K := ⟨⟨⟨hp,by
      have := min_le_left (1:ℝ) ((x.1+2*x.2-1)/2)
      change η ≤ 1 at this
      linarith⟩,⟨hq,by
      have := min_le_left (1:ℝ) ((x.1+2*x.2-1)/2)
      change η ≤ 1 at this
      linarith⟩⟩,hlarge,hfirst,hbalanced,by linarith⟩
    have hm := hmin hmem
    change x.1+2*x.2-1 ≤ p+2*q-1 at hm
    have he : η ≤ (x.1+2*x.2-1)/2 := min_le_right _ _
    linarith [hpositive x hx]
  · refine ⟨1,γ/2,by norm_num,le_rfl,by positivity,?_⟩
    intro p q hp hq hsize hlarge hfirst hbalanced
    by_contra! hbad
    apply hne
    exact ⟨(p,q),⟨⟨⟨hp,by linarith⟩,⟨hq,by linarith⟩⟩,
      hlarge,hfirst,hbalanced,by linarith⟩⟩

/-- The same enlargement allows all sieve epsilon losses to be absorbed. -/
theorem enlarged_noncube_ratio_saving {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ η γ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < γ ∧
      ∀ (B p q e : ℝ), 1 ≤ B → 0 ≤ p → 0 ≤ q → p+2*q ≤ 1+η →
      κ ≤ p+2*q → δ ≤ |p-1|+|q| → δ ≤ |p-1/3|+|q-1/3| → e ≤ γ/2 →
      B^e * min (pSieveRatio B (B^p) (B^q))
        (min (qSieveRatio B (B^p) (B^q)) (ordinarySieveRatio B (B^p) (B^q))) ≤
          3*B^(-γ/2) := by
  obtain ⟨η,γ,hη,hηhi,hγ,hgap⟩ := enlarged_noncube_exponent_gap hκ hδ
  refine ⟨η,γ,hη,hηhi,hγ,?_⟩
  intro B p q e hB hp hq hsize hlarge hfirst hbalanced he
  have hg := hgap p q hp hq hsize hlarge hfirst hbalanced
  calc
    _ ≤ B^e*(3*B^(noncubeSieveExponent p q)) :=
      mul_le_mul_of_nonneg_left (noncubeSieveRatio_le hB p q)
        (Real.rpow_nonneg (by linarith) _)
    _ = 3*B^(e+noncubeSieveExponent p q) := by
      rw [Real.rpow_add (by linarith : 0 < B)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hB (by linarith)) (by norm_num)

end CubicFirstMoment

end

end OAI
