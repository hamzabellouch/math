import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileData

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open CompletedHeight FourierBridge
open InverseMomentFirstProfileUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι κ : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

include hp in
lemma physical_rows_congr_positive (F : Finset ι) (selector C₁ C₂ : Finset ι→ℂ)
    (W₁ W₂ V₁ V₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : O)
    (hA₁ : 0<A₁) (hA₂ : 0<A₂) (hC : 0<C)
    (h₁ : ∀x,0<x→W₁ x=V₁ x) (h₂ : ∀x,0<x→W₂ x=V₂ x) :
    firstBlockedPhysicalRows p hg F selector C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h=
      firstBlockedPhysicalRows p hg F selector C₁ C₂ V₁ V₂ Φ A₁ A₂ C R K d h := by
  unfold firstBlockedPhysicalRows
  apply Finset.sum_congr rfl
  intro j hj
  have he₁ := h₁ (A₁*C*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1)
    (mul_pos (mul_pos (mul_pos hA₁ hC) (primeProductNorm_pos p hp _)) (primeProductNorm_pos p hp _))
  have he₂ := h₂ (A₂*C*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2)
    (mul_pos (mul_pos (mul_pos hA₂ hC) (primeProductNorm_pos p hp _)) (primeProductNorm_pos p hp _))
  simp [firstNormProfile,firstCommonNorms,he₁,he₂]

include hp in
lemma physical_family_congr_positive (S : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ→Finset ι→ℂ) (w : κ→ℂ)
    (W₁ W₂ V₁ V₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R : κ→ℝ) (K : ℝ)
    (d h : κ→O) (s : Fin 9→ℝ) (hs : ∀i,0<s i)
    (hpos : ∀x∈S,0<A₁ x ∧ 0<A₂ x ∧ 0<C x)
    (h₁ : ∀x,0<x→W₁ x=V₁ x) (h₂ : ∀x,0<x→W₂ x=V₂ x) :
    firstFamilyPhysicalRows p hg S F selector C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s=
      firstFamilyPhysicalRows p hg S F selector C₁ C₂ w V₁ V₂ Φ A₁ A₂ C R K d h s := by
  unfold firstFamilyPhysicalRows
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  exact physical_rows_congr_positive p hp hg F (selector x) (C₁ x) (C₂ x) _ _ _ _ Φ
    (A₁ x) (A₂ x) (C x) (R x) K (d x) (h x) (hpos x hx).1 (hpos x hx).2.1 (hpos x hx).2.2
    (fun y hy=>h₁ _ (div_pos hy (mul_pos (mul_pos (mul_pos (hs 0) (hs 2)) (hs 5)) (hs 7))))
    (fun y hy=>h₂ _ (div_pos hy (mul_pos (mul_pos (mul_pos (hs 1) (hs 2)) (hs 5)) (hs 8))))

include hp in

theorem original_family_profiles (S : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ→Finset ι→ℂ) (w : κ→ℂ)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hsom : Function.support om⊆Set.Icc a b)
    (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R : κ→ℝ) (K X theta : ℝ)
    (d h : κ→O) (s : Fin 9→ℝ) (hs : ∀i,0<s i)
    (hpos : ∀x∈S,0<A₁ x ∧ 0<A₂ x ∧ 0<C x)
    (hX : 0<X) (hleft : s 0*s 2*s 5*s 7=X) (hright : s 1*s 2*s 5*s 8=X) :
    firstFamilyPhysicalRows p hg S F selector C₁ C₂ w
      (fun y=>star (normTwistedSource om theta ((s 0*s 2*s 5*s 7)*y/X)))
      (fun y=>normTwistedSource om theta ((s 1*s 2*s 5*s 8)*y/X)) Φ A₁ A₂ C R K d h s=
    firstFamilyPhysicalRows p hg S F selector C₁ C₂ w
      (positiveSource (priorityLogWindow om a b ha hsom true) 1 (-theta))
      (positiveSource (priorityLogWindow om a b ha hsom false) 1 theta) Φ A₁ A₂ C R K d h s := by
  apply physical_family_congr_positive p hp hg S F selector C₁ C₂ w _ _ _ _ Φ A₁ A₂ C R K d h s hs hpos
  · intro y hy
    rw [hleft,mul_div_cancel_left₀ y (ne_of_gt hX)]
    exact (actual_old_profile om a b ha hsom theta y hy).2.symm
  · intro y hy
    rw [hright,mul_div_cancel_left₀ y (ne_of_gt hX)]
    exact (actual_old_profile om a b ha hsom theta y hy).1.symm

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
