import OAI.NumberTheory.DirichletL.Descent.FirstChildWindows

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstChildWindows
open InverseMoment InverseMomentFirstProfileUniform ActualEisensteinCubic
open FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

def actualOuterRatios {ι : Type*} (p : ι→O) (A₁ A₂ C R : ℝ) (d h : O)
    (j : FirstCommonIndex ι) (s : Fin 9→ℝ) (i : Fin 7) : ℝ :=
  firstCommonNorms p A₁ A₂ C R d h j (outerIndex i)/s (outerIndex i)

theorem actual_first_child_windows (g₁ g₂ : 𝓢(ℝ,ℂ)) (m₁ m₂ bcap : ℝ)
    (lo hi : Fin 7→ℝ) (Bρ : Fin 9→ℝ)
    (hm₁ : 0≤m₁) (hm₂ : 0≤m₂)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂)
    (hlo : ∀i,0<lo i) (hhi : ∀i,lo i≤hi i) (hBρ : ∀i,0≤Bρ i) :
    ∃(w₁ w₂ : 𝓢(ℝ,ℂ))(U₀ : Fin 9→𝓢(ℝ,ℂ))(M₀ : Fin 9→ℝ)(a b : ℝ),
      0<a ∧ a≤b ∧ HasCompactSupport (w₁ : ℝ→ℂ) ∧ HasCompactSupport (w₂ : ℝ→ℂ) ∧
      tsupport (w₁ : ℝ→ℂ)⊆Set.Icc a b ∧ tsupport (w₂ : ℝ→ℂ)⊆Set.Icc a b ∧
      (∀i,0≤M₀ i) ∧ (∀i,HasCompactSupport (U₀ i : ℝ→ℂ)) ∧
      (∀i,Function.support (U₀ i)⊆Set.Icc (-M₀ i) (M₀ i)) ∧
      ∀{ι κ : Type*}[DecidableEq ι][DecidableEq κ]
      (p : ι→O)(_hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (source : Finset κ)(F : Finset ι)(selector C₁ C₂ : κ→Finset ι→ℂ)
      (A₁ A₂ C R : κ→ℝ)(d h : κ→O)(s : Fin 9→ℝ)
      (ρ : Fin 9→ℝ)(c₁ c₂ θ₁ θ₂ : ℝ),
      (∀i,0<s i) → (∀i,|ρ i|≤Bρ i) →
      1≤c₁ → c₁≤bcap → 1≤c₂ → c₂≤bcap →
      (∀x∈source,∀j∈firstCommonIndices F,
        selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j≠0 →
        ∀i,actualOuterRatios p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j s i∈Set.Icc (lo i) (hi i)) →
      (∀x∈source,∀j∈firstCommonIndices F,
        selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j≠0 →
        positiveSource g₁ c₁ θ₁ (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7))≠0 →
        w₁ (primeProductNorm p j.2.2.1/s 7)=1) ∧
      (∀x∈source,∀j∈firstCommonIndices F,
        selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j≠0 →
        positiveSource g₂ c₂ θ₂ (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8))≠0 →
        w₂ (primeProductNorm p j.2.2.2/s 8)=1) ∧
      (∀x∈source,∀j∈firstCommonIndices F,
        selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j≠0 →
        w₁ (primeProductNorm p j.2.2.1/s 7)≠0 → w₂ (primeProductNorm p j.2.2.2/s 8)≠0 →
        ∀i,U₀ i (firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j) s i+ρ i)=1) := by
  obtain ⟨w₁,w₂,U,M,a,b,ha,hab,hwc₁,hwc₂,hws₁,hws₂,hM,hUc,hUs,hfresh₁,hfresh₂,hcut⟩ :=
    fixed_windows g₁ g₂ m₁ m₂ bcap lo hi Bρ hm₁ hm₂ hg₁ hg₂ hlo hhi hBρ
  refine ⟨w₁,w₂,U,M,a,b,ha,hab,hwc₁,hwc₂,hws₁,hws₂,hM,hUc,hUs,?_⟩
  intro ι κ _ _ p hp _ hg source F selector C₁ C₂ A₁ A₂ C R d h s ρ c₁ c₂ θ₁ θ₂
    hs hρ hc₁ hcb₁ hc₂ hcb₂ hblock
  refine ⟨?_,?_,?_⟩
  · intro x hx j hj hn hg₁n
    apply hfresh₁ c₁ θ₁ (A₁ x/s 0) (C x/s 2) (primeProductNorm p j.2.1/s 5) _
      hc₁ hcb₁ (hblock x hx j hj hn 0) (hblock x hx j hj hn 2) (hblock x hx j hj hn 5)
      (div_pos (primeProductNorm_pos p hp _) (hs 7))
    convert hg₁n using 2 ; ring
  · intro x hx j hj hn hg₂n
    apply hfresh₂ c₂ θ₂ (A₂ x/s 1) (C x/s 2) (primeProductNorm p j.2.1/s 5) _
      hc₂ hcb₂ (hblock x hx j hj hn 1) (hblock x hx j hj hn 2) (hblock x hx j hj hn 5)
      (div_pos (primeProductNorm_pos p hp _) (hs 8))
    convert hg₂n using 2 ; ring
  · intro x hx j hj hn hw₁ hw₂ i
    exact hcut (fun i=>firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j i/s i)
      ρ hρ (hblock x hx j hj hn) hw₁ hw₂ i

end SevenEighths.InverseMomentFirstChildWindows
end

end OAI
