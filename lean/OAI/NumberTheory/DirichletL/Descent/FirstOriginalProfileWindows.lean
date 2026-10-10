import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileCells

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseMomentFirstProfileUniform
local notation "O" => ActualEisensteinCubic.O
theorem original_cell_windows (g₁ g₂ : 𝓢(ℝ,ℂ)) (m₁ m₂ bcap : ℝ)
    (Bρ : Fin 9→ℝ)
    (hm₁ : 0≤m₁) (hm₂ : 0≤m₂)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂)
    (hBρ : ∀i,0≤Bρ i) :
    ∃(w₁ w₂ : 𝓢(ℝ,ℂ))(U₀ : Fin 9→𝓢(ℝ,ℂ))(M₀ : Fin 9→ℝ)(a b : ℝ),
      0<a ∧ a≤b ∧ HasCompactSupport (w₁ : ℝ→ℂ) ∧ HasCompactSupport (w₂ : ℝ→ℂ) ∧
      tsupport (w₁ : ℝ→ℂ)⊆Set.Icc a b ∧ tsupport (w₂ : ℝ→ℂ)⊆Set.Icc a b ∧
      (∀i,0≤M₀ i) ∧ (∀i,HasCompactSupport (U₀ i : ℝ→ℂ)) ∧
      (∀i,Function.support (U₀ i)⊆Set.Icc (-M₀ i) (M₀ i)) ∧
      ∀{ι : Type*}[DecidableEq ι]
      (p : ι→O)(_hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O)) (Y : ℝ)
      (C₁ C₂ : OriginalIndex ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ)
      (ρ : Fin 9→ℝ)(c₁ c₂ θ₁ θ₂ : ℝ),
      0<T₁ → 0<T₂ → (∀i,|ρ i|≤Bρ i) →
      1≤c₁ → c₁≤bcap → 1≤c₂ → c₂≤bcap →
      let source := sourceCell (originalNorms p)
        (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) k
      let F := pool
      let selector : OriginalIndex ι→Finset ι→ℂ := fun _=>commonSelector p (fun _=>1) l
      let A₁ := leftNorm p
      let A₂ := rightNorm p
      let C := commonNorm p
      let R := activeNorm p
      let d := fun x : OriginalIndex ι=>divisorElement p x.1
      let h := fun x : OriginalIndex ι=>x.2.2
      let s := rawScales k l T₁ T₂
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
  obtain ⟨w₁,w₂,U,M,a,b,ha,hab,hwc₁,hwc₂,hws₁,hws₂,hM,hUc,hUs,he⟩ :=
    actual_first_child_windows g₁ g₂ m₁ m₂ bcap (fun _=>1) (fun _=>2) Bρ
      hm₁ hm₂ hg₁ hg₂ (by intro i;norm_num) (by intro i;norm_num) hBρ
  refine ⟨w₁,w₂,U,M,a,b,ha,hab,hwc₁,hwc₂,hws₁,hws₂,hM,hUc,hUs,?_⟩
  intro ι _ p hp _ hg pool Q labels Y C₁ C₂ k l T₁ T₂ ρ c₁ c₂ θ₁ θ₂
    hT₁ hT₂ hρ hc₁ hcb₁ hc₂ hcb₂ source F selector A₁ A₂ C R d h s
  apply he p hp hg source F selector C₁ C₂ A₁ A₂ C R d h s ρ c₁ c₂ θ₁ θ₂
    (rawScales_pos k l T₁ T₂ hT₁ hT₂) hρ hc₁ hcb₁ hc₂ hcb₂
  intro x hx j hj hn
  exact actual_original_cell_ratios p hp hg _ (fun _ _=>1) C₁ C₂
    (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p)
    (fun x=>divisorElement p x.1) (fun x=>x.2.2)
    (original_source_norms_ge_one p hp pool Q labels Y) k l T₁ T₂ x hx j hn

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
