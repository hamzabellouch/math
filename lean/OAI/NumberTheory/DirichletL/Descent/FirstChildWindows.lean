import OAI.NumberTheory.DirichletL.Inversion.SecondChildWindows
import OAI.NumberTheory.DirichletL.Descent.FirstUnequalRetainedEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseMomentFirstChildWindows
open InverseMoment InverseMomentFirstProfileUniform
open InverseSecondChildWindows

theorem fresh_three_window (g : 𝓢(ℝ,ℂ)) (m bcap : ℝ)
    (lo hi : Fin 3→ℝ) (hm : 0≤m)
    (hg : Function.support g⊆Set.Icc (-m) m)
    (hlo : ∀i,0<lo i) (hhi : ∀i,lo i≤hi i) :
    ∃(w : 𝓢(ℝ,ℂ))(a b : ℝ),0<a ∧ a≤b ∧ HasCompactSupport (w : ℝ→ℂ) ∧
      tsupport (w : ℝ→ℂ)⊆Set.Icc a b ∧
      ∀(c θ u v r n : ℝ),1≤c → c≤bcap →
        u∈Set.Icc (lo 0) (hi 0) → v∈Set.Icc (lo 1) (hi 1) → r∈Set.Icc (lo 2) (hi 2) →
        0<n → positiveSource g c θ (u*v*r*n)≠0 → w n=1 := by
  let R := m+Real.log bcap
  let a := Real.exp (-R)/(hi 0*hi 1*hi 2)
  let b := Real.exp R/(lo 0*lo 1*lo 2)
  have hhip (i : Fin 3) : 0<hi i := (hlo i).trans_le (hhi i)
  have hh0 := hhip 0
  have hh1 := hhip 1
  have hh2 := hhip 2
  have hl0 := hlo 0
  have hl1 := hlo 1
  have hl2 := hlo 2
  have ha : 0<a := by dsimp [a];positivity
  have hb : 0<b := by dsimp [b];positivity
  obtain ⟨w,hwc,hwone,hws⟩ := positive_cutoff a (a+b+1) ha (by linarith)
  refine ⟨w,a/2,a+b+2,half_pos ha,by linarith,hwc,by convert hws using 1; ring_nf,?_⟩
  intro c θ u v r n hc hcb hu hv hr hn hnz
  have hu0 := (hlo 0).trans_le hu.1
  have hv0 := (hlo 1).trans_le hv.1
  have hr0 := (hlo 2).trans_le hr.1
  have hs := positiveSource_ratio_support g m bcap c θ (u*v*r*n) hm hg hc hcb (by positivity) hnz
  have hnlo : a≤n := by
    apply (div_le_iff₀ (by positivity : 0<hi 0*hi 1*hi 2)).mpr
    calc
      _ ≤ u*v*r*n := hs.1
      _ ≤ (hi 0*hi 1*hi 2)*n := mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul hu.2 hv.2 hv0.le (hhip 0).le) hr.2 hr0.le (by positivity)) hn.le
      _ = _ := by ring
  have hnhi : n≤b := by
    apply (le_div_iff₀ (by positivity : 0<lo 0*lo 1*lo 2)).mpr
    calc
      _ = (lo 0*lo 1*lo 2)*n := by ring
      _ ≤ u*v*r*n := mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul hu.1 hv.1 (hlo 1).le hu0.le) hr.1 (hlo 2).le (by positivity)) hn.le
      _ ≤ _ := hs.2
  exact hwone n ⟨hnlo,by linarith⟩

def outerIndex (i : Fin 7) : Fin 9 := i.castLE (by decide)

theorem fixed_windows (g₁ g₂ : 𝓢(ℝ,ℂ)) (m₁ m₂ bcap : ℝ)
    (lo hi : Fin 7→ℝ) (Bρ : Fin 9→ℝ)
    (hm₁ : 0≤m₁) (hm₂ : 0≤m₂)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂)
    (hlo : ∀i,0<lo i) (hhi : ∀i,lo i≤hi i) (hBρ : ∀i,0≤Bρ i) :
    ∃(w₁ w₂ : 𝓢(ℝ,ℂ))(U : Fin 9→𝓢(ℝ,ℂ))(M : Fin 9→ℝ)(a b : ℝ),
      0<a ∧ a≤b ∧ HasCompactSupport (w₁ : ℝ→ℂ) ∧ HasCompactSupport (w₂ : ℝ→ℂ) ∧
      tsupport (w₁ : ℝ→ℂ)⊆Set.Icc a b ∧ tsupport (w₂ : ℝ→ℂ)⊆Set.Icc a b ∧
      (∀i,0≤M i) ∧ (∀i,HasCompactSupport (U i : ℝ→ℂ)) ∧
      (∀i,Function.support (U i)⊆Set.Icc (-M i) (M i)) ∧
      (∀(c θ u v r n : ℝ),1≤c → c≤bcap →
        u∈Set.Icc (lo 0) (hi 0) → v∈Set.Icc (lo 2) (hi 2) → r∈Set.Icc (lo 5) (hi 5) →
        0<n → positiveSource g₁ c θ (u*v*r*n)≠0 → w₁ n=1) ∧
      (∀(c θ u v r n : ℝ),1≤c → c≤bcap →
        u∈Set.Icc (lo 1) (hi 1) → v∈Set.Icc (lo 2) (hi 2) → r∈Set.Icc (lo 5) (hi 5) →
        0<n → positiveSource g₂ c θ (u*v*r*n)≠0 → w₂ n=1) ∧
      (∀(q ρ : Fin 9→ℝ),(∀i,|ρ i|≤Bρ i) →
        (∀i : Fin 7,q (outerIndex i)∈Set.Icc (lo i) (hi i)) →
        w₁ (q 7)≠0 → w₂ (q 8)≠0 → ∀i,U i (Real.log (q i)+ρ i)=1) := by
  let left : Fin 3→Fin 7 := ![0,2,5]
  let right : Fin 3→Fin 7 := ![1,2,5]
  obtain ⟨w₁,a₁,b₁,ha₁,hab₁,hwc₁,hws₁,hfresh₁⟩ := fresh_three_window g₁ m₁ bcap
    (lo ∘ left) (hi ∘ left) hm₁ hg₁ (fun i=>hlo (left i)) (fun i=>hhi (left i))
  obtain ⟨w₂,a₂,b₂,ha₂,hab₂,hwc₂,hws₂,hfresh₂⟩ := fresh_three_window g₂ m₂ bcap
    (lo ∘ right) (hi ∘ right) hm₂ hg₂ (fun i=>hlo (right i)) (fun i=>hhi (right i))
  let l : Fin 9→ℝ := ![lo 0,lo 1,lo 2,lo 3,lo 4,lo 5,lo 6,a₁,a₂]
  let u : Fin 9→ℝ := ![hi 0,hi 1,hi 2,hi 3,hi 4,hi 5,hi 6,b₁,b₂]
  have hl (i : Fin 9) : 0<l i := by
    fin_cases i
    · exact hlo 0
    · exact hlo 1
    · exact hlo 2
    · exact hlo 3
    · exact hlo 4
    · exact hlo 5
    · exact hlo 6
    · exact ha₁
    · exact ha₂
  let H (i : Fin 9) := |Real.log (l i)|+|Real.log (u i)|+Bρ i
  have hH (i : Fin 9) : 0≤H i := by dsimp [H];exact add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (hBρ i)
  choose V hVc hVs hVone hVsupport hVzero using
    fun i : Fin 9=>FourierBridge.exists_complex_smooth_cutoff (H i) (hH i)
  let U (i : Fin 9) : 𝓢(ℝ,ℂ) := (hVc i).toSchwartzMap (hVs i)
  refine ⟨w₁,w₂,U,(fun i=>H i+1),min a₁ a₂,max b₁ b₂,lt_min ha₁ ha₂,
    (min_le_left _ _).trans (hab₁.trans (le_max_left _ _)),hwc₁,hwc₂,?_,?_,
    (fun i=>by linarith [hH i]),hVc,(fun i=>(subset_tsupport _).trans (hVsupport i)),hfresh₁,hfresh₂,?_⟩
  · intro x hx
    exact ⟨(min_le_left _ _).trans (hws₁ hx).1,(hws₁ hx).2.trans (le_max_left _ _)⟩
  · intro x hx
    exact ⟨(min_le_right _ _).trans (hws₂ hx).1,(hws₂ hx).2.trans (le_max_right _ _)⟩
  · intro q ρ hρ hblock hw₁ hw₂ i
    have hq (k : Fin 9) : q k∈Set.Icc (l k) (u k) := by
      fin_cases k
      · exact hblock 0
      · exact hblock 1
      · exact hblock 2
      · exact hblock 3
      · exact hblock 4
      · exact hblock 5
      · exact hblock 6
      · exact hws₁ (subset_tsupport _ hw₁)
      · exact hws₂ (subset_tsupport _ hw₂)
    exact hVone i _ (translated_log_bound _ _ _ _ _ (hl i) (hq i) (hρ i))

end SevenEighths.InverseMomentFirstChildWindows
end

end OAI
