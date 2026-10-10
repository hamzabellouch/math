import OAI.Geometry.RCD.Coordinates.InnerCoordinateSequence

namespace OAI

/-! # One subsequence for the finite harmonic coordinate family -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem finite_subsequence_choice {ι D : Type*} [Fintype ι] [Inhabited D]
    (P : ι → (ℕ → ℕ) → (ℕ → D) → Prop)
    (hsub : ∀ i α w β, P i α w → StrictMono β → P i (α∘β) (w∘β))
    (hex : ∀ α : ℕ → ℕ, StrictMono α → ∀ i, ∃ β : ℕ → ℕ, StrictMono β ∧ ∃ w, P i (α∘β) w) :
    ∃ α, StrictMono α ∧ ∃ w : ι → ℕ → D, ∀ i, P i α (w i) := by
  classical
  have hfinite (s : Finset ι) :
      ∃ α, StrictMono α ∧ ∃ w : ι → ℕ → D, ∀ i∈s, P i α (w i) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨id,strictMono_id,(fun _ _ => default),by simp⟩
    | @insert i s hi ih =>
      obtain ⟨α,hα,w,hw⟩ := ih
      obtain ⟨β,hβ,v,hv⟩ := hex α hα i
      refine ⟨α∘β,hα.comp hβ,Function.update (fun j => w j∘β) i v,?_⟩
      intro j hj
      by_cases hji : j=i
      · subst j
        simpa only [Function.update_self] using hv
      · rw [Function.update_of_ne hji]
        exact hsub j α (w j) β (hw j ((Finset.mem_insert.mp hj).resolve_left hji)) hβ
  obtain ⟨α,hα,w,hw⟩ := hfinite Finset.univ
  exact ⟨α,hα,w,fun i => hw i (Finset.mem_univ i)⟩

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.finite_harmonic_coordinate_sequence {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hcurv : ∀ k, -1≤K*(16*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) 16 (ε k) (V k)) :
    ∃ α : ℕ → ℕ, StrictMono α ∧ ∃ w : Fin n → ℕ → SobolevSpace (hausdorff n X) hX.quadratic,
      (∀ i k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p (α k)) (5*r (α k))) (w i k)) ∧
      (∀ i k, harmonicTargetNorm hX (p (α k)) (5*r (α k)) (w i k)≤7) ∧
      (∀ i W, 0<W → W<5 → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
        ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (α k)) (W*r (α k))),
          |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w i k) x-V (α k) x i|≤δ) := by
  let P := fun (i : Fin n) (α : ℕ → ℕ) (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic) =>
    (∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p (α k)) (5*r (α k))) (w k)) ∧
    (∀ k, harmonicTargetNorm hX (p (α k)) (5*r (α k)) (w k)≤7) ∧
    (∀ W, 0<W → W<5 → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (α k)) (W*r (α k))),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-V (α k) x i|≤δ)
  have hsub : ∀ i α w β, P i α w → StrictMono β → P i (α∘β) (w∘β) := by
    rintro i α w β ⟨hh,hnm,hv⟩ hβ
    exact ⟨fun k => hh (β k),fun k => hnm (β k),
      fun W hW hW5 δ hδ => hβ.tendsto_atTop.eventually (hv W hW hW5 δ hδ)⟩
  have hsmall (k : ℕ) {t : ℝ} (ht : 0≤t) (ht16 : t≤16) : -1≤K*(t*r k)^2 := by
    by_cases hK : 0≤K
    · exact (by norm_num : (-1:ℝ)≤0).trans (mul_nonneg hK (sq_nonneg _))
    · exact (hcurv k).trans (mul_le_mul_of_nonpos_left
        (pow_le_pow_left₀ (mul_nonneg ht (hr k).le) (mul_le_mul_of_nonneg_right ht16 (hr k).le) 2)
        (le_of_not_ge hK))
  have hex : ∀ α : ℕ → ℕ, StrictMono α → ∀ i, ∃ β : ℕ → ℕ, StrictMono β ∧ ∃ w, P i (α∘β) w := by
    intro α hα i
    have hc1 (k : ℕ) : -1≤K*(r (α k))^2 := by
      simpa using hsmall (α k) (t:=1) (by norm_num) (by norm_num)
    have hc14 (k : ℕ) : -1≤K*(2*(7*r (α k)))^2 := by
      convert hsmall (α k) (t:=14) (by norm_num) (by norm_num) using 1; ring
    obtain ⟨β,hβ,w,_,hh,hnm,hv⟩ := hX.inner_coordinate_sequence hn
      (S:=16) (R:=7) (T:=5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (p∘α) (r∘α) (ε∘α) (V∘α) (fun k => hr (α k)) hc1 hc14 (fun k => hcurv (α k))
      (fun k => hε (α k)) (fun k => hε1 (α k)) (hεlim.comp hα.tendsto_atTop) (fun k => hV (α k)) i
    exact ⟨β,hβ,w,hh,by simpa only [Function.comp_def,show (5:ℝ)+2=7 by norm_num] using hnm,hv⟩
  let : Inhabited (SobolevSpace (hausdorff n X) hX.quadratic) := ⟨0⟩
  obtain ⟨α,hα,w,hw⟩ := finite_subsequence_choice P hsub hex
  exact ⟨α,hα,w,fun i => (hw i).1,fun i => (hw i).2.1,fun i => (hw i).2.2⟩

end RegularPointCoordinates

end

end OAI
