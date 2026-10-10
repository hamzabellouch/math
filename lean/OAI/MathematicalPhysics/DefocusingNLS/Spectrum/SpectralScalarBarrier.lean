import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! Entry into, and preservation of, a strict scalar differential barrier.
This is used for the Airy logarithmic slope. -/

open Set
namespace DefocusingNLS

theorem spectralScalar_eventually_below (f D : ℝ → ℝ) (T B c : ℝ) (hc : 0<c)
    (hf : ContinuousOn f (Ici T)) (hD : ∀ t, T≤t → HasDerivAt f (D t) t)
    (hpush : ∀ t, T≤t → B≤f t → D t≤ -c) :
    ∃ S : ℝ, T≤S ∧ ∀ t, S≤t → f t≤B := by
  have hex : ∃ S : ℝ, T≤S ∧ f S≤B := by
    by_contra hn
    have hgt (t : ℝ) (ht : T≤t) : B<f t := by
      by_contra h
      exact hn ⟨t,ht,le_of_not_gt h⟩
    let S := T+(f T-B+1)/c
    have hST : T≤S := by
      have hp : 0≤(f T-B+1)/c := div_nonneg (by linarith [hgt T le_rfl]) hc.le
      dsimp only [S]
      linarith
    have hcont : ContinuousOn f (Icc T S) := hf.mono (fun _ ht => ht.1)
    have hd : DifferentiableOn ℝ f (interior (Icc T S)) := by
      intro t ht
      have ht' : t ∈ Ioo T S := by simpa only [interior_Icc] using ht
      exact (hD t ht'.1.le).differentiableAt.differentiableWithinAt
    have hb : ∀ t ∈ interior (Icc T S), deriv f t≤ -c := by
      intro t ht
      have ht' : t ∈ Ioo T S := by simpa only [interior_Icc] using ht
      rw [(hD t ht'.1.le).deriv]
      exact hpush t ht'.1.le (hgt t ht'.1.le).le
    have hh := (convex_Icc T S).image_sub_le_mul_sub_of_deriv_le hcont hd hb
      T ⟨le_rfl,hST⟩ S ⟨hST,le_rfl⟩ hST
    have he : c*(S-T)=f T-B+1 := by dsimp only [S]; field_simp; ring
    have := hgt S hST
    nlinarith
  obtain ⟨S,hST,hSB⟩ := hex
  refine ⟨S,hST,?_⟩
  intro t hSt
  have hh := image_le_of_deriv_right_lt_deriv_boundary (a := S) (b := t)
    (hf.mono (fun _ ht => hST.trans ht.1))
    (fun x hx => (hD x (hST.trans hx.1)).hasDerivWithinAt)
    (B := fun _ => B) (B' := fun _ => 0) hSB (fun x => hasDerivAt_const x B) (by
      intro x hx he
      have hd := hpush x (hST.trans hx.1) he.ge
      linarith)
  exact hh ⟨hSt,le_rfl⟩

theorem spectralScalar_eventually_above (f D : ℝ → ℝ) (T B c : ℝ) (hc : 0<c)
    (hf : ContinuousOn f (Ici T)) (hD : ∀ t, T≤t → HasDerivAt f (D t) t)
    (hpush : ∀ t, T≤t → f t≤B → c≤D t) :
    ∃ S : ℝ, T≤S ∧ ∀ t, S≤t → B≤f t := by
  obtain ⟨S,hS,hbound⟩ := spectralScalar_eventually_below (fun t => -f t) (fun t => -D t)
    T (-B) c hc hf.neg (fun t ht => (hD t ht).neg) (by
      intro t ht hfB
      have h := hpush t ht (by linarith)
      linarith)
  exact ⟨S,hS,fun t ht => by have := hbound t ht; linarith⟩

end DefocusingNLS

end OAI
