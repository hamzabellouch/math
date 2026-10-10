import Mathlib
import OAI.Probability.BinarySweep.GridBounds.EmptyGrid

namespace OAI

noncomputable section

section

open scoped Topology
open Set Complex Complex.HadamardThreeLines

namespace BinaryCoordinateSweeps

lemma cosh_norm_le (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.cosh z.re := by
  rw [Complex.cosh, norm_div]
  norm_num only [Complex.norm_ofNat]
  rw [Real.cosh_eq]
  have h := norm_add_le (Complex.exp z) (Complex.exp (-z))
  rw [Complex.norm_exp,Complex.norm_exp,Complex.neg_re] at h
  linarith

def ellipseMap (v : ℝ) (z : ℂ) : ℂ := (v:ℂ)/2*(Complex.cosh z+1)

lemma ellipseMap_norm {v L : ℝ} (hv : 0 ≤ v) (hL : 0 ≤ L) (z : ℂ)
    (hz : z ∈ verticalClosedStrip 0 L) :
    ‖ellipseMap v z‖ ≤ v/2*(Real.cosh L+1) := by
  change 0 ≤ z.re ∧ z.re ≤ L at hz
  have hc : Real.cosh z.re ≤ Real.cosh L := by
    rw [Real.cosh_le_cosh,abs_of_nonneg hz.1,abs_of_nonneg hL]
    exact hz.2
  have hn : ‖Complex.cosh z+1‖ ≤ Real.cosh L+1 := by
    have := norm_add_le (Complex.cosh z) (1:ℂ)
    norm_num only [norm_one] at this
    linarith [cosh_norm_le z]
  simpa only [ellipseMap,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hv,Complex.norm_ofNat] using mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ v/2)

lemma ellipseMap_left {v : ℝ} (hv : 0 ≤ v) (z : ℂ) (hz : z.re=0) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ v ∧ ellipseMap v z=(t:ℂ) := by
  have he : z=(z.im:ℂ)*Complex.I := by apply Complex.ext <;> simp [hz]
  refine ⟨v/2*(Real.cos z.im+1),?_,?_,?_⟩
  · have := Real.neg_one_le_cos z.im
    exact mul_nonneg (div_nonneg hv (by norm_num)) (by linarith)
  · have := Real.cos_le_one z.im
    nlinarith
  · have hc : Complex.cosh z=(Real.cos z.im:ℂ) := by
      calc Complex.cosh z = Complex.cosh ((z.im:ℂ)*Complex.I) := congrArg _ he
           _ = (Real.cos z.im:ℂ) := by rw [Complex.cosh_mul_I,Complex.ofReal_cos]
    rw [ellipseMap,hc]
    push_cast
    rfl

theorem analytic_segment_transfer (R a : ℝ) (hR : 1 < R) (ha : 0 < a) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
    ∀ E : Type*, ∀ [NormedAddCommGroup E] [NormedSpace ℂ E],
    ∀ f : ℂ → E, Differentiable ℂ f → ∀ ε : ℝ, 0 ≤ ε →
    (∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ 1) →
    (∀ t : ℝ, 0 ≤ t → t ≤ a → ‖f (t:ℂ)‖ ≤ ε) → ‖f 1‖ ≤ ε^θ := by
  let v := min a (1/2)
  have hv : 0 < v := lt_min ha (by norm_num)
  have hva : v ≤ a := min_le_left _ _
  have hv1 : v < 1 := (min_le_right _ _).trans_lt (by norm_num)
  let x := Real.arcosh (2/v-1)
  let L := Real.arcosh (2*R/v-1)
  have hargx : 1 < 2/v-1 := by
    have : (2:ℝ) < 2/v := (lt_div_iff₀ hv).mpr (by linarith)
    linarith
  have hargL : 2/v-1 < 2*R/v-1 := by
    apply sub_lt_sub_right
    apply (div_lt_div_iff_of_pos_right hv).2
    linarith
  have hx : 0 < x := Real.arcosh_pos hargx
  have hxL : x < L := (Real.arcosh_lt_arcosh (by linarith) (by linarith)).mpr hargL
  have hL : 0 < L := hx.trans hxL
  have hcoshx : Real.cosh x=2/v-1 := Real.cosh_arcosh hargx.le
  have hcoshL : Real.cosh L=2*R/v-1 := Real.cosh_arcosh (hargx.trans hargL).le
  have houter : v/2*(Real.cosh L+1)=R := by rw [hcoshL]; field_simp; ring
  have hat : ellipseMap v (x:ℂ)=1 := by
    rw [ellipseMap,←Complex.ofReal_cosh,hcoshx]
    push_cast
    have hvC : (v:ℂ) ≠ 0 := by exact_mod_cast hv.ne'
    field_simp [hvC]
    ring
  refine ⟨1-x/L,by have := (div_lt_one hL).mpr hxL; linarith,
    by have := div_nonneg hx.le hL.le; linarith,?_⟩
  intro E _ _ f hf ε hε hbound hsmall
  let F : ℂ → E := fun z => f (ellipseMap v z)
  have hmap : Differentiable ℂ (ellipseMap v) :=
    (Complex.differentiable_cosh.add_const 1).const_mul ((v:ℂ)/2)
  have hFd : Differentiable ℂ F := hf.comp hmap
  have hF1 : ∀z ∈ verticalClosedStrip 0 L, ‖F z‖ ≤ 1 := by
    intro z hz
    exact hbound _ ((ellipseMap_norm hv.le hL.le z hz).trans_eq houter)
  have hc : BddAbove ((norm ∘ F) '' verticalClosedStrip 0 L) := by
    use 1
    rintro y ⟨z,hz,rfl⟩
    exact hF1 z hz
  have hleft : ∀z ∈ Complex.re ⁻¹' {(0:ℝ)}, ‖F z‖ ≤ ε := by
    intro z hz
    obtain ⟨t,ht,htv,he⟩ := ellipseMap_left hv.le z hz
    dsimp [F]
    rw [he]
    exact hsmall t ht (htv.trans hva)
  have hright : ∀z ∈ Complex.re ⁻¹' {L}, ‖F z‖ ≤ 1 := by
    intro z hz
    apply hF1
    change 0 ≤ z.re ∧ z.re ≤ L
    change z.re=L at hz
    rw [hz]
    exact ⟨hL.le,le_rfl⟩
  have ht := norm_le_interp_of_mem_verticalClosedStrip' hL
    (show (x:ℂ) ∈ verticalClosedStrip 0 L from ⟨hx.le,hxL.le⟩)
    hFd.diffContOnCl hc hleft hright
  simpa only [F,hat,Complex.ofReal_re,sub_zero,Real.one_rpow,mul_one] using ht

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

theorem grid_analytic_contraction : ∃ r : ℕ, 0<r ∧ ∃ g : ℝ, 0<g ∧
    ∀b : ℕ, 1≤b → ∀bits : Fin b → ℕ,
    (∀j,r≤bits j ∧ bits j≤2*r) → ∀D : ℕ,
    ∀ρ : Representation ℂ (Equiv.Perm (GridSlot bits)) (RepSpace D),
    ρ.IsIrreducible → IsUnitaryRep ρ →
      ‖complexGridAverage bits ρ 1‖ ≤ (D:ℝ)^(-g) := by
  obtain ⟨r,hr,q,hq,a,ha,hreal⟩ := real_grid_bound
  obtain ⟨R,hR,hdisk⟩ := complex_grid_disk (2*r)
  obtain ⟨θ,hθ,hθ1,htrans⟩ := analytic_segment_transfer R a hR ha
  refine ⟨r,hr,(c0/(2*q))*θ,mul_pos (div_pos (by norm_num [c0]) (by positivity)) hθ,?_⟩
  intro b hb bits hbits D ρ hi hρ
  have := hi
  have : Nontrivial (RepSpace D) :=
    Module.nontrivial_of_finrank_pos (Signed.irreducible_finrank_pos ρ)
  have ht := htrans (RepSpace D →L[ℂ] RepSpace D) (complexGridAverage bits ρ)
    (complexGridAverage_differentiable bits ρ) ((D:ℝ)^(-c0/(2*q))) (by positivity)
    (hdisk b bits (fun j => (hbits j).2) (RepSpace D) ρ hρ)
    (hreal b hb bits hbits D ρ hi hρ)
  rw [←Real.rpow_mul (Nat.cast_nonneg D)] at ht
  have he : (-c0/(2*(q:ℝ)))*θ = -(c0/(2*q)*θ) := by ring
  simpa only [he] using ht

end BinaryCoordinateSweeps

end

end OAI
