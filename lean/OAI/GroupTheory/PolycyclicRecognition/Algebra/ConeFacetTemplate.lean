import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConePolarTemplate
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

namespace OAI

/-! # A fixed polar template near a generator facet

The template radius is independent of the small chart enlargement. Only
its centre moves inward with that enlargement.
-/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

/-- The Euclidean contact point has strict slack in every other oriented
ray. This is the equality case of the Cauchy--Schwarz inequality. -/
theorem exists_weight_contact_point (α : W →L[ℝ] ℝ) (hα : α ≠ 0) :
    ∃ p : W, ‖p‖ = 1 ∧ α p = ‖α‖ ∧ ∀ β : W →L[ℝ] ℝ, β ≠ 0 →
      (¬ ∃ t : ℝ, 0 < t ∧ β = t • α) → β p < ‖β‖ := by
  let v := (InnerProductSpace.toDual ℝ W).symm α
  have hv : v ≠ 0 := by
    intro h
    apply hα
    simpa [v] using congrArg (InnerProductSpace.toDual ℝ W) h
  have hvnorm : ‖v‖ = ‖α‖ := (InnerProductSpace.toDual ℝ W).symm.norm_map α
  let p := ‖v‖⁻¹ • v
  have hp : ‖p‖ = 1 := by simp [p, norm_smul, norm_ne_zero_iff.mpr hv]
  have heval (β : W →L[ℝ] ℝ) (x : W) :
      inner ℝ ((InnerProductSpace.toDual ℝ W).symm β) x = β x :=
    InnerProductSpace.toDual_symm_apply
  refine ⟨p, hp, ?_, ?_⟩
  · rw [← heval α, show (InnerProductSpace.toDual ℝ W).symm α = v from rfl]
    simp only [p, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [← hvnorm]
    field_simp
  · intro β hβ hnot
    let b := (InnerProductSpace.toDual ℝ W).symm β
    have hb : b ≠ 0 := by
      intro h
      apply hβ
      simpa [b] using congrArg (InnerProductSpace.toDual ℝ W) h
    have hbnorm : ‖b‖ = ‖β‖ := (InnerProductSpace.toDual ℝ W).symm.norm_map β
    have hneq : ‖p‖ • b ≠ ‖b‖ • p := by
      intro h
      have hrel : b = (‖b‖ / ‖v‖) • v := by
        simpa [hp, p, smul_smul, div_eq_mul_inv] using h
      apply hnot
      refine ⟨‖b‖ / ‖v‖, div_pos (norm_pos_iff.mpr hb) (norm_pos_iff.mpr hv), ?_⟩
      have hh := congrArg (InnerProductSpace.toDual ℝ W) hrel
      simpa [b, v] using hh
    have hh := inner_lt_norm_mul_iff_real.mpr hneq
    rw [hp, mul_one, hbnorm] at hh
    change inner ℝ ((InnerProductSpace.toDual ℝ W).symm β) p < ‖β‖ at hh
    rwa [heval β p] at hh

/-- All small polar templates centred just inside the contact facet lie
strictly in the prescribed smaller weight polyhedron. One positive radius
works for every sufficiently small positive chart enlargement. -/
theorem exists_polar_template_facet_slack
    {I : Type*} [Fintype I] (α : I → W →L[ℝ] ℝ) (hne : ∀ i, α i ≠ 0)
    (i₀ : I) (C : ProperCone ℝ (W →L[ℝ] ℝ)) (hC : α i₀ ∈ C)
    {c c' : ℝ} (hc : 0 ≤ c) (hcc : c < c') :
    ∃ (p : W) (ε₀ δ₀ : ℝ), α i₀ p = ‖α i₀‖ ∧
      0 < ε₀ ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ → ∀ z ∈ conePolarTemplate C,
        ∀ i, α i ((1 - c' * δ) • p + ε • z) < (1 - c * δ) * ‖α i‖ := by
  classical
  obtain ⟨p, hp, hpα, hstrict⟩ := exists_weight_contact_point (α i₀) (hne i₀)
  let ray (i : I) : Prop := ∃ t : ℝ, 0 < t ∧ α i = t • α i₀
  let m : Option I → ℝ := fun j => match j with
    | none => 1
    | some i => if ray i then 1 else
        (‖α i‖ - α i p) / ((c + c' + 1) * ‖α i‖)
  have hc' : 0 < c' := lt_of_le_of_lt hc hcc
  have hm : ∀ j, 0 < m j := by
    intro j
    cases j with
    | none => exact zero_lt_one
    | some i =>
      dsimp [m]
      split_ifs with h
      · exact zero_lt_one
      · exact div_pos (sub_pos.mpr (hstrict (α i) (hne i) h))
          (mul_pos (by linarith) (norm_pos_iff.mpr (hne i)))
  let τ := Finset.univ.inf' Finset.univ_nonempty m
  have hτ : 0 < τ := (Finset.lt_inf'_iff _).mpr (fun j _ => hm j)
  have hτm (i : I) : τ ≤ m (some i) :=
    Finset.inf'_le _ (Finset.mem_univ (some i))
  let ε₀ := τ / 2
  let δ₀ := min ε₀ (1 / (2 * (c' + 1)))
  have hε₀ : 0 < ε₀ := half_pos hτ
  have hδ₀ : 0 < δ₀ := lt_min hε₀ (by positivity)
  refine ⟨p, ε₀, δ₀, hpα, hε₀, hδ₀, ?_⟩
  intro δ hδ hδmax ε hε hεmax z hz i
  have hδτ : δ ≤ τ / 2 := hδmax.trans (min_le_left _ _)
  have hδbound : δ ≤ 1 / (2 * (c' + 1)) := hδmax.trans (min_le_right _ _)
  have hfactor : 0 ≤ 1 - c' * δ := by
    have hh := (le_div_iff₀ (show 0 < 2 * (c' + 1) by positivity)).mp hδbound
    nlinarith
  have hi : 0 < ‖α i‖ := norm_pos_iff.mpr (hne i)
  have happ : |α i p| ≤ ‖α i‖ := by simpa [hp] using (α i).le_opNorm p
  have haz : α i z ≤ ‖α i‖ := by
    exact ((le_abs_self _).trans ((α i).le_opNorm z)).trans
      ((mul_le_mul_of_nonneg_left hz.1 (norm_nonneg _)).trans_eq (mul_one _))
  simp only [map_add, map_smul, smul_eq_mul]
  by_cases hray : ray i
  · obtain ⟨t, ht, he⟩ := hray
    have hiC : α i ∈ C := by
      rw [he]
      exact C.smul_mem hC ht.le
    have hzneg : α i z ≤ 0 := hz.2 (α i) hiC
    have hfirst := mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) happ) hfactor
    have hlast : ε * α i z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε hzneg
    have hgap : 0 < (c' - c) * δ * ‖α i‖ :=
      mul_pos (mul_pos (sub_pos.mpr hcc) hδ) hi
    nlinarith
  · have htau : τ * ((c + c' + 1) * ‖α i‖) ≤ ‖α i‖ - α i p := by
      apply (le_div_iff₀ (mul_pos (by linarith) hi)).mp
      simpa [m, hray] using hτm i
    have hneg : -α i p ≤ ‖α i‖ := (neg_le_abs _).trans happ
    have herror : -c' * δ * α i p ≤ c' * δ * ‖α i‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hneg (mul_nonneg hc'.le hδ.le)]
    have hzerror : ε * α i z ≤ ε * ‖α i‖ := mul_le_mul_of_nonneg_left haz hε
    have htotal : (c + c') * δ * ‖α i‖ + ε * ‖α i‖ < ‖α i‖ - α i p := by
      have hδerr := mul_le_mul_of_nonneg_right hδτ
        (mul_nonneg (show 0 ≤ c + c' by linarith) hi.le)
      have hεerr := mul_le_mul_of_nonneg_right hεmax hi.le
      have hgap : 0 < ‖α i‖ - α i p := sub_pos.mpr (hstrict (α i) (hne i) hray)
      dsimp only [ε₀] at hεerr
      nlinarith
    nlinarith

end PolycyclicRecognition

end

end OAI
