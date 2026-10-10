import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConeFacetTemplate

namespace OAI

/-! # A common Euclidean contact point for every cone containing one root -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

/-- All unit contact points for a nonzero functional coincide. -/
theorem weight_contact_unique (α : W →L[ℝ] ℝ) (hα : α ≠ 0)
    {p q : W} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hap : α p = ‖α‖) (haq : α q = ‖α‖) : p = q := by
  let v := (InnerProductSpace.toDual ℝ W).symm α
  have hv : ‖v‖ = ‖α‖ := (InnerProductSpace.toDual ℝ W).symm.norm_map α
  have hc (x : W) (hx : ‖x‖ = 1) (hax : α x = ‖α‖) : v = ‖α‖ • x := by
    have he : inner ℝ v x = ‖v‖ * ‖x‖ := by
      rw [show inner ℝ v x = α x from InnerProductSpace.toDual_symm_apply,
        hax, hv, hx, mul_one]
    simpa only [hx, one_smul, hv] using inner_eq_norm_mul_iff_real.mp he
  have he := congrArg (fun x : W => ‖α‖⁻¹ • x) ((hc p hp hap).symm.trans (hc q hq haq))
  simpa only [smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hα), one_smul] using he

/-- The contact point is fixed before choosing any cone that contains the root. -/
theorem exists_polar_template_facet_slack_at
    {I : Type*} [Fintype I] (α : I → W →L[ℝ] ℝ) (hne : ∀ i, α i ≠ 0)
    (i₀ : I) (p : W) (hp : ‖p‖ = 1) (hpα : α i₀ p = ‖α i₀‖)
    (C : ProperCone ℝ (W →L[ℝ] ℝ)) (hC : α i₀ ∈ C)
    {c c' : ℝ} (hc : 0 ≤ c) (hcc : c < c') :
    ∃ (ε₀ δ₀ : ℝ), 0 < ε₀ ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ → ∀ z ∈ conePolarTemplate C,
        ∀ i, α i ((1 - c' * δ) • p + ε • z) < (1 - c * δ) * ‖α i‖ := by
  classical
  obtain ⟨q, hq, hqα, hstrictq⟩ := exists_weight_contact_point (α i₀) (hne i₀)
  have hpq : p = q := weight_contact_unique (α i₀) (hne i₀) hp hq hpα hqα
  subst q
  have hstrict := hstrictq
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
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
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
