import OAI.MeasureTheory.Falconer.Geometry.ProjectionRows
import OAI.MeasureTheory.Falconer.Incidence.FiniteBallBounds

namespace OAI

/-! The actual dilation of a coarse line packet and the error from moving
its incident points to a common row. Used in the product extraction step
of the planar regular-set argument (Orponen--Shmerkin, Appendix A.6). -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def packetLineDilate (Δ : ℝ) (l : Space 2) : Space 2 := Δ⁻¹ • l

theorem packetLineDilate_apply (Δ : ℝ) (l : Space 2) (i : Fin 2) :
    packetLineDilate Δ l i = l i/Δ := by
  change Δ⁻¹*l i = l i/Δ
  rw [div_eq_mul_inv,mul_comm]

theorem packetLineDilate_dist {Δ : ℝ} (hΔ : 0 < Δ) (l m : Space 2) :
    dist (packetLineDilate Δ l) (packetLineDilate Δ m) = dist l m/Δ := by
  rw [packetLineDilate,packetLineDilate,dist_smul₀,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hΔ),div_eq_mul_inv,mul_comm]

theorem packetLineDilate_inverse {Δ : ℝ} (hΔ : 0 < Δ) (z : Space 2) :
    packetLineDilate Δ (Δ • z) = z := by
  simp only [packetLineDilate,smul_smul,inv_mul_cancel₀ hΔ.ne',one_smul]

theorem packetLineDilate_injective {Δ : ℝ} (hΔ : 0 < Δ) :
    Function.Injective (packetLineDilate Δ) := by
  intro l m h
  have hd : dist l m/Δ = 0 := by rw [← packetLineDilate_dist hΔ,h,dist_self]
  exact dist_eq_zero.mp ((div_eq_zero_iff.mp hd).resolve_right hΔ.ne')

theorem packetLineDilate_card {Δ : ℝ} (hΔ : 0 < Δ) (S : Finset (Space 2)) :
    (S.image (packetLineDilate Δ)).card = S.card :=
  Finset.card_image_of_injective _ (packetLineDilate_injective hΔ)

theorem packetLineDilate_separated {δ Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (Space 2)) (hsep : FiniteSeparatedAt δ S) :
    FiniteSeparatedAt (δ/Δ) (S.image (packetLineDilate Δ)) := by
  intro l hl m hm hlm
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hm
  rw [packetLineDilate_dist hΔ]
  exact div_le_div_of_nonneg_right
    (hsep x hx y hy (fun h => hlm (congrArg _ h))) hΔ.le

theorem packetLineDilate_chart {Δ : ℝ} (hΔ : 0 < Δ) (S : Finset (Space 2))
    (hS : ∀ l ∈ S, |l 0| ≤ Δ ∧ |l 1| ≤ Δ) :
    InBoundedLineChart (S.image (packetLineDilate Δ)) := by
  intro l hl
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hl
  constructor
  · rw [packetLineDilate_apply,abs_div,abs_of_pos hΔ]
    exact (div_le_one hΔ).2 (hS m hm).1
  · rw [packetLineDilate_apply,abs_div,abs_of_pos hΔ]
    exact (div_le_one hΔ).2 (hS m hm).2

theorem packetLineDilate_regular {δ Δ s K : ℝ} (hδ : 0 < δ)
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (S : Finset (Space 2))
    (hreg : NormalizedFiniteBallBound δ s K S) :
    NormalizedFiniteBallBound (δ/Δ) s (K*Δ^s) (S.image (packetLineDilate Δ)) := by
  intro z r hr hr1
  have hr0 : 0 < r := (div_pos hδ hΔ).trans_le hr
  have hδr : δ ≤ Δ*r := by nlinarith only [(div_le_iff₀ hΔ).1 hr]
  have hΔr : Δ*r ≤ 1 := (mul_le_mul hΔ1 hr1 hr0.le (by norm_num)).trans_eq (by norm_num)
  have hsub : (S.image (packetLineDilate Δ)).filter (fun l => dist l z ≤ r) ⊆
      (S.filter (fun l => dist l (Δ • z) ≤ Δ*r)).image (packetLineDilate Δ) := by
    intro l hl
    obtain ⟨hl,hlr⟩ := Finset.mem_filter.mp hl
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hl
    refine Finset.mem_image.mpr ⟨m,Finset.mem_filter.mpr ⟨hm,?_⟩,rfl⟩
    have he := packetLineDilate_dist hΔ m (Δ • z)
    rw [packetLineDilate_inverse hΔ] at he
    rw [he] at hlr
    nlinarith only [(div_le_iff₀ hΔ).1 hlr]
  have hc : (((S.image (packetLineDilate Δ)).filter (fun l => dist l z ≤ r)).card:ℝ) ≤
      ((S.filter (fun l => dist l (Δ • z) ≤ Δ*r)).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [packetLineDilate_card hΔ]
  calc
    _ ≤ ((S.filter (fun l => dist l (Δ • z) ≤ Δ*r)).card:ℝ) := hc
    _ ≤ K*(Δ*r)^s*(S.card:ℝ) := hreg _ _ hδr hΔr
    _ = _ := by rw [Real.mul_rpow hΔ.le hr0.le]; ring

theorem packet_common_row_incident {δ Δ y : ℝ} (hδ : 0 ≤ δ)
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (p l : Space 2)
    (hslope : |l 0| ≤ Δ) (hrow : |p 0-y| ≤ Δ)
    (hi : TubeIncident δ p l) :
    TubeIncident ((2*δ+Δ^2)/Δ) (rowPoint y (p 1/Δ)) (packetLineDilate Δ l) := by
  have hsqrt : 0 < Real.sqrt (1+(l 0)^2) := Real.sqrt_pos.2 (by positivity)
  have hsqrt2 : Real.sqrt (1+(l 0)^2) ≤ 2 := by
    apply (Real.sqrt_le_iff).2
    have ha : |l 0| ≤ 1 := hslope.trans hΔ1
    have hs : (l 0)^2 ≤ 1 := by nlinarith only [sq_abs (l 0),sq_nonneg (|l 0|-1),ha,abs_nonneg (l 0)]
    exact ⟨by norm_num,by nlinarith only [hs]⟩
  have hres : |p 1-l 0*p 0-l 1| ≤ 2*δ := by
    have hh := (div_le_iff₀ hsqrt).1 hi
    exact hh.trans (by nlinarith only [hsqrt2,hδ])
  have hprod : |l 0*(p 0-y)| ≤ Δ^2 := by
    rw [abs_mul]
    have hh := mul_le_mul hslope hrow (abs_nonneg _) hΔ.le
    nlinarith only [hh]
  have hnum : |p 1-l 0*y-l 1| ≤ 2*δ+Δ^2 := by
    have he : p 1-l 0*y-l 1 = (p 1-l 0*p 0-l 1)+l 0*(p 0-y) := by ring
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add hres hprod)
  have he : rowPoint y (p 1/Δ) 1-packetLineDilate Δ l 0*rowPoint y (p 1/Δ) 0-
      packetLineDilate Δ l 1 = (p 1-l 0*y-l 1)/Δ := by
    simp only [rowPoint_zero,rowPoint_one,packetLineDilate_apply]
    ring
  unfold TubeIncident
  rw [he,abs_div,abs_of_pos hΔ]
  have hden : 1 ≤ Real.sqrt (1+(packetLineDilate Δ l 0)^2) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    nlinarith only [sq_nonneg (packetLineDilate Δ l 0)]
  apply (div_le_iff₀ (zero_lt_one.trans_le hden)).2
  exact (div_le_div_of_nonneg_right hnum hΔ.le).trans
    (le_mul_of_one_le_right (by positivity) hden)

theorem packet_common_row_square_scale {Δ y : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (p l : Space 2) (hslope : |l 0| ≤ Δ) (hrow : |p 0-y| ≤ Δ)
    (hi : TubeIncident (Δ^2) p l) :
    TubeIncident (3*Δ) (rowPoint y (p 1/Δ)) (packetLineDilate Δ l) := by
  have hh := packet_common_row_incident (sq_nonneg Δ) hΔ hΔ1 p l hslope hrow hi
  have he : (2*Δ^2+Δ^2)/Δ = 3*Δ := by field_simp; ring
  rwa [he] at hh

end Falconer

end OAI
