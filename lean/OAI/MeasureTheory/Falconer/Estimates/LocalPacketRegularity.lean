import OAI.MeasureTheory.Falconer.Estimates.LocalPacketRows

namespace OAI

/-! Exact similarity and regularity of the original points in a local
packet chart. The only cost is the explicit cardinality restriction. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem localPacketPoint_eq_smul {Δ : ℝ} (y a : ℝ) (p : Space 2) :
    localPacketPoint Δ y a p = Δ⁻¹ • (p-rowPoint y a) := by
  ext i
  fin_cases i <;> simp [localPacketPoint,div_eq_mul_inv,mul_comm]

theorem localPacketPoint_dist {Δ : ℝ} (hΔ : 0 < Δ) (y a : ℝ) (p q : Space 2) :
    dist (localPacketPoint Δ y a p) (localPacketPoint Δ y a q) = dist p q/Δ := by
  rw [localPacketPoint_eq_smul,localPacketPoint_eq_smul,dist_smul₀,
    dist_sub_right,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hΔ),div_eq_mul_inv,mul_comm]

theorem localPacketPoint_inverse {Δ : ℝ} (hΔ : 0 < Δ) (y a : ℝ) (z : Space 2) :
    localPacketPoint Δ y a (Δ • z+rowPoint y a) = z := by
  rw [localPacketPoint_eq_smul,add_sub_cancel_right,smul_smul,inv_mul_cancel₀ hΔ.ne',one_smul]

theorem localPacketPoint_regular {δ Δ t K : ℝ} (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hΔ1 : Δ ≤ 1) (y a : ℝ) (P : Finset (Space 2))
    (hreg : NormalizedFiniteBallBound δ t K P) :
    NormalizedFiniteBallBound (δ/Δ) t (K*Δ^t) (P.image (localPacketPoint Δ y a)) := by
  intro z r hr hr1
  have hr0 : 0 < r := (div_pos hδ hΔ).trans_le hr
  have hδr : δ ≤ Δ*r := by nlinarith only [(div_le_iff₀ hΔ).1 hr]
  have hΔr : Δ*r ≤ 1 := (mul_le_mul hΔ1 hr1 hr0.le (by norm_num)).trans_eq (by norm_num)
  have hsub : (P.image (localPacketPoint Δ y a)).filter (fun p => dist p z ≤ r) ⊆
      (P.filter (fun p => dist p (Δ • z+rowPoint y a) ≤ Δ*r)).image (localPacketPoint Δ y a) := by
    intro p hp
    obtain ⟨hp,hpr⟩ := Finset.mem_filter.mp hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩,rfl⟩
    have he := localPacketPoint_dist hΔ y a x (Δ • z+rowPoint y a)
    rw [localPacketPoint_inverse hΔ] at he
    rw [he] at hpr
    nlinarith only [(div_le_iff₀ hΔ).1 hpr]
  rw [Finset.card_image_of_injective _ (localPacketPoint_injective hΔ y a)]
  calc
    _ ≤ ((P.filter (fun p => dist p (Δ • z+rowPoint y a) ≤ Δ*r)).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
    _ ≤ K*(Δ*r)^t*(P.card:ℝ) := hreg _ _ hδr hΔr
    _ = _ := by rw [Real.mul_rpow hΔ.le hr0.le]; ring

theorem local_packet_subset_regular {δ Δ t K C : ℝ}
    (hδ : 0 < δ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hK : 0 ≤ K)
    (y a : ℝ) (P S : Finset (Space 2)) (hSP : S ⊆ P)
    (hsize : (P.card:ℝ) ≤ C*(S.card:ℝ)) (hreg : NormalizedFiniteBallBound δ t K P) :
    NormalizedFiniteBallBound (δ/Δ) t ((K*C)*Δ^t) (S.image (localPacketPoint Δ y a)) :=
  localPacketPoint_regular hδ hΔ hΔ1 y a S
    (normalized_finite_ball_bound_subset hδ.le hK hSP hsize hreg)

end Falconer

end OAI
