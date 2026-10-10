import OAI.NumberTheory.TotientAsymptotic.JoinedSimplex
import OAI.NumberTheory.TotientAsymptotic.PointEnclosure
import OAI.NumberTheory.TotientAsymptotic.TailCutScale

namespace OAI

/-! Thickening a discrete witness tail to its entire unit box preserves
membership in the same controlled full-dimensional enlargement. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma thickened_witness_enclosure {x : ℝ} {H : ℕ} {η : TailDatum H}
    (hs : 0 ≤ theta x) (hcut : 4 ≤ lam*(P H : ℝ))
    (hHm : H ≤ m x) (hPH : P H < H) (hB : 0 ≤ B x)
    (hBr : 1 ≤ B x*rho^(m x)) (hη : IsWitness H (theta x) η)
    {u : Fin (R x H) → ℝ} (hu : u ∈ tailPrefixRegion x H η)
    (hprefix : ∀ i, 1 ≤ rho^(m x-(i.val+1))*u i)
    {v : Fin (H-P H) → ℝ} (hv : ∀ i, |tailVector η i-v i| ≤ 1) :
    joinCoordinates (R x H) (H-P H) (u,v) ∈
      enlargedSimplex (R x H+(H-P H)) (B x) (1+simplexBoxError 4 (m x))
        (fun i => 1+simplexBoxError 4 (m x-(i.val+1))) := by
  have hP : 1 ≤ P H := by
    by_contra hn
    have hz : P H=0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero] at hcut
    norm_num at hcut
  have hsize : R x H+(H-P H) < m x := by unfold R; omega
  apply point_cube_full_enclosure hsize hBr (join_witness_enlarged hη hPH hHm hB hu)
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [joinCoordinates_left, sub_self, abs_zero, zero_le_one]
    · simpa only [joinCoordinates_right] using hv j
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.val_castAdd, joinCoordinates_left] using hprefix j
    · simp only [Fin.val_natAdd, joinCoordinates_right]
      have hj := j.isLt
      have he : m x-(R x H+j.val+1)=H-1-j.val := by unfold R; omega
      have hmem : H-1-j.val ∈ Finset.Ico (P H) H := Finset.mem_Ico.mpr (by omega)
      have hb := (hη.2.2.1 _ hmem).2.1
      have hband : (9/10 : ℝ)*bandScale x (R x H+j.val+1) ≤ tailVector η j := by
        simpa only [bandScale, he, tailVector, mul_assoc] using hb
      exact cube_band_lower hs hcut (by unfold R; omega) hband (hv j)

/-- The prefix lower-bound hypothesis above is automatic uniformly over all
witnesses and all prefix points once the tail cut is large. -/
theorem eventually_thickened_witness_enclosure (hren : FordRenewalInput) :
    ∀ᶠ H : ℕ in atTop, ∀ {x : ℝ} {η : TailDatum H},
      0 ≤ theta x → H ≤ m x → P H < H → 0 ≤ B x →
      1 ≤ B x*rho^(m x) → IsWitness H (theta x) η →
      ∀ {u : Fin (R x H) → ℝ}, u ∈ tailPrefixRegion x H η →
      ∀ {v : Fin (H-P H) → ℝ}, (∀ i, |tailVector η i-v i| ≤ 1) →
      joinCoordinates (R x H) (H-P H) (u,v) ∈
        enlargedSimplex (R x H+(H-P H)) (B x) (1+simplexBoxError 4 (m x))
          (fun i => 1+simplexBoxError 4 (m x-(i.val+1))) := by
  obtain ⟨c, hc, hlower⟩ := tailPrefixRegion_scaled_lower hren
  have hgrow : Tendsto (fun H : ℕ => c*((H-1 : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1)).const_mul_atTop hc
  have hcut : Tendsto (fun H : ℕ => lam*(P H : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp P_tendsto).const_mul_atTop lam_pos
  filter_upwards [hgrow.eventually (eventually_ge_atTop (1 : ℝ)),
    hcut.eventually (eventually_ge_atTop (4 : ℝ))] with H hH hP
  intro x η hs hHm hPH hB hBr hη u hu v hv
  apply thickened_witness_enclosure hs hP hHm hPH hB hBr hη hu _ hv
  intro i
  exact hH.trans (hlower hs hη hPH hHm hu i)

end TotientAsymptotic

end

end OAI
