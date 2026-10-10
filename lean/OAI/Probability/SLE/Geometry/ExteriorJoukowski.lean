import OAI.Probability.SLE.LoewnerCharts
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace OAI

/-! The Joukowski chart from the upper half of the exterior disk to the
half-plane. This is the final elementary chart in exterior slit normalization. -/
noncomputable section
open Set Complex

namespace SLEExactGauge

def exteriorUpperDisk : Set ℂ := {w | 1 < ‖w‖ ∧ 0 < w.im}

def exteriorJoukowski (w : ℂ) : ℂ := w+w⁻¹

lemma exteriorJoukowski_im (w : ℂ) :
    (exteriorJoukowski w).im=w.im-w.im/‖w‖^2 := by
  simp only [exteriorJoukowski,add_im,inv_im,normSq_eq_norm_sq,neg_div,sub_eq_add_neg]

lemma exteriorJoukowski_im_mul {w : ℂ} (hw : w ≠ 0) :
    (exteriorJoukowski w).im*‖w‖^2=w.im*(‖w‖^2-1) := by
  rw [exteriorJoukowski_im]
  have hn : ‖w‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hw)
  field_simp

lemma exteriorJoukowski_mapsTo : MapsTo exteriorJoukowski exteriorUpperDisk upperHalfPlane := by
  intro w hw
  change 1 < ‖w‖ ∧ 0 < w.im at hw
  have hwn : 0 < ‖w‖ := zero_lt_one.trans hw.1
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp hwn.ne'
  have hsq : 1 < ‖w‖^2 := by nlinarith
  have he := exteriorJoukowski_im_mul hw0
  change 0 < (exteriorJoukowski w).im
  nlinarith [mul_pos hw.2 (sub_pos.mpr hsq),sq_nonneg ‖w‖]

lemma exteriorJoukowski_injOn : InjOn exteriorJoukowski {w : ℂ | 1 < ‖w‖} := by
  intro u hu v hv he
  change 1 < ‖u‖ at hu
  change 1 < ‖v‖ at hv
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (zero_lt_one.trans hu).ne'
  have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (zero_lt_one.trans hv).ne'
  have hf : (u-v)*(u*v-1)=0 := by
    calc
      (u-v)*(u*v-1)=(exteriorJoukowski u-exteriorJoukowski v)*(u*v) := by
        dsimp only [exteriorJoukowski]
        field_simp [hu0,hv0]
        ring
      _ = 0 := by rw [he,sub_self,zero_mul]
  rcases mul_eq_zero.mp hf with h|h
  · exact sub_eq_zero.mp h
  · have hnorm : ‖u‖*‖v‖=1 := by
      simpa only [norm_mul,norm_one] using congrArg norm (sub_eq_zero.mp h)
    have hmul := mul_lt_mul_of_pos_left hv (zero_lt_one.trans hu)
    have hp : 1 < ‖u‖*‖v‖ := hu.trans (by simpa only [mul_one] using hmul)
    linarith

lemma exteriorJoukowski_surjOn : SurjOn exteriorJoukowski exteriorUpperDisk upperHalfPlane := by
  intro z hz
  obtain ⟨s,hs⟩ := IsAlgClosed.exists_pow_nat_eq (z^2-4) (by decide : 0 < (2:ℕ))
  let u : ℂ := (z+s)/2
  let v : ℂ := (z-s)/2
  have hsum : u+v=z := by dsimp [u,v]; ring
  have hprod : u*v=1 := by
    dsimp only [u,v]
    linear_combination -hs/4
  have hu0 : u ≠ 0 := by intro he; rw [he,zero_mul] at hprod; exact zero_ne_one hprod
  have hv0 : v ≠ 0 := by intro he; rw [he,mul_zero] at hprod; exact zero_ne_one hprod
  have huinv : u⁻¹=v := by
    apply (mul_left_cancel₀ hu0)
    rw [mul_inv_cancel₀ hu0,hprod]
  have hvinv : v⁻¹=u := by rw [← huinv,inv_inv]
  have huJ : exteriorJoukowski u=z := by rw [exteriorJoukowski,huinv,hsum]
  have hvJ : exteriorJoukowski v=z := by rw [exteriorJoukowski,hvinv,add_comm,hsum]
  have hunit (w : ℂ) (hw0 : w ≠ 0) (hwJ : exteriorJoukowski w=z) : ‖w‖ ≠ 1 := by
    intro h
    have he := exteriorJoukowski_im_mul hw0
    rw [hwJ,h] at he
    norm_num at he
    exact hz.ne' he
  have hex : ∃ w : ℂ, 1 < ‖w‖ ∧ exteriorJoukowski w=z := by
    by_cases hu : 1 < ‖u‖
    · exact ⟨u,hu,huJ⟩
    · have hvnorm : ‖u‖*‖v‖=1 := by
        simpa only [norm_mul,norm_one] using congrArg norm hprod
      have hult : ‖u‖ < 1 := lt_of_le_of_ne (le_of_not_gt hu) (hunit u hu0 huJ)
      have hvn : 0 ≤ ‖v‖ := norm_nonneg _
      have hup : 0 < ‖u‖ := norm_pos_iff.mpr hu0
      have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv0
      have hh := mul_lt_mul_of_pos_right hult hvp
      exact ⟨v,by nlinarith, hvJ⟩
  obtain ⟨w,hwn,hwJ⟩ := hex
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (zero_lt_one.trans hwn).ne'
  have hi : 0 < w.im := by
    have he := exteriorJoukowski_im_mul hw0
    rw [hwJ] at he
    have hsq : 1 < ‖w‖^2 := by nlinarith
    have hh : 0 < z.im*‖w‖^2 := mul_pos hz (sq_pos_of_pos (zero_lt_one.trans hwn))
    nlinarith
  exact ⟨w,⟨hwn,hi⟩,hwJ⟩

theorem exteriorJoukowski_bijOn : BijOn exteriorJoukowski exteriorUpperDisk upperHalfPlane :=
  ⟨exteriorJoukowski_mapsTo,exteriorJoukowski_injOn.mono (fun _ h => h.1),
    exteriorJoukowski_surjOn⟩

theorem exteriorJoukowski_differentiableOn :
    DifferentiableOn ℂ exteriorJoukowski exteriorUpperDisk := by
  intro w hw
  exact (differentiableAt_id.add (differentiableAt_id.inv
    (norm_ne_zero_iff.mp (zero_lt_one.trans hw.1).ne'))).differentiableWithinAt

end SLEExactGauge

end

end OAI
