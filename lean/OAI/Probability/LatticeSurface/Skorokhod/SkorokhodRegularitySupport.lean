import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodSegment

namespace OAI

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma sample_floor_bounds (N : ℕ) (hN : 0 < N) (t : ℝ) (ht : 0 ≤ t) :
    (⌊t*N⌋₊:ℝ)/N ≤ t ∧ t-(1:ℝ)/N < (⌊t*N⌋₊:ℝ)/N := by
  have hN' : (0:ℝ)<N := by exact_mod_cast hN
  constructor
  · exact (div_le_iff₀ hN').mpr (Nat.floor_le (mul_nonneg ht hN'.le))
  · apply (lt_div_iff₀ hN').mpr
    have hh := Nat.lt_floor_add_one (t*(N:ℝ))
    have he : (t-1/(N:ℝ))*N=t*N-1 := by field_simp
    rw [he];linarith

lemma sample_floor_mem (N : ℕ) (hN : 0 < N) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    (⌊t*N⌋₊:ℝ)/N∈Icc (0:ℝ) 1 :=
  ⟨by positivity,(sample_floor_bounds N hN t ht.1).1.trans ht.2⟩

lemma sample_floor_tendsto (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => (⌊t*((n+1:ℕ):ℝ)⌋₊:ℝ)/(n+1:ℕ)) atTop (nhds t) := by
  have hh := (tendsto_const_nhds (x:=t) (f:=atTop)).sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  have hh' : Tendsto (fun n : ℕ => t-1/(n+1:ℕ)) atTop (nhds t) := by simpa using hh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hh' tendsto_const_nhds
    (fun n => (sample_floor_bounds (n+1) (Nat.succ_pos _) t ht).2.le)
    (fun n => (sample_floor_bounds (n+1) (Nat.succ_pos _) t ht).1)

lemma mesh_modulus (B : Body E) (x₀ c : E) (r δ η : ℝ)
    (hx₀ : x₀∈B.carrier) (hr : 0 < r) (hball : Metric.closedBall c r⊆B.carrier)
    (w : ℝ → E) (hosc : ∀t∈Icc (0:ℝ) 1,‖w t-w 0‖ ≤ r/2)
    (hδ : 0 ≤ δ) (huc : ∀s∈Icc (0:ℝ) 1,∀t∈Icc (0:ℝ) 1,|s-t|<η → ‖w s-w t‖ ≤ δ)
    (N : ℕ) (hN : 0 < N) (s t : ℝ) (hs : s∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (hst : |s-t|+1/(N:ℝ)<η) :
    ‖mesh B x₀ w N s-mesh B x₀ w N t‖ ≤ δ+Real.sqrt (2*δ*(‖x₀-c‖^2/r)) := by
  have hN' : (0:ℝ)<N := by exact_mod_cast hN
  have htime (i : ℕ) (hi : i ≤ N) : (i:ℝ)/N∈Icc (0:ℝ) 1 := by
    refine ⟨by positivity,?_⟩
    rw [div_le_one hN'];exact_mod_cast hi
  have hvar := regulator_variation_bound B x₀ c r ‖x₀-c‖ hx₀ hr le_rfl hball (sampledDriver w N) N
    (by intro i hi; simpa [sampledDriver] using hosc _ (htime i hi))
  have ordered (s t : ℝ) (hs : s∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
      (hle : s ≤ t) (hst : t-s+1/(N:ℝ)<η) :
      ‖mesh B x₀ w N t-mesh B x₀ w N s‖ ≤ δ+Real.sqrt (2*δ*(‖x₀-c‖^2/r)) := by
    let a := ⌊s*N⌋₊
    let b := ⌊t*N⌋₊
    have hab : a ≤ b := Nat.floor_mono (mul_le_mul_of_nonneg_right hle hN'.le)
    have hb : b ≤ N := Nat.floor_le_of_le (by nlinarith [ht.2])
    have haa := sample_floor_bounds N hN s hs.1
    have hbb := sample_floor_bounds N hN t ht.1
    have he : a+(b-a)=b := Nat.add_sub_of_le hab
    have hh := walk_segment_displacement B x₀ hx₀ (sampledDriver w N) a (b-a) N (by omega) δ (‖x₀-c‖^2/r) hδ hvar
      (by
        intro i hi
        have hai : a+i ≤ b := by omega
        have hia : (a:ℝ)/N ≤ (a+i:ℕ)/N := div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_add_right a i) hN'.le
        have hit : ((a+i:ℕ):ℝ)/N ≤ t := (div_le_div_of_nonneg_right (by exact_mod_cast hai) hN'.le).trans hbb.1
        apply huc _ (htime _ (hai.trans hb)) _ (htime a (hab.trans hb))
        rw [abs_of_nonneg (sub_nonneg.mpr hia)]
        have haalo : s-1/(N:ℝ)<(a:ℝ)/N := haa.2
        linarith)
    simpa only [he,mesh] using hh
  rcases le_total s t with h|h
  · rw [norm_sub_rev]
    exact ordered s t hs ht h (by simpa only [abs_of_nonpos (sub_nonpos.mpr h),neg_sub] using hst)
  · exact ordered t s ht hs h (by simpa only [abs_of_nonneg (sub_nonneg.mpr h)] using hst)

end ConvexSkorokhod

end OAI
