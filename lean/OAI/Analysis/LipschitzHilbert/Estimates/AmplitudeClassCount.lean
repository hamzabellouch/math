import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeClassSum

namespace OAI

/-! A logarithmic window of support measures contains only linearly many
of the dyadic classes used in the retained amplitude sum. -/
noncomputable section
namespace LipschitzHilbert

theorem dyadicMeasureClass_abs_le (m L : ℝ) (hlog : |Real.log m|≤L) :
    |(dyadicMeasureClass m:ℝ)|≤L/Real.log 2+1 := by
  have hc : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hx : |Real.log m/Real.log 2|≤L/Real.log 2 := by
    rw [abs_div,abs_of_pos hc]
    exact div_le_div_of_nonneg_right hlog hc.le
  have hfloor := Int.floor_le (Real.log m/Real.log 2)
  have hceil := Int.lt_floor_add_one (Real.log m/Real.log 2)
  change |(⌊Real.log m/Real.log 2⌋:ℝ)|≤_
  exact abs_le.mpr ⟨by linarith [(abs_le.mp hx).1],by linarith [(abs_le.mp hx).2]⟩

theorem dyadicMeasureClass_image_card (I : Finset ℤ) (mass : ℤ → ℝ) (L : ℝ)
    (hL : 0≤L) (hlog : ∀ i∈I, |Real.log (mass i)|≤L) :
    ((I.image (fun i => dyadicMeasureClass (mass i))).card:ℝ)≤2*(L/Real.log 2)+5 := by
  classical
  have hc : 0<Real.log 2 := Real.log_pos (by norm_num)
  let K : ℕ := ⌈L/Real.log 2+1⌉₊
  have hKlo : L/Real.log 2+1≤K := Nat.le_ceil _
  have hKhi : (K:ℝ)≤L/Real.log 2+2 := by
    have h := (Nat.ceil_lt_add_one (show 0≤L/Real.log 2+1 by positivity)).le
    simpa only [add_assoc,show (1:ℝ)+1=2 by norm_num] using h
  have hsub : I.image (fun i => dyadicMeasureClass (mass i)) ⊆ Finset.Icc (-(K:ℤ)) K := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    have habs : |(dyadicMeasureClass (mass i):ℝ)|≤K :=
      (dyadicMeasureClass_abs_le _ L (hlog i hi)).trans hKlo
    have hInt : |dyadicMeasureClass (mass i)|≤(K:ℤ) := by exact_mod_cast habs
    exact Finset.mem_Icc.mpr (abs_le.mp hInt)
  have hcard : (Finset.Icc (-(K:ℤ)) K).card=2*K+1 := by
    have h := Int.card_Icc_of_le (a:=-(K:ℤ)) (b:=(K:ℤ)) (by omega)
    omega
  have hn : (I.image (fun i => dyadicMeasureClass (mass i))).card≤2*K+1 := by
    rw [←hcard]
    exact Finset.card_le_card hsub
  have hreal : ((I.image (fun i => dyadicMeasureClass (mass i))).card:ℝ)≤2*(K:ℝ)+1 := by
    exact_mod_cast hn
  linarith

end LipschitzHilbert

end

end OAI
