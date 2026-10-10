import OAI.MeasureTheory.Falconer.Estimates.QuantitativePacketPoints

namespace OAI

/-! All four losses in weighted fine-packet extraction are polynomial in
the original weak-regularity loss. -/
namespace Falconer

theorem packet_parameter_bounds {Δ s E KF J B m M : ℝ}
    (hΔ : 0 < Δ) (hE : 1 ≤ E) (hKF : 1 ≤ KF) (hKFup : KF ≤ E)
    (hJ : 0 < J) (hJup : J ≤ E) (hB : 0 < B) (hBup : B ≤ E/Δ^s)
    (hm : 1/(E*(Δ^s)^2) ≤ m) (hM : 0 < M) (hMup : M ≤ E/(Δ^s)^2) :
    1/(4*E^3*Δ^s) ≤ m/(4*J*B) ∧
    KF*Δ^s*M ≤ E^2/Δ^s ∧
    KF*(4*J*B*M/m) ≤ 4*E^5/Δ^s ∧
    1/(4*E^5) ≤ m/(4*J*B*(KF*Δ^s*M)) := by
  have hE0 : 0 < E := zero_lt_one.trans_le hE
  have hpow : 0 < Δ^s := Real.rpow_pos_of_pos hΔ _
  have hm0 : 0 < m := (by positivity : 0 < 1/(E*(Δ^s)^2)).trans_le hm
  have hKF0 : 0 < KF := zero_lt_one.trans_le hKF
  constructor
  · calc
      _ = (1/(E*(Δ^s)^2))/(4*E*(E/Δ^s)) := by field_simp
      _ ≤ _ := by gcongr
  constructor
  · calc
      _ ≤ E*Δ^s*(E/(Δ^s)^2) := by gcongr
      _ = _ := by field_simp
  constructor
  · calc
      _ ≤ E*(4*E*(E/Δ^s)*(E/(Δ^s)^2)/(1/(E*(Δ^s)^2))) := by gcongr
      _ = _ := by field_simp
  · calc
      _ = (1/(E*(Δ^s)^2))/(4*E*(E/Δ^s)*(E*Δ^s*(E/(Δ^s)^2))) := by
        field_simp
      _ ≤ _ := by gcongr

end Falconer

end OAI
