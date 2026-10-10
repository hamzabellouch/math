import OAI.MeasureTheory.Falconer.Estimates.PacketLogBounds
import OAI.MeasureTheory.Falconer.Estimates.UniformScaleCombination

namespace OAI

/-! Uniform depth bounds for the actual scale-product costs. Each pencil
is separated individually; separation of their entire union is not assumed. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem separated_pencil_configuration_logs (N : ℕ)
    (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2))
    (hP : InBoundedLineChart P) (hPsep : FiniteSeparatedAt (1/(2:ℝ)^N) P)
    (hV : ∀ x ∈ P, InBoundedLineChart (V x) ∧ FiniteSeparatedAt (1/(2:ℝ)^N) (V x)) :
    Nat.log 2 (∑ x ∈ P, (V x).card)+1 ≤ 4*N+11 ∧
      Nat.log 2 (P.biUnion V).card+1 ≤ 4*N+11 := by
  have hPcard := bounded_planar_card_dyadic N P hP hPsep
  have hsum : ∑ x ∈ P, (V x).card ≤ 2^(4*N+10) := by
    calc
      _ ≤ ∑ _x ∈ P, 2^(2*N+5) := Finset.sum_le_sum fun x hx =>
        bounded_planar_card_dyadic N (V x) (hV x hx).1 (hV x hx).2
      _ = P.card*2^(2*N+5) := by simp
      _ ≤ 2^(2*N+5)*2^(2*N+5) := Nat.mul_le_mul_right _ hPcard
      _ = _ := by rw [← pow_add]; congr 1; omega
  constructor
  · simpa only [Nat.add_assoc] using packet_log_of_card_bound hsum
  · have hcard : (P.biUnion V).card ≤ 2^(4*N+10) := Finset.card_biUnion_le.trans hsum
    simpa only [Nat.add_assoc] using packet_log_of_card_bound hcard

theorem uniform_scale_cost_bounds {α β H L E F K KP R s : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hH : 0 ≤ H) (hαH : α ≤ H) (hβH : β ≤ H)
    (hL : 0 ≤ L) (hLb : L ≤ 20*β^2) (hE : E = 8*α*β) (hF : F = 2*E*R)
    (hK : 0 ≤ K) (hKP : 0 ≤ KP) (hR : 0 ≤ R) (hs : s ≤ 1) :
    L ≤ 20*H^2 ∧ E ≤ 8*H^2 ∧ F ≤ 16*R*H^2 ∧
      (2*(K*7^s)*α)*L ≤ 280*K*H^3 ∧
      2*(((K*F)*3^s)*7^s)*β ≤ 672*K*R*H^3 ∧
      (KP*F)*β ≤ 16*KP*R*H^3 ∧
      4*E*β*R ≤ 32*R*H^3 ∧
      43264*α*β^3 ≤ 43264*H^4 := by
  have h7 : (7:ℝ)^s ≤ 7 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 7) hs
  have h3 : (3:ℝ)^s ≤ 3 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hs
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hF0 : 0 ≤ F := by rw [hF]; positivity
  have hLH : L ≤ 20*H^2 := hLb.trans (by gcongr)
  have hEH : E ≤ 8*H^2 := by rw [hE]; nlinarith only [mul_le_mul hαH hβH hβ hH]
  have hFH : F ≤ 16*R*H^2 := by
    rw [hF]
    calc
      _ ≤ 2*(8*H^2)*R := by gcongr
      _ = _ := by ring
  refine ⟨hLH,hEH,hFH,?_,?_,?_,?_,?_⟩
  · calc
      _ ≤ (2*(K*7)*H)*(20*H^2) := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ 2*(((K*(16*R*H^2))*3)*7)*H := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ (KP*(16*R*H^2))*H := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ 4*(8*H^2)*H*R := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ 43264*H*H^3 := by gcongr
      _ = _ := by ring

theorem rescaled_pencil_size_ratio {m M E β : ℝ}
    (hm : 0 < m) (hE : 0 < E) (hβ : 0 < β) (j : ℕ) :
    (M/(2:ℝ)^j)/((m/(2*E))/(2*β*(2:ℝ)^j)) = 4*E*β*(M/m) := by
  field_simp
  ring

theorem coarse_pencil_size_ratio {w β : ℝ} (hw : 0 < w) (hβ : 0 < β) :
    (2*w)/(w/(2*β)) = 4*β := by
  field_simp
  ring

end Falconer

end OAI
