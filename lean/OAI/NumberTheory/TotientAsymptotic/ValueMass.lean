import OAI.NumberTheory.TotientAsymptotic.ValueComparison
import OAI.NumberTheory.TotientAsymptotic.Scaling

namespace OAI

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

/-- Actual distinct values and the common-endpoint arithmetic mass. -/
theorem value_mass_approximation (hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) {a : ℝ} (ha : 0 < a) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
      ∀ t : ℝ, a*x ≤ t → t ≤ x →
        |V t/tupleNormalization x-(t/x)*(M x H (fun _ => 1)/G x (m x))| ≤ δ H+ε := by
  obtain ⟨δ,hδ,hv⟩ := value_tuple_comparison hscale hstruct hbox hren hmertens h26 h51
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hv,tuple_mass_normalized_approximation hpnt hbox hren hmertens ha] with H hV hM
  intro ε hε
  filter_upwards [hV (ε/2) (by positivity),hM (ε/2) (by positivity),scale_eventually_pos]
    with x hV hM hN
  intro t ht htx
  change 0 < tupleNormalization x at hN
  have he : |V t/tupleNormalization x-((tupleFinset x H t).card : ℝ)/tupleNormalization x| ≤ δ H+ε/2 := by
    rw [← sub_div,abs_div,abs_of_pos hN,abs_sub_comm]
    exact (div_le_iff₀ hN).mpr (hV t htx)
  have hm := hM t ht htx (fun _ => 1) (fun _ => ⟨zero_le_one,le_rfl⟩)
  rw [weightedTupleCount_one] at hm
  exact (abs_sub_le _ _ _).trans ((add_le_add he hm).trans_eq (by ring))

lemma massError_eq_normalized {x t : ℝ} (H : ℕ) (hx : x ≠ 0) (ht : t ≠ 0) :
    massError x H t = (x/t)*(V t/tupleNormalization x-
      (t/x)*(M x H (fun _ => 1)/G x (m x))) := by
  unfold massError tupleNormalization
  field_simp

/-- The common-endpoint estimate is proved from published inputs, rather than
assumed as an internal comparison. -/
theorem common_endpoint_comparison (hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) {c : ℝ} (hc : 1 ≤ c) :
    CommonEndpointComparison c := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  obtain ⟨δ,hδ,happ⟩ := value_mass_approximation hscale hstruct hpnt hbox hren hmertens h26 h51
    (a := 1/c) (by positivity)
  intro ε hε
  have he : ∀ᶠ H : ℕ in atTop, δ H < ε/(2*c) :=
    hδ.eventually (eventually_lt_nhds (by positivity))
  obtain ⟨H,hH,hδH⟩ := (happ.and he).exists
  refine ⟨H,?_⟩
  filter_upwards [hH (ε/(2*c)) (by positivity),eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hcx : x/c ≤ x := div_le_self hx0.le hc
  have h1 := hx x (by simpa [div_eq_mul_inv,mul_comm] using hcx) le_rfl
  have h2 := hx (x/c) (by simp [div_eq_mul_inv,mul_comm]) hcx
  have heps : δ H+ε/(2*c) ≤ ε/c := by
    calc
      δ H+ε/(2*c) ≤ ε/(2*c)+ε/(2*c) := by
        simpa only [add_comm] using add_le_add_right hδH.le (ε/(2*c))
      _ = ε/c := by ring
  have hs : δ H+ε/(2*c) ≤ ε := heps.trans (div_le_self hε.le hc)
  constructor
  · rw [massError_eq_normalized H hx0.ne' hx0.ne',div_self hx0.ne',one_mul]
    simpa only [div_self hx0.ne',one_mul] using h1.trans hs
  · rw [massError_eq_normalized H hx0.ne' (div_pos hx0 hc0).ne',
      show x/(x/c)=c by field_simp,abs_mul,abs_of_pos hc0]
    exact (mul_le_mul_of_nonneg_left (h2.trans heps) hc0.le).trans_eq (by field_simp)

end TotientAsymptotic

end

end OAI
