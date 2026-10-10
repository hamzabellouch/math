import OAI.MeasureTheory.Falconer.Radial.RadialTupleTransversality
import OAI.MeasureTheory.Falconer.Incidence.CommonTupleIncidence
import OAI.MeasureTheory.Falconer.Radial.GeneralTubeMass

namespace OAI

/-! # Small common transverse tube intersections force small original incidence -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal BigOperators
variable {n : ℕ}

theorem radial_tube_incidence_bound (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    (μ ν : Measure (Space (n+1))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : Space (n+1)) {r R : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hR : ∀ᵐ x ∂ν, ‖c-x‖ ≤ R) (K : ℝ≥0∞)
    (hslab : ∀ u : Space (n+1), ‖u‖ = 1 →
      ν {x | |inner ℝ u x-inner ℝ u c| ≤ R*r} ≤ K)
    (E : Set (Space (n+1) × Space (n+1))) (hE : MeasurableSet E)
    (A : Space (n+1) → Finset (Space (n+1))) (B : ℝ)
    (hbounded : ∀ x w, (x,w) ∈ E → ‖x‖ ≤ B)
    {δ C H M t : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) (hH : 0 ≤ H) (ht : 0 ≤ t)
    (hball : ∀ p : Space (n+1), μ (ball p ((((n+1:ℕ):ℝ)^2+1)*δ)) ≤ ENNReal.ofReal H)
    (hcover : ∀ x w, (x,w) ∈ E → ∃ a ∈ A w,
      ‖perpendicularPart (NormedSpace.normalize (c-w)) (x-a)‖ ≤ C*δ)
    (hcard : ∀ w, ((A w).card:ℝ) ≤ M)
    (hbudget : M^(n+1)*(generalTubeCountConstant (n+1) C/r^(n+1))^(n*(n+1))*H^n ≤ t^n) :
    ((μ.prod ν) E)^(n+1) ≤ ENNReal.ofReal t+(n+1:ℝ≥0∞)*K := by
  by_contra! hlarge
  have hbad := radial_bad_tuple_mass ν c hr.le hR K hslab
  simp only [measure_univ,one_pow,mul_one] at hbad
  have hgap : (μ univ)^((n+1)-1)*
      (ENNReal.ofReal t*(ν univ)^(n+1)+μ univ*
        (Measure.pi (fun _ : Fin (n+1) => ν)) (radialTupleBad c r)) < ((μ.prod ν) E)^(n+1) := by
    simpa only [measure_univ,one_pow,one_mul,mul_one] using
      lt_of_le_of_lt (add_le_add le_rfl hbad) hlarge
  obtain ⟨w,hw,hmass⟩ := exists_good_common_tuple μ ν (by omega) E hE
    (radialTupleBad c r) (radialTupleBad_measurable c r) (ENNReal.ofReal t) hgap
  obtain ⟨hunit,hgram⟩ := radial_good_tuple_gram c hr w hw
  let S : Set (Space (n+1)) := {x | (x,w) ∈ commonTupleRelation (n+1) E}
  have hS (x) (hx : x ∈ S) (i : Fin (n+1)) : (x,w i) ∈ E := hx i
  have hbd : ∀ x ∈ S, ‖x‖ ≤ B := fun x hx => hbounded x (w 0) (hS x hx 0)
  have hm := general_tube_mass_power hLW hn μ (radialPinTuple c w) hunit
    (pow_pos hr _) (pow_le_one₀ hr.le hr1) hgram S (fun i => A (w i)) B hbd
    hδ hC hH hball (fun i x hx => hcover x (w i) (hS x hx i))
  have hc : (∏ i : Fin (n+1), ((A (w i)).card:ℝ)) ≤ M^(n+1) := by
    calc
      _ ≤ ∏ _i : Fin (n+1), M := Finset.prod_le_prod₀
        (fun i _ => Nat.cast_nonneg _) (fun i _ => hcard (w i))
      _ = _ := by simp
  have hup : (μ S).toReal^n ≤ t^n := by
    have hcount : 0 ≤ generalTubeCountConstant (n+1) C := by
      unfold generalTubeCountConstant
      positivity
    have hp : 0 ≤ (generalTubeCountConstant (n+1) C/r^(n+1))^(n*(n+1)) :=
      pow_nonneg (div_nonneg hcount (pow_nonneg hr.le _)) _
    apply (hm.trans ?_).trans hbudget
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc hp) (pow_nonneg hH _)
  have ht' : t < (μ S).toReal := by
    have hh := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top (measure_ne_top μ S)).mpr hmass
    rwa [ENNReal.toReal_ofReal ht] at hh
  exact (not_lt_of_ge hup) (pow_lt_pow_left₀ ht' ht (by omega))

end Falconer

end OAI
