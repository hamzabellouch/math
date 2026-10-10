import OAI.NumberTheory.Jacobsthal.Estimates.RepresentativeAdmission

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.PrimeProductLogCoordinates
open FinitePathGeometry PrimeHistories RepresentativeAdmission
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem log_nat_product (ps : List ℕ) (hp : ∀ p ∈ ps,0 < p) :
    Real.log (ps.prod:ℝ)=(ps.map (fun p : ℕ => Real.log (p:ℝ))).sum := by
  rw [Nat.cast_list_prod]
  have hh := Real.log_list_prod (l := ps.map (fun p : ℕ => (p:ℝ))) (by
    intro x hx
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hx
    exact_mod_cast (hp p hp').ne')
  simpa only [List.map_map,Function.comp_def] using hh

theorem exponent_sum_log_product (w : ℝ) (ps : List ℕ) (hp : ∀ p ∈ ps,0 < p) :
    (ps.map (primeExponent w)).sum=Real.log (ps.prod:ℝ)/Real.log w := by
  rw [log_nat_product ps hp]
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,add_div,primeExponent]
    rw [ih (fun q hq => hp q (by simp [hq]))]

theorem terminal_gap_log_quotient {w a : ℝ} (Y : ℕ) (hY : 0 < Y) (z : Node)
    (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (ps : List ℕ) (hp : ∀ p ∈ ps,0 < p) :
    (terminal w z ps).gap=Real.log ((Y:ℝ)/(ps.prod:ℝ))/Real.log w-a+2 := by
  have hprodNat : 0 < ps.prod := List.prod_pos hp
  have hprod : 0 < (ps.prod:ℝ) := by exact_mod_cast hprodNat
  have hYr : 0 < (Y:ℝ) := by exact_mod_cast hY
  rw [terminal_gap_sum,exponent_sum_log_product w ps hp,hroot,Real.log_div hYr.ne' hprod.ne']
  ring

theorem source_length_exponent_identity {w a : ℝ} (hw : 1 < w) (Y P : ℕ)
    (hY : 0 < Y) (hP : 1 < P) (z : Node)
    (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (ps : List ℕ) (hp : ∀ p ∈ ps,0 < p) :
    Real.log ((Y:ℝ)/(ps.prod:ℝ))/Real.log (P:ℝ)=
      (terminal w z ps).gap/primeExponent w P+(a-2)/primeExponent w P := by
  have hlogw : 0 < Real.log w := Real.log_pos hw
  have hlogP : 0 < Real.log (P:ℝ) := Real.log_pos (by exact_mod_cast hP)
  rw [terminal_gap_log_quotient Y hY z hroot ps hp,primeExponent]
  field_simp [hlogw.ne',hlogP.ne']
  ring
end NumberTheoryLean.PrimeProductLogCoordinates


end Erdos970

end OAI
