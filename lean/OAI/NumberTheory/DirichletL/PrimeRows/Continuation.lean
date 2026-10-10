import OAI.NumberTheory.DirichletL.PrimeRows.Product
import OAI.NumberTheory.DirichletL.Detector.HighRowsHolomorphic

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

lemma actualACube_norm_le (η : Character) (p : O) : ‖actualACube η p‖≤1 := by
  have h := actualAPhase_norm_le_one η p
  rw [←actualACube_sq,norm_pow] at h
  nlinarith [norm_nonneg (actualACube η p)]

theorem ramifiedCorrection_analytic_x (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (w z : ℂ) (hz : (4/25 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x =>ramifiedCorrection η u P hs x w z) {x : ℂ | 7/8<x.re} := by
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_analytic_x
  · simpa only [span_primaryGenerator_of_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hz

theorem ramifiedCorrection_analytic_w (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (x z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hz : (4/25 : ℝ)≤z.re) :
    Differentiable ℂ (fun w =>ramifiedCorrection η u P hs x w z) := by
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_analytic_w
  · simpa only [span_primaryGenerator_of_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hx
  · exact hz

theorem ramifiedCorrection_analytic_z (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (x w : ℂ) (hx : (7/8 : ℝ)≤x.re) :
    AnalyticOnNhd ℂ (fun z =>ramifiedCorrection η u P hs x w z) {z : ℂ | 4/25<z.re} := by
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_analytic_z
  · simpa only [span_primaryGenerator_of_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hx

def ramifiedProduct (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ∏ P∈(ramifiedPrimes S u).attach,ramifiedCorrection η u P.val
    (outside_prime_supported S hS.bad P.val (Finset.mem_filter.mp P.property).2) x w z

def continuedCorrection (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ramifiedProduct S hS η u x w z*unramifiedProduct S η u x w z

theorem continuedCorrection_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (η : Character) (u : FreeRow) (x w z : ℂ),
      (7/8 : ℝ)≤x.re → (19/20 : ℝ)≤w.re → (33/200 : ℝ)≤z.re →
      ‖continuedCorrection S hS η u x w z‖≤C*((Ideal.span {u.val}:Ideal O).absNorm : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := ramified_product_subpower ε hε
  refine ⟨C*(3/2),by positivity,?_⟩
  intro S hS η u x w z hx hw hz
  have hR := hbound S hS η u x w z hx hw hz
  have hU := unramifiedProduct_defect S hS.tail η u x w z hx (by linarith) (by linarith)
  have hnorm : ‖unramifiedProduct S η u x w z‖≤3/2 := by
    have hh := norm_add_le (unramifiedProduct S η u x w z-1) (1 : ℂ)
    simp only [sub_add_cancel,norm_one] at hh
    linarith
  rw [continuedCorrection,norm_mul]
  apply (mul_le_mul hR hnorm (norm_nonneg _) (by positivity)).trans
  exact le_of_eq (by ring)

theorem continuedCorrection_analytic_x (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (w z : ℂ) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x =>continuedCorrection S hS η u x w z) {x : ℂ | 7/8<x.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_analytic_x S hS.tail η u w z hw hz)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  exact ramifiedCorrection_analytic_x η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2) w z hz

theorem continuedCorrection_analytic_w (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x z : ℂ) (hx : (7/8 : ℝ)≤x.re) (hz : (4/25 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun w =>continuedCorrection S hS η u x w z) {w : ℂ | 9/10<w.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_analytic_w S hS.tail η u x z hx hz)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  exact (ramifiedCorrection_analytic_w η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2) x z hx hz).differentiableOn.analyticOnNhd
      (Complex.isOpen_re_gt _)

theorem continuedCorrection_analytic_z (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w : ℂ) (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)≤w.re) :
    AnalyticOnNhd ℂ (fun z =>continuedCorrection S hS η u x w z) {z : ℂ | 4/25<z.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_analytic_z S hS.tail η u x w hx hw)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  exact ramifiedCorrection_analytic_z η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2) x w hx

end SevenEighths.ProbeHighRowFamily

end

end OAI
