import Mathlib
import OAI.Geometry.HypersurfaceGerms.Orders
import OAI.Geometry.HypersurfaceGerms.PlaneIsolation
import OAI.Geometry.HypersurfaceGerms.Reducedness

namespace OAI

/-! Reduced isolated holomorphic germs with specified ordinary orders. -/

namespace AmbientMultiplicity

abbrev C4 := Fin 4 → ℂ

 
def ReducedAtZero (f : C4 → ℂ) : Prop :=
  ∀ g k : C4 → ℂ, AnalyticAt ℂ g 0 → AnalyticAt ℂ k 0 →
    (∀ᶠ z in nhds (0 : C4), f z = g z ^ 2 * k z) → g 0 ≠ 0

 
def HasOrderAtZero (f : C4 → ℂ) (n : ℕ) : Prop :=
  (∀ m : ℕ, m < n → iteratedFDeriv ℂ m f 0 = 0) ∧
    iteratedFDeriv ℂ n f 0 ≠ 0

 
def IsolatedCriticalAtZero (f : C4 → ℂ) : Prop :=
  fderiv ℂ f 0 = 0 ∧
    ∀ᶠ z in nhds (0 : C4), z ≠ 0 → fderiv ℂ f z ≠ 0

 
def AmbientPairEquivalent (f g : C4 → ℂ) : Prop :=
  ∃ e : OpenPartialHomeomorph C4 C4,
    (0 : C4) ∈ e.source ∧ e 0 = 0 ∧
      ∀ z ∈ e.source, (f z = 0 ↔ g (e z) = 0)

 
def MainStatement : Prop :=
  ∃ f4 f5 : C4 → ℂ,
    AnalyticAt ℂ f4 0 ∧ AnalyticAt ℂ f5 0 ∧
    f4 0 = 0 ∧ f5 0 = 0 ∧
    ReducedAtZero f4 ∧ ReducedAtZero f5 ∧
    IsolatedCriticalAtZero f4 ∧ IsolatedCriticalAtZero f5 ∧
    HasOrderAtZero f4 4 ∧ HasOrderAtZero f5 5 ∧
    AmbientPairEquivalent f4 f5


 
section PolynomialInput
variable {R : Type*} [CommRing R]

def planeH (X T : R) : R := T * (X - T ^ 2) * (X - 2 * T ^ 2)
def planeHX (X T : R) : R := T * (2 * X - 3 * T ^ 2)
def planeHT (X T : R) : R := X ^ 2 - 9 * T ^ 2 * X + 10 * T ^ 4

def planeQ1 (u w : R) : R := (u - w - w ^ 8) * (u - w - 2 * w ^ 8) * (u - w ^ 2)
def planeQ2 (u w : R) : R := planeQ1 u w - u ^ 2
def graphPhi (u w : R) : R := u ^ 2 + planeQ1 u w
def graphPsi (x w : R) : R :=
  let u := x + w
  u * (u - w ^ 2) * planeQ2 u w

theorem planeH_expansion (X T : R) :
    planeH X T = T * X ^ 2 - 3 * X * T ^ 3 + 2 * T ^ 5 := by
  unfold planeH
  ring

 
theorem gradient_elimination (X T : R) :
    planeHX X T * (2 * X - 15 * T ^ 2) - 4 * T * planeHT X T = 5 * T ^ 5 := by
  unfold planeHX planeHT
  ring
end PolynomialInput

 
theorem base_gradient_zero_iff (X T : ℂ) :
    planeHX X T = 0 ∧ planeHT X T = 0 ↔ X = 0 ∧ T = 0 := by
  constructor
  · rintro ⟨hX, hT⟩
    have he := gradient_elimination X T
    rw [hX, hT] at he
    have ht5 : T ^ 5 = 0 := by linear_combination -(1 / 5 : ℂ) * he
    have ht : T = 0 := by simpa using ht5
    have hx2 : X ^ 2 = 0 := by simpa [planeHT, ht] using hT
    exact ⟨by simpa using hx2, ht⟩
  · rintro ⟨rfl, rfl⟩
    simp [planeHX, planeHT]


noncomputable section
open Filter Topology

lemma critical_origin_of_order {f : C4 → ℂ} {n : ℕ}
    (hn : 1 < n) (hf : HasOrderAtZero f n) : fderiv ℂ f 0 = 0 := by
  have h := hf.1 1 hn
  ext x
  have h' := congrArg (fun L => L (fun _ : Fin 1 => x)) h
  simpa only [iteratedFDeriv_one_apply, zero_apply] using h'

 
theorem exact_source_germs (s : ℂ) (hs : s ≠ 0) (a b : ℕ)
    (ha : 11 ≤ a) (hb : 11 ≤ b) :
    AnalyticAt ℂ (Preparation.f4 s a b) 0 ∧
    AnalyticAt ℂ (Preparation.f5 s a b) 0 ∧
    Preparation.f4 s a b 0 = 0 ∧ Preparation.f5 s a b 0 = 0 ∧
    ReducedAtZero (Preparation.f4 s a b) ∧
    ReducedAtZero (Preparation.f5 s a b) ∧
    IsolatedCriticalAtZero (Preparation.f4 s a b) ∧
    IsolatedCriticalAtZero (Preparation.f5 s a b) ∧
    HasOrderAtZero (Preparation.f4 s a b) 4 ∧
    HasOrderAtZero (Preparation.f5 s a b) 5 := by
  have h4 : HasOrderAtZero (Preparation.f4 s a b) 4 :=
    Preparation.order_four s hs (by omega) (by omega)
  have h5 : HasOrderAtZero (Preparation.f5 s a b) 5 :=
    Preparation.order_five s hs (by omega) (by omega)
  have hi4 := Preparation.f4_critical_isolated s hs a b ha hb
  have hi5 := Preparation.f5_critical_isolated s hs a b ha hb
  refine ⟨Preparation.f4_analytic s a b, Preparation.f5_analytic s a b,
    Preparation.f4_zero s a b, Preparation.f5_zero s a b, ?_, ?_, ?_, ?_, h4, h5⟩
  · exact ReducedIsolation.no_square_factor hi4
  · exact ReducedIsolation.no_square_factor hi5
  · refine ⟨critical_origin_of_order (by norm_num) h4, ?_⟩
    filter_upwards [hi4] with z hz hn hc
    exact hn (hz hc)
  · refine ⟨critical_origin_of_order (by norm_num) h5, ?_⟩
    filter_upwards [hi5] with z hz hn hc
    exact hn (hz hc)

end
end AmbientMultiplicity

end OAI
