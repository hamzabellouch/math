import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.Rescaling
import OAI.Analysis.CoulombRadii.Propagation.RetainedGoodEvent

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom

def physical_family_of_data {Ω : ℕ → Type*} [∀ n,MeasurableSpace (Ω n)]
    (P : ∀ n,Measure (Ω n)) (μ : ∀ n,Ω n → Position → ℝ)
    (Z q : ℕ → ℕ) (s r : ℕ → ℝ) (B C L Ccap : ℝ)
    (hB : 0 < B) (hcap : 0 ≤ Ccap) (hs : ∀ n,0 < s n) (hr : ∀ n,0 < r n)
    (hslim : Tendsto s atTop (𝓝 0)) (hqlim : Tendsto q atTop atTop)
    (hlo : ∀ n,1/(2*(q n:ℝ)) ≤ r n/s n) (hhi : ∀ n,r n/s n ≤ (q n:ℝ)⁻¹)
    (hμi : ∀ n o,Integrable (μ n o)) (hμp : ∀ n o x,0 ≤ μ n o x)
    (Aμ : ℕ → ℝ) (hμb : ∀ n o x,μ n o x ≤ Aμ n)
    (hμmass : ∀ n o,(∫ x,μ n o x)=(Z n:ℝ))
    (d : ∀ n,PropagationDatum (P n) B C (r n) (Z n:ℝ) L (μ n))
    (G : ∀ n,Set (Ω n))
    (hvalid : ∀ n o,o∈G n → PropagationInvariant B C (r n) (Z n:ℝ) L
      ((d n).offset o) (μ n o) ((d n).error o) ∧ Integrable ((d n).error o) ∧
      (∫ x,(d n).error o x) ≤ 1)
    (hband : ∀ n o,o∈G n → ∀ x,r n ≤ ‖x‖ → ‖x‖ ≤ (q n:ℝ)*s n →
      screenedField (Z n:ℝ) (μ n o) x ≤ Ccap/‖x‖^4 ∧
      |μ n o x-tfDensityScalar (screenedField (Z n:ℝ) (μ n o) x)| ≤ ((q n:ℝ)^8)⁻¹/‖x‖^6) :
    PhysicalRetainedFamily (fun n => G n) where
  μ := fun n o => μ n o
  u := fun n o x => (Z n:ℝ)*coulombKernel x+(d n).offset o x
  p := fun n o => (d n).error o
  Z := Z
  s := s
  r := r
  q := q
  Aμ := fun n _ => Aμ n
  Ap := fun n _ => ((d n).error_global_bound).choose
  B := B
  Ccap := Ccap
  Cinv := C
  Bpos := hB
  Cpos := hcap
  sp := hs
  rp := hr
  slim := hslim
  qlim := hqlim
  rlo := hlo
  rhi := hhi
  μi := fun n o => hμi n o
  μp := fun n o => hμp n o
  μb := fun n o => hμb n o
  μmass := fun n o => hμmass n o
  pi := fun n o => (hvalid n o o.property).2.1
  pp := fun n o => (hvalid n o o.property).1.nonnegative_error
  pb := fun n o => ((d n).error_global_bound).choose_spec o (hvalid n o o.property).1
  ps := fun n o x hx => (hvalid n o o.property).1.error_support x hx.le
  pm := fun n o => (hvalid n o o.property).2.2
  ucont := fun n o => by simpa only [add_sub_cancel_left] using (hvalid n o o.property).1.continuous_offset
  ubounds := fun n o x hx => by
    simpa only [propagationBarrier_eq] using (hvalid n o o.property).1.caps x hx
  uweak := fun n o => by
    rw [show barrierSource (r n) (fun x => (Z n:ℝ)*coulombKernel x+(d n).offset o x)
      (μ n o) ((d n).error o) = (fun x => propagationRHS (r n) ‖x‖ (μ n o x)
        ((d n).error o x) ((Z n:ℝ)*coulombKernel x+(d n).offset o x)) from
      funext (barrierSource_eq_propagationRHS _ _ _ _)]
    exact (hvalid n o o.property).1.weak
  band := fun n o => hband n o o.property
end NeutralAtom
end

end

end OAI
