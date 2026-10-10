import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.FinitePrimeTwistsPowerLogarithmic
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ForwardOnUnit
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.EventualGate

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory

namespace OrdinaryRoughTarget
open OrdinaryCorrelations SourceRoughFourier OrdinaryTwistWidth OrdinaryInitialWidth OrdinaryRoughBridge
open Finset Filter MeasureTheory

theorem eventual_short_twists : ∀ᶠ B : ℝ in atTop,
    ∀ {f : ℕ→ℂ}, OneBounded f → Multiplicative f → UniformlyNonpretentious f →
    ∀ P : Finset ℕ, (∀p∈P,Nat.Prime p) →
    ∀ᶠ U : ℕ in atTop, ∀ E : ℕ,
      (1/2:ℝ)*Real.exp (B^(9999/10000:ℝ))≤E → (E:ℝ)≤(U:ℝ)+1 →
      ∀ t : ℝ, ∀ {N : ℕ} [NeZero N], ∀k:ZMod N,
      (∑v∈Icc 1 U,‖poly (Icc 1 E) (fun m=>twist f P t (v+m)) (fun m=>(m:ZMod N)) k‖)
        ≤8016*B^(-1/950:ℝ)*E*U := by
  obtain ⟨v,hv⟩ := finite_prime_twists_power_logarithmic
  filter_upwards [OrdinaryRoughGate.eventual_gate v,eventually_ge_atTop (1:ℝ)] with B hB hB1
  obtain ⟨m,hm,hε⟩ := hB
  intro f hf hfm hfNP P hP
  have hlim : Tendsto (fun U:ℕ=>(U:ℝ)+1) atTop atTop := by
    apply tendsto_atTop_mono (fun U=>by linarith : ∀U:ℕ,(U:ℝ)≤(U:ℝ)+1)
    exact tendsto_natCast_atTop_atTop
  have hX := hlim.eventually (hv m hf hfm hfNP P hP)
  filter_upwards [hX,eventually_ge_atTop (1:ℕ)] with U hU hU1
  intro E hE hEU t N hN k
  have hi := (grid_short_le_forward (twist f P t) E U k).trans
    (hU E (hm.trans hE) hEU ((k.val:ℝ)/N) t)
  have hUU : (U:ℝ)+1≤2*U := by exact_mod_cast (by omega : U+1≤2*U)
  calc
    _ ≤1002*(1/2:ℝ)^(2*m)*E*((U:ℝ)+1) := hi
    _ ≤1002*(4*B^(-1/950:ℝ))*E*(2*U) := by gcongr
    _ = _ := by ring
end OrdinaryRoughTarget

end

end OAI
