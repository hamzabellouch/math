import OAI.NumberTheory.Ostmann.Construction.InitialEtaCRTTransform

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators FourierTransform
namespace Ostmann.Construction.InitialEta

def stateAtFrequency (a : State) (s : ℤ) : State := {a with frequency := s}

theorem state_normalized_poisson_base (d : Decomposition) (P : Finset ℕ)
    (a : State) (outside : List ℕ)
    (hp : ∀ q ∈ a.values ++ outside, q.Prime)
    (hnd : (a.values ++ outside).Nodup)
    {X : ℝ} (hX : 0 < X) (V : ℕ)
    (hV : ((outsideProduct outside*a.product:ℕ):ℝ)/(4*X) ≤ V) (B : ℝ) :
    (B:ℂ)*(∑' n : ℤ,statePhysicalProduct d P a outside n *
      SchwartzCutoff.psi ((n:ℝ)/X))/(Real.sqrt X:ℂ) =
    ∑ s ∈ Finset.Icc (-(V:ℤ)) (V:ℤ),
      regularTransform (residueTransform d) (favorableGiantResidueTransform d P)
        outside (stateAtFrequency a s) *
      baseCoefficient X (fun ξ => 𝓕 SchwartzCutoff.psi ξ) (residueTransform d)
        (fun _ _ => B) outside (stateAtFrequency a s) := by
  have hpi := stateModuli_prime a outside hp
  let : ∀ i, NeZero (stateModuli a outside i) := fun i => ⟨(hpi i).ne_zero⟩
  let : NeZero (∏i,stateModuli a outside i) :=
    ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => (hpi i).ne_zero)⟩
  have hc := stateModuli_pairwise a outside (state_coprime_of_distinct a outside hp hnd)
  have hcut : (((∏i,stateModuli a outside i):ℕ):ℝ)/(4*X) ≤ V := by
    rw [stateModuli_prod]
    exact hV
  have hcrt := crt_normalized_poisson_finite (stateModuli a outside) hc
    (stateLocalTest d P a outside) hX V hcut
  simp_rw [stateLocalTest_product,stateLocalTest_unitary_product d P a outside _ hp] at hcrt
  rw [stateModuli_prod] at hcrt
  rw [mul_div_assoc,hcrt,← mul_assoc,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have ha : (stateAtFrequency a s).Positive := by
    intro q hq
    exact (hp q (List.mem_append_left outside hq)).pos
  simpa only [Nat.cast_mul, stateAtFrequency, completeTransform, State.product, State.values] using completeTransform_scalar_eq_base (residueTransform d)
    (favorableGiantResidueTransform d P) X (fun ξ => 𝓕 SchwartzCutoff.psi ξ)
    (fun _ _ => B) (stateAtFrequency a s) outside ha

end Ostmann.Construction.InitialEta

end

end OAI
