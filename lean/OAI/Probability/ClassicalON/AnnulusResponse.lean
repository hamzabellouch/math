import OAI.Probability.ClassicalON.RotationInequality

namespace OAI

universe uE uV

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON

namespace SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem response_imaginary_multiple (S : SpinSystem 3 V E) (u : E → ℝ) (r : ℝ) :
    (S.complexSecondResponse (fun e => -Complex.I*((r*u e:ℝ):ℂ))
      (fun e => conj (-Complex.I*((r*u e:ℝ):ℂ)))).re = r^2*S.secondAxisResponse u u := by
  have hf : (fun e => -Complex.I*((r*u e:ℝ):ℂ)) = (-Complex.I*(r:ℂ)) • (fun e => (u e:ℂ)) := by
    ext e; simp only [Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul]; ring
  have hg : (fun e => conj (-Complex.I*((r*u e:ℝ):ℂ))) = (Complex.I*(r:ℂ)) • (fun e => (u e:ℂ)) := by
    ext e; simp only [map_mul,map_neg,Complex.conj_I,neg_neg,Complex.conj_ofReal,Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul]; ring
  rw [hf,hg,S.complexSecondResponse_smul_left,S.complexSecondResponse_smul_right,S.complexSecondResponse_ofReal]
  simp only [Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

end SpinSystem

namespace LatticeGraph

def spinSystem (G : LatticeGraph) (n : ℕ) (b : G.edges → ℝ) (P : G.vertices → Option (Spin n)) :
    SpinSystem n G.vertices G.edges := ⟨fun e => e.val.1,fun e => e.val.2,b,P⟩

def BoundaryPins (G : LatticeGraph) (k n : ℕ) (P : G.vertices → Option (Spin n)) : Prop :=
  ∀ x s, P x=some s →
    (|(scaledSite k x.val).1| ≤ 1 ∧ |(scaledSite k x.val).2| ≤ 1) ∨
    (2 ≤ |(scaledSite k x.val).1| ∨ 2 ≤ |(scaledSite k x.val).2|)

theorem modes_zero_pins (G : LatticeGraph) (k n : ℕ) (P : G.vertices → Option (Spin n))
    (hP : G.BoundaryPins k n P) (i : ModeIndex k) (x : G.vertices) (s : Spin n) (hs : P x=some s) :
    G.modes i x=0 := by
  have hp : squareProfile i.1.1 i.1.2 (scaledSite k x.val)=0 := by
    rcases hP x s hs with h | h
    · exact squareProfile_zero_inner _ _ _ h.1 h.2
    · exact squareProfile_zero_outer _ _ _ h
  simp [modes,latticeMode,hp]

theorem system_modes_commutator (G : LatticeGraph) (k : ℕ) (b : G.edges → ℝ) (P : G.vertices → Option (Spin 3)) :
    (∑ i : ModeIndex k, (G.spinSystem 3 b P).commutatorForm (G.modes i) (fun x => conj (G.modes i x))) =
      (fun e => -Complex.I*((dyadicLambda k*G.profileEdge k e:ℝ):ℂ)) := by
  ext e
  rw [Finset.sum_apply]
  convert G.modes_commutator e using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [SpinSystem.commutatorForm,SpinSystem.complexCross,Pi.smul_apply,smul_eq_mul,
    spinSystem,modes,modeCommutator]
  ring

theorem profile_response_bound (G : LatticeGraph) (k : ℕ) (hk : 0 < k) (hG : G.WithinDyadicBox k)
    (β : ℝ) (hβ : 0 ≤ β) (b : G.edges → ℝ) (hb : ∀ e, 0 ≤ b e ∧ b e ≤ β)
    (P : G.vertices → Option (Spin 3)) (hP : G.BoundaryPins k 3 P)
    (C : ℝ) (hC : 0 ≤ C) (hv : ∀ m s z, |squareProfile m s z| ≤ C)
    (hLip : ∀ m s z w, |squareProfile m s w-squareProfile m s z| ≤ C*‖w-z‖) :
    -(G.spinSystem 3 b P).secondAxisResponse (G.profileEdge k) (G.profileEdge k) ≤
      4*((6*β^2+4*β*Real.sqrt β+β)*(48*(2*modeBlockConstant C)^4)+
        β*(576*C^2*(2*modeBlockConstant C)^2))/(k:ℝ) := by
  let a := 2*modeBlockConstant C
  let M := (6*β^2+4*β*Real.sqrt β+β)*(48*a^4)+β*(576*C^2*a^2)
  have ha (m s : Bool) := G.scaledModes_squareBound hG C hv hLip m s
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hLam : (k:ℝ)/2 ≤ dyadicLambda k := dyadicLambda_lower k
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hLp : 0 < dyadicLambda k := by linarith
  have h := (G.spinSystem 3 b P).rotation_family_bound β hβ hb (G.modes (k := k))
    (fun i x s hs => G.modes_zero_pins k 3 P hP i x s hs)
  have hd : (fun i : ModeIndex k => (G.spinSystem 3 b P).differential (G.modes i)) = G.modeDifferences := rfl
  rw [G.system_modes_commutator k b P, (G.spinSystem 3 b P).response_imaginary_multiple,hd] at h
  have hHS := G.modes_HS_bound a ha
  have hmin := G.modes_min_bound a C hC hv ha
  have hK : 0 ≤ 6*β^2+4*β*Real.sqrt β+β := by positivity
  have hcost : (6*β^2+4*β*Real.sqrt β+β)*familyHSSquare (G.modeDifferences (k := k))+
      β*(∑ i : ModeIndex k, ∑ j : ModeIndex k,
      min (‖G.modes i‖^2*∑ e, ‖G.modeDifferences j e‖^2)
          (‖G.modes j‖^2*∑ e, ‖G.modeDifferences i e‖^2)) ≤ M*(k:ℝ) := by
    calc _ ≤ (6*β^2+4*β*Real.sqrt β+β)*(48*a^4*(k:ℝ))+β*(576*C^2*a^2*(k:ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hHS hK) (mul_le_mul_of_nonneg_left hmin hβ)
         _ = _ := by dsimp only [M]; ring
  have hfinal : -(G.spinSystem 3 b P).secondAxisResponse (G.profileEdge k) (G.profileEdge k) ≤ 4*M/(k:ℝ) := by
    by_cases hr : (G.spinSystem 3 b P).secondAxisResponse (G.profileEdge k) (G.profileEdge k) ≤ 0
    · apply (le_div_iff₀ hkR).mpr
      have hsq : (k:ℝ)^2/4 ≤ (dyadicLambda k)^2 := by nlinarith
      have hh := mul_le_mul_of_nonneg_right hsq (neg_nonneg.mpr hr)
      have ht := h.trans hcost
      nlinarith
    · have hh : 0 ≤ 4*M/(k:ℝ) := by positivity
      linarith
  exact hfinal

end LatticeGraph
end ClassicalON

end

end OAI
