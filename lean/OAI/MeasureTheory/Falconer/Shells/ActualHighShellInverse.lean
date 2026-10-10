import OAI.MeasureTheory.Falconer.Fourier.MinimalPairSymbol
import OAI.MeasureTheory.Falconer.Shells.HighShellNormalization
import OAI.MeasureTheory.Falconer.Shells.HighShellCone
import OAI.MeasureTheory.Falconer.Angular.InverseCircleArcLength

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology ComplexConjugate

namespace PositiveDistanceData

theorem uniform_actual_high_shell_inverse {sig T : ℝ} (hsig : 0 < sig) :
    ∃ n N₀ : ℕ, ∀ d : PositiveDistanceData, N₀ ≤ d.N → d.sig = sig →
    0 < d.Q.side → d.StronglySeparated → 0 < d.q →
    d.sig*d.N ≤ (d.q:ℝ) → d.a+100*d.q < d.t → d.t ≤ d.N →
    ∀ v r : ℝ, (d.t:ℝ)-d.sig*d.N ≤ v → (2:ℝ)^(v-1) ≤ r →
    ∀ x ∈ (d.Q.descendant d.X).carrier, ∀ y ∈ (d.Q.descendant d.Y).carrier,
    ‖Complex.exp (Complex.I*((r*dist x y:ℝ):ℂ))*(d.minimalMask (x,y):ℂ) -
      sourceInverseCircleIntegral n r (x-y)
        (sourceConeCircle (sourceParentAxis (d.Q.descendant d.X) (d.Q.descendant d.Y)))
        (d.pairMaskSymbol (x,y))‖ ≤ ((2:ℝ)^d.N)^(-T) := by
  obtain ⟨n,hn⟩ := rotated_inverse_circle_power (T := T) (c := 90) (by norm_num) hsig
  obtain ⟨P,hP,hPb⟩ := sourceConeCircle_uniform_derivatives (4*(n+1)+2)
  obtain ⟨C,hC,N₁,h₁⟩ := uniform_actual_pair_derivatives hsig 0 (4*(n+1)+2)
  obtain ⟨N₂,h₂⟩ := hn P C hP hC
  refine ⟨n,max N₁ N₂,?_⟩
  intro d hN hdsig hQ hs hq hqscale hw ht v r hv hr x hx y hy
  subst sig
  let S := policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t
  let L := (d.t-d.a)/2
  have hLN : L ≤ d.N := by dsimp [L]; omega
  have hcard : S.card ≤ (d.N+1)^3+1 := (policyDescriptorList_card _ hq).trans (by omega)
  have hL : ∀ b ∈ S, descriptorLength b ≤ L := fun b hb => policyDescriptor_length_le_half _ hq hb
  have hder := h₁ d.N ((le_max_left _ _).trans hN) S id (fun _ => 0) hcard
    (by simp) L hL d.Q hQ d.ρ d.mass d.lam d.J d.i (fun _ => 1) x y (by simp) (by simp)
  let f := fun θ => d.pairMaskSymbol (x,y) (sourceUnitDirection θ)
  have he : f = fun θ =>
      inheritedCircleSymbol S id (fun _ => 0) d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i (fun _ => 1) x (sourceUnitDirection θ) *
      conj (inheritedCircleSymbol S id (fun _ => 0) d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i (fun _ => 1) y (sourceUnitDirection θ)) :=
    funext (fun θ => d.pairMaskSymbol_inherited (x,y) (sourceUnitDirection θ))
  have hf : ContDiff ℝ ∞ f := by rw [he]; exact hder.1
  have hb : ∀ j ≤ 4*(n+1)+2, ∀ θ, ‖iteratedDeriv j f θ‖ ≤ C*sourceSymbolScale d.N d.sig L^j := by
    rw [he]; exact hder.2
  let axis := sourceParentAxis (d.Q.descendant d.X) (d.Q.descendant d.Y)
  obtain ⟨φ,hφ,hdir,hgeom⟩ := strong_separation_parent_angle _ _
    (d.Q.descendant_side_pos hQ _) (d.Q.descendant_side_pos hQ _)
    hs.1 hs.2.1 hs.2.2.1 hx hy
  have hdir' : sourceUnitDirection (φ+axis) = sourceRadialUnit y x := by
    have hh := congrArg (sourceCircleRotate axis) hdir
    simpa only [axis,sourceCircleRotate_comp,sourceCircleRotate_add,neg_add_cancel,
      sourceCircleRotate_zero] using hh
  have hval : f (φ+axis) = (d.minimalMask (x,y):ℂ) := by
    change d.pairMaskSymbol (x,y) (sourceUnitDirection (φ+axis)) = _
    rw [hdir',pairMaskSymbol_radial]
  have hslack := d.actual_high_shell_stationary_slack hQ hs hsig.le hqscale hw hv hr (z := (x,y)) hx hy
  have hψ := sourceConeCircle_rotated_contDiff axis
  obtain ⟨hg₁,hg₂⟩ := sourceConeCircle_inverse_germs axis hφ
  have hpψ : Function.Periodic (fun θ => sourceConeCircle axis (sourceUnitDirection θ)) (2*Real.pi) :=
    fun θ => congrArg (sourceConeCircle axis) (sourceUnitDirection_periodic θ)
  have hpf : Function.Periodic f (2*Real.pi) :=
    fun θ => congrArg (d.pairMaskSymbol (x,y)) (sourceUnitDirection_periodic θ)
  have hh := h₂ d.N ((le_max_right _ _).trans hN) hψ hf hpψ hpf (φ+axis)
    hg₁ hg₂ (sourceSymbolScale_one_le d.N hsig.le L) hslack.1
    (sourceSymbolScale_upper d.N hsig.le hLN) hslack.2 (hPb axis) hb
  rw [hval] at hh
  rw [sourceInverseCircleIntegral_eq n r (φ+axis) hgeom hψ.continuous hf]
  simpa only [dist_eq_norm] using hh

end PositiveDistanceData

end PlanarFalconer

end OAI
