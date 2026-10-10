import OAI.MeasureTheory.Falconer.Fourier.RootPairSymbols
import OAI.MeasureTheory.Falconer.Angular.RootStationaryScale
import OAI.MeasureTheory.Falconer.Shells.HighShellCone
import OAI.MeasureTheory.Falconer.Angular.InverseCircleArcLength

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology ComplexConjugate

theorem uniform_root_high_shell_inverse {sig δ T : ℝ}
    (hsig : 0 < sig) (hsmall : sig ≤ 1/4) (hδ : 0 < δ) :
    ∃ n N₀ : ℕ, ∀ N ≥ N₀, ∀ d e : RootEndpointData,
    0 < d.Q.side → 0 < e.Q.side →
    d.S.card ≤ (N+1)^3+1 → e.S.card ≤ (N+1)^3+1 →
    (∀ b ∈ d.S, descriptorLength b ≤ N/2) →
    (∀ b ∈ e.S, descriptorLength b ≤ N/2) →
    ∀ U V : DyadicSquare, 0 < U.side → 0 < V.side →
    ∀ s : ℝ, U.side ≤ s → V.side ≤ s → 100*s ≤ dist U.center V.center →
    ∀ r : ℝ, (2:ℝ)^((N:ℝ)-1) ≤ r →
    ∀ x ∈ U.carrier, ∀ y ∈ V.carrier, δ ≤ dist x y →
    ‖Complex.exp (Complex.I*((r*dist x y:ℝ):ℂ))*(rootPairMask d e N sig (x,y):ℂ) -
      sourceInverseCircleIntegral n r (x-y) (sourceConeCircle (sourceParentAxis U V))
        (rootPairSymbol d e N sig (x,y))‖ ≤ ((2:ℝ)^N)^(-T) := by
  obtain ⟨n,hn⟩ := rotated_inverse_circle_power (T := T) (c := 1) (by norm_num) hsig
  obtain ⟨P,hP,hPb⟩ := sourceConeCircle_uniform_derivatives (4*(n+1)+2)
  obtain ⟨C,hC,N₁,h₁⟩ := uniform_root_pair_derivatives hsig 0 (4*(n+1)+2)
  obtain ⟨N₂,h₂⟩ := hn P C hP hC
  obtain ⟨N₃,h₃⟩ := root_stationary_slack hsig hsmall hδ
  refine ⟨n,max (max N₁ N₂) N₃,?_⟩
  intro N hN d e hd he hc₁ hc₂ hL₁ hL₂ U V hU hV s hUs hVs hsep r hr x hx y hy hxy
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN₃ : N₃ ≤ N := (le_max_right _ _).trans hN
  have hder := h₁ N hN₁ d e hd he hc₁ hc₂ (fun _ => 0) (fun _ => 0)
    (by simp) (by simp) (N/2) hL₁ hL₂ (fun _ => 1) (fun _ => 1) x y (by simp) (by simp)
  let f := fun θ => rootPairSymbol d e N sig (x,y) (sourceUnitDirection θ)
  have hf : ContDiff ℝ ∞ f := by
    simpa only [f,rootPairSymbol_inherited] using hder.1
  have hb : ∀ j ≤ 4*(n+1)+2, ∀ θ, ‖iteratedDeriv j f θ‖ ≤ C*sourceSymbolScale N sig (N/2)^j := by
    simpa only [f,rootPairSymbol_inherited] using hder.2
  let axis := sourceParentAxis U V
  obtain ⟨φ,hφ,hdir,hgeom⟩ := strong_separation_parent_angle U V hU hV hUs hVs hsep hx hy
  have hdir' : sourceUnitDirection (φ+axis) = sourceRadialUnit y x := by
    have hh := congrArg (sourceCircleRotate axis) hdir
    simpa only [axis,sourceCircleRotate_comp,sourceCircleRotate_add,neg_add_cancel,
      sourceCircleRotate_zero] using hh
  have hval : f (φ+axis) = (rootPairMask d e N sig (x,y):ℂ) := by
    change rootPairSymbol d e N sig (x,y) (sourceUnitDirection (φ+axis)) = _
    rw [hdir',rootPairSymbol_radial]
  have hslack := h₃ N hN₃ (N/2) (by omega) r (dist x y) hr hxy
  have hψ := sourceConeCircle_rotated_contDiff axis
  obtain ⟨hg₁,hg₂⟩ := sourceConeCircle_inverse_germs axis hφ
  have hpψ : Function.Periodic (fun θ => sourceConeCircle axis (sourceUnitDirection θ)) (2*Real.pi) :=
    fun θ => congrArg (sourceConeCircle axis) (sourceUnitDirection_periodic θ)
  have hpf : Function.Periodic f (2*Real.pi) :=
    fun θ => congrArg (rootPairSymbol d e N sig (x,y)) (sourceUnitDirection_periodic θ)
  have hh := h₂ N hN₂ hψ hf hpψ hpf (φ+axis) hg₁ hg₂
    (sourceSymbolScale_one_le N hsig.le (N/2))
    (by simpa only [one_mul] using hslack.1)
    (sourceSymbolScale_upper N hsig.le (Nat.div_le_self N 2))
    (by simpa only [neg_mul,one_mul] using hslack.2) (hPb axis) hb
  rw [hval] at hh
  rw [sourceInverseCircleIntegral_eq n r (φ+axis) hgeom hψ.continuous hf]
  simpa only [dist_eq_norm] using hh

end PlanarFalconer

end OAI
