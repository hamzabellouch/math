import OAI.MeasureTheory.Falconer.Radial.UniformProjectionCollision
import OAI.MeasureTheory.Falconer.Recursion.SuffixDirectionGeometry
import OAI.MeasureTheory.Falconer.Angular.SuffixAngularRadius

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem uniform_actual_suffix_projection {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) (K : ℝ) :
    ∃ N₀ : ℕ, ∀ d : PositiveDistanceData, d.sig = sig → d.J = J →
      N₀ ≤ d.N → d.Q.side = 1 → d.StronglySeparated → 0 < d.q →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      d.a+100*d.q < d.t → d.t ≤ d.N → d.i ≤ J →
      let p := policyDepth (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t
      d.a+d.t < 2*p → ∀ P C : CellPath, P.length = p → C.length = p →
      P.take d.a = d.X → C.take d.a = d.Y →
      ∀ x ∈ (d.Q.descendant P).carrier, ∀ y ∈ (d.Q.descendant C).carrier,
      (x,y) ∈ d.good →
      ((d.ρ.restrict (d.Q.descendant C).carrier).prod (d.ρ.restrict (d.Q.descendant C).carrier))
        {z : Plane × Plane | |planeDot (z.1-z.2)
          (sourceRadialUnit (d.Q.descendant C).center (d.Q.descendant P).center : Plane)| ≤
            K/(2:ℝ)^d.t} ≤
        (d.ρ (d.Q.descendant C).carrier)^2 * ENNReal.ofReal (((2:ℝ)^d.N)^
          (-(d.mass d.t-d.mass p)+height (fun n : ℕ => d.mass n-(n:ℝ)/(d.N:ℝ)) p d.t+
            2000*(d.lam+sig)+12*d.lam)) := by
  obtain ⟨N₀,hN₀⟩ := uniform_profile_projection_collision hsig hJ 1 K
  refine ⟨N₀,?_⟩
  intro d hsig' hJ' hN hQ hs hq B δ hprof hw htN hi p hsuffix P C hP hC hPX hCY x hx y hy hg
  have hside : 0 < d.Q.side := by rw [hQ]; norm_num
  have hp := policyDepth_interior (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) hq
    (policyBlocks_nonempty hq htN hw)
  have hpt : p ≤ d.t := by dsimp [p]; omega
  have hmem := suffix_projection_mem (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) htN hw hsuffix
  have hgC := (hg _ hmem).2 C ((mem_dyadicPaths _ _).mpr hC) hy
  have hdir := d.fine_directions hQ hs hP hC hPX hCY hx hy
    ((d.Q.descendant P).center_mem (d.Q.descendant_side_pos hside P))
    ((d.Q.descendant C).center_mem (d.Q.descendant_side_pos hside C))
  have hsmall := hdir.trans (suffix_direction_scale (by omega : d.a+d.t ≤ 2*p) hpt)
  rw [hsig',hJ'] at hgC
  exact hN₀ d.N hN d.Q hQ d.ρ B δ d.lam d.mass hprof p d.t hpt htN C hC
    d.i hi _ _ hsmall hgC

end PlanarFalconer

end OAI
