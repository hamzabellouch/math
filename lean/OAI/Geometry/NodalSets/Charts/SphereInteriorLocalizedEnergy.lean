import OAI.Geometry.NodalSets.Charts.SphereInteriorFluxCoercivity
import OAI.Geometry.NodalSets.Elliptic.RealDivergenceEnergyAE
import OAI.Geometry.NodalSets.Elliptic.RealInteriorSquareDifferenceTest
import OAI.Geometry.NodalSets.Elliptic.RealLocalWeakDifferenceBound
import OAI.Geometry.NodalSets.Elliptic.RealLocalizedDifferenceIdentity
import OAI.Geometry.NodalSets.Elliptic.RealSquareDifferenceEnergy

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_interior_localized_energy (d : SphereEnergyData) (p : Base) :
    ∃ m > 0, ∃ K > 0,
      ∀ (R0 r : ℝ), r ≤ R0 → R0 ≤ 1 →
      ∀ (u : Yau.Jets.Coord → ℝ) (V0 P0 G : Fin 4 → Yau.Jets.Coord → ℝ)
        (DG : Fin 4 → Fin 4 → Yau.Jets.Coord → ℝ) (F0 : Yau.Jets.Coord → ℝ),
      let Q := Yau.realCenteredCube 4 R0
      MemLp u 2 (volume.restrict Q) →
      (∀ a, MemLp (V0 a) 2 (volume.restrict Q)) →
      (∀ a, MemLp (P0 a) 2 (volume.restrict Q)) →
      (∀ j, MemLp (G j) 2 (volume.restrict Q)) →
      (∀ j i, MemLp (DG j i) 2 (volume.restrict Q)) →
      MemLp F0 2 (volume.restrict Q) →
      (∀ a, P0 a =ᵐ[volume.restrict (interior Q)] V0 a) →
      (∀ j psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, u x*Yau.coordPartial psi x j)=-(∫ x in Q, V0 j x*psi x)) →
      (∀ j i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, G j x*Yau.coordPartial psi x i)=-(∫ x in Q, DG j i x*psi x)) →
      (∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∑ a, ∑ j, ∫ x in Q, sphereChartPrincipalDensity d p x a j*P0 a x*Yau.coordPartial psi x j)=
          (∫ x in Q, F0 x*psi x)-(∑ j, ∫ x in Q, G j x*Yau.coordPartial psi x j)) →
      ∀ (eta chi : Yau.Jets.Coord → ℝ),
        ContDiff ℝ ∞ eta → HasCompactSupport eta → (∀ x, |eta x| ≤ 1) →
        tsupport eta ⊆ interior (Yau.realCenteredCube 4 r) →
        ContDiff ℝ ∞ chi → tsupport chi ⊆ Q →
        ∀ (i : Fin 4) (h : ℝ), |h| ≤ R0-r →
        (∀ x ∈ tsupport eta, x ∈ interior Q ∧ x+Pi.single i h ∈ interior Q ∧
          chi x=1 ∧ chi (x+Pi.single i h)=1) →
        let U := Q.indicator u
        let V := fun a ↦ Q.indicator (V0 a)
        let F := Q.indicator F0
        let q := Yau.realDifferenceQuotient i h U
        let T := fun a x ↦ eta x*Yau.realDifferenceQuotient i h (V a) x
        let W := fun a x ↦ eta x*V a x
        let R := fun a x ↦ Yau.coordPartial eta x a*q x
        (∀ a, MemLp (T a) 2 volume ∧ MemLp (W a) 2 volume ∧ MemLp (R a) 2 volume) ∧
        (∑ a, ∫ x, (T a x)^2) ≤ (4/m)*
          ((16/m)*((∫ x, (F x)^2)+
              (∑ j, ∫ x, (chi x*DG j i x+Yau.coordPartial chi x i*G j x)^2))+
            K*(∑ a, ∫ x, (W a x)^2)+(K+m)*(∑ a, ∫ x, (R a x)^2)) := by
  obtain ⟨m,hm,K,hK,hcoer⟩ := sphere_interior_flux_difference_coercivity d p
  refine ⟨m,hm,K,hK,?_⟩
  intro R0 r hr hR u V0 P0 G DG F0
  dsimp only
  intro hu hv hp hg hd hf hsame hweak hcomm hequation eta chi he hc heb hs hchi hchis i h hh hend
  let Q := Yau.realCenteredCube 4 R0
  have hQ : IsCompact Q := Yau.realCenteredCube_isCompact 4 R0
  have hsub : Q ⊆ realFinCube 4 := Yau.realCenteredCube_mono hR
  let U := Q.indicator u
  let V := fun a ↦ Q.indicator (V0 a)
  let A := fun j ↦ Q.indicator (fun x ↦ ∑ a, sphereChartPrincipalDensity d p x a j*P0 a x)
  let F := Q.indicator F0
  let q := Yau.realDifferenceQuotient i h U
  let T := fun a x ↦ eta x*Yau.realDifferenceQuotient i h (V a) x
  let W := fun a x ↦ eta x*V a x
  let R := fun a x ↦ Yau.coordPartial eta x a*q x
  let P := Yau.realSquareCutoffGradient eta q (fun a ↦ Yau.realDifferenceQuotient i h (V a))
  let v := Yau.realSquareCutoff eta q
  let b := Yau.realDifferenceQuotient i (-h) v
  let L := fun j ↦ Yau.realDifferenceQuotient i h (fun x ↦ chi x*G j x)
  have hU : MemLp U 2 volume := (memLp_indicator_iff_restrict hQ.measurableSet).mpr hu
  have hV (j : Fin 4) : MemLp (V j) 2 volume :=
    (memLp_indicator_iff_restrict hQ.measurableSet).mpr (hv j)
  have hW (j : Fin 4) : MemLp (W j) 2 volume :=
    Yau.real_compact_localL2_product hc eta (V j) he.continuous Subset.rfl ((hV j).restrict _)
  have hzpair (a b : Yau.Jets.Coord → ℝ) :
      (∫ x, Q.indicator a x*b x) = ∫ x in Q, a x*b x := by
    simp only [← indicator_mul_left,integral_indicator hQ.measurableSet]
  have hUW (j : Fin 4) (psi : Yau.Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ psi)
      (hpc : HasCompactSupport psi) (hps : tsupport psi ⊆ Q) :
      (∫ x, U x*Yau.coordPartial psi x j)=-(∫ x, V j x*psi x) := by
    change (∫ x, Q.indicator u x*Yau.coordPartial psi x j)=-(∫ x, Q.indicator (V0 j) x*psi x)
    rw [hzpair,hzpair]
    exact hweak j psi hp hpc hps
  have htest := Yau.real_interior_square_difference_test R0 r hr
    (sphereChartPrincipalDensity d p) (fun a j ↦ (sphereChartPrincipalDensity_smooth d p a j).continuous)
    u V0 P0 G F0 hu hv hp hg hf hweak hequation eta he hc hs i h hh
  have henergy := Yau.real_square_difference_test_energy eta U V hU hV R0 r hr
    he hc heb (hs.trans interior_subset) hUW i h hh
  have hlocal (j : Fin 4) := Yau.real_local_weak_cutoff_difference_bound hQ (G j) (DG j i) chi
    (hg j) (hd j i) hchi hchis i (hcomm j i) h
  have hF : MemLp F 2 volume := (memLp_indicator_iff_restrict hQ.measurableSet).mpr hf
  have hlow := hcoer Q hsub P0 V0 hsame i h eta q (fun x hx ↦ ⟨(hend x hx).1,(hend x hx).2.1⟩)
  have hend0 : ∀ x ∈ tsupport eta, x ∈ Q ∧ x+Pi.single i h ∈ Q ∧ chi x=1 ∧ chi (x+Pi.single i h)=1 :=
    fun x hx ↦ ⟨interior_subset (hend x hx).1,interior_subset (hend x hx).2.1,(hend x hx).2.2⟩
  have heq : (∑ j, ∫ x, Yau.realDifferenceQuotient i h (A j) x*P j x) =
      -(∫ x, F x*b x)-(∑ j, ∫ x, L j x*P j x) := by
    have hl (j : Fin 4) := Yau.real_square_gradient_difference_pairing_localize Q (G j) chi eta q
      (fun a ↦ Yau.realDifferenceQuotient i h (V a)) i j h hend0
    have hlsum : (∑ j, ∫ x, Yau.realDifferenceQuotient i h (Q.indicator (G j)) x*P j x) =
        (∑ j, ∫ x, L j x*P j x) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun v : Yau.Jets.Coord → ℝ ↦ ∫ x, v x) (hl j)
    rw [← hlsum]
    exact htest.2.2.2.2
  have habs := Yau.real_divergence_difference_energy_absorption_ae volume m K hm
    T W R (fun j ↦ Yau.realDifferenceQuotient i h (A j)) P L F b
    (fun j ↦ (henergy.1 j).1) hW (fun j ↦ (henergy.1 j).2.1)
    (fun j ↦ (henergy.1 j).2.2) (fun j ↦ (hlocal j).1)
    (fun j ↦ (htest.2.2.1 j).1) hF henergy.2.1 hlow henergy.2.2.2 henergy.2.2.1 heq
  refine ⟨fun j ↦ ⟨(henergy.1 j).1,hW j,(henergy.1 j).2.1⟩,habs.trans ?_⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ (hlocal j).2)
  gcongr

end
end Yau.Target

end OAI
