import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.GeneralSurfaceEuler
import OAI.AlgebraicGeometry.Seshadri.Jets.SectionJetDimensions
import OAI.AlgebraicGeometry.Seshadri.Cohomology.GeneralSurfaceH2

namespace OAI


                                       
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

theorem Surface.eventually_effective_with_jets (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme)
    (hm : 0 ≤ mixedEuler S L M) {r : ℕ} (m : Fin r → ℕ)
    (hq : (∑ i, (m i)^2 : ℕ) < selfIntersection S M)
    (U : Fin r → S.scheme.affineOpens)
    (e : ∀ i, M.sheaf.restrict (U i).1.ι ≅ O (U i).1.toScheme)
    (t : ∀ i, Fin 2 → Γ(S.scheme,(U i).1))
    (het : ∀ i, (MvPolynomial.eval₂Hom (openScalars S.structureMap (U i).1) (t i)).Etale)
    (ρ : ∀ i, letI := (openScalars S.structureMap (U i).1).toAlgebra;
      Γ(S.scheme,(U i).1) →ₐ[ℂ] ℂ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∃ s : O S.scheme ⟶ (M.pow n).sheaf, s ≠ 0 ∧
        ∀ i, affineCoefficient (U i) (localPowerFrame (U i).1 (e i) n) s ∈
          (RingHom.ker (ρ i))^(n*m i) := by
  classical
  let W : ℕ := ∑ i, (m i)^2
  let T : ℕ := ∑ i, m i
  obtain ⟨B,C,hB⟩ := S.power_H2_linear_bound L hL M hm
  obtain ⟨N,hN,hpos⟩ := quadratic_lower_eventually_pos (selfIntersection S M-W)
    (eulerCharacteristic S.structureMap 2 M.sheaf -
      eulerCharacteristic S.structureMap 2 (O S.scheme) - C - (W+T))
    (eulerCharacteristic S.structureMap 2 (O S.scheme)) (by omega) B
  refine ⟨N,hN,fun n hn => ?_⟩
  refine S.exists_section_with_point_orders L hL (M.pow n) U
    (fun i => localPowerFrame (U i).1 (e i) n) t het ρ (fun i => n*m i) ?_
  have he := S.arbitrary_power_euler_quadratic L hL M n
  rw [surface_euler_expansion] at he
  have hb : (cohomologyDimension S.structureMap (M.pow n).sheaf 2 : ℤ) ≤
      B+(C:ℤ)*n := by exact_mod_cast hB n
  have hi : (0 : ℤ) ≤ cohomologyDimension S.structureMap (M.pow n).sheaf 1 := Nat.cast_nonneg _
  have hsum : (∑ i, (n*m i)*(n*m i+1)) = n*n*W+n*T := by
    dsimp only [W,T]
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro index _
    ring
  rw [hsum]
  have hp := hpos n hn
  have hnon : 0 ≤ (n : ℤ)*(W+T) := by positivity
  have HH : (n : ℤ)*n*W+n*T <
      2*(cohomologyDimension S.structureMap (M.pow n).sheaf 0 : ℤ) := by
    nlinarith only [he,hb,hi,hp,hnon]
  exact_mod_cast HH

end
end MaximalSeshadri.Geometry

end


end OAI
