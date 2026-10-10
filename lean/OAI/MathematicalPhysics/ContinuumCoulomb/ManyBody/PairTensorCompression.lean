import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockTwoBodyIntegral
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.NuclearTensorCompression
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.RepulsionCross

namespace OAI

/-! The full-spin Coulomb pair form is exactly the quartic CAR operator
on the finite orbital tensor. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

private theorem symmetric_pair_sum {n : ℕ} (K : Fin n → Fin n → ℝ)
    (hK : ∀ i j, K i j=K j i) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, K i j) =
      2*(∑ i, ∑ j, if i < j then K i j else 0) := by
  have hrow (i : Fin n) :
      (∑ j, ((if i < j then K i j else 0)+(if j < i then K j i else 0))) =
        ∑ j ∈ Finset.univ.erase i, K i j := by
    calc
      _ = ∑ j ∈ Finset.univ.erase i,
          ((if i < j then K i j else 0)+(if j < i then K j i else 0)) := by
        symm
        apply Finset.sum_subset (Finset.erase_subset _ _)
        intro j _ hj
        have he : j=i := by simpa only [Finset.mem_erase,Finset.mem_univ,and_true,not_not] using hj
        subst j
        simp only [lt_self_iff_false,ite_false,add_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj).symm with h|h
        · simp only [h,not_lt_of_gt h,ite_true,ite_false,add_zero]
        · simp only [h,not_lt_of_gt h,ite_true,ite_false,zero_add,hK]
  calc
    _ = ∑ i, ∑ j, ((if i < j then K i j else 0)+(if j < i then K j i else 0)) := by
      simp only [hrow]
    _ = (∑ i, ∑ j, if i < j then K i j else 0)+
        (∑ i, ∑ j, if j < i then K j i else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = _ := by
      rw [Finset.sum_comm (f := fun i j => if j < i then K j i else 0)]
      ring

def flatPairCoulomb (x y : Fin 2 × (Fin 3 → ℝ)) : ℂ :=
  (Coulomb.coulombKernel (WithLp.toLp 2 x.2-WithLp.toLp 2 y.2):ℂ)

theorem pairEnergy_cube {n : ℕ} (u : Coulomb.H1Vector n) :
    (Coulomb.pairEnergy u : ℂ) = (2:ℂ)⁻¹ *
      (∫ z, (∑ i, ∑ j ∈ Finset.univ.erase i, flatPairCoulomb (z i) (z j))*
        (star (Coulomb.cubeState u z)*Coulomb.cubeState u z)
        ∂(Measure.pi fun _ : Fin n => Coulomb.spinSpaceMeasure)) := by
  have hn (z : ℂ) : ((‖z‖^2:ℝ):ℂ) = star z*z := by
    simpa only [starRingEnd_apply,Complex.ofReal_pow] using (Complex.conj_mul' z).symm
  have hpoint (x : Configuration n) :
      (∑ i, ∑ j ∈ Finset.univ.erase i,
        (Coulomb.coulombKernel (Coulomb.position x i-Coulomb.position x j):ℂ)) =
        2*(repulsionPotential x:ℂ) := by
    have h := symmetric_pair_sum
      (fun i j => Coulomb.coulombKernel (Coulomb.position x i-Coulomb.position x j))
      (fun i j => by unfold Coulomb.coulombKernel; rw [norm_sub_rev])
    exact_mod_cast (show _ = 2*repulsionPotential x from by
      simpa only [repulsionPotential,pairRepulsionTerm,Fintype.sum_prod_type] using h)
  have he := spinConfiguration_complex_integral
    (fun s x => ((repulsionPotential x*‖u.value s x‖^2 : ℝ):ℂ))
    (fun s => by
      convert (u.pair_integrable s).ofReal (𝕜 := ℂ) using 1
      funext x
      simp only [repulsionPotential,pairRepulsionTerm,Fintype.sum_prod_type]
      rfl)
  have hp (z : Fin n → Fin 2 × (Fin 3 → ℝ)) :
      (∑ i, ∑ j ∈ Finset.univ.erase i, flatPairCoulomb (z i) (z j))*
        (star (Coulomb.cubeState u z)*Coulomb.cubeState u z) =
      (2:ℂ)*((repulsionPotential (WithLp.toLp 2 ((Coulomb.spinCubeEquiv n) z).2)*
        ‖u.value ((Coulomb.spinCubeEquiv n) z).1
          (WithLp.toLp 2 ((Coulomb.spinCubeEquiv n) z).2)‖^2 : ℝ):ℂ) := by
    rw [Complex.ofReal_mul,hn]
    change _ = (2:ℂ)*((repulsionPotential (WithLp.toLp 2 ((Coulomb.spinCubeEquiv n) z).2):ℂ)*
      (star (Coulomb.cubeState u z)*Coulomb.cubeState u z))
    have hz := hpoint (WithLp.toLp 2 ((Coulomb.spinCubeEquiv n) z).2)
    change (∑ i, ∑ j ∈ Finset.univ.erase i, flatPairCoulomb (z i) (z j)) =
      2*(repulsionPotential (WithLp.toLp 2 ((Coulomb.spinCubeEquiv n) z).2):ℂ) at hz
    rw [hz]
    ring
  simp_rw [hp]
  rw [integral_const_mul,he]
  have hs : (∑ s, ∫ x, ((repulsionPotential x*‖u.value s x‖^2:ℝ):ℂ)) =
      (Coulomb.pairEnergy u : ℂ) := by
    simp only [integral_complex_ofReal,← Complex.ofReal_sum]
    simp only [Coulomb.pairEnergy,repulsionPotential,pairRepulsionTerm,Fintype.sum_prod_type]
  rw [hs]
  ring

theorem finiteTensorState_pair_compression {n Q : ℕ}
    (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x, star (v a x s)*v b x s) = if a=b then (1:ℂ) else 0)
    (hentry : ∀ a b c d, Integrable (fun z => flatPairCoulomb z.1 z.2*
      ((star (Coulomb.flatSpinOrbital (v a) z.1)*Coulomb.flatSpinOrbital (v c) z.1)*
        (star (Coulomb.flatSpinOrbital (v b) z.2)*Coulomb.flatSpinOrbital (v d) z.2)))
        (Coulomb.spinSpaceMeasure.prod Coulomb.spinSpaceMeasure))
    (c : Laughlin.State (n+2) Q) (hc : Laughlin.Antisymmetric c) :
    (Coulomb.pairEnergy (finiteTensorState v hv hL2 hpartial c) : ℂ) =
      Laughlin.Fock.occupationInner Q (Laughlin.Fock.normalizedTensorExterior (n+2) Q c)
        (HubbardGlobal.twoBodyOperator (fun a b c d =>
          ∫ z, flatPairCoulomb z.1 z.2*
            ((star (Coulomb.flatSpinOrbital (v a) z.1)*Coulomb.flatSpinOrbital (v c) z.1)*
              (star (Coulomb.flatSpinOrbital (v b) z.2)*Coulomb.flatSpinOrbital (v d) z.2))
            ∂(Coulomb.spinSpaceMeasure.prod Coulomb.spinSpaceMeasure))
          (Laughlin.Fock.normalizedTensorExterior (n+2) Q c)) := by
  rw [pairEnergy_cube]
  simp_rw [finiteTensorState_cubeState]
  apply FockTwoBodyIntegral.tensorValue_twoBody_integral _
    (fun a => Coulomb.flatSpinOrbital_memLp (v a) (hL2 a)) _ _ hentry c c hc hc
  intro a b
  rw [Coulomb.flatSpinOrbital_inner _ _ (hL2 a) (hL2 b)]
  exact ho a b

end ContinuumCoulomb

end

end OAI
