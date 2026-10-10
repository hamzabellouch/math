import Mathlib
import OAI.Analysis.HardSphere.Orbitals.Joint2
import OAI.Analysis.HardSphere.Geometry.FinsetEraseRecursion

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter PeriodicCutoff
open scoped ComplexConjugate
noncomputable section

lemma joint_empty_onScalar {S : Type*} [DecidableEq S] {n : ℕ} {L : Length}
    (c : S → Torus L) (h : ℝ) (u : ScalarL2 n L) : (joint n L c h ∅).onScalar u=u := by
  apply Lp.ext
  filter_upwards [(joint n L c h ∅).coe_onScalar u] with X hX
  simpa only [joint_apply,Finset.prod_empty,one_mul] using hX

theorem joint_low_counts : ∃ C B E G : ℝ, 0<C ∧ 0<B ∧ 0<E ∧ 0<G ∧
    ∀ (S : Type) [DecidableEq S] (n : ℕ) (L : Length) (r : ℝ),
      0<r → r ≤ 1/100 → 0<n → 1/100 ≤ L.val →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (c : S → Torus L), (∀ z v, z≠v → 1 ≤ dist (c z) (c v)) →
    ∀ (k m : ℕ) (h : ℝ), 0<h → 2*h ≤ k → C*B*(k+m)*r^3 ≤ 1/4 →
      0 < m*(energy g/(n:ℝ)-C*(E+B*(k+m)*r)) →
    ∀ A : Finset S, ‖(joint n L c h A).onScalar g.1‖^2 ≤
      (G/(h*(m*(energy g/(n:ℝ)-C*(E+B*(k+m)*r)))))^A.card := by
  obtain ⟨C,B,E,hC,hB,hE,hdef⟩ := physical_deficiency
  obtain ⟨M,hM,hb⟩ := exists_transition_bound
  let G : ℝ := 2*M^2*(3*(4*(24*Real.pi^2*M^2/(8*(1/100))^2)))
  have hG : 0<G := by dsimp [G]; positivity
  refine ⟨C,B,E,G,hC,hB,hE,hG,?_⟩
  intro S _ n L r hr hrd hn hL g hg c hc k m h hh hk hsmall hgap A
  let γ : ℝ := m*(energy g/(n:ℝ)-C*(E+B*(k+m)*r))
  have hγ : 0<γ := hgap
  let q : ℝ := G/(h*γ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  change ‖(joint n L c h A).onScalar g.1‖^2 ≤ q^A.card
  apply finset_erase_recursion (fun A ↦ ‖(joint n L c h A).onScalar g.1‖^2) q hq
  · rw [joint_empty_onScalar,hg.2.2.1]
    norm_num
  · intro A hA
    let : Nonempty A := hA.to_subtype
    let u := (joint n L c h A).onJet g
    have hu : u∈dirichletDomain n L r := (joint n L c h A).onJet_mem_domain hg.1
    have hs : ∀ᵐ X ∂volume, u.1 X≠0 → ∀ z : A, count L (1/100) (c z) X ≤ k := by
      filter_upwards [joint_support hh c A g.1] with X hX huX z
      exact (hX huX z z.property).trans hk
    have hp := hdef A n L r hr hrd hn hL g hg (fun z : A ↦ c z)
      (fun z v hzv ↦ hc z v (fun he ↦ hzv (Subtype.ext he))) k m hsmall u hu hs
    have hm := hg.smooth_multiplier_identity (joint n L c h A) (joint_real n L c h A)
    have hbnd := joint_gradient_norm_le hh hM.le hb c hc A g.1
    have hpen : γ*((A.card : ℝ)*‖(joint n L c h A).onScalar g.1‖^2) ≤
        (G/h)*∑ s∈A, ‖(joint n L c h (A.erase s)).onScalar g.1‖^2 := by
      calc
        _ = m*Fintype.card A*(energy g/(n:ℝ)-C*(E+B*(k+m)*r))*‖u.1‖^2 := by
          simp only [Fintype.card_coe,u,SmoothMultiplier.onJet_fst,γ]
          ring
        _ ≤ energy u-energy g*‖u.1‖^2 := hp
        _ = ∑ p : Direction n, ‖(joint n L c h A).derivativeScalar p g.1‖^2 := hm
        _ ≤ _ := hbnd
    have hdiv := (le_div_iff₀ hγ).mpr (by simpa only [mul_comm γ] using hpen)
    have he : ((G/h)*∑ s∈A, ‖(joint n L c h (A.erase s)).onScalar g.1‖^2)/γ =
        q*∑ s∈A, ‖(joint n L c h (A.erase s)).onScalar g.1‖^2 := by
      dsimp [q]
      field_simp
    simpa only [he] using hdiv

end
end HardSphere.CellOrbital

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

end
end
end
end
end
end
end

end OAI
