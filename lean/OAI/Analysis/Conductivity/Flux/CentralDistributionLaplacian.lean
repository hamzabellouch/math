import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactRegularCorrection
import OAI.Analysis.Conductivity.Flux.CentralDistribution

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def centralLaplacian (f : Box3 → ℝ) (x : Box3) : ℝ :=
  ∑ i : Fin 3,cubePartial (cubePartial f (centralDirection i)) (centralDirection i) x

def centralSmoothPartial (f : centralSmoothFunctions) (i : Fin 3) : centralSmoothFunctions :=
  ⟨cubePartial f (centralDirection i),cubePartial_smooth (central_smooth f) _⟩

lemma centralSmoothPartial_jet_zero (f : centralSmoothFunctions) (i : Fin 3) :
    centralSmoothJet (centralSmoothPartial f i) 0=centralSmoothJet f i.succ := by
  apply Lp.ext
  filter_upwards [centralSmoothJet_ae (centralSmoothPartial f i) 0,
    centralSmoothJet_ae f i.succ] with x hx hy
  rw [hx,hy,centralJetField_succ]
  rfl

theorem central_variational_distributional_laplacian (s slopes : Fin 3 → ℝ)
    (hs : ∑ i,slopes i=0) :
    ∃ p : centralEnergySpace s,centralM s p=0 ∧ CentralVariationalEquation s slopes p ∧
      ∀ ψ : centralSmoothFunctions,HasCompactSupport ψ → tsupport ψ⊆centralClosed →
        (∀ (i : Fin 3) x,ψ (centralBoundary i x)=0) →
        (∫ x,(centralAmbientComponent s 0 p.val) x*centralLaplacian ψ x ∂centralMeasure)=0 := by
  obtain ⟨p,hp,hvar,hweak⟩ := central_variational_weak_interior s slopes hs
  refine ⟨p,hp,hvar,?_⟩
  intro ψ hc hsp hboundary
  have he := hweak ψ hboundary
  rw [PiLp.inner_apply] at he
  have hparts (i : Fin 3) :
      inner ℝ (centralSmoothJet ψ i.succ) (centralAmbientComponent s i.succ p.val)=
        -inner ℝ (centralSmoothJet (centralSmoothPartial ψ i) i.succ)
          (centralAmbientComponent s 0 p.val) := by
    have hd := central_distributional_derivative s p (centralSmoothPartial ψ i)
      (cubePartial_compact hc _) ((tsupport_fderiv_apply_subset ℝ _).trans hsp) i
    rwa [centralSmoothPartial_jet_zero] at hd
  have hsum : (∑ i : Fin 3,inner ℝ (centralSmoothJet (centralSmoothPartial ψ i) i.succ)
        (centralAmbientComponent s 0 p.val))=0 := by
    have hrew (i : Fin 3) :
        inner ℝ (centralD s p i) (centralJetD (centralSmoothJet ψ) i)=
          -inner ℝ (centralSmoothJet (centralSmoothPartial ψ i) i.succ)
            (centralAmbientComponent s 0 p.val) := by
      rw [real_inner_comm]
      exact hparts i
    simp only [hrew,Finset.sum_neg_distrib,neg_eq_zero] at he
    exact he
  have hint (i : Fin 3) :
      inner ℝ (centralSmoothJet (centralSmoothPartial ψ i) i.succ) (centralAmbientComponent s 0 p.val)=
        ∫ x,(centralAmbientComponent s 0 p.val) x*
          cubePartial (cubePartial ψ (centralDirection i)) (centralDirection i) x ∂centralMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [centralSmoothJet_ae (centralSmoothPartial ψ i) i.succ] with x hx
    rw [hx,centralJetField_succ,Real.inner_apply]
    exact mul_comm _ _
  have hInt (i : Fin 3) : Integrable (fun x => (centralAmbientComponent s 0 p.val) x*
      cubePartial (cubePartial ψ (centralDirection i)) (centralDirection i) x) centralMeasure :=
    (Lp.memLp _).integrable_mul (central_continuous_memLp
      (cubePartial_smooth (cubePartial_smooth (central_smooth ψ) _) _).continuous)
  simp only [hint] at hsum
  simpa only [centralLaplacian,Finset.mul_sum,integral_finsetSum _ (fun i _ => hInt i)] using hsum

end ScalarConductivity

end
end

end OAI
