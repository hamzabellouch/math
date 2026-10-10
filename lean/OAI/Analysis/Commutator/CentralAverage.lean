import Mathlib
import OAI.Analysis.Commutator.CentralPinching
import OAI.Analysis.Commutator.CommutatorPerturbation
import OAI.Analysis.Commutator.ProjectionCommutant
import OAI.Analysis.Commutator.WeakOperatorAlgebra
import OAI.Analysis.Commutator.WeakOperatorLimit

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped InnerProductSpace Topology

namespace Kadison.CentralAverage

open UnitaryOrbit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_center_average (M : VonNeumannAlgebra H) (Y : H →L[ℂ] H) :
    ∃ Y₁ : H →L[ℂ] H,
      (∀ a∈M,a∈Set.centralizer (M : Set (H →L[ℂ] H)) → Y₁*a=a*Y₁) ∧
      ‖Y₁-Y‖≤commutatorSeminorm M Y ∧
      commutatorSeminorm M Y₁≤3*commutatorSeminorm M Y := by
  classical
  choose T hT hcomm using exists_finite_average M Y
  let ω : Ultrafilter (Finset (CentralProjection M)) := Ultrafilter.of atTop
  have hω : (ω : Filter (Finset (CentralProjection M)))≤atTop := Ultrafilter.of_le atTop
  obtain ⟨Y₁,_,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω T
    (commutatorSeminorm M Y+‖Y‖) (add_nonneg (commutatorSeminorm_nonneg M Y) (norm_nonneg Y))
    (fun s => hull_norm M (hT s))
  have hd : ‖Y₁-Y‖≤commutatorSeminorm M Y := by
    apply WeakOperatorLimit.norm_le_of_tendsto (l := (ω : Filter (Finset (CentralProjection M))))
      (T := fun s => T s-Y)
      (fun x y => ?_) (commutatorSeminorm_nonneg M Y)
      (Filter.Eventually.of_forall fun s => hull_distance M (hT s))
    simpa only [sub_apply,inner_sub_left] using
      (hlim x y).sub_const (inner ℂ (Y x) y)
  have hc (p : CentralProjection M) : Y₁*p.val=p.val*Y₁ := by
    apply WeakOperatorLimit.intertwine hlim p.val p.val
    have he := (Filter.eventually_ge_atTop ({p} : Finset (CentralProjection M))).filter_mono hω
    filter_upwards [he] with s hs
    exact hcomm s p (hs (Finset.mem_singleton_self p))
  refine ⟨Y₁,?_,hd,?_⟩
  · intro a ha haz
    apply commutes_algebra_of_commutes_projections (vonNeumannIntersection M M.commutant) Y₁
      (fun p hp hpp => hc ⟨p,hp.1,hpp,by
        simpa only [VonNeumannAlgebra.coe_toStarSubalgebra,VonNeumannAlgebra.coe_commutant] using hp.2⟩) a
    exact ⟨ha,by
      simpa only [VonNeumannAlgebra.coe_toStarSubalgebra,VonNeumannAlgebra.coe_commutant] using haz⟩
  · exact commutatorSeminorm_three M Y Y₁ hd

end Kadison.CentralAverage

end

end
end

end OAI
