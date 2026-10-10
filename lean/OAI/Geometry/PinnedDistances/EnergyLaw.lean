import OAI.Geometry.PinnedDistances.MobiusObstruction

namespace OAI

universe u1 u2

section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace WeakPinned.Bounded

abbrev Quad (X : Type u1) := X × X × X × X
abbrev Expanded (X : Type u2) := Quad X × ((X × X) × (X × X))

lemma no_energy_law (μ ν : Measure ℂ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [NullSingletonClass μ] [NullSingletonClass ν]
    (Q : Measure (Quad ℂ)) [IsProbabilityMeasure Q]
    (hind : Q.map (fun q => (q.1,q.2.2))=μ.prod (Q.map (fun q => q.2.2)))
    (hsupp : ∀ᵐ q ∂ Q,q.2.2.1∈μ.support)
    (he : ∀ᵐ q ∂ Q,crossEnergy μ q.1 q.2.2.1=targetEnergy ν q.2.2.2) : False := by
  let τ : Measure (ℂ × ℂ) := Q.map (fun q => q.2.2)
  have : IsProbabilityMeasure τ := inferInstance
  have hp := measurableSet_energy_eq μ ν
  have he' : ∀ᵐ v ∂ μ.prod τ,crossEnergy μ v.1 v.2.1=targetEnergy ν v.2.2 := by
    rw [← hind]
    exact (ae_map_iff (by fun_prop) hp).mpr he
  have hf : ∀ᵐ cd ∂ τ,∀ᵐ a ∂ μ,crossEnergy μ a cd.1=targetEnergy ν cd.2 :=
    (Measure.ae_ae_comm hp).mp ((Measure.ae_prod_iff_ae_ae hp).mp he')
  have hs : ∀ᵐ cd ∂ τ,cd.1∈μ.support :=
    (ae_map_iff (by fun_prop) (μ.isClosed_support.measurableSet.preimage measurable_fst)).mpr hsupp
  obtain ⟨cd,hc,hcd⟩ := (hs.and hf).exists
  exact not_ae_energy_eq μ ν cd.1 cd.2 hc hcd

lemma mobius_of_product (a b c d z v : ℂ) (hz : z≠a)
    (hp : (z-a)*(v-b)=(c-a)*(d-b)) : v=mobius a b c d z := by
  unfold mobius
  have hh : v-b=(c-a)*(d-b)/(z-a) := (eq_div_iff (sub_ne_zero.mpr hz)).mpr (by simpa [mul_comm] using hp)
  linear_combination hh

lemma expanded_kernel_eq (μ ν : Measure ℂ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [NullSingletonClass μ]
    (Q : Measure (Quad ℂ)) (R : Measure (Expanded ℂ))
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (he : R.map Prod.fst=Q)
    (hm : R.map (fun r => (r.1,(r.2.1.1,r.2.2.1)))=Q.prod (μ.prod μ))
    (hbd : ∀ᵐ q ∂ Q,q.2.1≠q.2.2.2)
    (hz : ∀ᵐ r ∂ R,(r.2.1.1-r.1.1)*(r.2.1.2-r.1.2.1)=
      (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1))
    (hw : ∀ᵐ r ∂ R,(r.2.2.1-r.1.1)*(r.2.2.2-r.1.2.1)=
      (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1)) :
    ∀ᵐ r ∂ R,crossKernel r.1.1 r.1.2.2.1 (r.2.1.1,r.2.2.1)=
      targetKernel r.1.2.2.2 (r.2.1.2,r.2.2.2) := by
  have hpred : MeasurableSet {p : Quad ℂ × (ℂ × ℂ) |
      p.2.1≠p.1.1 ∧ p.2.2≠p.1.1 ∧ p.2.2≠p.1.2.2.1} := by
    measurability
  have hpair : ∀ᵐ p ∂ Q.prod (μ.prod μ),
      p.2.1≠p.1.1 ∧ p.2.2≠p.1.1 ∧ p.2.2≠p.1.2.2.1 := by
    rw [Measure.ae_prod_iff_ae_ae hpred]
    exact Eventually.of_forall fun e => by
      filter_upwards [ae_pair_ne μ e.1,ae_pair_ne μ e.2.2.1] with zw ha hc
      exact ⟨ha.1,ha.2,hc.2⟩
  rw [← hm] at hpair
  have hp := (ae_map_iff (by fun_prop) hpred).mp hpair
  have hd : ∀ᵐ r ∂ R,r.1.2.1≠r.1.2.2.2 := by
    rw [← he] at hbd
    exact (ae_map_iff measurable_fst.aemeasurable (by measurability)).mp hbd
  filter_upwards [hp,hd,hz,hw] with r hp hd hz hw
  have hz' := mobius_of_product r.1.1 r.1.2.1 r.1.2.2.1 r.1.2.2.2 _ _ hp.1 hz
  have hw' := mobius_of_product r.1.1 r.1.2.1 r.1.2.2.1 r.1.2.2.2 _ _ hp.2.1 hw
  have hh := (kernel_mobius r.1.1 r.1.2.1 r.1.2.2.1 r.1.2.2.2
    (r.2.1.1,r.2.2.1) hd hp.1 hp.2.1 hp.2.2).symm
  simpa only [← hz',← hw'] using hh

lemma expanded_energy_eq (μ ν : Measure ℂ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (Q : Measure (Quad ℂ)) (R : Measure (Expanded ℂ))
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (hm₁ : R.map (fun r => (r.1,(r.2.1.1,r.2.2.1)))=Q.prod (μ.prod μ))
    (hm₂ : R.map (fun r => (r.1,(r.2.1.2,r.2.2.2)))=Q.prod (ν.prod ν))
    (hk : ∀ᵐ r ∂ R,crossKernel r.1.1 r.1.2.2.1 (r.2.1.1,r.2.2.1)=
      targetKernel r.1.2.2.2 (r.2.1.2,r.2.2.2)) :
    ∀ᵐ q ∂ Q,crossEnergy μ q.1 q.2.2.1=targetEnergy ν q.2.2.2 := by
  apply conditional_integral_eq R Q (μ.prod μ) (ν.prod ν) Prod.fst
    (fun r => (r.2.1.1,r.2.2.1)) (fun r => (r.2.1.2,r.2.2.2))
    (by fun_prop) (by fun_prop) (by fun_prop) hm₁ hm₂
    (fun p => crossKernel p.1.1 p.1.2.2.1 p.2)
    (fun p => targetKernel p.1.2.2.2 p.2) ?_ ?_ ?_ ?_ hk
  · unfold crossKernel; fun_prop
  · unfold targetKernel; fun_prop
  · intro p
    rw [Real.norm_eq_abs,abs_of_nonneg (crossKernel_nonneg _ _ _)]
    exact crossKernel_le_one _ _ _
  · intro p
    rw [Real.norm_eq_abs,abs_of_nonneg (targetKernel_nonneg _ _)]
    exact targetKernel_le_one _ _

end WeakPinned.Bounded

end
end

end OAI
