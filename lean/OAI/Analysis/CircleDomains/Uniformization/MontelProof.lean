import OAI.Analysis.CircleDomains.Uniformization.MontelAscoli

namespace OAI

/-! Discharge the precise varying-domain Montel input by cutoff
exhaustion, local Schwarz bounds and compact-open Ascoli extraction. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem montelExhaustion : MontelExhaustion := by
  classical
  intro D F hD hmono hF hbound
  obtain ⟨s,hs,G,heq,he,hb⟩ := exists_montel_continuous_family D F hD hmono hF hbound
  let U := ⋃ n, D n
  have hU : IsOpen U := isOpen_iUnion hD
  let H : ℕ → C(U, ℂ) := fun n => (G n).comp ⟨Subtype.val,continuous_subtype_val⟩
  obtain ⟨v,t,ht,hv⟩ := locally_uniform_complex_subsequence hU H he hb
  let f : ℂ → ℂ := fun z => if hz : z ∈ U then v ⟨z,hz⟩ else 0
  have hf : (f ∘ ((↑) : U → ℂ)) = v := by
    funext z
    simp only [Function.comp_apply,f,dite_eq_left z.property]
  have hlim : TendstoLocallyUniformlyOn (fun n => G (t n)) f atTop U := by
    apply tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr
    rw [hf]
    exact hv
  refine ⟨s ∘ t,f,hs.comp ht,?_⟩
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mpr
  intro K hKU hK
  have hKlim := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hlim K hKU hK
  exact hKlim.congr (ht.tendsto_atTop.eventually (heq K hK hKU))

end CircleDomainRigidity

end

end OAI
