import OAI.Geometry.SurfaceImmersion.Correction.CompactModeCoefficients
import OAI.Geometry.Immersion.ClosedSurface.LocalMean

namespace OAI

/-! Construction of all numerical mean budgets from compact geometric
margins. The same numerical profiles work at every smaller slow scale. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes WeightedEstimates

lemma reconstruction_shrink_scale {G : Field 4} {U : Set SmallModes.Base}
    {s t C : ℝ} {m : ℕ} (h : ReconstructionCoefficientBound G U s m C)
    (ht : 0 ≤ t) (hts : t ≤ s) : ReconstructionCoefficientBound G U t m C :=
  ⟨⟨⟨h.xxX.shrink_scale ht hts,h.xxY.shrink_scale ht hts,
    h.xyX.shrink_scale ht hts,h.xyY.shrink_scale ht hts,
    h.yyX.shrink_scale ht hts,h.yyY.shrink_scale ht hts,
    h.ratioxx.shrink_scale ht hts,h.ratioxy.shrink_scale ht hts⟩,
    h.secondxx.shrink_scale ht hts,h.secondxy.shrink_scale ht hts⟩,
    h.dualx.shrink_scale ht hts,h.dualy.shrink_scale ht hts,h.dualn.shrink_scale ht hts⟩

def Budgets.atScale {U V : Set SmallModes.Base} {F : RField 4}
    {ψ : SmallModes.Base → ℝ} {Q : SmallModes.Base → Tensor →L[ℝ] ℝ}
    {χ e : SmallModes.Base → SmallModes.Base}
    (d : Budgets U V 1 F ψ Q χ e) (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Budgets U V s F ψ Q χ e where
  inv := d.inv
  chi := d.chi
  psi := d.psi
  forms := d.forms
  pull := d.pull
  normal := d.normal
  mode := d.mode
  inv_pos := d.inv_pos
  chi_pos := d.chi_pos
  psi_pos := d.psi_pos
  forms_pos := d.forms_pos
  pull_pos := d.pull_pos
  normal_pos := d.normal_pos
  mode_pos := d.mode_pos
  inv_bound := d.inv_bound
  chi_bound := d.chi_bound
  psi_bound := fun m => (d.psi_bound m).shrink_scale hs hs1
  forms_bound := fun m => (d.forms_bound m).shrink_scale hs hs1
  pull_bound := fun m => (d.pull_bound m).shrink_scale hs hs1
  normal_bound := fun m => (d.normal_bound m).shrink_scale hs hs1
  mode_bound := fun m => reconstruction_shrink_scale (d.mode_bound m) hs hs1

theorem compact_mean_budgets {U V ΩU ΩV KU KV : Set SmallModes.Base}
    (hU : IsOpen U) (hV : IsOpen V) (hΩU : IsOpen ΩU)
    (hKU : IsCompact KU) (hKV : IsCompact KV)
    (hUK : U ⊆ KU) (hVK : V ⊆ KV) (hKUΩ : KU ⊆ ΩU) (hKVΩ : KV ⊆ ΩV)
    {F : RField 4} (hF : ContDiff ℝ ∞ F) (hdom : RealModeDomain F ΩV)
    {ψ : SmallModes.Base → ℝ} {Q : SmallModes.Base → Tensor →L[ℝ] ℝ}
    {χ e : SmallModes.Base → SmallModes.Base}
    (hψ : ContDiffOn ℝ ∞ ψ ΩV) (hQ : ContDiffOn ℝ ∞ Q ΩV)
    (hχ : ContDiffOn ℝ ∞ χ ΩU) (he : ContDiffOn ℝ ∞ e ΩV)
    (hpull : ContDiffOn ℝ ∞ (pullbackField χ) ΩU) :
    Nonempty (Budgets U V 1 F ψ Q χ e) := by
  choose I hI hbI using fun m => compact_local_weighted_bound hV hdom.isOpen hKV hVK hKVΩ he m
  choose J hJ hbJ using fun m => compact_local_weighted_bound hU hΩU hKU hUK hKUΩ hχ m
  choose P hP hbP using fun m => compact_local_weighted_bound hV hdom.isOpen hKV hVK hKVΩ hψ m
  choose Qb hQb hbQ using fun m => compact_local_weighted_bound hV hdom.isOpen hKV hVK hKVΩ hQ m
  choose T hT hbT using fun m => compact_local_weighted_bound hU hΩU hKU hUK hKUΩ hpull m
  choose N hN hbN using fun m => compact_local_weighted_bound hV hdom.isOpen hKV hVK hKVΩ
    (contDiffOn_freeNormal hF hdom) m
  choose C hC hbC using fun m => (hdom.complexDomain hF).compact_reconstruction_bounds hV hKV hVK hKVΩ m
  refine ⟨{
    inv := I
    chi := J
    psi := P
    forms := Qb
    pull := T
    normal := N
    mode := C
    inv_pos := hI
    chi_pos := hJ
    psi_pos := hP
    forms_pos := hQb
    pull_pos := hT
    normal_pos := hN
    mode_pos := hC
    inv_bound := ?_
    chi_bound := ?_
    psi_bound := ?_
    forms_bound := ?_
    pull_bound := ?_
    normal_bound := ?_
    mode_bound := ?_
  }⟩
  · intro m j _ hj x hx
    simpa only [one_pow, one_mul] using hbI m 1 zero_le_one le_rfl j hj x hx
  · intro m j _ hj x hx
    simpa only [one_pow, one_mul] using hbJ m 1 zero_le_one le_rfl j hj x hx
  · exact fun m => hbP m 1 zero_le_one le_rfl
  · exact fun m => hbQ m 1 zero_le_one le_rfl
  · exact fun m => hbT m 1 zero_le_one le_rfl
  · exact fun m => hbN m 1 zero_le_one le_rfl
  · exact fun m => hbC m 1 zero_lt_one le_rfl

end ClosedSurfaceR4.PhaseMean

end

end OAI
