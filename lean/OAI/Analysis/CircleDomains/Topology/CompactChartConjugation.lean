import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace OAI

/-! Extend a compactly supported deformation in an actual plane chart by
identity outside the chart. The support and smoothness are retained. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

def chartConjugate (e : OpenPartialHomeomorph ℂ ℂ) (T : ℂ ≃ₜ ℂ) (x : ℂ) : ℂ :=
  by
    classical
    exact if x∈e.target then e (T (e.symm x)) else x

lemma homeomorph_symm_eq_of_fixed {T : ℂ ≃ₜ ℂ} {x : ℂ} (hx : T x=x) : T.symm x=x := by
  apply T.injective
  rw [T.apply_symm_apply,hx]

lemma compactChart_maps_source (e : OpenPartialHomeomorph ℂ ℂ) (T : ℂ ≃ₜ ℂ)
    {K : Set ℂ} (hK : K⊆e.source) (hfix : ∀x∉K,T x=x) {x : ℂ} (hx : x∈e.source) :
    T x∈e.source := by
  by_contra hn
  have hfixed : T (T x)=T x := hfix _ (fun h => hn (hK h))
  have he : T x=x := T.injective hfixed
  rw [he] at hn
  exact hn hx

lemma chartConjugate_eq_off (e : OpenPartialHomeomorph ℂ ℂ) (T : ℂ ≃ₜ ℂ)
    {K : Set ℂ} (hfix : ∀x∉K,T x=x) {x : ℂ} (hx : x∉e '' K) :
    chartConjugate e T x=x := by
  unfold chartConjugate
  split_ifs with h
  · have hk : e.symm x∉K := fun hk => hx ⟨e.symm x,hk,e.right_inv h⟩
    rw [hfix _ hk,e.right_inv h]
  · rfl

lemma chartConjugate_left_inv (e : OpenPartialHomeomorph ℂ ℂ) (T : ℂ ≃ₜ ℂ)
    {K : Set ℂ} (hK : K⊆e.source) (hfix : ∀x∉K,T x=x) :
    LeftInverse (chartConjugate e T.symm) (chartConjugate e T) := by
  intro x
  by_cases hx : x∈e.target
  · have hs := compactChart_maps_source e T hK hfix (e.map_target hx)
    have ht := e.map_source hs
    change chartConjugate e T.symm (chartConjugate e T x)=x
    have hv : chartConjugate e T x=e (T (e.symm x)) := by
      rw [chartConjugate,ite_eq_left hx]
    rw [hv,chartConjugate,ite_eq_left ht,e.left_inv hs,T.symm_apply_apply,e.right_inv hx]
  · have hv : chartConjugate e T x=x := by rw [chartConjugate,ite_eq_right hx]
    rw [hv,chartConjugate,ite_eq_right hx]

lemma chartConjugate_continuous (e : OpenPartialHomeomorph ℂ ℂ) (T : ℂ ≃ₜ ℂ)
    {K : Set ℂ} (hKc : IsCompact K) (hK : K⊆e.source) (hfix : ∀x∉K,T x=x) :
    Continuous (chartConjugate e T) := by
  have himage : IsCompact (e '' K) := hKc.image_of_continuousOn (e.continuousOn.mono hK)
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x∈e.target
  · have hs := compactChart_maps_source e T hK hfix (e.map_target hx)
    have he := e.continuousOn.continuousAt (e.open_source.mem_nhds hs)
    have hi := e.continuousOn_symm.continuousAt (e.open_target.mem_nhds hx)
    have hT : ContinuousAt (T : ℂ → ℂ) (e.symm x) := T.continuous.continuousAt
    have hcomp : ContinuousAt (fun y => e (T (e.symm y))) x := ContinuousAt.comp (f := fun y => T (e.symm y)) (g := (e : ℂ → ℂ)) he
      (ContinuousAt.comp (f := (e.symm : ℂ → ℂ)) (g := (T : ℂ → ℂ)) hT hi)
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hx] with y hy
    simp only [chartConjugate,ite_eq_left hy]
  · have ho : x∈(e '' K)ᶜ := by
      rintro ⟨z,hz,rfl⟩
      exact hx (e.map_source (hK hz))
    apply continuousAt_id.congr_of_eventuallyEq
    filter_upwards [himage.isClosed.isOpen_compl.mem_nhds ho] with y hy
    exact chartConjugate_eq_off e T hfix hy

def compactChartHomeomorph (e : OpenPartialHomeomorph ℂ ℂ) (T : ℂ ≃ₜ ℂ)
    {K : Set ℂ} (hKc : IsCompact K) (hK : K⊆e.source) (hfix : ∀x∉K,T x=x) : ℂ ≃ₜ ℂ :=
  { toFun := chartConjugate e T
    invFun := chartConjugate e T.symm
    left_inv := chartConjugate_left_inv e T hK hfix
    right_inv := chartConjugate_left_inv e T.symm hK
      (fun x hx => homeomorph_symm_eq_of_fixed (hfix x hx))
    continuous_toFun := chartConjugate_continuous e T hKc hK hfix
    continuous_invFun := chartConjugate_continuous e T.symm hKc hK
      (fun x hx => homeomorph_symm_eq_of_fixed (hfix x hx)) }

lemma chartConjugate_contDiff (e : OpenPartialHomeomorph ℂ ℂ) (T : ℂ ≃ₜ ℂ)
    {K : Set ℂ} (hKc : IsCompact K) (hK : K⊆e.source) (hfix : ∀x∉K,T x=x)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hT : ContDiff ℝ ∞ (T : ℂ → ℂ)) : ContDiff ℝ ∞ (chartConjugate e T) := by
  have himage : IsCompact (e '' K) := hKc.image_of_continuousOn (e.continuousOn.mono hK)
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x∈e.target
  · have hs := compactChart_maps_source e T hK hfix (e.map_target hx)
    have he' := (he _ hs).contDiffAt (e.open_source.mem_nhds hs)
    have hi' := (hi _ hx).contDiffAt (e.open_target.mem_nhds hx)
    apply (he'.comp x (hT.contDiffAt.comp x hi')).congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hx] with y hy
    simp only [chartConjugate,ite_eq_left hy,comp_apply]
  · have ho : x∈(e '' K)ᶜ := by
      rintro ⟨z,hz,rfl⟩
      exact hx (e.map_source (hK hz))
    apply contDiffAt_id.congr_of_eventuallyEq
    filter_upwards [himage.isClosed.isOpen_compl.mem_nhds ho] with y hy
    exact chartConjugate_eq_off e T hfix hy

lemma compactChartHomeomorph_image (e : OpenPartialHomeomorph ℂ ℂ) (T : ℂ ≃ₜ ℂ)
    {K A : Set ℂ} (hKc : IsCompact K) (hK : K⊆e.source) (hfix : ∀x∉K,T x=x)
    (hA : A⊆e.source) :
    compactChartHomeomorph e T hKc hK hfix '' (e '' A)=e '' (T '' A) := by
  rw [image_image,image_image]
  apply image_congr
  intro z hz
  change chartConjugate e T (e z)=e (T z)
  rw [chartConjugate,ite_eq_left (e.map_source (hA hz)),e.left_inv (hA hz)]

lemma compactChartHomeomorph_inverse_smooth (e : OpenPartialHomeomorph ℂ ℂ) (T : ℂ ≃ₜ ℂ)
    {K : Set ℂ} (hKc : IsCompact K) (hK : K⊆e.source) (hfix : ∀x∉K,T x=x)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hT : ContDiff ℝ ∞ (T.symm : ℂ → ℂ)) :
    ContDiff ℝ ∞ ((compactChartHomeomorph e T hKc hK hfix).symm : ℂ → ℂ) :=
  chartConjugate_contDiff e T.symm hKc hK
    (fun x hx => homeomorph_symm_eq_of_fixed (hfix x hx)) he hi hT

end CircleDomainRigidity

end

end OAI
