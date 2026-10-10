import OAI.Analysis.CircleDomains.Topology.RegularJordanParametrization
import Mathlib.Topology.MetricSpace.Basic

namespace OAI

/-! A small spatial neighborhood of a regular Jordan circuit sees only
one small parameter interval, modulo its period. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma RegularJordanParametrization.fract_value
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ) (s : ℝ) :
    γ (Int.fract s) = γ s := by
  simpa only [Int.fract,mul_one] using hγ.periodic.sub_int_mul_eq (x := s) ⌊s⌋

lemma RegularJordanParametrization.eq_iff_fract
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ) (s t : ℝ) :
    γ s = γ t ↔ Int.fract s = Int.fract t := by
  constructor
  · intro h
    exact hγ.injective ⟨Int.fract_nonneg s,Int.fract_lt_one s⟩
      ⟨Int.fract_nonneg t,Int.fract_lt_one t⟩
      ((hγ.fract_value s).trans (h.trans (hγ.fract_value t).symm))
  · intro h
    rw [← hγ.fract_value s,← hγ.fract_value t,h]

lemma RegularJordanParametrization.eq_of_eq_short
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ)
    {s t : ℝ} (h : γ s = γ t) (hlo : -1 < s-t) (hhi : s-t < 1) : s = t := by
  obtain ⟨n,hn⟩ := Int.fract_eq_fract.mp ((hγ.eq_iff_fract s t).mp h)
  have hnlo : (-1 : ℤ) < n := by exact_mod_cast (hn ▸ hlo)
  have hnhi : n < (1 : ℤ) := by exact_mod_cast (hn ▸ hhi)
  have hn0 : n = 0 := by omega
  rw [hn0,Int.cast_zero] at hn
  exact sub_eq_zero.mp hn

lemma RegularJordanParametrization.centered_representative
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ) (s t : ℝ) :
    ∃ u ∈ Icc (t-1/2) (t+1/2), γ u = γ s := by
  let u := s - (⌊s-t+1/2⌋ : ℤ)
  have he : u = t + Int.fract (s-t+1/2) - 1/2 := by dsimp only [u,Int.fract]; ring
  refine ⟨u,?_,?_⟩
  · rw [he]
    exact ⟨by linarith [Int.fract_nonneg (s-t+1/2)],by linarith [Int.fract_lt_one (s-t+1/2)]⟩
  · simpa only [u,mul_one] using hγ.periodic.sub_int_mul_eq (x := s) ⌊s-t+1/2⌋

lemma RegularJordanParametrization.local_parameter_isolation
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ)
    (t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ s : ℝ, dist (γ s) (γ t) < ε →
      ∃ u ∈ Ioo (t-δ) (t+δ), γ u = γ s := by
  let K := Icc (t-1/2) (t+1/2) \ Ioo (t-δ) (t+δ)
  have hK : IsCompact K := isCompact_Icc.diff isOpen_Ioo
  have him : IsClosed (γ '' K) := (hK.image hγ.smooth.continuous).isClosed
  have hnot : γ t ∉ γ '' K := by
    rintro ⟨s,hs,he⟩
    have hst : s = t := hγ.eq_of_eq_short he
      (by linarith [hs.1.1]) (by linarith [hs.1.2])
    exact hs.2 (hst ▸ ⟨by linarith,by linarith⟩)
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp him.isOpen_compl (γ t) hnot
  refine ⟨ε,hε,?_⟩
  intro s hs
  obtain ⟨u,hu,he⟩ := hγ.centered_representative s t
  refine ⟨u,?_,he⟩
  by_contra hout
  exact hball hs ⟨u,⟨hu,hout⟩,he⟩

end CircleDomainRigidity

end

end OAI
