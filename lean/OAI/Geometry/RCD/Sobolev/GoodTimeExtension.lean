import OAI.Geometry.RCD.Sobolev.RemoveExceptionalTimes
import Mathlib.Topology.ExtendFrom

namespace OAI

/-! # A common time extension agreeing with every continuous cylinder -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

def goodTimeExtension {Y : Type*} (N : Set ℝ) (G : ℝ → Y → ℝ) (t : ℝ) (x : Y) : ℝ :=
  if t ∈ Ioo 0 1 then extendFrom (Ioo 0 1 \ N) (fun s => G s x) t else 0

theorem goodTimeExtension_eq_local {Y : Type*} (N : Set ℝ) (hN : N.Countable)
    (G U : ℝ → Y → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hU : ∀ x, Continuous (fun t => U t x))
    (heq : ∀ t ∈ Ioo δ 1, t ∉ N → ∀ x, U t x = G t x)
    {t : ℝ} (ht : t ∈ Ioo δ 1) (x : Y) : goodTimeExtension N G t x = U t x := by
  have ht0 : t ∈ Ioo (0:ℝ) 1 := ⟨hδ.trans ht.1,ht.2⟩
  have hd : Dense Nᶜ := volume.dense_of_ae (hN.ae_notMem volume)
  have hc : t ∈ closure (Ioo (0:ℝ) 1 \ N) := by
    simpa only [sdiff_eq] using isOpen_Ioo.inter_closure (t := Nᶜ) ⟨ht0,hd t⟩
  have hevent : (fun s => G s x) =ᶠ[𝓝[Ioo (0:ℝ) 1 \ N] t] (fun s => U s x) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds ht)] with s hs hsi
    exact (heq s hsi hs.2 x).symm
  have hlim : Tendsto (fun s => G s x) (𝓝[Ioo (0:ℝ) 1 \ N] t) (𝓝 (U t x)) :=
    ((hU x).continuousAt.tendsto.mono_left inf_le_left).congr' hevent.symm
  simp only [goodTimeExtension,ite_eq_left ht0]
  exact extendFrom_eq hc hlim

theorem goodTimeExtension_eq_local_subtype {X : Type*} (A : Set X)
    (N : Set ℝ) (hN : N.Countable) (G : ℝ → X → ℝ) (U : ℝ → A → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hU : ∀ x, Continuous (fun t => U t x))
    (heq : ∀ t ∈ Ioo δ 1, t ∉ N → ∀ x, U t x = G t x)
    {t : ℝ} (ht : t ∈ Ioo δ 1) (x : A) : goodTimeExtension N G t x = U t x :=
  goodTimeExtension_eq_local N hN (fun t (x : A) => G t x) U hδ hU heq ht x

end RegularPointCoordinates

end

end OAI
