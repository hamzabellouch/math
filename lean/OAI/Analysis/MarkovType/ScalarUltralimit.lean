import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Hausdorff

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace MarkovSuperreflexivity

def RealSeqBounded (f : ℕ → ℝ) : Prop :=
  ∃ B : ℝ, ∀ n, |f n| ≤ B

namespace RealSeqBounded

variable {f g : ℕ → ℝ}

theorem exists_nonneg_bound (hf : RealSeqBounded f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n, |f n| ≤ B := by
  obtain ⟨B, hB⟩ := hf
  exact ⟨B, (abs_nonneg (f 0)).trans (hB 0), hB⟩

theorem const (c : ℝ) : RealSeqBounded (fun _ : ℕ => c) :=
  ⟨|c|, fun _ => le_rfl⟩

theorem add (hf : RealSeqBounded f) (hg : RealSeqBounded g) :
    RealSeqBounded (fun n => f n + g n) := by
  obtain ⟨B, hB⟩ := hf
  obtain ⟨C, hC⟩ := hg
  exact ⟨B + C, fun n => (abs_add_le (f n) (g n)).trans (add_le_add (hB n) (hC n))⟩

theorem neg (hf : RealSeqBounded f) : RealSeqBounded (fun n => -f n) := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨B, fun n => ?_⟩
  simpa only [abs_neg] using hB n

theorem sub (hf : RealSeqBounded f) (hg : RealSeqBounded g) :
    RealSeqBounded (fun n => f n - g n) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem const_mul (c : ℝ) (hf : RealSeqBounded f) :
    RealSeqBounded (fun n => c * f n) := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨|c| * B, fun n => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hB n) (abs_nonneg c)

theorem abs (hf : RealSeqBounded f) : RealSeqBounded (fun n => |f n|) := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨B, fun n => ?_⟩
  simpa only [abs_abs] using hB n

end RealSeqBounded

def realULim (U : Ultrafilter ℕ) (f : ℕ → ℝ) : ℝ :=
  Filter.limUnder (U : Filter ℕ) f

variable {f g : ℕ → ℝ}

theorem tendsto_realULim (U : Ultrafilter ℕ) (hf : RealSeqBounded f) :
    Tendsto f (U : Filter ℕ) (𝓝 (realULim U f)) := by
  obtain ⟨B, hB⟩ := hf
  have hmem : Set.Icc (-B) B ∈ Ultrafilter.map f U := by
    change ∀ᶠ n in (U : Filter ℕ), f n ∈ Set.Icc (-B) B
    exact Filter.Eventually.of_forall fun n => abs_le.mp (hB n)
  obtain ⟨a, _ha, hlim⟩ :=
    isCompact_Icc.ultrafilter_le_nhds' (Ultrafilter.map f U) hmem
  have ha : Tendsto f (U : Filter ℕ) (𝓝 a) := hlim
  exact tendsto_nhds_limUnder ⟨a, ha⟩

theorem realULim_eq_of_tendsto (U : Ultrafilter ℕ) {a : ℝ}
    (h : Tendsto f (U : Filter ℕ) (𝓝 a)) : realULim U f = a :=
  h.limUnder_eq

@[simp]
theorem realULim_const (U : Ultrafilter ℕ) (c : ℝ) :
    realULim U (fun _ : ℕ => c) = c :=
  realULim_eq_of_tendsto U tendsto_const_nhds

theorem realULim_add (U : Ultrafilter ℕ) (hf : RealSeqBounded f)
    (hg : RealSeqBounded g) :
    realULim U (fun n => f n + g n) = realULim U f + realULim U g :=
  realULim_eq_of_tendsto U ((tendsto_realULim U hf).add (tendsto_realULim U hg))

theorem realULim_neg (U : Ultrafilter ℕ) (hf : RealSeqBounded f) :
    realULim U (fun n => -f n) = -realULim U f :=
  realULim_eq_of_tendsto U (tendsto_realULim U hf).neg

theorem realULim_sub (U : Ultrafilter ℕ) (hf : RealSeqBounded f)
    (hg : RealSeqBounded g) :
    realULim U (fun n => f n - g n) = realULim U f - realULim U g :=
  realULim_eq_of_tendsto U ((tendsto_realULim U hf).sub (tendsto_realULim U hg))

theorem realULim_const_mul (U : Ultrafilter ℕ) (c : ℝ) (hf : RealSeqBounded f) :
    realULim U (fun n => c * f n) = c * realULim U f :=
  realULim_eq_of_tendsto U ((tendsto_realULim U hf).const_mul c)

theorem realULim_abs (U : Ultrafilter ℕ) (hf : RealSeqBounded f) :
    realULim U (fun n => |f n|) = |realULim U f| :=
  realULim_eq_of_tendsto U (tendsto_realULim U hf).abs

theorem realULim_le_realULim (U : Ultrafilter ℕ) (hf : RealSeqBounded f)
    (hg : RealSeqBounded g) (h : ∀ᶠ n in (U : Filter ℕ), f n ≤ g n) :
    realULim U f ≤ realULim U g :=
  le_of_tendsto_of_tendsto (tendsto_realULim U hf) (tendsto_realULim U hg) h

theorem realULim_le_of_eventually_le (U : Ultrafilter ℕ) (hf : RealSeqBounded f)
    {c : ℝ} (h : ∀ᶠ n in (U : Filter ℕ), f n ≤ c) : realULim U f ≤ c :=
  le_of_tendsto (tendsto_realULim U hf) h

theorem le_realULim_of_eventually_le (U : Ultrafilter ℕ) (hf : RealSeqBounded f)
    {c : ℝ} (h : ∀ᶠ n in (U : Filter ℕ), c ≤ f n) : c ≤ realULim U f := by
  have hlim := realULim_le_realULim U (RealSeqBounded.const c) hf h
  simpa only [realULim_const] using hlim

def freeUltrafilter : Ultrafilter ℕ := Filter.hyperfilter ℕ

theorem freeUltrafilter_le_cofinite :
    (freeUltrafilter : Filter ℕ) ≤ Filter.cofinite :=
  Filter.hyperfilter_le_cofinite

theorem freeUltrafilter_le_atTop : (freeUltrafilter : Filter ℕ) ≤ Filter.atTop :=
  Nat.hyperfilter_le_atTop

theorem not_mem_freeUltrafilter_of_finite {s : Set ℕ} (hs : s.Finite) :
    s ∉ freeUltrafilter :=
  Filter.notMem_hyperfilter_of_finite hs

theorem tendsto_freeUltrafilter_of_tendsto_atTop {α : Type*} [TopologicalSpace α]
    {a : ℕ → α} {x : α} (h : Tendsto a atTop (𝓝 x)) :
    Tendsto a (freeUltrafilter : Filter ℕ) (𝓝 x) :=
  h.mono_left freeUltrafilter_le_atTop

theorem realULim_freeUltrafilter_eq_of_tendsto_atTop {a : ℝ}
    (h : Tendsto f atTop (𝓝 a)) : realULim freeUltrafilter f = a :=
  realULim_eq_of_tendsto freeUltrafilter (tendsto_freeUltrafilter_of_tendsto_atTop h)

end MarkovSuperreflexivity

end

end OAI
