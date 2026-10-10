import Mathlib

namespace OAI

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace Problem336
namespace CanonicalDrift

def outerLimit {X : Type*} (b : ℕ → X → ℝ) (x : X) : ℝ :=
  Filter.limsup (fun n => b n x) Filter.atTop

theorem measurable_outerLimit {X : Type*} [MeasurableSpace X]
    {b : ℕ → X → ℝ} (hb : ∀ n, Measurable (b n)) :
    Measurable (outerLimit b) :=
  Measurable.limsup hb

theorem outerLimit_mem_Icc {X : Type*} {b : ℕ → X → ℝ}
    {a c : ℝ} (hb : ∀ n x, b n x ∈ Set.Icc a c) (x : X) :
    outerLimit b x ∈ Set.Icc a c := by
  have hu : atTop.IsBoundedUnder (· ≤ ·) (fun n => b n x) :=
    isBoundedUnder_of ⟨c, fun n => (hb n x).2⟩
  have hl : atTop.IsCoboundedUnder (· ≤ ·) (fun n => b n x) :=
    isCoboundedUnder_le_of_le atTop fun n => (hb n x).1
  constructor
  · exact le_limsup_of_frequently_le
      (Eventually.of_forall fun n => (hb n x).1).frequently hu
  · exact limsup_le_of_le hl (Eventually.of_forall fun n => (hb n x).2)

theorem outerLimit_le_add {X Y : Type*}
    {b : ℕ → X → ℝ} {c : ℕ → Y → ℝ}
    {lo hi : ℝ} (hb : ∀ n x, lo ≤ b n x)
    (hc : ∀ n y, c n y ∈ Set.Icc lo hi)
    {x : X} {y : Y} {d : ℝ} (hbc : ∀ n, b n x ≤ c n y + d) :
    outerLimit b x ≤ outerLimit c y + d := by
  have hbl : atTop.IsCoboundedUnder (· ≤ ·) (fun n => b n x) :=
    isCoboundedUnder_le_of_le atTop fun n => hb n x
  have hcu : atTop.IsBoundedUnder (· ≤ ·) (fun n => c n y) :=
    isBoundedUnder_of ⟨hi, fun n => (hc n y).2⟩
  have hcl : atTop.IsCoboundedUnder (· ≤ ·) (fun n => c n y) :=
    isCoboundedUnder_le_of_le atTop fun n => (hc n y).1
  have hcdu : atTop.IsBoundedUnder (· ≤ ·) (fun n => c n y + d) :=
    isBoundedUnder_of ⟨hi + d, fun n => add_le_add (hc n y).2 le_rfl⟩
  exact (limsup_le_limsup (Eventually.of_forall hbc) hbl hcdu).trans_eq
    (limsup_add_const atTop (fun n => c n y) d hcu hcl)

theorem abs_outerLimit_sub_le {X : Type*} {b : ℕ → X → ℝ}
    {lo hi : ℝ} (hb : ∀ n x, b n x ∈ Set.Icc lo hi)
    {x y : X} {d : ℝ} (hxy : ∀ n, |b n x - b n y| ≤ d) :
    |outerLimit b x - outerLimit b y| ≤ d := by
  apply abs_le.mpr
  constructor
  · have h := outerLimit_le_add (fun n x => (hb n x).1) hb
      (x := y) (y := x) (d := d) (fun n => by
        have h := (abs_le.mp (hxy n)).1
        linarith)
    linarith
  · have h := outerLimit_le_add (fun n x => (hb n x).1) hb
      (x := x) (y := y) (d := d) (fun n => by
        have h := (abs_le.mp (hxy n)).2
        linarith)
    linarith

theorem outerLimit_transport {X Y : Type*}
    {b : ℕ → X → ℝ} {c : ℕ → Y → ℝ} (f : X → Y)
    (h : ∀ n x, c n (f x) = b n x) (x : X) :
    outerLimit c (f x) = outerLimit b x := by
  exact limsup_congr (Eventually.of_forall fun n => h n x)

theorem outerLimit_eq_of_tendsto {X : Type*} {b : ℕ → X → ℝ}
    {x : X} {a : ℝ} (h : Tendsto (fun n => b n x) atTop (nhds a)) :
    outerLimit b x = a :=
  h.limsup_eq

end CanonicalDrift
end Problem336

end

end OAI
