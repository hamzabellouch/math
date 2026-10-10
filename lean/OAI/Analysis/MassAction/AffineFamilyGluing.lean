import OAI.Analysis.MassAction.AffineNeighborhood
import OAI.Analysis.MassAction.AffineGluing
import OAI.Analysis.MassAction.ExponentAsymptotics

namespace OAI

universe uIota

noncomputable section

open Filter Asymptotics
open scoped BigOperators Topology

namespace Problem326.Affine

/-- Shift an affine label without changing its slope. -/
def Label.shiftOffset {d : ℕ} (L : Label d) (s : ℝ → ℝ) : Label d :=
  ⟨L.slope, fun h => L.offset h - s h⟩

@[simp] theorem Label.shiftOffset_slope {d : ℕ} (L : Label d) (s : ℝ → ℝ) :
    (L.shiftOffset s).slope = L.slope := rfl

@[simp] theorem Label.shiftOffset_value {d : ℕ} (L : Label d) (s : ℝ → ℝ)
    (h : ℝ) (x : Fin d → ℝ) :
    (L.shiftOffset s).value h x = L.value h x - s h := by
  simp only [Label.shiftOffset, Label.value]
  ring

/-- The finite union of shifted local families; duplicate labels are harmless. -/
def shiftedFamily {d : ℕ} {ι : Type uIota} [Fintype ι]
    (Λ : ι → Finset (Label d)) (s : ι → ℝ → ℝ) : Finset (Label d) := by
  classical
  exact Finset.univ.biUnion (fun i => (Λ i).image (fun L => L.shiftOffset (s i)))

theorem mem_shiftedFamily_iff {d : ℕ} {ι : Type uIota} [Fintype ι]
    (Λ : ι → Finset (Label d)) (s : ι → ℝ → ℝ) (J : Label d) :
    J ∈ shiftedFamily Λ s ↔ ∃ i, ∃ L ∈ Λ i, L.shiftOffset (s i) = J := by
  classical
  simp [shiftedFamily]

theorem shiftOffset_mem_shiftedFamily {d : ℕ} {ι : Type uIota} [Fintype ι]
    (Λ : ι → Finset (Label d)) (s : ι → ℝ → ℝ)
    {i : ι} {L : Label d} (hL : L ∈ Λ i) :
    L.shiftOffset (s i) ∈ shiftedFamily Λ s :=
  (mem_shiftedFamily_iff Λ s _).mpr ⟨i, L, hL, rfl⟩

theorem active_shiftedFamily_restrict {d : ℕ} {ι : Type uIota} [Fintype ι]
    (Λ : ι → Finset (Label d)) (s : ι → ℝ → ℝ)
    {i : ι} {L : Label d} {h : ℝ} {x : Fin d → ℝ}
    (hL : L ∈ Λ i)
    (hA : Active (shiftedFamily Λ s) (L.shiftOffset (s i)) h x) :
    Active (Λ i) L h x := by
  refine ⟨hL, ?_⟩
  intro J hJ
  have hcomp := hA.2 (J.shiftOffset (s i)) (shiftOffset_mem_shiftedFamily Λ s hJ)
  simpa only [Label.shiftOffset_value, sub_le_sub_iff_right] using hcomp

/-- An arbitrary total extension is only used at valid cut indices. -/
def extendedCut {n : ℕ} (q : Fin n → ℝ) (k : ℕ) : ℝ :=
  if hk : k < n then q ⟨k, hk⟩ else 0

@[simp] theorem extendedCut_fin {n : ℕ} (q : Fin n → ℝ) (i : Fin n) :
    extendedCut q i.val = q i := by simp [extendedCut, i.isLt]

/-- Cumulative shifts select a local family on the corresponding exponent cell. -/
def cutShift {n : ℕ} (q : Fin n → ℝ) (j : Fin (n + 1)) (h : ℝ) : ℝ :=
  ∑ k ∈ Finset.range j.val, h ^ extendedCut q k

/-- Closed cells include tied transition points. -/
def InCutCell {n : ℕ} (q : Fin n → ℝ) (a b : ℝ)
    (j : Fin (n + 1)) (μ : ℝ) : Prop :=
  a ≤ μ ∧ μ ≤ b ∧
    (∀ i : Fin n, i.castSucc = j → μ ≤ q i) ∧
    (∀ i : Fin n, i.succ = j → q i ≤ μ)

/-- Actual canonical label activity supplies the upper-cut inequality needed
by the asymptotic neighboring-family comparison. -/
theorem active_shiftedFamily_upper_cut {d n : ℕ}
    (Λ : Fin (n + 1) → Finset (Label d))
    (q : Fin n → ℝ) (t : Fin (n + 1) → ℝ)
    (hbase : ∀ j, (⟨fun _ => t j, fun _ => 0⟩ : Label d) ∈ Λ j)
    (i : Fin n) {L : Label d}
    (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ)
    (hpos : ∀ k, 0 < h k) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 p₀))
    (hoff : L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ q i))
    (hA : ∀ k, Active (shiftedFamily Λ (cutShift q))
      (L.shiftOffset (cutShift q i.castSucc)) (h k) (powerPoint (h k) (p k))) :
    ∃ k, p₀ k ≤ q i := by
  have hto : Tendsto h atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hh, Filter.Eventually.of_forall hpos⟩
  apply AffineGluing.shifted_active_upper_cut
    (x := fun j k => h k ^ p k j) (c := fun k => L.offset (h k))
    (fun j k => h k ^ extendedCut q j) L.slope p₀ (t i.succ) (q i) i.val
  · exact Filter.Eventually.of_forall (fun k => Real.rpow_pos_of_pos (hpos k) _)
  · simpa only [extendedCut_fin, Function.comp_def] using hoff.comp_tendsto hto
  · intro k hk
    simpa only [extendedCut_fin, Function.comp_def] using isLittleO_rpow_variable_of_gap
      (Filter.Eventually.of_forall hpos) hh
      (((continuous_apply k).tendsto p₀).comp hp) tendsto_const_nhds hk
  · apply Filter.Eventually.of_forall
    intro k
    have hc := (hA k).2
      ((⟨fun _ => t i.succ, fun _ => 0⟩ : Label d).shiftOffset (cutShift q i.succ))
      (shiftOffset_mem_shiftedFamily Λ (cutShift q) (hbase i.succ))
    simpa only [Label.shiftOffset, Label.value, powerPoint, cutShift,
      Fin.val_succ, Fin.val_castSucc, add_zero, zero_add, zero_sub, sub_eq_add_neg, add_assoc] using hc

/-- The corresponding lower-cut conclusion, using the strict slope gap to
the preceding baseline. -/
theorem active_shiftedFamily_lower_cut {d n : ℕ}
    (Λ : Fin (n + 1) → Finset (Label d))
    (q : Fin n → ℝ) (t : Fin (n + 1) → ℝ)
    (hbase : ∀ j, (⟨fun _ => t j, fun _ => 0⟩ : Label d) ∈ Λ j)
    (i : Fin n) {L : Label d} (hr : ∀ k, t i.castSucc < L.slope k)
    (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ)
    (hpos : ∀ k, 0 < h k) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 p₀))
    (hoff : L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ q i))
    (hA : ∀ k, Active (shiftedFamily Λ (cutShift q))
      (L.shiftOffset (cutShift q i.succ)) (h k) (powerPoint (h k) (p k))) :
    ∀ k, q i ≤ p₀ k := by
  have hto : Tendsto h atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hh, Filter.Eventually.of_forall hpos⟩
  apply AffineGluing.shifted_active_lower_cut
    (x := fun j k => h k ^ p k j) (c := fun k => L.offset (h k))
    (fun j k => h k ^ extendedCut q j) L.slope p₀ (t i.castSucc) (q i) i.val hr
  · exact Filter.Eventually.of_forall (fun k => Real.rpow_pos_of_pos (hpos k) _)
  · simpa only [extendedCut_fin, Function.comp_def] using hoff.comp_tendsto hto
  · exact Filter.Eventually.of_forall
      (fun k j => (Real.rpow_pos_of_pos (hpos k) (p k j)).le)
  · intro k hk
    simpa only [extendedCut_fin, Function.comp_def] using tendsto_rpow_div_rpow_atTop_of_gap
      (Filter.Eventually.of_forall hpos) hh
      (((continuous_apply k).tendsto p₀).comp hp) tendsto_const_nhds hk
  · apply Filter.Eventually.of_forall
    intro k
    have hc := (hA k).2
      ((⟨fun _ => t i.castSucc, fun _ => 0⟩ : Label d).shiftOffset (cutShift q i.castSucc))
      (shiftOffset_mem_shiftedFamily Λ (cutShift q) (hbase i.castSucc))
    simpa only [Label.shiftOffset, Label.value, powerPoint, cutShift,
      Fin.val_succ, Fin.val_castSucc, add_zero, zero_add, zero_sub, sub_eq_add_neg, add_assoc] using hc

/-- Assemble the global sequential approximation statement from local cell
statements. All activity is activity of the actual finite union of shifted
canonical labels; no analytically unsupported preferred minimizer is selected. -/
theorem approximatesOnCube_shiftedFamily_of_cells {d n : ℕ} [NeZero d]
    (Λ : Fin (n + 1) → Finset (Label d))
    (q : Fin n → ℝ) (t : Fin (n + 1) → ℝ)
    (a b : ℝ) (E : (Fin d → ℝ) → ℝ)
    (ht : StrictMono t)
    (hbase : ∀ j, (⟨fun _ => t j, fun _ => 0⟩ : Label d) ∈ Λ j)
    (hslope : ∀ j, ∀ L ∈ Λ j, ∀ k, t j ≤ L.slope k)
    (hoffUpper : ∀ i : Fin n, ∀ L ∈ Λ i.castSucc,
      L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ q i))
    (hoffLower : ∀ i : Fin n, ∀ L ∈ Λ i.succ,
      L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ q i))
    (hlocal : ∀ j, ∀ L ∈ Λ j,
      ∀ (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ),
      (∀ k, 0 < h k) → Tendsto h atTop (𝓝 0) →
      Tendsto p atTop (𝓝 p₀) → Cube a b p₀ →
      InCutCell q a b j (coordinateMinimum p₀) →
      (∀ k, Active (Λ j) L (h k) (powerPoint (h k) (p k))) →
      ‖p₀ - L.slope‖ < E L.slope) :
    ApproximatesOnCube (shiftedFamily Λ (cutShift q)) a b E := by
  intro J hJ h p p₀ hpos hh hp hcube hA
  obtain ⟨j, L, hL, rfl⟩ := (mem_shiftedFamily_iff Λ (cutShift q) J).mp hJ
  change ‖p₀ - L.slope‖ < E L.slope
  apply hlocal j L hL h p p₀ hpos hh hp hcube
  · have hm := hasMinimum_coordinateMinimum p₀
    obtain ⟨k, hk⟩ := hm.2
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hk]
      exact (hcube k).1
    · rw [← hk]
      exact (hcube k).2
    · intro i hij
      subst j
      obtain ⟨k, hki⟩ := active_shiftedFamily_upper_cut Λ q t hbase i
        h p p₀ hpos hh hp (hoffUpper i L hL) hA
      exact (hm.1 k).trans hki
    · intro i hij
      subst j
      have hr : ∀ k, t i.castSucc < L.slope k := fun k =>
        (ht (by simp : i.castSucc < i.succ)).trans_le (hslope i.succ L hL k)
      have hki := active_shiftedFamily_lower_cut Λ q t hbase i hr
        h p p₀ hpos hh hp (hoffLower i L hL) hA
      rw [← hk]
      exact hki k
  · intro k
    exact active_shiftedFamily_restrict Λ (cutShift q) hL (hA k)

/-- Every cumulative cut shift is negligible at the original lower exponent. -/
theorem cutShift_isLittleO {n : ℕ} (q : Fin n → ℝ) (a : ℝ)
    (hq : ∀ i, a < q i) (j : Fin (n + 1)) :
    cutShift q j =o[𝓝[>] (0 : ℝ)] (fun h => h ^ a) := by
  unfold cutShift
  apply IsLittleO.fun_sum
  intro k hk
  have hkj : k < j.val := Finset.mem_range.mp hk
  have hkn : k < n := lt_of_lt_of_le hkj (Nat.le_of_lt_succ j.isLt)
  have hpow := isLittleO_rpow_variable_of_gap
    (h := fun h : ℝ => h) (l := 𝓝[>] (0 : ℝ))
    (show ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), 0 < h from self_mem_nhdsWithin)
    (show Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 0) from nhdsWithin_le_nhds)
    (tendsto_const_nhds (x := q ⟨k, hkn⟩)) (tendsto_const_nhds (x := a)) (hq ⟨k, hkn⟩)
  simpa only [extendedCut, dite_eq_left hkn] using hpow

/-- The union stays nonempty, preserves slope bounds, and preserves the
required offset decay after all cumulative shifts. -/
theorem shiftedFamily_properties {d n : ℕ}
    (Λ : Fin (n + 1) → Finset (Label d)) (q : Fin n → ℝ) (a b : ℝ)
    (hne : (Λ 0).Nonempty)
    (hslopes : ∀ j, ∀ L ∈ Λ j, Cube a b L.slope)
    (hoff : ∀ j, ∀ L ∈ Λ j, L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ a))
    (hq : ∀ i, a < q i) :
    (shiftedFamily Λ (cutShift q)).Nonempty ∧
      ∀ J ∈ shiftedFamily Λ (cutShift q), Cube a b J.slope ∧
        J.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ a) := by
  constructor
  · obtain ⟨L, hL⟩ := hne
    exact ⟨L.shiftOffset (cutShift q 0), shiftOffset_mem_shiftedFamily Λ (cutShift q) hL⟩
  · intro J hJ
    obtain ⟨j, L, hL, rfl⟩ := (mem_shiftedFamily_iff Λ (cutShift q) J).mp hJ
    exact ⟨hslopes j L hL, (hoff j L hL).sub (cutShift_isLittleO q a hq j)⟩

end Problem326.Affine

end

end OAI
