import OAI.Analysis.MassAction.AffineFamilyGluing
import OAI.Analysis.MassAction.IntervalGluing
import OAI.Analysis.MassAction.UniformOffsetDecay

namespace OAI

noncomputable section

open Filter Asymptotics
open scoped BigOperators Topology

namespace Problem326.Affine

/-- The closed cell between neighboring cuts is contained in the corresponding
open localization neighborhood, including all endpoint and tie cases. -/
theorem InCutCell.abs_sub_lt {n : ℕ} {q : Fin n → ℝ}
    {a b : ℝ} {t ρ : Fin (n + 1) → ℝ}
    (hfirst : t 0 - ρ 0 < a)
    (hlast : b < t (Fin.last n) + ρ (Fin.last n))
    (hcuts : ∀ i : Fin n,
      q i ∈ Set.Ioo (t i.castSucc - ρ i.castSucc) (t i.castSucc + ρ i.castSucc) ∧
      q i ∈ Set.Ioo (t i.succ - ρ i.succ) (t i.succ + ρ i.succ))
    {j : Fin (n + 1)} {μ : ℝ} (hcell : InCutCell q a b j μ) :
    |μ - t j| < ρ j := by
  apply abs_lt.mpr
  have hlo : t j - ρ j < μ := by
    by_cases hj : j = 0
    · subst j
      exact hfirst.trans_le hcell.1
    · have hjpos : 0 < j.val := by
        have hjne : j.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using hj
        omega
      let i : Fin n := ⟨j.val - 1, by omega⟩
      have hij : i.succ = j := by apply Fin.ext; dsimp [i]; omega
      have hq := (hcuts i).2.1
      rw [hij] at hq
      exact hq.trans_le (hcell.2.2.2 i hij)
  have hhi : μ < t j + ρ j := by
    by_cases hj : j = Fin.last n
    · subst j
      exact hcell.2.1.trans_lt hlast
    · have hjlt : j.val < n := by
        have hjne : j.val ≠ n := by simpa only [Fin.ext_iff, Fin.val_last] using hj
        omega
      let i : Fin n := ⟨j.val, hjlt⟩
      have hij : i.castSucc = j := by apply Fin.ext; rfl
      have hq := (hcuts i).1.2
      rw [hij] at hq
      exact (hcell.2.2.1 i hij).trans_lt hq
  constructor <;> linarith

/-- All data needed from one fixed-minimum construction after its localization
radius has been shrunk to retain a stronger offset decay exponent. -/
structure LocalFamilyData (d : ℕ) [NeZero d] (a b t : ℝ)
    (E : (Fin d → ℝ) → ℝ) where
  family : Finset (Label d)
  radius : ℝ
  radius_pos : 0 < radius
  baseline_mem : (⟨fun _ => t, fun _ => 0⟩ : Label d) ∈ family
  slope_cube : ∀ L ∈ family, Cube a b L.slope
  slope_lower : ∀ L ∈ family, ∀ k, t ≤ L.slope k
  offset_decay : ∀ L ∈ family,
    L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ (t + radius))
  approximates_near : ∀ L ∈ family,
    ∀ (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ),
    (∀ k, 0 < h k) → Tendsto h atTop (𝓝 0) →
    Tendsto p atTop (𝓝 p₀) → Cube a b p₀ →
    |coordinateMinimum p₀ - t| < radius →
    (∀ k, Active family L (h k) (powerPoint (h k) (p k))) →
    ‖p₀ - L.slope‖ < E L.slope

/-- The fixed-minimum theorem and stronger individual big-O exponents supply
exactly the local data required for global gluing. -/
theorem localFamilyData_nonempty_of_fixedMinimum {d : ℕ} [NeZero d]
    (a b t : ℝ) (E : (Fin d → ℝ) → ℝ) (Λ : Finset (Label d))
    (hbase : (⟨fun _ => t, fun _ => 0⟩ : Label d) ∈ Λ)
    (hcube : ∀ L ∈ Λ, Cube a b L.slope)
    (hlower : ∀ L ∈ Λ, ∀ k, t ≤ L.slope k)
    (hdecay : ∀ L ∈ Λ, ∃ β : ℝ, t < β ∧
      L.offset =O[𝓝[>] (0 : ℝ)] (fun h => h ^ β))
    (happrox : ApproximatesAtMinimum Λ a b t E) :
    Nonempty (LocalFamilyData d a b t E) := by
  classical
  obtain ⟨ρ₀, hρ₀, hnear⟩ := happrox.exists_nearby
  let : Nonempty ↥Λ := ⟨⟨_, hbase⟩⟩
  obtain ⟨ρ, hρ, hρsmall, hρdecay⟩ := exists_radius_with_offset_decay
    (fun L : Λ => L.val.offset) t ρ₀ hρ₀ (fun L => hdecay L.val L.property)
  refine ⟨⟨Λ, ρ, hρ, hbase, hcube, hlower, ?_, ?_⟩⟩
  · intro L hL
    exact hρdecay ⟨L, hL⟩
  · intro L hL h p p₀ hpos hh hp hp₀ hclose hactive
    exact hnear L hL h p p₀ hpos hh hp hp₀ (hclose.trans hρsmall) hactive

/-- A convenient strict-power comparison for offset decay. -/
theorem offset_isLittleO_of_exponent_lt {c : ℝ → ℝ} {a b : ℝ}
    (hc : c =o[𝓝[>] (0 : ℝ)] (fun h => h ^ b)) (hab : a < b) :
    c =o[𝓝[>] (0 : ℝ)] (fun h => h ^ a) := by
  apply hc.trans
  exact isLittleO_rpow_variable_of_gap
    (h := fun h : ℝ => h) (l := 𝓝[>] (0 : ℝ))
    (show ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), 0 < h from self_mem_nhdsWithin)
    (show Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 0) from nhdsWithin_le_nhds)
    tendsto_const_nhds tendsto_const_nhds hab

/-- Complete global gluing: one localized family at every possible minimum
level gives a fixed finite family on the whole exponent cube. The only input
not discharged here is existence of the fixed-minimum local families. -/
theorem exists_global_family_of_local_data {d : ℕ} [NeZero d]
    {a b : ℝ} (hab : a ≤ b) (E : (Fin d → ℝ) → ℝ)
    (hdata : ∀ t ∈ Set.Icc a b, Nonempty (LocalFamilyData d a b t E)) :
    ∃ Λ : Finset (Label d), Λ.Nonempty ∧
      (∀ L ∈ Λ, Cube a b L.slope ∧
        L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ a)) ∧
      ApproximatesOnCube Λ a b E := by
  classical
  let D : (t : {t : ℝ // t ∈ Set.Icc a b}) → LocalFamilyData d a b t.val E :=
    fun t => Classical.choice (hdata t.val t.property)
  let r : ℝ → ℝ := fun t => if ht : t ∈ Set.Icc a b then (D ⟨t, ht⟩).radius else 1
  have hr : ∀ t ∈ Set.Icc a b, 0 < r t := by
    intro t ht
    simpa only [r, dite_eq_left ht] using (D ⟨t, ht⟩).radius_pos
  obtain ⟨n, t, q, ht, hcent, hfirst, hlast, hcuts⟩ :=
    IntervalGluing.exists_interval_gluing hab r hr
  let F : (j : Fin (n + 1)) → LocalFamilyData d a b (t j) E :=
    fun j => D ⟨t j, hcent j⟩
  let Γ : Fin (n + 1) → Finset (Label d) := fun j => (F j).family
  have hrF : ∀ j, r (t j) = (F j).radius := by
    intro j
    simp only [r, dite_eq_left (hcent j), F]
  have hcutmem : ∀ i : Fin n,
      q i ∈ Set.Ioo (t i.castSucc - (F i.castSucc).radius)
        (t i.castSucc + (F i.castSucc).radius) ∧
      q i ∈ Set.Ioo (t i.succ - (F i.succ).radius)
        (t i.succ + (F i.succ).radius) := by
    intro i
    simpa only [hrF] using (hcuts i).2.2
  have hinitial : t 0 - (F 0).radius < a := by
    simpa only [hrF] using hfirst.1
  have hfinal : b < t (Fin.last n) + (F (Fin.last n)).radius := by
    simpa only [hrF] using hlast.2
  have hqa : ∀ i : Fin n, a < q i :=
    fun i => (hcent i.castSucc).1.trans_lt (hcuts i).1
  have hdecay : ∀ j, ∀ L ∈ Γ j,
      L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ a) := by
    intro j L hL
    apply offset_isLittleO_of_exponent_lt ((F j).offset_decay L hL)
    have htja := (hcent j).1
    have hrad := (F j).radius_pos
    linarith
  have hprop := shiftedFamily_properties Γ q a b
    ⟨_, (F 0).baseline_mem⟩
    (fun j L hL => (F j).slope_cube L hL) hdecay hqa
  refine ⟨shiftedFamily Γ (cutShift q), hprop.1, hprop.2, ?_⟩
  apply approximatesOnCube_shiftedFamily_of_cells Γ q t a b E ht
    (fun j => (F j).baseline_mem) (fun j L hL => (F j).slope_lower L hL)
  · intro i L hL
    exact offset_isLittleO_of_exponent_lt ((F i.castSucc).offset_decay L hL)
      (hcutmem i).1.2
  · intro i L hL
    exact offset_isLittleO_of_exponent_lt ((F i.succ).offset_decay L hL)
      (hcutmem i).2.2
  · intro j L hL h p p₀ hpos hh hp hcube hcell hactive
    exact (F j).approximates_near L hL h p p₀ hpos hh hp hcube
      (InCutCell.abs_sub_lt (t := t) (ρ := fun j => (F j).radius) hinitial hfinal hcutmem hcell) hactive

/-- Direct interface for the dimension induction: fixed-minimum families with
individual stronger big-O exponents imply the complete affine approximation
lemma in that dimension. -/
theorem exists_global_family_of_fixedMinimum {d : ℕ} [NeZero d]
    {a b : ℝ} (hab : a ≤ b) (E : (Fin d → ℝ) → ℝ)
    (hfixed : ∀ t ∈ Set.Icc a b, ∃ Λ : Finset (Label d),
      (⟨fun _ => t, fun _ => 0⟩ : Label d) ∈ Λ ∧
      (∀ L ∈ Λ, Cube a b L.slope) ∧
      (∀ L ∈ Λ, ∀ k, t ≤ L.slope k) ∧
      (∀ L ∈ Λ, ∃ β : ℝ, t < β ∧
        L.offset =O[𝓝[>] (0 : ℝ)] (fun h => h ^ β)) ∧
      ApproximatesAtMinimum Λ a b t E) :
    ∃ Λ : Finset (Label d), Λ.Nonempty ∧
      (∀ L ∈ Λ, Cube a b L.slope ∧
        L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ a)) ∧
      ApproximatesOnCube Λ a b E := by
  apply exists_global_family_of_local_data hab E
  intro t ht
  obtain ⟨Λ, hbase, hcube, hlower, hdecay, happrox⟩ := hfixed t ht
  exact localFamilyData_nonempty_of_fixedMinimum a b t E Λ hbase hcube hlower hdecay happrox

end Problem326.Affine

end

end OAI
