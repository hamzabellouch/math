import Mathlib

namespace OAI

universe uIota

noncomputable section

open scoped BigOperators
open Filter Topology

namespace Problem326.Affine

structure Label (d : ℕ) where
  slope : Fin d → ℝ
  offset : ℝ → ℝ

def Label.value {d : ℕ} (L : Label d) (h : ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i, L.slope i * x i + L.offset h

def Active {d : ℕ} (Λ : Finset (Label d)) (L : Label d)
    (h : ℝ) (x : Fin d → ℝ) : Prop :=
  L ∈ Λ ∧ ∀ J ∈ Λ, L.value h x ≤ J.value h x

def Cube {d : ℕ} (a b : ℝ) (p : Fin d → ℝ) : Prop :=
  ∀ i, a ≤ p i ∧ p i ≤ b

def HasMinimum {d : ℕ} (p : Fin d → ℝ) (t : ℝ) : Prop :=
  (∀ i, t ≤ p i) ∧ ∃ i, p i = t

def powerPoint {d : ℕ} (h : ℝ) (p : Fin d → ℝ) : Fin d → ℝ :=
  fun i => h ^ p i

/-- The sequential condition required of a family at one fixed minimum level. -/
def ApproximatesAtMinimum {d : ℕ} (Λ : Finset (Label d))
    (a b t : ℝ) (E : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ L ∈ Λ, ∀ (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ),
    (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
    Tendsto p atTop (𝓝 p₀) → Cube a b p₀ → HasMinimum p₀ t →
    (∀ n, Active Λ L (h n) (powerPoint (h n) (p n))) →
    ‖p₀ - L.slope‖ < E L.slope

lemma active_mono {d : ℕ} {Λ Γ : Finset (Label d)} {L : Label d}
    {h : ℝ} {x : Fin d → ℝ} (hΛ : Λ ⊆ Γ) (hL : L ∈ Λ)
    (ha : Active Γ L h x) : Active Λ L h x :=
  ⟨hL, fun J hJ => ha.2 J (hΛ hJ)⟩

lemma active_singleton {d : ℕ} (L : Label d) (h : ℝ) (x : Fin d → ℝ) :
    Active {L} L h x := by
  classical
  refine ⟨by simp, ?_⟩
  intro J hJ
  have hJL : J = L := by simpa using hJ
  subst J
  exact le_rfl

/-- Comparison activity is insensitive to a common additive shift. -/
lemma active_iff_common_shift {ι : Type uIota} (s : Finset ι) (v : ι → ℝ)
    (i : ι) (c : ℝ) :
    (∀ j ∈ s, v i + c ≤ v j + c) ↔ (∀ j ∈ s, v i ≤ v j) := by
  simp only [add_le_add_iff_right]

lemma exists_active {d : ℕ} (Λ : Finset (Label d)) (hne : Λ.Nonempty)
    (h : ℝ) (x : Fin d → ℝ) : ∃ L, Active Λ L h x := by
  classical
  obtain ⟨L, hL, hmin⟩ := Λ.exists_min_image (fun J => J.value h x) hne
  exact ⟨L, hL, hmin⟩

/-- A finite collection of positive tolerances admits one strict common bound. -/
lemma exists_common_pos_lt {ι : Type uIota} (s : Finset ι) (E : ι → ℝ)
    (hE : ∀ i ∈ s, 0 < E i) (u : ℝ) (hu : 0 < u) :
    ∃ δ : ℝ, 0 < δ ∧ δ < u ∧ ∀ i ∈ s, δ < E i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨u / 2, by positivity, by linarith, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨δ, hδ, hδu, hδE⟩ := ih (fun j hj => hE j (Finset.mem_insert_of_mem hj))
      have hEi : 0 < E i := hE i (Finset.mem_insert_self _ _)
      refine ⟨min δ (E i / 2), lt_min hδ (by positivity),
        (min_le_left _ _).trans_lt hδu, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (min_le_right _ _).trans_lt (by linarith)
      · exact (min_le_left _ _).trans_lt (hδE j hj)

/-- The choice of the next type threshold in the fixed-minimum induction.
The upper endpoint can itself be the preceding threshold, giving a decreasing
sequence while only querying finitely many tolerance values. -/
lemma exists_threshold {ι : Type uIota} (s : Finset ι) (E : ι → ℝ)
    (hE : ∀ i ∈ s, 0 < E i) {t u : ℝ} (htu : t < u) :
    ∃ β : ℝ, t < β ∧ β < u ∧ ∀ i ∈ s, β - t < E i := by
  obtain ⟨δ, hδ, hδu, hδE⟩ := exists_common_pos_lt s E hE (u - t) (sub_pos.mpr htu)
  refine ⟨t + δ, by linarith, by linarith, ?_⟩
  intro i hi
  simpa using hδE i hi

lemma eq_const_of_minimum_at_upper {d : ℕ} {a b : ℝ} {p : Fin d → ℝ}
    (hp : Cube a b p) (hm : HasMinimum p b) : p = fun _ => b := by
  funext i
  exact le_antisymm (hp i).2 (hm.1 i)

lemma eq_const_of_minimum_one {p : Fin 1 → ℝ} {t : ℝ}
    (hm : HasMinimum p t) : p = fun _ => t := by
  obtain ⟨i, hi⟩ := hm.2
  funext j
  have hij : j = i := Subsingleton.elim _ _
  simpa [hij] using hi

/-- Final coordinate estimate for types with a further threshold. -/
lemma norm_sub_lt_of_support {d : ℕ} (U : Finset (Fin d))
    {p r : Fin d → ℝ} {t β ε : ℝ} (hε : 0 < ε)
    (hin : ∀ i ∈ U, |p i - r i| < ε)
    (hout : ∀ i ∉ U, r i = t ∧ t ≤ p i ∧ p i ≤ β)
    (hβ : β - t < ε) : ‖p - r‖ < ε := by
  rw [pi_norm_lt_iff hε]
  intro i
  change |p i - r i| < ε
  by_cases hi : i ∈ U
  · exact hin i hi
  · obtain ⟨hr, hp, hpβ⟩ := hout i hi
    rw [hr, abs_of_nonneg (sub_nonneg.mpr hp)]
    linarith

/-- For the last type, the unique unraised coordinate realizes the minimum. -/
lemma off_support_eq_minimum {d : ℕ} (U : Finset (Fin d))
    {p : Fin d → ℝ} {t : ℝ} (hm : HasMinimum p t)
    (hin : ∀ i ∈ U, t < p i) (hcomp : ∀ i ∉ U, ∀ j ∉ U, i = j) :
    ∀ i ∉ U, p i = t := by
  obtain ⟨j, hj⟩ := hm.2
  have hjU : j ∉ U := by
    intro hjU
    have := hin j hjU
    linarith
  intro i hi
  have hij : i = j := hcomp i hi j hjU
  simpa [hij] using hj

/-- The singleton family verifies the fixed-minimum base case in dimension one. -/
lemma singleton_approximates_one (a b t : ℝ) (E : (Fin 1 → ℝ) → ℝ)
    (hE : 0 < E (fun _ => t)) :
    ApproximatesAtMinimum {⟨fun _ => t, fun _ => 0⟩} a b t E := by
  classical
  intro L hL h p p₀ hh hlim hp hp₀ hm ha
  have hL' : L = (⟨fun _ => t, fun _ => 0⟩ : Label 1) := by simpa using hL
  subst L
  rw [eq_const_of_minimum_one hm]
  simpa using hE

/-- The other singleton base case works in every dimension at the upper corner. -/
lemma singleton_approximates_upper {d : ℕ} (a b : ℝ)
    (E : (Fin d → ℝ) → ℝ) (hE : 0 < E (fun _ => b)) :
    ApproximatesAtMinimum {⟨fun _ => b, fun _ => 0⟩} a b b E := by
  classical
  intro L hL h p p₀ hh hlim hp hp₀ hm ha
  have hL' : L = (⟨fun _ => b, fun _ => 0⟩ : Label d) := by simpa using hL
  subst L
  rw [eq_const_of_minimum_at_upper hp₀ hm]
  simpa using hE

end Problem326.Affine

end

end OAI
