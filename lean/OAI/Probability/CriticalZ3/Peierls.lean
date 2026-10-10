import OAI.Probability.CriticalZ3.Matching

namespace OAI

universe uOmega

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

open Filter Topology

namespace PlanarBoundary
open Classical _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
variable {Ω : Type uOmega} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

def blocked {n : ℕ} (Bad : Point → Set Ω) (c : Code n) : Set Ω :=
  {ω | ∀ i, ω ∈ Bad (inner c i) ∨ ω ∈ Bad (outer c i)}

/-- Matching and endpoint union bound; the bad vertices may be arbitrarily dependent. -/
theorem blocked_bound {n : ℕ} (Bad : Point → Set Ω) (c : Code n) (hc : Valid c)
    {f : ℝ} (hf0 : 0 < f) (hf1 : 2*f ≤ 1)
    (hbad : ∀ s : Finset Point, μ.real {ω | ∀ v ∈ s, ω ∈ Bad v} ≤ f^s.card) :
    μ.real (blocked Bad c) ≤ (2*f)^((n : ℝ)/7) := by
  obtain ⟨s,hpair,hsize⟩ := exists_code_matching c hc
  let choose (η : s → Bool) (i : s) := if η i then inner c i.val else outer c i.val
  let E (η : s → Bool) : Set Ω := {ω | ∀ i : s, ω ∈ Bad (choose η i)}
  have hE (η : s → Bool) : μ.real (E η) ≤ f^s.card := by
    let t : Finset Point := Finset.univ.image (choose η)
    have hinj : Function.Injective (choose η) :=
      FiniteMatching.endpoint_injective _ _ s hpair η
    have ht : t.card = s.card := by
      rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_coe]
    have he : E η = {ω | ∀ v ∈ t, ω ∈ Bad v} := by
      ext ω
      constructor
      · intro h v hv
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
        exact h i
      · intro h i
        exact h _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    rw [he,←ht]
    exact hbad t
  have hcover : blocked Bad c ⊆ ⋃ η, E η := by
    intro ω hω
    let η : s → Bool := fun i => if ω ∈ Bad (inner c i.val) then true else false
    refine Set.mem_iUnion.mpr ⟨η,?_⟩
    intro i
    by_cases hi : ω ∈ Bad (inner c i.val)
    · simp only [choose,η,hi,ite_true]
    · simpa only [choose,η,hi,ite_false,Bool.false_eq_true] using (hω i.val).resolve_left hi
  have hbound : μ.real (blocked Bad c) ≤ (2*f)^s.card := by
    calc
      _ ≤ μ.real (⋃ η, E η) := measureReal_mono hcover
      _ ≤ ∑ η, μ.real (E η) := measureReal_iUnion_fintype_le E
      _ ≤ ∑ _η : s → Bool, f^s.card := Finset.sum_le_sum (fun η _ => hE η)
      _ = (2*f)^s.card := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,
          Fintype.card_coe,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat,mul_pow]
  apply hbound.trans
  rw [←Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_ge (by positivity) hf1
  have hs : (n : ℝ) ≤ 7*s.card := by exact_mod_cast hsize
  linarith

/-- Codes arising from actual boundaries are the only candidates needed. -/
def candidate {n : ℕ} (Bad : Point → Set Ω) (c : {c : Code n // Valid c}) : Set Ω :=
  blocked Bad c.val

theorem candidates_bound (Bad : Point → Set Ω) {f : ℝ} (hf0 : 0 < f) (hf1 : 2*f ≤ 1)
    (hbad : ∀ s : Finset Point, μ.real {ω | ∀ v ∈ s, ω ∈ Bad v} ≤ f^s.card) (n : ℕ) :
    μ.real (⋃ c : {c : Code n // Valid c}, candidate Bad c) ≤
      4*(n : ℝ)*4^n*(2*f)^((n : ℝ)/7) := by
  calc
    _ ≤ ∑ c : {c : Code n // Valid c}, μ.real (candidate Bad c) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _c : {c : Code n // Valid c}, (2*f)^((n : ℝ)/7) :=
      Finset.sum_le_sum (fun c _ => blocked_bound μ Bad c.val c.property hf0 hf1 hbad)
    _ = (Fintype.card {c : Code n // Valid c} : ℝ)*(2*f)^((n : ℝ)/7) := by simp
    _ ≤ (Fintype.card (Code n) : ℝ)*(2*f)^((n : ℝ)/7) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Fintype.card_subtype_le (fun c : Code n => Valid c)
      · positivity
    _ = _ := by rw [card_code]; push_cast; ring

/-- A summable real upper bound for countably many events bounds their union. -/
theorem union_bound (A : ℕ → Set Ω) (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n)
    (hg : Summable g) (hA : ∀ n, μ.real (A n) ≤ g n) :
    μ.real (⋃ n, A n) ≤ ∑' n, g n := by
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (tsum_nonneg hg0)).mp
  rw [ENNReal.ofReal_tsum_of_nonneg hg0 hg]
  apply (measure_iUnion_le A).trans
  apply ENNReal.tsum_le_tsum
  intro n
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (hg0 n)).mpr (hA n)

/-- Exact numerical budget for the benign overcount of encoded trails. -/
theorem encoded_budget_hasSum :
    HasSum (fun n : ℕ => 4*(n : ℝ)*4^n*(2*CriticalScales.contourError)^((n : ℝ)/7)) (25/144 : ℝ) := by
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(4/100 : ℝ)‖ < 1)).mul_left 4
  have he (n : ℕ) : 4*(n : ℝ)*4^n*(2*CriticalScales.contourError)^((n : ℝ)/7) =
      4*((n : ℝ)*(4/100 : ℝ)^n) := by
    rw [CriticalScales.contour_power]
    have hp : (4/100 : ℝ)^n = 4^n*(1/100 : ℝ)^n := by rw [←mul_pow]; congr 1; ring
    rw [hp]
    ring
  simp_rw [he]
  have hz : 4*((4/100 : ℝ)/(1-4/100)^2) = 25/144 := by norm_num
  rw [hz] at h
  exact h

omit [MeasurableSpace Ω] in
/-- The main contour inclusion, without conditioning on a random boundary. -/
theorem finite_good_subset (Good : Ω → Set Point) (Bad : Point → Set Ω)
    (houtside : ∀ ω, (Good ω).Finite → ∀ x ∈ Good ω, ∀ d : Direction,
      x+outward d ∉ Good ω → ω ∈ Bad (x+outward d)) :
    {ω | (Good ω).Finite ∧ (0,0) ∈ Good ω} ⊆
      ⋃ n, ⋃ c : {c : Code n // Valid c}, candidate Bad c := by
  intro ω hω
  let X := hω.1.toFinset
  have hX : (0,0) ∈ X := by simpa only [X,Set.Finite.mem_toFinset] using hω.2
  obtain ⟨n,_,c,e,hinj,he⟩ := exists_boundary_code X hX
  refine Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨⟨c,X,e,hinj,he⟩,?_⟩⟩
  intro i
  right
  change ω ∈ Bad ((traceSide c i).1+outward (traceSide c i).2)
  rw [he]
  apply houtside ω hω.1
  · simpa only [X,Set.Finite.mem_toFinset] using (e i).property.1
  · simpa only [X,Set.Finite.mem_toFinset] using (e i).property.2

theorem finite_good_bound (Good : Ω → Set Point) (Bad : Point → Set Ω)
    (houtside : ∀ ω, (Good ω).Finite → ∀ x ∈ Good ω, ∀ d : Direction,
      x+outward d ∉ Good ω → ω ∈ Bad (x+outward d))
    (hbad : ∀ s : Finset Point,
      μ.real {ω | ∀ v ∈ s, ω ∈ Bad v} ≤ CriticalScales.contourError^s.card) :
    μ.real {ω | (Good ω).Finite ∧ (0,0) ∈ Good ω} ≤ 25/144 := by
  apply (measureReal_mono (finite_good_subset Good Bad houtside)).trans
  have h := union_bound μ (fun n => ⋃ c : {c : Code n // Valid c}, candidate Bad c)
    (fun n => 4*(n : ℝ)*4^n*(2*CriticalScales.contourError)^((n : ℝ)/7))
    (fun n => mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith [CriticalScales.contourError_pos]) _)) encoded_budget_hasSum.summable
    (candidates_bound μ Bad CriticalScales.contourError_pos
      (by linarith [CriticalScales.contourError_lt_half]) hbad)
  rwa [encoded_budget_hasSum.tsum_eq] at h

end PlanarBoundary

end OAI
