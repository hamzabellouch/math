import Mathlib
import OAI.Probability.UnimodularPercolation.Kernel.Spectral

namespace OAI

/-! Haar-measure transport for graph automorphism actions. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory
open scoped ENNReal
universe u v w

 

theorem haar_invInvariant_of_rightInvariant
    {H : Type w} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] [LocallyCompactSpace H]
    (μ : Measure H) [μ.IsHaarMeasure] [μ.Regular] [μ.IsMulRightInvariant] :
    μ.IsInvInvariant := by
  constructor
  let c : ℝ≥0∞ := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul_of_regular μ.inv μ
  have he : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul c continuous_inv.measurable.aemeasurable,
      ← Measure.inv_def μ, hc,
      smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at he
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using he
  let K : TopologicalSpace.PositiveCompacts H := Classical.arbitrary _
  have hpow : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have hpow' : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj
      (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
      K.isCompact.measure_lt_top.ne).mp hpow
  have hc1 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective hpow'
  rw [hc, hc1, one_smul]

section HaarAction
attribute [local instance] Classical.propDecidable Classical.decEq
variable {H : Type w} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]
variable {V : Type u} [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
variable [MulAction H V]

 
def actionStabilizer (x : V) : Set H := {g | g • x = x}

 
def actionOrbit (x : V) : Set V := {y | ∃ g : H, g • x = y}

omit [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H] [Countable V]
  [MeasurableSpace V] [MeasurableSingletonClass V] in
theorem actionOrbit_self (x : V) : x ∈ actionOrbit (H := H) x := ⟨1,one_smul _ _⟩

omit [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H] [Countable V]
  [MeasurableSpace V] [MeasurableSingletonClass V] in
theorem actionOrbit_eq_of_mem {x y : V} (h : y ∈ actionOrbit (H := H) x) :
    actionOrbit (H := H) y = actionOrbit (H := H) x := by
  obtain ⟨g,rfl⟩ := h
  ext z
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨k*g,by simpa only [mul_smul] using hk⟩
  · rintro ⟨k,hk⟩
    exact ⟨k*g⁻¹,by simpa only [mul_smul, inv_smul_smul] using hk⟩

 

omit [MeasurableInv H] [Countable V] [MeasurableSingletonClass V] in
theorem orbit_fiber_measure (μ : Measure H) [μ.IsMulLeftInvariant]
    (_hmeas : ∀ x : V, Measurable (fun g : H => g • x)) (x y : V) :
    μ {g : H | g • x = y} = if y ∈ actionOrbit (H := H) x then μ (actionStabilizer (H := H) x) else 0 := by
  classical
  split_ifs with h
  · obtain ⟨g,rfl⟩ := h
    have he : {k : H | k • x = g • x} = (fun k : H => g⁻¹*k) ⁻¹' actionStabilizer (H := H) x := by
      ext k
      simp only [Set.mem_ofPred_eq,Set.mem_preimage,actionStabilizer,mul_smul]
      exact ⟨fun hk => by rw [hk,inv_smul_smul],fun hk => by simpa using congrArg (fun z => g • z) hk⟩
    rw [he]
    exact measure_preimage_mul μ g⁻¹ _
  · have he : {g : H | g • x = y} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro g hg
      exact h ⟨g,hg⟩
    simp only [he,measure_empty]

 

omit [MeasurableInv H] in
theorem orbit_map_measure (μ : Measure H) [μ.IsMulLeftInvariant]
    (hmeas : ∀ x : V, Measurable (fun g : H => g • x)) (x : V) :
    Measure.map (fun g : H => g • x) μ =
      Measure.sum (fun y : V => (if y ∈ actionOrbit (H := H) x then μ (actionStabilizer (H := H) x) else 0) • Measure.dirac y) := by
  classical
  apply Measure.ext_of_singleton
  intro y
  rw [Measure.map_apply (hmeas x) (measurableSet_singleton y),Measure.sum_apply _ (measurableSet_singleton y)]
  rw [tsum_eq_single y (fun z hz => by split_ifs <;> simp [Measure.smul_apply,Measure.dirac_apply',hz])]
  simp only [Measure.smul_apply,Measure.dirac_apply_of_mem (Set.mem_singleton y),smul_eq_mul,mul_one]
  exact orbit_fiber_measure μ hmeas x y

 

omit [MeasurableInv H] in
theorem integral_orbit_sum (μ : Measure H) [μ.IsMulLeftInvariant]
    (hmeas : ∀ x : V, Measurable (fun g : H => g • x)) (x : V)
    (hx : μ (actionStabilizer (H := H) x) ≠ ∞) (f : V → ℂ) :
    (∫ g : H, f (g • x) ∂μ) =
      (μ.real (actionStabilizer (H := H) x) : ℂ) *
        ∑' y : V, if y ∈ actionOrbit (H := H) x then f y else 0 := by
  classical
  rw [←integral_map_of_stronglyMeasurable (hmeas x) (measurable_of_countable f).stronglyMeasurable,
    orbit_map_measure μ hmeas x,integral_sum_dirac (fun y => by split_ifs <;> simp_all)]
  rw [←tsum_mul_left]
  apply tsum_congr
  intro y
  split_ifs <;> simp [Measure.real,Complex.real_smul]

 

theorem orbit_mass_balance (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (hmeas : ∀ x : V, Measurable (fun g : H => g • x)) (x y : V)
    (hx : μ (actionStabilizer (H := H) x) ≠ ∞) (hy : μ (actionStabilizer (H := H) y) ≠ ∞)
    (m : V → V → ℂ) (hinv : ∀ g : H, ∀ x y : V, m (g • x) (g • y) = m x y) :
    (μ.real (actionStabilizer (H := H) y) : ℂ) * (∑' z, if z ∈ actionOrbit (H := H) y then m x z else 0) =
      (μ.real (actionStabilizer (H := H) x) : ℂ) * (∑' z, if z ∈ actionOrbit (H := H) x then m z y else 0) := by
  rw [←integral_orbit_sum μ hmeas y hy (m x),←integral_orbit_sum μ hmeas x hx (fun z => m z y)]
  calc
    _ = ∫ g : H, m (g⁻¹ • x) y ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with g
      have h := hinv g⁻¹ x (g • y)
      simpa only [inv_smul_smul] using h.symm
    _ = _ := integral_inv_eq_self (fun g : H => m (g • x) y) μ

variable {ι : Type*} [Fintype ι]

 

noncomputable def inverseStabilizerWeight (μ : Measure H) (root : ι → V) (i : ι) : ℝ :=
  (μ.real (actionStabilizer (H := H) (root i)))⁻¹ /
    ∑ j, (μ.real (actionStabilizer (H := H) (root j)))⁻¹

omit [MeasurableMul₂ H] [MeasurableInv H] [Countable V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
theorem inverseStabilizerWeight_pos [Nonempty ι] (μ : Measure H) (root : ι → V)
    (hvol : ∀ i, 0 < μ.real (actionStabilizer (H := H) (root i))) (i : ι) :
    0 < inverseStabilizerWeight μ root i := by
  apply div_pos (inv_pos.mpr (hvol i))
  exact Finset.sum_pos (fun j _ => inv_pos.mpr (hvol j)) Finset.univ_nonempty

omit [MeasurableMul₂ H] [MeasurableInv H] [Countable V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
theorem inverseStabilizerWeight_sum [Nonempty ι] (μ : Measure H) (root : ι → V)
    (hvol : ∀ i, 0 < μ.real (actionStabilizer (H := H) (root i))) :
    ∑ i, inverseStabilizerWeight μ root i = 1 := by
  unfold inverseStabilizerWeight
  rw [←Finset.sum_div,div_self]
  exact ne_of_gt (Finset.sum_pos (fun j _ => inv_pos.mpr (hvol j)) Finset.univ_nonempty)

 

omit [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H] [Countable V]
  [MeasurableSpace V] [MeasurableSingletonClass V] in
theorem tsum_eq_sum_orbits (root : ι → V)
    (hcov : ∀ x, ∃ i, x ∈ actionOrbit (H := H) (root i))
    (hsep : ∀ i j, root j ∈ actionOrbit (H := H) (root i) → i = j)
    (f : V → ℂ) (hf : Summable f) :
    ∑' x, f x = ∑ i, ∑' x, if x ∈ actionOrbit (H := H) (root i) then f x else 0 := by
  have hi (i : ι) : Summable (fun x => if x ∈ actionOrbit (H := H) (root i) then f x else 0) := hf.indicator _
  rw [←Summable.tsum_finsetSum (s := Finset.univ) (fun i _ => hi i)]
  apply tsum_congr
  intro x
  obtain ⟨i,hi⟩ := hcov x
  symm
  rw [Finset.sum_eq_single i]
  · exact ite_eq_left hi
  · intro j _ hji
    have hj : x ∉ actionOrbit (H := H) (root j) := by
      intro hj
      apply hji
      apply hsep j i
      rw [←actionOrbit_eq_of_mem hj,actionOrbit_eq_of_mem hi]
      exact actionOrbit_self _
    exact ite_eq_right hj
  · simp

 

theorem rootTransport_of_invariant_measure [Nonempty ι]
    (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (hmeas : ∀ x : V, Measurable (fun g : H => g • x))
    (root : ι → V) (hvol : ∀ i, 0 < μ.real (actionStabilizer (H := H) (root i)))
    (hfinite : ∀ i, μ (actionStabilizer (H := H) (root i)) ≠ ∞)
    (hcov : ∀ x, ∃ i, x ∈ actionOrbit (H := H) (root i))
    (hsep : ∀ i j, root j ∈ actionOrbit (H := H) (root i) → i = j)
    (Γ : Set (V ≃ V)) (hΓ : ∀ g : H, MulAction.toPerm g ∈ Γ) :
    RootTransport root (inverseStabilizerWeight μ root) Γ := by
  intro m hinv hrow hcol
  have hm : ∀ g : H, ∀ x y : V, m (g • x) (g • y) = m x y := fun g => hinv _ (hΓ g)
  have hp (i j : ι) :
      (inverseStabilizerWeight μ root i : ℂ) * (∑' y, if y ∈ actionOrbit (H := H) (root j) then m (root i) y else 0) =
      (inverseStabilizerWeight μ root j : ℂ) * (∑' x, if x ∈ actionOrbit (H := H) (root i) then m x (root j) else 0) := by
    have hb := orbit_mass_balance μ hmeas (root i) (root j) (hfinite i) (hfinite j) m hm
    have hi : (μ.real (actionStabilizer (H := H) (root i)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hvol i).ne'
    have hj : (μ.real (actionStabilizer (H := H) (root j)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hvol j).ne'
    have hZ : ((∑ k, (μ.real (actionStabilizer (H := H) (root k)))⁻¹ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Finset.sum_pos (fun k _ => inv_pos.mpr (hvol k)) Finset.univ_nonempty))
    unfold inverseStabilizerWeight
    push_cast
    field_simp
    simpa only [mul_comm,mul_left_comm,mul_assoc] using congrArg (fun z : ℂ => z / ∑ k, (1 : ℂ) / (μ.real (actionStabilizer (H := H) (root k)) : ℂ)) hb
  conv_lhs => arg 2; ext i; rw [tsum_eq_sum_orbits root hcov hsep (m (root i)) (hrow (root i)),Finset.mul_sum]
  simp_rw [hp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [←Finset.mul_sum,←tsum_eq_sum_orbits root hcov hsep (fun x => m x (root j)) (hcol (root j))]

end HaarAction
end Percolation

end OAI
