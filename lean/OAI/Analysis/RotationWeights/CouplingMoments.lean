import OAI.Analysis.RotationWeights.DigitCouplings

namespace OAI

noncomputable section

namespace CircleCoupling

universe uD uA uι uΩ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
section

lemma sum_sq_le_card_mul {D : Type uD} [Fintype D] (f : D → ℝ) :
    (∑ d, f d)^2 ≤ (Fintype.card D : ℝ) * ∑ d, (f d)^2 := by
  simpa [mul_comm] using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset D) f (fun _ => (1 : ℝ))

lemma centered_density_squares {D : Type uD} [Fintype D] (g : D → ℝ) (M : ℝ)
    (hg : ∀ d, 0 ≤ g d) (hM : ∀ d, g d ≤ M)
    (hmean : ∑ d, g d = (Fintype.card D : ℝ)) :
    ∑ d, (g d - 1)^2 ≤ (Fintype.card D : ℝ) * M := by
  have hsq : ∑ d, (g d)^2 ≤ M * ∑ d, g d := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d _
    nlinarith [mul_le_mul_of_nonneg_right (hM d) (hg d)]
  have heq : ∑ d, (g d - 1)^2 = (∑ d, (g d)^2) - (Fintype.card D : ℝ) := by
    simp_rw [sub_sq]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,
      Finset.card_univ,nsmul_eq_mul,one_pow,mul_one]
    rw [← Finset.mul_sum, hmean]
    ring
  rw [heq]
  rw [hmean] at hsq
  have : (0 : ℝ) ≤ Fintype.card D := Nat.cast_nonneg _
  nlinarith

lemma mixture_density_squares {D : Type uD} {A : Type uA} [Fintype D] [Fintype A]
    (g : A → D → ℝ) (p M : A → ℝ)
    (hg : ∀ a d, 0 ≤ g a d) (hM : ∀ a d, g a d ≤ M a)
    (hmean : ∀ a, ∑ d, g a d = (Fintype.card D : ℝ)) :
    ∑ d, (1 + ∑ a, p a * (g a d - 1))^2 ≤
      (Fintype.card D : ℝ) * (1 + (Fintype.card A : ℝ) * ∑ a, (p a)^2 * M a) := by
  let v : D → ℝ := fun d => ∑ a, p a * (g a d - 1)
  have hvmean : ∑ d, v d = 0 := by
    simp only [v]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro a _
    rw [← Finset.mul_sum,Finset.sum_sub_distrib,hmean]
    simp
  have hv : ∑ d, (v d)^2 ≤ (Fintype.card D : ℝ) *
      ((Fintype.card A : ℝ) * ∑ a, (p a)^2 * M a) := by
    calc
      ∑ d, (v d)^2 ≤ ∑ d, (Fintype.card A : ℝ) * ∑ a, (p a * (g a d-1))^2 :=
        Finset.sum_le_sum (fun d _ => sum_sq_le_card_mul _)
      _ = (Fintype.card A : ℝ) * ∑ a, (p a)^2 * ∑ d, (g a d-1)^2 := by
        simp_rw [mul_pow]
        rw [← Finset.mul_sum,Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
      _ ≤ (Fintype.card A : ℝ) * ∑ a, (p a)^2 * ((Fintype.card D : ℝ) * M a) := by
        gcongr with a
        exact centered_density_squares (g a) (M a) (hg a) (hM a) (hmean a)
      _ = _ := by simp_rw [mul_left_comm ((p _)^2) (Fintype.card D : ℝ)]; rw [← Finset.mul_sum]; ring
  have heq : ∑ d, (1+v d)^2 = (Fintype.card D : ℝ) + ∑ d, (v d)^2 := by
    simp_rw [add_sq]
    simp only [Finset.sum_add_distrib,one_pow,Finset.sum_const,
      Finset.card_univ,nsmul_eq_mul,mul_one,← Finset.mul_sum,hvmean,mul_zero,add_zero]
  change ∑ d, (1+v d)^2 ≤ _
  rw [heq]
  nlinarith

lemma probability_sum_singleton_real {D : Type uD} [Fintype D] [MeasurableSpace D]
    [MeasurableSingletonClass D] (μ : Measure D) [IsProbabilityMeasure μ] :
    ∑ d, μ.real {d} = 1 := by
  simp

lemma uniform_l2_set_bound {D : Type uD} [Fintype D] [Nonempty D]
    [MeasurableSpace D] [MeasurableSingletonClass D]
    (μ ν : Measure D) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ d, μ.real {d} = (Fintype.card D : ℝ)⁻¹) {H : ℝ} (hH : 0 ≤ H)
    (hL2 : (Fintype.card D : ℝ) * ∑ d, (ν.real {d})^2 ≤ H^2)
    (A : Set D) : ν.real A ≤ H * Real.sqrt (μ.real A) := by
  classical
  let s := A.toFinite.toFinset
  have hs : (s : Set D) = A := by simp [s]
  have hνA : ν.real A = ∑ d ∈ s, ν.real {d} := by rw [← hs, sum_measureReal_singleton]
  have hμA : μ.real A = (s.card : ℝ) / (Fintype.card D : ℝ) := by
    rw [← hs, ← sum_measureReal_singleton]
    simp only [hμ,Finset.sum_const,nsmul_eq_mul,div_eq_mul_inv]
  have hc : (0 : ℝ) < Fintype.card D := Nat.cast_pos.mpr Fintype.card_pos
  have hsq : (ν.real A)^2 ≤ H^2 * μ.real A := by
    rw [hνA,hμA]
    have hh := Finset.sum_mul_sq_le_sq_mul_sq s (fun d => ν.real {d}) (fun _ => (1 : ℝ))
    simp only [mul_one,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hh
    have hsub : ∑ d ∈ s, (ν.real {d})^2 ≤ ∑ d, (ν.real {d})^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    have hcard : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
    have hbound := mul_le_mul_of_nonneg_right hsub hcard
    have hbound2 := mul_le_mul_of_nonneg_left ((le_div_iff₀ hc).mpr (by nlinarith :
      (∑ d, (ν.real {d})^2) * (Fintype.card D : ℝ) ≤ H^2)) hcard
    calc
      _ ≤ (∑ d, (ν.real {d})^2) * (s.card : ℝ) := hh.trans hbound
      _ ≤ (s.card : ℝ) * (H^2 / (Fintype.card D : ℝ)) := by simpa [mul_comm] using hbound2
      _ = _ := by ring
  apply (sq_le_sq₀ measureReal_nonneg (mul_nonneg hH (Real.sqrt_nonneg _))).mp
  simpa [mul_pow,Real.sq_sqrt measureReal_nonneg] using hsq

lemma pi_second_moment {ι : Type uι} [Fintype ι] [DecidableEq ι] {D : ι → Type uD}
    [∀ i, Fintype (D i)] [∀ i, MeasurableSpace (D i)]
    [∀ i, MeasurableSingletonClass (D i)] (μ : ∀ i, Measure (D i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    (Fintype.card (∀ i, D i) : ℝ) * ∑ d, ((Measure.pi μ).real {d})^2 =
      ∏ i, (Fintype.card (D i) : ℝ) * ∑ d, ((μ i).real {d})^2 := by
  classical
  simp only [Measure.real,Measure.pi_singleton,ENNReal.toReal_prod,← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun i (d : D i) => ((μ i) {d}).toReal^2),
    Fintype.card_pi,Nat.cast_prod,Finset.prod_mul_distrib]

lemma pi_uniform_singleton_real {ι : Type uι} [Fintype ι] [DecidableEq ι] {D : ι → Type uD}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)] [∀ i, MeasurableSpace (D i)]
    [∀ i, MeasurableSingletonClass (D i)] (d : ∀ i, D i) :
    (Measure.pi (fun i => (PMF.uniformOfFintype (D i)).toMeasure)).real {d} =
      (Fintype.card (∀ i, D i) : ℝ)⁻¹ := by
  classical
  simp [Measure.real,Measure.pi_singleton,ENNReal.toReal_prod,PMF.uniformOfFintype_apply,
    Fintype.card_pi,Finset.prod_inv_distrib]


lemma mixture_endpoint_second_moment {A : Type uA} {D : Type uD} [Fintype A] [Fintype D] [Nonempty D]
    [MeasurableSpace A] [MeasurableSpace D] [MeasurableSingletonClass D]
    (p : A → ℝ≥0∞) (μ₀ : Measure (D × D)) (μ : A → Measure (D × D))
    [IsProbabilityMeasure μ₀] [∀ a, IsProbabilityMeasure (μ a)]
    (hp : ∑ a, p a ≤ 1) (f : D × D → D) (hf : Measurable f)
    (hdiag : ∀ d, μ₀.real (f ⁻¹' {d}) = (Fintype.card D : ℝ)⁻¹)
    (M : A → ℝ) (hM : ∀ a d, (Fintype.card D : ℝ) * (μ a).real (f ⁻¹' {d}) ≤ M a) :
    (Fintype.card D : ℝ) * ∑ d,
      ((mixture p (1-∑ a, p a) μ₀ μ).real {ω | f ω.2 = d})^2 ≤
      1 + (Fintype.card A : ℝ) * ∑ a, (p a).toReal^2 * M a := by
  classical
  let L : ℝ := Fintype.card D
  have hL : 0 < L := Nat.cast_pos.mpr Fintype.card_pos
  have hpfin (a : A) : p a ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ a)).trans hp)
  have hsfin : (∑ a, p a) ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hp
  have hremfin : 1-∑ a, p a ≠ (∞ : ℝ≥0∞) := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hrem : (1-∑ a, p a).toReal = 1-∑ a, (p a).toReal := by
    rw [ENNReal.toReal_sub_of_le hp ENNReal.one_ne_top,ENNReal.toReal_one,
      ENNReal.toReal_sum (fun a _ => hpfin a)]
  let g : A → D → ℝ := fun a d => L * (μ a).real (f ⁻¹' {d})
  have hg : ∀ a d, 0 ≤ g a d := fun a d => mul_nonneg hL.le measureReal_nonneg
  have hgmean : ∀ a, ∑ d, g a d = L := by
    intro a
    rw [show (∑ d, g a d) = L * ∑ d, (μ a).real (f ⁻¹' {d}) by
      simp only [g,Finset.mul_sum]]
    rw [sum_measureReal_preimage_singleton Finset.univ (fun d _ => hf (measurableSet_singleton d))]
    simp
  have hden (d : D) : L * (mixture p (1-∑ a, p a) μ₀ μ).real {ω | f ω.2 = d} =
      1 + ∑ a, (p a).toReal * (g a d-1) := by
    rw [mixture_fiber_real p _ μ₀ μ hpfin hremfin f hf d,hdiag d,hrem]
    change L * ((1-∑ a, (p a).toReal)*L⁻¹ + ∑ a, (p a).toReal*(μ a).real (f ⁻¹' {d})) = _
    simp only [g,mul_sub,Finset.sum_sub_distrib,mul_one]
    rw [mul_add,← mul_assoc,mul_comm L (1-∑ a, (p a).toReal),mul_assoc,mul_inv_cancel₀ hL.ne',mul_one]
    rw [Finset.mul_sum]
    simp_rw [mul_left_comm L]
    ring
  have hh := mixture_density_squares g (fun a => (p a).toReal) M hg hM hgmean
  simp_rw [← hden,mul_pow] at hh
  rw [← Finset.mul_sum] at hh
  apply (mul_le_mul_iff_right₀ hL).mp
  nlinarith


def digitEndpoint {D : Type uD} (e : Bool) (z : D × D) : D := if e then z.2 else z.1
lemma digitEndpoint_measurable {D : Type uD} [MeasurableSpace D] (e : Bool) :
    Measurable (digitEndpoint (D := D) e) := by
  cases e
  · exact measurable_fst
  · exact measurable_snd

lemma diagonal_endpoint_real (l : ℕ) [NeZero l] (e : Bool) (d : Fin l) :
    (diagonal l).real (digitEndpoint e ⁻¹' {d}) = (l : ℝ)⁻¹ := by
  cases e
  · change ((diagonal l) (Prod.fst ⁻¹' {d})).toReal = _
    rw [diagonal_fiber_fst]; simp
  · change ((diagonal l) (Prod.snd ⁻¹' {d})).toReal = _
    rw [diagonal_fiber_snd]; simp

lemma rectangle_endpoint_density_bound (l a b : ℕ) (ha : a < l) (hp : 0 < a) (hb : b < l)
    (e : Bool) (M : ℝ) (hM : 0 ≤ M)
    (hA : (l : ℝ) * (a : ℝ)⁻¹ ≤ M) (hB : (l : ℝ) * ((l-b : ℕ) : ℝ)⁻¹ ≤ M)
    (d : Fin l) : (l : ℝ) * (rectangle l a b ha hp hb).real (digitEndpoint e ⁻¹' {d}) ≤ M := by
  cases e
  · change (l : ℝ) * (rectangle l a b ha hp hb).real (Prod.fst ⁻¹' {d}) ≤ M
    rw [rectangle_fst_real]
    split_ifs <;> simp_all
  · change (l : ℝ) * (rectangle l a b ha hp hb).real (Prod.snd ⁻¹' {d}) ≤ M
    rw [rectangle_snd_real]
    split_ifs <;> simp_all

lemma sixComponents_density_bound (l t u r : ℕ) [NeZero l]
    (ht : 0 < t ∧ t < l) (hu : 0 < u ∧ u < l) (hr : 0 < r ∧ r < l)
    (a b m : ℝ) (ha : 0 < a) (hb : 0 < b) (hm : 0 < m)
    (htlo : (l : ℝ)*a/3 ≤ (t : ℝ)) (hthi : (t : ℝ) ≤ (l : ℝ)/2)
    (hulo : (l : ℝ)*b/3 ≤ (u : ℝ)) (huhi : (u : ℝ) ≤ (l : ℝ)/2)
    (hrlo : (l : ℝ)/(2*m) ≤ (r : ℝ)) (_hrhi : (r : ℝ) ≤ (l : ℝ)/2)
    (e : Bool) : ∀ i d, (l : ℝ) * (components l t u r ht hu hr i).real
      (digitEndpoint e ⁻¹' {d}) ≤ (![3/a,3/a,3/b,3/b,2*m] : Fin 5 → ℝ) i := by
  have bound (n : ℕ) (hn : 0 < n) (w : ℝ) (hw : 0 < w) (hnw : (l : ℝ)*w/3 ≤ n) :
      (l : ℝ)*(n : ℝ)⁻¹ ≤ 3/w := by
    rw [← div_eq_mul_inv,div_le_div_iff₀ (by exact_mod_cast hn) hw]
    linarith
  have ht1 := bound t ht.1 a ha htlo
  have hu1 := bound u hu.1 b hb hulo
  have ht2 := bound (l-t) (by omega) a ha (by rw [Nat.cast_sub ht.2.le]; linarith)
  have hu2 := bound (l-u) (by omega) b hb (by rw [Nat.cast_sub hu.2.le]; linarith)
  have hr1 : (l : ℝ)*(r : ℝ)⁻¹ ≤ 2*m := by
    rw [← div_eq_mul_inv,div_le_iff₀ (by exact_mod_cast hr.1)]
    have hh := (div_le_iff₀ (by positivity : 0 < 2*m)).mp hrlo
    nlinarith
  intro i d
  fin_cases i
  all_goals dsimp [components]
  · exact rectangle_endpoint_density_bound l (l-t) (l-t) (by omega) (by omega) (by omega) e
      (3/a) (by positivity) ht2 (by simpa [Nat.sub_sub_self ht.2.le] using ht1) d
  · exact rectangle_endpoint_density_bound l t t ht.2 ht.1 ht.2 e (3/a) (by positivity) ht1 ht2 d
  · exact rectangle_endpoint_density_bound l (l-u) (l-u) (by omega) (by omega) (by omega) e
      (3/b) (by positivity) hu2 (by simpa [Nat.sub_sub_self hu.2.le] using hu1) d
  · exact rectangle_endpoint_density_bound l u u hu.2 hu.1 hu.2 e (3/b) (by positivity) hu1 hu2 d
  · exact rectangle_endpoint_density_bound l r (l-r) hr.2 hr.1 (by omega) e (2*m) (by positivity)
      hr1 (by simpa [Nat.sub_sub_self hr.2.le] using hr1) d

lemma sixLaw_second_moment (l t u r : ℕ) [NeZero l]
    (ht : 0 < t ∧ t < l) (hu : 0 < u ∧ u < l) (hr : 0 < r ∧ r < l)
    (a b m κ ρ σ τ I : ℝ) (ha : 0 < a) (hb : 0 < b) (hm : 0 < m)
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ)
    (htlo : (l : ℝ)*a/3 ≤ (t : ℝ)) (hthi : (t : ℝ) ≤ (l : ℝ)/2)
    (hulo : (l : ℝ)*b/3 ≤ (u : ℝ)) (huhi : (u : ℝ) ≤ (l : ℝ)/2)
    (hrlo : (l : ℝ)/(2*m) ≤ (r : ℝ)) (hrhi : (r : ℝ) ≤ (l : ℝ)/2)
    (hρsq : ρ^2 = κ^2*a/m) (hσsq : σ^2 = κ^2*b/m) (hτsq : τ^2 ≤ I/m^2)
    (hprob : 2*ENNReal.ofReal ρ+2*ENNReal.ofReal σ+ENNReal.ofReal τ ≤ 1)
    (e : Bool) :
    (l : ℝ) * ∑ d : Fin l,
      ((sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)).real
        {ω | digitEndpoint e ω.2 = d})^2 ≤ 1+(60*κ^2+10*I)/m := by
  have hh := mixture_endpoint_second_moment (sixWeights (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ))
    (diagonal l) (components l t u r ht hu hr) (by simpa [sum_sixWeights] using hprob)
    (digitEndpoint e) (digitEndpoint_measurable e) (by intro d; simpa using diagonal_endpoint_real l e d)
    (![3/a,3/a,3/b,3/b,2*m])
    (by simpa using sixComponents_density_bound l t u r ht hu hr a b m ha hb hm htlo hthi hulo huhi hrlo hrhi e)
  simp only [Fintype.card_fin,sum_sixWeights] at hh
  change (l : ℝ) * ∑ d : Fin l, _ ≤ _ at hh
  change (l : ℝ) * ∑ d : Fin l, _ ≤ _
  apply hh.trans
  simp only [sixWeights,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,add_zero,ENNReal.toReal_ofReal hρ,
    ENNReal.toReal_ofReal hσ,ENNReal.toReal_ofReal hτ]
  have heq : 1+(5 : ℝ)*(ρ^2*(3/a)+(ρ^2*(3/a)+(σ^2*(3/b)+(σ^2*(3/b)+τ^2*(2*m))))) =
      1+60*κ^2/m+10*m*τ^2 := by rw [hρsq,hσsq]; field_simp; ring
  norm_num only [Nat.cast_ofNat]
  rw [heq]
  have hτ' := mul_le_mul_of_nonneg_left hτsq (by positivity : 0 ≤ 10*m)
  have hid : 10*m*(I/m^2) = 10*I/m := by field_simp
  rw [hid] at hτ'
  calc
    _ ≤ 1+60*κ^2/m+10*I/m := by linarith
    _ = _ := by ring

end
open MeasureTheory Set
open scoped ENNReal
section

lemma fiber_failure_bound {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F S : Set Ω) (hS : MeasurableSet S)
    (c : ℝ) (_hc : 0 ≤ c) (hc' : c ≤ 1)
    (hhit : c * μ.real F ≤ μ.real (F ∩ S)) :
    μ (F ∩ Sᶜ) ≤ ENNReal.ofReal (1-c) * μ F := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hc')]
  change μ.real (F ∩ Sᶜ) ≤ (1-c) * μ.real F
  have hsum := measureReal_sdiff_add_inter (μ := μ) (s := F) hS
  rw [sdiff_eq] at hsum
  nlinarith

lemma fiber_failure_of_density_bounds {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F S : Set Ω) (hS : MeasurableSet S)
    (r B : ℝ) (hr : 0 ≤ r) (hB : 0 < B) (hrB : r ≤ B)
    (htotal : μ.real F ≤ B) (hhit : r ≤ μ.real (F ∩ S)) :
    μ (F ∩ Sᶜ) ≤ ENNReal.ofReal (1-r/B) * μ F := by
  apply fiber_failure_bound μ F S hS (r/B) (div_nonneg hr hB.le)
    ((div_le_one hB).mpr hrB)
  exact (mul_le_mul_of_nonneg_left htotal (div_nonneg hr hB.le)).trans
    (by simpa [div_mul_cancel₀ _ hB.ne'] using hhit)

lemma fiber_failure_tenth {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F S : Set Ω) (hS : MeasurableSet S)
    (ρ l : ℝ) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) (hl : 0 < l)
    (htotal : μ.real F ≤ 10/l) (hhit : ρ/l ≤ μ.real (F ∩ S)) :
    μ (F ∩ Sᶜ) ≤ ENNReal.ofReal (1-ρ/10) * μ F := by
  have h := fiber_failure_of_density_bounds μ F S hS (ρ/l) (10/l)
    (div_nonneg hρ hl.le) (div_pos (by norm_num) hl)
    (div_le_div_of_nonneg_right (by linarith : ρ ≤ 10) hl.le) htotal hhit
  simpa [div_div_div_cancel_right₀ hl.ne'] using h
end

lemma sixLaw_density_ten (l t u r : ℕ) [NeZero l]
    (ht : 0 < t ∧ t < l) (hu : 0 < u ∧ u < l) (hr : 0 < r ∧ r < l)
    (a b m κ ρ σ τ : ℝ) (ha : 0 < a) (hb : 0 < b) (hm : 0 < m)
    (hκ : κ ≤ 1/100) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ)
    (htlo : (l : ℝ)*a/3 ≤ (t : ℝ)) (hthi : (t : ℝ) ≤ (l : ℝ)/2)
    (hulo : (l : ℝ)*b/3 ≤ (u : ℝ)) (huhi : (u : ℝ) ≤ (l : ℝ)/2)
    (hrlo : (l : ℝ)/(2*m) ≤ (r : ℝ)) (hrhi : (r : ℝ) ≤ (l : ℝ)/2)
    (hρα : ρ/a ≤ κ) (hσb : σ/b ≤ κ) (hτm : τ ≤ 1/m)
    (hprob : 2*ENNReal.ofReal ρ+2*ENNReal.ofReal σ+ENNReal.ofReal τ ≤ 1)
    (e : Bool) (d : Fin l) :
    (sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)).real
      {ω | digitEndpoint e ω.2 = d} ≤ 10/l := by
  have hl : (0 : ℝ) < l := Nat.cast_pos.mpr (NeZero.pos l)
  let M : Fin 5 → ℝ := ![3/a,3/a,3/b,3/b,2*m]
  have hM := sixComponents_density_bound l t u r ht hu hr a b m ha hb hm
    htlo hthi hulo huhi hrlo hrhi e
  have hh := sixLaw_fiber_real_le l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ)
    (ENNReal.ofReal τ) hprob (digitEndpoint e) (digitEndpoint_measurable e) d
    (diagonal_endpoint_real l e d) (fun i => M i/l)
    (fun i => by apply (le_div_iff₀ hl).mpr; simpa [mul_comm,M] using hM i d)
  apply hh.trans
  simp only [M,sixWeights,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,add_zero,ENNReal.toReal_ofReal hρ,
    ENNReal.toReal_ofReal hσ,ENNReal.toReal_ofReal hτ]
  have hτ' : τ*m ≤ 1 := by have := (le_div_iff₀ hm).mp hτm; nlinarith
  have hsum : 1 + 6*(ρ/a)+6*(σ/b)+2*(τ*m) ≤ 10 := by linarith
  calc
    _ = (1+6*(ρ/a)+6*(σ/b)+2*(τ*m))/l := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hsum hl.le

lemma sixLaw_top_t_failure (l t u r : ℕ) [NeZero l]
    (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l) (hr : 0<r ∧ r<l)
    (ρ σ τ : ℝ) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1)
    (hp : 2*ENNReal.ofReal ρ+2*ENNReal.ofReal σ+ENNReal.ofReal τ ≤ 1)
    (d : Fin l) (hd : d.val < l-t)
    (hbound : (sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)).real
      {ω | ω.2.1 = d} ≤ 10/l) :
    sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)
      ({ω | ω.2.1=d} ∩ {ω | ω.1=some (0 : Fin 5)}ᶜ) ≤ ENNReal.ofReal (1-ρ/10) *
    sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ) {ω | ω.2.1=d} := by
  let μ := sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)
  let : IsProbabilityMeasure μ := sixLaw_probability l t u r ht hu hr _ _ _ hp
  apply fiber_failure_tenth μ _ _ (by measurability) ρ l hρ hρ' (by exact_mod_cast NeZero.pos l) hbound
  change ρ/(l : ℝ) ≤ (μ {ω | ω.2.1=d ∧ ω.1=some (0 : Fin 5)}).toReal
  rw [show μ {ω | ω.2.1=d ∧ ω.1=some (0 : Fin 5)} =
    ENNReal.ofReal ρ * ((l-t : ℕ) : ℝ≥0∞)⁻¹ from sixLaw_top_t l t u r ht hu hr _ _ _ d hd]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hρ,ENNReal.toReal_inv,ENNReal.toReal_natCast]
  rw [← div_eq_mul_inv]
  apply div_le_div_of_nonneg_left hρ (by exact_mod_cast Nat.sub_pos_of_lt ht.2)
  exact_mod_cast Nat.sub_le l t

lemma sixLaw_bottom_t_failure (l t u r : ℕ) [NeZero l]
    (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l) (hr : 0<r ∧ r<l)
    (ρ σ τ : ℝ) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1)
    (hp : 2*ENNReal.ofReal ρ+2*ENNReal.ofReal σ+ENNReal.ofReal τ ≤ 1)
    (d : Fin l) (hd : t ≤ d.val)
    (hbound : (sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)).real
      {ω | ω.2.2 = d} ≤ 10/l) :
    sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)
      ({ω | ω.2.2=d} ∩ {ω | ω.1=some (1 : Fin 5)}ᶜ) ≤ ENNReal.ofReal (1-ρ/10) *
    sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ) {ω | ω.2.2=d} := by
  let μ := sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)
  let : IsProbabilityMeasure μ := sixLaw_probability l t u r ht hu hr _ _ _ hp
  apply fiber_failure_tenth μ _ _ (by measurability) ρ l hρ hρ' (by exact_mod_cast NeZero.pos l) hbound
  change ρ/(l : ℝ) ≤ (μ {ω | ω.2.2=d ∧ ω.1=some (1 : Fin 5)}).toReal
  rw [show μ {ω | ω.2.2=d ∧ ω.1=some (1 : Fin 5)} =
    ENNReal.ofReal ρ * ((l-t : ℕ) : ℝ≥0∞)⁻¹ from sixLaw_bottom_t l t u r ht hu hr _ _ _ d hd]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hρ,ENNReal.toReal_inv,ENNReal.toReal_natCast]
  rw [← div_eq_mul_inv]
  apply div_le_div_of_nonneg_left hρ (by exact_mod_cast Nat.sub_pos_of_lt ht.2)
  exact_mod_cast Nat.sub_le l t

lemma sixLaw_top_u_failure (l t u r : ℕ) [NeZero l]
    (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l) (hr : 0<r ∧ r<l)
    (ρ σ τ : ℝ) (hσ : 0 ≤ σ) (hσ' : σ ≤ 1)
    (hp : 2*ENNReal.ofReal ρ+2*ENNReal.ofReal σ+ENNReal.ofReal τ ≤ 1)
    (d : Fin l) (hd : d.val < l-u)
    (hbound : (sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)).real
      {ω | ω.2.1 = d} ≤ 10/l) :
    sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)
      ({ω | ω.2.1=d} ∩ {ω | ω.1=some (2 : Fin 5)}ᶜ) ≤ ENNReal.ofReal (1-σ/10) *
    sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ) {ω | ω.2.1=d} := by
  let μ := sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)
  let : IsProbabilityMeasure μ := sixLaw_probability l t u r ht hu hr _ _ _ hp
  apply fiber_failure_tenth μ _ _ (by measurability) σ l hσ hσ' (by exact_mod_cast NeZero.pos l) hbound
  change σ/(l : ℝ) ≤ (μ {ω | ω.2.1=d ∧ ω.1=some (2 : Fin 5)}).toReal
  rw [show μ {ω | ω.2.1=d ∧ ω.1=some (2 : Fin 5)} =
    ENNReal.ofReal σ * ((l-u : ℕ) : ℝ≥0∞)⁻¹ from sixLaw_top_u l t u r ht hu hr _ _ _ d hd]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hσ,ENNReal.toReal_inv,ENNReal.toReal_natCast]
  rw [← div_eq_mul_inv]
  apply div_le_div_of_nonneg_left hσ (by exact_mod_cast Nat.sub_pos_of_lt hu.2)
  exact_mod_cast Nat.sub_le l u

lemma sixLaw_bottom_u_failure (l t u r : ℕ) [NeZero l]
    (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l) (hr : 0<r ∧ r<l)
    (ρ σ τ : ℝ) (hσ : 0 ≤ σ) (hσ' : σ ≤ 1)
    (hp : 2*ENNReal.ofReal ρ+2*ENNReal.ofReal σ+ENNReal.ofReal τ ≤ 1)
    (d : Fin l) (hd : u ≤ d.val)
    (hbound : (sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)).real
      {ω | ω.2.2 = d} ≤ 10/l) :
    sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)
      ({ω | ω.2.2=d} ∩ {ω | ω.1=some (3 : Fin 5)}ᶜ) ≤ ENNReal.ofReal (1-σ/10) *
    sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ) {ω | ω.2.2=d} := by
  let μ := sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)
  let : IsProbabilityMeasure μ := sixLaw_probability l t u r ht hu hr _ _ _ hp
  apply fiber_failure_tenth μ _ _ (by measurability) σ l hσ hσ' (by exact_mod_cast NeZero.pos l) hbound
  change σ/(l : ℝ) ≤ (μ {ω | ω.2.2=d ∧ ω.1=some (3 : Fin 5)}).toReal
  rw [show μ {ω | ω.2.2=d ∧ ω.1=some (3 : Fin 5)} =
    ENNReal.ofReal σ * ((l-u : ℕ) : ℝ≥0∞)⁻¹ from sixLaw_bottom_u l t u r ht hu hr _ _ _ d hd]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hσ,ENNReal.toReal_inv,ENNReal.toReal_natCast]
  rw [← div_eq_mul_inv]
  apply div_le_div_of_nonneg_left hσ (by exact_mod_cast Nat.sub_pos_of_lt hu.2)
  exact_mod_cast Nat.sub_le l u



end CircleCoupling

end

end OAI
