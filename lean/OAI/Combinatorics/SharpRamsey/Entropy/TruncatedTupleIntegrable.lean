import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.ComponentLabelWitness

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.HighMoment
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open Classical
variable {D H : Type} [Fintype D] [DecidableEq D] [Fintype H] [DecidableEq H]
variable (R : ℕ) (s : H → Finset D) (b : ℝ) (own : H → Fin R → Bool)
omit [Fintype H] [DecidableEq H] [DecidableEq D] in
lemma truncated_tuple_integrable (rate : D → ℝ≥0) (J : ℕ) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    {V : Type} [Fintype V] (f : V → H) :
    Integrable (fun ω => allTrunc R J ω *
      ∏ v, scoreTerm (s (f v)) b (own (f v)) (fun r d => ω (r,d)))
      (batchMeasure (fun i : Fin R × D => rate i.2)) := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun ω => by
    simpa only [Real.norm_eq_abs] using truncated_tuple_abs_le R s b own J hb f ω)

omit [DecidableEq H] in

theorem integral_truncated_score_pow (weight rate : D → ℝ≥0) (t : ℝ) (J p : ℕ)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    (∫ ω, allTrunc R J ω *
      (∑ h : H, scoreTerm (s h) b (own h) (fun r d => ω (r,d))) ^ p
      ∂batchMeasure (fun i : Fin R × D => rate i.2)) =
        ∑ f : Fin p → H, strongSplit R (s ∘ f) b (own ∘ f) weight rate t J := by
  have hp (ω : Fin R × D → ℕ) :
      (∑ h : H, scoreTerm (s h) b (own h) (fun r d => ω (r,d))) ^ p =
        ∑ f : Fin p → H, ∏ v, scoreTerm (s (f v)) b (own (f v)) (fun r d => ω (r,d)) := by
    simpa using Finset.sum_pow' Finset.univ
      (fun h : H => scoreTerm (s h) b (own h) (fun r d => ω (r,d))) p
  simp_rw [hp, Finset.mul_sum]
  rw [integral_finsetSum _ (fun f _ => truncated_tuple_integrable R s b own rate J hb f)]
  apply Finset.sum_congr rfl
  intro f _
  exact strong_tuple_integral_split R (s ∘ f) b (own ∘ f) weight rate t J hb

variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def absSplit (f : V → H) (weight rate : D → ℝ≥0) (t : ℝ) (J : ℕ) : ℝ := by
  let sf := s ∘ f
  let G := strongGraph weight sf t
  let label := componentLabel weight sf t
  exact ∫ z, blockTrunc label R J none z * ∏ c : G.ConnectedComponent,
    |∫ x, componentFactor label R G.connectedComponentMk sf b (own ∘ f) J c z x
      ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2)|
      ∂batchMeasure (fun i : Block label R none => rate i.1.2)
omit [DecidableEq V] in
omit [DecidableEq D] in

lemma integral_abs_component_le_one {C : Type} [Fintype C] [DecidableEq C]
    (label : D → Option C) (col : V → C) (sf : V → Finset D)
    (of : V → Fin R → Bool) (rate : D → ℝ≥0) (J : ℕ)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (c : C) (z : Block label R none → ℕ) :
    |∫ x, componentFactor label R col sf b of J c z x
      ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2)| ≤ 1 := by
  have hi : Integrable (fun x => |componentFactor label R col sf b of J c z x|)
      (batchMeasure (fun i : Block label R (some c) => rate i.1.2)) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs, abs_abs] using
        componentFactor_bound label R col sf b of J hb c z x)
  calc
    _ ≤ ∫ x, |componentFactor label R col sf b of J c z x|
        ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2) := abs_integral_le_integral_abs
    _ ≤ ∫ _, (1 : ℝ) ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2) :=
      integral_mono hi (integrable_const _) (componentFactor_bound label R col sf b of J hb c z)
    _ = 1 := by simp

omit [Fintype H] [DecidableEq H] in
lemma absSplit_nonneg (f : V → H) (weight rate : D → ℝ≥0) (t : ℝ) (J : ℕ) :
    0 ≤ absSplit R s b own f weight rate t J := by
  unfold absSplit
  apply integral_nonneg
  intro z
  exact mul_nonneg (blockTrunc_range _ R J none z).1 (Finset.prod_nonneg (fun _ _ => abs_nonneg _))

omit [Fintype H] [DecidableEq H] in
lemma strongSplit_abs_le (f : V → H) (weight rate : D → ℝ≥0) (t : ℝ) (J : ℕ)
    (_hb : b ∈ Set.Icc (0 : ℝ) 1) :
    |strongSplit R (s ∘ f) b (own ∘ f) weight rate t J| ≤
      absSplit R s b own f weight rate t J := by
  unfold strongSplit absSplit
  apply (abs_integral_le_integral_abs).trans_eq
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  dsimp only
  rw [abs_mul, abs_of_nonneg (blockTrunc_range _ R J none z).1, Finset.abs_prod]

omit [DecidableEq H] in

theorem truncated_moment_le_tuple_sum (weight rate : D → ℝ≥0) (t : ℝ) (J p : ℕ)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    (∫ ω, allTrunc R J ω *
      (∑ h : H, scoreTerm (s h) b (own h) (fun r d => ω (r,d))) ^ p
      ∂batchMeasure (fun i : Fin R × D => rate i.2)) ≤
        ∑ f : Fin p → H, absSplit R s b own f weight rate t J := by
  rw [integral_truncated_score_pow R s b own weight rate t J p hb]
  apply Finset.sum_le_sum
  intro f _
  exact (le_abs_self _).trans (strongSplit_abs_le R s b own f weight rate t J hb)

theorem truncated_moment_le_representative_sum (weight rate : D → ℝ≥0) (t : ℝ) (J p : ℕ)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    (∫ ω, allTrunc R J ω *
      (∑ h : H, scoreTerm (s h) b (own h) (fun r d => ω (r,d))) ^ p
      ∂batchMeasure (fun i : Fin R × D => rate i.2)) ≤
        ∑ r : TupleMultiplicity.RepresentativeMap (Fin p),
          ∑ h : TupleMultiplicity.Representatives r ↪ H,
            absSplit R s b own (TupleMultiplicity.decode r h) weight rate t J := by
  apply (truncated_moment_le_tuple_sum R s b own weight rate t J p hb).trans
  convert TupleMultiplicity.sum_tuples_le_representative_assignments (V := Fin p) (H := H) _
    (fun f : Fin p → H => absSplit_nonneg R s b own f weight rate t J) using 1
  apply Finset.sum_congr (by ext; simp)
  intro representative _
  rfl

end SharpRamseyFive.HighMoment

namespace SharpRamseyFive.Designations
open MeasureTheory
open scoped BigOperators
open Classical
variable {C Ω : Type*} [Fintype C] [DecidableEq C]

noncomputable def badIndicator (bad : C → Ω → Prop) (c : C) (z : Ω) : ℝ :=
  if bad c z then 1 else 0

omit [Fintype C] [DecidableEq C] in
lemma badIndicator_range (bad : C → Ω → Prop) (c : C) (z : Ω) :
    badIndicator bad c z ∈ Set.Icc (0 : ℝ) 1 := by
  unfold badIndicator
  split_ifs <;> constructor <;> norm_num

lemma product_expansion (S : Finset C) (A N : ℝ) (w : C → ℝ)
    (bad : C → Ω → Prop) (T : Ω → ℝ) (z : Ω) :
    T z * ∏ c : C, (if c ∈ S then A * (w c + badIndicator bad c z) else N) =
      (A ^ S.card * N ^ (Fintype.card C - S.card)) *
        ∑ U ∈ S.powerset, (∏ c ∈ S \ U, w c) * (T z * ∏ c ∈ U, badIndicator bad c z) := by
  have hf : Finset.univ.filter (fun c : C => c ∈ S) = S := by ext; simp
  have hg : Finset.univ.filter (fun c : C => c ∉ S) = Finset.univ \ S := by ext; simp
  rw [Finset.prod_ite, hf, hg, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_const, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  have ha : (∏ c ∈ S, (w c + badIndicator bad c z)) =
      ∑ U ∈ S.powerset, (∏ c ∈ U, badIndicator bad c z) * ∏ c ∈ S \ U, w c := by
    rw [← Finset.prod_add]
    apply Finset.prod_congr rfl
    intro c _
    exact add_comm _ _
  rw [ha, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U _
  ring

variable [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]

noncomputable def badMass (T : Ω → ℝ) (bad : C → Ω → Prop) (U : Finset C) : ℝ :=
  ∫ z, T z * ∏ c ∈ U, badIndicator bad c z ∂μ

omit [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω] in
omit [Fintype C] [DecidableEq C] in
lemma badTerm_range (T : Ω → ℝ) (hT : ∀ z, T z ∈ Set.Icc (0 : ℝ) 1)
    (bad : C → Ω → Prop) (U : Finset C) (z : Ω) :
    T z * ∏ c ∈ U, badIndicator bad c z ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact mul_nonneg (hT z).1 (Finset.prod_nonneg (fun c _ => (badIndicator_range bad c z).1))
  · exact (mul_le_of_le_one_left
      (Finset.prod_nonneg (fun component _ => (badIndicator_range bad component z).1))
      (hT z).2).trans
      (Finset.prod_le_one₀ (fun component _ => (badIndicator_range bad component z).1)
        (fun component _ => (badIndicator_range bad component z).2))
omit [Fintype C] [DecidableEq C] in

lemma badTerm_integrable (T : Ω → ℝ) (hT : ∀ z, T z ∈ Set.Icc (0 : ℝ) 1)
    (bad : C → Ω → Prop) (U : Finset C) :
    Integrable (fun z => T z * ∏ c ∈ U, badIndicator bad c z) μ := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (badTerm_range T hT bad U z).1]
    exact (badTerm_range T hT bad U z).2)

omit [IsProbabilityMeasure μ] in
omit [Countable Ω] [MeasurableSingletonClass Ω] in
omit [Fintype C] [DecidableEq C] in
lemma badMass_nonneg (T : Ω → ℝ) (hT : ∀ z, T z ∈ Set.Icc (0 : ℝ) 1)
    (bad : C → Ω → Prop) (U : Finset C) : 0 ≤ badMass μ T bad U :=
  integral_nonneg (fun z => (badTerm_range T hT bad U z).1)

lemma majorant_integrable (S : Finset C) (A N : ℝ) (w : C → ℝ)
    (bad : C → Ω → Prop) (T : Ω → ℝ) (hT : ∀ z, T z ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun z => T z * ∏ c : C,
      if c ∈ S then A * (w c + badIndicator bad c z) else N) μ := by
  simp_rw [product_expansion]
  exact (integrable_finsetSum _ (fun U _ =>
    (badTerm_integrable μ T hT bad U).const_mul (∏ c ∈ S \ U, w c))).const_mul _

lemma integral_expansion (S : Finset C) (A N : ℝ) (w : C → ℝ)
    (bad : C → Ω → Prop) (T : Ω → ℝ) (hT : ∀ z, T z ∈ Set.Icc (0 : ℝ) 1) :
    (∫ z, T z * ∏ c : C,
      if c ∈ S then A * (w c + badIndicator bad c z) else N ∂μ) =
      (A ^ S.card * N ^ (Fintype.card C - S.card)) *
        ∑ U ∈ S.powerset, (∏ c ∈ S \ U, w c) * badMass μ T bad U := by
  simp_rw [product_expansion]
  rw [integral_const_mul, integral_finsetSum _ (fun U _ =>
    (badTerm_integrable μ T hT bad U).const_mul (∏ c ∈ S \ U, w c))]
  simp_rw [integral_const_mul]
  rfl

theorem integral_product_le (S : Finset C) (A N : ℝ) (w : C → ℝ)
    (bad : C → Ω → Prop) (T : Ω → ℝ) (hT : ∀ z, T z ∈ Set.Icc (0 : ℝ) 1)
    (F : C → Ω → ℝ) (hF : ∀ c z, F c z ∈ Set.Icc (0 : ℝ) 1)
    (hs : ∀ c ∈ S, ∀ z, F c z ≤ A * (w c + badIndicator bad c z))
    (hn : ∀ c ∉ S, ∀ z, F c z ≤ N) :
    (∫ z, T z * ∏ c, F c z ∂μ) ≤
      (A ^ S.card * N ^ (Fintype.card C - S.card)) *
        ∑ U ∈ S.powerset, (∏ c ∈ S \ U, w c) * badMass μ T bad U := by
  rw [← integral_expansion μ S A N w bad T hT]
  have hi : Integrable (fun z => T z * ∏ c, F c z) μ := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hT z).1
      (Finset.prod_nonneg (fun c _ => (hF c z).1)))]
    exact (mul_le_of_le_one_left
      (Finset.prod_nonneg (fun component _ => (hF component z).1)) (hT z).2).trans
      (Finset.prod_le_one₀ (fun component _ => (hF component z).1)
        (fun component _ => (hF component z).2))
  apply integral_mono hi (majorant_integrable μ S A N w bad T hT)
  intro z
  apply mul_le_mul_of_nonneg_left _ (hT z).1
  apply Finset.prod_le_prod₀ (fun component _ => (hF component z).1)
  intro c _
  split_ifs with hc
  · exact hs c hc z
  · exact hn c hc z

end SharpRamseyFive.Designations

namespace SharpRamseyFive.AmbientDesignations
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations
open Classical
variable {D V : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
variable (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ)

abbrev Components := (strongGraph weight s t).ConnectedComponent
noncomputable def vertex (c : Components weight s t) : V := c.out
omit [Fintype D] [Fintype V] [DecidableEq V] in
lemma vertex_color (c : Components weight s t) :
    (strongGraph weight s t).connectedComponentMk (vertex weight s t c) = c :=
  c.out_eq

noncomputable def simpleSet : Finset (Components weight s t) :=
  Finset.univ.filter (fun c => ∀ v, (strongGraph weight s t).connectedComponentMk v = c →
    v = vertex weight s t c)

noncomputable def alpha (v : V) : ℝ := mass weight (externalPart weight s t v)
noncomputable def delta (base : ℝ) (v : V) : ℝ := mass weight (s v) - base

omit [Fintype V] [DecidableEq V] in
omit [Fintype D] in
lemma alpha_nonneg (v : V) : 0 ≤ alpha weight s t v := mass_nonneg weight _
omit [Fintype D] in

lemma source_alpha_le {p : ℕ} (hp : 0 < p) (hc : Fintype.card V ≤ p) (v : V) :
    alpha weight s (1 / (100 * p)) v ≤ (1 / 100 : ℝ) := by
  have hl := external_mass_le weight s (show (0 : ℝ) ≤ 1 / (100 * p : ℝ) by positivity) v
  have hcr : ((Fintype.card V - 1 : ℕ) : ℝ) ≤ p := by
    exact_mod_cast (Nat.sub_le (Fintype.card V) 1).trans hc
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have he : (p : ℝ) * (1 / (100 * p : ℝ)) = 1 / 100 := by field_simp
  exact hl.trans ((mul_le_mul_of_nonneg_right hcr (by positivity)).trans_eq he)
omit [Fintype D] [Fintype V] [DecidableEq V] in

lemma internal_mass_eq (base : ℝ) (v : V) :
    mass weight (internalPart weight s t v) =
      base + delta weight s base v - alpha weight s t v := by
  have he := internal_external_mass weight s t v
  dsimp [delta, alpha]
  linarith
omit [Fintype D] in

lemma source_local_data {p : ℕ} (hp : 0 < p) (hc : Fintype.card V ≤ p)
    (base : ℝ) (hlower : ∀ v, (3 / 4 : ℝ) ≤ mass weight (s v))
    (hdelta : ∀ v, |delta weight s base v| ≤ (17 / 100 : ℝ)) (v : V) :
    (37 / 50 : ℝ) ≤ base + delta weight s base v - alpha weight s (1 / (100 * p)) v ∧
      |delta weight s base v| + alpha weight s (1 / (100 * p)) v ≤ 1 := by
  constructor
  · rw [← internal_mass_eq]
    exact source_internal_mass_lower weight s hp hc hlower v
  · have ha := source_alpha_le weight s hp hc v
    have hd := hdelta v
    linarith

variable (R J K : ℕ) (L : ℝ≥0) (base : ℝ) (own : V → Fin R → Bool)

noncomputable def extraWeight (c : Components weight s t) : ℝ :=
  |delta weight s base (vertex weight s t c)| ^ (R / 2) +
    alpha weight s t (vertex weight s t c) ^ K +
    (if R < J then 0 else
      ∑ d ∈ inside (componentLabel weight s t) c (s (vertex weight s t c)),
        ((R : ℝ) * ((L * weight d : ℝ≥0) : ℝ)) ^ J)

noncomputable def isBad (c : Components weight s t)
    (z : Block (componentLabel weight s t) R none → ℕ) : Prop :=
  BAD (touched (componentLabel weight s t) R c (s (vertex weight s t c)) z)

noncomputable def componentAbs (c : Components weight s t)
    (z : Block (componentLabel weight s t) R none → ℕ) : ℝ :=
  |∫ x, componentFactor (componentLabel weight s t) R
      (strongGraph weight s t).connectedComponentMk s (Real.exp (-(L : ℝ) * base)) own J c z x
    ∂batchMeasure (fun i : Block (componentLabel weight s t) R (some c) => L * weight i.1.2)|
omit [DecidableEq V] in

lemma scaled_internal (c : Components weight s t) :
    mass (fun d : IntDir (componentLabel weight s t) c => L * weight d)
      (inside (componentLabel weight s t) c (s (vertex weight s t c))) =
    (L : ℝ) * (base + delta weight s base (vertex weight s t c) -
      alpha weight s t (vertex weight s t c)) := by
  have he := mass_inside_eq weight (fun d => L * weight d) s t (vertex weight s t c)
  rw [vertex_color] at he
  rw [he, mass_scaled, internal_mass_eq weight s t base]

lemma componentAbs_range (hbase : (23 / 25 : ℝ) ≤ base)
    (c : Components weight s t) (z : Block (componentLabel weight s t) R none → ℕ) :
    componentAbs weight s t R J L base own c z ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact abs_nonneg _
  · change |∫ x, componentFactor (componentLabel weight s t) R
      (strongGraph weight s t).connectedComponentMk s (Real.exp (-(L : ℝ) * base)) own J c z x
      ∂batchMeasure (fun i : Block (componentLabel weight s t) R (some c) => L * weight i.1.2)| ≤ 1
    apply SharpRamseyFive.HighMoment.integral_abs_component_le_one R
      (Real.exp (-(L : ℝ) * base)) (componentLabel weight s t)
      (strongGraph weight s t).connectedComponentMk s own (fun d => L * weight d) J
    refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
    have hb : 0 ≤ base := by linarith
    simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg L.coe_nonneg hb)

lemma simple_bound {p : ℕ} (hp : 0 < p) (hc : Fintype.card V ≤ p)
    (hL : 10000 ≤ (L : ℝ)) (hbase : (23 / 25 : ℝ) ≤ base)
    (hlower : ∀ v, (3 / 4 : ℝ) ≤ mass weight (s v))
    (hdelta : ∀ v, |delta weight s base v| ≤ (17 / 100 : ℝ)) (hK : K ≤ R / 2)
    (c : Components weight s (1 / (100 * p)))
    (hs : c ∈ simpleSet weight s (1 / (100 * p)))
    (z : Block (componentLabel weight s (1 / (100 * p))) R none → ℕ) :
    componentAbs weight s (1 / (100 * p)) R J L base own c z ≤
      Real.exp (-(17 / 25 : ℝ) * ((L : ℝ) * R)) *
        (extraWeight weight s (1 / (100 * p)) R J K L base c +
          badIndicator (isBad weight s (1 / (100 * p)) R) c z) := by
  let v := vertex weight s (1 / (100 * p)) c
  have hv : (strongGraph weight s (1 / (100 * p))).connectedComponentMk v = c :=
    vertex_color weight s (1 / (100 * p)) c
  have hs' : ∀ u, (strongGraph weight s (1 / (100 * p))).connectedComponentMk u = c → u = v :=
    (Finset.mem_filter.mp hs).2
  have hi := simple_inside_univ s weight (1 / (100 * p)) v (by
    intro u hu
    exact hs' u (hu.trans hv))
  rw [hv] at hi
  have hm := source_local_data weight s hp hc base hlower hdelta v
  exact simple_component_designations (componentLabel weight s (1 / (100 * p))) R
    (strongGraph weight s (1 / (100 * p))).connectedComponentMk s own (fun d => L * weight d)
    J c ⟨v,hv⟩ hs' (fun d hd => by
      simpa only [hv] using direction_internal_or_external weight s (1 / (100 * p)) hd)
    hi z hL (scaled_internal weight s (1 / (100 * p)) L base c)
    hm.1 (by linarith) (alpha_nonneg weight s _ v) hm.2 hK

lemma nonsimple_bound {p : ℕ} (hp : 0 < p) (hc : Fintype.card V ≤ p)
    (hL : 10000 ≤ (L : ℝ)) (hbase : (23 / 25 : ℝ) ≤ base)
    (hlower : ∀ v, (3 / 4 : ℝ) ≤ mass weight (s v))
    (c : Components weight s (1 / (100 * p)))
    (z : Block (componentLabel weight s (1 / (100 * p))) R none → ℕ) :
    componentAbs weight s (1 / (100 * p)) R J L base own c z ≤
      Real.exp (-(7 / 10 : ℝ) * ((L : ℝ) * R)) := by
  let v := vertex weight s (1 / (100 * p)) c
  have hv : (strongGraph weight s (1 / (100 * p))).connectedComponentMk v = c :=
    vertex_color weight s (1 / (100 * p)) c
  change |∫ x, componentFactor (componentLabel weight s (1 / (100 * p))) R
    (strongGraph weight s (1 / (100 * p))).connectedComponentMk s
    (Real.exp (-(L : ℝ) * base)) own J c z x
    ∂batchMeasure (fun i : Block (componentLabel weight s (1 / (100 * p))) R (some c) =>
      L * weight i.1.2)| ≤ _
  apply abs_integral_le_integral_abs.trans
  apply nonsimple_component_attenuation (componentLabel weight s (1 / (100 * p))) R
    (strongGraph weight s (1 / (100 * p))).connectedComponentMk s own (fun d => L * weight d)
    J c ⟨v,hv⟩ z (fun d hd => by
      simpa only [hv] using direction_internal_or_external weight s (1 / (100 * p)) hd)
    hL (scaled_internal weight s (1 / (100 * p)) L base c) _ (by linarith)
  rw [← internal_mass_eq]
  exact source_internal_mass_lower weight s hp hc hlower v

noncomputable def designatedBound : ℝ :=
  let S := simpleSet weight s t
  (Real.exp (-(17 / 25 : ℝ) * ((L : ℝ) * R)) ^ S.card *
    Real.exp (-(7 / 10 : ℝ) * ((L : ℝ) * R)) ^
      (Fintype.card (Components weight s t) - S.card)) *
    ∑ U ∈ S.powerset, (∏ c ∈ S \ U, extraWeight weight s t R J K L base c) *
      badMass (batchMeasure (fun i : Block (componentLabel weight s t) R none => L * weight i.1.2))
        (blockTrunc (componentLabel weight s t) R J none) (isBad weight s t R) U
omit [DecidableEq V] in

lemma extraWeight_nonneg (c : Components weight s t) :
    0 ≤ extraWeight weight s t R J K L base c := by
  unfold extraWeight
  apply add_nonneg (add_nonneg (by positivity) (pow_nonneg (alpha_nonneg weight s t _) _))
  split_ifs <;> positivity

lemma designatedBound_nonneg : 0 ≤ designatedBound weight s t R J K L base := by
  unfold designatedBound
  apply mul_nonneg (mul_nonneg (by positivity) (by positivity))
  apply Finset.sum_nonneg
  intro U _
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun c _ => extraWeight_nonneg weight s t R J K L base c)
  · exact badMass_nonneg _ _ (blockTrunc_range _ R J none) _ U

theorem component_product_designated {p : ℕ} (hp : 0 < p) (hc : Fintype.card V ≤ p)
    (hL : 10000 ≤ (L : ℝ)) (hbase : (23 / 25 : ℝ) ≤ base)
    (hlower : ∀ v, (3 / 4 : ℝ) ≤ mass weight (s v))
    (hdelta : ∀ v, |delta weight s base v| ≤ (17 / 100 : ℝ)) (hK : K ≤ R / 2) :
    (∫ z, blockTrunc (componentLabel weight s (1 / (100 * p))) R J none z *
      ∏ c, componentAbs weight s (1 / (100 * p)) R J L base own c z
      ∂batchMeasure (fun i : Block (componentLabel weight s (1 / (100 * p))) R none =>
        L * weight i.1.2)) ≤
      designatedBound weight s (1 / (100 * p)) R J K L base := by
  exact integral_product_le _ (simpleSet weight s (1 / (100 * p))) _ _ _ _ _
    (blockTrunc_range _ R J none) _
    (componentAbs_range weight s (1 / (100 * p)) R J L base own hbase)
    (simple_bound weight s R J K L base own hp hc hL hbase hlower hdelta hK)
    (fun c _ z => nonsimple_bound weight s R J L base own hp hc hL hbase hlower c z)

variable {H : Type} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in

theorem truncated_power_designated (sf : H → Finset D) (of : H → Fin R → Bool)
    {p : ℕ} (hp : 0 < p) (hL : 10000 ≤ (L : ℝ))
    (hbase : (23 / 25 : ℝ) ≤ base)
    (hlower : ∀ h, (3 / 4 : ℝ) ≤ mass weight (sf h))
    (hdelta : ∀ h, |mass weight (sf h) - base| ≤ (17 / 100 : ℝ)) (hK : K ≤ R / 2) :
    (∫ ω, HighMoment.allTrunc R J ω *
      (∑ h : H, scoreTerm (sf h) (Real.exp (-(L : ℝ) * base)) (of h)
        (fun r d => ω (r,d))) ^ p
      ∂batchMeasure (fun i : Fin R × D => L * weight i.2)) ≤
        ∑ f : Fin p → H, designatedBound weight (sf ∘ f) (1 / (100 * p)) R J K L base := by
  have hb : Real.exp (-(L : ℝ) * base) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
    have hbas : 0 ≤ base := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr L.coe_nonneg) hbas
  apply (HighMoment.truncated_moment_le_tuple_sum R sf _ of weight
    (fun d => L * weight d) (1 / (100 * p)) J p hb).trans
  apply Finset.sum_le_sum
  intro f _
  exact component_product_designated weight (sf ∘ f) R J K L base (of ∘ f) hp
    (by simp) hL hbase (fun v => hlower (f v)) (fun v => hdelta (f v)) hK

end SharpRamseyFive.AmbientDesignations

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.StaticCertificates

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end SharpRamseyFive.StaticCertificates
end

end OAI
