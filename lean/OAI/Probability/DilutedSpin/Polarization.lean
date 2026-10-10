import Mathlib

namespace OAI

section
section
open scoped BigOperators

namespace DilutedSpinGlass.Polarization

def sign (b : Bool) : ℝ := if b then 1 else -1
@[simp] lemma sign_not (b : Bool) : sign (!b) = -sign b := by cases b <;> norm_num [sign]
@[simp] lemma sign_sq (b : Bool) : sign b * sign b = 1 := by cases b <;> norm_num [sign]

variable {ι : Type} [DecidableEq ι]

def flip (j : ι) (ε : ι → Bool) : ι → Bool := Function.update ε j (!ε j)
lemma flip_involutive (j : ι) : Function.Involutive (flip j) := by
  intro ε
  funext i
  by_cases h : i=j <;> simp [flip, h]

variable [Fintype ι]

lemma prod_sign_flip (j : ι) (ε : ι → Bool) :
    (∏ i, sign (flip j ε i)) = -(∏ i, sign (ε i)) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun i => sign (flip j ε i)) (Finset.mem_univ j),
      ← Finset.mul_prod_erase Finset.univ (fun i => sign (ε i)) (Finset.mem_univ j)]
  simp only [flip, Function.update_self, sign_not, neg_mul]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]

/-- The signed cube average annihilates every non-surjective assignment of
k slots to k colors. Thus only permutations survive polarization. -/
lemma signed_cube_sum (f : ι → ι) :
    (∑ ε : ι → Bool, (∏ i, sign (ε i)) * ∏ i, sign (ε (f i))) =
      if Function.Bijective f then (2 : ℝ) ^ Fintype.card ι else 0 := by
  classical
  by_cases hf : Function.Bijective f
  · rw [ite_eq_left hf]
    have he (ε : ι → Bool) : (∏ i, sign (ε (f i))) = ∏ i, sign (ε i) :=
      Equiv.prod_comp (Equiv.ofBijective f hf) (fun i => sign (ε i))
    simp_rw [he, ← Finset.prod_mul_distrib, sign_sq]
    simp
  · rw [ite_eq_right hf]
    have hns : ¬ Function.Surjective f := fun hs => hf ⟨(Finite.injective_iff_surjective).mpr hs, hs⟩
    obtain ⟨j, hj⟩ : ∃ j, ∀ i, f i ≠ j := by simpa [Function.Surjective] using hns
    let H (ε : ι → Bool) := (∏ i, sign (ε i)) * ∏ i, sign (ε (f i))
    have hflip (ε : ι → Bool) : H (flip j ε) = -H ε := by
      dsimp [H]
      rw [prod_sign_flip]
      have he : (∏ i, sign (flip j ε (f i))) = ∏ i, sign (ε (f i)) := by
        apply Finset.prod_congr rfl
        intro i _
        simp [flip, hj i]
      rw [he, neg_mul]
    have he := Equiv.sum_comp (Equiv.ofBijective (flip j) (flip_involutive j).bijective) H
    change (∑ ε, H (flip j ε)) = ∑ ε, H ε at he
    simp_rw [hflip, Finset.sum_neg_distrib] at he
    change (∑ ε, H ε) = 0
    linarith

variable {E : Type} [AddCommGroup E] [Module ℝ E]

/-- Unnormalized real polarization, with exactly the ordered-permutation
multiplicity. This does not assume a vanishing diagonal. -/
lemma signed_polarization (M : MultilinearMap ℝ (fun _ : ι => E) ℝ)
    (hsym : ∀ (v : ι → E) (π : Equiv.Perm ι), M (v ∘ π) = M v) (v : ι → E) :
    (∑ ε : ι → Bool, (∏ j, sign (ε j)) *
        M (fun _ => ∑ j, sign (ε j) • v j)) =
      (2 : ℝ) ^ Fintype.card ι * (Fintype.card ι).factorial * M v := by
  classical
  have he (ε : ι → Bool) : M (fun _ : ι => ∑ j, sign (ε j) • v j) =
      ∑ f : ι → ι, (∏ i, sign (ε (f i))) * M (fun i => v (f i)) := by
    rw [M.map_sum]
    apply Finset.sum_congr rfl
    intro f _
    simpa only [smul_eq_mul] using M.map_smul_univ (fun i => sign (ε (f i))) (fun i => v (f i))
  simp_rw [he, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, signed_cube_sum]
  have hc : (Finset.univ.filter (Function.Bijective : (ι → ι) → Prop)).card =
      (Fintype.card ι).factorial := by
    calc
      _ = Fintype.card {f : ι → ι // Function.Bijective f} := (Fintype.card_subtype _).symm
      _ = Fintype.card (Equiv.Perm ι) := Fintype.card_congr Equiv.bijectiveEquiv
      _ = _ := Fintype.card_perm
  calc
    _ = ∑ f ∈ Finset.univ.filter (Function.Bijective : (ι → ι) → Prop), (2 : ℝ) ^ Fintype.card ι * M v := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro f _
      by_cases hf : Function.Bijective f
      · simp only [ite_eq_left hf]
        apply congrArg ((2 : ℝ) ^ Fintype.card ι * ·)
        exact hsym v (Equiv.ofBijective f hf)
      · simp only [ite_eq_right hf, zero_mul]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, hc]; ring

 
noncomputable def averageDirection {k : ℕ} (ε : Fin k → Bool) (v : Fin k → E) : E :=
  (k : ℝ)⁻¹ • ∑ j, sign (ε j) • v j

lemma normalized_polarization {k : ℕ} (hk : 0 < k)
    (M : MultilinearMap ℝ (fun _ : Fin k => E) ℝ)
    (hsym : ∀ (v : Fin k → E) (π : Equiv.Perm (Fin k)), M (v ∘ π) = M v)
    (v : Fin k → E) :
    M v = ((k : ℝ)^k / (2^k * k.factorial)) *
      ∑ ε : Fin k → Bool, (∏ j, sign (ε j)) * M (fun _ => averageDirection ε v) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hscale (ε : Fin k → Bool) :
      (k : ℝ)^k * M (fun _ => averageDirection ε v) =
        M (fun _ => ∑ j, sign (ε j) • v j) := by
    unfold averageDirection
    rw [M.map_smul_univ]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hk0, one_pow, one_mul]
  have he := signed_polarization M hsym v
  simp only [Fintype.card_fin] at he
  simp_rw [← hscale] at he
  have hh : (k : ℝ)^k *
      (∑ ε : Fin k → Bool, (∏ j, sign (ε j)) * M (fun _ => averageDirection ε v)) =
      (2^k * (k.factorial : ℝ)) * M v := by
    rw [Finset.mul_sum]
    convert he using 1
    · apply Finset.sum_congr rfl
      intro ε _
      ring
  have hd : (2^k * (k.factorial : ℝ)) ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num))
    (by exact_mod_cast Nat.factorial_ne_zero k)
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hd).mpr
  linarith

lemma averageDirection_bound {k : ℕ} (hk : 0 < k) {X : Type}
    (ε : Fin k → Bool) (v : Fin k → X → ℝ) (hv : ∀ j x, |v j x| ≤ 1) (x : X) :
    |averageDirection ε v x| ≤ 1 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  simp only [averageDirection, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  rw [abs_mul, abs_of_pos (inv_pos.mpr hk0)]
  have hb : |∑ j, sign (ε j) * v j x| ≤ (k : ℝ) := by
    calc
      _ ≤ ∑ j, |sign (ε j) * v j x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin k, (1 : ℝ) := Finset.sum_le_sum (fun j _ => by
        have hs : |sign (ε j)| = 1 := by cases ε j <;> norm_num [sign]
        simpa only [abs_mul, hs, one_mul] using hv j x)
      _ = _ := by simp
  calc
    _ ≤ (k : ℝ)⁻¹ * k := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hk0.le)
    _ = 1 := inv_mul_cancel₀ hk0.ne'

end DilutedSpinGlass.Polarization
end

end

section
section
namespace DilutedSpinGlass
open MeasureTheory

lemma abs_integral_le_one {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (f : Z → ℝ) (hf : ∀ z, |f z| ≤ 1) :
    |∫ z, f z ∂μ| ≤ 1 := by
  calc
    _ ≤ ∫ z, |f z| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _z : Z, (1:ℝ) ∂μ := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun z => abs_nonneg (f z))) (integrable_const 1)
      (Filter.Eventually.of_forall hf)
    _ = 1 := by simp

lemma centered_scalar_div_bound {H H1 F A J δ : ℝ}
    (_hJ : J ≠ 0) (hδ : 0 ≤ δ) (hF : |F| ≤ 1) (hA : |A| ≤ 1)
    (h1 : H1/J = -δ*A) :
    H/J ≤ |H-F*H1|/|J|+δ := by
  have he : H/J = (H-F*H1)/J+F*(H1/J) := by ring
  have hD : (H-F*H1)/J ≤ |H-F*H1|/|J| := by
    simpa only [abs_div] using le_abs_self ((H-F*H1)/J)
  have hFA : |F*A| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hF hA (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hl := (abs_le.mp hFA).1
  rw [he,h1]
  nlinarith

/-- Root averaging MUST precede the absolute value of the covariance. This
lemma retains that quantifier order, while integrating genuine single-copy
projection errors. There is no root-wise concentration hypothesis. -/
theorem root_matrix_error_bound {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (E H H1 F A Et Eo : Z → ℝ) (J δ c B M : ℝ)
    (hJ : J ≠ 0) (hδ : 0 ≤ δ)
    (hF : ∀ z, |F z| ≤ 1) (hA : ∀ z, |A z| ≤ 1)
    (h1 : ∀ z, H1 z/J = -δ*A z)
    (hE : Integrable E μ) (hH : Integrable H μ) (_hAint : Integrable A μ)
    (hEt : Integrable Et μ) (hEo : Integrable Eo μ)
    (hpoint : ∀ z, c*E z ≤ δ+H z/J+Et z*B/|J|+M*Eo z) :
    c*(∫ z, E z ∂μ) ≤ 2*δ+
      |(∫ z, H z ∂μ)-(∫ z, F z ∂μ)*(∫ z, H1 z ∂μ)|/|J|+
      (∫ z, Et z ∂μ)*B/|J|+M*(∫ z, Eo z ∂μ) := by
  have hh1 : (∫ z, H1 z ∂μ)/J = -δ*(∫ z, A z ∂μ) := by
    rw [← integral_div]
    simp_rw [h1]
    rw [integral_const_mul]
  have hs := centered_scalar_div_bound (H := ∫ z, H z ∂μ) hJ hδ (abs_integral_le_one μ F hF)
    (abs_integral_le_one μ A hA) hh1
  have hi1 : Integrable (fun z => δ+H z/J) μ := (integrable_const δ).add (hH.div_const J)
  have hi2 : Integrable (fun z => δ+H z/J+Et z*B/|J|) μ := hi1.add ((hEt.mul_const B).div_const |J|)
  have hi := integral_mono (hE.const_mul c) (hi2.add (hEo.const_mul M)) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul,integral_add hi2 (hEo.const_mul M),
    integral_add hi1 ((hEt.mul_const B).div_const |J|),
    integral_add (integrable_const δ) (hH.div_const J),
    integral_div,integral_div,integral_mul_const,integral_const_mul] at hi
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hi
  linarith

end DilutedSpinGlass
end

end

section
section
open MeasureTheory Filter
open scoped Topology

namespace DilutedSpinGlass

 
theorem select_parameters {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    (Δ : Ω → ℝ) (e : ι → Ω → ℝ) (hΔ : Integrable Δ μ)
    (he : ∀ i, Integrable (e i) μ) (hne : ∀ i x, 0 ≤ e i x)
    {C v u ε K : ℝ} (hK : 0 < K) (_hε : 0 < ε)
    (hlower : ∀ x, -C ≤ Δ x) (havg : ∫ x, Δ x ∂μ ≤ v)
    (hpen : u+C ≤ K*ε)
    (hsmall : v+K*(∑ i, ∫ x, e i x ∂μ) ≤ u) :
    ∃ x, Δ x ≤ u ∧ ∀ i, e i x ≤ ε := by
  classical
  let F (x : Ω) := Δ x + K * ∑ i, e i x
  have hi : Integrable F μ :=
    hΔ.add ((integrable_finsetSum Finset.univ (fun i _ => he i)).const_mul K)
  obtain ⟨x, hx⟩ := exists_le_integral hi
  have hF : ∫ x, F x ∂μ ≤ u := by
    dsimp [F]
    rw [integral_add hΔ ((integrable_finsetSum _ (fun i _ => he i)).const_mul K),
      integral_const_mul, integral_finsetSum _ (fun i _ => he i)]
    linarith
  have hx' : F x ≤ u := hx.trans hF
  have hsum : 0 ≤ ∑ i, e i x := Finset.sum_nonneg (fun i _ => hne i x)
  refine ⟨x, ?_, ?_⟩
  · dsimp [F] at hx'
    nlinarith
  · intro i
    have hle : e i x ≤ ∑ j, e j x :=
      Finset.single_le_sum (fun j _ => hne j x) (Finset.mem_univ i)
    have hlo := hlower x
    dsimp [F] at hx'
    nlinarith

end DilutedSpinGlass

namespace DilutedSpinGlass

/-- All score errors are made small on one deterministic low-increment
sequence. The parameter may range over an arbitrary probability space; this
is the noncompact-parameter step in pert:selection. -/
theorem countable_parameter_selection
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Δ : ℕ → Ω → ℝ) (e : ℕ → ℕ → Ω → ℝ)
    (hΔ : ∀ N, Integrable (Δ N) μ) (he : ∀ ν N, Integrable (e ν N) μ)
    (hne : ∀ ν N x, 0 ≤ e ν N x)
    {C v u : ℝ} (hC : 0 ≤ C) (hvu : v < u)
    (hlower : ∀ N x, -C ≤ Δ N x)
    (hlow : ∀ n, ∃ N, n ≤ N ∧ ∫ x, Δ N x ∂μ ≤ v)
    (hlim : ∀ ν, Tendsto (fun N => ∫ x, e ν N x ∂μ) atTop (𝓝 0)) :
    ∃ (Ns : ℕ → ℕ) (xs : ℕ → Ω), StrictMono Ns ∧
      (∀ j, Δ (Ns j) (xs j) ≤ u) ∧
      (∀ ν, Tendsto (fun j => e ν (Ns j) (xs j)) atTop (𝓝 0)) := by
  classical
  have hstep (j n : ℕ) : ∃ z : ℕ × Ω, n < z.1 ∧ Δ z.1 z.2 ≤ u ∧
      ∀ ν ≤ j, e ν z.1 z.2 ≤ 1/((j : ℝ)+1) := by
    let K := (|u|+C+1)*((j : ℝ)+1)
    have hK : 0 < K := by dsimp [K]; positivity
    have hgap : 0 < (u-v)/K := div_pos (sub_pos.mpr hvu) hK
    have ht : Tendsto (fun N => ∑ i : Fin (j+1), ∫ x, e i N x ∂μ) atTop (𝓝 0) := by
      simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ
        (fun (i : Fin (j+1)) _ => hlim i)
    obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hgap))
    obtain ⟨N, hN, hNv⟩ := hlow (max n₁ (n+1))
    have hsum := hn₁ N ((le_max_left _ _).trans hN)
    obtain ⟨x, hxu, hxe⟩ := select_parameters μ (Δ N) (fun i : Fin (j+1) => e i N)
      (hΔ N) (fun i => he i N) (fun i => hne i N) hK (by positivity : 0 < 1/((j : ℝ)+1))
      (hlower N) hNv (show u+C ≤ K*(1/((j : ℝ)+1)) from by
        dsimp [K]
        field_simp
        nlinarith [le_abs_self u])
      (show v+K*(∑ i : Fin (j+1), ∫ x, e i N x ∂μ) ≤ u from by
        have := (lt_div_iff₀ hK).mp hsum
        nlinarith)
    refine ⟨(N,x), ?_, hxu, ?_⟩
    · have : n+1 ≤ N := (le_max_right _ _).trans hN
      omega
    · intro ν hν
      exact hxe ⟨ν, by omega⟩
  let step (j n : ℕ) : ℕ × Ω := Classical.choose (hstep j n)
  have hs (j n : ℕ) := Classical.choose_spec (hstep j n)
  let seq : ℕ → ℕ × Ω := Nat.rec (step 0 0) (fun j z => step (j+1) z.1)
  have hseq (j : ℕ) : Δ (seq j).1 (seq j).2 ≤ u ∧
      ∀ ν ≤ j, e ν (seq j).1 (seq j).2 ≤ 1/((j : ℝ)+1) := by
    cases j with
    | zero => exact (hs 0 0).2
    | succ j => simpa only [seq, step] using (hs (j+1) (seq j).1).2
  refine ⟨fun j => (seq j).1, fun j => (seq j).2, ?_, fun j => (hseq j).1, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro j
    simpa only [seq, step] using (hs (j+1) (seq j).1).1
  · intro ν
    apply squeeze_zero' (Eventually.of_forall (fun j => hne ν (seq j).1 (seq j).2))
    · filter_upwards [eventually_ge_atTop ν] with j hj
      exact (hseq j).2 ν hj
    · exact tendsto_one_div_add_atTop_nhds_zero_nat

end DilutedSpinGlass
end

end

end OAI
