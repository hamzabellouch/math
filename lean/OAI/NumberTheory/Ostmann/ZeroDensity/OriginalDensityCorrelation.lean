import OAI.NumberTheory.Ostmann.ZeroDensity.DensityFourierUnitProduct

namespace OAI

/-! # Correlation estimates for the original two divisor transforms -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

private theorem prime_list_nodup (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hc : ps.Pairwise Nat.Coprime) : ps.Nodup := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hc
    refine List.nodup_cons.mpr ⟨?_, ih (fun q hq => hp q (List.mem_cons_of_mem p hq)) htail⟩
    intro hmem
    have he : p = 1 := by simpa [Nat.Coprime] using hhead p hmem
    exact (hp p List.mem_cons_self).ne_one he

noncomputable def supportCorrelationSide (U V : Finset ℕ) (p : ℕ) : CorrelationSide :=
  if p ∈ U then if p ∈ V then .both else .left else .right

private theorem prod_mask_subset {ι : Type*} [DecidableEq ι] (U P : Finset ι)
    (hUP : U ⊆ P) (F : ι → ℂ) :
    (∏ p ∈ P, if p ∈ U then F p else 1) = ∏ p ∈ U, F p := by
  rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hUP]

theorem local_correlation_product (U V P : Finset ℕ) (hP : P = U ∪ V)
    (f : ∀ p : ℕ, ZMod p → ℂ) (a b : ∀ p : ℕ, (ZMod p)ˣ) (n : ℤ) :
    (∏ p ∈ P, correlationPrimeFactor f (supportCorrelationSide U V) a b p (n : ZMod p)) =
      (∏ p ∈ U, primeDensityFourier f p ((a p : ZMod p) * (n : ZMod p))) *
        conj (∏ p ∈ V, primeDensityFourier f p ((b p : ZMod p) * (n : ZMod p))) := by
  classical
  have hf (p : ℕ) (hp : p ∈ P) :
      correlationPrimeFactor f (supportCorrelationSide U V) a b p (n : ZMod p) =
      (if p ∈ U then primeDensityFourier f p ((a p : ZMod p) * (n : ZMod p)) else 1) *
      (if p ∈ V then conj (primeDensityFourier f p ((b p : ZMod p) * (n : ZMod p))) else 1) := by
    have hm : p ∈ U ∨ p ∈ V := by simpa only [hP, Finset.mem_union] using hp
    unfold correlationPrimeFactor supportCorrelationSide
    rcases hm with hu | hv
    · by_cases hv : p ∈ V <;> simp [hu, hv]
    · by_cases hu : p ∈ U <;> simp [hu, hv]
  rw [Finset.prod_congr rfl hf, Finset.prod_mul_distrib,
    prod_mask_subset U P (by rw [hP]; exact Finset.subset_union_left),
    prod_mask_subset V P (by rw [hP]; exact Finset.subset_union_right), map_prod]

/-- Both original transforms have one common periodic model. Its coefficient
bound is derived from the local density functions, including their CRT twists. -/
theorem original_density_correlation_model (ps qs rs : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) (hq : ∀ p ∈ qs, p.Prime) (hr : ∀ p ∈ rs, p.Prime)
    (hcp : ps.Pairwise Nat.Coprime) (hcq : qs.Pairwise Nat.Coprime) (hcr : rs.Pairwise Nat.Coprime)
    (hrs : rs.toFinset = ps.toFinset ∪ qs.toFinset)
    (vp : (ZMod ps.prod)ˣ) (vq : (ZMod qs.prod)ˣ)
    (f : ∀ p : ℕ, ZMod p → ℂ) (hf : ∀ p ∈ rs, ∀ x, ‖f p x‖ ≤ 1) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    let : NeZero qs.prod := ⟨(prime_list_prod_pos qs hq).ne'⟩
    let : NeZero rs.prod := ⟨(prime_list_prod_pos rs hr).ne'⟩
    ∃ F : ZMod rs.prod → ℂ,
      (∀ n : ℤ, densityFourier (primeCRTFunction ps hp hcp f) ((vp : ZMod ps.prod) * (n : ZMod ps.prod)) *
        conj (densityFourier (primeCRTFunction qs hq hcq f) ((vq : ZMod qs.prod) * (n : ZMod qs.prod))) = F (n : ZMod rs.prod)) ∧
      (∀ u, ‖additiveFourier F u‖ ≤
        (rs.map (correlationPrimeBound (supportCorrelationSide ps.toFinset qs.toFinset))).prod) := by
  let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
  let : NeZero qs.prod := ⟨(prime_list_prod_pos qs hq).ne'⟩
  let : NeZero rs.prod := ⟨(prime_list_prod_pos rs hr).ne'⟩
  obtain ⟨a, ha⟩ := densityFourier_primeCRTFunction_unit ps hp hcp f vp
  obtain ⟨b, hb⟩ := densityFourier_primeCRTFunction_unit qs hq hcq f vq
  refine ⟨primeCRTFunction rs hr hcr
    (correlationPrimeFactor f (supportCorrelationSide ps.toFinset qs.toFinset) a b), ?_, ?_⟩
  · intro n
    rw [ha, hb, primeCRTFunction_intCast,
      ← List.prod_toFinset _ (prime_list_nodup ps hp hcp),
      ← List.prod_toFinset _ (prime_list_nodup qs hq hcq),
      ← List.prod_toFinset _ (prime_list_nodup rs hr hcr)]
    exact (local_correlation_product ps.toFinset qs.toFinset rs.toFinset hrs f a b n).symm
  · exact density_correlation_coefficient_bound rs hr hcr f hf _ a b

/-- The weighted periodic estimate applies to the two CRT divisor transforms. -/
theorem original_density_correlation_weighted_bound (ps qs rs : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) (hq : ∀ p ∈ qs, p.Prime) (hr : ∀ p ∈ rs, p.Prime)
    (hcp : ps.Pairwise Nat.Coprime) (hcq : qs.Pairwise Nat.Coprime) (hcr : rs.Pairwise Nat.Coprime)
    (hrs : rs.toFinset = ps.toFinset ∪ qs.toFinset)
    (vp : (ZMod ps.prod)ˣ) (vq : (ZMod qs.prod)ˣ)
    (f : ∀ p : ℕ, ZMod p → ℂ) (hf : ∀ p ∈ rs, ∀ x, ‖f p x‖ ≤ 1)
    (α : ℝ) (w : ℕ → ℂ) (N : ℕ) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    let : NeZero qs.prod := ⟨(prime_list_prod_pos qs hq).ne'⟩
    ‖∑ n ∈ Finset.range N, w n *
      (densityFourier (primeCRTFunction ps hp hcp f) ((vp : ZMod ps.prod) * (n : ZMod ps.prod)) *
        conj (densityFourier (primeCRTFunction qs hq hcq f) ((vq : ZMod qs.prod) * (n : ZMod qs.prod))) *
          realAdditivePhase α ^ n)‖ ≤ discreteVariation w N *
      (2 * (rs.map (correlationPrimeBound (supportCorrelationSide ps.toFinset qs.toFinset))).prod *
        ((N : ℝ) + rs.prod * (1 + Real.log rs.prod))) := by
  let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
  let : NeZero qs.prod := ⟨(prime_list_prod_pos qs hq).ne'⟩
  let : NeZero rs.prod := ⟨(prime_list_prod_pos rs hr).ne'⟩
  obtain ⟨F, hF, hbound⟩ := original_density_correlation_model ps qs rs hp hq hr hcp hcq hcr hrs vp vq f hf
  have he (n : ℕ) : densityFourier (primeCRTFunction ps hp hcp f)
      ((vp : ZMod ps.prod) * (n : ZMod ps.prod)) *
      conj (densityFourier (primeCRTFunction qs hq hcq f)
        ((vq : ZMod qs.prod) * (n : ZMod qs.prod))) = F (n : ZMod rs.prod) := by
    simpa only [Int.cast_natCast] using hF (n : ℤ)
  simp_rw [he]
  apply weighted_periodic_linear_phase_bound rs.prod F _ α _ hbound w N
  exact List.prod_nonneg (fun x hx => by
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    exact correlationPrimeBound_nonneg _ p)

end Ostmann

end OAI
