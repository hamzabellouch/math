import Mathlib

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
abbrev JetIndex (r m : ℕ) := Fin r × Fin m × Fin m

noncomputable def finiteJetColumn (r m : ℕ) (points : Fin r → ℂ × ℂ)
    (f : ℂ → ℂ → ℂ) : JetIndex r m → ℂ := fun j =>
  if (j.2.1 : ℕ) + (j.2.2 : ℕ) < m then
    iteratedDeriv j.2.2 (fun z => iteratedDeriv j.2.1 (fun u => f u z)
      (points j.1).1) (points j.1).2 else 0

theorem finite_jet_rank_persistence {α ι : Type*} [Finite ι]
    (l : Filter α) (r m : ℕ) (points : Fin r → ℂ × ℂ)
    (f : α → ι → ℂ → ℂ → ℂ) (f₀ : ι → ℂ → ℂ → ℂ)
    (hconv : ∀ i j, Tendsto (fun s => finiteJetColumn r m points (f s i) j) l
      (𝓝 (finiteJetColumn r m points (f₀ i) j)))
    (h₀ : LinearIndependent ℂ (fun i => finiteJetColumn r m points (f₀ i))) :
    ∀ᶠ s in l, LinearIndependent ℂ (fun i => finiteJetColumn r m points (f s i)) := by
  have hlim : Tendsto (fun s i => finiteJetColumn r m points (f s i)) l
      (𝓝 (fun i => finiteJetColumn r m points (f₀ i))) :=
    tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (hconv i))
  exact hlim.eventually h₀.eventually

theorem contDiff_iteratedDeriv_parameter (f : ℂ → ℂ → ℂ)
    (hf : ContDiff ℂ ∞ (Function.uncurry f)) (n : ℕ) :
    ContDiff ℂ ∞ (fun p : ℂ × ℂ => iteratedDeriv n (f p.1) p.2) := by
  induction n with
  | zero =>
    exact hf
  | succ n ih =>
    have hh : ContDiff ℂ ∞ (Function.uncurry
        (fun p : ℂ × ℂ => fun z : ℂ => iteratedDeriv n (f p.1) z)) := by
      exact ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
    have hd := hh.fderiv contDiff_snd (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
    have ha := hd.clm_apply (contDiff_const (c := (1 : ℂ)))
    simpa only [iteratedDeriv_succ, deriv] using ha

theorem compression_row_smooth (B h : ℕ) :
    ContDiff ℂ ∞ (fun p : ℂ × ℂ => (1 + p.1 * p.2) ^ B * p.2 ^ h) := by
  fun_prop

theorem compression_row_derivative_limit (B h n : ℕ) (z : ℂ) :
    Tendsto (fun s : ℂ => iteratedDeriv n (fun y : ℂ => (1 + s * y) ^ B * y ^ h) z)
      (𝓝 0) (𝓝 (iteratedDeriv n (fun y : ℂ => y ^ h) z)) := by
  have hc := (contDiff_iteratedDeriv_parameter
    (fun s y : ℂ => (1 + s * y) ^ B * y ^ h) (compression_row_smooth B h) n).continuous
  have hh := (hc.comp (continuous_id.prodMk (continuous_const (y := z)))).tendsto (0 : ℂ)
  change Tendsto (fun s : ℂ => iteratedDeriv n (fun y : ℂ =>
    (1 + s * y) ^ B * y ^ h) z) (𝓝 0)
    (𝓝 (iteratedDeriv n (fun y : ℂ => (1 + 0 * y) ^ B * y ^ h) z)) at hh
  simpa only [zero_mul, add_zero, one_pow, one_mul] using hh

theorem mixed_deriv_separated (f g : ℂ → ℂ) (a b : ℕ) (u z : ℂ) :
    iteratedDeriv b (fun y => iteratedDeriv a (fun x => f x * g y) u) z =
      iteratedDeriv a f u * iteratedDeriv b g z := by
  simp_rw [iteratedDeriv_mul_const_field]
  rw [iteratedDeriv_const_mul_field]

theorem compression_mixed_derivative_limit (q : ℤ) (B h a b : ℕ) (u z : ℂ) :
    Tendsto (fun s : ℂ => iteratedDeriv b (fun y => iteratedDeriv a
      (fun x => x ^ q * ((1 + s * y) ^ B * y ^ h)) u) z) (𝓝 0)
      (𝓝 (iteratedDeriv b (fun y => iteratedDeriv a (fun x => x ^ q * y ^ h) u) z)) := by
  simp_rw [mixed_deriv_separated]
  exact tendsto_const_nhds.mul (compression_row_derivative_limit B h b z)

theorem compression_finite_rank {ι : Type*} [Finite ι] (q : ι → ℤ) (B h : ι → ℕ)
    (r m : ℕ) (points : Fin r → ℂ × ℂ)
    (h₀ : LinearIndependent ℂ (fun i => finiteJetColumn r m points
      (fun u z => u ^ q i * z ^ h i))) :
    ∀ᶠ s : ℂ in 𝓝 0, LinearIndependent ℂ (fun i => finiteJetColumn r m points
      (fun u z => u ^ q i * ((1 + s * z) ^ B i * z ^ h i))) := by
  apply finite_jet_rank_persistence (𝓝 (0 : ℂ)) r m points _ _ _ h₀
  intro i j
  dsimp only [finiteJetColumn]
  split_ifs
  · exact compression_mixed_derivative_limit (q i) (B i) (h i) j.2.1 j.2.2
      (points j.1).1 (points j.1).2
  · exact tendsto_const_nhds

theorem linearIndependent_of_span_le {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℂ V] (u v : ι → V)
    (hu : LinearIndependent ℂ u)
    (hspan : Submodule.span ℂ (Set.range u) ≤ Submodule.span ℂ (Set.range v)) :
    LinearIndependent ℂ v := by
  let := Module.Finite.span_of_finite ℂ (Set.finite_range v)
  apply linearIndependent_iff_card_le_finrank_span.mpr
  rw [← finrank_span_eq_card hu]
  exact Submodule.finrank_mono hspan

theorem iteratedDeriv_polynomial (P : Polynomial ℂ) (n : ℕ) :
    iteratedDeriv n (fun z : ℂ => P.eval z) =
      fun z => (((Polynomial.derivative : Module.End ℂ (Polynomial ℂ)) ^ n) P).eval z := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have he : deriv (fun z : ℂ => P.eval z) = fun z => P.derivative.eval z := by
      funext z
      exact P.deriv
    rw [he, ih, Module.End.iterate_succ]
    rfl

noncomputable def polynomialJetMap (r m : ℕ) (points : Fin r → ℂ × ℂ) (q : ℤ) :
    Polynomial ℂ →ₗ[ℂ] (JetIndex r m → ℂ) :=
  LinearMap.pi fun j => if (j.2.1 : ℕ) + (j.2.2 : ℕ) < m then
    (iteratedDeriv j.2.1 (fun u : ℂ => u ^ q) (points j.1).1) •
      ((Polynomial.aeval (points j.1).2).toLinearMap.comp
        ((Polynomial.derivative : Module.End ℂ (Polynomial ℂ)) ^ (j.2.2 : ℕ)))
  else 0

theorem polynomialJetMap_eq (r m : ℕ) (points : Fin r → ℂ × ℂ) (q : ℤ)
    (P : Polynomial ℂ) :
    polynomialJetMap r m points q P = finiteJetColumn r m points
      (fun u z => u ^ q * P.eval z) := by
  funext j
  simp only [polynomialJetMap, LinearMap.pi_apply, finiteJetColumn]
  split_ifs <;> simp only [LinearMap.smul_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, Polynomial.coe_aeval_eq_eval, smul_eq_mul,
    mixed_deriv_separated, iteratedDeriv_polynomial, LinearMap.zero_apply]

theorem polynomial_image_mem_span {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : Polynomial ℂ →ₗ[ℂ] V) (P : Polynomial ℂ) (n : ℕ) (hP : P.natDegree ≤ n) :
    L P ∈ Submodule.span ℂ (Set.range fun j : Fin (n + 1) => L (Polynomial.X ^ (j : ℕ))) := by
  classical
  rw [← P.sum_monomial_eq, Polynomial.sum_def, map_sum]
  apply Submodule.sum_mem
  intro j hj
  have hjn : j < n + 1 := by
    have h := (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hj)).trans hP
    omega
  have he : Polynomial.monomial j (P.coeff j) = (P.coeff j) • (Polynomial.X : Polynomial ℂ) ^ j := by
    simp [Polynomial.smul_eq_C_mul, Polynomial.C_mul_X_pow_eq_monomial]
  rw [he, map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hjn⟩, rfl⟩)

noncomputable def compressionRowMap (s : ℂ) (B : ℕ) : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ where
  toFun P := (1 + Polynomial.C s * Polynomial.X) ^ B * P.comp (1 + Polynomial.C s * Polynomial.X)
  map_add' P Q := by simp [mul_add]
  map_smul' c P := by
    simp only [Polynomial.smul_eq_C_mul, RingHom.id_apply, Polynomial.mul_comp,
      Polynomial.C_comp]
    ring

@[simp] theorem compressionRowMap_pow (s : ℂ) (B j : ℕ) :
    compressionRowMap s B (Polynomial.X ^ j) = (1 + Polynomial.C s * Polynomial.X) ^ (B + j) := by
  simp [compressionRowMap, pow_add]

theorem compressionRowMap_inverse (s : ℂ) (hs : s ≠ 0) (B h : ℕ) :
    compressionRowMap s B ((Polynomial.C s⁻¹ * (Polynomial.X - 1)) ^ h) =
      (1 + Polynomial.C s * Polynomial.X) ^ B * Polynomial.X ^ h := by
  have he : Polynomial.C s⁻¹ * ((1 + Polynomial.C s * Polynomial.X) - 1) =
      (Polynomial.X : Polynomial ℂ) := by
    rw [add_sub_cancel_left, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hs,
      Polynomial.C_1, one_mul]
  simp only [compressionRowMap, LinearMap.coe_mk, AddHom.coe_mk, Polynomial.pow_comp,
    Polynomial.mul_comp, Polynomial.C_comp, Polynomial.sub_comp, Polynomial.X_comp,
    Polynomial.one_comp, he]

theorem compression_inverse_degree (s : ℂ) (h : ℕ) :
    ((Polynomial.C s⁻¹ * (Polynomial.X - 1)) ^ h).natDegree ≤ h := by
  have ha : (Polynomial.C s⁻¹ * (Polynomial.X - 1)).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_mul_le).trans ?_
    simp only [Polynomial.natDegree_C, zero_add]
    exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  exact (Polynomial.natDegree_pow_le).trans (by simpa using Nat.mul_le_mul_left h ha)


end MaximalSeshadri.Interpolation
end

end OAI
