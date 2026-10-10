import OAI.RepresentationTheory.KazhdanLusztig.GradedSheaves

namespace OAI

/-!
Hilbert series of graded modules and boundary sheaves, positivity and strict detection.
-/

section

namespace KLInvariance.Hilbert

/-- Sum over all monomials in finitely many variables, before grouping by degree. -/
theorem hasSum_monomials (σ : Type*) [Fintype σ] {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun d : σ → ℕ => q ^ (∑ i, d i)) ((1-q)⁻¹ ^ Fintype.card σ) := by
  classical
  apply Fintype.induction_empty_option (P := fun σ _ =>
    HasSum (fun d : σ → ℕ => q ^ (∑ i, d i)) ((1-q)⁻¹ ^ Fintype.card σ))
  · intro α β _ e ih
    let : Fintype α := Fintype.ofEquiv β e.symm
    rw [← Fintype.card_congr e]
    apply (Equiv.piCongrLeft (fun _ : β => ℕ) e).hasSum_iff.mp
    convert ih using 1
    ext d
    simp only [Function.comp_apply, Equiv.piCongrLeft_apply]
    congr 1
    simpa using e.symm.sum_comp d
  · simp
  · intro α _ ih
    have hg := hasSum_geometric_of_lt_one hq hq1
    have hs := hg.summable.mul_of_nonneg ih.summable
      (fun _ => pow_nonneg hq _) (fun _ => pow_nonneg hq _)
    have hh := hg.mul ih hs
    have he := (Equiv.piOptionEquivProd (β := fun _ : Option α => ℕ)).hasSum_iff.mpr hh
    simpa [Function.comp_def, Fintype.sum_option, pow_add, pow_succ, mul_comm] using he


lemma intWeight_eq_natWeight {σ : Type*} (d : σ →₀ ℕ) :
    Finsupp.weight (fun _ : σ => (1 : ℤ)) d =
      (Finsupp.weight (fun _ : σ => (1 : ℕ)) d : ℕ) := by
  simp [Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum]

lemma polynomialGrading_nat (k : Type*) [Field k] (σ : Type*) (n : ℕ) :
    Graded.polynomialGrading k σ n =
      MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => (1 : ℕ)) n := by
  ext p
  change (∀ d, p.coeff d ≠ 0 →
    Finsupp.weight (fun _ : σ => (1 : ℤ)) d = (n : ℤ)) ↔ _
  simp only [intWeight_eq_natWeight, Nat.cast_inj]
  rfl

instance polynomialPiece_finite (k : Type*) [Field k] (σ : Type*) [Finite σ] (n : ℤ) :
    Module.Finite k (Graded.polynomialGrading k σ n) := by
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [polynomialGrading_nat]
    exact Module.Finite.iff_fg.mpr
      (MvPolynomial.weightedHomogeneousSubmodule_fg k (fun _ : σ => 1) (by simp) m)
  · rw [Graded.polynomialGrading_negative k σ n (lt_of_not_ge hn)]
    infer_instance

lemma polynomial_finrank_nat (k : Type*) [Field k] (σ : Type*) (n : ℕ) :
    Module.finrank k (Graded.polynomialGrading k σ n) =
      Nat.card {d : σ →₀ ℕ // Finsupp.weight (fun _ => (1 : ℕ)) d = n} := by
  rw [polynomialGrading_nat, MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  exact Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport k _)

lemma hasSum_finsupp_monomials (σ : Type*) [Fintype σ] {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun d : σ →₀ ℕ => q ^ Finsupp.weight (fun _ => (1 : ℕ)) d)
      ((1-q)⁻¹ ^ Fintype.card σ) := by
  have h := (Finsupp.equivFunOnFinite (α := σ) (M := ℕ)).hasSum_iff.mpr
    (hasSum_monomials σ hq hq1)
  convert h using 1
  ext d
  congr 1
  simp only [Finsupp.weight_apply, smul_eq_mul, mul_one]
  exact Finsupp.sum_fintype d _ (by simp)

/-- The actual finite polynomial ring has Hilbert series `(1-q)⁻ᴺ`. -/
theorem hasSum_polynomial_nat (k : Type*) [Field k] (σ : Type*) [Fintype σ]
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => (Module.finrank k (Graded.polynomialGrading k σ n) : ℝ) * q^n)
      ((1-q)⁻¹ ^ Fintype.card σ) := by
  have h := (hasSum_finsupp_monomials σ hq hq1).tsum_fiberwise
    (Finsupp.weight (fun _ : σ => (1 : ℕ)))
  apply h.congr_fun
  intro n
  rw [polynomial_finrank_nat]
  have hf : (fun d : ↑((Finsupp.weight (R := ℕ) (fun _ : σ => (1 : ℕ))) ⁻¹' {n}) =>
      q ^ (Finsupp.weight (fun _ : σ => (1 : ℕ))) d.val) = fun _ => q^n := by
    funext d
    rw [show Finsupp.weight (fun _ : σ => (1 : ℕ)) d.val = n from d.property]
  rw [hf, tsum_const, nsmul_eq_mul]
  simp only [Set.preimage, Set.mem_singleton_iff]
  rfl


/-- Integer-indexed grading, including its zero negative pieces. -/
theorem hasSum_polynomial (k : Type*) [Field k] (σ : Type*) [Fintype σ]
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℤ => (Module.finrank k (Graded.polynomialGrading k σ n) : ℝ) * q^n)
      ((1-q)⁻¹ ^ Fintype.card σ) := by
  apply ((Nat.cast_injective : Function.Injective ((↑) : ℕ → ℤ)).hasSum_iff ?_).mp
  · simpa only [Function.comp_def, zpow_natCast] using hasSum_polynomial_nat k σ hq hq1
  · intro n hn
    have hn' : n < 0 := by
      by_contra h
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt h)
      exact hn ⟨m, rfl⟩
    rw [Graded.polynomialGrading_negative k σ n hn']
    simp

end KLInvariance.Hilbert


end


section

namespace KLInvariance.Hilbert
universe uk ua um ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]

/-- Degree pieces of a shifted finite free module, as a genuine linear equivalence. -/
def shiftedPieceEquiv {ι : Type ui} (𝓐 : ℤ → Submodule k A) (d : ι → ℤ) (n : ℤ) :
    Graded.shiftedPiece 𝓐 d n ≃ₗ[k] (∀ i, 𝓐 (n-d i)) where
  toFun v i := ⟨v.val i, v.property i⟩
  invFun v := ⟨fun i => v i, fun i => (v i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance shiftedPiece_finite {ι : Type ui} [Finite ι]
    (𝓐 : ℤ → Submodule k A) [∀ n, Module.Finite k (𝓐 n)] (d : ι → ℤ) (n : ℤ) :
    Module.Finite k (Graded.shiftedPiece 𝓐 d n) :=
  Module.Finite.of_surjective (shiftedPieceEquiv 𝓐 d n).symm.toLinearMap
    (shiftedPieceEquiv 𝓐 d n).symm.surjective

lemma shiftedPiece_finrank {ι : Type ui} [Fintype ι]
    (𝓐 : ℤ → Submodule k A) [∀ n, Module.Finite k (𝓐 n)] (d : ι → ℤ) (n : ℤ) :
    Module.finrank k (Graded.shiftedPiece 𝓐 d n) = ∑ i, Module.finrank k (𝓐 (n-d i)) := by
  rw [(shiftedPieceEquiv 𝓐 d n).finrank_eq, Module.finrank_pi_fintype]

lemma hasSum_shifted_polynomial (k : Type*) [Field k] (σ : Type*) [Fintype σ]
    (d : ℤ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℤ => (Module.finrank k (Graded.polynomialGrading k σ (n-d)) : ℝ) * q^n)
      (q^d * (1-q)⁻¹ ^ Fintype.card σ) := by
  apply (Equiv.addRight d).hasSum_iff.mp
  have h := (hasSum_polynomial k σ hq.le hq1).mul_left (q^d)
  apply h.congr_fun
  intro n
  change (Module.finrank k (Graded.polynomialGrading k σ (n+d-d)) : ℝ) * q^(n+d) = _
  rw [add_sub_cancel_right, zpow_add₀ hq.ne']
  ring

/-- Convergent Hilbert series and its normalization for the actual shifted free module. -/
theorem hasSum_shiftedFree (k : Type*) [Field k] (σ : Type*) [Fintype σ]
    {ι : Type*} [Fintype ι] (d : ι → ℤ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℤ =>
      (Module.finrank k (Graded.shiftedPiece (Graded.polynomialGrading k σ) d n) : ℝ) * q^n)
      ((∑ i, q^(d i)) * (1-q)⁻¹ ^ Fintype.card σ) := by
  have h := hasSum_sum (s := Finset.univ)
    (fun i _ => hasSum_shifted_polynomial k σ (d i) hq hq1)
  rw [← Finset.sum_mul] at h
  apply h.congr_fun
  intro n
  rw [shiftedPiece_finrank, Nat.cast_sum, Finset.sum_mul]


section FiniteModule
variable {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type*} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- Any finite graded module admits a finite homogeneous free cover. No projectivity is assumed. -/
theorem exists_finite_graded_cover [Module.Finite A M]
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul 𝓐 𝓜] :
    ∃ (ι : Type um), Finite ι ∧ ∃ (d : ι → ℤ) (f : (ι → A) →ₗ[A] M),
      Function.Surjective f ∧ ∀ n v, v ∈ Graded.shiftedPiece 𝓐 d n → f v ∈ 𝓜 n := by
  classical
  obtain ⟨t,ht,hd⟩ := Graded.exists_finite_homogeneous_generators (A := A) 𝓜
  choose d hd using fun i : t => hd i.val i.property
  have hspan : Submodule.span A (Set.range fun i : t => i.val) = ⊤ := by simpa using ht
  refine ⟨t, inferInstance, d, Fintype.linearCombination A (fun i : t => i.val), ?_, ?_⟩
  · intro m
    exact (Submodule.mem_span_range_iff_exists_fun A).mp (hspan ▸ Submodule.mem_top)
  · intro n v hv
    change (∑ i, v i • (i : M)) ∈ 𝓜 n
    apply Submodule.sum_mem
    intro i _
    simpa using SetLike.GradedSMul.smul_mem (hv i) (hd i)

def degreeMap (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n) (n : ℤ) :
    𝓜 n →ₗ[k] 𝓝 n :=
  LinearMap.codRestrict (𝓝 n) ((f.restrictScalars k).comp (𝓜 n).subtype)
    (fun m => hf n m m.property)

lemma degreeMap_surjective
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n)
    (hs : Function.Surjective f) (n : ℤ) : Function.Surjective (degreeMap 𝓜 𝓝 f hf n) := by
  intro m
  obtain ⟨v,hv⟩ := hs m.val
  refine ⟨DirectSum.decompose 𝓜 v n, ?_⟩
  apply Subtype.ext
  change f (Graded.component 𝓜 n v) = m.val
  have h := Graded.map_component 𝓜 𝓝 f 0 (by simpa using hf) n v
  rw [sub_zero, hv] at h
  exact h.symm.trans (DirectSum.decompose_of_mem_same 𝓝 m.property)
end FiniteModule

lemma term_top {M : Type um} [AddCommGroup M] [Module k M]
    (𝓜 : ℤ → Submodule k M) (q : ℝ) (n : ℤ) :
    term 𝓜 ⊤ q n = (Module.finrank k (𝓜 n) : ℝ)*q^n := by
  rw [term, piece, Submodule.comap_top, finrank_top]

section PolynomialModule
variable (k : Type uk) [Field k] (σ : Type ua) [Fintype σ]
  {M : Type um} [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [IsScalarTower k (MvPolynomial σ k) M] [Module.Finite (MvPolynomial σ k) M]
  (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
  [SetLike.GradedSMul (Graded.polynomialGrading k σ) 𝓜]

include σ

/-- Finiteness of every genuine homogeneous piece, not an extra assumption on the Hilbert series. -/
theorem polynomialModule_piece_finite (n : ℤ) : Module.Finite k (𝓜 n) := by
  classical
  obtain ⟨ι,hι,d,f,hs,hf⟩ := exists_finite_graded_cover (Graded.polynomialGrading k σ) 𝓜
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  let : DirectSum.Decomposition (Graded.shiftedPiece (Graded.polynomialGrading k σ) d) :=
    (Graded.shifted_isInternal (Graded.polynomialGrading k σ) d).chooseDecomposition
  exact Module.Finite.of_surjective
    (degreeMap (Graded.shiftedPiece (Graded.polynomialGrading k σ) d) 𝓜 f hf n)
    (degreeMap_surjective _ _ f hf hs n)

/-- Every finite graded module over the actual finite polynomial ring has a convergent
Hilbert series at every `0<q<1`, even when it is not free. -/
theorem summable_polynomialModule {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Summable (fun n : ℤ => (Module.finrank k (𝓜 n) : ℝ)*q^n) := by
  classical
  obtain ⟨ι,hι,d,f,hs,hf⟩ := exists_finite_graded_cover (Graded.polynomialGrading k σ) 𝓜
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  let : DirectSum.Decomposition (Graded.shiftedPiece (Graded.polynomialGrading k σ) d) :=
    (Graded.shifted_isInternal (Graded.polynomialGrading k σ) d).chooseDecomposition
  apply (hasSum_shiftedFree k σ d hq hq1).summable.of_nonneg_of_le
  · intro n
    exact mul_nonneg (Nat.cast_nonneg _) (zpow_nonneg hq.le _)
  · intro n
    apply mul_le_mul_of_nonneg_right _ (zpow_nonneg hq.le _)
    exact_mod_cast LinearMap.finrank_le_finrank_of_surjective
      (degreeMap_surjective (Graded.shiftedPiece (Graded.polynomialGrading k σ) d) 𝓜 f hf hs n)

/-- Convergence for every submodule in the fixed finite graded ambient module. -/
theorem summable_term (S : Submodule k M) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Summable (term 𝓜 S q) := by
  let : ∀ n, Module.Finite k (𝓜 n) := polynomialModule_piece_finite k σ 𝓜
  have heq : term 𝓜 ⊤ q = fun n : ℤ => (Module.finrank k (𝓜 n) : ℝ)*q^n :=
    funext (term_top 𝓜 q)
  have htop : Summable (term 𝓜 ⊤ q) := by
    rw [heq]
    exact summable_polynomialModule k σ 𝓜 hq hq1
  exact summable_of_le 𝓜 le_top hq htop

/-- Global detection, now with all the manuscript's finite-polynomial-ring hypotheses supplied. -/
theorem polynomial_eq_of_value_eq {S T : Submodule k M}
    (h : S ≤ T) (hhom : ∀ n m, m ∈ T → Graded.component 𝓜 n m ∈ T)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hv : value 𝓜 S q = value 𝓜 T q) : S = T := by
  let : ∀ n, Module.Finite k (𝓜 n) := polynomialModule_piece_finite k σ 𝓜
  exact eq_of_value_eq 𝓜 h hhom hq (summable_term k σ 𝓜 T hq hq1) hv
end PolynomialModule

section HomogeneousBasis
variable {σ : Type ua} [Fintype σ]
  {M : Type um} [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [IsScalarTower k (MvPolynomial σ k) M]
  (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
  [SetLike.GradedSMul (Graded.polynomialGrading k σ) 𝓜]
  {ι : Type ui} [Fintype ι] (b : Module.Basis ι (MvPolynomial σ k) M)
  (d : ι → ℤ) (hd : ∀ i, b i ∈ 𝓜 (d i))

include hd

omit [Fintype σ] [IsScalarTower k (MvPolynomial σ k) M] [DirectSum.Decomposition 𝓜] in
lemma basis_equivFun_symm_graded (n : ℤ) (v : ι → MvPolynomial σ k)
    (hv : v ∈ Graded.shiftedPiece (Graded.polynomialGrading k σ) d n) :
    b.equivFun.symm v ∈ 𝓜 n := by
  rw [b.equivFun_symm_apply]
  apply Submodule.sum_mem
  intro i _
  simpa using SetLike.GradedSMul.smul_mem (hv i) (hd i)

lemma finrank_homogeneous_basis (n : ℤ) :
    Module.finrank k (𝓜 n) =
      ∑ i, Module.finrank k (Graded.polynomialGrading k σ (n-d i)) := by
  let : DirectSum.Decomposition (Graded.shiftedPiece (Graded.polynomialGrading k σ) d) :=
    (Graded.shifted_isInternal (Graded.polynomialGrading k σ) d).chooseDecomposition
  let f := degreeMap (Graded.shiftedPiece (Graded.polynomialGrading k σ) d) 𝓜
    b.equivFun.symm.toLinearMap (basis_equivFun_symm_graded 𝓜 b d hd) n
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply b.equivFun.symm.injective
      exact congrArg Subtype.val h
    · exact degreeMap_surjective _ _ b.equivFun.symm.toLinearMap
        (basis_equivFun_symm_graded 𝓜 b d hd) b.equivFun.symm.surjective n
  rw [← (LinearEquiv.ofBijective f hf).finrank_eq]
  exact shiftedPiece_finrank _ d n

/-- The precise Hilbert normalization for a finite homogeneous basis, with the source's
convention that a generator in degree `d` contributes `q^d`. -/
theorem hasSum_homogeneous_basis {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℤ => (Module.finrank k (𝓜 n) : ℝ)*q^n)
      ((∑ i, q^(d i)) * (1-q)⁻¹ ^ Fintype.card σ) := by
  apply (hasSum_shiftedFree k σ d hq hq1).congr_fun
  intro n
  rw [finrank_homogeneous_basis 𝓜 b d hd, shiftedPiece_finrank]
end HomogeneousBasis


end KLInvariance.Hilbert


end


section

namespace KLInvariance.Hilbert
open _root_.OAI.KLInvariance.Graded
universe uk ua um un
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type un} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- The actual degreewise kernel, not merely an equality of dimensions. -/
def degreeKernelEquiv (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n) (n : ℤ) :
    subPiece 𝓜 (LinearMap.ker f) n ≃ₗ[k] LinearMap.ker (degreeMap 𝓜 𝓝 f hf n) where
  toFun m := ⟨⟨m.val.val,m.property⟩, by
    apply Subtype.ext
    exact m.val.property⟩
  invFun m := ⟨⟨m.val.val, by
    have h := congrArg Subtype.val m.property
    exact h⟩,m.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem finrank_exact
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    [∀ n, Module.Finite k (𝓜 n)]
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n)
    (hs : Function.Surjective f) (n : ℤ) :
    Module.finrank k (𝓜 n) = Module.finrank k (subPiece 𝓜 (LinearMap.ker f) n) +
      Module.finrank k (𝓝 n) := by
  have h := LinearMap.finrank_range_add_finrank_ker (degreeMap 𝓜 𝓝 f hf n)
  rw [LinearMap.range_eq_top.mpr (degreeMap_surjective 𝓜 𝓝 f hf hs n),finrank_top,
    ← (degreeKernelEquiv 𝓜 𝓝 f hf n).finrank_eq] at h
  omega


 theorem value_exact
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    [∀ n, Module.Finite k (𝓜 n)]
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n)
    (hs : Function.Surjective f) (q : ℝ)
    (hK : Summable (term (subPiece 𝓜 (LinearMap.ker f)) ⊤ q))
    (hN : Summable (term 𝓝 ⊤ q)) :
    value 𝓜 ⊤ q = value (subPiece 𝓜 (LinearMap.ker f)) ⊤ q + value 𝓝 ⊤ q := by
  have ht : term 𝓜 ⊤ q = fun n => term (subPiece 𝓜 (LinearMap.ker f)) ⊤ q n +
      term 𝓝 ⊤ q n := by
    funext n
    rw [term_top,term_top,term_top,finrank_exact 𝓜 𝓝 f hf hs n,Nat.cast_add,add_mul]
  rw [value,ht,hK.tsum_add hN]
  rfl

/-- Finite degreewise exactness supplies convergence of both terms; no
free-module hypothesis is used. -/
 theorem value_exact_of_summable
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    [∀ n, Module.Finite k (𝓜 n)]
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n)
    (hs : Function.Surjective f) {q : ℝ} (hq : 0 < q)
    (hM : Summable (term 𝓜 ⊤ q)) :
    value 𝓜 ⊤ q = value (subPiece 𝓜 (LinearMap.ker f)) ⊤ q + value 𝓝 ⊤ q := by
  apply value_exact 𝓜 𝓝 f hf hs q
  · apply hM.of_nonneg_of_le
    · intro n
      rw [term_top]
      positivity
    · intro n
      rw [term_top,term_top]
      apply mul_le_mul_of_nonneg_right _ (zpow_nonneg hq.le _)
      exact_mod_cast (show Module.finrank k (subPiece 𝓜 (LinearMap.ker f) n) ≤
        Module.finrank k (𝓜 n) by rw [finrank_exact 𝓜 𝓝 f hf hs n]; omega)
  · apply hM.of_nonneg_of_le
    · intro n
      rw [term_top]
      positivity
    · intro n
      rw [term_top,term_top]
      apply mul_le_mul_of_nonneg_right _ (zpow_nonneg hq.le _)
      exact_mod_cast (show Module.finrank k (𝓝 n) ≤ Module.finrank k (𝓜 n) by
        rw [finrank_exact 𝓜 𝓝 f hf hs n]; omega)

end KLInvariance.Hilbert

end


section

namespace KLInvariance.Hilbert
open _root_.OAI.KLInvariance.Graded
universe uk ua um un
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type un} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

 def subPieceEquiv (𝓜 : ℤ → Submodule k M) (S : Submodule A M) (n : ℤ) :
    subPiece 𝓜 S n ≃ₗ[k] piece 𝓜 (S.restrictScalars k) n where
  toFun v := ⟨⟨v.val.val,v.property⟩,v.val.property⟩
  invFun v := ⟨⟨v.val.val,v.property⟩,v.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem term_subPiece (𝓜 : ℤ → Submodule k M) (S : Submodule A M) (q : ℝ) (n : ℤ) :
    term (subPiece 𝓜 S) ⊤ q n = term 𝓜 (S.restrictScalars k) q n := by
  rw [term_top,term,(subPieceEquiv 𝓜 S n).finrank_eq]

 theorem value_subPiece (𝓜 : ℤ → Submodule k M) (S : Submodule A M) (q : ℝ) :
    value (subPiece 𝓜 S) ⊤ q = value 𝓜 (S.restrictScalars k) q := by
  exact tsum_congr (term_subPiece 𝓜 S q)

 def imagePieceMap (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    (S : Submodule A M) (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n)
    (n : ℤ) : subPiece 𝓜 S n →ₗ[k] subPiece 𝓝 (S.map f) n where
  toFun v := ⟨⟨f v.val.val,Submodule.mem_map.mpr ⟨_,v.val.property,rfl⟩⟩,
    hf n v.val.val v.property⟩
  map_add' _ _ := by ext; exact map_add f _ _
  map_smul' c v := by ext; exact (f.restrictScalars k).map_smul c v.val.val

 theorem imagePieceMap_surjective
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n) (n : ℤ) :
    Function.Surjective (imagePieceMap 𝓜 𝓝 S f hf n) := by
  rintro ⟨⟨m,hm⟩,hgrad⟩
  obtain ⟨v,hv,rfl⟩ := Submodule.mem_map.mp hm
  refine ⟨⟨⟨component 𝓜 n v,hS n v hv⟩,(DirectSum.decompose 𝓜 v n).property⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change f (component 𝓜 n v) = f v
  have hh := map_component 𝓜 𝓝 f 0 (by simpa using hf) n v
  rw [sub_zero] at hh
  rw [← hh]
  exact DirectSum.decompose_of_mem_same 𝓝 hgrad

 def imageKernelEquiv (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    (S : Submodule A M) (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n)
    (n : ℤ) : subPiece 𝓜 (S ⊓ LinearMap.ker f) n ≃ₗ[k]
      LinearMap.ker (imagePieceMap 𝓜 𝓝 S f hf n) where
  toFun v := ⟨⟨⟨v.val.val,v.val.property.1⟩,v.property⟩,by
    apply Subtype.ext
    apply Subtype.ext
    exact v.val.property.2⟩
  invFun v := ⟨⟨v.val.val.val,⟨v.val.val.property,by
    have h := congrArg (fun z => z.val.val) v.property
    exact h⟩⟩,v.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem finrank_image_exact
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    [∀ n, Module.Finite k (𝓜 n)]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n) (n : ℤ) :
    Module.finrank k (piece 𝓜 (S.restrictScalars k) n) =
      Module.finrank k (piece 𝓜 ((S ⊓ LinearMap.ker f).restrictScalars k) n) +
      Module.finrank k (piece 𝓝 ((S.map f).restrictScalars k) n) := by
  let : Module.Finite k (subPiece 𝓜 S n) := Module.Finite.of_surjective
    (subPieceEquiv 𝓜 S n).symm.toLinearMap (subPieceEquiv 𝓜 S n).symm.surjective
  have h := LinearMap.finrank_range_add_finrank_ker (imagePieceMap 𝓜 𝓝 S f hf n)
  rw [LinearMap.range_eq_top.mpr (imagePieceMap_surjective 𝓜 𝓝 S hS f hf n),finrank_top,
    ← (imageKernelEquiv 𝓜 𝓝 S f hf n).finrank_eq,
    (subPieceEquiv 𝓜 S n).finrank_eq,
    (subPieceEquiv 𝓜 (S ⊓ LinearMap.ker f) n).finrank_eq,
    (subPieceEquiv 𝓝 (S.map f) n).finrank_eq] at h
  omega

/-- Removing a kernel condition adds exactly the Hilbert value of its
embedded restriction image. No freeness of the source kernel is used. -/
 theorem value_image_exact
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    [∀ n, Module.Finite k (𝓜 n)]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n)
    {q : ℝ} (hq : 0 < q) (hs : Summable (term 𝓜 (S.restrictScalars k) q)) :
    value 𝓜 (S.restrictScalars k) q =
      value 𝓜 ((S ⊓ LinearMap.ker f).restrictScalars k) q +
      value 𝓝 ((S.map f).restrictScalars k) q := by
  have ht (n : ℤ) : term 𝓜 (S.restrictScalars k) q n =
      term 𝓜 ((S ⊓ LinearMap.ker f).restrictScalars k) q n +
      term 𝓝 ((S.map f).restrictScalars k) q n := by
    unfold term
    rw [finrank_image_exact 𝓜 𝓝 S hS f hf n,Nat.cast_add,add_mul]
  have hk : Summable (term 𝓜 ((S ⊓ LinearMap.ker f).restrictScalars k) q) := by
    apply hs.of_nonneg_of_le
    · exact fun n => term_nonneg _ _ hq n
    · intro n
      rw [ht n]
      exact le_add_of_nonneg_right (term_nonneg _ _ hq n)
  have hi : Summable (term 𝓝 ((S.map f).restrictScalars k) q) := by
    apply hs.of_nonneg_of_le
    · exact fun n => term_nonneg _ _ hq n
    · intro n
      rw [ht n]
      exact le_add_of_nonneg_left (term_nonneg _ _ hq n)
  unfold value
  rw [show term 𝓜 (S.restrictScalars k) q = _ from funext ht,hk.tsum_add hi]

end KLInvariance.Hilbert

end


section


end

end OAI
