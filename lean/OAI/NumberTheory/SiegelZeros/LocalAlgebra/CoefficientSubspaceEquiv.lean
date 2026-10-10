import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Hilbert.HilbertSeries

namespace OAI

namespace SiegelZeros

section
open scoped BigOperators
namespace WeightedTorusJets

variable {K A M ι : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M] [Fintype ι]

noncomputable def coefficientSubspaceEquiv (C : Submodule K A) (P : Submodule K M)
    (v : ι → M) (hv : LinearIndependent A v)
    (hmem : ∀ c : ι → C, ∑ i, (c i : A) • v i ∈ P)
    (hrep : ∀ y ∈ P, ∃ c : ι → C, ∑ i, (c i : A) • v i = y) :
    (ι → C) ≃ₗ[K] P := by
  let f : (ι → C) →ₗ[K] M :=
    ((Fintype.linearCombination A v).restrictScalars K).comp
      (LinearMap.pi fun i => C.subtype.comp (LinearMap.proj i))
  refine LinearEquiv.ofBijective (f.codRestrict P hmem) ⟨?_, ?_⟩
  · intro c d hcd
    have heq : ∑ i, (c i : A) • v i = ∑ i, (d i : A) • v i :=
      congrArg Subtype.val hcd
    funext i
    exact Subtype.ext (hv.eq_coords_of_eq heq i)
  · intro y
    obtain ⟨c, hc⟩ := hrep y y.property
    exact ⟨c, Subtype.ext hc⟩

@[simp]
theorem coefficientSubspaceEquiv_apply (C : Submodule K A) (P : Submodule K M)
    (v : ι → M) (hv : LinearIndependent A v)
    (hmem : ∀ c : ι → C, ∑ i, (c i : A) • v i ∈ P)
    (hrep : ∀ y ∈ P, ∃ c : ι → C, ∑ i, (c i : A) • v i = y) (c : ι → C) :
    (coefficientSubspaceEquiv C P v hv hmem hrep c : M) = ∑ i, (c i : A) • v i :=
  rfl

theorem finrank_coefficient_subspace (C : Submodule K A) (P : Submodule K M)
    (v : ι → M) (hv : LinearIndependent A v)
    (hmem : ∀ c : ι → C, ∑ i, (c i : A) • v i ∈ P)
    (hrep : ∀ y ∈ P, ∃ c : ι → C, ∑ i, (c i : A) • v i = y) :
    Module.finrank K P = Fintype.card ι * Module.finrank K C := by
  rw [← (coefficientSubspaceEquiv C P v hv hmem hrep).finrank_eq]
  simp [Module.finrank]

end WeightedTorusJets

namespace WeightedTorusJets

theorem finrank_homogeneous_span {K A M : Type*} [Field K] [CommRing A]
    [Algebra K A] [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]
    (ℳ : ℕ → Submodule K M) [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {r D n : ℕ} (v : Fin r → M) (hv : ∀ i, v i ∈ ℳ D)
    (hlin : LinearIndependent A v) (hn : D ≤ n) :
    Module.finrank K ↥(ℳ n ⊓ (Submodule.span A (Set.range v)).restrictScalars K) =
      r * Module.finrank K (𝒜 (n - D)) := by
  simpa only [Fintype.card_fin] using finrank_coefficient_subspace (𝒜 (n - D))
    (ℳ n ⊓ (Submodule.span A (Set.range v)).restrictScalars K) v hlin
    (homogeneous_coefficients_sum_mem 𝒜 ℳ v hv hn)
    (fun y hy => exists_homogeneous_coefficients 𝒜 ℳ v hv hn y hy.1 hy.2)

end WeightedTorusJets

open scoped BigOperators DirectSum

namespace WeightedTorusJets.Geometry

theorem exists_finset_homogeneous_span_eq_top
    {A K M : Type*} [CommRing A] [Field K] [AddCommGroup M]
    [Module A M] [Module K M] [Module.Finite A M]
    (𝓜 : ℕ → Submodule K M) [DirectSum.Decomposition 𝓜] :
    ∃ s : Finset M, Submodule.span A (s : Set M) = ⊤ ∧
      ∀ x ∈ s, ∃ n, x ∈ 𝓜 n := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := M)
  let t := s.biUnion fun x => (DirectSum.decompose 𝓜 x).support.image
    fun n => (DirectSum.decompose 𝓜 x n : M)
  refine ⟨t, ?_, ?_⟩
  · apply top_unique
    rw [← hs]
    apply Submodule.span_le.mpr
    intro x hx
    rw [← DirectSum.sum_support_decompose 𝓜 x]
    apply Submodule.sum_mem
    intro n hn
    apply Submodule.subset_span
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨n, hn, rfl⟩⟩
  · intro x hx
    obtain ⟨y, _, hy⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨n, (DirectSum.decompose 𝓜 y n).property⟩

theorem exists_homogeneous_generic_basis
    {A K M F N : Type*} [CommRing A] [Field K] [Field F]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module K M]
    [Algebra A F] [IsFractionRing A F] [Module A N] [Module F N]
    [IsScalarTower A F N] [Module.Finite A M]
    (𝓜 : ℕ → Submodule K M) [DirectSum.Decomposition 𝓜]
    (f : M →ₗ[A] N) [IsLocalizedModule (nonZeroDivisors A) f] :
    ∃ v : Fin (Module.finrank F N) → M,
      ∃ b : Module.Basis (Fin (Module.finrank F N)) F N,
        (∀ i, f (v i) = b i) ∧
        (∀ i, ∃ n, v i ∈ 𝓜 n) ∧ LinearIndependent A v := by
  classical
  have : Module.Finite F N :=
    Module.Finite.of_isLocalizedModule (nonZeroDivisors A) (Rₚ := F) f
  have : FaithfulSMul A F :=
    (faithfulSMul_iff_algebraMap_injective A F).mpr (IsFractionRing.injective A F)
  obtain ⟨s, hs, hhom⟩ := exists_finset_homogeneous_span_eq_top (A := A) 𝓜
  have hspan : Submodule.span F (f '' (s : Set M)) = ⊤ :=
    span_eq_top_of_isLocalizedModule F (nonZeroDivisors A) f hs
  let ι := (linearIndepOn_empty F (id : N → N)).extend
    (Set.empty_subset (f '' (s : Set M)))
  let b₀ : Module.Basis ι F N := Module.Basis.ofSpan hspan.ge
  let := Module.Finite.finite_basis b₀
  let := Fintype.ofFinite ι
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b₀).symm
  let b := b₀.reindex e
  have hpre (i : Fin (Module.finrank F N)) : ∃ x ∈ s, f x = b i := by
    apply Module.Basis.ofSpan_subset hspan.ge
    refine ⟨e.symm i, ?_⟩
    exact (Module.Basis.reindex_apply b₀ e i).symm
  choose v hv hvf using hpre
  refine ⟨v, b, hvf, fun i => hhom _ (hv i), ?_⟩
  have hcomp : f ∘ v = b := funext hvf
  apply LinearIndependent.of_comp f
  rw [hcomp]
  exact b.linearIndependent.restrict_scalars' A

theorem fraction_finrank_eq_pos
    (B A K L : Type*) [CommRing B] [IsDomain B] [CommRing A] [IsDomain A]
    [Field K] [Field L] [Algebra B A] [Algebra B K] [Algebra A L] [Algebra B L]
    [Module K L] [IsScalarTower B K L] [IsScalarTower B A L]
    [IsFractionRing B K] [IsFractionRing A L]
    [Module.Finite B A] [Module.IsTorsionFree B A] :
    Module.finrank K L = Module.finrank B A ∧ 0 < Module.finrank K L := by
  have heq := IsFractionRing.finrank_eq B K A L
  exact ⟨heq, heq.symm ▸ Module.finrank_pos (R := B) (M := A)⟩

theorem finrank_quotient_span_eq_zero_of_full_rank
    {A M : Type*} [CommRing A] [IsDomain A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] {n : ℕ} {v : Fin n → M}
    (hv : LinearIndependent A v) (hn : n = Module.finrank A M) :
    Module.finrank A (M ⧸ Submodule.span A (Set.range v)) = 0 := by
  have h := (Submodule.span A (Set.range v)).finrank_quotient_add_finrank
  rw [finrank_span_eq_card hv, Fintype.card_fin] at h
  omega

theorem generic_fiber_finrank_eq
    {A M F N : Type*} [CommRing A] [Field F]
    [AddCommGroup M] [AddCommGroup N] [Module A M]
    [Algebra A F] [IsFractionRing A F] [Module A N] [Module F N]
    [IsScalarTower A F N] (f : M →ₗ[A] N)
    [IsLocalizedModule (nonZeroDivisors A) f] :
    Module.finrank F N = Module.finrank A M :=
  (IsLocalization.finrank_eq F (nonZeroDivisors A) le_rfl).trans
    (IsLocalizedModule.finrank_eq (nonZeroDivisors A) f le_rfl)

end WeightedTorusJets.Geometry

open scoped BigOperators

namespace WeightedTorusJets.Geometry

theorem exists_common_degree_independent
    {K A M ι : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [AddCommGroup M] [Module K M] [Module A M] [Fintype ι]
    (𝓐 : ℕ → Submodule K A) [GradedAlgebra 𝓐]
    (𝓜 : ℕ → Submodule K M)
    [SetLike.GradedSMul 𝓐 𝓜]
    {a : A} (ha0 : a ≠ 0) (ha1 : a ∈ 𝓐 1)
    {v : ι → M} (hv : LinearIndependent A v)
    (hhom : ∀ i, ∃ n, v i ∈ 𝓜 n) :
    ∃ D : ℕ, ∃ w : ι → M, LinearIndependent A w ∧ ∀ i, w i ∈ 𝓜 D := by
  classical
  choose e he using hhom
  let D := Finset.univ.sup e
  let w := fun i => a ^ (D - e i) • v i
  refine ⟨D, w, ?_, ?_⟩
  · apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    have hc' : ∑ j, (c j * a ^ (D - e j)) • v j = 0 := by
      simpa only [mul_smul] using hc
    exact (mul_eq_zero.mp (Fintype.linearIndependent_iff.mp hv _ hc' i)).resolve_right
      (pow_ne_zero _ ha0)
  · intro i
    have hei : e i ≤ D := Finset.le_sup (Finset.mem_univ i)
    have ha : a ^ (D - e i) ∈ 𝓐 (D - e i) := by
      simpa using SetLike.pow_mem_graded (D - e i) ha1
    have hw := SetLike.GradedSMul.smul_mem ha (he i)
    simpa only [vadd_eq_add, Nat.sub_add_cancel hei] using hw



variable {K A M : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [Module.IsTorsionFree A M]
    (𝓐 : ℕ → Submodule K A) (𝓜 : ℕ → Submodule K M)
    [SetLike.GradedSMul 𝓐 𝓜]

theorem finrank_gradedPiece_le_shifted_submodule
    (N : Submodule A M) {b : A} {E : ℕ} (hb0 : b ≠ 0) (hb : b ∈ 𝓐 E)
    (hN : ∀ m : M, b • m ∈ N) (n : ℕ)
    [Module.Finite K (𝓜 (E + n))] :
    Module.finrank K (𝓜 n) ≤
      Module.finrank K ↥((𝓜 (E + n)) ⊓ N.restrictScalars K) := by
  have hle : (𝓜 (E + n)) ⊓ N.restrictScalars K ≤ 𝓜 (E + n) := inf_le_left
  have : Module.Finite K ↥((𝓜 (E + n)) ⊓ N.restrictScalars K) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  let f : 𝓜 n →ₗ[K] ↥((𝓜 (E + n)) ⊓ N.restrictScalars K) :=
    { toFun m := ⟨b • (m : M),
        ⟨by
          change b • (m : M) ∈ 𝓜 (E + n)
          exact SetLike.GradedSMul.smul_mem hb m.property,
          hN m⟩⟩
      map_add' m m' := by ext; exact smul_add b (m : M) m'
      map_smul' c m := by ext; exact smul_comm b c (m : M) }
  apply LinearMap.finrank_le_finrank_of_injective (f := f)
  intro x y h
  apply Subtype.ext
  exact smul_right_injective M hb0 (congrArg Subtype.val h)

omit [IsDomain A] [Module.IsTorsionFree A M] in

theorem finrank_gradedSubmodule_le
    (N : Submodule A M) (n : ℕ) [Module.Finite K (𝓜 n)] :
    Module.finrank K ↥((𝓜 n) ⊓ N.restrictScalars K) ≤ Module.finrank K (𝓜 n) :=
  Submodule.finrank_mono inf_le_left

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

theorem exists_hilbert_finrank_sandwich
    {K A M : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [Module.Finite A M] [Module.IsTorsionFree A M]
    (𝓐 : ℕ → Submodule K A) [GradedAlgebra 𝓐]
    (𝓜 : ℕ → Submodule K M) [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul 𝓐 𝓜] [∀ n, Module.Finite K (𝓜 n)]
    {a : A} (ha0 : a ≠ 0) (ha1 : a ∈ 𝓐 1)
    (d : ℕ) (hdim : ∀ n, Module.finrank K (𝓐 n) = (n + d).choose d) :
    ∃ D E : ℕ, ∀ n, D ≤ n →
      Module.finrank A M * ((n - D + d).choose d) ≤ Module.finrank K (𝓜 n) ∧
      Module.finrank K (𝓜 n) ≤
        Module.finrank A M * ((n + E - D + d).choose d) := by
  classical
  let f := LocalizedModule.mkLinearMap (nonZeroDivisors A) M
  obtain ⟨v, _, _, hhom, hv⟩ := exists_homogeneous_generic_basis
    (F := FractionRing A) 𝓜 f
  have hr := generic_fiber_finrank_eq (F := FractionRing A) f
  obtain ⟨D, w, hw, hwD⟩ := exists_common_degree_independent 𝓐 𝓜 ha0 ha1 hv hhom
  let N := Submodule.span A (Set.range w)
  have hN : N.IsHomogeneous 𝓜 := by
    apply WeightedTorusJets.homogeneous_submodule_span 𝓐 𝓜
    rintro x ⟨i, rfl⟩
    exact ⟨D, hwD i⟩
  have hzero : Module.finrank A (M ⧸ N) = 0 :=
    finrank_quotient_span_eq_zero_of_full_rank hw hr
  have hrank : Module.rank A (M ⧸ N) = 0 := by
    rw [← Module.finrank_eq_rank, hzero, Nat.cast_zero]
  obtain ⟨b, hb0, ⟨E, hbE⟩, hbN⟩ :=
    WeightedTorusJets.exists_homogeneous_annihilator_of_rank_zero 𝓐 𝓜 N hN hrank
  refine ⟨D, E, fun n hn => ⟨?_, ?_⟩⟩
  · have h := finrank_gradedSubmodule_le 𝓜 N n
    change Module.finrank K ↥(𝓜 n ⊓ (Submodule.span A (Set.range w)).restrictScalars K) ≤ _ at h
    rw [WeightedTorusJets.finrank_homogeneous_span 𝓐 𝓜 w hwD hw hn, hr, hdim] at h
    exact h
  · have h := finrank_gradedPiece_le_shifted_submodule 𝓐 𝓜 N hb0 hbE hbN n
    change _ ≤ Module.finrank K
      ↥(𝓜 (E + n) ⊓ (Submodule.span A (Set.range w)).restrictScalars K) at h
    rw [WeightedTorusJets.finrank_homogeneous_span 𝓐 𝓜 w hwD hw (by omega), hr, hdim] at h
    simpa only [Nat.add_comm E n] using h

end WeightedTorusJets.Geometry

end

namespace WeightedTorusJets.Geometry

open Filter _root_.Polynomial

theorem leadingCoeff_nonneg_of_eventually_nat_eval_nonneg (P : Polynomial ℚ)
    (hpos : ∀ᶠ n : ℕ in atTop, 0 ≤ P.eval (n : ℚ)) : 0 ≤ P.leadingCoeff := by
  by_cases hP : P = 0
  · simp [hP]
  · exact (leadingCoeff_pos_of_eventually_nat_eval_nonneg P hP hpos).le

theorem natDegree_leadingCoeff_eq_of_eventually_nat_eval_sandwich
    (P L U : Polynomial ℚ) (d : ℕ)
    (hL : L.natDegree = d) (hU : U.natDegree = d)
    (hLU : L.leadingCoeff = U.leadingCoeff) (hpos : 0 < L.leadingCoeff)
    (hlo : ∀ᶠ n : ℕ in atTop, L.eval (n : ℚ) ≤ P.eval (n : ℚ))
    (hhi : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) ≤ U.eval (n : ℚ)) :
    P.natDegree = d ∧ P.leadingCoeff = L.leadingCoeff := by
  have hlo' : ∀ᶠ n : ℕ in atTop, 0 ≤ (P - L).eval (n : ℚ) := by
    filter_upwards [hlo] with n hn
    simpa only [eval_sub] using sub_nonneg.mpr hn
  have hhi' : ∀ᶠ n : ℕ in atTop, 0 ≤ (U - P).eval (n : ℚ) := by
    filter_upwards [hhi] with n hn
    simpa only [eval_sub] using sub_nonneg.mpr hn
  have hcPL := leadingCoeff_nonneg_of_eventually_nat_eval_nonneg (P - L) hlo'
  have hcUP := leadingCoeff_nonneg_of_eventually_nat_eval_nonneg (U - P) hhi'
  have hLne : L ≠ 0 := leadingCoeff_ne_zero.mp hpos.ne'
  have hUne : U ≠ 0 := leadingCoeff_ne_zero.mp (hLU ▸ hpos.ne')
  have hdegreeLU : L.degree = U.degree := by
    rw [degree_eq_natDegree hLne, degree_eq_natDegree hUne, hL, hU]
  have hdegLP : L.degree ≤ P.degree := by
    by_contra h
    rw [leadingCoeff_sub_of_degree_lt' (lt_of_not_ge h)] at hcPL
    linarith
  have hdegPU : P.degree ≤ U.degree := by
    by_contra h
    have hUP : U.degree < P.degree := lt_of_not_ge h
    have hLP : L.degree < P.degree := hdegreeLU ▸ hUP
    rw [leadingCoeff_sub_of_degree_lt hLP] at hcPL
    rw [leadingCoeff_sub_of_degree_lt' hUP] at hcUP
    have hPne : P ≠ 0 := ne_zero_of_degree_gt hUP
    exact (leadingCoeff_ne_zero.mpr hPne) (by linarith)
  have hdeg : P.degree = L.degree := le_antisymm (hdegPU.trans_eq hdegreeLU.symm) hdegLP
  have hnat : P.natDegree = d := (natDegree_eq_natDegree hdeg).trans hL
  refine ⟨hnat, ?_⟩
  have coeff_nonneg (Q : Polynomial ℚ) (hQ : Q.natDegree ≤ d)
      (hQpos : ∀ᶠ n : ℕ in atTop, 0 ≤ Q.eval (n : ℚ)) : 0 ≤ Q.coeff d := by
    rcases hQ.eq_or_lt with h | h
    · rw [← h, coeff_natDegree]
      exact leadingCoeff_nonneg_of_eventually_nat_eval_nonneg Q hQpos
    · rw [coeff_eq_zero_of_natDegree_lt h]
  have hsub₁ : (P - L).natDegree ≤ d := by
    simpa only [hnat, hL, max_self] using natDegree_sub_le P L
  have hsub₂ : (U - P).natDegree ≤ d := by
    simpa only [hnat, hU, max_self] using natDegree_sub_le U P
  have hcoeff₁ := coeff_nonneg (P - L) hsub₁ hlo'
  have hcoeff₂ := coeff_nonneg (U - P) hsub₂ hhi'
  have hcoeffP : P.coeff d = P.leadingCoeff := by rw [← hnat, coeff_natDegree]
  have hcoeffL : L.coeff d = L.leadingCoeff := by rw [← hL, coeff_natDegree]
  have hcoeffU : U.coeff d = U.leadingCoeff := by rw [← hU, coeff_natDegree]
  rw [coeff_sub, hcoeffP, hcoeffL] at hcoeff₁
  rw [coeff_sub, hcoeffU, hcoeffP, ← hLU] at hcoeff₂
  linarith

theorem natDegree_leadingCoeff_eq_of_eventually_binomial_sandwich
    (P : Polynomial ℚ) (d D E r : ℕ) (hr : 0 < r)
    (hlo : ∀ᶠ n : ℕ in atTop,
      (r : ℚ) * ((n - D + d).choose d : ℚ) ≤ P.eval (n : ℚ))
    (hhi : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) ≤ (r : ℚ) * ((n + E - D + d).choose d : ℚ)) :
    P.natDegree = d ∧ P.leadingCoeff = (r : ℚ) / (d.factorial : ℚ) := by
  let L : Polynomial ℚ := (r : ℚ) • preHilbertPoly ℚ d D
  let U : Polynomial ℚ := (r : ℚ) •
    (preHilbertPoly ℚ d D).comp (Polynomial.X + Polynomial.C (E : ℚ))
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  have hL : L.natDegree = d := by
    dsimp [L]
    rw [natDegree_smul _ hr0, natDegree_preHilbertPoly]
  have hU : U.natDegree = d := by
    dsimp [U]
    rw [natDegree_smul _ hr0, natDegree_comp, natDegree_preHilbertPoly,
      natDegree_add_C, natDegree_X, mul_one]
  have hcL : L.leadingCoeff = (r : ℚ) / (d.factorial : ℚ) := by
    rw [leadingCoeff, hL]
    change ((r : ℚ) • preHilbertPoly ℚ d D).coeff d = _
    rw [coeff_smul, coeff_preHilbertPoly_self]
    rfl
  have hcU : U.leadingCoeff = (r : ℚ) / (d.factorial : ℚ) := by
    have hcompdeg : ((preHilbertPoly ℚ d D).comp (X + C (E : ℚ))).natDegree = d := by
      rw [natDegree_comp, natDegree_preHilbertPoly, natDegree_add_C, natDegree_X, mul_one]
    have hcompcoeff : ((preHilbertPoly ℚ d D).comp (X + C (E : ℚ))).coeff d =
        ((preHilbertPoly ℚ d D).comp (X + C (E : ℚ))).leadingCoeff := by
      calc
        _ = ((preHilbertPoly ℚ d D).comp (X + C (E : ℚ))).coeff
            ((preHilbertPoly ℚ d D).comp (X + C (E : ℚ))).natDegree :=
          congrArg ((preHilbertPoly ℚ d D).comp (X + C (E : ℚ))).coeff hcompdeg.symm
        _ = _ := coeff_natDegree
    rw [leadingCoeff, hU]
    change ((r : ℚ) • (preHilbertPoly ℚ d D).comp (X + C (E : ℚ))).coeff d = _
    rw [coeff_smul, hcompcoeff,
      leadingCoeff_comp (by rw [natDegree_add_C, natDegree_X]; decide),
      leadingCoeff_preHilbertPoly, leadingCoeff_X_add_C, one_pow, mul_one]
    rfl
  have hLpos : 0 < L.leadingCoeff := by rw [hcL]; positivity
  have hL_eval : ∀ᶠ n : ℕ in atTop, L.eval (n : ℚ) ≤ P.eval (n : ℚ) := by
    filter_upwards [hlo, eventually_ge_atTop D] with n hn hDn
    have hind : n + d - D = n - D + d := by omega
    simpa only [L, eval_smul, smul_eq_mul,
      preHilbertPoly_eq_choose_add_sub ℚ d (by omega : D ≤ n + d), hind] using hn
  have hU_eval : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) ≤ U.eval (n : ℚ) := by
    filter_upwards [hhi, eventually_ge_atTop D] with n hn hDn
    have hind : n + E + d - D = n + E - D + d := by omega
    simpa only [U, eval_smul, smul_eq_mul, eval_comp, eval_add, eval_X, eval_C,
      ← Nat.cast_add,
      preHilbertPoly_eq_choose_add_sub ℚ d (by omega : D ≤ n + E + d), hind] using hn
  obtain ⟨hdeg, hlc⟩ := natDegree_leadingCoeff_eq_of_eventually_nat_eval_sandwich
    P L U d hL hU (hcL.trans hcU.symm) hLpos hL_eval hU_eval
  exact ⟨hdeg, hlc.trans hcL⟩

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open Filter

theorem hilbertPolynomial_degree_coefficient_eq_rank
    {K A M : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [Module.Finite A M] [Module.IsTorsionFree A M] [Nontrivial M]
    (𝓐 : ℕ → Submodule K A) [GradedAlgebra 𝓐]
    (𝓜 : ℕ → Submodule K M) [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul 𝓐 𝓜] [∀ n, Module.Finite K (𝓜 n)]
    {a : A} (ha0 : a ≠ 0) (ha1 : a ∈ 𝓐 1)
    (d : ℕ) (hdim : ∀ n, Module.finrank K (𝓐 n) = (n + d).choose d)
    (P : Polynomial ℚ)
    (hP : ∀ᶠ n : ℕ in atTop, (Module.finrank K (𝓜 n) : ℚ) = P.eval (n : ℚ)) :
    P.natDegree = d ∧ (d.factorial : ℚ) * P.leadingCoeff = (Module.finrank A M : ℚ) := by
  obtain ⟨D, E, hDE⟩ := exists_hilbert_finrank_sandwich 𝓐 𝓜 ha0 ha1 d hdim
  have hlo : ∀ᶠ n : ℕ in atTop,
      (Module.finrank A M : ℚ) * ((n - D + d).choose d : ℚ) ≤ P.eval (n : ℚ) := by
    filter_upwards [hP, eventually_ge_atTop D] with n hPn hn
    rw [← hPn]
    exact_mod_cast (hDE n hn).1
  have hhi : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) ≤ (Module.finrank A M : ℚ) * ((n + E - D + d).choose d : ℚ) := by
    filter_upwards [hP, eventually_ge_atTop D] with n hPn hn
    rw [← hPn]
    exact_mod_cast (hDE n hn).2
  obtain ⟨hdeg, hlc⟩ := natDegree_leadingCoeff_eq_of_eventually_binomial_sandwich
    P d D E (Module.finrank A M) (Module.finrank_pos (R := A) (M := M)) hlo hhi
  refine ⟨hdeg, ?_⟩
  rw [hlc]
  field_simp

end WeightedTorusJets.Geometry


open scoped BigOperators DirectSum

namespace WeightedTorusJets.Geometry

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (𝓜 : ℕ → Submodule K M) [DirectSum.Decomposition 𝓜]
    (N : Submodule K M)

theorem graded_quotient_coeLinearMap_injective (hN : N.IsHomogeneous 𝓜) :
    Function.Injective
      (DirectSum.coeLinearMap (fun n => (𝓜 n).map N.mkQ)) := by
  classical
  let 𝓠 := fun n => (𝓜 n).map N.mkQ
  change Function.Injective (DirectSum.coeLinearMap 𝓠)
  suffices hk : ∀ x : ⨁ i, 𝓠 i, DirectSum.coeLinearMap 𝓠 x = 0 → x = 0 by
    intro x y hxy
    exact sub_eq_zero.mp (hk (x - y) (by simp only [map_sub, hxy, sub_self]))
  intro x hx
  have hxsum : (∑ i ∈ x.support, (x i : M ⧸ N)) = 0 := by
    simpa only [DirectSum.coeLinearMap_eq_dfinsuppSum, DFinsupp.sum] using hx
  have hlift (i : ℕ) : ∃ m : M, m ∈ 𝓜 i ∧ N.mkQ m = (x i : M ⧸ N) :=
    (x i).property
  choose m hm hmx using hlift
  have hsum : (∑ i ∈ x.support, m i) ∈ N := by
    apply (Submodule.Quotient.mk_eq_zero N).mp
    change N.mkQ (∑ i ∈ x.support, m i) = 0
    rw [map_sum]
    simpa only [hmx] using hxsum
  apply DFinsupp.ext
  intro i
  by_cases hi : i ∈ x.support
  · apply Subtype.ext
    change (x i : M ⧸ N) = 0
    rw [← hmx i]
    apply (Submodule.Quotient.mk_eq_zero N).mpr
    have hmem := hN i hsum
    have heq : (DirectSum.decompose 𝓜 (∑ j ∈ x.support, m j) i : M) = m i := by
      rw [DirectSum.decompose_sum]
      rw [DirectSum.sum_apply, AddSubmonoidClass.coe_finsetSum]
      rw [Finset.sum_eq_single i]
      · exact DirectSum.decompose_of_mem_same 𝓜 (hm i)
      · intro j _ hji
        exact DirectSum.decompose_of_mem_ne 𝓜 (hm j) hji
      · exact fun hnot => (hnot hi).elim
    rwa [heq] at hmem
  · simpa only [DFinsupp.zero_apply] using DFinsupp.notMem_support_iff.mp hi

theorem graded_quotient_coeLinearMap_surjective :
    Function.Surjective
      (DirectSum.coeLinearMap (fun n => (𝓜 n).map N.mkQ)) := by
  classical
  rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap]
  apply top_unique
  intro x _
  obtain ⟨m, rfl⟩ := N.mkQ_surjective x
  rw [← DirectSum.sum_support_decompose 𝓜 m, map_sum]
  apply Submodule.sum_mem
  intro n _
  apply le_iSup (fun n => (𝓜 n).map N.mkQ) n
  exact Submodule.mem_map_of_mem (DirectSum.decompose 𝓜 m n).property

@[instance_reducible]
noncomputable def gradedQuotientDecomposition (hN : N.IsHomogeneous 𝓜) :
    DirectSum.Decomposition (fun n => (𝓜 n).map N.mkQ) :=
  (show DirectSum.IsInternal (fun n => (𝓜 n).map N.mkQ) from
    ⟨graded_quotient_coeLinearMap_injective 𝓜 N hN,
      graded_quotient_coeLinearMap_surjective 𝓜 N⟩).chooseDecomposition

end WeightedTorusJets.Geometry


end SiegelZeros

end OAI
