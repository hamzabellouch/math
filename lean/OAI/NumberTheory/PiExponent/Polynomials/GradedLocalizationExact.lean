import OAI.NumberTheory.PiExponent.Polynomials.GradedSerre

namespace OAI

namespace PiExponent.GradedLocalizationExact

noncomputable section

variable {R M N P σR σM σN σP : Type*}
  [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
  [SetLike σR R]
  [SetLike σM M] [AddSubgroupClass σM M]
  [SetLike σN N] [AddSubgroupClass σN N]
  [SetLike σP P] [AddSubgroupClass σP P]

def powerDenominator (a : R) (n : ℕ) : Submonoid.powers a :=
  ⟨a ^ n, ⟨n, rfl⟩⟩

@[simp] theorem powerDenominator_val (a : R) (n : ℕ) :
    (powerDenominator a n : R) = a ^ n := rfl

@[simp] theorem powerDenominator_zero (a : R) : powerDenominator a 0 = 1 := by
  apply Subtype.ext
  simp [powerDenominator]

theorem powerDenominator_add (a : R) (n k : ℕ) :
    powerDenominator a (n + k) = powerDenominator a n * powerDenominator a k := by
  apply Subtype.ext
  exact pow_add a n k

def fraction (a : R) (m : M) (n : ℕ) : LocalizedModule (Submonoid.powers a) M :=
  LocalizedModule.mk m (powerDenominator a n)

@[simp] theorem fraction_zero (a : R) (n : ℕ) : fraction a (0 : M) n = 0 :=
  LocalizedModule.zero_mk _

@[simp] theorem fraction_neg (a : R) (m : M) (n : ℕ) :
    fraction a (-m) n = -fraction a m n := LocalizedModule.mk_neg

theorem fraction_add (a : R) (m m' : M) (n k : ℕ) :
    fraction a m n + fraction a m' k =
      fraction a (a ^ k • m + a ^ n • m') (n + k) := by
  simp only [fraction, powerDenominator_add, LocalizedModule.mk_add_mk,
    Submonoid.smul_def, powerDenominator_val]

theorem fraction_cancel (a : R) (m : M) (n k : ℕ) :
    fraction a (a ^ k • m) (n + k) = fraction a m n := by
  simpa only [fraction, powerDenominator_add, Submonoid.smul_def,
    powerDenominator_val] using
    LocalizedModule.mk_cancel_common_right (powerDenominator a n) (powerDenominator a k) m

theorem fraction_eq_zero (a : R) (m : M) (n : ℕ) :
    fraction a m n = 0 ↔ ∃ k : ℕ, a ^ k • m = 0 := by
  rw [← fraction_zero a 0, fraction, fraction, LocalizedModule.mk_eq]
  simp only [powerDenominator_zero, one_smul, smul_zero]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨k, hk⟩ := s.property
    refine ⟨k, ?_⟩
    simpa only [Submonoid.smul_def, ← hk] using hs
  · rintro ⟨k, hk⟩
    exact ⟨powerDenominator a k, hk⟩

variable (𝒜 : ℤ → σR) (𝓜 : ℤ → σM)
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 𝓜]
  (a : R) (e : ℤ) (ha : a ∈ 𝒜 e)

omit [AddSubgroupClass σM M] in
include ha in
theorem power_smul_mem {d : ℤ} {m : M} (hm : m ∈ 𝓜 d) (n : ℕ) :
    a ^ n • m ∈ 𝓜 (d + (n : ℤ) * e) := by
  have h := SetLike.GradedSMul.smul_mem (SetLike.pow_mem_graded n ha) hm
  simpa only [nsmul_eq_mul, vadd_eq_add, add_comm] using h

def degreePiece (d : ℤ) : AddSubgroup (LocalizedModule (Submonoid.powers a) M) where
  carrier := {z | ∃ (n : ℕ) (m : M), m ∈ 𝓜 (d + (n : ℤ) * e) ∧ z = fraction a m n}
  zero_mem' := ⟨0, 0, zero_mem _, (fraction_zero a 0).symm⟩
  add_mem' := by
    rintro z z' ⟨n, m, hm, rfl⟩ ⟨k, m', hm', rfl⟩
    refine ⟨n + k, a ^ k • m + a ^ n • m', ?_, fraction_add a m m' n k⟩
    apply add_mem
    · have h := power_smul_mem 𝒜 𝓜 a e ha hm k
      convert h using 1
      push_cast
      ring_nf
    · have h := power_smul_mem 𝒜 𝓜 a e ha hm' n
      convert h using 1
      push_cast
      ring_nf
  neg_mem' := by
    rintro z ⟨n, m, hm, rfl⟩
    exact ⟨n, -m, neg_mem hm, (fraction_neg a m n).symm⟩

@[simp] theorem mem_degreePiece (d : ℤ) (z : LocalizedModule (Submonoid.powers a) M) :
    z ∈ degreePiece 𝒜 𝓜 a e ha d ↔
      ∃ (n : ℕ) (m : M), m ∈ 𝓜 (d + (n : ℤ) * e) ∧ z = fraction a m n := Iff.rfl

def localizedMap (f : M →ₗ[R] N) :
    LocalizedModule (Submonoid.powers a) M →ₗ[R] LocalizedModule (Submonoid.powers a) N :=
  IsLocalizedModule.map (Submonoid.powers a) (LocalizedModule.mkLinearMap _ M)
    (LocalizedModule.mkLinearMap _ N) f

@[simp] theorem localizedMap_fraction (f : M →ₗ[R] N) (m : M) (n : ℕ) :
    localizedMap a f (fraction a m n) = fraction a (f m) n :=
  IsLocalizedModule.map_LocalizedModules _ f m _

variable (𝓝 : ℤ → σN) [SetLike.GradedSMul 𝒜 𝓝]

def pieceMap (d : ℤ) (f : M →ₗ[R] N)
    (hf : ∀ i m, m ∈ 𝓜 i → f m ∈ 𝓝 i) :
    degreePiece 𝒜 𝓜 a e ha d →+ degreePiece 𝒜 𝓝 a e ha d where
  toFun z := ⟨localizedMap a f z.val, by
    obtain ⟨n, m, hm, hz⟩ := z.property
    refine ⟨n, f m, hf _ _ hm, ?_⟩
    rw [hz, localizedMap_fraction]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' z z' := Subtype.ext (map_add _ _ _)

@[simp] theorem pieceMap_coe (d : ℤ) (f : M →ₗ[R] N)
    (hf : ∀ i m, m ∈ 𝓜 i → f m ∈ 𝓝 i)
    (z : degreePiece 𝒜 𝓜 a e ha d) :
    (pieceMap 𝒜 𝓜 a e ha 𝓝 d f hf z).val = localizedMap a f z.val := rfl

section Decomposition
variable [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]

theorem preserves_of_compatible (f : M →ₗ[R] N)
    (hf : ∀ i x, f (DirectSum.decompose 𝓜 x i : M) =
      (DirectSum.decompose 𝓝 (f x) i : N)) :
    ∀ i m, m ∈ 𝓜 i → f m ∈ 𝓝 i := by
  intro i m hm
  have h := hf i m
  rw [DirectSum.decompose_of_mem_same 𝓜 hm] at h
  exact h.symm ▸ (DirectSum.decompose 𝓝 (f m) i).property

theorem homogeneous_preimage (f : M →ₗ[R] N)
    (hf : ∀ i x, f (DirectSum.decompose 𝓜 x i : M) =
      (DirectSum.decompose 𝓝 (f x) i : N))
    {d : ℤ} {y : N} (hy : y ∈ 𝓝 d) (hrange : y ∈ LinearMap.range f) :
    ∃ x : M, x ∈ 𝓜 d ∧ f x = y := by
  obtain ⟨x, hx⟩ := hrange
  refine ⟨DirectSum.decompose 𝓜 x d, (DirectSum.decompose 𝓜 x d).property, ?_⟩
  rw [hf, hx, DirectSum.decompose_of_mem_same 𝓝 hy]

theorem pieceMap_surjective (d : ℤ) (f : M →ₗ[R] N)
    (hf : ∀ i x, f (DirectSum.decompose 𝓜 x i : M) =
      (DirectSum.decompose 𝓝 (f x) i : N)) (hsurj : Function.Surjective f) :
    Function.Surjective
      (pieceMap 𝒜 𝓜 a e ha 𝓝 d f (preserves_of_compatible 𝓜 𝓝 f hf)) := by
  intro z
  obtain ⟨n, y, hy, hz⟩ := z.property
  obtain ⟨x, hx, hxy⟩ := homogeneous_preimage 𝓜 𝓝 f hf hy (hsurj y)
  refine ⟨⟨fraction a x n, n, x, hx, rfl⟩, ?_⟩
  apply Subtype.ext
  change localizedMap a f (fraction a x n) = z.val
  rw [localizedMap_fraction, hxy, ← hz]

variable (𝓟 : ℤ → σP) [SetLike.GradedSMul 𝒜 𝓟] [DirectSum.Decomposition 𝓟]

theorem pieceMap_exact (d : ℤ) (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : ∀ i x, f (DirectSum.decompose 𝓜 x i : M) =
      (DirectSum.decompose 𝓝 (f x) i : N))
    (hg : ∀ i x, g (DirectSum.decompose 𝓝 x i : N) =
      (DirectSum.decompose 𝓟 (g x) i : P))
    (hex : Function.Exact f g) :
    Function.Exact
      (pieceMap 𝒜 𝓜 a e ha 𝓝 d f (preserves_of_compatible 𝓜 𝓝 f hf))
      (pieceMap 𝒜 𝓝 a e ha 𝓟 d g (preserves_of_compatible 𝓝 𝓟 g hg)) := by
  intro z
  constructor
  · intro hz
    obtain ⟨n, y, hy, hzy⟩ := z.property
    have hzero : localizedMap a g z.val = 0 := congrArg Subtype.val hz
    rw [hzy, localizedMap_fraction, fraction_eq_zero] at hzero
    obtain ⟨k, hk⟩ := hzero
    have hclear : g (a ^ k • y) = 0 := by rw [map_smul, hk]
    have hy' : a ^ k • y ∈ 𝓝 (d + ((n + k : ℕ) : ℤ) * e) := by
      have h := power_smul_mem 𝒜 𝓝 a e ha hy k
      convert h using 1
      push_cast
      ring_nf
    obtain ⟨x, hx, hxy⟩ := homogeneous_preimage 𝓜 𝓝 f hf hy' ((hex _).mp hclear)
    refine ⟨⟨fraction a x (n + k), n + k, x, hx, rfl⟩, ?_⟩
    apply Subtype.ext
    change localizedMap a f (fraction a x (n + k)) = z.val
    rw [localizedMap_fraction, hxy, fraction_cancel, ← hzy]
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    obtain ⟨n, y, hy, hxy⟩ := x.property
    change localizedMap a g (localizedMap a f x.val) = 0
    rw [hxy, localizedMap_fraction, localizedMap_fraction,
      hex.apply_apply_eq_zero, fraction_zero]

end Decomposition

section FinitePresentation
variable [AddSubgroupClass σR R] [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition 𝓜]
  [IsNoetherianRing R] [Module.Finite R M]

theorem exists_exact_localized_free_presentation :
    ∃ (n₀ n₁ : ℕ) (w₀ : Fin n₀ → ℤ) (w₁ : Fin n₁ → ℤ)
      (f₀ : (Fin n₀ → R) →ₗ[R] M)
      (f₁ : (Fin n₁ → R) →ₗ[R] (Fin n₀ → R)),
      ∃ (hf₀ : ∀ i x,
        f₀ (DirectSum.decompose (ShiftedFreeGrading.piece 𝒜 w₀) x i : Fin n₀ → R) =
          (DirectSum.decompose 𝓜 (f₀ x) i : M))
        (hf₁ : ∀ i x,
          f₁ (DirectSum.decompose (ShiftedFreeGrading.piece 𝒜 w₁) x i : Fin n₁ → R) =
            (DirectSum.decompose (ShiftedFreeGrading.piece 𝒜 w₀) (f₁ x) i : Fin n₀ → R)),
        Function.Surjective f₀ ∧ LinearMap.range f₁ = f₀.ker ∧
        ∀ d : ℤ,
          Function.Surjective
            (pieceMap 𝒜 (ShiftedFreeGrading.piece 𝒜 w₀) a e ha 𝓜 d f₀
              (preserves_of_compatible (ShiftedFreeGrading.piece 𝒜 w₀) 𝓜 f₀ hf₀)) ∧
          Function.Exact
            (pieceMap 𝒜 (ShiftedFreeGrading.piece 𝒜 w₁) a e ha
              (ShiftedFreeGrading.piece 𝒜 w₀) d f₁
              (preserves_of_compatible (ShiftedFreeGrading.piece 𝒜 w₁)
                (ShiftedFreeGrading.piece 𝒜 w₀) f₁ hf₁))
            (pieceMap 𝒜 (ShiftedFreeGrading.piece 𝒜 w₀) a e ha 𝓜 d f₀
              (preserves_of_compatible (ShiftedFreeGrading.piece 𝒜 w₀) 𝓜 f₀ hf₀)) := by
  obtain ⟨n₀, n₁, w₀, w₁, f₀, f₁, hsurj, hex, hf₀, hf₁⟩ :=
    GradedSerre.exists_graded_free_presentation 𝒜 𝓜
  refine ⟨n₀, n₁, w₀, w₁, f₀, f₁, hf₀, hf₁, hsurj, hex, ?_⟩
  intro d
  refine ⟨pieceMap_surjective 𝒜 (ShiftedFreeGrading.piece 𝒜 w₀) a e ha 𝓜 d f₀ hf₀ hsurj,
    pieceMap_exact 𝒜 (ShiftedFreeGrading.piece 𝒜 w₁) a e ha
      (ShiftedFreeGrading.piece 𝒜 w₀) 𝓜 d f₁ f₀ hf₁ hf₀ ?_⟩
  exact LinearMap.exact_iff.mpr hex.symm

end FinitePresentation

end
end PiExponent.GradedLocalizationExact

end OAI
