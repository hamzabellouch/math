import Mathlib
import OAI.Computability.DirectedFeedback.Games.KMSAnalyticCodomainTransport

namespace OAI

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Inverse.KMSAnalytic
open DFVSGames.Inverse.KMSFourthMoment

universe u v w

@[instance_reducible]
def mixedMapFintype {V W : Type*}
    [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]
    [Fintype V] [Fintype W] : Fintype (V →ₗ[F2] W) :=
  Fintype.ofInjective (fun L : V →ₗ[F2] W => (L : V → W)) DFunLike.coe_injective

attribute [local instance] mixedMapFintype

variable {E : Type u} {F : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F]

def UniformMixedBound (r : ℕ) (L : ℝ) (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ (A I J : Type u)
    [AddCommGroup A] [Module F2 A] [FiniteDimensional F2 A] [Fintype A]
    [AddCommGroup I] [Module F2 I] [FiniteDimensional F2 I] [Fintype I]
    [AddCommGroup J] [Module F2 J] [FiniteDimensional F2 J] [Fintype J],
    ∀ (ι : (A × I) →ₗ[F2] E), Function.Injective ι →
    ∀ (a : A →ₗ[F2] F) (π : I →ₗ[F2] J), Function.Surjective π →
    ∀ (ν : F →ₗ[F2] J), Module.finrank F2 A + Module.finrank F2 I ≤ r →
      (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
        sliceEnergy (fun T => π.comp T = ν)
          (partialRestrict (smallComponent ι f) a) ≤ L

section Transport

variable {E' : Type u} {F' : Type w}
  [AddCommGroup E'] [Module F2 E'] [AddCommGroup F'] [Module F2 F']
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F']
  [Fintype E'] [Fintype F']

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E'] in
theorem UniformMixedBound.pullback {r : ℕ} {L : ℝ}
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (hf : UniformMixedBound r L f) :
    UniformMixedBound r L (fun M => f (LinearEquiv.arrowCongr a b M)) := by
  intro A I J _ _ _ _ _ _ _ _ _ _ _ _ ι hι u π hπ ν hr
  rw [sliceEnergy_partialRestrict_smallComponent_pullback a b ι f π ν u,
    a.finrank_eq]
  exact hf A I J (a.toLinearMap.comp ι) (a.injective.comp hι)
    (b.toLinearMap.comp u) π hπ (ν.comp b.symm.toLinearMap) hr

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E'] in
theorem UniformMixedBound.pullback_iff {r : ℕ} {L : ℝ}
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) :
    UniformMixedBound r L (fun M => f (LinearEquiv.arrowCongr a b M)) ↔
      UniformMixedBound r L f := by
  constructor
  · intro hf
    have h := UniformMixedBound.pullback a.symm b.symm
      (fun M => f (LinearEquiv.arrowCongr a b M)) hf
    have he : (fun M : E' →ₗ[F2] F' =>
        f (LinearEquiv.arrowCongr a b (LinearEquiv.arrowCongr a.symm b.symm M))) = f := by
      funext M
      apply congrArg f
      apply LinearMap.ext
      intro x
      change b (b.symm (M (a (a.symm x)))) = M x
      simp
    rw [he] at h
    exact h
  · exact UniformMixedBound.pullback a b f

end Transport

theorem uniformMixedBound_of_affineDensityBound (r : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (hd : AffineDensityBound r ε f) :
    UniformMixedBound r (mixedRankConstant r * ε) f := by
  intro A I J _ _ _ _ _ _ _ _ _ _ _ _ ι hι a π hπ ν hr
  exact mixed_slice_bound_uniform r ε hε ι hι f hf
    (AffineDensityBound.mono hr ε f hd) a π hπ ν hr

end
end DFVSGames.Inverse.KMSAnalyticHybridEnergy

noncomputable section
namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Appendix DFVSGames.Appendix.Derivatives
open DFVSGames.Fourier.MatrixRestrictions
open KMSAnalytic KMSFourthMoment

universe u

attribute [local instance] mapFintype

section Product
variable {A U B C : Type u}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype A] [Fintype U] [Fintype B] [Fintype C]

theorem productMixedSliceBound_of_uniform (i : ℕ) (L : ℝ)
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (hMixed : UniformMixedBound i L f)
    (ho : Module.finrank F2 A + Module.finrank F2 C ≤ i)
    (T : (A × U) →ₗ[F2] (B × C)) : ProductMixedSliceBound i f T L := by
  intro W D hW hD κ hκ
  have hm := UniformMixedBound.pullback (imageAmbientEquiv (A := A) W D hD)
    (LinearEquiv.refl F2 (B × C)) f hMixed
  have hm' : UniformMixedBound i L (imagePullback W D hD f) := by
    exact hm
  have hr : Module.finrank F2 A + Module.finrank F2 (W × C) ≤ i := by
    rw [Module.finrank_prod, hW]
    omega
  have hπ : Function.Surjective (LinearMap.snd F2 W C) := by
    intro c
    exact ⟨(0, c), rfl⟩
  have hh := hm' A (W × C) C κ hκ (primalA (imageTranslate W D hD T))
    (LinearMap.snd F2 W C) hπ (LinearMap.snd F2 B C) hr
  have hdim : Module.finrank F2 (A × (W × D)) = Module.finrank F2 (A × U) :=
    (imageAmbientEquiv (A := A) W D hD).finrank_eq
  have hexp : (Module.finrank F2 (W × C) + Module.finrank F2 C) *
      Module.finrank F2 (A × (W × D)) =
      (2 * Module.finrank F2 C + (i - (Module.finrank F2 A + Module.finrank F2 C))) *
        Module.finrank F2 (A × U) := by
    rw [Module.finrank_prod, hW, hdim]
    congr 1
    omega
  rw [hexp] at hh
  apply (le_div_iff₀ (by positivity)).mpr
  convert hh using 1
  simp only [mul_comm]

end Product

variable {E F : Type u}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F]

omit [FiniteDimensional F2 E] [Fintype E] in
theorem map_leftRange_complement (A U : Submodule F2 E) (h : IsCompl A U) :
    (LinearMap.range (LinearMap.inl F2 A U)).map
      (Submodule.prodEquivOfIsCompl A U h).toLinearMap = A := by
  rw [← LinearMap.range_comp]
  have hc : (Submodule.prodEquivOfIsCompl A U h).toLinearMap.comp
      (LinearMap.inl F2 A U) = A.subtype := by
    apply LinearMap.ext
    intro a
    change (a : E) + (0 : E) = (a : E)
    simp
  rw [hc, Submodule.range_subtype]

theorem hybridDerivative_energy_le_of_uniform
    (i : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (hMixed : UniformMixedBound i L f) (hi : i ≤ Module.finrank F2 E)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F) :
    (𝔼 N, hybridDerivative A B T (rankComponent i f) N ^ 2) ≤ L := by
  obtain ⟨U, hU⟩ := A.exists_isCompl
  obtain ⟨C, hC⟩ := B.exists_isCompl
  let a : (A × U) ≃ₗ[F2] E := Submodule.prodEquivOfIsCompl A U hU
  let b : (B × C) ≃ₗ[F2] F := Submodule.prodEquivOfIsCompl B C hC
  let f' : ((A × U) →ₗ[F2] (B × C)) → ℝ :=
    fun M => f (LinearEquiv.arrowCongr a b M)
  let T' : (A × U) →ₗ[F2] (B × C) := (LinearEquiv.arrowCongr a b).symm T
  have hf' : KMSBasisInvariant.IsBasisInvariant f' := basisInvariant_pullback a b f hf
  have hm' : UniformMixedBound i L f' := UniformMixedBound.pullback a b f hMixed
  have hi' : i ≤ Module.finrank F2 (A × U) := by rw [a.finrank_eq]; exact hi
  have hcoord : (𝔼 N, hybridDerivative
      (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) T' (rankComponent i f') N ^ 2) ≤ L := by
    by_cases ho : Module.finrank F2 A + Module.finrank F2 C ≤ i
    · exact product_hybrid_energy_le_of_mixed i f' hf' T' L hL hi'
        (productMixedSliceBound_of_uniform i L f' hm' ho T')
    · have hzero := hybridDerivative_rankComponent_eq_zero_of_lt_order
        (LinearMap.range (LinearMap.inl F2 A U))
        (LinearMap.range (LinearMap.inl F2 B C)) T' f' i
        (by rw [product_restriction_order]
            change i < Module.finrank F2 A + Module.finrank F2 C
            omega)
      simpa [hzero] using hL
  have he := hybridDerivative_rankComponent_energy_pullback a b f i
    (LinearMap.range (LinearMap.inl F2 A U))
    (LinearMap.range (LinearMap.inl F2 B C)) T'
  have hA : (LinearMap.range (LinearMap.inl F2 A U)).map a.toLinearMap = A :=
    map_leftRange_complement A U hU
  have hB : (LinearMap.range (LinearMap.inl F2 B C)).map b.toLinearMap = B :=
    map_leftRange_complement B C hC
  have hT : LinearEquiv.arrowCongr a b T' = T :=
    (LinearEquiv.arrowCongr a b).apply_symm_apply T
  rw [hA, hB, hT] at he
  exact he ▸ hcoord

theorem hybridDerivative_energy_bound
    (i : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (hd : AffineDensityBound i ε f) (hi : i ≤ Module.finrank F2 E)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F) :
    (𝔼 N, hybridDerivative A B T (rankComponent i f) N ^ 2) ≤ mixedRankConstant i * ε :=
  hybridDerivative_energy_le_of_uniform i (mixedRankConstant i * ε)
    (mul_nonneg (mixedRankConstant_nonneg i) hε) f hf
    (uniformMixedBound_of_affineDensityBound i ε hε f hf hd) hi A B T

end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end

namespace DFVSGames.Appendix.LevelInequality

open scoped BigOperators

variable {α : Type*} [Fintype α]

def IsBoolean (f : α → ℝ) : Prop := ∀ x, f x = 0 ∨ f x = 1

omit [Fintype α] in
theorem boolean_nonneg {f : α → ℝ} (hf : IsBoolean f) (x : α) : 0 ≤ f x := by
  rcases hf x with h | h <;> simp [h]

omit [Fintype α] in
theorem boolean_sq {f : α → ℝ} (hf : IsBoolean f) (x : α) : f x ^ 2 = f x := by
  rcases hf x with h | h <;> simp [h]

theorem boolean_positive_moment {f : α → ℝ} (hf : IsBoolean f)
    (k : ℕ) (hk : 0 < k) : (𝔼 x, f x ^ k) = 𝔼 x, f x := by
  apply Finset.expect_congr rfl
  intro x _
  rcases hf x with h | h <;> simp [h, Nat.ne_of_gt hk]

theorem boolean_squared_norm_eq_density {f : α → ℝ} (hf : IsBoolean f) :
    (𝔼 x, f x ^ 2) = 𝔼 x, f x :=
  boolean_positive_moment hf 2 (by decide)

theorem boolean_four_thirds_moment {f : α → ℝ} (hf : IsBoolean f) :
    (𝔼 x, |f x| ^ ((4 : ℝ) / 3)) = 𝔼 x, f x := by
  apply Finset.expect_congr rfl
  intro x _
  rcases hf x with h | h <;> norm_num [h]

theorem boolean_holder_fourth {f : α → ℝ} (hf : IsBoolean f) (h : α → ℝ) :
    (𝔼 x, h x * f x) ^ 4 ≤ (𝔼 x, h x ^ 4) * (𝔼 x, f x) ^ 3 := by
  have hfirst := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => h x * f x) f
  have eleft : (𝔼 x, (h x * f x) * f x) = 𝔼 x, h x * f x := by
    apply Finset.expect_congr rfl
    intro x _
    calc
      _ = h x * (f x ^ 2) := by ring
      _ = _ := by rw [boolean_sq hf]
  have eright : (𝔼 x, (h x * f x) ^ 2) = 𝔼 x, h x ^ 2 * f x := by
    apply Finset.expect_congr rfl
    intro x _
    rw [mul_pow, boolean_sq hf]
  rw [eleft, eright, boolean_squared_norm_eq_density hf] at hfirst
  have hsecond := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => h x ^ 2) f
  have epow : (𝔼 x, (h x ^ 2) ^ 2) = 𝔼 x, h x ^ 4 := by
    apply Finset.expect_congr rfl
    intro x _
    ring
  rw [epow, boolean_squared_norm_eq_density hf] at hsecond
  have hμ : 0 ≤ 𝔼 x, f x :=
    Finset.expect_nonneg (fun x _ => boolean_nonneg hf x)
  have hweighted : 0 ≤ 𝔼 x, h x ^ 2 * f x :=
    Finset.expect_nonneg (fun x _ => mul_nonneg (sq_nonneg _) (boolean_nonneg hf x))
  have hsquare := mul_self_le_mul_self (sq_nonneg (𝔼 x, h x * f x)) hfirst
  have hscaled := mul_le_mul_of_nonneg_right hsecond (sq_nonneg (𝔼 x, f x))
  nlinarith only [hsquare, hscaled]

theorem fourth_power_le_implies_le {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 4 ≤ b ^ 4) : a ≤ b := by
  by_contra hab
  have hba : b < a := lt_of_not_ge hab
  have hpow : b ^ 4 < a ^ 4 := pow_lt_pow_left₀ hba hb (by decide : (4 : ℕ) ≠ 0)
  exact (not_lt_of_ge h) hpow

theorem boolean_level_bound_of_fourth_moment {f h : α → ℝ}
    (hf : IsBoolean f) (d : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (hprojection : (𝔼 x, h x ^ 2) = 𝔼 x, h x * f x)
    (hfourth : (𝔼 x, h x ^ 4) ≤ (2 : ℝ) ^ (113 * d * d) * η * (𝔼 x, f x)) :
    (𝔼 x, h x ^ 2) ≤
      (2 : ℝ) ^ (30 * d * d) * η ^ ((1 : ℝ) / 4) * (𝔼 x, f x ^ 2) := by
  have hμ : 0 ≤ 𝔼 x, f x :=
    Finset.expect_nonneg (fun x _ => boolean_nonneg hf x)
  have hh : 0 ≤ 𝔼 x, h x ^ 2 := Finset.expect_nonneg (fun x _ => sq_nonneg _)
  have hηroot : 0 ≤ η ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hη _
  have hroot : (η ^ ((1 : ℝ) / 4)) ^ 4 = η := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hη]
    norm_num
  have hslack : 113 * d * d ≤ (30 * d * d) * 4 := by
    calc
      113 * d * d = 113 * (d * d) := by ring
      _ ≤ 120 * (d * d) := Nat.mul_le_mul_right _ (by decide)
      _ = (30 * d * d) * 4 := by ring
  have htwo : (2 : ℝ) ^ (113 * d * d) ≤ ((2 : ℝ) ^ (30 * d * d)) ^ 4 := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) hslack
  have hholder := boolean_holder_fourth hf h
  rw [← hprojection] at hholder
  have hscale := mul_le_mul_of_nonneg_right hfourth (pow_nonneg hμ 3)
  have hlarge := mul_le_mul_of_nonneg_right htwo (mul_nonneg hη (pow_nonneg hμ 4))
  rw [boolean_squared_norm_eq_density hf]
  apply fourth_power_le_implies_le hh
    (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hηroot) hμ)
  calc
    _ ≤ (2 : ℝ) ^ (113 * d * d) * η * (𝔼 x, f x) ^ 4 := by
      nlinarith only [hholder, hscale]
    _ ≤ ((2 : ℝ) ^ (30 * d * d)) ^ 4 * η * (𝔼 x, f x) ^ 4 := by
      nlinarith only [hlarge]
    _ = _ := by rw [mul_pow, mul_pow, hroot]

end DFVSGames.Appendix.LevelInequality

noncomputable section

namespace DFVSGames.Appendix.LevelInequality

open scoped BigOperators
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def frequencyRank (S : F →ₗ[F2] E) : ℕ := Module.finrank F2 (LinearMap.range S)

def rankLevel (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : (E →ₗ[F2] F) → ℝ :=
  ∑ S with frequencyRank S = d,
    linearCoeff f S • (fun X => (linearTraceCharacter S X).re)

theorem linearCoeff_rankLevel (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (S : F →ₗ[F2] E) :
    linearCoeff (rankLevel d f) S = if frequencyRank S = d then linearCoeff f S else 0 := by
  classical
  unfold rankLevel
  rw [linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_character, mul_ite, mul_one, mul_zero]
  simp

theorem rankLevel_energy (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankLevel d f X ^ 2) =
      ∑ S with frequencyRank S = d, linearCoeff f S ^ 2 := by
  classical
  rw [← linear_parseval]
  simp only [linearCoeff_rankLevel]
  simp [Finset.sum_filter]

theorem rankLevel_inner_self (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankLevel d f X ^ 2) = 𝔼 X, rankLevel d f X * f X := by
  classical
  rw [← linear_parseval, ← linear_parseval_inner]
  apply Finset.sum_congr rfl
  intro S _
  rw [linearCoeff_rankLevel]
  split_ifs <;> ring

theorem rankLevel_energy_le (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankLevel d f X ^ 2) ≤ 𝔼 X, f X ^ 2 := by
  classical
  rw [rankLevel_energy, ← linear_parseval]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun S _ _ => sq_nonneg _)

theorem rankLevel_degree_le (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (S : F →ₗ[F2] E) (hS : d < frequencyRank S) :
    linearCoeff (rankLevel d f) S = 0 := by
  rw [linearCoeff_rankLevel, ite_eq_right (Nat.ne_of_gt hS)]

theorem rankLevel_bound_of_fourth_moment (d : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (η : ℝ) (hη : 0 ≤ η)
    (hfourth : (𝔼 X, rankLevel d f X ^ 4) ≤
      (2 : ℝ) ^ (113 * d * d) * η * (𝔼 X, f X)) :
    (𝔼 X, rankLevel d f X ^ 2) ≤
      (2 : ℝ) ^ (30 * d * d) * η ^ ((1 : ℝ) / 4) * (𝔼 X, f X ^ 2) :=
  boolean_level_bound_of_fourth_moment hf d η hη (rankLevel_inner_self d f) hfourth

variable [Finite E] [Finite F]

def IsRestrictionGlobal (f : (E →ₗ[F2] F) → ℝ) (d : ℕ) (η : ℝ) : Prop :=
  ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
    DFVSGames.Fourier.MatrixRestrictions.order A B ≤ d →
      (𝔼 N, DFVSGames.Fourier.MatrixRestrictions.restrict f A B T N ^ 2) ≤ η

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
theorem boolean_restriction (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F) :
    IsBoolean (DFVSGames.Fourier.MatrixRestrictions.restrict f A B T) := by
  intro N
  exact hf (DFVSGames.Fourier.MatrixRestrictions.translate A B T N)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem boolean_global_iff_density (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (d : ℕ) (η : ℝ) :
    IsRestrictionGlobal f d η ↔
      ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
        DFVSGames.Fourier.MatrixRestrictions.order A B ≤ d →
          (𝔼 N, DFVSGames.Fourier.MatrixRestrictions.restrict f A B T N) ≤ η := by
  unfold IsRestrictionGlobal
  simp_rw [boolean_squared_norm_eq_density (boolean_restriction f hf _ _ _)]

def Theorem23 : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (ρ : ℝ), 0 < ρ → ρ < 1 →
    ∀ (f : (E →ₗ[F2] F) → ℝ), IsBoolean f →
      (∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
        DFVSGames.Fourier.MatrixRestrictions.order A B ≤ d →
          (𝔼 N, DFVSGames.Fourier.MatrixRestrictions.restrict f A B T N) ≤ ρ) →
      (𝔼 X, rankLevel d f X ^ 2) ≤
        (2 : ℝ) ^ (30 * d * d) * ρ ^ ((1 : ℝ) / 4) * (𝔼 X, f X ^ 2)

end DFVSGames.Appendix.LevelInequality
end

noncomputable section
namespace DFVSGames.Appendix.DerivativeDegree

open scoped BigOperators
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier
open DFVSGames.Fourier.MatrixRestrictions
open DFVSGames.Appendix.Derivatives
open DFVSGames.Appendix.LevelInequality (frequencyRank)
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def DegreeAtMost (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ Y, d < frequencyRank Y → linearCoeff f Y = 0

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem DegreeAtMost.mono {d e : ℕ} {f : (E →ₗ[F2] F) → ℝ}
    (hf : DegreeAtMost d f) (hde : d ≤ e) : DegreeAtMost e f := by
  intro Y hY
  exact hf Y (lt_of_le_of_lt hde hY)

theorem degree_rankLevel (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    DegreeAtMost d (LevelInequality.rankLevel d f) :=
  LevelInequality.rankLevel_degree_le d f

theorem degree_spectralProjector (P : (F →ₗ[F2] E) → Prop)
    {d : ℕ} {f : (E →ₗ[F2] F) → ℝ} (hf : DegreeAtMost d f) :
    DegreeAtMost d (spectralProjector P f) := by
  intro Y hY
  rw [linearCoeff_spectralProjector, hf Y hY]
  split_ifs <;> rfl

theorem eq_zero_of_linearCoeff_zero {f : (E →ₗ[F2] F) → ℝ}
    (hf : ∀ Y, linearCoeff f Y = 0) : f = 0 := by
  funext M
  rw [← linear_fourier_inversion f M]
  simp [hf]

variable [Finite E] [Finite F]

local instance quotientFinite (A : Submodule F2 E) : Finite (E ⧸ A) :=
  Finite.of_surjective A.mkQ A.mkQ_surjective

local instance compressedDualFintype (A : Submodule F2 E) (B : Submodule F2 F) :
    Fintype (B →ₗ[F2] (E ⧸ A)) := by
  classical
  letI : Fintype B := Fintype.ofFinite _
  letI : Fintype (E ⧸ A) := Fintype.ofFinite _
  exact Fintype.ofInjective (fun L : B →ₗ[F2] (E ⧸ A) => (L : B → E ⧸ A))
    DFunLike.coe_injective

theorem hybridDerivative_coeff_zero_of_lt (A : Submodule F2 E)
    (B : Submodule F2 F) (T : E →ₗ[F2] F) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (Z : B →ₗ[F2] (E ⧸ A))
    (hZ : d < frequencyRank Z + order A B) :
    linearCoeff (hybridDerivative A B T f) Z = 0 := by
  unfold hybridDerivative
  rw [Restriction.linear_coefficient_merging]
  apply Finset.sum_eq_zero
  intro Y _
  by_cases hc : Restriction.compressFrequency A B Y = Z
  · rw [ite_eq_left hc]
    unfold hybridProjector
    rw [linearCoeff_spectralProjector]
    by_cases hY : LinearIdentities.Hybrid Y A B
    · rw [ite_eq_left hY]
      have hr := Level.LinearRank.hybrid_rank_loss A B Y hY.1 hY.2
      have he : Level.LinearRank.compress A B Y = Z := by
        simpa only [Level.LinearRank.compress, Restriction.compressFrequency,
          LinearMap.comp_assoc] using hc
      rw [he] at hr
      have hr' : frequencyRank Z + order A B = frequencyRank Y := by
        simpa only [frequencyRank, order, Nat.add_assoc] using hr
      have hdY : d < frequencyRank Y := hZ.trans_eq hr'
      rw [hf Y hdY, zero_mul]
    · rw [ite_eq_right hY, zero_mul]
  · rw [ite_eq_right hc]

theorem degree_hybridDerivative (A : Submodule F2 E) (B : Submodule F2 F)
    (T : E →ₗ[F2] F) {d : ℕ} (f : (E →ₗ[F2] F) → ℝ)
    (hf : DegreeAtMost d f) :
    DegreeAtMost (d - order A B) (hybridDerivative A B T f) := by
  intro Z hZ
  exact hybridDerivative_coeff_zero_of_lt A B T f hf Z (by omega)

theorem hybridDerivative_eq_zero_of_lt_order (A : Submodule F2 E)
    (B : Submodule F2 F) (T : E →ₗ[F2] F) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < order A B) : hybridDerivative A B T f = 0 := by
  apply eq_zero_of_linearCoeff_zero
  intro Z
  exact hybridDerivative_coeff_zero_of_lt A B T f hf Z (by omega)

theorem mapDerivative_coeff_zero_of_lt (X : F →ₗ[F2] E) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (Z : X.ker →ₗ[F2] (E ⧸ X.range))
    (hZ : d < frequencyRank Z + frequencyRank X) :
    linearCoeff (mapDerivative X f) Z = 0 := by
  rw [linearCoeff_mapDerivative]
  apply Finset.sum_eq_zero
  intro Y _
  by_cases hY : RankAdditivity.RankBelow X Y ∧
      Restriction.compressFrequency X.range X.ker Y = Z
  · rw [ite_eq_left hY]
    have hc : FullCompression.compression X Y = Z := by
      simpa only [FullCompression.compression, Restriction.compressFrequency] using hY.2
    have hr := FullCompression.fiber_rank X Z
      (⟨Y, hY.1, hc⟩ : FullCompression.Fiber X Z)
    apply hf Y
    unfold frequencyRank at *
    change Module.finrank F2 Y.range =
      Module.finrank F2 X.range + Module.finrank F2 Z.range at hr
    omega
  · rw [ite_eq_right hY]

theorem degree_mapDerivative (X : F →ₗ[F2] E) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f) :
    DegreeAtMost (d - frequencyRank X) (mapDerivative X f) := by
  intro Z hZ
  exact mapDerivative_coeff_zero_of_lt X f hf Z (by omega)

theorem mapDerivative_eq_zero_of_lt_rank (X : F →ₗ[F2] E) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < frequencyRank X) : mapDerivative X f = 0 := by
  apply eq_zero_of_linearCoeff_zero
  intro Z
  exact mapDerivative_coeff_zero_of_lt X f hf Z (by omega)

theorem mapDerivative_zero (X : F →ₗ[F2] E) :
    mapDerivative X (0 : (E →ₗ[F2] F) → ℝ) = 0 := by
  apply eq_zero_of_linearCoeff_zero
  intro Z
  rw [linearCoeff_mapDerivative]
  simp [linearCoeff]

theorem degree_map_hybridDerivative (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (T : E →ₗ[F2] F) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f) :
    DegreeAtMost (d - (order A B + frequencyRank X))
      (mapDerivative X (hybridDerivative A B T f)) := by
  simpa only [Nat.sub_sub] using
    degree_mapDerivative X (hybridDerivative A B T f)
      (degree_hybridDerivative A B T f hf)

theorem map_hybridDerivative_eq_zero_of_lt_order_rank
    (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (T : E →ₗ[F2] F) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < order A B + Module.finrank F2 X.range) :
    mapDerivative X (hybridDerivative A B T f) = 0 := by
  by_cases hAB : d < order A B
  · rw [hybridDerivative_eq_zero_of_lt_order A B T f hf hAB, mapDerivative_zero]
  · apply mapDerivative_eq_zero_of_lt_rank X (hybridDerivative A B T f)
      (degree_hybridDerivative A B T f hf)
    unfold frequencyRank
    omega

theorem map_hybridDerivative_fourth_average_eq_zero_of_lt_order_rank
    (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < order A B + Module.finrank F2 X.range) :
    (𝔼 T, 𝔼 N, mapDerivative X (hybridDerivative A B T f) N ^ 4) = 0 := by
  simp_rw [map_hybridDerivative_eq_zero_of_lt_order_rank A B X _ f hf h]
  simp

end DFVSGames.Appendix.DerivativeDegree
end

noncomputable section
namespace DFVSGames.Appendix.DegreeZero
open scoped BigOperators
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in
theorem rank_pos_of_ne_zero (Y : F →ₗ[F2] E) (hY : Y ≠ 0) :
    0 < Module.finrank F2 Y.range := by
  apply Nat.pos_of_ne_zero
  intro hr
  have hb : Y.range = ⊥ := Submodule.finrank_eq_zero.mp hr
  apply hY
  ext x
  have hx : Y x ∈ Y.range := ⟨x, rfl⟩
  rw [hb] at hx
  exact hx

variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem eq_constant_of_degree_zero (f : (E →ₗ[F2] F) → ℝ)
    (hdegree : ∀ Y : F →ₗ[F2] E, 0 < Module.finrank F2 Y.range → linearCoeff f Y = 0)
    (M : E →ₗ[F2] F) : f M = linearCoeff f 0 := by
  classical
  rw [← linear_fourier_inversion f M, Finset.sum_eq_single (0 : F →ₗ[F2] E)]
  · simp
  · intro Y _ hY
    rw [hdegree Y (rank_pos_of_ne_zero Y hY), zero_mul]
  · simp

theorem fourth_moment_eq_energy_sq (f : (E →ₗ[F2] F) → ℝ)
    (hdegree : ∀ Y : F →ₗ[F2] E, 0 < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    (𝔼 M, f M^4) = (𝔼 M, f M^2)^2 := by
  simp only [eq_constant_of_degree_zero f hdegree, Fintype.expect_const]
  rw [← pow_mul]

end DFVSGames.Appendix.DegreeZero
end

noncomputable section

namespace DFVSGames.Appendix.A5IndexCount

open DFVSGames.Integration.BinaryLinear (F2)

variable {V W : Type*}
  [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]

def insideEquiv (A I : Submodule F2 V) (hIA : I ≤ A) :
    (I.comap A.subtype) ≃ₗ[F2] I where
  toFun i := ⟨i.val.val, i.property⟩
  invFun i := ⟨⟨i.val, hIA i.property⟩, i.property⟩
  left_inv _i := Subtype.ext (Subtype.ext rfl)
  right_inv _i := Subtype.ext rfl
  map_add' _i _j := Subtype.ext rfl
  map_smul' _c _i := Subtype.ext rfl

theorem internal_isCompl (A I A0 : Submodule F2 V) (hIA : I ≤ A)
    (hd : Disjoint A0 I) (hj : A0 ⊔ I = A) :
    IsCompl (I.comap A.subtype) (A0.comap A.subtype) := by
  have hA0 : A0 ≤ A := le_sup_left.trans hj.le
  refine ⟨Submodule.disjoint_def.mpr ?_, codisjoint_iff.mpr ?_⟩
  · intro a hi h0
    exact Subtype.ext (Submodule.disjoint_def.mp hd a.val h0 hi)
  · apply eq_top_iff.mpr
    intro a _
    have ha : a.val ∈ A0 ⊔ I := by rw [hj]; exact a.property
    rcases Submodule.mem_sup.mp ha with ⟨v, hv, i, hi, hvi⟩
    refine Submodule.mem_sup.mpr ⟨⟨i, hIA hi⟩, hi, ⟨v, hA0 hv⟩, hv, ?_⟩
    apply Subtype.ext
    change i + v = a.val
    rw [add_comm]
    exact hvi

def projectionA0 (A I A0 : Submodule F2 V) (hIA : I ≤ A)
    (hd : Disjoint A0 I) (hj : A0 ⊔ I = A) : A →ₗ[F2] I :=
  (insideEquiv A I hIA).toLinearMap.comp
    (((I.comap A.subtype).isComplEquivProj
      ⟨A0.comap A.subtype, internal_isCompl A I A0 hIA hd hj⟩).val)

theorem projectionA0_injective (A I A0 A0' : Submodule F2 V) (hIA : I ≤ A)
    (hd : Disjoint A0 I) (hj : A0 ⊔ I = A)
    (hd' : Disjoint A0' I) (hj' : A0' ⊔ I = A)
    (h : projectionA0 A I A0 hIA hd hj = projectionA0 A I A0' hIA hd' hj') :
    A0 = A0' := by
  let P := I.comap A.subtype
  let Q : {Q : Submodule F2 A // IsCompl P Q} :=
    ⟨A0.comap A.subtype, internal_isCompl A I A0 hIA hd hj⟩
  let Q' : {Q : Submodule F2 A // IsCompl P Q} :=
    ⟨A0'.comap A.subtype, internal_isCompl A I A0' hIA hd' hj'⟩
  have hp : (P.isComplEquivProj Q).val = (P.isComplEquivProj Q').val := by
    apply LinearMap.ext
    intro a
    apply (insideEquiv A I hIA).injective
    exact LinearMap.congr_fun h a
  have hQ := P.isComplEquivProj.injective (Subtype.ext hp)
  have hq : A0.comap A.subtype = A0'.comap A.subtype := congrArg Subtype.val hQ
  have hA0 : A0 ≤ A := le_sup_left.trans hj.le
  have hA0' : A0' ≤ A := le_sup_left.trans hj'.le
  ext x
  constructor
  · intro hx
    have hm : (⟨x, hA0 hx⟩ : A) ∈ A0.comap A.subtype := hx
    rw [hq] at hm
    exact hm
  · intro hx
    have hm : (⟨x, hA0' hx⟩ : A) ∈ A0'.comap A.subtype := hx
    rw [← hq] at hm
    exact hm

def fullRange {U L : Type*} [AddCommGroup U] [Module F2 U]
    [AddCommGroup L] [Module F2 L] (S : U →ₗ[F2] L) (hS : S.range = ⊤) :
    L →ₗ[F2] S.range :=
  (LinearMap.id : L →ₗ[F2] L).codRestrict S.range (fun x => by rw [hS]; trivial)

theorem fullRange_surjective {U L : Type*} [AddCommGroup U] [Module F2 U]
    [AddCommGroup L] [Module F2 L] (S : U →ₗ[F2] L) (hS : S.range = ⊤) :
    Function.Surjective (fullRange S hS) := fun c => ⟨c.val, Subtype.ext rfl⟩

theorem quotientRestriction_surjective (J B0 : Submodule F2 W) (hc : B0 ⊔ J = ⊤) :
    Function.Surjective (A4IndexCount.quotientRestriction J B0) := by
  intro z
  obtain ⟨w, rfl⟩ := J.mkQ_surjective z
  have hw : w ∈ B0 ⊔ J := by rw [hc]; trivial
  rcases Submodule.mem_sup.mp hw with ⟨b, hb, j, hj, hbj⟩
  refine ⟨⟨b, hb⟩, ?_⟩
  change J.mkQ b = J.mkQ w
  have hz : J.mkQ j = 0 := (Submodule.Quotient.mk_eq_zero J).mpr hj
  rw [← hbj, map_add, hz, add_zero]

theorem quotientRestriction_same_kernel (B J B0 : Submodule F2 W)
    (hm : B0 ⊓ J = B) :
    (A4IndexCount.quotientRestriction J B0).ker =
      (A4IndexCount.quotientRestriction B B0).ker := by
  rw [A4IndexCount.ker_quotientRestriction, A4IndexCount.ker_quotientRestriction]
  ext b
  change (b : W) ∈ J ↔ (b : W) ∈ B
  constructor
  · intro hj
    have hb : (b : W) ∈ B0 ⊓ J := ⟨b.property, hj⟩
    rwa [hm] at hb
  · intro hb
    exact (hm.symm.le.trans inf_le_right) hb

def sectionB0 (B J B0 : Submodule F2 W)
    (hc : B0 ⊔ J = ⊤) (hm : B0 ⊓ J = B) : (W ⧸ J) →ₗ[F2] (W ⧸ B) :=
  (A4IndexCount.factorViaRange (A4IndexCount.quotientRestriction J B0)
    (A4IndexCount.quotientRestriction B B0)
    (quotientRestriction_same_kernel B J B0 hm).le).comp
      (fullRange (A4IndexCount.quotientRestriction J B0)
        (LinearMap.range_eq_top.mpr (quotientRestriction_surjective J B0 hc)))

theorem range_sectionB0 (B J B0 : Submodule F2 W)
    (hc : B0 ⊔ J = ⊤) (hm : B0 ⊓ J = B) :
    (sectionB0 B J B0 hc hm).range = (A4IndexCount.quotientRestriction B B0).range := by
  rw [sectionB0, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (fullRange_surjective _ _))]
  exact A4IndexCount.factorViaRange_range _ _ _

theorem recover_sectionB0 (B J B0 : Submodule F2 W)
    (hc : B0 ⊔ J = ⊤) (hm : B0 ⊓ J = B) :
    (sectionB0 B J B0 hc hm).range.comap B.mkQ = B0 := by
  rw [range_sectionB0]
  have hB : B ≤ B0 := hm.symm.le.trans inf_le_left
  ext w
  change B.mkQ w ∈ (A4IndexCount.quotientRestriction B B0).range ↔ w ∈ B0
  constructor
  · rintro ⟨b, hb⟩
    change B.mkQ (b : W) = B.mkQ w at hb
    have hz : w - (b : W) ∈ B := by
      apply (Submodule.Quotient.mk_eq_zero B).mp
      change B.mkQ (w - (b : W)) = 0
      rw [map_sub, hb, sub_self]
    simpa only [sub_add_cancel] using B0.add_mem (hB hz) b.property
  · intro hw
    exact ⟨⟨w, hw⟩, rfl⟩

theorem sectionB0_injective (B J B0 B0' : Submodule F2 W)
    (hc : B0 ⊔ J = ⊤) (hm : B0 ⊓ J = B)
    (hc' : B0' ⊔ J = ⊤) (hm' : B0' ⊓ J = B)
    (h : sectionB0 B J B0 hc hm = sectionB0 B J B0' hc' hm') : B0 = B0' := by
  calc
    B0 = (sectionB0 B J B0 hc hm).range.comap B.mkQ :=
      (recover_sectionB0 B J B0 hc hm).symm
    _ = (sectionB0 B J B0' hc' hm').range.comap B.mkQ :=
      congrArg (fun T : (W ⧸ J) →ₗ[F2] (W ⧸ B) => T.range.comap B.mkQ) h
    _ = B0' := recover_sectionB0 B J B0' hc' hm'

def encode (X : W →ₗ[F2] V) (A : Submodule F2 V) (B : Submodule F2 W)
    (hIA : X.range ≤ A) (p : OperatorPartitions.A5GeometricIndex X A B) :
    (A →ₗ[F2] X.range) × ((W ⧸ X.ker) →ₗ[F2] (W ⧸ B)) :=
  (projectionA0 A X.range p.val.1 hIA p.property.1 p.property.2.1,
    sectionB0 B X.ker p.val.2 p.property.2.2.1 p.property.2.2.2)

theorem encode_injective (X : W →ₗ[F2] V) (A : Submodule F2 V) (B : Submodule F2 W)
    (hIA : X.range ≤ A) : Function.Injective (encode X A B hIA) := by
  intro p q h
  apply Subtype.ext
  apply Prod.ext
  · exact projectionA0_injective A X.range p.val.1 q.val.1 hIA
      p.property.1 p.property.2.1 q.property.1 q.property.2.1 (congrArg Prod.fst h)
  · exact sectionB0_injective B X.ker p.val.2 q.val.2
      p.property.2.2.1 p.property.2.2.2 q.property.2.2.1 q.property.2.2.2
      (congrArg Prod.snd h)

variable [FiniteDimensional F2 V] [FiniteDimensional F2 W]

theorem card_geometricIndex_le (X : W →ₗ[F2] V)
    (A : Submodule F2 V) (B : Submodule F2 W) (hIA : X.range ≤ A) :
    Nat.card (OperatorPartitions.A5GeometricIndex X A B) ≤
      2 ^ (Module.finrank F2 X.range *
        (Module.finrank F2 A + Module.finrank F2 (W ⧸ B))) := by
  have hfirst := CompressionCount.natCard_linearMap (U := A) (C := X.range)
  have hsecond := CompressionCount.natCard_linearMap (U := W ⧸ X.ker) (C := W ⧸ B)
  let : Finite (A →ₗ[F2] X.range) := Nat.finite_of_card_ne_zero
    (by rw [hfirst]; exact pow_ne_zero _ (by decide))
  let : Finite ((W ⧸ X.ker) →ₗ[F2] (W ⧸ B)) := Nat.finite_of_card_ne_zero
    (by rw [hsecond]; exact pow_ne_zero _ (by decide))
  have h := Nat.card_le_card_of_injective (encode X A B hIA) (encode_injective X A B hIA)
  rw [Nat.card_prod, hfirst, hsecond, X.quotKerEquivRange.finrank_eq, ← pow_add] at h
  have he : Module.finrank F2 A * Module.finrank F2 X.range +
      Module.finrank F2 X.range * Module.finrank F2 (W ⧸ B) =
      Module.finrank F2 X.range *
        (Module.finrank F2 A + Module.finrank F2 (W ⧸ B)) := by ring
  rwa [he] at h

theorem card_geometricIndex_degree_le (X : W →ₗ[F2] V)
    (A : Submodule F2 V) (B : Submodule F2 W) (hIA : X.range ≤ A) (d : Nat)
    (hA : Module.finrank F2 A ≤ d) (hB : Module.finrank F2 (W ⧸ B) ≤ d) :
    Nat.card (OperatorPartitions.A5GeometricIndex X A B) ≤
      2 ^ (2 * d * Module.finrank F2 X.range) := by
  have hs : Module.finrank F2 A + Module.finrank F2 (W ⧸ B) ≤ 2 * d := by omega
  have he : Module.finrank F2 X.range *
      (Module.finrank F2 A + Module.finrank F2 (W ⧸ B)) ≤
      2 * d * Module.finrank F2 X.range := by
    calc
      _ ≤ Module.finrank F2 X.range * (2 * d) := Nat.mul_le_mul_left _ hs
      _ = _ := by ac_rfl
  exact (card_geometricIndex_le X A B hIA).trans
    (Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2) he)

theorem card_geometricIndex_cube_le (X : W →ₗ[F2] V)
    (A : Submodule F2 V) (B : Submodule F2 W) (hIA : X.range ≤ A) (d : Nat)
    (hA : Module.finrank F2 A ≤ d) (hB : Module.finrank F2 (W ⧸ B) ≤ d) :
    Nat.card (OperatorPartitions.A5GeometricIndex X A B) ^ 3 ≤
      2 ^ (6 * d * Module.finrank F2 X.range) := by
  have h := Nat.pow_le_pow_left (card_geometricIndex_degree_le X A B hIA d hA hB) 3
  rw [← pow_mul] at h
  convert h using 1
  congr 1
  ring

end DFVSGames.Appendix.A5IndexCount
end

end OAI
