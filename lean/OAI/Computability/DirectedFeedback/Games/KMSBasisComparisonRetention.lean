import Mathlib
import OAI.Computability.DirectedFeedback.Games.KMSBasisComparisonFibers

namespace OAI

namespace DFVSGames.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

def fullStepRetention {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : ℝ :=
  𝔼 p : Functional ell × KMS.Ambient n,
    liftedIndicator S (rankOneUpdate X p.1 p.2)

def liftRetention {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) : ℝ :=
  𝔼 X : lift S, fullStepRetention S X.val

def goodParametersEquiv {n ell : ℕ} (X : BasisMap n ell) :
    goodParameters X ≃ OutsideNeighborFactors X where
  toFun p := ⟨⟨p.val.1, ((mem_goodParameters X p.val).mp p.property).1⟩,
    ⟨p.val.2, ((mem_goodParameters X p.val).mp p.property).2⟩⟩
  invFun p := ⟨(p.1.val, p.2.val),
    (mem_goodParameters X _).mpr ⟨p.1.property, p.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem goodParameters_expect {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) (hX : Function.Injective X) :
    (goodParameters X).expect
      (fun p => liftedIndicator S (rankOneUpdate X p.1 p.2)) =
        KMS.relativeDensity S (KMS.neighbors (rangeVertex X hX)) := by
  rw [← expect_coe_eq]
  calc
    _ = 𝔼 p : OutsideNeighborFactors X,
        liftedIndicator S (rankOneUpdate X p.1.val p.2.val) :=
      Fintype.expect_equiv (goodParametersEquiv X) _ _ (fun _ => rfl)
    _ = _ := outsideNeighbor_retention S X hX

theorem fullStepRetention_compare {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) (hX : Function.Injective X) :
    |fullStepRetention S X -
      KMS.relativeDensity S (KMS.neighbors (rangeVertex X hX))| ≤
        ((2 : ℝ) ^ ell)⁻¹ + (2 : ℝ) ^ ell / (2 : ℝ) ^ n := by
  rw [← goodParameters_expect S X hX]
  apply (abs_expect_sub_restrict_le (goodParameters X)
    (fun p => liftedIndicator S (rankOneUpdate X p.1 p.2))
    (fun p => liftedIndicator_nonneg S _) (fun p => liftedIndicator_le_one S _)).trans
  simpa only [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ] using
    (badParameters_mass_le_compl X hX)

theorem liftRange_retention_expect {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) :
    (𝔼 X : lift S,
      KMS.relativeDensity S (KMS.neighbors (liftRange S X).val)) = KMS.retention S := by
  let : Nonempty (KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) :=
    ⟨LinearEquiv.refl _ _⟩
  rw [expect_eq_of_uniform_fibers (liftRange S) (liftRangeFiberAut S)
    (fun L : S => KMS.relativeDensity S (KMS.neighbors L.val))]
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ,
    Fintype.card_coe, KMS.retention]
  congr 1
  exact (Finset.sum_subtype S (fun _ => Iff.rfl)
    (fun L => KMS.relativeDensity S (KMS.neighbors L))).symm

theorem liftRetention_compare {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (hS : S.Nonempty) :
    |liftRetention S - KMS.retention S| ≤
      ((2 : ℝ) ^ ell)⁻¹ + (2 : ℝ) ^ ell / (2 : ℝ) ^ n := by
  have hLift := (lift_nonempty_iff S).mpr hS
  let : Nonempty (lift S) := ⟨⟨hLift.choose, hLift.choose_spec⟩⟩
  rw [liftRetention, ← liftRange_retention_expect S,
    ← Finset.expect_sub_distrib]
  apply (Finset.abs_expect_le _ _).trans
  apply Finset.expect_le Finset.univ_nonempty
  intro X _
  exact fullStepRetention_compare S X.val
    (injective_of_inLift ((mem_lift S X.val).mp X.property))

theorem liftRetention_compare_kms {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (hS : S.Nonempty) :
    |liftRetention S - KMS.retention S| ≤
      ((2 : ℝ) ^ ell)⁻¹ + 2 * ((2 : ℝ) ^ ell / (2 : ℝ) ^ n) := by
  have hratio : 0 ≤ (2 : ℝ) ^ ell / (2 : ℝ) ^ n := by positivity
  exact (liftRetention_compare S hS).trans (by linarith)

def liftDensity {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) : ℝ :=
  𝔼 X : BasisMap n ell, liftedIndicator S X

theorem liftDensity_eq_card {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) :
    liftDensity S = ((lift S).card : ℝ) / Fintype.card (BasisMap n ell) := by
  simp only [liftDensity, liftedIndicator, Fintype.expect_eq_sum_div_card,
    Finset.sum_boole, lift]

theorem liftDensity_pos {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (hS : S.Nonempty) : 0 < liftDensity S := by
  rw [liftDensity_eq_card]
  apply div_pos
  · exact Nat.cast_pos.mpr ((lift_nonempty_iff S).mpr hS).card_pos
  · exact Nat.cast_pos.mpr Fintype.card_pos

theorem liftDensity_mul_retention {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) :
    liftDensity S * liftRetention S =
      𝔼 X : BasisMap n ell, liftedIndicator S X * fullStepRetention S X := by
  rw [liftDensity_eq_card, liftRetention, expect_coe_eq, mass_mul_expect,
    Fintype.expect_eq_sum_div_card]
  congr 1
  simp only [liftedIndicator, ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
  rfl

theorem fullStepRetention_eq_noise {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) :
    fullStepRetention S X =
      𝔼 y : KMS.Ambient n, 𝔼 a : Functional ell,
        liftedIndicator S (X + a.smulRight y) := by
  unfold fullStepRetention
  rw [← Finset.univ_product_univ, Finset.expect_product]
  exact Finset.expect_comm _ _ _

theorem liftRetention_le_of_correlation_le {n ell : ℕ}
    (S : Finset (KMS.Vertex n ell)) (hS : S.Nonempty) (ζ : ℝ)
    (hc : (𝔼 X : BasisMap n ell,
      liftedIndicator S X * fullStepRetention S X) ≤ ζ * liftDensity S) :
    liftRetention S ≤ ζ := by
  rw [← liftDensity_mul_retention S, mul_comm ζ (liftDensity S)] at hc
  exact le_of_mul_le_mul_left hc (liftDensity_pos S hS)

end
end DFVSGames.Inverse.KMSBasisComparison

namespace DFVSGames.Inverse.KMSBasisComparison

noncomputable section
open scoped Classical
open KMSBasisComparisonPseudorandom

def LiftExpansionPrinciple : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∃ r ell₀ : ℕ, ∀ ell : ℕ, ell₀ ≤ ell →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ∀ S : Finset (KMS.Vertex n ell), S.Nonempty →
            TuplePseudorandom S r ε → liftRetention S ≤ ζ

theorem exists_binary_ratio_threshold (c ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n → c / (2 : ℝ) ^ n ≤ ε := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (c / ε) (show (1 : ℝ) < 2 by norm_num)
  refine ⟨k, fun n hn => ?_⟩
  have hp : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) hn
  have hcp : c / ε ≤ (2 : ℝ) ^ n := hk.le.trans hp
  have hc : c ≤ (2 : ℝ) ^ n * ε := (div_le_iff₀ hε).mp hcp
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) n)).mpr
  simpa only [mul_comm] using hc

theorem nonempty_of_relativeDensity_pos {Ω : Type*} [DecidableEq Ω]
    (S I : Finset Ω) (h : 0 < KMS.relativeDensity S I) : (S ∩ I).Nonempty := by
  by_contra hn
  have he : S ∩ I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  simp [KMS.relativeDensity, he] at h

theorem expansion_of_liftExpansion (h : LiftExpansionPrinciple) :
    KMS.ExpansionPrinciple := by
  intro ζ hζ hζ1
  obtain ⟨ε, hε, hε1, r, ellA, hA⟩ :=
    h (ζ / 2) (by positivity) (by linarith)
  obtain ⟨ellE, hEllE⟩ := exists_binary_ratio_threshold 1 (ζ / 8) (by positivity)
  refine ⟨ε, hε, hε1, max r 1, le_max_right _ _, max ellA ellE, ?_⟩
  intro ell hEll
  obtain ⟨nA, hnA⟩ := hA ell ((le_max_left _ _).trans hEll)
  obtain ⟨nE, hnE⟩ := exists_binary_ratio_threshold ((2 : ℝ) ^ ell)
    (ζ / 8) (by positivity)
  refine ⟨max nA nE, ?_⟩
  intro n hn S hS hret
  have hError : ((2 : ℝ) ^ ell)⁻¹ + (2 : ℝ) ^ ell / (2 : ℝ) ^ n ≤ ζ / 4 := by
    have he := hEllE ell ((le_max_right _ _).trans hEll)
    have hn' := hnE n ((le_max_right _ _).trans hn)
    rw [one_div] at he
    linarith
  by_contra hNo
  have hPseudo : GrassmannPseudorandom S r ε := by
    intro A B hAB hbudget
    by_contra hd
    have hd' : ε < KMS.relativeDensity S (KMS.interval A B) := lt_of_not_ge hd
    apply hNo
    exact ⟨A, B, hAB, hbudget.trans (le_max_left _ _),
      nonempty_of_relativeDensity_pos S _ (hε.trans hd'), hd'.le⟩
  have hLift : liftRetention S ≤ ζ / 2 :=
    hnA n ((le_max_left _ _).trans hn) S hS
      (grassmann_pseudorandom_lift S hPseudo hε.le)
  have hCmp := (abs_le.mp ((liftRetention_compare S hS).trans hError)).1
  linarith

end
end DFVSGames.Inverse.KMSBasisComparison

namespace DFVSGames.Inverse.KMSMomentToExpansion
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open KMSMomentScalar KMSAnalytic KMSLowLevel

theorem liftExpansion_of_upperMoments
    (C : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r) (R ellMin : ℕ → ℕ)
    (hupper : ∀ r : ℕ, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ ell : ℕ, ellMin r ≤ ell → ∀ n : ℕ,
      ∀ S : Finset (Vertex n ell), TuplePseudorandom S (R r) ε →
      ∀ i : ℕ, i ≤ r →
        (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 4) ≤
          C r * (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 2) * ε) :
    LiftExpansionPrinciple := by
  intro ζ hζ _hζ1
  obtain ⟨r, _hr, ε, hε, hε1, hcut⟩ := exists_general_cutoff_parameters C hC hζ
  refine ⟨ε, hε, hε1, R r, ellMin r, ?_⟩
  intro ell hell
  refine ⟨0, ?_⟩
  intro n _hn S hS hPseudo
  have hf : IsBoolean (liftedIndicator S) := by
    intro X
    unfold liftedIndicator
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hδ : 0 ≤ liftDensity S := boolean_average_nonneg hf
  have hc := uniformNoise_bound_of_general_fourthMoments (liftedIndicator S) hf
    r (C r) ε (hC r) hε.le (hupper r ε hε.le hε1 ell hell n S hPseudo)
  have heq : (𝔼 X : BasisMap n ell,
      liftedIndicator S X * fullStepRetention S X) =
      𝔼 X : BasisMap n ell, liftedIndicator S X * uniformNoise (liftedIndicator S) X := by
    apply Finset.expect_congr rfl
    intro X _
    congr 1
    rw [fullStepRetention_eq_noise, uniformNoise_apply]
  apply liftRetention_le_of_correlation_le S hS ζ
  rw [heq]
  apply hc.trans
  change ((r + 1 : ℕ) * ((C r + 1) * ε ^ ((1 : ℝ) / 4)) +
    ((2 : ℝ) ^ (r + 1))⁻¹) * liftDensity S ≤ ζ * liftDensity S
  apply mul_le_mul_of_nonneg_right _ hδ
  exact hcut.trans (by linarith)

theorem expansion_of_upperMoments
    (C : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r) (R ellMin : ℕ → ℕ)
    (hupper : ∀ r : ℕ, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ ell : ℕ, ellMin r ≤ ell → ∀ n : ℕ,
      ∀ S : Finset (Vertex n ell), TuplePseudorandom S (R r) ε →
      ∀ i : ℕ, i ≤ r →
        (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 4) ≤
          C r * (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 2) * ε) :
    KMS.ExpansionPrinciple :=
  expansion_of_liftExpansion (liftExpansion_of_upperMoments C hC R ellMin hupper)

end
end DFVSGames.Inverse.KMSMomentToExpansion

namespace DFVSGames.Inverse.KMSExpansion
noncomputable section

theorem kms_expansion : KMS.ExpansionPrinciple := by
  apply KMSMomentToExpansion.expansion_of_upperMoments
    KMSMomentConstants.fourthMomentConstant
    KMSMomentConstants.fourthMomentConstant_nonneg
    (fun r => 2 * r) (fun r => r)
  intro r ε hε _hε1 ell hell n S hS i hi
  exact KMSMomentTheorem.lifted_fourth_moment_bound r ε hε ell hell n S hS i hi

end
end DFVSGames.Inverse.KMSExpansion

namespace DFVSGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode MatrixChart

def matrixFiber {ell m : ℕ} (f : Mat ell m → Vector ell) (y : Vector ell) :
    Finset (Mat ell m) := Finset.univ.filter fun M => f M = y

def liftedFiber {ell m : ℕ} (f : Mat ell m → Vector ell) (y : Vector ell) :
    Finset (KMS.Vertex (ell + m) ell) := (matrixFiber f y).image matrixVertex

theorem liftedFiber_subset_chart {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    liftedFiber f y ⊆ matrixChart ell m := by
  intro L hL
  obtain ⟨M, _, rfl⟩ := Finset.mem_image.mp hL
  exact (mem_matrixChart _).mpr ⟨M, rfl⟩

@[simp] theorem matrixVertex_mem_liftedFiber {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) (M : Mat ell m) :
    matrixVertex M ∈ liftedFiber f y ↔ f M = y := by
  constructor
  · intro h
    obtain ⟨N, hN, hNM⟩ := Finset.mem_image.mp h
    have : N = M := matrixVertex_injective hNM
    subst N
    exact (Finset.mem_filter.mp hN).2
  · intro h
    exact Finset.mem_image.mpr ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩

theorem image_slice_points {ell m : ℕ} (S : Slice ell m)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I) :
    S.points.image matrixVertex = I ∩ matrixChart ell m := by
  ext L
  constructor
  · intro h
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_inter.mpr ⟨(hS M).mp (Finset.mem_filter.mp hM).2,
      (mem_matrixChart _).mpr ⟨M, rfl⟩⟩
  · intro h
    obtain ⟨hI, hC⟩ := Finset.mem_inter.mp h
    obtain ⟨M, rfl⟩ := (mem_matrixChart _).mp hC
    exact Finset.mem_image.mpr ⟨M,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hS M).mpr hI⟩, rfl⟩

theorem image_slice_fiber {ell m : ℕ} (S : Slice ell m)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I)
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    (S.points.filter fun M => f M = y).image matrixVertex =
      liftedFiber f y ∩ (I ∩ matrixChart ell m) := by
  ext L
  constructor
  · intro h
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hpoints, hfy⟩ := Finset.mem_filter.mp hM
    refine Finset.mem_inter.mpr ⟨(matrixVertex_mem_liftedFiber f y M).mpr hfy, ?_⟩
    rw [← image_slice_points S I hS]
    exact Finset.mem_image.mpr ⟨M, hpoints, rfl⟩
  · intro h
    obtain ⟨hf, hIC⟩ := Finset.mem_inter.mp h
    rw [← image_slice_points S I hS] at hIC
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hIC
    exact Finset.mem_image.mpr ⟨M, Finset.mem_filter.mpr
      ⟨hM, (matrixVertex_mem_liftedFiber f y M).mp hf⟩, rfl⟩

theorem constantAgreement_eq_chart_density {ell m : ℕ} (S : Slice ell m)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I)
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    S.constantAgreement f y =
      KMS.relativeDensity (liftedFiber f y) (I ∩ matrixChart ell m) := by
  unfold Slice.constantAgreement KMS.relativeDensity
  rw [Finset.expect_eq_sum_div_card, Finset.sum_boole]
  rw [← image_slice_fiber S I hS f y, ← image_slice_points S I hS]
  simp only [Finset.card_image_of_injective _ matrixVertex_injective]

theorem hasAffineSlice_of_dense_interval {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (S : Slice ell m) (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I)
    {α : ℝ} {r : ℕ} (hrows : S.rows ≤ r) (hcolumns : S.columns ≤ r)
    (hne : (liftedFiber f y ∩ I).Nonempty)
    (hdense : α ≤ KMS.relativeDensity (liftedFiber f y) I) :
    HasAffineSlice f α r := by
  obtain ⟨hIC, hα⟩ := KMS.density_bound_passes_to_chart
    (liftedFiber f y) I (matrixChart ell m)
    (liftedFiber_subset_chart f y) hne hdense
  have hpoints : S.points.Nonempty := by
    rw [← image_slice_points S I hS] at hIC
    exact Finset.image_nonempty.mp hIC
  apply hasAffineSlice_of_constant f α r S hrows hcolumns hpoints y
  rw [constantAgreement_eq_chart_density S I hS f y]
  exact hα

end
end DFVSGames.Inverse.ShortcodeFromGrassmann

namespace DFVSGames.Inverse.MatrixChart

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

theorem span_basis_values {ι : Type*} (A : Submodule K (X × Y))
    (b : Module.Basis ι K A) :
    Submodule.span K (Set.range fun i => (b i).val) = A := by
  have h := congrArg (Submodule.map A.subtype) b.span_eq
  simpa only [Submodule.map_span, Submodule.map_top, Submodule.range_subtype,
    ← Set.range_comp', Submodule.coe_subtype] using h

theorem lowerRows_basis {ι : Type*} (A : Submodule K (X × Y))
    (b : Module.Basis ι K A) :
    lowerRows (fun i => (b i).val.1) (fun i => (b i).val.2) = A := by
  exact span_basis_values A b

theorem mem_iff_annihilator_basis {ι : Type*} (B : Submodule K (X × Y))
    (b : Module.Basis ι K B.dualAnnihilator) (x : X × Y) :
    x ∈ B ↔ ∀ i, (b i).val x = 0 := by
  constructor
  · intro hx i
    exact (Submodule.mem_dualAnnihilator (b i).val).mp (b i).property x hx
  · intro h
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff B x).mp
    intro φ hφ
    let ev : B.dualAnnihilator →ₗ[K] K :=
      (Module.Dual.eval K (X × Y) x).comp B.dualAnnihilator.subtype
    have hev : ev = 0 := b.ext (fun i => h i)
    exact congrArg (fun f : B.dualAnnihilator →ₗ[K] K => f ⟨φ, hφ⟩) hev

theorem functional_coordinate_decomposition (φ : (X × Y) →ₗ[K] K) (x : X) (y : Y) :
    φ (x, y) = φ (x, 0) + φ (0, y) := by
  have h : (x, y) = (x, 0) + (0, y) := by simp
  rw [h, map_add]

theorem upperColumns_annihilator_basis {ι : Type*} (B : Submodule K (X × Y))
    (b : Module.Basis ι K B.dualAnnihilator) :
    upperColumns
      (fun i => -((b i).val.comp (LinearMap.inl K X Y)))
      (fun i => (b i).val.comp (LinearMap.inr K X Y)) = B := by
  ext x
  rw [mem_iff_annihilator_basis B b]
  simp only [upperColumns, Submodule.mem_iInf]
  change (∀ i, x ∈ LinearMap.ker
    (((b i).val.comp (LinearMap.inr K X Y)).comp (LinearMap.snd K X Y) -
      (-((b i).val.comp (LinearMap.inl K X Y))).comp (LinearMap.fst K X Y))) ↔ _
  constructor <;> intro h i
  · have hi := h i
    change (b i).val (0, x.2) - -(b i).val (x.1, 0) = 0 at hi
    rw [functional_coordinate_decomposition]
    simpa only [sub_neg_eq_add, add_comm] using hi
  · change (b i).val (0, x.2) - -(b i).val (x.1, 0) = 0
    have hi := h i
    rw [functional_coordinate_decomposition] at hi
    simpa only [sub_neg_eq_add, add_comm] using hi

theorem exists_interval_coordinates [FiniteDimensional K X] [FiniteDimensional K Y]
    (A B : Submodule K (X × Y)) :
    ∃ (n_r n_c : Nat) (d : Fin n_r → X) (s : Fin n_r → Y)
      (t : Fin n_c → X →ₗ[K] K) (q : Fin n_c → Y →ₗ[K] K),
      n_r = Module.finrank K A ∧ n_c = Module.finrank K ((X × Y) ⧸ B) ∧
      ∀ T : X →ₗ[K] Y,
        (A ≤ T.graph ∧ T.graph ≤ B) ↔
          ((∀ i, T (d i) = s i) ∧ (∀ j, (q j).comp T = t j)) := by
  let a := Module.finBasis K A
  let : Module.Free K B.dualAnnihilator := Module.Free.of_divisionRing K B.dualAnnihilator
  let b := Module.finBasis K B.dualAnnihilator
  refine ⟨Module.finrank K A, Module.finrank K B.dualAnnihilator,
    (fun i => (a i).val.1), (fun i => (a i).val.2),
    (fun i => -((b i).val.comp (LinearMap.inl K X Y))),
    (fun i => (b i).val.comp (LinearMap.inr K X Y)), rfl, ?_, ?_⟩
  · exact (Subspace.quotEquivAnnihilator B).finrank_eq.symm
  · intro T
    have h := interval_iff_slice (fun i => (a i).val.1) (fun i => (a i).val.2)
      (fun i => -((b i).val.comp (LinearMap.inl K X Y)))
      (fun i => (b i).val.comp (LinearMap.inr K X Y)) T
    simpa only [lowerRows_basis A a, upperColumns_annihilator_basis B b] using h

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.MatrixChart

open Matrix

variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]

theorem dotFunctional_surjective :
    Function.Surjective (dotFunctional (K := K) (ι := ι)) := by
  classical
  intro f
  refine ⟨fun i => f (Pi.single i 1), ?_⟩
  apply (Pi.basisFun K ι).ext
  intro i
  change (fun j => f (Pi.single j 1)) ⬝ᵥ (Pi.basisFun K ι i) =
    f (Pi.basisFun K ι i)
  simp

theorem exists_matrix_interval_slice (A B : Submodule K ((ι → K) × (κ → K))) :
    ∃ (n_r n_c : Nat) (d : Fin n_r → ι → K) (s : Fin n_r → κ → K)
      (t : Fin n_c → ι → K) (q : Fin n_c → κ → K),
      n_r = Module.finrank K A ∧
      n_c = Module.finrank K (((ι → K) × (κ → K)) ⧸ B) ∧
      ∀ M : Matrix ι κ K,
        (A ≤ matrixGraph M ∧ matrixGraph M ≤ B) ↔
          ((∀ i, d i ᵥ* M = s i) ∧ (∀ j, M *ᵥ q j = t j)) := by
  classical
  obtain ⟨nr, nc, d, s, t, q, hnr, hnc, h⟩ := exists_interval_coordinates A B
  choose tv htv using (fun j => dotFunctional_surjective (t j))
  choose qv hqv using (fun j => dotFunctional_surjective (q j))
  refine ⟨nr, nc, d, s, tv, qv, hnr, hnc, ?_⟩
  intro M
  rw [h M.vecMulLinear]
  have hj (j : Fin nc) : (q j).comp M.vecMulLinear = t j ↔ M *ᵥ qv j = tv j := by
    rw [← hqv j, ← htv j]
    exact column_equation_iff M (qv j) (tv j)
  simp only [Matrix.vecMulLinear_apply, hj]

theorem exists_bounded_matrix_interval_slice
    (A B : Submodule K ((ι → K) × (κ → K))) (r : Nat)
    (horder : Module.finrank K A +
      Module.finrank K (((ι → K) × (κ → K)) ⧸ B) ≤ r) :
    ∃ (n_r n_c : Nat) (d : Fin n_r → ι → K) (s : Fin n_r → κ → K)
      (t : Fin n_c → ι → K) (q : Fin n_c → κ → K),
      n_r ≤ r ∧ n_c ≤ r ∧
      ∀ M : Matrix ι κ K,
        (A ≤ matrixGraph M ∧ matrixGraph M ≤ B) ↔
          ((∀ i, d i ᵥ* M = s i) ∧ (∀ j, M *ᵥ q j = t j)) := by
  obtain ⟨nr, nc, d, s, t, q, hnr, hnc, h⟩ := exists_matrix_interval_slice A B
  refine ⟨nr, nc, d, s, t, q, ?_, ?_, h⟩ <;> omega

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.MatrixChart

open Matrix

theorem exists_shortcode_slice {ell m : Nat}
    (A B : Submodule (ZMod 2) (KMS.Ambient (ell + m))) :
    ∃ S : Shortcode.Slice ell m,
      S.rows = Module.finrank (ZMod 2) A ∧
      S.columns = (ell + m) - Module.finrank (ZMod 2) B ∧
      ∀ M : Shortcode.Mat ell m,
        S.Contains M ↔ A ≤ (matrixVertex M).val ∧ (matrixVertex M).val ≤ B := by
  classical
  let e := coordinateJoin (ZMod 2) ell m
  let A' := A.comap e.toLinearMap
  let B' := B.comap e.toLinearMap
  have hA : Module.finrank (ZMod 2) A' = Module.finrank (ZMod 2) A := by
    rw [show A' = A.map e.symm.toLinearMap from
      Submodule.comap_equiv_eq_map_symm e A]
    exact e.symm.finrank_map_eq A
  have hB : Module.finrank (ZMod 2) B' = Module.finrank (ZMod 2) B := by
    rw [show B' = B.map e.symm.toLinearMap from
      Submodule.comap_equiv_eq_map_symm e B]
    exact e.symm.finrank_map_eq B
  obtain ⟨nr, nc, d, s, t, q, hnr, hnc, h⟩ := exists_matrix_interval_slice A' B'
  have hE : Module.finrank (ZMod 2)
      ((Fin ell → ZMod 2) × (Fin m → ZMod 2)) = ell + m := by simp
  have hnc' : nc = (ell + m) - Module.finrank (ZMod 2) B := by
    simpa only [Submodule.finrank_quotient, hE, hB] using hnc
  let S : Shortcode.Slice ell m := ⟨nr, nc, d, s, q, t⟩
  refine ⟨S, hnr.trans hA, hnc', ?_⟩
  intro M
  have hcontains : S.Contains M ↔
      (∀ i, d i ᵥ* M = s i) ∧ (∀ j, M *ᵥ q j = t j) := by
    constructor
    · rintro ⟨hr, hc⟩
      exact ⟨fun i => funext (hr i), hc⟩
    · rintro ⟨hr, hc⟩
      exact ⟨fun i j => congrFun (hr i) j, hc⟩
  rw [hcontains, ← h M]
  have hlow : A' ≤ matrixGraph M ↔ A ≤ (matrixVertex M).val := by
    change A.comap e.toLinearMap ≤ matrixGraph M ↔
      A ≤ (matrixGraph M).map e.toLinearMap
    have hh := Submodule.comap_le_comap_iff_of_surjective
      (f := e.toLinearMap) e.surjective (p := A)
      (q := (matrixGraph M).map e.toLinearMap)
    simpa only [Submodule.comap_map_eq_of_injective e.injective] using hh
  have hupp : matrixGraph M ≤ B' ↔ (matrixVertex M).val ≤ B :=
    Submodule.map_le_iff_le_comap.symm
  exact and_congr hlow hupp

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped Classical
open Shortcode MatrixChart

def zeroFactorMass (ell m : ℕ) : ℝ :=
  ((2 : ℝ) ^ ell)⁻¹ + ((2 : ℝ) ^ m)⁻¹ - ((2 : ℝ) ^ (ell + m))⁻¹

theorem exists_zeroFactorMass_threshold {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ ell m : ℕ, N ≤ ell → N ≤ m → zeroFactorMass ell m ≤ η / 2 := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < η / 4 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨N, ?_⟩
  intro ell m hell hm
  have hpow (n : ℕ) (hn : N ≤ n) : ((2 : ℝ) ^ n)⁻¹ ≤ η / 4 := by
    have hmon : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    simpa only [one_div, inv_pow] using hmon.trans hN.le
  have hell' := hpow ell hell
  have hm' := hpow m hm
  have hnonneg : 0 ≤ ((2 : ℝ) ^ (ell + m))⁻¹ := by positivity
  unfold zeroFactorMass
  linarith

def ChartFiberRetention : Prop :=
  ∀ {ell m : ℕ}, 1 ≤ ell → 1 ≤ m →
    ∀ η : ℝ, 0 < η → η < 1 → zeroFactorMass ell m ≤ η / 2 →
      ∀ f : Mat ell m → Vector ell, η ≤ equalityAcceptance f →
        ∃ y : Vector ell, (liftedFiber f y).Nonempty ∧
          η / 4 ≤ KMS.retention (liftedFiber f y)

theorem inversePrinciple_of_expansion_and_chart
    (hKMS : KMS.ExpansionPrinciple) (hChart : ChartFiberRetention) :
    InversePrinciple := by
  intro η hη hη1
  obtain ⟨α, hαpos, hαone, r, hr, ellKMS, hKMSell⟩ :=
    hKMS (η / 4) (by positivity) (by linarith)
  obtain ⟨N, hN⟩ := exists_zeroFactorMass_threshold hη
  refine ⟨α, hαpos, hαone, r, hr, max ellKMS (max 1 N), ?_⟩
  intro ell hell
  have hellKMS : ellKMS ≤ ell := (le_max_left _ _).trans hell
  have hellone : 1 ≤ ell := (le_max_left 1 N).trans ((le_max_right _ _).trans hell)
  have hellN : N ≤ ell := (le_max_right 1 N).trans ((le_max_right _ _).trans hell)
  obtain ⟨nKMS, hKMSn⟩ := hKMSell ell hellKMS
  refine ⟨max nKMS (max 1 N), ?_⟩
  intro m hm f haccept
  have hmKMS : nKMS ≤ m := (le_max_left _ _).trans hm
  have hmone : 1 ≤ m := (le_max_left 1 N).trans ((le_max_right _ _).trans hm)
  have hmN : N ≤ m := (le_max_right 1 N).trans ((le_max_right _ _).trans hm)
  obtain ⟨y, hnonempty, hretention⟩ :=
    hChart hellone hmone η hη hη1 (hN ell m hellN hmN) f haccept
  obtain ⟨A, B, _hAB, hbudget, hintersection, hdense⟩ :=
    hKMSn (ell + m) (by omega) (liftedFiber f y) hnonempty hretention
  change Module.finrank (ZMod 2) A +
    ((ell + m) - Module.finrank (ZMod 2) B) ≤ r at hbudget
  obtain ⟨S, hrows, hcolumns, hcontains⟩ := exists_shortcode_slice A B
  apply hasAffineSlice_of_dense_interval f y (KMS.interval A B) S
  · intro M
    simpa only [KMS.interval, Finset.mem_filter, Finset.mem_univ, true_and]
      using hcontains M
  · omega
  · omega
  · exact hintersection
  · exact hdense

end
end DFVSGames.Inverse.ShortcodeFromGrassmann

namespace DFVSGames.Inverse.MatrixChart

open Matrix
open Shortcode (Vector Mat rankOne)

variable {ell m : ℕ}

@[simp] theorem dotFunctional_zero_binary :
    dotFunctional (0 : Vector ell) = 0 := by
  apply LinearMap.ext
  intro x
  change (0 : Vector ell) ⬝ᵥ x = 0
  simp

theorem dotFunctional_ne_zero {a : Vector ell} (ha : a ≠ 0) :
    dotFunctional a ≠ 0 := by
  intro h
  exact ha (dotFunctional_injective (h.trans dotFunctional_zero_binary.symm))

theorem vecMulLinear_rankOne (a : Vector ell) (l : Vector m) :
    (rankOne a l).vecMulLinear = (dotFunctional a).smulRight l := by
  apply LinearMap.ext
  intro x
  change x ᵥ* Matrix.vecMulVec a l = (a ⬝ᵥ x) • l
  rw [Matrix.vecMul_vecMulVec, dotProduct_comm x a]

theorem vecMulLinear_add_rankOne (M : Mat ell m) (a : Vector ell) (l : Vector m) :
    (M + rankOne a l).vecMulLinear = M.vecMulLinear + (dotFunctional a).smulRight l := by
  apply LinearMap.ext
  intro x
  change x ᵥ* (M + rankOne a l) = M.vecMulLinear x +
    ((dotFunctional a).smulRight l) x
  rw [Matrix.vecMul_add]
  exact congrArg (fun y => M.vecMulLinear x + y)
    (LinearMap.congr_fun (vecMulLinear_rankOne a l) x)

theorem adjacent_matrixVertex_add_rankOne (M : Mat ell m)
    (a : Vector ell) (l : Vector m) (ha : a ≠ 0) (hl : l ≠ 0) :
    KMS.Adjacent (matrixVertex M) (matrixVertex (M + rankOne a l)) := by
  apply (adjacent_matrixVertex_iff M (M + rankOne a l)).mpr
  apply (adjacent_iff_rank_one M.vecMulLinear (M + rankOne a l).vecMulLinear).mp
  rw [vecMulLinear_add_rankOne]
  exact adjacent_rank_one_step M.vecMulLinear (dotFunctional a) l
    (dotFunctional_ne_zero ha) hl

abbrev NonzeroVectorFactors (ell m : ℕ) :=
  {a : Vector ell // a ≠ 0} × {l : Vector m // l ≠ 0}

abbrev MatrixVertexChartNeighbors (M : Mat ell m) :=
  {L : KMS.Vertex (ell + m) ell //
    KMS.Adjacent (matrixVertex M) L ∧ L ∈ matrixChart ell m}

def vectorFactorMatrixNeighbor (M : Mat ell m) (p : NonzeroVectorFactors ell m) :
    MatrixVertexChartNeighbors M :=
  ⟨matrixVertex (M + rankOne p.1.val p.2.val),
    adjacent_matrixVertex_add_rankOne M p.1.val p.2.val p.1.property p.2.property,
    (mem_matrixChart _).mpr ⟨M + rankOne p.1.val p.2.val, rfl⟩⟩

theorem vectorFactorMatrixNeighbor_injective (M : Mat ell m) :
    Function.Injective (vectorFactorMatrixNeighbor M) := by
  intro p q h
  have hM : M + rankOne p.1.val p.2.val = M + rankOne q.1.val q.2.val :=
    matrixVertex_injective (congrArg Subtype.val h)
  have hrank := congrArg Matrix.vecMulLinear (add_left_cancel hM)
  rw [vecMulLinear_rankOne, vecMulLinear_rankOne] at hrank
  obtain ⟨ha, hl⟩ := binary_smulRight_unique (dotFunctional_ne_zero p.1.property)
    p.2.property hrank
  exact Prod.ext (Subtype.ext (dotFunctional_injective ha)) (Subtype.ext hl)

theorem vectorFactorMatrixNeighbor_surjective (M : Mat ell m) :
    Function.Surjective (vectorFactorMatrixNeighbor M) := by
  intro L
  obtain ⟨N, hN⟩ := (mem_matrixChart L.val).mp L.property.2
  have hMN : KMS.Adjacent (matrixVertex M) (matrixVertex N) := by
    rw [hN]
    exact L.property.1
  have hNM : KMS.Adjacent (matrixVertex N) (matrixVertex M) :=
    ⟨hMN.1.symm, by rw [inf_comm]; exact hMN.2⟩
  obtain ⟨a, l, ha, hl, hfactor⟩ := exists_smulRight_of_rank_one
    (N.vecMulLinear - M.vecMulLinear) ((adjacent_matrixVertex_iff N M).mp hNM)
  obtain ⟨v, hv⟩ := dotFunctional_surjective a
  have hv0 : v ≠ 0 := by
    intro h
    apply ha
    rw [← hv, h, dotFunctional_zero_binary]
  have hmatrix : M + rankOne v l = N := by
    apply (LinearMap.toMatrixRight' (R := ZMod 2)).symm.injective
    change (M + rankOne v l).vecMulLinear = N.vecMulLinear
    rw [vecMulLinear_add_rankOne, hv]
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp hfactor).symm
  refine ⟨(⟨v, hv0⟩, ⟨l, hl⟩), ?_⟩
  apply Subtype.ext
  change matrixVertex (M + rankOne v l) = L.val
  rw [hmatrix]
  exact hN

noncomputable def vectorFactorsEquivMatrixVertexChartNeighbors (M : Mat ell m) :
    NonzeroVectorFactors ell m ≃ MatrixVertexChartNeighbors M :=
  Equiv.ofBijective (vectorFactorMatrixNeighbor M)
    ⟨vectorFactorMatrixNeighbor_injective M, vectorFactorMatrixNeighbor_surjective M⟩

@[simp] theorem vectorFactorsEquivMatrixVertexChartNeighbors_apply (M : Mat ell m)
    (p : NonzeroVectorFactors ell m) :
    (vectorFactorsEquivMatrixVertexChartNeighbors M p).val =
      matrixVertex (M + rankOne p.1.val p.2.val) := rfl

theorem card_matrixVertexChartNeighbors (M : Mat ell m) :
    Nat.card (MatrixVertexChartNeighbors M) = (2 ^ ell - 1) * (2 ^ m - 1) := by
  classical
  rw [← Nat.card_congr (vectorFactorsEquivMatrixVertexChartNeighbors M)]
  simp only [NonzeroVectorFactors, Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    Shortcode.Vector, Fintype.card_fun, ZMod.card, Fintype.card_fin]

end DFVSGames.Inverse.MatrixChart

end OAI
