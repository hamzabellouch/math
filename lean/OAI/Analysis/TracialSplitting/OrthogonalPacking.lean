import OAI.Analysis.TracialSplitting.WeightedFamilies

namespace OAI

universe uD uI

noncomputable section

namespace CurrentMain

section

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma projection_orthogonal_of_le_complement {t z : D}
    (ht : IsStarProjection t) (hz : IsStarProjection z) (hle : t ≤ 1 - z) : t * z = 0 := by
  have h := (ht.le_iff_mul_eq_left hz.one_sub).mp hle
  rw [mul_sub, mul_one] at h
  exact sub_eq_self.mp h

structure ProjectionInsertion (n : ℕ) (z₀ : D) where
  occupied : Fin (n + 1) → D
  sampled : Fin n → D
  inserted : Fin n → D
  initial : occupied 0 = z₀
  occupied_projection : ∀ a, IsStarProjection (occupied a)
  sampled_projection : ∀ a, IsStarProjection (sampled a)
  inserted_projection : ∀ a, IsStarProjection (inserted a)
  complement : ∀ a, inserted a ≤ 1 - occupied a.castSucc
  update : ∀ a, occupied a.succ = occupied a.castSucc + inserted a

namespace ProjectionInsertion

variable {n : ℕ} {z₀ : D} (S : ProjectionInsertion n z₀)

lemma monotone : Monotone S.occupied := by
  apply Fin.monotone_iff_le_succ.mpr
  intro a
  rw [S.update a]
  exact le_add_of_nonneg_right (S.inserted_projection a).nonneg

lemma inserted_le_next (a : Fin n) : S.inserted a ≤ S.occupied a.succ := by
  rw [S.update a]
  exact le_add_of_nonneg_left (S.occupied_projection a.castSucc).nonneg

lemma inserted_occupied_orthogonal (a : Fin n) : S.inserted a * S.occupied a.castSucc = 0 :=
  projection_orthogonal_of_le_complement (S.inserted_projection a)
    (S.occupied_projection a.castSucc) (S.complement a)

lemma orthogonal : Pairwise (fun a b => S.inserted a * S.inserted b = 0) := by
  have hef (a b : Fin n) (hab : a < b) : S.inserted b * S.inserted a = 0 := by
    have hle : S.inserted a ≤ S.occupied b.castSucc :=
      (S.inserted_le_next a).trans (S.monotone (Fin.succ_le_castSucc_iff.mpr hab))
    have hs := ((S.inserted_projection a).le_iff_mul_eq_right
      (S.occupied_projection b.castSucc)).mp hle
    rw [← hs, ← mul_assoc, S.inserted_occupied_orthogonal b, zero_mul]
  intro a b hab
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact projection_mul_zero_symm (S.inserted_projection b) (S.inserted_projection a) (hef a b hab)
  · exact hef b a hba

lemma final_eq : S.occupied (Fin.last n) = z₀ + ∑ a, S.inserted a := by
  have hu : ∑ a : Fin n, S.occupied a.succ =
      (∑ a : Fin n, S.occupied a.castSucc) + ∑ a, S.inserted a := by
    simp_rw [S.update]
    exact Finset.sum_add_distrib
  have h₁ := Fin.sum_univ_succ S.occupied
  have h₂ := Fin.sum_univ_castSucc S.occupied
  have he : S.occupied (Fin.last n) + (∑ a : Fin n, S.occupied a.castSucc) =
      (z₀ + ∑ a, S.inserted a) + (∑ a : Fin n, S.occupied a.castSucc) := by
    calc
      _ = ∑ a, S.occupied a := by simpa only [add_comm] using h₂.symm
      _ = S.occupied 0 + ∑ a : Fin n, S.occupied a.succ := h₁
      _ = _ := by rw [S.initial, hu]; abel
  exact add_right_cancel he

lemma initial_orthogonal (a : Fin n) : z₀ * S.inserted a = 0 := by
  have hp₀ : IsStarProjection z₀ := by simpa only [S.initial] using S.occupied_projection 0
  have hsub₀ := ((S.occupied_projection 0).le_iff_mul_eq_right
    (S.occupied_projection a.castSucc)).mp (S.monotone (Fin.zero_le _))
  have hsub : S.occupied a.castSucc * z₀ = z₀ := by simpa only [S.initial] using hsub₀
  have hzi : S.inserted a * z₀ = 0 := by
    calc
      _ = S.inserted a * (S.occupied a.castSucc * z₀) := congrArg (S.inserted a * ·) hsub.symm
      _ = 0 := by rw [← mul_assoc, S.inserted_occupied_orthogonal a, zero_mul]
  exact projection_mul_zero_symm (S.inserted_projection a) hp₀ hzi

end ProjectionInsertion

lemma exists_projection_insertion (n : ℕ) {z₀ : D} (hz₀ : IsStarProjection z₀)
    (Q : Fin n → D → D → D → Prop)
    (hstep : ∀ a z, IsStarProjection z → ∃ y t, IsStarProjection y ∧ IsStarProjection t ∧
      t ≤ 1 - z ∧ Q a z y t) :
    ∃ S : ProjectionInsertion n z₀, ∀ a,
      Q a (S.occupied a.castSucc) (S.sampled a) (S.inserted a) := by
  induction n generalizing z₀ with
  | zero =>
    refine ⟨⟨fun _ => z₀, Fin.elim0, Fin.elim0, rfl, fun _ => hz₀,
      (fun a => Fin.elim0 a), (fun a => Fin.elim0 a), (fun a => Fin.elim0 a),
      (fun a => Fin.elim0 a)⟩, (fun a => Fin.elim0 a)⟩
  | succ n ih =>
    obtain ⟨y, t, hy, ht, htz, hQ⟩ := hstep 0 z₀ hz₀
    have hzt : z₀ * t = 0 := projection_mul_zero_symm ht hz₀
      (projection_orthogonal_of_le_complement ht hz₀ htz)
    obtain ⟨S, hS⟩ := ih (hz₀.add ht hzt) (fun a => Q a.succ)
      (fun a => hstep a.succ)
    let R : ProjectionInsertion (n + 1) z₀ := {
      occupied := Fin.cons z₀ S.occupied
      sampled := Fin.cons y S.sampled
      inserted := Fin.cons t S.inserted
      initial := rfl
      occupied_projection := Fin.cases hz₀ S.occupied_projection
      sampled_projection := Fin.cases hy S.sampled_projection
      inserted_projection := Fin.cases ht S.inserted_projection
      complement := by
        intro a
        cases a using Fin.cases with
        | zero => exact htz
        | succ a => exact S.complement a
      update := by
        intro a
        cases a using Fin.cases with
        | zero => exact S.initial
        | succ a => exact S.update a }
    refine ⟨R, ?_⟩
    intro a
    cases a using Fin.cases with
    | zero => exact hQ
    | succ a => exact hS a

structure PackingStepBounds (p z y t : D) (c η ε : ℝ) (K : Finset (unitary D)) : Prop where
  mass : ∀ τ : Pureness.TracialState D,
    |(τ.functional y).re - c * (τ.functional p).re| ≤ ε
  overlap : ∀ τ : Pureness.TracialState D,
    |(τ.functional (z * y)).re - c * (τ.functional (z * p)).re| ≤ ε
  inserted_mass_lower : ∀ τ : Pureness.TracialState D,
    (τ.functional y).re - 3 * (τ.functional (z * y)).re ≤ (τ.functional t).re
  inserted_mass_upper : ∀ τ : Pureness.TracialState D,
    (τ.functional t).re ≤ (τ.functional y).re
  inserted_distance : ∀ τ : Pureness.TracialState D,
    traceTwoNorm τ (t - y) ^ 2 ≤ 5 * (τ.functional (z * y)).re
  inserted_linear : ∀ τ : Pureness.TracialState D, ∀ x : D, ‖x‖ ≤ 1 →
    ‖τ.functional ((t - y) * x)‖ ≤
      2 * Real.sqrt (τ.functional y).re * traceTwoNorm τ (t - y)
  sampled_linear : ∀ x ∈ K, ∀ τ : Pureness.TracialState D,
    ‖τ.functional (y * (x : D)) - (c : ℂ) * τ.functional (p * (x : D))‖ ≤
      η * ((τ.functional y).re + c * (τ.functional p).re) + 2 * ε
  sampled_energy : ∀ x ∈ K, ∀ τ : Pureness.TracialState D,
    traceTwoNorm τ ((x : D) * y - y * (x : D)) ^ 2 ≤
      c * traceTwoNorm τ ((x : D) * p - p * (x : D)) ^ 2 +
        6 * η * ((τ.functional y).re + c * (τ.functional p).re) + 10 * ε

lemma re_difference_le_of_complex {a b : ℂ} {c ε : ℝ}
    (h : ‖a - (c : ℂ) * b‖ ≤ ε) : |a.re - c * b.re| ≤ ε := by
  simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using (Complex.abs_re_le_norm (a - (c : ℂ) * b)).trans h

lemma exists_packing_step {I : Type uI} [Fintype I] {q z : D} (U : ProjectionRow I q)
    (hRR : RealRankZero D)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ g : D, IsStarProjection g ∧ IsFull g ∧
      (⨆ τ : Pureness.TracialState D, (τ.functional g).re) < δ)
    (hz : IsStarProjection z) (K : Finset (unitary D)) {c η ε : ℝ}
    (hc : c ∈ Set.Icc 0 1) (hη : η < 1) (hε : 0 < ε)
    (happrox : ∀ x ∈ K, ∃ H : Matrix I I ℂ,
      ‖U.sample q * (x : D) * U.sample q - U.matrix q H‖ < η) :
    ∃ y t : D, IsStarProjection y ∧ IsStarProjection t ∧ t ≤ 1 - z ∧
      PackingStepBounds (U.sample q) z y t c η ε K := by
  obtain ⟨e, he, heq, hs⟩ := U.sample_mass_overlap hRR hsmall z hc hε
  let y := U.sample e
  have hy : IsStarProjection y := U.sample_projection he
    ((he.le_iff_mul_eq_right U.projection).mp heq)
  obtain ⟨t, ht, htz, hmove⟩ := orthogonal_insertion hRR hz hy
  have hm (τ : Pureness.TracialState D) :
      |(τ.functional y).re - c * (τ.functional (U.sample q)).re| ≤ ε :=
    re_difference_le_of_complex (hs τ).1.le
  refine ⟨y, t, hy, ht, htz, {
    mass := hm
    overlap := fun τ => re_difference_le_of_complex (hs τ).2.le
    inserted_mass_lower := ?_
    inserted_mass_upper := fun τ => (hmove τ).1.2
    inserted_distance := ?_
    inserted_linear := fun τ => (hmove τ).2.2
    sampled_linear := ?_
    sampled_energy := ?_ }⟩
  · intro τ
    simpa only [τ.tracial y z] using (hmove τ).1.1
  · intro τ
    simpa only [τ.tracial y z] using (hmove τ).2.1
  · intro x hx τ
    have hb := (U.matrix_block_sampling he heq x hη hc.1 (happrox x hx) τ).1
    exact hb.trans (by dsimp [y] at hm ⊢; linarith [hm τ])
  · intro x hx τ
    have hb := (U.matrix_block_sampling he heq x hη hc.1 (happrox x hx) τ).2
    have hb' := (abs_le.mp hb).2
    dsimp [y] at hm ⊢
    linarith [hm τ]

end

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable {r : D}

structure SampledPackingRound (F : WeightedBlockFamily r) (z₀ : D)
    (K : Finset (unitary D)) (η δ : ℝ) where
  final : D
  occupied : F.Index × Bool → D
  sampled : F.Index × Bool → D
  inserted : F.Index × Bool → D
  final_projection : IsStarProjection final
  occupied_projection : ∀ a, IsStarProjection (occupied a)
  sampled_projection : ∀ a, IsStarProjection (sampled a)
  inserted_projection : ∀ a, IsStarProjection (inserted a)
  occupied_le_final : ∀ a, occupied a ≤ final
  inserted_orthogonal : Pairwise (fun a b => inserted a * inserted b = 0)
  initial_orthogonal : ∀ a, z₀ * inserted a = 0
  final_eq : final = z₀ + ∑ a, inserted a
  bounds : ∀ a, PackingStepBounds (F.range a.1) (occupied a) (sampled a) (inserted a)
    (η * F.weight a.1 / 2) η δ K

lemma exists_sampled_packing_round (hRR : RealRankZero D)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ g : D, IsStarProjection g ∧ IsFull g ∧
      (⨆ τ : Pureness.TracialState D, (τ.functional g).re) < δ)
    {z₀ : D} (hz₀ : IsStarProjection z₀) (F : WeightedBlockFamily r)
    (K : Finset (unitary D)) {η δ : ℝ} (hη : 0 < η) (hη1 : η < 1) (hδ : 0 < δ)
    (happrox : ∀ j, ∀ x ∈ K, ∃ H : Matrix (Fin (F.columns j)) (Fin (F.columns j)) ℂ,
      ‖F.range j * (x : D) * F.range j - (F.row j).matrix (F.base j) H‖ < η) :
    Nonempty (SampledPackingRound F z₀ K η δ) := by
  classical
  let e := Fintype.equivFin (F.Index × Bool)
  let Q := fun (a : Fin (Fintype.card (F.Index × Bool))) (z y t : D) =>
    PackingStepBounds (F.range (e.symm a).1) z y t (η * F.weight (e.symm a).1 / 2) η δ K
  have hstep (a : Fin (Fintype.card (F.Index × Bool))) (z : D) (hz : IsStarProjection z) :
      ∃ y t, IsStarProjection y ∧ IsStarProjection t ∧ t ≤ 1 - z ∧ Q a z y t := by
    have hc : η * F.weight (e.symm a).1 / 2 ∈ Set.Icc (0 : ℝ) 1 := by
      have hw := F.weight_le_one (e.symm a).1
      have hw0 := F.weight_pos (e.symm a).1
      constructor
      · positivity
      · nlinarith
    exact exists_packing_step (F.row (e.symm a).1) hRR hsmall hz K hc hη1 hδ (happrox _)
  obtain ⟨S, hS⟩ := exists_projection_insertion _ hz₀ Q hstep
  refine ⟨{
    final := S.occupied (Fin.last _)
    occupied := fun a => S.occupied (e a).castSucc
    sampled := fun a => S.sampled (e a)
    inserted := fun a => S.inserted (e a)
    final_projection := S.occupied_projection _
    occupied_projection := fun a => S.occupied_projection _
    sampled_projection := fun a => S.sampled_projection _
    inserted_projection := fun a => S.inserted_projection _
    occupied_le_final := fun a => S.monotone (Fin.le_last _)
    inserted_orthogonal := fun a b hab => S.orthogonal (e.injective.ne hab)
    initial_orthogonal := fun a => S.initial_orthogonal _
    final_eq := ?_
    bounds := ?_ }⟩
  · rw [e.sum_comp S.inserted]
    exact S.final_eq
  · intro a
    simpa only [Q, Equiv.symm_apply_apply] using hS (e a)

omit [StarOrderedRing D] in
lemma signed_weighted_sum (F : WeightedBlockFamily r) (η : ℝ) (f : F.Index → ℝ) :
    (∑ a : F.Index × Bool, (η * F.weight a.1 / 2) * f a.1) =
      η * ∑ j, F.weight j * f j := by
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.sum_bool]
  ring

namespace SampledPackingRound

variable {F : WeightedBlockFamily r} {z₀ : D} {K : Finset (unitary D)} {η δ : ℝ}

variable (R : SampledPackingRound F z₀ K η δ)

def sampledMass (τ : Pureness.TracialState D) : ℝ := ∑ a, (τ.functional (R.sampled a)).re

def targetMass (_R : SampledPackingRound F z₀ K η δ) (τ : Pureness.TracialState D) : ℝ :=
  η * ∑ j, F.weight j * (τ.functional (F.range j)).re

def overlap (τ : Pureness.TracialState D) : ℝ :=
  ∑ a, (τ.functional (R.occupied a * R.sampled a)).re

def totalError (_R : SampledPackingRound F z₀ K η δ) : ℝ := Fintype.card (F.Index × Bool) * δ

lemma sampledMass_nonneg (τ : Pureness.TracialState D) : 0 ≤ R.sampledMass τ :=
  Finset.sum_nonneg fun a _ => (τ.functional.map_nonneg (R.sampled_projection a).nonneg).1

lemma overlap_nonneg (τ : Pureness.TracialState D) : 0 ≤ R.overlap τ :=
  Finset.sum_nonneg fun a _ => (trace_mul_nonneg τ
    (R.occupied_projection a).nonneg (R.sampled_projection a).nonneg).1

omit [StarOrderedRing D] in
lemma sampledMass_error (τ : Pureness.TracialState D) :
    |R.sampledMass τ - R.targetMass τ| ≤ R.totalError := by
  rw [sampledMass, targetMass, ← signed_weighted_sum F η (fun j => (τ.functional (F.range j)).re),
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a, |(τ.functional (R.sampled a)).re -
        (η * F.weight a.1 / 2) * (τ.functional (F.range a.1)).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : F.Index × Bool, δ := Finset.sum_le_sum fun a _ => (R.bounds a).mass τ
    _ = R.totalError := by simp [totalError, nsmul_eq_mul]

omit [StarOrderedRing D] in
lemma totalError_nonneg (hδ : 0 ≤ δ) : 0 ≤ R.totalError := mul_nonneg (Nat.cast_nonneg _) hδ

omit [StarOrderedRing D] in
lemma insertedMass_bounds (τ : Pureness.TracialState D) :
    R.sampledMass τ - 3 * R.overlap τ ≤
      (τ.functional R.final).re - (τ.functional z₀).re ∧
    (τ.functional R.final).re - (τ.functional z₀).re ≤ R.sampledMass τ := by
  have hm : (τ.functional R.final).re - (τ.functional z₀).re =
      ∑ a, (τ.functional (R.inserted a)).re := by
    rw [R.final_eq, map_add, map_sum, Complex.add_re, Complex.re_sum]
    abel
  rw [hm]
  constructor
  · have h := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => (R.bounds a).inserted_mass_lower τ
    simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, sampledMass, overlap] using h
  · exact Finset.sum_le_sum fun a _ => (R.bounds a).inserted_mass_upper τ

lemma initial_le_final : z₀ ≤ R.final := by
  conv_rhs => rw [R.final_eq]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun a _ => (R.inserted_projection a).nonneg)

lemma overlap_le_target (τ : Pureness.TracialState D) (hη : 0 ≤ η) :
    R.overlap τ ≤ R.totalError + η * ∑ j, F.weight j * (τ.functional (R.final * F.range j)).re := by
  have hb (a : F.Index × Bool) : (τ.functional (R.occupied a * R.sampled a)).re ≤
      (η * F.weight a.1 / 2) * (τ.functional (R.final * F.range a.1)).re + δ := by
    have h := (abs_le.mp ((R.bounds a).overlap τ)).2
    have hm := trace_mul_mono_left τ (F.range_projection a.1).nonneg (R.occupied_le_final a)
    have hc : 0 ≤ η * F.weight a.1 / 2 := by
      have hw := F.weight_pos a.1
      positivity
    nlinarith
  calc
    _ ≤ ∑ a, ((η * F.weight a.1 / 2) * (τ.functional (R.final * F.range a.1)).re + δ) :=
      Finset.sum_le_sum fun a _ => hb a
    _ = _ := by
      rw [Finset.sum_add_distrib, signed_weighted_sum F η (fun j => (τ.functional (R.final * F.range j)).re)]
      simp [totalError, nsmul_eq_mul, add_comm]

omit [StarOrderedRing D] in
lemma sampled_linear_sum (τ : Pureness.TracialState D) (x : unitary D) (hx : x ∈ K) :
    (∑ a, ‖τ.functional (R.sampled a * (x : D)) -
      ((η * F.weight a.1 / 2 : ℝ) : ℂ) * τ.functional (F.range a.1 * (x : D))‖) ≤
      η * (R.sampledMass τ + R.targetMass τ) + 2 * R.totalError := by
  have h := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => (R.bounds a).sampled_linear x hx τ
  apply h.trans_eq
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sampledMass, targetMass, totalError]
  rw [signed_weighted_sum F η (fun j => (τ.functional (F.range j)).re)]

omit [StarOrderedRing D] in
lemma sampled_energy_sum (τ : Pureness.TracialState D) (x : unitary D) (hx : x ∈ K) :
    (∑ a, traceTwoNorm τ ((x : D) * R.sampled a - R.sampled a * (x : D)) ^ 2) ≤
      η * ∑ j, F.weight j * traceTwoNorm τ ((x : D) * F.range j - F.range j * (x : D)) ^ 2 +
      6 * η * (R.sampledMass τ + R.targetMass τ) + 10 * R.totalError := by
  have h := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => (R.bounds a).sampled_energy x hx τ
  apply h.trans_eq
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sampledMass, targetMass, totalError]
  rw [signed_weighted_sum F η (fun j => traceTwoNorm τ ((x : D) * F.range j - F.range j * (x : D)) ^ 2),
    signed_weighted_sum F η (fun j => (τ.functional (F.range j)).re)]

lemma inserted_energy_sum (τ : Pureness.TracialState D) (x : unitary D) :
    (∑ a, traceTwoNorm τ ((x : D) * R.inserted a - R.inserted a * (x : D)) ^ 2) ≤
      2 * ∑ a, traceTwoNorm τ ((x : D) * R.sampled a - R.sampled a * (x : D)) ^ 2 +
        40 * R.overlap τ := by
  have hx : ‖(x : D)‖ ≤ 1 := by
    have h := CStarRing.norm_coe_unitary_mul x (1 : D)
    rw [mul_one] at h
    exact h.le.trans (IsStarProjection.one D).norm_le
  have hd := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => (R.bounds a).inserted_distance τ
  have he := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
    commutator_perturb_sq τ hx (R.inserted a) (R.sampled a)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hd he
  dsimp [overlap]
  linarith

end SampledPackingRound

end CurrentMain

end

end OAI
