import OAI.Analysis.KadisonSimilarity.Tracial.ConcreteMatrixTower

namespace OAI

/-! A full finite matrix stage has a minimal diagonal projection. This
is the obstruction to a diffuse generated algebra stabilizing at a stage. -/

noncomputable section
namespace KadisonSimilarity

open Generator

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_diagonal_no_proper_subprojection (E : MatrixUnitSystem ι A)
    (o : ι) (q : A) (hmem : q ∈ E.algebra) (hq : IsStarProjection q)
    (hpq : E.entry o o * q = q) (hqp : q * E.entry o o = q) :
    q = 0 ∨ q = E.entry o o := by
  change ∃ a, E.hom a = q at hmem
  obtain ⟨a, rfl⟩ := hmem
  have he : E.hom a = a o o • E.entry o o := by
    calc
      E.hom a = E.entry o o * E.hom a * E.entry o o := by rw [hpq, hqp]
      _ = a o o • E.entry o o := E.sandwich a o o o
  have hp : E.entry o o * E.entry o o = E.entry o o := by
    simpa only [ite_true] using E.mul_entry o o o o
  have hid := hq.isIdempotentElem.eq
  rw [he] at hid
  have hc : a o o * a o o = a o o :=
    (smul_left_injective ℂ (E.diagonal_ne_zero o)) (by
      simpa only [smul_mul_smul, hp] using hid)
  have hmul : a o o * (a o o - 1) = 0 := by
    rw [mul_sub, mul_one, hc, sub_self]
  rcases mul_eq_zero.mp hmul with hz | ho
  · left
    rw [he, hz, zero_smul]
  · right
    rw [he, sub_eq_zero.mp ho, one_smul]

section Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N : VonNeumannAlgebra H} [Nontrivial N.toStarSubalgebra]

theorem concreteStage_finrank (E : FiniteMatrixStage N) :
    Module.finrank ℂ E.units.concreteAlgebra = E.size ^ 2 := by
  rw [← (concreteStageEquiv E).toAlgEquiv.toLinearEquiv.finrank_eq]
  simp only [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one, pow_two]

theorem concreteStage_size_le {E F : FiniteMatrixStage N}
    (h : E.units.concreteAlgebra ≤ F.units.concreteAlgebra) : E.size ≤ F.size := by
  have hd : E.size ^ 2 ≤ F.size ^ 2 := by
    rw [← concreteStage_finrank E, ← concreteStage_finrank F]
    exact LinearMap.finrank_le_finrank_of_injective
      (f := (StarSubalgebra.inclusion h).toLinearMap) (StarSubalgebra.inclusion_injective h)
  exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hd

theorem concreteStage_eq_of_size_eq {E F : FiniteMatrixStage N}
    (h : E.units.concreteAlgebra ≤ F.units.concreteAlgebra) (hs : E.size = F.size) :
    E.units.concreteAlgebra = F.units.concreteAlgebra := by
  have hd : Module.finrank ℂ E.units.concreteAlgebra =
      Module.finrank ℂ F.units.concreteAlgebra := by
    rw [concreteStage_finrank, concreteStage_finrank, hs]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd
    (f := (StarSubalgebra.inclusion h).toLinearMap)).mp (StarSubalgebra.inclusion_injective h)
  apply le_antisymm h
  intro c hc
  obtain ⟨a, ha⟩ := hsurj ⟨c, hc⟩
  have he : (a : H →L[ℂ] H) = c :=
    congrArg (fun b : F.units.concreteAlgebra => (b : H →L[ℂ] H)) ha
  rw [← he]
  exact a.property

theorem generated_ne_stage_of_diffuse (F : ℕ → FiniteMatrixStage N)
    (hdiff : ∀ p : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra,
      IsStarProjection p → p ≠ 0 → ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧
        p * q = q ∧ q * p = q) (n : ℕ) :
    FiniteMatrixStage.generated F ≠ (F n).units.concreteAlgebra := by
  intro heq
  let E := F n
  let o : Fin E.size := ⟨0, E.positive⟩
  have hpN : IsStarProjection (E.units.entry o o) := by
    constructor
    · change E.units.entry o o * E.units.entry o o = E.units.entry o o
      simpa only [ite_true] using E.units.mul_entry o o o o
    · exact E.units.star_entry o o
  let p : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra :=
    ⟨(E.units.entry o o).val, FiniteMatrixStage.stage_le_generated F n
      ((E.units.mem_concreteAlgebra _).mpr (E.units.entry_mem o o))⟩
  let i : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra →⋆ₐ[ℂ]
      N.toStarSubalgebra := StarSubalgebra.inclusion (FiniteMatrixStage.generated_le F)
  have hinj : Function.Injective i :=
    StarSubalgebra.inclusion_injective (FiniteMatrixStage.generated_le F)
  have hip : i p = E.units.entry o o := Subtype.ext rfl
  have hp : IsStarProjection p := by
    constructor
    · change p * p = p
      apply Subtype.ext
      exact congrArg (fun a : N.toStarSubalgebra => (a : H →L[ℂ] H))
        hpN.isIdempotentElem.eq
    · change star p = p
      apply Subtype.ext
      exact congrArg (fun a : N.toStarSubalgebra => (a : H →L[ℂ] H))
        hpN.isSelfAdjoint.star_eq
  have hp0 : p ≠ 0 := by
    intro hz
    apply E.units.diagonal_ne_zero o
    rw [← hip, hz, map_zero i]
  obtain ⟨q, hq, hq0, hqp, hpq, hqp'⟩ := hdiff p hp hp0
  have hmem : i q ∈ E.units.algebra := by
    apply (E.units.mem_concreteAlgebra _).mp
    change (q : H →L[ℂ] H) ∈ (F n).units.concreteAlgebra
    rw [← heq]
    exact q.property
  have hl : E.units.entry o o * i q = i q := by
    rw [← hip, ← map_mul i p q, hpq]
  have hr : i q * E.units.entry o o = i q := by
    rw [← hip, ← map_mul i q p, hqp']
  rcases matrix_diagonal_no_proper_subprojection E.units o (i q) hmem (hq.map i) hl hr
      with hz | he
  · apply hq0
    apply hinj
    simpa only [map_zero i] using hz
  · exact hqp (hinj (he.trans hip.symm))

theorem matrix_stage_sizes_cofinal (F : ℕ → FiniteMatrixStage N)
    (hmono : Monotone (fun n => (F n).units.concreteAlgebra))
    (hdiff : ∀ p : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra,
      IsStarProjection p → p ≠ 0 → ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧
        p * q = q ∧ q * p = q) :
    ∀ b : ℕ, ∃ n, b ≤ (F n).size := by
  intro b
  by_contra hb
  have hlt (n : ℕ) : (F n).size < b :=
    Nat.lt_of_not_ge (fun h => hb ⟨n, h⟩)
  let S : Set ℕ := Set.range (fun n => (F n).size)
  have hS : S.Nonempty := ⟨(F 0).size, 0, rfl⟩
  have hB : BddAbove S := ⟨b, by rintro _ ⟨n, rfl⟩; exact (hlt n).le⟩
  obtain ⟨n₀, hn₀⟩ := Nat.sSup_mem hS hB
  change (F n₀).size = sSup S at hn₀
  have hmax (n : ℕ) : (F n).size ≤ (F n₀).size := by
    rw [hn₀]
    exact le_csSup hB ⟨n, rfl⟩
  have hstage (n : ℕ) : (F n).units.concreteAlgebra ≤ (F n₀).units.concreteAlgebra := by
    have hs : (F n₀).size = (F (max n n₀)).size :=
      le_antisymm (concreteStage_size_le (hmono (Nat.le_max_right n n₀))) (hmax _)
    have he := concreteStage_eq_of_size_eq (hmono (Nat.le_max_right n n₀)) hs
    exact (hmono (Nat.le_max_left n n₀)).trans (le_of_eq he.symm)
  apply generated_ne_stage_of_diffuse F hdiff n₀
  exact le_antisymm
    (FiniteMatrixStage.generated_minimal F _ (F n₀).units.concreteAlgebra_wotClosed hstage)
    (FiniteMatrixStage.stage_le_generated F n₀)

/-- Diffuseness forces exactly the diverging matrix sizes needed in the
finite-factor commutator argument. -/
theorem matrix_stage_sizes_tendsto (F : ℕ → FiniteMatrixStage N)
    (hmono : Monotone (fun n => (F n).units.concreteAlgebra))
    (hdiff : ∀ p : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra,
      IsStarProjection p → p ≠ 0 → ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧
        p * q = q ∧ q * p = q) :
    Filter.Tendsto (fun n => (Fintype.card (Fin (F n).size) : ℝ))
      Filter.atTop Filter.atTop := by
  have hn : Filter.Tendsto (fun n => (F n).size) Filter.atTop Filter.atTop :=
    (show Monotone (fun n => (F n).size) from fun _ _ h =>
      concreteStage_size_le (hmono h)).tendsto_atTop_atTop
        (matrix_stage_sizes_cofinal F hmono hdiff)
  convert (tendsto_natCast_atTop_atTop (R := ℝ)).comp hn using 1
  funext n
  simp only [Function.comp_apply, Fintype.card_fin]

end Concrete

end KadisonSimilarity

end

end OAI
