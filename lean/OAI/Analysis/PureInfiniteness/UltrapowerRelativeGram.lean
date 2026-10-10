import OAI.Analysis.PureInfiniteness.UltrapowerGramCuts

namespace OAI

/-! Simultaneous Gram orthogonality and orthogonality relative to one extra
coefficient. This is the finite two-pass diagonalization in KR02 Lemma 7.12;
its coefficient bound is independent of the number of spectral cells. -/

noncomputable section
open scoped NNReal ENNReal

namespace WeakPureInfiniteness

variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance : PartialOrder A := CStarAlgebra.spectralOrder A
local instance : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

theorem ultrapower_relative_cut_gram_row (hP : MainGap.PropertyP A)
    (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ Filter.atTop)]
    (δ η : ℝ≥0) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ∀ f : Fin n → NormUltra.QuotientAlgebra (fun _ : ℕ => A) U,
      (∀ i, 0 ≤ f i) → (∀ i, ‖f i‖ ≤ 1) →
      ∀ b : NormUltra.QuotientAlgebra (fun _ : ℕ => A) U,
      ∃ d : Fin n → NormUltra.QuotientAlgebra (fun _ : ℕ => A) U,
      (∀ i, ‖d i‖ ≤ C) ∧
      ∃ h : CStarMatrix (Fin 1) (Fin n) (NormUltra.QuotientAlgebra (fun _ : ℕ => A) U),
        (∀ i, h 0 i = CFC.sqrt (f i) * d i) ∧ ‖h‖ ≤ 1 ∧
        h.conjTranspose * h = NonunitalGamma.diagonalHom (fun i => MainGap.cut (f i) (δ + η)) ∧
        ∀ i j, i ≠ j → star (h 0 i) * b * h 0 j = 0 := by
  classical
  obtain ⟨C₁, hC₁, hfirst⟩ := ultrapower_cut_gram_row hP U δ hδ
  obtain ⟨C₂, hC₂, hsecond⟩ := ultrapower_matrix_cut_diagonalization hP U 1 η hη
  refine ⟨C₁ * C₂, mul_nonneg hC₁ hC₂, ?_⟩
  intro n f hfp hfn b
  obtain ⟨d, hdn, h, hentry, _, hgram⟩ := hfirst n f hfp hfn
  have hgramEntry (i j : Fin n) :
      star (h 0 i) * h 0 j = if i = j then MainGap.cut (f i) δ else 0 := by
    have he := congrArg (fun M => M i j) hgram
    change (∑ k : Fin 1, star (h k i) * h k j) =
      (if i = j then MainGap.cut (f i) δ else 0) at he
    simpa only [Fin.sum_univ_one] using he
  let M (i j : Fin n) := if i = j then MainGap.cut (f i) δ else star (h 0 i) * b * h 0 j
  have hM (i : Fin n) : M i i = MainGap.cut (f i) δ := ite_eq_left rfl
  obtain ⟨e, hen, hediag, heoff⟩ := hsecond n M
    (fun i => by rw [hM]; exact MainGap.cut_nonneg _ _)
    (fun i => by rw [hM]; exact (MainGap.norm_cut_le (hfp i) δ.2).trans (hfn i))
  let u : CStarMatrix (Fin 1) (Fin n) (NormUltra.QuotientAlgebra (fun _ : ℕ => A) U) :=
    CStarMatrix.ofMatrix (fun _ i => h 0 i * e i)
  have hugram : u.conjTranspose * u =
      NonunitalGamma.diagonalHom (fun i => MainGap.cut (f i) (δ + η)) := by
    ext i j
    change (∑ k : Fin 1, star (u k i) * u k j) =
      if i = j then MainGap.cut (f i) (δ + η) else 0
    simp only [Fin.sum_univ_one]
    change star (h 0 i * e i) * (h 0 j * e j) = _
    rw [star_mul]
    calc
      _ = star (e i) * (star (h 0 i) * h 0 j) * e j := by simp only [mul_assoc]
      _ = _ := by
        rw [hgramEntry]
        split_ifs with hij
        · subst j
          have hi := hediag i
          rw [hM] at hi
          exact hi.trans (MainGap.cut_cut (hfp i) δ.2 η.2)
        · simp only [mul_zero, zero_mul]
  refine ⟨fun i => d i * e i, fun i => (norm_mul_le _ _).trans
    (mul_le_mul (hdn i) (hen i) (norm_nonneg _) hC₁), u, ?_, ?_, hugram, ?_⟩
  · intro i
    change h 0 i * e i = CFC.sqrt (f i) * (d i * e i)
    rw [hentry, mul_assoc]
  · have hn : ‖u‖ ^ 2 ≤ 1 := by
      rw [← rectangular_norm_initial, hugram]
      exact NonunitalGamma.diagonalHom_norm_le_one _ fun i =>
        (MainGap.norm_cut_le (hfp i) (add_nonneg δ.2 η.2)).trans (hfn i)
    nlinarith [norm_nonneg u]
  · intro i j hij
    have he := heoff i j hij
    simp only [M, ite_eq_right hij] at he
    change star (h 0 i * e i) * b * (h 0 j * e j) = 0
    simpa only [star_mul, mul_assoc] using he

end WeakPureInfiniteness

end

end OAI
