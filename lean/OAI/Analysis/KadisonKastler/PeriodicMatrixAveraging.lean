import OAI.Analysis.KadisonKastler.PeriodicMatrixUnits
import OAI.Analysis.KadisonKastler.MatrixAveraging
import OAI.Analysis.KadisonKastler.WeakCPLimits

namespace OAI

/-! # Averaging over the countable matrix factor

Weak limits of finite signed-permutation averages commute with the
countable matrix units, preserving both the displacement and the scalar
commutator estimate.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isSelfAdjoint_of_weak_limit {ι : Type*} {l : Filter ι} [l.NeBot]
    (a : ι → H →L[ℂ] H) (T : H →L[ℂ] H) (ha : ∀ i, IsSelfAdjoint (a i))
    (ht : ∀ x y, Tendsto (fun i => inner ℂ y (a i x)) l (𝓝 (inner ℂ y (T x)))) :
    IsSelfAdjoint T := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℂ (T x) y = inner ℂ x (T y)
  have he (i : ι) : star (inner ℂ y (a i x)) = inner ℂ x (a i y) := by
    change (starRingEnd ℂ) (inner ℂ y (a i x)) = _
    rw [inner_conj_symm]
    exact (ha i).isSymmetric x y
  have hlim := (ht x y).star.congr he
  have hid := tendsto_nhds_unique hlim (ht y x)
  change (starRingEnd ℂ) (inner ℂ y (T x)) = inner ℂ x (T y) at hid
  simpa only [inner_conj_symm] using hid

namespace FullMatrixCorner

variable {E : Submodule ℂ H} [CompleteSpace E] (F : FullMatrixCorner E)

theorem weak_limit_commutes_matrixUnits {l : Filter ℕ} [l.NeBot] (hl : l ≤ atTop)
    (a : ℕ → H →L[ℂ] H) (T : H →L[ℂ] H)
    (ha : ∀ n i j, Commute ((F.periodicMatrixUnits (n + 1)).entry i j) (a n))
    (ht : ∀ x y, Tendsto (fun n => inner ℂ y (a n x)) l (𝓝 (inner ℂ y (T x)))) :
    ∀ i j, Commute (F.entry i j) T := by
  intro i j
  apply Commute.symm
  apply F.ext_on_columns
  intro k x
  apply F.eq_of_inner_columns
  intro m y
  change inner ℂ (F.column m y) (T (F.entry i j (F.column k x))) =
    inner ℂ (F.column m y) (F.entry i j (T (F.column k x)))
  have he : ∀ᶠ n in l,
      inner ℂ (F.column m y) (a n (F.entry i j (F.column k x))) =
        inner ℂ (star (F.entry i j) (F.column m y)) (a n (F.column k x)) := by
    filter_upwards [(eventually_ge_atTop (max (max i j) (max k m))).filter_mono hl] with n hn
    have hi : i < n + 1 := by omega
    have hj : j < n + 1 := by omega
    have hk : k < n + 1 := by omega
    have hm : m < n + 1 := by omega
    let P := (F.periodicMatrixUnits (n + 1)).entry ⟨i, hi⟩ ⟨j, hj⟩
    have hright : P (F.column k x) = F.entry i j (F.column k x) :=
      F.periodicMatrixUnits_agree_on_column _ i j k hi hj hk x
    have hleft : star P (F.column m y) = star (F.entry i j) (F.column m y) := by
      rw [F.star_entry]
      change (star ((F.periodicMatrixUnits (n + 1)).entry ⟨i, hi⟩ ⟨j, hj⟩)) _ = _
      rw [(F.periodicMatrixUnits (n + 1)).star_entry]
      exact F.periodicMatrixUnits_agree_on_column _ j i m hj hi hm y
    calc
      _ = inner ℂ (F.column m y) (a n (P (F.column k x))) := by rw [hright]
      _ = inner ℂ (F.column m y) (P (a n (F.column k x))) :=
        congrArg (fun S : H →L[ℂ] H => inner ℂ (F.column m y) (S (F.column k x)))
          (ha n ⟨i, hi⟩ ⟨j, hj⟩).eq.symm
      _ = inner ℂ (star P (F.column m y)) (a n (F.column k x)) := by
        rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
      _ = _ := by rw [hleft]
  have hlim := (ht (F.entry i j (F.column k x)) (F.column m y)).congr' he
  have heq := tendsto_nhds_unique hlim (ht (F.column k x)
    (star (F.entry i j) (F.column m y)))
  simpa only [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left] using heq

theorem exists_matrixUnit_commuting_average (M : VonNeumannAlgebra H)
    (hM : ∀ i j, F.entry i j ∈ M) (h : H →L[ℂ] H) (hh : IsSelfAdjoint h)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖) :
    ∃ h0 : H →L[ℂ] H, IsSelfAdjoint h0 ∧ (∀ i j, Commute (F.entry i j) h0) ∧
      ‖h - h0‖ ≤ δ ∧ (∀ a ∈ M, ‖h0 * a - a * h0‖ ≤ δ * ‖a‖) := by
  classical
  have hfinite (n : ℕ) := exists_matrixUnitAverage M (F.periodicMatrixUnits (n + 1))
    ((F.periodicMatrixUnits (n + 1)).algebra_le_iff M.toStarSubalgebra |>.mpr
      (F.periodicMatrixUnits_mem (n + 1) M hM)) h hδ hb
  choose a hac had hab has using hfinite
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have han (n : ℕ) : ‖a n‖ ≤ ‖h‖ + δ := by
    calc
      ‖a n‖ ≤ ‖h‖ + ‖a n - h‖ := by
        simpa only [add_sub_cancel] using norm_add_le h (a n - h)
      _ ≤ ‖h‖ + δ := by rw [norm_sub_rev]; exact add_le_add le_rfl (had n)
  obtain ⟨h0, _, ht⟩ := Generator.Tracial.exists_weak_operator_ultralimit ω a
    (‖h‖ + δ) (add_nonneg (norm_nonneg h) hδ) han
  refine ⟨h0, isSelfAdjoint_of_weak_limit a h0 (fun n => has n hh) ht,
    F.weak_limit_commutes_matrixUnits hω a h0 (fun n i j =>
      hac n _ ((F.periodicMatrixUnits (n + 1)).entry_mem i j)) ht, ?_, ?_⟩
  · apply norm_le_of_weak_limit (l := (ω : Filter ℕ)) (fun n => h - a n) (h - h0) hδ had
    intro x y
    simpa only [sub_apply, inner_sub_right] using tendsto_const_nhds.sub (ht x y)
  · intro b hbM
    apply norm_le_of_weak_limit (l := (ω : Filter ℕ))
      (fun n => a n * b - b * a n) (h0 * b - b * h0)
      (mul_nonneg hδ (norm_nonneg b)) (fun n => hab n b hbM)
    intro x y
    have hlim := (ht (b x) y).sub (ht x (star b y))
    simpa only [mul_apply_eq_comp, sub_apply, inner_sub_right,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left] using hlim

theorem commute_finiteCuntz_of_commute_matrixUnits (T : H →L[ℂ] H)
    (hT : IsSelfAdjoint T) (hc : ∀ i j, Commute (F.entry i j) T)
    (n : ℕ) [NeZero n] (i : Fin n) : Commute T ((F.finiteCuntz n).entry i) := by
  let C : VonNeumannAlgebra H :=
    { toStarSubalgebra := StarSubalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H))
      centralizer_centralizer' := Set.centralizer_centralizer_centralizer _ }
  have hmem (j k : ℕ) : F.entry j k ∈ C := by
    change F.entry j k ∈ StarSubalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H))
    rw [StarSubalgebra.mem_centralizer_iff]
    intro a ha
    obtain rfl := Set.mem_singleton_iff.mp ha
    exact ⟨(hc j k).symm.eq, by rw [hT.star_eq]; exact (hc j k).symm.eq⟩
  have hS := F.finiteCuntz_mem n C hmem i
  change (F.finiteCuntz n).entry i ∈
    StarSubalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H)) at hS
  rw [StarSubalgebra.mem_centralizer_iff] at hS
  exact (hS T (Set.mem_singleton T)).1

end FullMatrixCorner

end

end KadisonKastler

end OAI
