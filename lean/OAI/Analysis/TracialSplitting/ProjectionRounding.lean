import OAI.Analysis.TracialSplitting.ProjectionFrames

namespace OAI

universe uD uI


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section ProjectionSorting

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma projection_family_orthogonal {I : Type uI} [Fintype I] {f : D}
    (hf : IsStarProjection f) (e : I → D) (he : ∀ i, IsStarProjection (e i))
    (hsum : ∑ i, e i = f) : Pairwise (fun i j => e i * e j = 0) := by
  classical
  intro i j hij
  have hif : e i ≤ f := by
    rw [← hsum]
    exact Finset.single_le_sum (fun k _ => (he k).nonneg) (Finset.mem_univ i)
  have hr : IsStarProjection (f - e i) := ((he i).le_iff_sub hf).mp hif
  have hrest : ∑ k ∈ Finset.univ.erase i, e k = f - e i := by
    rw [← hsum, ← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_sub_cancel_right]
  have hjr : e j ≤ f - e i := by
    rw [← hrest]
    exact Finset.single_le_sum (fun k _ => (he k).nonneg)
      (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
  have hir : e i * (f - e i) = 0 := by
    rw [mul_sub, ((he i).le_iff_mul_eq_left hf).mp hif, (he i).isIdempotentElem, sub_self]
  exact mul_eq_zero_of_supports (he i).isIdempotentElem
    (((he j).le_iff_mul_eq_right hr).mp hjr) hir

lemma collect_max_piece (hRR : RealRankZero D) (n : ℕ) {x f g : D}
    (hx : IsStarProjection x) (hf : IsStarProjection f) (hg : IsStarProjection g)
    (v : Fin n → D) (hv : ∀ i, IsStarProjection (v i))
    (hsum : x + ∑ i, v i = f) (hxg : ProjectionSubequivalent x g)
    (hvg : ∀ i, ProjectionSubequivalent (v i) g) :
    ∃ p : D, ∃ E : Fin n → D, IsStarProjection p ∧
      (∀ i, IsStarProjection (E i)) ∧ p + ∑ i, E i = f ∧
      x ≤ p ∧ ProjectionSubequivalent p g ∧
      ∀ i, ProjectionSubequivalent (E i) p := by
  induction n generalizing x f with
  | zero =>
    refine ⟨x, Fin.elim0, hx, (fun i => Fin.elim0 i), ?_, le_rfl, hxg,
      (fun i => Fin.elim0 i)⟩
    simpa only [Fin.sum_univ_zero] using hsum
  | succ n ih =>
    have htail : 0 ≤ ∑ i : Fin n, v i.succ := Finset.sum_nonneg fun i _ => (hv _).nonneg
    have hxf : x ≤ f := by
      rw [← hsum]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => (hv i).nonneg)
    have hrest : IsStarProjection (f - x) := (hx.le_iff_sub hf).mp hxf
    have hv0rest : v 0 ≤ f - x := by
      have heq : f - x = v 0 + ∑ i : Fin n, v i.succ := by
        rw [← hsum, Fin.sum_univ_succ]; abel
      rw [heq]
      exact le_add_of_nonneg_right htail
    have hxrest : x * (f - x) = 0 := by
      rw [mul_sub, (hx.le_iff_mul_eq_left hf).mp hxf, hx.isIdempotentElem, sub_self]
    have hxv : x * v 0 = 0 := mul_eq_zero_of_supports hx.isIdempotentElem
      (((hv 0).le_iff_mul_eq_right hrest).mp hv0rest) hxrest
    obtain ⟨k, z, hk, hz, hkz, hxz, hkzcomp, hzg⟩ :=
      comparison_pair hRR hx (hv 0) hg hxv hxg (hvg 0)
    have hnewsum : k + (z + ∑ i : Fin n, v i.succ) = f := by
      rw [← add_assoc, hkz]
      simpa only [Fin.sum_univ_succ, add_assoc] using hsum
    have hkf : k ≤ f := by
      rw [← hnewsum]
      exact le_add_of_nonneg_right (add_nonneg hz.nonneg htail)
    have hf' : IsStarProjection (f - k) := (hk.le_iff_sub hf).mp hkf
    have hzsum : z + ∑ i : Fin n, v i.succ = f - k := by rw [← hnewsum]; abel
    obtain ⟨p, E, hp, hE, hpEsum, hzp, hpg, hEp⟩ :=
      ih hz hf' (fun i => v i.succ) (fun i => hv i.succ) hzsum hzg (fun i => hvg i.succ)
    refine ⟨p, Fin.cases k E, hp, ?_, ?_, hxz.trans hzp, hpg, ?_⟩
    · intro i; cases i using Fin.cases with
      | zero => exact hk
      | succ i => exact hE i
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cases_zero, Fin.cases_succ]
      calc
        p + (k + ∑ i, E i) = k + (p + ∑ i, E i) := by abel
        _ = f := by rw [hpEsum]; abel
    · intro i; cases i using Fin.cases with
      | zero => exact hkzcomp.trans (ProjectionSubequivalent.of_le hz hp hzp)
      | succ i => exact hEp i

theorem comparison_sorted_partition (hRR : RealRankZero D) (n : ℕ) {f g : D}
    (hf : IsStarProjection f) (hg : IsStarProjection g)
    (v : Fin n → D) (hv : ∀ i, IsStarProjection (v i))
    (hsum : ∑ i, v i = f) (hvg : ∀ i, ProjectionSubequivalent (v i) g) :
    ∃ e : Fin n → D, (∀ i, IsStarProjection (e i)) ∧ (∑ i, e i = f) ∧
      (∀ i j, i ≤ j → ProjectionSubequivalent (e j) (e i)) ∧
      ∀ i, ProjectionSubequivalent (e i) g := by
  induction n generalizing f g with
  | zero =>
    refine ⟨Fin.elim0, (fun i => Fin.elim0 i), ?_, ?_, (fun i => Fin.elim0 i)⟩
    · simpa only [Fin.sum_univ_zero] using hsum
    · intro i; exact Fin.elim0 i
  | succ n ih =>
    have hsum' : v 0 + ∑ i : Fin n, v i.succ = f := by
      simpa only [Fin.sum_univ_succ] using hsum
    obtain ⟨p, E, hp, hE, hpE, _, hpg, hEp⟩ := collect_max_piece hRR n (hv 0) hf hg
      (fun i => v i.succ) (fun i => hv i.succ) hsum' (hvg 0) (fun i => hvg i.succ)
    have hpf : p ≤ f := by
      rw [← hpE]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => (hE i).nonneg)
    have hr : IsStarProjection (f - p) := (hp.le_iff_sub hf).mp hpf
    have hEsum : ∑ i, E i = f - p := by rw [← hpE]; abel
    obtain ⟨s, hs, hssum, hsort, hsp⟩ := ih hr hp E hE hEsum hEp
    refine ⟨Fin.cases p s, ?_, ?_, ?_, ?_⟩
    · intro i; cases i using Fin.cases with
      | zero => exact hp
      | succ i => exact hs i
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cases_zero, Fin.cases_succ, hssum]
      abel
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact ProjectionSubequivalent.refl p hp
        | succ j => exact hsp j
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          have hbad : i.val + 1 ≤ 0 := hij
          omega
        | succ j => exact hsort i j (Fin.succ_le_succ_iff.mp hij)
    · intro i; cases i using Fin.cases with
      | zero => exact hpg
      | succ i => exact (hsp i).trans hpg

theorem full_projection_partition (hRR : RealRankZero D) {f g : D}
    (hf : IsStarProjection f) (hg : IsStarProjection g) (hfull : IsFull g) :
    ∃ n : ℕ, ∃ e : Fin n → D, (∀ i, IsStarProjection (e i)) ∧ (∑ i, e i = f) ∧
      ∀ i, ProjectionSubequivalent (e i) g := by
  obtain ⟨l, hl⟩ := exists_positive_fullness_frame hg.nonneg hfull
  let a : Fin l.length → D := l.get
  have ha : ∑ i, star (a i) * g * a i = 1 := by
    rw [← List.sum_ofFn]
    have hlist : List.ofFn (fun i => star (a i) * g * a i) =
        l.map (fun x => star x * g * x) := by
      change List.ofFn ((fun x : D => star x * g * x) ∘ l.get) = _
      rw [← List.map_ofFn, List.ofFn_get]
    rw [hlist, hl]
  let v : Fin l.length → D := fun i => g * a i * f
  have hleft (i : Fin l.length) : g * v i = v i := by
    dsimp [v]; simp only [← mul_assoc, hg.isIdempotentElem.eq]
  have hvs (i : Fin l.length) : star (v i) * v i = f * (star (a i) * g * a i) * f := by
    dsimp [v]
    simp only [star_mul, hg.isSelfAdjoint.star_eq, hf.isSelfAdjoint.star_eq, mul_assoc,
      ← mul_assoc g g, hg.isIdempotentElem.eq]
  have hsum : ∑ i, star (v i) * v i = f := by
    simp_rw [hvs]
    rw [← Finset.sum_mul, ← Finset.mul_sum, ha, mul_one, hf.isIdempotentElem]
  obtain ⟨e, he, _, hesum, hecomp⟩ := split_column hRR l.length hf (fun _ => g) v
    (fun _ => hg) hleft hsum
  exact ⟨l.length, e, he, hesum, hecomp⟩

end ProjectionSorting

section RoundingNumerics

def roundCoeff (s : ℝ) (i : ℕ) : ℝ := (⌊s * (i + 1 : ℕ)⌋ - ⌊s * i⌋ : ℤ)

def roundDeficit (s : ℝ) (i : ℕ) : ℝ := (⌊s * i⌋ : ℝ) - s * i

lemma roundCoeff_zero_or_one {s : ℝ} (hs : s ∈ Set.Icc 0 1) (i : ℕ) :
    roundCoeff s i = 0 ∨ roundCoeff s i = 1 := by
  have hlow : ⌊s * (i : ℝ)⌋ ≤ ⌊s * (i + 1 : ℕ)⌋ :=
    Int.floor_mono (by push_cast; nlinarith [hs.1])
  have hupp : ⌊s * (i + 1 : ℕ)⌋ ≤ ⌊s * (i : ℝ)⌋ + 1 := by
    calc
      _ ≤ ⌊s * (i : ℝ) + 1⌋ := Int.floor_mono (by push_cast; nlinarith [hs.2])
      _ = _ := Int.floor_add_one _
  have h : (⌊s * (i + 1 : ℕ)⌋ - ⌊s * (i : ℝ)⌋ : ℤ) = 0 ∨
      (⌊s * (i + 1 : ℕ)⌋ - ⌊s * (i : ℝ)⌋ : ℤ) = 1 := by omega
  rcases h with h | h
  · left; simp only [roundCoeff, h, Int.cast_zero]
  · right; simp only [roundCoeff, h, Int.cast_one]

lemma roundDeficit_bounds (s : ℝ) (i : ℕ) :
    -1 ≤ roundDeficit s i ∧ roundDeficit s i ≤ 0 := by
  have h₁ := Int.floor_le (s * (i : ℝ))
  have h₂ := Int.lt_floor_add_one (s * (i : ℝ))
  dsimp [roundDeficit]
  constructor <;> linarith

@[simp] lemma roundDeficit_zero (s : ℝ) : roundDeficit s 0 = 0 := by simp [roundDeficit]

lemma roundCoeff_sub (s : ℝ) (i : ℕ) :
    roundCoeff s i - s = roundDeficit s (i + 1) - roundDeficit s i := by
  dsimp only [roundCoeff, roundDeficit]
  push_cast
  ring

lemma weighted_differences_bounds (n : ℕ) (a t : ℕ → ℝ)
    (ha : ∀ i, -1 ≤ a i ∧ a i ≤ 0) (ht : ∀ i, 0 ≤ t i) (hmono : Antitone t) :
    -t 0 ≤ (∑ i ∈ Finset.range n, (a (i + 1) - a i) * t i) + a 0 * t 0 ∧
      (∑ i ∈ Finset.range n, (a (i + 1) - a i) * t i) + a 0 * t 0 ≤ 0 := by
  induction n generalizing a t with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    constructor
    · simpa only [neg_one_mul] using mul_le_mul_of_nonneg_right (ha 0).1 (ht 0)
    · exact mul_nonpos_of_nonpos_of_nonneg (ha 0).2 (ht 0)
  | succ n ih =>
    have hshift := ih (fun i => a (i + 1)) (fun i => t (i + 1))
      (fun i => ha (i + 1)) (fun i => ht (i + 1))
      (fun i j hij => hmono (Nat.add_le_add_right hij 1))
    have hδ : 0 ≤ t 0 - t 1 := sub_nonneg.mpr (hmono (Nat.zero_le 1))
    have hprodLow : -(t 0 - t 1) ≤ a 1 * (t 0 - t 1) := by
      simpa only [neg_one_mul] using mul_le_mul_of_nonneg_right (ha 1).1 hδ
    have hprodUpp : a 1 * (t 0 - t 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (ha 1).2 hδ
    rw [Finset.sum_range_succ']
    have heq :
        (∑ i ∈ Finset.range n, (a (i + 1 + 1) - a (i + 1)) * t (i + 1)) +
          (a 1 - a 0) * t 0 + a 0 * t 0 =
        ((∑ i ∈ Finset.range n, (a (i + 1 + 1) - a (i + 1)) * t (i + 1)) +
          a 1 * t 1) + a 1 * (t 0 - t 1) := by ring
    simp only [zero_add] at *
    rw [heq]
    constructor <;> linarith

lemma floor_weighted_rounding {s M : ℝ} (hM : 0 ≤ M)
    (n : ℕ) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i)
    (hmono : Antitone t) (hbound : ∀ i, t i ≤ M) :
    |(∑ i : Fin n, roundCoeff s i * t i) - s * ∑ i, t i| ≤ M := by
  let T : ℕ → ℝ := fun i => if hi : i < n then t ⟨i, hi⟩ else 0
  have hT (i : ℕ) : 0 ≤ T i := by
    dsimp only [T]
    split_ifs with hi
    · exact ht ⟨i, hi⟩
    · exact le_rfl
  have hTM : T 0 ≤ M := by
    dsimp only [T]
    split_ifs with hi
    · exact hbound ⟨0, hi⟩
    · exact hM
  have hTmono : Antitone T := by
    intro i j hij
    by_cases hi : i < n
    · by_cases hj : j < n
      · simp only [T, dite_eq_left hi, dite_eq_left hj]
        exact hmono (show (⟨i, hi⟩ : Fin n) ≤ ⟨j, hj⟩ from hij)
      · simp only [T, dite_eq_left hi, dite_eq_right hj]
        exact ht ⟨i, hi⟩
    · have hj : ¬j < n := fun h => hi (lt_of_le_of_lt hij h)
      simp only [T, dite_eq_right hi, dite_eq_right hj, le_refl]
  have h := weighted_differences_bounds n (roundDeficit s) T (roundDeficit_bounds s) hT hTmono
  simp only [roundDeficit_zero, zero_mul, add_zero, ← roundCoeff_sub] at h
  have heq : (∑ i : Fin n, roundCoeff s i * t i) - s * ∑ i, t i =
      ∑ i ∈ Finset.range n, (roundCoeff s i - s) * T i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp only [← sub_mul]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp only [T, dite_eq_left i.isLt]
  rw [heq, abs_le]
  exact ⟨by linarith [h.1], h.2.trans hM⟩

end RoundingNumerics

section ProportionalProjections

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [PartialOrder D] [StarOrderedRing D] in
lemma orthogonal_projection_sum {I : Type uI} (S : Finset I) (p : I → D)
    (hp : ∀ i ∈ S, IsStarProjection (p i))
    (hortho : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → p i * p j = 0) :
    IsStarProjection (∑ i ∈ S, p i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using IsStarProjection.zero D
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha]
    apply (hp a (Finset.mem_insert_self a S)).add
    · exact ih (fun i hi => hp i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj hij => hortho i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj) hij)
    · rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      exact hortho a (Finset.mem_insert_self a S) j (Finset.mem_insert_of_mem hj)
        (fun h => ha (h ▸ hj))

lemma trace_projection_real (τ : TracialState D) {p : D} (hp : IsStarProjection p) :
    τ.functional p = ((τ.functional p).re : ℂ) :=
  Complex.eq_re_of_ofReal_le (τ.functional.map_nonneg hp.nonneg)

lemma trace_projection_le_one (τ : TracialState D) {p : D} (hp : IsStarProjection p) :
    (τ.functional p).re ≤ 1 := by
  have h := (Complex.le_def.mp (τ.functional.monotone hp.le_one)).1
  change (τ.functional p).re ≤ (τ.functional 1).re at h
  simpa only [τ.normalized, Complex.one_re] using h

theorem proportional_projection_bound (hRR : RealRankZero D) {f g : D}
    (hf : IsStarProjection f) (hg : IsStarProjection g) (hfull : IsFull g)
    {s : ℝ} (hs : s ∈ Set.Icc 0 1) :
    ∃ e : D, IsStarProjection e ∧ e ≤ f ∧ ∀ τ : TracialState D,
      ‖τ.functional e - (s : ℂ) * τ.functional f‖ ≤ (τ.functional g).re := by
  classical
  obtain ⟨n, v, hv, hvsum, hvg⟩ := full_projection_partition hRR hf hg hfull
  obtain ⟨p, hp, hpsum, hsort, hpg⟩ :=
    comparison_sorted_partition hRR n hf hg v hv hvsum hvg
  let S : Finset (Fin n) := Finset.univ.filter (fun i => roundCoeff s i = 1)
  let e := ∑ i ∈ S, p i
  have hortho := projection_family_orthogonal hf p hp hpsum
  have he : IsStarProjection e := orthogonal_projection_sum S p (fun i _ => hp i)
    (fun _ _ _ _ hij => hortho hij)
  have hef : e ≤ f := by
    rw [← hpsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => (hp i).nonneg)
  refine ⟨e, he, hef, ?_⟩
  intro τ
  have htrace : (τ.functional e).re =
      ∑ i : Fin n, roundCoeff s i * (τ.functional (p i)).re := by
    simp only [e, map_sum, Complex.re_sum, S, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    rcases roundCoeff_zero_or_one hs i with h | h <;> simp only [h] <;> norm_num
  have hsum : (τ.functional f).re = ∑ i, (τ.functional (p i)).re := by
    rw [← hpsum, map_sum, Complex.re_sum]
  have hb := floor_weighted_rounding (s := s) (τ.functional.map_nonneg hg.nonneg).1 n
    (fun i => (τ.functional (p i)).re)
    (fun i => (τ.functional.map_nonneg (hp i).nonneg).1)
    (fun i j hij => ProjectionSubequivalent.trace_le τ (hp j) (hp i) (hsort i j hij))
    (fun i => ProjectionSubequivalent.trace_le τ (hp i) hg (hpg i))
  rw [trace_projection_real τ he, trace_projection_real τ hf,
    ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    htrace, hsum]
  exact hb

theorem uniform_proportional_subprojection (hRR : RealRankZero D)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ g : D, IsStarProjection g ∧ IsFull g ∧
      (⨆ τ : TracialState D, (τ.functional g).re) < δ)
    {f : D} (hf : IsStarProjection f) {s : ℝ} (hs : s ∈ Set.Icc 0 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e : D, IsStarProjection e ∧ e ≤ f ∧
      (⨆ τ : TracialState D, ‖τ.functional e - (s : ℂ) * τ.functional f‖) < ε := by
  obtain ⟨g, hg, hgfull, hgsmall⟩ := hsmall ε hε
  obtain ⟨e, he, hef, hbound⟩ := proportional_projection_bound hRR hf hg hgfull hs
  refine ⟨e, he, hef, lt_of_le_of_lt ?_ hgsmall⟩
  by_cases hT : Nonempty (TracialState D)
  · let := hT
    have hbg : BddAbove (Set.range (fun τ : TracialState D => (τ.functional g).re)) :=
      ⟨1, by rintro _ ⟨τ, rfl⟩; exact trace_projection_le_one τ hg⟩
    exact ciSup_le fun τ => (hbound τ).trans (le_ciSup hbg τ)
  · have : IsEmpty (TracialState D) := not_nonempty_iff.mp hT
    exact le_of_eq (congrArg sSup (by simp only [Set.range_eq_empty]))

lemma proportional_subprojection (hRR : RealRankZero D)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ g : D, IsStarProjection g ∧ IsFull g ∧
      (⨆ τ : TracialState D, (τ.functional g).re) < δ)
    {f : D} (hf : IsStarProjection f) {s : ℝ} (hs : s ∈ Set.Icc 0 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e : D, IsStarProjection e ∧ e ≤ f ∧ ∀ τ : TracialState D,
      ‖τ.functional e - (s : ℂ) * τ.functional f‖ < ε := by
  obtain ⟨g, hg, hgfull, hgsmall⟩ := hsmall ε hε
  obtain ⟨e, he, hef, hbound⟩ := proportional_projection_bound hRR hf hg hgfull hs
  refine ⟨e, he, hef, fun τ => lt_of_le_of_lt (hbound τ) ?_⟩
  have hbg : BddAbove (Set.range (fun τ : TracialState D => (τ.functional g).re)) :=
    ⟨1, by rintro _ ⟨τ, rfl⟩; exact trace_projection_le_one τ hg⟩
  exact (le_ciSup hbg τ).trans_lt hgsmall

end ProportionalProjections

end CurrentMain

end

end

end OAI
