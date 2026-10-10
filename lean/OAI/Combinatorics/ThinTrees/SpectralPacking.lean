import OAI.Combinatorics.ThinTrees.Shells

namespace OAI

universe uE uι uι2 uV uι3 uV2 uV3 uV4 uV5 uV6 uι4 uη

section
open scoped Classical
open Matrix

namespace StrongThinTree.Spectral
noncomputable section
open Finset LinearMap
open scoped InnerProductSpace
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def frobSq (T : E →ₗ[ℝ] E) : ℝ := LinearMap.trace ℝ E (T.adjoint ∘ₗ T)

lemma frobSq_eq_sum {ι : Type uι} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (T : E →ₗ[ℝ] E) :
    frobSq T = ∑i, ‖T (b i)‖ ^ 2 := by
  rw [frobSq, LinearMap.trace_eq_sum_inner _ b]
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

lemma frobSq_nonneg (T : E →ₗ[ℝ] E) : 0 ≤ frobSq T := by
  rw [frobSq_eq_sum (stdOrthonormalBasis ℝ E)]
  positivity

lemma frobSq_adjoint (T : E →ₗ[ℝ] E) : frobSq T.adjoint = frobSq T := by
  rw [frobSq, adjoint_adjoint, LinearMap.trace_comp_comm', frobSq]

omit [FiniteDimensional ℝ E] in
lemma trace_bound (T : E →ₗ[ℝ] E) {ι : Type uι2} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    |LinearMap.trace ℝ E T| ≤ ∑i, ‖T (b i)‖ := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro i hi
  calc
    |⟪b i, T (b i)⟫_ℝ| ≤ ‖b i‖ * ‖T (b i)‖ := abs_real_inner_le_norm _ _
    _ = ‖T (b i)‖ := by rw [b.orthonormal.norm_eq_one, one_mul]

lemma norm_eigenvector (T : E →ₗ[ℝ] E) (i : Fin (Module.finrank ℝ E)) :
    ‖T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i)‖ = T.singularValues i := by
  let h := T.isSymmetric_adjoint_comp_self
  let b := h.eigenvectorBasis rfl
  have he := h.apply_eigenvectorBasis rfl i
  have he' := congrArg (fun x => ⟪b i, x⟫_ℝ) he
  change ⟪b i, T.adjoint (T (b i))⟫_ℝ = ⟪b i, h.eigenvalues rfl i • b i⟫_ℝ at he'
  rw [adjoint_inner_right, real_inner_self_eq_norm_sq, inner_smul_right,
    real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one, one_pow, mul_one] at he'
  rw [T.singularValues_fin rfl i, ← he', Real.sqrt_sq (norm_nonneg _)]

lemma trace_le_singular_sum (T : E →ₗ[ℝ] E) :
    |LinearMap.trace ℝ E T| ≤ ∑i : Fin (Module.finrank ℝ E), T.singularValues i := by
  simpa only [norm_eigenvector] using trace_bound T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl)

lemma frobSq_eq_singular_sum (T : E →ₗ[ℝ] E) :
    frobSq T = ∑i : Fin (Module.finrank ℝ E), T.singularValues i ^ 2 := by
  rw [frobSq_eq_sum (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl)]
  simp only [norm_eigenvector]

lemma projection_symmetric (K : Submodule ℝ E) : K.starProjection.toLinearMap.IsSymmetric := by
  intro u v
  exact K.inner_starProjection_left_eq_right u v

lemma projection_sq (K : Submodule ℝ E) :
    K.starProjection.toLinearMap ∘ₗ K.starProjection.toLinearMap = K.starProjection.toLinearMap := by
  ext v
  exact K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem v)

lemma projection_trace (K : Submodule ℝ E) :
    LinearMap.trace ℝ E K.starProjection.toLinearMap = (Module.finrank ℝ K : ℝ) := by
  exact (show LinearMap.IsProj K K.starProjection.toLinearMap from
    ⟨K.starProjection_apply_mem, fun v hv => K.starProjection_eq_self_iff.mpr hv⟩).trace

lemma projection_inner (K : Submodule ℝ E) (v : E) :
    ⟪v, K.starProjection v⟫_ℝ = ‖K.starProjection v‖ ^ 2 := by
  rw [real_inner_comm]
  exact K.re_inner_starProjection_eq_normSq v

lemma frobSq_projection_le (K : Submodule ℝ E) (T : E →ₗ[ℝ] E) :
    frobSq (K.starProjection.toLinearMap ∘ₗ T) ≤ frobSq T := by
  rw [frobSq_eq_sum (stdOrthonormalBasis ℝ E), frobSq_eq_sum (stdOrthonormalBasis ℝ E)]
  apply sum_le_sum
  intro i hi
  exact pow_le_pow_left₀ (norm_nonneg _) (K.norm_starProjection_apply_le _) 2

lemma frobSq_projection (K : Submodule ℝ E) (T : E →ₗ[ℝ] E) :
    frobSq (K.starProjection.toLinearMap ∘ₗ T) =
      LinearMap.trace ℝ E ((T ∘ₗ T.adjoint) ∘ₗ K.starProjection.toLinearMap) := by
  let P := K.starProjection.toLinearMap
  have hP : P.adjoint = P := (projection_symmetric K).adjoint_eq
  have hPP : P ∘ₗ P = P := projection_sq K
  change LinearMap.trace ℝ E ((P ∘ₗ T).adjoint ∘ₗ (P ∘ₗ T)) = _
  have heq : (P ∘ₗ T).adjoint ∘ₗ (P ∘ₗ T) = T.adjoint ∘ₗ (P ∘ₗ T) := by
    rw [adjoint_comp, hP]
    ext v
    change T.adjoint (P (P (T v))) = T.adjoint (P (T v))
    exact congrArg T.adjoint (congrArg (fun f : E →ₗ[ℝ] E => f (T v)) hPP)
  rw [heq, LinearMap.trace_comp_comm', comp_assoc, LinearMap.trace_comp_comm']

lemma weighted_tail_le {d k : ℕ} (hk : k ≤ d) (s w : Fin d → ℝ)
    (hs : Antitone s) (hn : ∀i, 0 ≤ s i)
    (hw : ∀i, 0 ≤ w i ∧ w i ≤ 1)
    (hsum : (d - k : ℕ) ≤ ∑i, w i) :
    (∑i with k ≤ i.val, s i) ≤ ∑i, s i * w i := by
  classical
  by_cases hkd : k = d
  · subst k
    have hz : univ.filter (fun i : Fin d => d ≤ i.val) = ∅ := by
      apply eq_empty_of_forall_notMem
      intro i hi
      exact (not_le_of_gt i.isLt) (mem_filter.mp hi).2
    rw [hz, sum_empty]
    exact sum_nonneg (fun i _ => mul_nonneg (hn i) (hw i).1)
  have hkd' : k < d := lt_of_le_of_ne hk hkd
  let c := s ⟨k, hkd'⟩
  let L := univ.filter (fun i : Fin d => i.val < k)
  let R := univ.filter (fun i : Fin d => k ≤ i.val)
  have hc : 0 ≤ c := hn _
  have hRcard : R.card = d - k := by
    suffices L.card = k by
      have hcard := card_filter_add_card_filter_not (s := (univ : Finset (Fin d))) (p := fun i => i.val < k)
      simp only [card_univ, Fintype.card_fin, not_lt] at hcard
      change L.card + R.card = d at hcard
      omega
    change (univ.filter (fun i : Fin d => i.val < k)).card = k
    calc
      _ = (univ : Finset (Fin k)).card := by
        apply card_bij (fun i hi => (⟨i.val, (mem_filter.mp hi).2⟩ : Fin k))
        · intro i hi; exact mem_univ _
        · intro i hi j hj he; exact Fin.ext (congrArg (fun x : Fin k => x.val) he)
        · intro j hj
          refine ⟨⟨j.val, j.isLt.trans_le hk⟩, mem_filter.mpr ⟨mem_univ _, j.isLt⟩, ?_⟩
          rfl
      _ = k := by simp
  have hsplit (f : Fin d → ℝ) : (∑i ∈ L, f i) + (∑i ∈ R, f i) = ∑i, f i := by
    simpa only [L, R, not_lt] using (sum_filter_add_sum_filter_not univ (fun i : Fin d => i.val < k) f)
  have hl : c * (∑i ∈ L, w i) ≤ ∑i ∈ L, s i * w i := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_right (hs (by exact (mem_filter.mp hi).2.le)) (hw i).1
  have hr : (∑i ∈ R, s i) - ∑i ∈ R, s i * w i ≤ c * ((d - k : ℕ) - ∑i ∈ R, w i) := by
    have hcard : (R.card : ℝ) = ∑i ∈ R, (1 : ℝ) := by simp
    rw [← hRcard, hcard, ← sum_sub_distrib, ← sum_sub_distrib, mul_sum]
    apply sum_le_sum
    intro i hi
    have hsic : s i ≤ c := hs (by exact (mem_filter.mp hi).2)
    have h := mul_le_mul_of_nonneg_right hsic (sub_nonneg.mpr (hw i).2)
    nlinarith
  have hwc : c * ((d - k : ℕ) - ∑i ∈ R, w i) ≤ c * ∑i ∈ L, w i := by
    apply mul_le_mul_of_nonneg_left _ hc
    have hspl := hsplit w
    linarith
  have hspl := hsplit (fun i => s i * w i)
  change (∑i ∈ R, s i) ≤ _
  linarith

lemma eigenvalue_eq_singular_sq (T : E →ₗ[ℝ] E) (i : Fin (Module.finrank ℝ E)) :
    T.isSymmetric_adjoint_comp_self.eigenvalues rfl i = T.singularValues i ^ 2 := by
  let h := T.isSymmetric_adjoint_comp_self
  let b := h.eigenvectorBasis rfl
  have he' := congrArg (fun x => ⟪b i, x⟫_ℝ) (h.apply_eigenvectorBasis rfl i)
  change ⟪b i, T.adjoint (T (b i))⟫_ℝ = ⟪b i, h.eigenvalues rfl i • b i⟫_ℝ at he'
  rw [adjoint_inner_right, real_inner_self_eq_norm_sq, inner_smul_right,
    real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one, one_pow, mul_one] at he'
  rw [← he']
  exact congrArg (fun x : ℝ => x ^ 2) (norm_eigenvector T i)

lemma trace_adjoint (T : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E T.adjoint = LinearMap.trace ℝ E T := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ E),
    LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ E)]
  apply sum_congr rfl
  intro i hi
  rw [adjoint_inner_right, real_inner_comm]

lemma frobSq_projection_eigenbasis (K : Submodule ℝ E) (T : E →ₗ[ℝ] E) :
    frobSq (K.starProjection.toLinearMap ∘ₗ T) =
      ∑i : Fin (Module.finrank ℝ E), T.adjoint.singularValues i ^ 2 *
        ⟪T.adjoint.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i,
          K.starProjection (T.adjoint.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i)⟫_ℝ := by
  let h := T.adjoint.isSymmetric_adjoint_comp_self
  let b := h.eigenvectorBasis rfl
  rw [frobSq_projection, LinearMap.trace_eq_sum_inner _ b]
  apply sum_congr rfl
  intro i hi
  have he : (T ∘ₗ T.adjoint) (b i) = h.eigenvalues rfl i • b i := by
    calc
      _ = (T.adjoint.adjoint ∘ₗ T.adjoint) (b i) := by rw [adjoint_adjoint]
      _ = _ := h.apply_eigenvectorBasis rfl i
  change ⟪b i, (T ∘ₗ T.adjoint) (K.starProjection (b i))⟫_ℝ = _
  rw [← T.isSymmetric_self_comp_adjoint, he, real_inner_smul_left,
    eigenvalue_eq_singular_sq]

lemma rank_approximation (T C : E →ₗ[ℝ] E) {k : ℕ}
    (hk : k ≤ Module.finrank ℝ E) (hC : Module.finrank ℝ (LinearMap.range C) ≤ k) :
    (∑i : Fin (Module.finrank ℝ E) with k ≤ i.val, T.adjoint.singularValues i ^ 2) ≤
      frobSq (T - C) := by
  let K := (LinearMap.range C)ᗮ
  let P := K.starProjection.toLinearMap
  let b := T.adjoint.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
  let w := fun i => ⟪b i, K.starProjection (b i)⟫_ℝ
  have hw (i : Fin (Module.finrank ℝ E)) : 0 ≤ w i ∧ w i ≤ 1 := by
    change 0 ≤ ⟪b i, K.starProjection (b i)⟫_ℝ ∧ _
    rw [projection_inner]
    constructor
    · positivity
    · have hh := K.norm_starProjection_apply_le (b i)
      rw [b.orthonormal.norm_eq_one] at hh
      dsimp [w]
      rw [projection_inner]
      exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans_eq (one_pow _)
  have hsum : ((Module.finrank ℝ E - k : ℕ) : ℝ) ≤ ∑i, w i := by
    have hh := (LinearMap.range C).finrank_add_finrank_orthogonal
    have hd : Module.finrank ℝ E - k ≤ Module.finrank ℝ K := by dsimp [K]; omega
    calc
      _ ≤ (Module.finrank ℝ K : ℝ) := by exact_mod_cast hd
      _ = ∑i, w i := by rw [← projection_trace, LinearMap.trace_eq_sum_inner _ b]; rfl
  have hs : Antitone (fun i : Fin (Module.finrank ℝ E) => T.adjoint.singularValues i ^ 2) := by
    intro i j hij
    exact pow_le_pow_left₀ (T.adjoint.singularValues_nonneg _) (T.adjoint.singularValues_antitone hij) 2
  have hb := weighted_tail_le hk (fun i => T.adjoint.singularValues i ^ 2) w hs
    (fun _ => sq_nonneg _) hw hsum
  have hPC : P ∘ₗ C = 0 := by
    ext x
    change K.starProjection (C x) = 0
    apply K.starProjection_apply_eq_zero_iff.mpr
    change C x ∈ (LinearMap.range C)ᗮᗮ
    rw [Submodule.orthogonal_orthogonal]
    exact LinearMap.mem_range_self C x
  have heq : P ∘ₗ (T - C) = P ∘ₗ T := by rw [comp_sub, hPC, sub_zero]
  calc
    _ ≤ ∑i : Fin (Module.finrank ℝ E), T.adjoint.singularValues i ^ 2 * w i := hb
    _ = frobSq (P ∘ₗ T) := (frobSq_projection_eigenbasis K T).symm
    _ = frobSq (P ∘ₗ (T - C)) := congrArg frobSq heq.symm
    _ ≤ frobSq (T - C) := frobSq_projection_le K (T - C)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in

lemma separated_net {V : Type uV} [DecidableEq V] (F : Finset V) (hF : F.Nonempty)
    (Y : V → E) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ S : Finset V, S ⊆ F ∧ S.Nonempty ∧
      (∀u ∈ S, ∀v ∈ S, u ≠ v → δ < ‖Y u - Y v‖) ∧
      ∀u ∈ F, ∃v ∈ S, ‖Y u - Y v‖ ≤ δ := by
  classical
  let sep : Finset V → Prop := fun S => ∀u ∈ S, ∀v ∈ S, u ≠ v → δ < ‖Y u - Y v‖
  let : DecidablePred sep := fun _ => Classical.propDecidable _
  let good := F.powerset.filter sep
  have hgood : good.Nonempty := ⟨∅, mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _), by simp [sep]⟩⟩
  obtain ⟨S, hS, hmax⟩ := exists_max_image good card hgood
  obtain ⟨hSF, hsep⟩ := mem_filter.mp hS
  have hcover : ∀u ∈ F, ∃v ∈ S, ‖Y u - Y v‖ ≤ δ := by
    intro u hu
    by_contra! hn
    have huS : u ∉ S := by
      intro huS
      have h := hn u huS
      simp only [sub_self, norm_zero] at h
      linarith
    have hnew : insert u S ∈ good := by
      apply mem_filter.mpr
      refine ⟨mem_powerset.mpr (insert_subset hu (mem_powerset.mp hSF)), ?_⟩
      intro x hx y hy hxy
      rcases mem_insert.mp hx with hxU | hxS
      · subst x
        rcases mem_insert.mp hy with hyU | hyS
        · exact (hxy hyU.symm).elim
        · exact hn y hyS
      · rcases mem_insert.mp hy with hyU | hyS
        · subst y
          rw [norm_sub_rev]; exact hn x hxS
        · exact hsep x hxS y hyS hxy
    have hh := hmax _ hnew
    rw [card_insert_of_notMem huS] at hh
    omega
  refine ⟨S, mem_powerset.mp hSF, ?_, hsep, hcover⟩
  obtain ⟨u, hu⟩ := hF
  obtain ⟨v, hv, _⟩ := hcover u hu
  exact ⟨v, hv⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma norm_sub_sq_le_twice (x y : E) : ‖x-y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have hn := norm_sub_le x y
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  have hh : ‖x-y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

omit [FiniteDimensional ℝ E] in
lemma range_le_of_basis {ι : Type uι3} [Fintype ι] (b : Module.Basis ι ℝ E)
    (T : E →ₗ[ℝ] E) (K : Submodule ℝ E) (h : ∀i, T (b i) ∈ K) :
    LinearMap.range T ≤ K := by
  rintro _ ⟨x, rfl⟩
  rw [← b.sum_repr x, map_sum]
  apply K.sum_mem
  intro i hi
  rw [map_smul]
  exact K.smul_mem _ (h i)

omit [FiniteDimensional ℝ E] in

lemma difference_span_rank {V : Type uV2} [DecidableEq V] (S : Finset V)
    (Y : V → E) {v₀ : V} (hv₀ : v₀ ∈ S) :
    Module.finrank ℝ (Submodule.span ℝ
      ((fun v => Y v - Y v₀) '' (S : Set V))) ≤ S.card - 1 := by
  classical
  let A := (S.erase v₀).image (fun v => Y v - Y v₀)
  have heq : Submodule.span ℝ ((fun v => Y v - Y v₀) '' (S : Set V)) =
      Submodule.span ℝ (A : Set E) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨v, hv, rfl⟩
      by_cases heq : v = v₀
      · simp [heq]
      · exact Submodule.subset_span (mem_image.mpr ⟨v, mem_erase.mpr ⟨heq, hv⟩, rfl⟩)
    · apply Submodule.span_mono
      intro x hx
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
      exact ⟨v, mem_of_mem_erase hv, rfl⟩
  rw [heq]
  exact (finrank_span_finset_le_card A).trans ((card_image_le).trans_eq (card_erase_of_mem hv₀))

lemma spectral_centers_at_radius {V : Type uV3} [DecidableEq V]
    (Y : V → E) (u v : Fin (Module.finrank ℝ E) → V)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (T : E →ₗ[ℝ] E) (hT : ∀i, T (b i) = Y (u i) - Y (v i))
    {p : ℕ} (hp : 1 ≤ p) (hpd : p ≤ Module.finrank ℝ E)
    {r : ℝ} (hr : 0 < r)
    (hrT : 32 * (Module.finrank ℝ E : ℝ) * r =
      ∑i : Fin (Module.finrank ℝ E) with p - 1 ≤ i.val, T.adjoint.singularValues i ^ 2) :
    ∃ S : Finset V, S ⊆ (univ.image u ∪ univ.image v) ∧ p < S.card ∧
      (∀x ∈ S, ∀y ∈ S, x ≠ y → 2 * Real.sqrt r < ‖Y x - Y y‖) := by
  classical
  let F := univ.image u ∪ univ.image v
  have hd : 0 < Module.finrank ℝ E := lt_of_lt_of_le (by omega) hpd
  have hF : F.Nonempty := ⟨u ⟨0, hd⟩, mem_union_left _ (mem_image.mpr ⟨⟨0, hd⟩, mem_univ _, rfl⟩)⟩
  obtain ⟨S, hSF, hSne, hsep, hcover⟩ := separated_net F hF Y (show 0 ≤ 2 * Real.sqrt r by positivity)
  refine ⟨S, hSF, ?_, hsep⟩
  by_contra! hSp
  obtain ⟨v₀, hv₀⟩ := hSne
  let c : V → V := fun x => if hx : x ∈ F then Classical.choose (hcover x hx) else v₀
  have hcS (x : V) : c x ∈ S := by
    dsimp [c]
    split
    · exact (Classical.choose_spec (hcover _ ‹_›)).1
    · exact hv₀
  have hcclose (x : V) (hx : x ∈ F) : ‖Y x - Y (c x)‖ ^ 2 ≤ 4 * r := by
    have hh := (Classical.choose_spec (hcover x hx)).2
    have he : c x = Classical.choose (hcover x hx) := dite_eq_left hx
    rw [he]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hh 2
    nlinarith [Real.sq_sqrt hr.le]
  have hu (i) : u i ∈ F := mem_union_left _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
  have hv (i) : v i ∈ F := mem_union_right _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
  let C := b.toBasis.constr ℝ (fun i => Y (c (u i)) - Y (c (v i)))
  let K := Submodule.span ℝ ((fun x => Y x - Y v₀) '' (S : Set V))
  have hCK : LinearMap.range C ≤ K := by
    apply range_le_of_basis b.toBasis
    intro i
    change C (b.toBasis i) ∈ K
    rw [Module.Basis.constr_basis]
    have huK : Y (c (u i)) - Y v₀ ∈ K := Submodule.subset_span ⟨_, hcS _, rfl⟩
    have hvK : Y (c (v i)) - Y v₀ ∈ K := Submodule.subset_span ⟨_, hcS _, rfl⟩
    convert K.sub_mem huK hvK using 1 ; abel
  have hCrank : Module.finrank ℝ (LinearMap.range C) ≤ p - 1 :=
    (Submodule.finrank_mono hCK).trans ((difference_span_rank S Y hv₀).trans (Nat.sub_le_sub_right hSp 1))
  have hlow := rank_approximation T C ((Nat.sub_le p 1).trans hpd) hCrank
  rw [← hrT] at hlow
  have hupp : frobSq (T - C) ≤ 16 * (Module.finrank ℝ E : ℝ) * r := by
    have hpoint (i : Fin (Module.finrank ℝ E)) : ‖(T - C) (b i)‖ ^ 2 ≤ 16 * r := by
      rw [LinearMap.sub_apply, hT]
      change ‖(Y (u i) - Y (v i)) - C (b.toBasis i)‖ ^ 2 ≤ _
      rw [Module.Basis.constr_basis]
      have heq : (Y (u i) - Y (v i)) - (Y (c (u i)) - Y (c (v i))) =
          (Y (u i) - Y (c (u i))) - (Y (v i) - Y (c (v i))) := by abel
      rw [heq]
      have hh := norm_sub_sq_le_twice (Y (u i) - Y (c (u i))) (Y (v i) - Y (c (v i)))
      linarith [hcclose (u i) (hu i), hcclose (v i) (hv i)]
    rw [frobSq_eq_sum b]
    calc
      _ ≤ ∑i : Fin (Module.finrank ℝ E), (16 * r) := sum_le_sum (fun i _ => hpoint i)
      _ = _ := by simp; ring
  have hdr : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast hd
  nlinarith [mul_pos hdr hr]

private def tail {d : ℕ} (s : Fin d → ℝ) (p : ℕ) := ∑i with p ≤ i.val + 1, s i
private def block {d : ℕ} (s : Fin d → ℝ) (p : ℕ) := ∑i with p ≤ i.val + 1 ∧ i.val + 1 < 2*p, s i

private lemma tail_split {d : ℕ} (s : Fin d → ℝ) (p : ℕ) :
    tail s p = block s p + tail s (2*p) := by
  classical
  have hh := sum_filter_add_sum_filter_not (univ.filter (fun i : Fin d => p ≤ i.val + 1))
    (fun i => i.val + 1 < 2*p) s
  have heq : (univ.filter (fun i : Fin d => p ≤ i.val+1)).filter (fun i => ¬i.val+1 < 2*p) =
      univ.filter (fun i : Fin d => 2*p ≤ i.val+1) := by
    ext i
    simp only [mem_filter, mem_univ, true_and]
    omega
  rw [heq] at hh
  simpa only [filter_filter, tail, block] using hh.symm

private lemma block_sq_le {d : ℕ} (s : Fin d → ℝ) (p : ℕ) :
    block s p ^ 2 ≤ (p : ℝ) * tail (fun i => s i ^ 2) p := by
  classical
  let B := univ.filter (fun i : Fin d => p ≤ i.val+1 ∧ i.val+1 < 2*p)
  have hcard : B.card ≤ p := by
    have hh : B.card ≤ (range p).card := by
      apply card_le_card_of_injOn (fun i : Fin d => i.val+1-p)
      · intro i hi
        have h := (mem_filter.mp hi).2
        exact mem_range.mpr (by dsimp; omega)
      · intro i hi j hj hij
        have hi' := (mem_filter.mp hi).2
        have hj' := (mem_filter.mp hj).2
        apply Fin.ext
        dsimp at hij
        omega
    simpa using hh
  have hsum : (∑i ∈ B, s i ^ 2) ≤ tail (fun i => s i ^ 2) p := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro i hi; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2.1⟩
    · intro i hi hn; positivity
  have hcs := sum_mul_sq_le_sq_mul_sq B s (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, nsmul_eq_mul, mul_one] at hcs
  calc
    _ ≤ (∑i ∈ B, s i ^ 2) * (B.card : ℝ) := hcs
    _ ≤ tail (fun i => s i ^ 2) p * (p : ℝ) :=
      mul_le_mul hsum (by exact_mod_cast hcard) (by positivity)
        (sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := mul_comm _ _

lemma dyadic_tail_selection {d p₀ L : ℕ} (s : Fin d → ℝ)
    (hs : ∀i, 0 ≤ s i) (_hp₀ : 1 ≤ p₀) (hL : 0 < L)
    (hcover : d < 2^L*p₀) (hpositive : 0 < tail s p₀) :
    ∃ p : ℕ, p₀ ≤ p ∧ p ≤ d ∧
      tail s p₀ ^ 2 ≤ (L : ℝ)^2 * ((p : ℝ) * tail (fun i => s i ^ 2) p) := by
  classical
  let p : ℕ → ℕ := fun j => 2^j*p₀
  let M : ℕ → ℝ := fun j => (p j : ℝ) * tail (fun i => s i ^ 2) (p j)
  obtain ⟨j, hj, hmax⟩ := exists_max_image (range L) M (nonempty_range_iff.mpr (ne_of_gt hL))
  have hM : 0 ≤ M j := mul_nonneg (Nat.cast_nonneg _) (sum_nonneg (fun _ _ => sq_nonneg _))
  have hzero : tail s (p L) = 0 := by
    apply sum_eq_zero
    intro i hi
    have hh := (mem_filter.mp hi).2
    dsimp [p] at hh
    omega
  have hpnext (i : ℕ) : p (i+1) = 2*p i := by dsimp [p]; rw [pow_succ]; ring
  have hsplit (i : ℕ) : tail s (p i) - tail s (p (i+1)) = block s (p i) := by
    rw [hpnext, tail_split s (p i)]
    ring
  have hsum : (∑i ∈ range L, block s (p i)) = tail s p₀ := by
    conv_lhs => enter [2, i]; rw [← hsplit]
    rw [sum_range_sub', hzero]
    simp [p]
  have hbound (i : ℕ) (hi : i ∈ range L) : block s (p i) ≤ Real.sqrt (M j) := by
    have hh := (block_sq_le s (p i)).trans (hmax i hi)
    have hn : 0 ≤ block s (p i) := sum_nonneg (fun i _ => hs i)
    nlinarith [Real.sq_sqrt hM, Real.sqrt_nonneg (M j)]
  have htotal : tail s p₀ ≤ (L : ℝ) * Real.sqrt (M j) := by
    rw [← hsum]
    calc
      _ ≤ ∑i ∈ range L, Real.sqrt (M j) := sum_le_sum hbound
      _ = _ := by simp
  have hsq : tail s p₀ ^ 2 ≤ (L : ℝ)^2 * M j := by
    have hh := pow_le_pow_left₀ hpositive.le htotal 2
    rw [mul_pow, Real.sq_sqrt hM] at hh
    exact hh
  have hpd : p j ≤ d := by
    by_contra! hpd
    have hzero : tail (fun i => s i ^ 2) (p j) = 0 := by
      apply sum_eq_zero
      intro i hi
      have hh := (mem_filter.mp hi).2
      omega
    dsimp [M] at hsq
    rw [hzero, mul_zero, mul_zero] at hsq
    nlinarith
  refine ⟨p j, ?_, hpd, hsq⟩
  have hpow : 1 ≤ 2^j := Nat.one_le_pow _ _ (by omega)
  simpa only [one_mul, p] using (Nat.mul_le_mul_right p₀ hpow)

lemma singular_tail_selection {d : ℕ} (hd : 0 < d) (s : Fin d → ℝ)
    (hs : ∀i, 0 ≤ s i) {a τ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hτ : 0 < τ)
    (htrace : τ ≤ ∑i, s i) (hfrob : a * d * (∑i, s i ^ 2) ≤ τ ^ 2) :
    ∃ p L : ℕ, a * d / 16 < p ∧ p ≤ d ∧ 0 < L ∧
      (L : ℝ) ≤ 5 + Real.logb 2 (1/a) ∧
      9 * τ ^ 2 ≤ 16 * (L : ℝ)^2 * ((p : ℝ) * tail (fun i => s i ^ 2) p) := by
  classical
  let f := ⌊a * d / 16⌋₊
  let p₀ := f+1
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have had : 0 ≤ a * d / 16 := by positivity
  have hf : (f : ℝ) ≤ a * d / 16 := Nat.floor_le had
  have hp₀ : a * d / 16 < (p₀ : ℝ) := by simpa only [p₀, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (a*d/16)
  have hp₀pos : 1 ≤ p₀ := by dsimp [p₀]; omega
  have hp₀d : p₀ ≤ d := by
    have hf' : (f : ℝ) < d := by nlinarith
    have hfn : f < d := by exact_mod_cast hf'
    dsimp [p₀]; omega
  let I := univ.filter (fun i : Fin d => i.val < f)
  have hcard : I.card ≤ f := by
    have hh : I.card ≤ (range f).card := by
      apply card_le_card_of_injOn (fun i : Fin d => i.val)
      · intro i hi; exact mem_range.mpr (mem_filter.mp hi).2
      · intro i hi j hj hij; exact Fin.ext hij
    simpa using hh
  have hhead : ∑i ∈ I, s i ≤ τ/4 := by
    have hcs := sum_mul_sq_le_sq_mul_sq I s (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, sum_const, nsmul_eq_mul, mul_one] at hcs
    have hsum : (∑i ∈ I, s i ^ 2) ≤ ∑i, s i ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i hi hn => sq_nonneg _)
    have hcard' : (I.card : ℝ) ≤ a*d/16 := (by exact_mod_cast hcard : (I.card : ℝ) ≤ f).trans hf
    have hupp := mul_le_mul hsum hcard' (Nat.cast_nonneg _) (sum_nonneg (fun _ _ => sq_nonneg _))
    have hheadn : 0 ≤ ∑i ∈ I, s i := sum_nonneg (fun i _ => hs i)
    nlinarith
  have hsplit : (∑i ∈ I, s i) + tail s p₀ = ∑i, s i := by
    have hh := sum_filter_add_sum_filter_not univ (fun i : Fin d => i.val < f) s
    have heq : univ.filter (fun i : Fin d => ¬i.val < f) =
        univ.filter (fun i : Fin d => p₀ ≤ i.val+1) := by
      ext i
      simp only [mem_filter, mem_univ, true_and]
      dsimp [p₀]
      omega
    rw [heq] at hh
    exact hh
  have htail : 3*τ/4 ≤ tail s p₀ := by linarith
  let q := d / p₀
  let L := q.log2 + 1
  have hq : q ≠ 0 := by
    have hqp : 0 < q := Nat.div_pos hp₀d (by omega)
    omega
  have hL : 0 < L := by dsimp [L]; omega
  have hcover : d < 2^L*p₀ := by
    have hh : q < 2^L := (Nat.log2_lt hq).mp (by dsimp [L]; omega)
    exact (Nat.div_lt_iff_lt_mul (by omega)).mp hh
  have hp₀r : (0 : ℝ) < p₀ := by exact_mod_cast (show 0 < p₀ by omega)
  have hqreal : (q : ℝ) ≤ 16/a := by
    have hh : (q : ℝ) * p₀ ≤ d := by exact_mod_cast (Nat.div_mul_le_self d p₀)
    have hqn : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    apply (le_div_iff₀ ha).mpr
    nlinarith
  have hlog : (L : ℝ) ≤ 5 + Real.logb 2 (1/a) := by
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_ne_zero hq)
    have hmono := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hqpos (by positivity : (0 : ℝ) < 16/a)).mpr hqreal
    have hlogq := Real.log2_le_logb q
    have hlog16 : Real.logb 2 (16/a) = 4 + Real.logb 2 (1/a) := by
      rw [show (16 : ℝ)/a = 2^4*(1/a) by ring, Real.logb_mul (by norm_num) (ne_of_gt (by positivity : (0 : ℝ) < 1/a)), Real.logb_pow]
      norm_num
    rw [hlog16] at hmono
    dsimp [L]
    push_cast
    linarith
  obtain ⟨p, hpp, hpd, hpbig⟩ := dyadic_tail_selection s hs hp₀pos hL hcover (by linarith)
  refine ⟨p, L, hp₀.trans_le (by exact_mod_cast hpp), hpd, hL, hlog, ?_⟩
  have htailn : 0 ≤ tail s p₀ := by linarith
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 3*τ/4) htail 2
  nlinarith

lemma trace_sq_le_frobSq (T : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E T ^ 2 ≤ (Module.finrank ℝ E : ℝ) * frobSq T := by
  let b := stdOrthonormalBasis ℝ E
  have hh := trace_bound T b
  have hn : 0 ≤ ∑i, ‖T (b i)‖ := sum_nonneg (fun _ _ => norm_nonneg _)
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hh 2
  have hcs := sum_mul_sq_le_sq_mul_sq univ (fun i => ‖T (b i)‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hcs
  rw [← frobSq_eq_sum b] at hcs
  rw [sq_abs] at hsq
  exact hsq.trans (hcs.trans_eq (mul_comm _ _))

lemma spectral_packing_log {V : Type uV4} [DecidableEq V]
    (Y : V → E) (u v : Fin (Module.finrank ℝ E) → V)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (T : E →ₗ[ℝ] E) (hT : ∀i, T (b i) = Y (u i) - Y (v i))
    {a : ℝ} (ha : 0 < a) (htrace : 0 < |LinearMap.trace ℝ E T|)
    (hassume : a * Module.finrank ℝ E * frobSq T ≤ LinearMap.trace ℝ E T ^ 2) :
    a ≤ 1 ∧ ∃ S : Finset V, ∃ r : ℝ, 0 < r ∧
      S ⊆ (univ.image u ∪ univ.image v) ∧ 2 ≤ S.card ∧
      a * Module.finrank ℝ E / 16 ≤ S.card ∧
      9 * LinearMap.trace ℝ E T ^ 2 ≤
        512 * Module.finrank ℝ E * (5 + Real.logb 2 (1/a))^2 * (S.card * r) ∧
      (∀x ∈ S, ∀y ∈ S, x ≠ y → 2 * Real.sqrt r < ‖Y x - Y y‖) := by
  classical
  let d := Module.finrank ℝ E
  let τ := |LinearMap.trace ℝ E T|
  have htsq : τ ^ 2 = LinearMap.trace ℝ E T ^ 2 := sq_abs _
  have htpos : 0 < τ ^ 2 := sq_pos_of_pos htrace
  have htraceF := trace_sq_le_frobSq T
  have hdn : (0 : ℝ) < d := by
    have hf := frobSq_nonneg T
    dsimp [d]
    by_contra! hn
    have hz : (Module.finrank ℝ E : ℝ) = 0 := le_antisymm hn (Nat.cast_nonneg _)
    rw [hz, zero_mul] at htraceF
    nlinarith
  have hd : 0 < d := by exact_mod_cast hdn
  have hfpos : 0 < frobSq T := by nlinarith
  have ha1 : a ≤ 1 := by
    have hh : 0 < (d : ℝ) * frobSq T := mul_pos hdn hfpos
    have hh' : a * ((d : ℝ) * frobSq T) ≤ (d : ℝ) * frobSq T := by
      calc
        _ = a * d * frobSq T := by ring
        _ ≤ LinearMap.trace ℝ E T ^ 2 := hassume
        _ ≤ _ := htraceF
    exact (mul_le_mul_iff_left₀ hh).mp (by simpa only [mul_comm, one_mul] using hh')
  let s := fun i : Fin d => T.adjoint.singularValues i
  have hs (i : Fin d) : 0 ≤ s i := T.adjoint.singularValues_nonneg i
  have hsum : τ ≤ ∑i, s i := by
    simpa only [trace_adjoint] using trace_le_singular_sum T.adjoint
  have hsq : a * d * (∑i, s i ^ 2) ≤ τ ^ 2 := by
    rw [← frobSq_eq_singular_sum T.adjoint, frobSq_adjoint, htsq]
    exact hassume
  obtain ⟨p, L, hpmin, hpd, hL, hlog, hpbig⟩ := singular_tail_selection hd s hs ha ha1 htrace hsum hsq
  have hpp : 1 ≤ p := by
    have hpp' : (0 : ℝ) < p := lt_of_le_of_lt (by positivity) hpmin
    have : 0 < p := by exact_mod_cast hpp'
    omega
  let tailVal := tail (fun i => s i ^ 2) p
  have htailpos : 0 < tailVal := by
    have hn : 0 ≤ tailVal := sum_nonneg (fun _ _ => sq_nonneg _)
    by_contra! hh
    have hz : tailVal = 0 := le_antisymm hh hn
    change 9*τ^2 ≤ 16*(L:ℝ)^2*((p:ℝ)*tailVal) at hpbig
    rw [hz, mul_zero, mul_zero] at hpbig
    nlinarith
  let r := tailVal / (32*d)
  have hr : 0 < r := div_pos htailpos (by positivity)
  have hrt : 32*(d:ℝ)*r = tailVal := by dsimp [r]; field_simp
  have heq : tailVal =
      ∑i : Fin d with p-1 ≤ i.val, T.adjoint.singularValues i ^ 2 := by
    unfold tailVal tail
    apply sum_congr
    · ext i
      simp only [mem_filter, mem_univ, true_and]
      omega
    · intro i hi; rfl
  obtain ⟨S, hSF, hpS, hsep⟩ := spectral_centers_at_radius Y u v b T hT hpp hpd hr (hrt.trans heq)
  have hpSr : (p : ℝ) ≤ S.card := by exact_mod_cast hpS.le
  have hSr : 0 ≤ (S.card : ℝ)*r := mul_nonneg (Nat.cast_nonneg _) hr.le
  have hpr : (p : ℝ)*r ≤ S.card*r := mul_le_mul_of_nonneg_right hpSr hr.le
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hlogn : 0 ≤ 5+Real.logb 2 (1/a) := hLr.le.trans hlog
  have hLsq := pow_le_pow_left₀ hLr.le hlog 2
  refine ⟨ha1, S, r, hr, hSF, by omega, hpmin.le.trans hpSr, ?_, hsep⟩
  have hpbig' : 9*τ^2 ≤ 512*(d:ℝ)*(L:ℝ)^2*((p:ℝ)*r) := by
    change 9*τ^2 ≤ 16*(L:ℝ)^2*((p:ℝ)*tailVal) at hpbig
    rw [← hrt] at hpbig
    convert hpbig using 1 ; ring
  rw [← htsq]
  calc
    _ ≤ 512*(d:ℝ)*(L:ℝ)^2*((p:ℝ)*r) := hpbig'
    _ ≤ 512*(d:ℝ)*(L:ℝ)^2*(S.card*r) :=
      mul_le_mul_of_nonneg_left hpr (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLsq (by positivity)) hSr

lemma logarithmic_power_bound {a ε : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hε : 0 < ε) (hε1 : ε < 1/3) :
    ε^2 * a^ε * (5 + Real.logb 2 (1/a))^2 ≤ 16 := by
  let t := Real.log (1/a)
  have ht : 0 ≤ t := Real.log_nonneg (by exact (one_le_div ha).mpr ha1)
  have htlog : t = - Real.log a := by dsimp [t]; rw [Real.log_div (by norm_num) ha.ne']; simp
  have hlog2 : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog : 5+Real.logb 2 (1/a) ≤ 5+2*t := by
    dsimp [Real.logb]
    have hh : t / Real.log 2 ≤ 2*t := (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr (by nlinarith)
    linarith
  have hlogn : 0 ≤ 5+Real.logb 2 (1/a) := by
    have hh := Real.logb_nonneg (by norm_num : (1:ℝ)<2) ((one_le_div ha).mpr ha1)
    linarith
  let z := ε*t/2
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hexple : Real.exp (-z) ≤ 1 := by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  have he1 : Real.exp (-1) ≤ 1/2 := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      (inv_anti₀ (by norm_num : (0:ℝ)<2) (by linarith [Real.add_one_le_exp 1] : (2:ℝ) ≤ Real.exp 1))
  have hzbound : z * Real.exp (-z) ≤ 1/2 := (Real.mul_exp_neg_le_exp_neg_one z).trans he1
  have hmain : ε*(5+Real.logb 2 (1/a))*Real.exp (-z) ≤ 4 := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hε.le) (Real.exp_pos (-z)).le
    have h5 := mul_le_mul_of_nonneg_left hexple (show 0 ≤ 5*ε by positivity)
    dsimp [z] at hzbound
    nlinarith
  have heq : Real.exp (-z)^2 = a^ε := by
    rw [← Real.exp_nat_mul, Real.rpow_def_of_pos ha]
    congr 1
    dsimp [z]
    rw [htlog]
    ring
  have hn : 0 ≤ ε*(5+Real.logb 2 (1/a))*Real.exp (-z) := by positivity
  have hh := pow_le_pow_left₀ hn hmain 2
  rw [mul_pow, mul_pow, heq] at hh
  nlinarith

lemma spectral_packing_power {V : Type uV5} [DecidableEq V]
    (Y : V → E) (u v : Fin (Module.finrank ℝ E) → V)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (T : E →ₗ[ℝ] E) (hT : ∀i, T (b i) = Y (u i) - Y (v i))
    {a ε : ℝ} (ha : 0 < a) (htrace : 0 < |LinearMap.trace ℝ E T|)
    (hassume : a * Module.finrank ℝ E * frobSq T ≤ LinearMap.trace ℝ E T ^ 2)
    (hε : 0 < ε) (hε1 : ε < 1/3) :
    a ≤ 1 ∧ ∃ S : Finset V, ∃ r : ℝ, 0 < r ∧
      S ⊆ (univ.image u ∪ univ.image v) ∧ 2 ≤ S.card ∧
      ε^2 * a * Module.finrank ℝ E ≤ 1024 * S.card ∧
      ε^2 * a^ε * LinearMap.trace ℝ E T ^ 2 ≤
        1024 * Module.finrank ℝ E * (S.card * r) ∧
      (∀x ∈ S, ∀y ∈ S, x ≠ y → 2 * Real.sqrt r < ‖Y x - Y y‖) := by
  obtain ⟨ha1, S, r, hr, hSF, hS2, hcard, hlog, hsep⟩ :=
    spectral_packing_log Y u v b T hT ha htrace hassume
  have he2 : ε^2 ≤ 64 := by nlinarith
  have hd : 0 ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hSr : 0 ≤ (S.card : ℝ)*r := mul_nonneg (Nat.cast_nonneg _) hr.le
  have hpow : 0 ≤ ε^2 * a^ε := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ha.le _)
  have hh := mul_le_mul_of_nonneg_left hlog hpow
  have hb := mul_le_mul_of_nonneg_right (logarithmic_power_bound ha ha1 hε hε1)
    (show 0 ≤ 512*(Module.finrank ℝ E : ℝ)*(S.card*r) by positivity)
  refine ⟨ha1, S, r, hr, hSF, hS2, ?_, ?_, hsep⟩
  · have hc : a * Module.finrank ℝ E ≤ 16 * S.card := by linarith
    have hh := mul_le_mul_of_nonneg_left hc (sq_nonneg ε)
    have hb := mul_le_mul_of_nonneg_right he2 (show 0 ≤ 16*(S.card:ℝ) by positivity)
    nlinarith
  · have h9 : 9 * (ε^2 * a^ε * LinearMap.trace ℝ E T ^ 2) ≤
        8192 * Module.finrank ℝ E * (S.card * r) := by
      calc
        _ ≤ ε^2 * a^ε *
          (512 * Module.finrank ℝ E * (5 + Real.logb 2 (1/a))^2 * (S.card*r)) := by
            nlinarith only [hh]
        _ = (ε^2 * a^ε * (5 + Real.logb 2 (1/a))^2) *
            (512 * Module.finrank ℝ E * (S.card*r)) := by ring
        _ ≤ _ := by nlinarith only [hb]
    have hn : 0 ≤ (Module.finrank ℝ E : ℝ) * (S.card*r) := mul_nonneg hd hSr
    nlinarith

theorem spectral_packing_coordinates {V : Type uV6} {ι : Type uι4} {η : Type uη} [DecidableEq V]
    [Fintype ι] [Fintype η] [DecidableEq ι] [DecidableEq η]
    (Y : V → EuclideanSpace ℝ η) (u v : ι → V)
    (j : ι → η) (hj : Function.Injective j) {a ε : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (hε1 : ε < 1/3)
    (hpos : 0 < (∑i, (Y (u i) - Y (v i)).ofLp (j i))^2)
    (hbound : a * Fintype.card ι * (∑i, ‖Y (u i)-Y (v i)‖^2) ≤
      (∑i, (Y (u i)-Y (v i)).ofLp (j i))^2) :
    a ≤ 1 ∧ ∃ S : Finset V, ∃ r : ℝ, 0 < r ∧
      S ⊆ (univ.image u ∪ univ.image v) ∧ 2 ≤ S.card ∧
      ε^2 * a * Fintype.card ι ≤ 1024 * S.card ∧
      ε^2 * a^ε * (∑i, (Y (u i)-Y (v i)).ofLp (j i))^2 ≤
        1024 * Fintype.card ι * (S.card*r) ∧
      (∀x ∈ S, ∀y ∈ S, x ≠ y → 2 * Real.sqrt r < ‖Y x-Y y‖) := by
  classical
  let Y' : V → EuclideanSpace ℝ ι := fun x => WithLp.toLp 2 (fun i => (Y x).ofLp (j i))
  let b₀ := EuclideanSpace.basisFun ι ℝ
  let T := b₀.toBasis.constr ℝ (fun i => Y' (u i)-Y' (v i))
  have hT₀ (i : ι) : T (b₀ i) = Y' (u i)-Y' (v i) :=
    b₀.toBasis.constr_basis ℝ _ i
  have htr : LinearMap.trace ℝ (EuclideanSpace ℝ ι) T =
      ∑i, (Y (u i)-Y (v i)).ofLp (j i) := by
    rw [LinearMap.trace_eq_sum_inner _ b₀]
    apply sum_congr rfl
    intro i hi
    rw [hT₀, EuclideanSpace.basisFun_inner]
    rfl
  have hn (x y : V) : ‖Y' x-Y' y‖^2 ≤ ‖Y x-Y y‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq]
    change (∑i, ‖(Y x-Y y).ofLp (j i)‖^2) ≤ ∑i, ‖(Y x-Y y).ofLp i‖^2
    rw [← sum_image (f := fun i => ‖(Y x-Y y).ofLp i‖^2) hj.injOn]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; positivity)
  have hf : frobSq T ≤ ∑i, ‖Y (u i)-Y (v i)‖^2 := by
    rw [frobSq_eq_sum b₀]
    exact sum_le_sum (fun i _ => by rw [hT₀]; exact hn _ _)
  let e : Fin (Module.finrank ℝ (EuclideanSpace ℝ ι)) ≃ ι :=
    (finCongr finrank_euclideanSpace).trans (Fintype.equivFin ι).symm
  let b := b₀.reindex e.symm
  have hT : ∀i, T (b i) = Y' (u (e i))-Y' (v (e i)) := by
    intro i
    simpa only [b, OrthonormalBasis.reindex_apply, Equiv.symm_symm] using hT₀ (e i)
  have hassume : a * Module.finrank ℝ (EuclideanSpace ℝ ι) * frobSq T ≤
      LinearMap.trace ℝ (EuclideanSpace ℝ ι) T ^ 2 := by
    rw [htr, finrank_euclideanSpace]
    exact (mul_le_mul_of_nonneg_left hf (by positivity)).trans hbound
  have htrace : 0 < |LinearMap.trace ℝ (EuclideanSpace ℝ ι) T| := by
    rw [htr]
    exact abs_pos.mpr (sq_pos_iff.mp hpos)
  obtain ⟨ha1, S, r, hr, hSF, hS2, hcard, hmass, hsep⟩ :=
    spectral_packing_power Y' (u ∘ e) (v ∘ e) b T hT ha htrace hassume hε hε1
  rw [htr, finrank_euclideanSpace] at hmass
  rw [finrank_euclideanSpace] at hcard
  refine ⟨ha1, S, r, hr, ?_, hS2, hcard, hmass, ?_⟩
  · intro x hx
    rcases mem_union.mp (hSF hx) with hh | hh
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hh
      exact mem_union_left _ (mem_image.mpr ⟨e i, mem_univ _, rfl⟩)
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hh
      exact mem_union_right _ (mem_image.mpr ⟨e i, mem_univ _, rfl⟩)
  · intro x hx y hy hxy
    exact (hsep x hx y hy hxy).trans_le ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hn x y))

end
end StrongThinTree.Spectral

end

end OAI
