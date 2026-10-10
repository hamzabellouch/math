import OAI.Analysis.RecursivePotentials.EquivalentNorms

namespace OAI

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

noncomputable def descEnergy (v : ι → ℝ) (s : ι) : ℝ :=
  v s ^ 2 + ∑ c : {c // c ∈ T.children s}, descEnergy v c.1
termination_by T.maxDepth - T.depth s
decreasing_by exact T.child_measure c.2

lemma descEnergy_eq (v : ι → ℝ) (s : ι) :
    T.descEnergy v s = v s ^ 2 + ∑ c ∈ T.children s, T.descEnergy v c := by
  rw [descEnergy, ← Finset.sum_subtype (T.children s) (fun _ => Iff.rfl) (T.descEnergy v)]

lemma descEnergy_nonneg (v : ι → ℝ) (s : ι) : 0 ≤ T.descEnergy v s := by
  rw [T.descEnergy_eq]
  exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun c hc => descEnergy_nonneg v c)
termination_by T.maxDepth - T.depth s
decreasing_by exact T.child_measure hc

lemma descEnergy_root (v : ι → ℝ) : T.descEnergy v T.root = ∑ s, v s ^ 2 := by
  have he : (∑ s, T.descEnergy v s) = ∑ s, (v s ^ 2 + ∑ c ∈ T.children s, T.descEnergy v c) :=
    Finset.sum_congr rfl (fun s _ => T.descEnergy_eq v s)
  rw [Finset.sum_add_distrib, T.sum_children, Finset.sum_erase_eq_sub (Finset.mem_univ T.root)] at he
  linarith

lemma max_fields_le (v : ι → ℝ) (s : ι) :
    max (T.fields v s).1 (T.fields v s).2 ≤
      |v s| + Real.sqrt (∑ c ∈ T.children s, (max (T.fields v c).1 (T.fields v c).2) ^ 2) := by
  have hp : Real.sqrt (∑ c ∈ T.children s, (T.fields v c).1 ^ 2) ≤
      Real.sqrt (∑ c ∈ T.children s, (max (T.fields v c).1 (T.fields v c).2) ^ 2) := by
    apply Real.sqrt_le_sqrt
    exact Finset.sum_le_sum fun c hc => pow_le_pow_left₀ (T.fields_nonneg v c).1 (le_max_left _ _) _
  have hq : Real.sqrt (∑ c ∈ T.children s, (T.fields v c).2 ^ 2) ≤
      Real.sqrt (∑ c ∈ T.children s, (max (T.fields v c).1 (T.fields v c).2) ^ 2) := by
    apply Real.sqrt_le_sqrt
    exact Finset.sum_le_sum fun c hc => pow_le_pow_left₀ (T.fields_nonneg v c).2 (le_max_right _ _) _
  rw [T.fields_eq v s]
  simp only [leastPair, max_le_iff]
  constructor <;> constructor
  · linarith [abs_nonneg (v s)]
  · linarith [le_abs_self (v s)]
  · linarith [abs_nonneg (v s)]
  · linarith [neg_le_abs (v s)]

lemma max_fields_square_le (v : ι → ℝ) (h : ℕ) (hh : ∀ s, T.depth s ≤ h) (s : ι) :
    (max (T.fields v s).1 (T.fields v s).2) ^ 2 ≤
      ((h : ℝ) + 1 - T.depth s) * T.descEnergy v s := by
  let k : ℝ := (h : ℝ) - T.depth s
  let B : ℝ := ∑ c ∈ T.children s, T.descEnergy v c
  let r : ℝ := Real.sqrt (∑ c ∈ T.children s, (max (T.fields v c).1 (T.fields v c).2) ^ 2)
  have hk : 0 ≤ k := sub_nonneg.mpr (by exact_mod_cast hh s)
  have hB : 0 ≤ B := Finset.sum_nonneg fun c hc => T.descEnergy_nonneg v c
  have hr : r ^ 2 ≤ k * B := by
    rw [show r ^ 2 = ∑ c ∈ T.children s, (max (T.fields v c).1 (T.fields v c).2) ^ 2 from
      Real.sq_sqrt (Finset.sum_nonneg fun c hc => sq_nonneg _)]
    calc
      _ ≤ ∑ c ∈ T.children s, k * T.descEnergy v c := by
        apply Finset.sum_le_sum
        intro c hc
        apply (max_fields_square_le v h hh c).trans
        apply mul_le_mul_of_nonneg_right _ (T.descEnergy_nonneg v c)
        dsimp [k]
        have hdc : (T.depth s : ℝ) + 1 ≤ T.depth c := by exact_mod_cast T.child_depth hc
        linarith
      _ = k * B := by rw [← Finset.mul_sum]
  have hm0 : 0 ≤ max (T.fields v s).1 (T.fields v s).2 :=
    (T.fields_nonneg v s).1.trans (le_max_left _ _)
  have hsq := pow_le_pow_left₀ hm0 (T.max_fields_le v s) 2
  have hw := weighted_square_bound (a := |v s|) hk hB hr
  rw [sq_abs] at hw
  rw [T.descEnergy_eq]
  calc
    _ ≤ (|v s| + r) ^ 2 := hsq
    _ ≤ (k + 1) * (v s ^ 2 + B) := hw
    _ = ((h : ℝ) + 1 - T.depth s) * (v s ^ 2 + ∑ c ∈ T.children s, T.descEnergy v c) := by
      dsimp [k, B]; ring
termination_by T.maxDepth - T.depth s
decreasing_by exact T.child_measure hc

lemma weighted_sum_children (w e : ι → ℝ) :
    ∑ s, w s * ∑ c ∈ T.children s, e c =
      ∑ c ∈ Finset.univ.erase T.root, w (T.parent c) * e c := by
  simp only [Finset.mul_sum, children, Finset.sum_filter, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  calc
    (∑ c, ∑ s, if c ≠ T.root ∧ T.parent c = s then w s * e c else 0) =
        ∑ c, if c = T.root then 0 else w (T.parent c) * e c := by
      apply Finset.sum_congr rfl
      intro c hc
      by_cases h : c = T.root
      · simp [h]
      · simp [h]
    _ = ∑ c ∈ Finset.univ.erase T.root, w (T.parent c) * e c := by
      have hset : Finset.univ.erase T.root =
          Finset.univ.filter (fun c => c ≠ T.root) := by
        ext c; simp
      rw [hset, Finset.sum_filter]
      simp only [ite_not]

lemma upper_sum_square_le {p : ι → ℝ} (hp : T.Upper p) (h : ℕ)
    (hh : ∀ s, T.depth s ≤ h) : ∑ s, p s ^ 2 ≤ ((h : ℝ) + 1) * p T.root ^ 2 := by
  let w : ι → ℝ := fun s => (h : ℝ) - T.depth s
  have hw : ∀ s, 0 ≤ w s := fun s => sub_nonneg.mpr (by exact_mod_cast hh s)
  have he : ∑ s, w s * ∑ c ∈ T.children s, p c ^ 2 ≤ ∑ s, w s * p s ^ 2 :=
    Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hp s) (hw s)
  rw [T.weighted_sum_children] at he
  have hc : ∑ c ∈ Finset.univ.erase T.root, (w c + 1) * p c ^ 2 ≤
      ∑ c ∈ Finset.univ.erase T.root, w (T.parent c) * p c ^ 2 := by
    apply Finset.sum_le_sum
    intro c hc
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    dsimp [w]
    have hd : (T.depth (T.parent c) : ℝ) + 1 ≤ T.depth c := by
      exact_mod_cast T.parent_depth c (Finset.mem_erase.mp hc).1
    linarith
  have hs : ∑ c ∈ Finset.univ.erase T.root, (w c + 1) * p c ^ 2 =
      (∑ s, w s * p s ^ 2) - h * p T.root ^ 2 + ((∑ s, p s ^ 2) - p T.root ^ 2) := by
    simp only [add_mul, one_mul, Finset.sum_add_distrib,
      Finset.sum_erase_eq_sub (Finset.mem_univ T.root)]
    simp only [w, T.depth_root, Nat.cast_zero, sub_zero]
    ring
  rw [hs] at hc
  nlinarith

lemma block_square_comparison (v : ι → ℝ) (h : ℕ) (hh : ∀ s, T.depth s ≤ h) :
    ((max (T.fields v T.root).1 (T.fields v T.root).2) ^ 2 ≤
      ((h : ℝ) + 1) * ∑ s, v s ^ 2) ∧
    ((∑ s, v s ^ 2) ≤ 4 * ((h : ℝ) + 1) *
      (max (T.fields v T.root).1 (T.fields v T.root).2) ^ 2) := by
  constructor
  · simpa only [T.depth_root, Nat.cast_zero, sub_zero, T.descEnergy_root] using
      T.max_fields_square_le v h hh T.root
  · have hp := T.upper_sum_square_le (T.fields_upper v).1 h hh
    have hq := T.upper_sum_square_le (T.fields_upper v).2 h hh
    have hv : ∑ s, v s ^ 2 ≤ 2 * (∑ s, (T.fields v s).1 ^ 2) +
        2 * (∑ s, (T.fields v s).2 ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro s hs
      rw [← T.fields_difference v s]
      nlinarith [sq_nonneg ((T.fields v s).1 + (T.fields v s).2)]
    have hpM := pow_le_pow_left₀ (T.fields_nonneg v T.root).1
      (le_max_left (T.fields v T.root).1 (T.fields v T.root).2) 2
    have hqM := pow_le_pow_left₀ (T.fields_nonneg v T.root).2
      (le_max_right (T.fields v T.root).1 (T.fields v T.root).2) 2
    have hh0 : 0 ≤ (h : ℝ) + 1 := by positivity
    have hp' := mul_le_mul_of_nonneg_left hpM hh0
    have hq' := mul_le_mul_of_nonneg_left hqM hh0
    nlinarith

end FiniteRootedTree

open Filter Topology

open scoped ENNReal

noncomputable section

lemma isReflexive_iff {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    IsReflexive E ↔ ∀ F : (E →L[ℝ] ℝ) →L[ℝ] ℝ, ∃ x : E, ∀ f : E →L[ℝ] ℝ, F f = f x := by
  constructor
  · intro h F
    obtain ⟨x, hx⟩ := h F
    exact ⟨x, fun f => (congrArg (fun G : (E →L[ℝ] ℝ) →L[ℝ] ℝ => G f) hx).symm⟩
  · intro h F
    obtain ⟨x, hx⟩ := h F
    exact ⟨x, ContinuousLinearMap.ext (fun f => (hx f).symm)⟩

lemma IsReflexive.of_equiv {E : Type uSpace} {F : Type uOther} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (hE : IsReflexive E) (e : E ≃L[ℝ] F) :
    IsReflexive F := by
  rw [isReflexive_iff] at hE ⊢
  intro G
  let D : (E →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ F E ℝ).flip e.symm.toContinuousLinearMap
  obtain ⟨x, hx⟩ := hE (G.comp D)
  refine ⟨e x, ?_⟩
  intro f
  have he : D (f.comp e.toContinuousLinearMap) = f := by
    ext y
    change f (e (e.symm y)) = f y
    rw [e.apply_symm_apply]
  have hh := hx (f.comp e.toContinuousLinearMap)
  change G (D (f.comp e.toContinuousLinearMap)) = f (e x) at hh
  rwa [he] at hh

lemma hilbert_isReflexive {E : Type uSpace} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] : IsReflexive E := by
  rw [isReflexive_iff]
  intro F
  let d := InnerProductSpace.toDual ℝ E
  let g : E →L[ℝ] ℝ := F.comp d.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨d.symm g, ?_⟩
  intro f
  have he : d (d.symm f) = f := d.apply_symm_apply f
  have hg : d (d.symm g) = g := d.apply_symm_apply g
  have h := congrArg (fun k : E →L[ℝ] ℝ => k (d.symm f)) hg
  change inner ℝ (d.symm g) (d.symm f) = F (d (d.symm f)) at h
  rw [he] at h
  have h' := congrArg (fun k : E →L[ℝ] ℝ => k (d.symm g)) he
  change inner ℝ (d.symm f) (d.symm g) = f (d.symm g) at h'
  rw [real_inner_comm] at h'
  exact h.symm.trans h'

namespace SquareSum

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (E : ι → Type uFiber)
    [∀ i, NormedAddCommGroup (E i)] [fiberNormedSpace : ∀ i, NormedSpace ℝ (E i)]

lemma pairing_apply {ι : Type uIndex} [DecidableEq ι] (E : ι → Type uFiber)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] (f : Space (DualFamily E))
    (x : Space E) :
    pairing E f x = ∑' i, f i (x i) := rfl

@[simp] lemma pairing_single_right (f : Space (DualFamily E)) (i : ι) (x : E i) :
    pairing E f (lp.single 2 i x) = f i x := by
  classical
  rw [pairing_apply, tsum_eq_single i]
  · rw [lp.single_apply_self]
  · intro j hj
    rw [lp.single_apply_ne _ _ _ hj, map_zero]

@[simp] lemma pairing_single_left (i : ι) (f : E i →L[ℝ] ℝ) (x : Space E) :
    pairing E (lp.single 2 i f) x = f (x i) := by
  classical
  rw [pairing_apply, tsum_eq_single i]
  · rw [lp.single_apply_self]
  · intro j hj
    rw [lp.single_apply_ne _ _ _ hj]
    rfl

def restrictAt (f : Space E →L[ℝ] ℝ) (i : ι) : E i →L[ℝ] ℝ :=
  f.comp (lp.singleContinuousLinearMap ℝ E 2 i)

@[simp] lemma restrictAt_apply (f : Space E →L[ℝ] ℝ) (i : ι) (x : E i) :
    restrictAt E f i x = f (lp.single 2 i x) := rfl

lemma exists_half_norming {X : Type uTarget} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X →L[ℝ] ℝ) : ∃ x : X, ‖x‖ ≤ 1 ∧ ‖f‖ / 2 ≤ f x := by
  by_cases hf : f = 0
  · subst f; exact ⟨0, by simp, by simp⟩
  have hfpos : 0 < ‖f‖ := norm_pos_iff.mpr hf
  obtain ⟨x, hx, hfx⟩ := f.exists_lt_apply_of_lt_opNorm (half_lt_self hfpos)
  by_cases hsgn : 0 ≤ f x
  · refine ⟨x, hx.le, ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg hsgn] at hfx
    exact hfx.le
  · refine ⟨-x, by simpa only [norm_neg] using hx.le, ?_⟩
    rw [map_neg]
    rw [Real.norm_eq_abs, abs_of_neg (lt_of_not_ge hsgn)] at hfx
    exact hfx.le

lemma restriction_square_bound (f : Space E →L[ℝ] ℝ) (S : Finset ι) :
    ∑ i ∈ S, ‖restrictAt E f i‖ ^ 2 ≤ (2 * ‖f‖) ^ 2 := by
  classical
  choose x hx hfx using fun i => exists_half_norming (restrictAt E f i)
  let q : ℝ := ∑ i ∈ S, ‖restrictAt E f i‖ ^ 2
  let v : Space E := ∑ i ∈ S, lp.single 2 i (‖restrictAt E f i‖ • x i)
  have hq : 0 ≤ q := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hv2 : ‖v‖ ^ 2 ≤ q := by
    have h := lp.norm_sum_single (E := E) (p := 2) (by norm_num) (fun i => ‖restrictAt E f i‖ • x i) S
    norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at h
    change ‖v‖ ^ 2 = _ at h
    rw [h]
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_smul, norm_norm, mul_pow]
    have hi0 := norm_nonneg (x i)
    have hi1 := hx i
    have hisq : ‖x i‖ ^ 2 ≤ 1 := by nlinarith
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hisq (sq_nonneg ‖restrictAt E f i‖)
  have hfv : q / 2 ≤ f v := by
    dsimp [v]
    rw [map_sum]
    calc
      q / 2 = ∑ i ∈ S, ‖restrictAt E f i‖ * (‖restrictAt E f i‖ / 2) := by
        dsimp [q]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        change _ ≤ restrictAt E f i (‖restrictAt E f i‖ • x i)
        rw [map_smul, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (hfx i) (norm_nonneg _)
  have hf' : f v ≤ ‖f‖ * ‖v‖ := (le_abs_self _).trans (f.le_opNorm v)
  have hv : ‖v‖ ≤ Real.sqrt q := (Real.le_sqrt (norm_nonneg _) hq).mpr hv2
  have hhalf := hf'.trans (mul_le_mul_of_nonneg_left hv (norm_nonneg f))
  have hr : Real.sqrt q ≤ 2 * ‖f‖ := by
    by_contra hh
    have hlt : 2 * ‖f‖ < Real.sqrt q := lt_of_not_ge hh
    have hp : 0 < Real.sqrt q := (by positivity : (0 : ℝ) ≤ 2 * ‖f‖).trans_lt hlt
    have H := mul_lt_mul_of_pos_right hlt hp
    nlinarith [Real.sq_sqrt hq]
  change q ≤ (2 * ‖f‖) ^ 2
  nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg q, norm_nonneg f]

lemma restriction_mem (f : Space E →L[ℝ] ℝ) : Memℓp (restrictAt E f) 2 := by
  apply memℓp_gen' (C := (2 * ‖f‖) ^ 2)
  intro S
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using restriction_square_bound E f S

def restrict (f : Space E →L[ℝ] ℝ) : Space (DualFamily E) := ⟨restrictAt E f, restriction_mem E f⟩

@[simp] lemma restrict_apply (f : Space E →L[ℝ] ℝ) (i : ι) :
    restrict E f i = restrictAt E f i := rfl

lemma restrict_norm (f : Space E →L[ℝ] ℝ) : ‖restrict E f‖ ≤ 2 * ‖f‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num) (by positivity)
  intro S
  simpa only [restrict, ENNReal.toReal_ofNat, Real.rpow_two] using restriction_square_bound E f S

lemma pairing_restrict (f : Space E →L[ℝ] ℝ) : pairing E (restrict E f) = f := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro i
  ext x
  exact pairing_single_right E (restrict E f) i x

theorem isReflexive (hE : ∀ i, IsReflexive (E i)) : IsReflexive (Space E) := by
  rw [isReflexive_iff]
  intro F
  let G : Space (DualFamily E) →L[ℝ] ℝ := F.comp (pairing E)
  let r := restrict (DualFamily E) G
  choose x hx using fun i => hE i (r i)
  have hnorm : ∀ i, ‖x i‖ = ‖r i‖ := by
    intro i
    rw [← (NormedSpace.inclusionInDoubleDualLi (E := E i) ℝ).norm_map]
    exact congrArg norm (hx i)
  have hmem : Memℓp x 2 := by
    apply memℓp_norm_iff.mp
    simpa only [hnorm] using (lp.memℓp r).norm
  let v : Space E := ⟨x, hmem⟩
  have hG : G = (pairing E).flip v := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro i
    ext f
    change (r i) f = pairing E (lp.single 2 i f) v
    rw [pairing_single_left]
    exact (congrArg (fun H : (E i →L[ℝ] ℝ) →L[ℝ] ℝ => H f) (hx i)).symm
  refine ⟨v, ?_⟩
  intro f
  have hh := congrArg (fun H : Space (DualFamily E) →L[ℝ] ℝ => H (restrict E f)) hG
  change F (pairing E (restrict E f)) = pairing E (restrict E f) v at hh
  simpa only [pairing_restrict] using hh

end SquareSum

end

open UniformSpace

noncomputable section

lemma IsReflexive.prod {E : Type uSpace} {F : Type uOther} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (hE : IsReflexive E) (hF : IsReflexive F) :
    IsReflexive (E × F) := by
  rw [isReflexive_iff] at hE hF ⊢
  intro G
  let D₁ : (E →L[ℝ] ℝ) →L[ℝ] ((E × F) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (E × F) E ℝ).flip (ContinuousLinearMap.fst ℝ E F)
  let D₂ : (F →L[ℝ] ℝ) →L[ℝ] ((E × F) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (E × F) F ℝ).flip (ContinuousLinearMap.snd ℝ E F)
  obtain ⟨x, hx⟩ := hE (G.comp D₁)
  obtain ⟨y, hy⟩ := hF (G.comp D₂)
  refine ⟨(x, y), ?_⟩
  intro f
  let f₁ := f.comp (ContinuousLinearMap.inl ℝ E F)
  let f₂ := f.comp (ContinuousLinearMap.inr ℝ E F)
  have hf : f = D₁ f₁ + D₂ f₂ := by
    apply ContinuousLinearMap.ext
    intro z
    change f z = f (z.1, 0) + f (0, z.2)
    rw [← map_add]
    simp
  rw [hf, map_add]
  change G (D₁ f₁) + G (D₂ f₂) = f₁ x + f₂ y
  exact congrArg₂ (· + ·) (hx f₁) (hy f₂)

namespace SquareSum

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (E : ι → Type uFiber)
    [∀ i, NormedAddCommGroup (E i)] [fiberNormedSpace : ∀ i, NormedSpace ℝ (E i)]

lemma closedSubmodule_eq_top (S : Submodule ℝ (Space E)) (hS : IsClosed (S : Set (Space E)))
    (hsingle : ∀ i (x : E i), lp.single 2 i x ∈ S) : S = ⊤ := by
  apply top_unique
  intro x hx
  exact hS.mem_of_tendsto (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x)
    (Filter.Eventually.of_forall fun J => S.sum_mem fun i hi => hsingle i (x i))

lemma denseRange_of_single {X : Type uTarget} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X →L[ℝ] Space E) (hsingle : ∀ i (x : E i), lp.single 2 i x ∈ f.range) :
    DenseRange f := by
  have htop := closedSubmodule_eq_top E f.range.topologicalClosure
    f.range.isClosed_topologicalClosure (fun i x => f.range.le_topologicalClosure (hsingle i x))
  intro x
  have hm : x ∈ f.range.topologicalClosure := by rw [htop]; trivial
  exact hm

end SquareSum

end

namespace TreeVector

open scoped ENNReal

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma toSquareLinear_norm_sq (v : TreeVector T) :
    ‖toSquareLinear T v‖ ^ 2 = ∑ s ∈ (show ι →₀ ℝ from v).support, v s ^ 2 := by
  change ‖∑ s ∈ (show ι →₀ ℝ from v).support, lp.single 2 s (v s)‖ ^ 2 = _
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
    lp.norm_sum_single (E := fun _ : ι => ℝ) (p := 2) (by norm_num) (fun s => v s)
      (show ι →₀ ℝ from v).support

@[simp] lemma toSquareLinear_single (s : ι) (a : ℝ) :
    toSquareLinear T (Finsupp.single s a) = lp.single 2 s a := by
  change ((Finsupp.lsum ℝ) (fun s : ι => lp.lsingle (𝕜 := ℝ) (E := fun _ : ι => ℝ) 2 s))
    (Finsupp.single s a) = _
  simp

lemma toSquareLinear_apply (v : TreeVector T) (s : ι) : toSquareLinear T v s = v s := by
  change (∑ i ∈ (show ι →₀ ℝ from v).support, lp.single 2 i (v i)) s = v s
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]
  split_ifs with hs
  · rfl
  · exact (Finsupp.notMem_support_iff.mp hs).symm

lemma block_square_comparison (v : TreeVector T) (h : ℕ) (hh : ∀ s, T.depth s ≤ h) :
    (max (T.P v T.root) (T.Q v T.root)) ^ 2 ≤
      ((h : ℝ) + 1) * ‖toSquareLinear T v‖ ^ 2 ∧
    ‖toSquareLinear T v‖ ^ 2 ≤ 4 * ((h : ℝ) + 1) *
      (max (T.P v T.root) (T.Q v T.root)) ^ 2 := by
  let w : ι →₀ ℝ := v
  let H := T.head w
  let U := T.restrict H (T.head_initial w)
  have hfields : T.P w T.root = (U.fields (fun c => w c.1) U.root).1 ∧
      T.Q w T.root = (U.fields (fun c => w c.1) U.root).2 :=
    T.potentials_on_head w H (T.head_initial w) (T.support_subset_head w)
      ⟨T.root, (T.head_initial w).1⟩
  have hn : ‖toSquareLinear T v‖ ^ 2 = ∑ s ∈ w.support, w s ^ 2 :=
    toSquareLinear_norm_sq T v
  have hsum : (∑ s : H, w s.1 ^ 2) = ‖toSquareLinear T v‖ ^ 2 := by
    rw [hn, ← Finset.sum_subtype H (fun _ => Iff.rfl) (fun s => w s ^ 2)]
    exact (Finset.sum_subset (T.support_subset_head w) (fun s hs hs' => by
      rw [Finsupp.notMem_support_iff.mp hs']; norm_num)).symm
  have hc := U.block_square_comparison (fun s => w s.1) h (fun s => hh s.1)
  rw [← hfields.1, ← hfields.2, hsum] at hc
  exact hc

lemma hilbert_comparisons (v : TreeVector T) (h : ℕ) (hh : ∀ s, T.depth s ≤ h) :
    ‖v‖ ≤ (2 * Real.sqrt ((h : ℝ) + 1)) * ‖toSquareLinear T v‖ ∧
    ‖toSquareLinear T v‖ ≤ (2 * Real.sqrt ((h : ℝ) + 1)) * ‖v‖ := by
  have hc := block_square_comparison T v h hh
  have hp := T.P_nonneg v T.root
  have hq := T.Q_nonneg v T.root
  have hM : 0 ≤ max (T.P v T.root) (T.Q v T.root) := hp.trans (le_max_left _ _)
  have hh0 : 0 ≤ (h : ℝ) + 1 := by positivity
  have hr := Real.sq_sqrt hh0
  have hn : ‖v‖ = T.P v T.root + T.Q v T.root := rfl
  have hnM : ‖v‖ ≤ 2 * max (T.P v T.root) (T.Q v T.root) := by
    rw [hn]; linarith [le_max_left (T.P v T.root) (T.Q v T.root), le_max_right (T.P v T.root) (T.Q v T.root)]
  have hMn : max (T.P v T.root) (T.Q v T.root) ≤ ‖v‖ := by rw [hn]; exact max_le (by linarith) (by linarith)
  have hM2n := pow_le_pow_left₀ hM hMn 2
  have hMbound : max (T.P v T.root) (T.Q v T.root) ≤
      Real.sqrt ((h : ℝ) + 1) * ‖toSquareLinear T v‖ := by
    have hsq : (Real.sqrt ((h : ℝ) + 1) * ‖toSquareLinear T v‖) ^ 2 =
        ((h : ℝ) + 1) * ‖toSquareLinear T v‖ ^ 2 := by rw [mul_pow, hr]
    nlinarith [mul_nonneg (Real.sqrt_nonneg ((h : ℝ) + 1)) (norm_nonneg (toSquareLinear T v))]
  constructor
  · nlinarith
  · have he := mul_le_mul_of_nonneg_left hM2n (by positivity : 0 ≤ 4 * ((h : ℝ) + 1))
    have hsq : ((2 * Real.sqrt ((h : ℝ) + 1)) * ‖v‖) ^ 2 =
        4 * ((h : ℝ) + 1) * ‖v‖ ^ 2 := by rw [mul_pow, mul_pow, hr]; ring
    nlinarith [norm_nonneg (toSquareLinear T v),
      mul_nonneg (by positivity : 0 ≤ 2 * Real.sqrt ((h : ℝ) + 1)) (norm_nonneg v)]

def toSquare (h : ℕ) (hh : ∀ s, T.depth s ≤ h) :
    TreeVector T →L[ℝ] SquareSum.Space (fun _ : ι => ℝ) :=
  (toSquareLinear T).mkContinuous (2 * Real.sqrt ((h : ℝ) + 1))
    (fun v => (hilbert_comparisons T v h hh).2)

lemma toSquare_dense (h : ℕ) (hh : ∀ s, T.depth s ≤ h) : DenseRange (toSquare T h hh) := by
  apply SquareSum.denseRange_of_single
  intro s a
  refine ⟨Finsupp.single s a, ?_⟩
  exact toSquareLinear_single T s a

end

end TreeVector

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

def hilbertEquiv (h : ℕ) (hh : ∀ s, T.depth s ≤ h) :
    TreeSpace T ≃L[ℝ] SquareSum.Space (fun _ : ι => ℝ) :=
  completionEquivOfDense (TreeVector.toSquare T h hh)
    ⟨2 * Real.sqrt ((h : ℝ) + 1), by positivity⟩
    (fun v => (TreeVector.hilbert_comparisons T v h hh).1) (TreeVector.toSquare_dense T h hh)

theorem finite_height_isReflexive (h : ℕ) (hh : ∀ s, T.depth s ≤ h) : IsReflexive (TreeSpace T) :=
  hilbert_isReflexive.of_equiv (hilbertEquiv T h hh).symm

end

end TreeSpace

namespace Joined

noncomputable section

open UniformSpace

abbrev Component (h : ℕ+) := TreeSpace (componentTree h)

abbrev Outer : Type := SquareSum.Space Component

def embed (h : ℕ+) : ComponentNode h ↪ JoinedNode where
  toFun s := some ⟨h, s⟩
  inj' := by intro s t he; simpa using he

@[simp] lemma embed_apply (h : ℕ+) (s : ComponentNode h) : embed h s = some ⟨h, s⟩ := rfl

@[simp] lemma embed_ne_root (h : ℕ+) (s : ComponentNode h) : embed h s ≠ joinedTree.root := by
  simp [joinedTree]

lemma embed_parent (h : ℕ+) (s : ComponentNode h) (hs : s ≠ (componentTree h).root) :
    joinedTree.parent (embed h s) = embed h ((componentTree h).parent s) := by
  have hn : s.1 ≠ [] := fun he => hs (Subtype.ext he)
  change (if s.1 = [] then none else _) = _
  rw [ite_eq_right hn]
  rfl

@[simp] lemma embed_root_parent (h : ℕ+) :
    joinedTree.parent (embed h (componentTree h).root) = joinedTree.root := rfl

def rootEmbed : ℕ+ ↪ JoinedNode where
  toFun h := embed h (componentTree h).root
  inj' := by
    intro h k he
    have hh := Option.some.inj he
    exact congrArg Sigma.fst hh

lemma root_child (c : JoinedNode) (hc : c ≠ joinedTree.root)
    (hp : joinedTree.parent c = joinedTree.root) : ∃ h, c = rootEmbed h := by
  cases c with
  | none => exact (hc rfl).elim
  | some c =>
    obtain ⟨h, s⟩ := c
    by_cases hs : s.1 = []
    · refine ⟨h, ?_⟩
      change (some ⟨h, s⟩ : JoinedNode) = some ⟨h, (componentTree h).root⟩
      congr 2
      exact Subtype.ext hs
    · change (if s.1 = [] then none else _) = none at hp
      rw [ite_eq_right hs] at hp
      contradiction

lemma component_child (h : ℕ+) (s : ComponentNode h) (c : JoinedNode)
    (hc : c ≠ joinedTree.root) (hp : joinedTree.parent c = embed h s) :
    ∃ d : ComponentNode h, c = embed h d ∧ d ≠ (componentTree h).root ∧
      (componentTree h).parent d = s := by
  cases c with
  | none => exact (hc rfl).elim
  | some c =>
    obtain ⟨k, d⟩ := c
    by_cases hd : d.1 = []
    · change (if d.1 = [] then none else _) = (some ⟨h, s⟩ : JoinedNode) at hp
      rw [ite_eq_left hd] at hp
      contradiction
    · change (if d.1 = [] then none else _) = (some ⟨h, s⟩ : JoinedNode) at hp
      rw [ite_eq_right hd] at hp
      have hk : k = h := congrArg Sigma.fst (Option.some.inj hp)
      subst k
      refine ⟨d, rfl, fun he => hd (congrArg Subtype.val he), ?_⟩
      exact (embed h).injective (by exact hp)

lemma upper_pull (h : ℕ+) {p : JoinedNode → ℝ} (hp : joinedTree.GlobalUpper p) :
    (componentTree h).GlobalUpper (fun s => p (embed h s)) := by
  intro s S hS
  have hh := hp (embed h s) (S.map (embed h)) (by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp hc
    refine ⟨embed_ne_root h d, ?_⟩
    rw [embed_parent h d (hS d hd).1, (hS d hd).2])
  simpa only [Finset.sum_map] using hh

def partLinear (h : ℕ+) : TreeVector joinedTree →ₗ[ℝ] TreeVector (componentTree h) where
  toFun v := Finsupp.comapDomain (embed h) v (embed h).injective.injOn
  map_add' v w := by apply Finsupp.ext; intro s; rfl
  map_smul' a v := by apply Finsupp.ext; intro s; rfl

@[simp] lemma partLinear_apply (h : ℕ+) (v : TreeVector joinedTree) (s : ComponentNode h) :
    partLinear h v s = v (embed h s) := rfl

lemma part_potentials_le (v : TreeVector joinedTree) (h : ℕ+) (s : ComponentNode h) :
    (componentTree h).P (partLinear h v) s ≤ joinedTree.P v (embed h s) ∧
    (componentTree h).Q (partLinear h v) s ≤ joinedTree.Q v (embed h s) := by
  apply (componentTree h).potentials_minimal (partLinear h v)
    (fun s => joinedTree.P v (embed h s)) (fun s => joinedTree.Q v (embed h s))
  · intro s; exact joinedTree.P_nonneg v _
  · intro s; exact joinedTree.Q_nonneg v _
  · intro s; exact joinedTree.P_sub_Q v _
  · exact upper_pull h (joinedTree.P_upper v)
  · exact upper_pull h (joinedTree.Q_upper v)

lemma part_square_bound (v : TreeVector joinedTree) (S : Finset ℕ+) :
    ∑ h ∈ S, ‖partLinear h v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  let w : JoinedNode →₀ ℝ := v
  have hp : ∑ h ∈ S, (componentTree h).P (partLinear h v) (componentTree h).root ^ 2 ≤
      joinedTree.P w joinedTree.root ^ 2 := by
    calc
      _ ≤ ∑ h ∈ S, joinedTree.P w (rootEmbed h) ^ 2 := by
        apply Finset.sum_le_sum
        intro h hh
        exact pow_le_pow_left₀ ((componentTree h).P_nonneg _ _)
          (part_potentials_le v h (componentTree h).root).1 2
      _ ≤ _ := by
        have hh := joinedTree.P_upper w joinedTree.root (S.map rootEmbed) (by
          intro c hc
          obtain ⟨h, hh, rfl⟩ := Finset.mem_map.mp hc
          exact ⟨embed_ne_root h _, embed_root_parent h⟩)
        simpa only [Finset.sum_map] using hh
  have hq : ∑ h ∈ S, (componentTree h).Q (partLinear h v) (componentTree h).root ^ 2 ≤
      joinedTree.Q w joinedTree.root ^ 2 := by
    calc
      _ ≤ ∑ h ∈ S, joinedTree.Q w (rootEmbed h) ^ 2 := by
        apply Finset.sum_le_sum
        intro h hh
        exact pow_le_pow_left₀ ((componentTree h).Q_nonneg _ _)
          (part_potentials_le v h (componentTree h).root).2 2
      _ ≤ _ := by
        have hh := joinedTree.Q_upper w joinedTree.root (S.map rootEmbed) (by
          intro c hc
          obtain ⟨h, hh, rfl⟩ := Finset.mem_map.mp hc
          exact ⟨embed_ne_root h _, embed_root_parent h⟩)
        simpa only [Finset.sum_map] using hh
  exact sum_add_sq_le S (fun h => (componentTree h).P (partLinear h v) (componentTree h).root)
    (fun h => (componentTree h).Q (partLinear h v) (componentTree h).root)
    (joinedTree.P_nonneg w _) (joinedTree.Q_nonneg w _) hp hq

lemma parts_mem (v : TreeVector joinedTree) :
    Memℓp (fun h => (partLinear h v : Component h)) 2 := by
  apply memℓp_gen' (C := ‖v‖ ^ 2)
  intro S
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Completion.norm_coe] using part_square_bound v S

def components (v : TreeVector joinedTree) :
    Outer := ⟨fun h => (partLinear h v : Component h), parts_mem v⟩

@[simp] lemma components_apply (v : TreeVector joinedTree) (h : ℕ+) :
    components v h = (partLinear h v : Component h) := rfl

lemma components_norm_le (v : TreeVector joinedTree) : ‖components v‖ ≤ ‖v‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg v)
  intro S
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, components_apply, Completion.norm_coe] using part_square_bound v S

def componentsLinear : TreeVector joinedTree →ₗ[ℝ] Outer where
  toFun := components
  map_add' v w := by
    apply lp.ext
    funext h
    simp only [lp.coeFn_add, Pi.add_apply, components_apply, map_add, Completion.coe_add]
  map_smul' a v := by
    apply lp.ext
    funext h
    simp only [lp.coeFn_smul, Pi.smul_apply, components_apply, map_smul, Completion.coe_smul, RingHom.id_apply]

def componentsMap : TreeVector joinedTree →L[ℝ] Outer :=
  componentsLinear.mkContinuous 1 (fun v => by
    change ‖components v‖ ≤ 1 * ‖v‖
    simpa only [one_mul] using components_norm_le v)

def field (r : ℝ) (f : ∀ h : ℕ+, ComponentNode h → ℝ) : JoinedNode → ℝ
  | none => r
  | some ⟨h, s⟩ => f h s

@[simp] lemma field_root (r : ℝ) (f : ∀ h : ℕ+, ComponentNode h → ℝ) :
    field r f joinedTree.root = r := rfl

@[simp] lemma field_embed (r : ℝ) (f : ∀ h : ℕ+, ComponentNode h → ℝ) (h : ℕ+) (s : ComponentNode h) :
    field r f (embed h s) = f h s := rfl

lemma field_nonneg (r : ℝ) (f : ∀ h : ℕ+, ComponentNode h → ℝ) (hr : 0 ≤ r)
    (hf : ∀ h s, 0 ≤ f h s) (c : JoinedNode) : 0 ≤ field r f c := by
  cases c with
  | none => exact hr
  | some c => exact hf c.1 c.2

lemma field_upper (r : ℝ) (f : ∀ h : ℕ+, ComponentNode h → ℝ)
    (hf : ∀ h, (componentTree h).GlobalUpper (f h))
    (hr : ∀ S : Finset ℕ+, ∑ h ∈ S, f h (componentTree h).root ^ 2 ≤ r ^ 2) :
    joinedTree.GlobalUpper (field r f) := by
  intro s S hS
  cases s with
  | none =>
    have he := Finset.sum_preimage rootEmbed S rootEmbed.injective.injOn
      (fun c => field r f c ^ 2) (by
        intro c hc hn
        obtain ⟨h, hh⟩ := root_child c (hS c hc).1 (hS c hc).2
        exact (hn ⟨h, hh.symm⟩).elim)
    rw [← he]
    exact hr _
  | some s =>
    obtain ⟨h, s⟩ := s
    have he := Finset.sum_preimage (embed h) S (embed h).injective.injOn
      (fun c => field r f c ^ 2) (by
        intro c hc hn
        obtain ⟨d, hd, hne, hpar⟩ := component_child h s c (hS c hc).1 (hS c hc).2
        exact (hn ⟨d, hd.symm⟩).elim)
    rw [← he]
    apply hf h s
    intro d hd
    have hd' := Finset.mem_preimage.mp hd
    obtain ⟨e, he, hne, hpar⟩ := component_child h s (embed h d) (hS _ hd').1 (hS _ hd').2
    have hde : d = e := (embed h).injective he
    exact hde ▸ ⟨hne, hpar⟩

lemma part_squares_le_outer (v : TreeVector joinedTree) (S : Finset ℕ+) :
    ∑ h ∈ S, ‖partLinear h v‖ ^ 2 ≤ ‖components v‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, components_apply, Completion.norm_coe] using
    lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) (components v) S

lemma part_field_squares_le_outer (v : TreeVector joinedTree) (S : Finset ℕ+) :
    (∑ h ∈ S, (componentTree h).P (partLinear h v) (componentTree h).root ^ 2 ≤ ‖components v‖ ^ 2) ∧
    (∑ h ∈ S, (componentTree h).Q (partLinear h v) (componentTree h).root ^ 2 ≤ ‖components v‖ ^ 2) := by
  constructor
  · apply le_trans (Finset.sum_le_sum (fun h hh => ?_)) (part_squares_le_outer v S)
    apply pow_le_pow_left₀ ((componentTree h).P_nonneg _ _) _ 2
    exact ((componentTree h).potentials_le_normSum (partLinear h v) (componentTree h).root).1
  · apply le_trans (Finset.sum_le_sum (fun h hh => ?_)) (part_squares_le_outer v S)
    apply pow_le_pow_left₀ ((componentTree h).Q_nonneg _ _) _ 2
    exact ((componentTree h).potentials_le_normSum (partLinear h v) (componentTree h).root).2

def liftP (v : TreeVector joinedTree) : JoinedNode → ℝ :=
  field (‖components v‖ + max (v joinedTree.root) 0)
    (fun h => (componentTree h).P (partLinear h v))

def liftQ (v : TreeVector joinedTree) : JoinedNode → ℝ :=
  field (‖components v‖ + max (-v joinedTree.root) 0)
    (fun h => (componentTree h).Q (partLinear h v))

lemma liftP_nonneg (v : TreeVector joinedTree) (s : JoinedNode) : 0 ≤ liftP v s :=
  field_nonneg _ _ (by positivity) (fun h s => (componentTree h).P_nonneg _ _) s

lemma liftQ_nonneg (v : TreeVector joinedTree) (s : JoinedNode) : 0 ≤ liftQ v s :=
  field_nonneg _ _ (by positivity) (fun h s => (componentTree h).Q_nonneg _ _) s

lemma lift_difference (v : TreeVector joinedTree) (s : JoinedNode) :
    liftP v s - liftQ v s = v s := by
  cases s with
  | none =>
    change (‖components v‖ + max (v joinedTree.root) 0) -
      (‖components v‖ + max (-v joinedTree.root) 0) = v joinedTree.root
    rcases le_total 0 (v joinedTree.root) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  | some s => exact (componentTree s.1).P_sub_Q (partLinear s.1 v) s.2

lemma lifts_upper (v : TreeVector joinedTree) :
    joinedTree.GlobalUpper (liftP v) ∧ joinedTree.GlobalUpper (liftQ v) := by
  constructor
  · apply field_upper
    · intro h; exact (componentTree h).P_upper _
    · intro S
      apply (part_field_squares_le_outer v S).1.trans
      exact pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_right (le_max_right _ _)) 2
  · apply field_upper
    · intro h; exact (componentTree h).Q_upper _
    · intro S
      apply (part_field_squares_le_outer v S).2.trans
      exact pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_right (le_max_right _ _)) 2

lemma potentials_le_lifts (v : TreeVector joinedTree) (s : JoinedNode) :
    joinedTree.P v s ≤ liftP v s ∧ joinedTree.Q v s ≤ liftQ v s :=
  joinedTree.potentials_minimal v (liftP v) (liftQ v) (liftP_nonneg v) (liftQ_nonneg v)
    (lift_difference v) (lifts_upper v).1 (lifts_upper v).2 s

lemma component_potentials (v : TreeVector joinedTree) (h : ℕ+) (s : ComponentNode h) :
    joinedTree.P v (embed h s) = (componentTree h).P (partLinear h v) s ∧
    joinedTree.Q v (embed h s) = (componentTree h).Q (partLinear h v) s := by
  have ha := potentials_le_lifts v (embed h s)
  have hb := part_potentials_le v h s
  exact ⟨le_antisymm ha.1 hb.1, le_antisymm ha.2 hb.2⟩

lemma norm_le_root_add_outer (v : TreeVector joinedTree) :
    ‖v‖ ≤ |v joinedTree.root| + 2 * ‖components v‖ := by
  have h := potentials_le_lifts v joinedTree.root
  have h1 : joinedTree.P v joinedTree.root ≤ ‖components v‖ + max (v joinedTree.root) 0 := h.1
  have h2 : joinedTree.Q v joinedTree.root ≤ ‖components v‖ + max (-v joinedTree.root) 0 := h.2
  change joinedTree.P v joinedTree.root + joinedTree.Q v joinedTree.root ≤ _
  rcases le_total 0 (v joinedTree.root) with hn | hn
  · rw [abs_of_nonneg hn, max_eq_left hn] at *
    rw [max_eq_right (by linarith : -v joinedTree.root ≤ 0)] at h2
    linarith
  · rw [abs_of_nonpos hn, max_eq_right hn] at *
    rw [max_eq_left (by linarith : 0 ≤ -v joinedTree.root)] at h2
    linarith

def put (h : ℕ+) (v : TreeVector (componentTree h)) :
    TreeVector joinedTree := Finsupp.embDomain (embed h) v

lemma put_root (h : ℕ+) (v : TreeVector (componentTree h)) : put h v joinedTree.root = 0 := by
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨s, hs⟩
  exact embed_ne_root h s hs

lemma part_put_same (h : ℕ+) (v : TreeVector (componentTree h)) : partLinear h (put h v) = v := by
  apply Finsupp.ext
  intro s
  exact Finsupp.embDomain_apply_self (embed h) v s

lemma part_put_other (h k : ℕ+) (hk : k ≠ h) (v : TreeVector (componentTree h)) :
    partLinear k (put h v) = 0 := by
  apply Finsupp.ext
  intro s
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨t, ht⟩
  have hk' := congrArg Sigma.fst (Option.some.inj ht)
  exact hk hk'.symm

lemma components_put (h : ℕ+) (v : TreeVector (componentTree h)) :
    components (put h v) = lp.single 2 h (v : Component h) := by
  apply lp.ext
  funext k
  by_cases hk : k = h
  · subst k
    rw [components_apply, part_put_same, lp.single_apply_self]
  · rw [components_apply, part_put_other h k hk, Completion.coe_zero, lp.single_apply_ne _ _ _ hk]

def rootVector (a : ℝ) : TreeVector joinedTree := Finsupp.single joinedTree.root a

lemma components_rootVector (a : ℝ) :
    components (rootVector a) = 0 := by
  have hp : ∀ h, partLinear h (rootVector a) = 0 := by
    intro h
    apply Finsupp.ext
    intro s
    change Finsupp.single joinedTree.root a (embed h s) = 0
    exact Finsupp.single_eq_of_ne (embed_ne_root h s)
  apply lp.ext
  funext h
  rw [components_apply, hp h, Completion.coe_zero]
  rfl

def splitting : TreeVector joinedTree →L[ℝ] ℝ × Outer :=
  (TreeVector.coordinate joinedTree joinedTree.root).prod componentsMap

lemma splitting_apply (v : TreeVector joinedTree) :
    splitting v = (v joinedTree.root, components v) := rfl

lemma norm_le_splitting (v : TreeVector joinedTree) : ‖v‖ ≤ 3 * ‖splitting v‖ := by
  rw [splitting_apply, Prod.norm_def, Real.norm_eq_abs]
  have hn := norm_le_root_add_outer v
  have ha := le_max_left |v joinedTree.root| ‖components v‖
  have hb := le_max_right |v joinedTree.root| ‖components v‖
  linarith

lemma splitting_put (h : ℕ+) (v : TreeVector (componentTree h)) :
    splitting (put h v) = (0, lp.single 2 h (v : Component h)) := by
  rw [splitting_apply, put_root, components_put]

lemma splitting_rootVector (a : ℝ) :
    splitting (rootVector a) = (a, 0) := by
  rw [splitting_apply, components_rootVector]
  exact Prod.ext (Finsupp.single_eq_same) rfl

lemma splitting_dense : DenseRange splitting := by
  let S := splitting.range.topologicalClosure
  have hS : IsClosed (S : Set (ℝ × Outer)) := splitting.range.isClosed_topologicalClosure
  have hroot : ∀ a : ℝ, (a, (0 : Outer)) ∈ S := by
    intro a
    exact splitting.range.le_topologicalClosure ⟨rootVector a, splitting_rootVector a⟩
  have hsingle : ∀ h (x : Component h), (0, lp.single 2 h x) ∈ S := by
    intro h x
    induction x using Completion.induction_on with
    | hp =>
      exact hS.preimage ((ContinuousLinearMap.inr ℝ ℝ Outer).comp
        (lp.singleContinuousLinearMap ℝ Component 2 h)).continuous
    | ih v => exact splitting.range.le_topologicalClosure ⟨put h v, splitting_put h v⟩
  have houter : S.comap (ContinuousLinearMap.inr ℝ ℝ Outer).toLinearMap = ⊤ := by
    apply SquareSum.closedSubmodule_eq_top Component
    · exact hS.preimage (ContinuousLinearMap.inr ℝ ℝ Outer).continuous
    · exact hsingle
  intro z
  have hz : (0, z.2) ∈ S := by
    have h : z.2 ∈ S.comap (ContinuousLinearMap.inr ℝ ℝ Outer).toLinearMap := by rw [houter]; trivial
    exact h
  have hm := S.add_mem (hroot z.1) hz
  have hm' : z ∈ S := by simpa using hm
  exact hm'

def freeEquiv : XJoined ≃L[ℝ] ℝ × Outer :=
  completionEquivOfDense splitting 3 norm_le_splitting splitting_dense

lemma components_reflexive (h : ℕ+) : IsReflexive (Component h) :=
  TreeSpace.finite_height_isReflexive (componentTree h) h.val (fun s => s.2)

theorem outer_isReflexive : IsReflexive Outer := SquareSum.isReflexive Component components_reflexive

end

end Joined

theorem XJoined_isReflexive : IsReflexive XJoined :=
  (hilbert_isReflexive (E := ℝ)).prod Joined.outer_isReflexive |>.of_equiv Joined.freeEquiv.symm

namespace Joined

noncomputable section

open UniformSpace

def zeroComponents : ZeroTreeVector joinedTree →L[ℝ] Outer :=
  componentsMap.comp (ZeroTreeVector.inclusion joinedTree)

lemma zero_norm_le_components (v : ZeroTreeVector joinedTree) : ‖v‖ ≤ ‖zeroComponents v‖ := by
  have h := norm_le_root_add_outer (ZeroTreeVector.toTree joinedTree v)
  rw [ZeroTreeVector.root_zero, abs_zero, zero_add] at h
  rw [ZeroTreeVector.norm_half]
  change _ ≤ ‖components (ZeroTreeVector.toTree joinedTree v)‖
  linarith

def zeroPut (h : ℕ+) (v : TreeVector (componentTree h)) : ZeroTreeVector joinedTree :=
  ⟨put h v, put_root h v⟩

lemma zeroComponents_zeroPut (h : ℕ+) (v : TreeVector (componentTree h)) :
    zeroComponents (zeroPut h v) = lp.single 2 h (v : Component h) := components_put h v

lemma zeroComponents_dense : DenseRange zeroComponents := by
  let S := zeroComponents.range.topologicalClosure
  have hS : IsClosed (S : Set Outer) := zeroComponents.range.isClosed_topologicalClosure
  have hsingle : ∀ h (x : Component h), lp.single 2 h x ∈ S := by
    intro h x
    induction x using Completion.induction_on with
    | hp => exact hS.preimage (lp.singleContinuousLinearMap ℝ Component 2 h).continuous
    | ih v => exact zeroComponents.range.le_topologicalClosure ⟨zeroPut h v, zeroComponents_zeroPut h v⟩
  have htop := SquareSum.closedSubmodule_eq_top Component S hS hsingle
  intro x
  have hx : x ∈ S := by rw [htop]; trivial
  exact hx

def zeroEquiv : XZero ≃L[ℝ] Outer :=
  completionEquivOfDense zeroComponents 1
    (fun v => by simpa only [NNReal.coe_one, one_mul] using zero_norm_le_components v)
    zeroComponents_dense

end

end Joined

theorem XZero_isReflexive : IsReflexive XZero := Joined.outer_isReflexive.of_equiv Joined.zeroEquiv.symm

noncomputable section

lemma logarithmicGamma_pos {M β : ℝ} (hβ : 0 < β) (hM : β ≤ M) :
    0 < logarithmicGamma M β := by
  have hm : 0 < M := hβ.trans_le hM
  unfold logarithmicGamma
  positivity

lemma logarithmicGamma_le {M β : ℝ} (hβ : 0 < β) (hM : β ≤ M) :
    logarithmicGamma M β ≤ β ^ 3 / (16 * M ^ 2) := by
  have hm : 0 < M := hβ.trans_le hM
  let h := β ^ 2 / (2 * M ^ 2)
  have hh : 0 < h := by dsimp [h]; positivity
  have hh1 : h ≤ 1 := by
    dsimp [h]
    apply (div_le_iff₀ (by positivity)).mpr
    have hb := pow_le_pow_left₀ hβ.le hM 2
    nlinarith [sq_nonneg M]
  have hs : Real.sqrt h ≤ 1 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by simpa using hh1⟩
  let c := β * Real.sqrt h / 8
  have hc : 0 < c := by dsimp [c]; positivity
  have hcM : c ≤ M := by
    have hcβ : c ≤ β := by dsimp [c]; nlinarith [Real.sqrt_nonneg h]
    exact hcβ.trans hM
  have hlog : 0 ≤ Real.log (M / c) := Real.log_nonneg ((le_div_iff₀ hc).mpr (by simpa using hcM))
  have hK : 0 ≤ 4 * (2 + Real.sqrt 6) * (1 + Real.log (M / c)) / h := by positivity
  have he : Real.exp (-(4 * (2 + Real.sqrt 6) * (1 + Real.log (M / c)) / h)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hK)
  calc
    logarithmicGamma M β ≤ β * h / 8 := by
      change β * h / 8 * Real.exp (-(4 * (2 + Real.sqrt 6) * (1 + Real.log (M / c)) / h)) ≤ _
      exact mul_le_of_le_one_right (by positivity) he
    _ = β ^ 3 / (16 * M ^ 2) := by dsimp [h]; ring

end

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

theorem logarithmic_propagation {M β : ℝ} (hβ : 0 < β) (hM : β ≤ M)
    (p q r : ι → ℝ) (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s) (hr : ∀ s, 0 ≤ r s)
    (hpU : T.Upper p) (hqU : T.Upper q)
    (hp'U : T.Upper (fun s => p s + r s))
    (hq'U : T.Upper (fun s => q s + r s))
    (htight : ∀ s, (T.children s).Nonempty →
      (∑ c ∈ T.children s, p c ^ 2 = p s ^ 2) ∨
      (∑ c ∈ T.children s, q c ^ 2 = q s ^ 2))
    (hroot : p T.root + q T.root + 2 * r T.root ≤ M)
    (hleaves : β ^ 2 ≤ ∑ b ∈ T.leaves, r b ^ 2) :
    logarithmicGamma M β ≤ r T.root ∧ 0 < logarithmicGamma M β := by
  have hm : 0 < M := hβ.trans_le hM
  have he := hleaves.trans (T.two_field_energy_all_leaves p q r hp hq hr hpU hqU hp'U hq'U htight)
  have hc : β ^ 3 ≤ r T.root * (2 * p T.root + r T.root) * (2 * q T.root + r T.root) := by
    simpa using cube_le_of_sq_le_energy hβ.le (by norm_num : (0 : ℝ) ≤ 1)
      (hp T.root) (hq T.root) (hr T.root) (by simpa using he)
  have hprod : (2 * p T.root + r T.root) * (2 * q T.root + r T.root) ≤ M ^ 2 := by
    have hs : (p T.root + q T.root + r T.root) ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (by linarith [hp T.root, hq T.root, hr T.root]) (by linarith [hr T.root]) 2
    nlinarith [sq_nonneg (p T.root - q T.root)]
  have hc' : β ^ 3 ≤ r T.root * M ^ 2 :=
    hc.trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hprod (hr T.root))
  refine ⟨(logarithmicGamma_le hβ hM).trans ?_, logarithmicGamma_pos hβ hM⟩
  apply (div_le_iff₀ (by positivity : 0 < 16 * M ^ 2)).mpr
  nlinarith [mul_nonneg (hr T.root) (sq_nonneg M)]

end FiniteRootedTree

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

theorem logarithmic_tail_gap (x : TreeVector T) {H : Finset ι} (hH : T.Initial H)
    (hx : (show ι →₀ ℝ from x).support ⊆ H) (y : TreeSpace T)
    (hy : y ∈ tail T H hH) {ζ : ℝ} (hζ : 0 < ζ) (hζ2 : ζ ≤ 2)
    (hY : ζ ≤ ‖y‖) (hplus : ‖(x : TreeSpace T) + y‖ ≤ 2)
    (hminus : ‖(x : TreeSpace T) - y‖ ≤ 2) :
    ‖(x : TreeSpace T)‖ + 2 * logarithmicGamma 2 (ζ / 4) ≤
      (‖(x : TreeSpace T) + y‖ + ‖(x : TreeSpace T) - y‖) / 2 := by
  have he := cubic_tail T x hH hx y hy
  have hd := meanExcess_nonneg T (x : TreeSpace T) y
  have ha : ‖(x : TreeSpace T)‖ + meanExcess T (x : TreeSpace T) y ≤ 2 := by
    unfold meanExcess; linarith
  have hb : 2 * ‖(x : TreeSpace T)‖ + meanExcess T (x : TreeSpace T) y ≤ 4 := by linarith
  have hb' := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * ‖(x : TreeSpace T)‖ + meanExcess T (x : TreeSpace T) y) hb 2
  have hh := mul_le_mul_of_nonneg_left hb' (by positivity : 0 ≤ 8 * meanExcess T (x : TreeSpace T) y)
  have hz3 := pow_le_pow_left₀ hζ.le hY 3
  have hg := logarithmicGamma_le (by positivity : 0 < ζ / 4) (by linarith : ζ / 4 ≤ 2)
  norm_num at hg hh
  have hout : 2 * logarithmicGamma 2 (ζ / 4) ≤ meanExcess T (x : TreeSpace T) y := by
    nlinarith [pow_nonneg hζ.le 3]
  unfold meanExcess at hout
  linarith

end

end TreeSpace

open Filter

open scoped Topology

lemma finite_dimensional_image_close_pair {A : Type uDomain} {E : Type uSpace}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (P : A →L[ℝ] E) (z : ℕ → A) {C ε : ℝ} (hb : ∀ n, ‖z n‖ ≤ C) (hε : 0 < ε) :
    ∃ i j : ℕ, i ≠ j ∧ ‖P (z i) - P (z j)‖ < ε := by
  obtain ⟨a, ha, φ, hφ, hz⟩ := tendsto_subseq_of_bounded
    (Metric.isBounded_closedBall : Bornology.IsBounded (Metric.closedBall (0 : A) C))
    (fun n => by simpa only [Metric.mem_closedBall, dist_zero_right] using hb n)
  have ht : Tendsto (fun n => P (z (φ n))) atTop (𝓝 (P a)) := P.continuous.continuousAt.tendsto.comp hz
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht (ε / 2) (by positivity)
  refine ⟨φ N, φ (N+1), ne_of_lt (hφ (Nat.lt_succ_self N)), ?_⟩
  have h1 := hN N le_rfl
  have h2 := hN (N+1) (Nat.le_succ N)
  rw [← dist_eq_norm]
  calc
    dist (P (z (φ N))) (P (z (φ (N+1)))) ≤ dist (P (z (φ N))) (P a) + dist (P (z (φ (N+1)))) (P a) := dist_triangle_right _ _ _
    _ < ε := by linarith

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

theorem averaged_modulus_all_radii_lower [Infinite ι] {t : ℝ} (ht : 0 < t) :
    min t (1/2) ^ 3 / 128 ≤ averagedModulus (TreeSpace T) t := by
  apply averagedModulus_lower_of_witness (not_finite_dimensional T) ht.le
  intro x hx ε hε
  obtain ⟨v, hv, hvx⟩ := finite_unit_dense T x hx hε
  let H := T.head (show ι →₀ ℝ from v)
  have hH : T.Initial H := T.head_initial v
  refine ⟨cofiniteTail T H hH, ?_⟩
  intro y hy hy1
  have hty : t ≤ ‖t • y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    nlinarith
  have hzy : t • y ∈ tail T H hH := (tail T H hH).smul_mem t hy
  have hfinite := finite_center_midpoint_gap T v hH (T.support_subset_head v) hv
    (t • y) hzy (lt_min ht (by norm_num))
      ((min_le_right t (1/2)).trans_lt (by norm_num)) ((min_le_left _ _).trans hty)
  have h₁ : ‖(v : TreeSpace T) + t • y‖ ≤ ‖x + t • y‖ + ‖(v : TreeSpace T) - x‖ := by
    calc
      ‖(v : TreeSpace T) + t • y‖ = ‖x + t • y + ((v : TreeSpace T) - x)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have h₂ : ‖(v : TreeSpace T) - t • y‖ ≤ ‖x - t • y‖ + ‖(v : TreeSpace T) - x‖ := by
    calc
      ‖(v : TreeSpace T) - t • y‖ = ‖x - t • y + ((v : TreeSpace T) - x)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  unfold averagedGain
  linarith

theorem averaged_modulus_pos [Infinite ι] {t : ℝ} (ht : 0 < t) :
    0 < averagedModulus (TreeSpace T) t :=
  lt_of_lt_of_le (by positivity : 0 < min t (1/2) ^ 3 / 128)
    (averaged_modulus_all_radii_lower T ht)

end

end TreeSpace

section Lens

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_center_le {x y : E} {R : ℝ} (hp : ‖x+y‖ ≤ R) (hm : ‖x-y‖ ≤ R) : ‖x‖ ≤ R := by
  have h := norm_add_le (x+y) (x-y)
  have he : x+y+(x-y) = (2 : ℝ) • x := by module
  rw [he, norm_smul] at h
  norm_num at h
  linarith

lemma norm_perturbation_le {x y : E} {R : ℝ} (hp : ‖x+y‖ ≤ R) (hm : ‖x-y‖ ≤ R) : ‖y‖ ≤ R := by
  apply norm_center_le (x := y) (y := x)
  · simpa [add_comm] using hp
  · simpa [norm_sub_rev] using hm

lemma lens_half_difference {x z w : E} {R : ℝ}
    (hzp : ‖x+z‖ ≤ R) (hzm : ‖x-z‖ ≤ R)
    (hwp : ‖x+w‖ ≤ R) (hwm : ‖x-w‖ ≤ R) :
    ‖x + (1/2 : ℝ) • (z-w)‖ ≤ R ∧ ‖x - (1/2 : ℝ) • (z-w)‖ ≤ R := by
  have he₁ : x + (1/2 : ℝ) • (z-w) = (1/2 : ℝ) • ((x+z)+(x-w)) := by module
  have he₂ : x - (1/2 : ℝ) • (z-w) = (1/2 : ℝ) • ((x-z)+(x+w)) := by module
  constructor
  · rw [he₁, norm_smul]; norm_num
    have hh := norm_add_le (x+z) (x-w); linarith
  · rw [he₂, norm_smul]; norm_num
    have hh := norm_add_le (x-z) (x+w); linarith

end Lens

namespace TreeSpace

noncomputable section

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

theorem separated_midpoint_families {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 2)
    (x : TreeSpace T) (z : ℕ → TreeSpace T)
    (hplus : ∀ n, ‖x+z n‖ ≤ 1) (hminus : ∀ n, ‖x-z n‖ ≤ 1)
    (hsep : ∀ i j, i ≠ j → ε ≤ ‖z i - z j‖) :
    ‖x‖ ≤ 1 - min (1/2) (logarithmicGamma 2 (ε/16)) := by
  let g := logarithmicGamma 2 (ε/16)
  have hg : 0 < g := logarithmicGamma_pos (by positivity) (by linarith)
  let δ := min (1/4 : ℝ) (min (ε/8) (g/4))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1/4 := min_le_left _ _
  have hδε : δ ≤ ε/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hδg : δ ≤ g/4 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨v, hv⟩ := Completion.denseRange_coe.exists_dist_lt x hδ
  have hvx : ‖(v : TreeSpace T) - x‖ < δ := by simpa [dist_eq_norm, norm_sub_rev] using hv
  let H := T.head (show ι →₀ ℝ from v)
  have hH : T.Initial H := T.head_initial v
  let f := headCoordinates T H
  let P : (H → ℝ) →L[ℝ] TreeSpace T :=
    (Completion.toComplL : TreeVector T →L[ℝ] TreeSpace T).comp (TreeVector.ofHead T H)
  have hP : ∀ w, P (f w) = projection T H hH w := fun w => (projection_reconstructs T H hH w).symm
  have hzb : ∀ j, ‖z j‖ ≤ 1 := fun j => norm_perturbation_le (hplus j) (hminus j)
  have hfb : ∀ j, ‖f (z j)‖ ≤ ‖f‖ := fun j =>
    (f.le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_left (hzb j) (norm_nonneg f))
  obtain ⟨i, j, hij, hijP⟩ := finite_dimensional_image_close_pair P (fun j => f (z j)) hfb
    (by positivity : 0 < 2 * δ)
  rw [hP, hP] at hijP
  let u := (1/2 : ℝ) • (z i - z j)
  have hu : ε / 2 ≤ ‖u‖ := by
    dsimp [u]; rw [norm_smul]; norm_num
    linarith [hsep i j hij]
  have he := lens_half_difference (hplus i) (hminus i) (hplus j) (hminus j)
  have hup : ‖x+u‖ ≤ 1 := he.1
  have hum : ‖x-u‖ ≤ 1 := he.2
  have hPu : ‖projection T H hH u‖ < δ := by
    dsimp [u]; rw [map_smul, map_sub, norm_smul]; norm_num
    linarith
  let y := u - projection T H hH u
  have hyt : y ∈ tail T H hH := by
    change projection T H hH y = 0
    dsimp [y]; rw [map_sub, projection_idem, sub_self]
  have hY : ε/4 ≤ ‖y‖ := by
    have htri : ‖u‖ ≤ ‖y‖ + ‖projection T H hH u‖ := by
      simpa [y] using norm_add_le y (projection T H hH u)
    linarith
  have hdist : ‖((v : TreeSpace T) - x) - projection T H hH u‖ < 2 * δ :=
    (norm_sub_le _ _).trans_lt (by linarith)
  have hdist' : ‖((v : TreeSpace T) - x) + projection T H hH u‖ < 2 * δ :=
    (norm_add_le _ _).trans_lt (by linarith)
  have hvp : ‖(v : TreeSpace T) + y‖ ≤ 1 + 2 * δ := by
    have heq : (v : TreeSpace T) + y = (x+u) + (((v : TreeSpace T)-x)-projection T H hH u) := by dsimp [y]; abel
    rw [heq]
    exact (norm_add_le _ _).trans (by linarith)
  have hvm : ‖(v : TreeSpace T) - y‖ ≤ 1 + 2 * δ := by
    have heq : (v : TreeSpace T) - y = (x-u) + (((v : TreeSpace T)-x)+projection T H hH u) := by dsimp [y]; abel
    rw [heq]
    exact (norm_add_le _ _).trans (by linarith)
  have hgap := logarithmic_tail_gap T v hH (T.support_subset_head v) y hyt
    (by positivity : 0 < ε/4) (by linarith : ε/4 ≤ 2) hY
    (hvp.trans (by linarith)) (hvm.trans (by linarith))
  have hg' : logarithmicGamma 2 (ε/4/4) = g := by dsimp [g]; congr 1 ; ring
  rw [hg'] at hgap
  have hxv := norm_sub_norm_le x (v : TreeSpace T)
  rw [norm_sub_rev] at hxv
  have hm : min (1/2 : ℝ) g ≤ g := min_le_right _ _
  change ‖x‖ ≤ 1 - min (1/2 : ℝ) g
  linarith

end

end TreeSpace

theorem XJoined_separated_families {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧
      (ε ≤ 2 → η = min (1/2) (logarithmicGamma 2 (ε/16))) ∧
      ∀ (x : XJoined) (z : ℕ → XJoined),
        (∀ n, ‖x+z n‖ ≤ 1) → (∀ n, ‖x-z n‖ ≤ 1) →
        (∀ i j, i ≠ j → ε ≤ ‖z i-z j‖) → ‖x‖ ≤ 1-η := by
  by_cases hε2 : ε ≤ 2
  · refine ⟨min (1/2) (logarithmicGamma 2 (ε/16)), ?_, ?_, fun _ => rfl, ?_⟩
    · exact lt_min (by norm_num) (logarithmicGamma_pos (by positivity) (by linarith))
    · exact (min_le_left _ _).trans_lt (by norm_num)
    · exact fun x z hp hm hs => TreeSpace.separated_midpoint_families joinedTree hε hε2 x z hp hm hs
  · refine ⟨1/2, by norm_num, by norm_num, fun h => (hε2 h).elim, ?_⟩
    intro x z hp hm hs
    have h0 := norm_perturbation_le (hp 0) (hm 0)
    have h1 := norm_perturbation_le (hp 1) (hm 1)
    have hsep := hs 0 1 (by norm_num)
    have htri := norm_sub_le (z 0) (z 1)
    exfalso; linarith

end RecursivePotentials

end OAI
