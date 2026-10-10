import Mathlib

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]



def WeightedBound (U : Set E) (s : ℝ) (m : ℕ) (C : ℝ) (f : E → F) : Prop :=
  ∀ j ≤ m, ∀ x ∈ U, s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖ ≤ C

lemma WeightedBound.mono_order {U : Set E} {s C : ℝ} {m r : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) (hr : r ≤ m) : WeightedBound U s r C f :=
  fun j hj => h j (hj.trans hr)

lemma WeightedBound.mono_const {U : Set E} {s C D : ℝ} {m : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) (hCD : C ≤ D) : WeightedBound U s m D f :=
  fun j hj x hx => (h j hj x hx).trans hCD

lemma WeightedBound.norm_le {U : Set E} {s C : ℝ} {m : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) {x : E} (hx : x ∈ U) : ‖f x‖ ≤ C := by
  simpa only [pow_zero, one_mul, norm_iteratedFDerivWithin_zero] using h 0 (Nat.zero_le m) x hx

lemma WeightedBound.deriv_le {U : Set E} {s C : ℝ} {m : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) (hs : 0 < s) {j : ℕ} (hj : j ≤ m) {x : E} (hx : x ∈ U) :
    ‖iteratedFDerivWithin ℝ j f U x‖ ≤ C / s ^ j := by
  apply (le_div_iff₀ (pow_pos hs j)).2
  simpa only [mul_comm] using h j hj x hx

lemma WeightedBound.shrink_scale {U : Set E} {s t C : ℝ} {m : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) (ht : 0 ≤ t) (hts : t ≤ s) : WeightedBound U t m C f := by
  intro j hj x hx
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht hts j) (norm_nonneg _)).trans (h j hj x hx)

lemma WeightedBound.add {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ} {f g : E → F}
    (hs : 0 ≤ s) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (C + D) (fun x => f x + g x) := by
  intro j hj x hx
  rw [fun_iteratedFDerivWithin_add_apply ((hf.of_le (m := (j : ℕ∞ω)) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffWithinAt hx)
    ((hg.of_le (m := (j : ℕ∞ω)) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffWithinAt hx) hU hx]
  calc
    _ ≤ s ^ j * (‖iteratedFDerivWithin ℝ j f U x‖ + ‖iteratedFDerivWithin ℝ j g U x‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ C + D := by rw [mul_add]; exact add_le_add (hbf j hj x hx) (hbg j hj x hx)

lemma WeightedBound.linear {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hs : 0 ≤ s) (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (L : F →L[ℝ] G) :
    WeightedBound U s m (‖L‖ * C) (L ∘ f) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (‖L‖ * ‖iteratedFDerivWithin ℝ j f U x‖) := by
      gcongr
      exact L.norm_iteratedFDerivWithin_comp_left (n := j) (N := ∞) (hf.contDiffWithinAt hx) hU hx (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ = ‖L‖ * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ ‖L‖ * C := mul_le_mul_of_nonneg_left (hb j hj x hx) (norm_nonneg _)

lemma WeightedBound.fderivWithin {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hs : 0 < s) (hb : WeightedBound U s (m + 1) C f) :
    WeightedBound U s m (C / s) (fderivWithin ℝ f U) := by
  intro j hj x hx
  rw [norm_iteratedFDerivWithin_fderivWithin hU hx]
  apply (le_div_iff₀ hs).2
  have hh := hb (j + 1) (Nat.add_le_add_right hj 1) x hx
  rw [pow_succ] at hh
  nlinarith

lemma sum_choose_real (j : ℕ) : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = 2 ^ j := by
  simpa only [one_pow, one_mul, show (1 : ℝ) + 1 = 2 by norm_num] using (add_pow (1 : ℝ) 1 j).symm


lemma weighted_binomial_bound {s C D : ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (j : ℕ) (a b : ℕ → ℝ) (_ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (haB : ∀ i ≤ j, s ^ i * a i ≤ C) (hbB : ∀ i ≤ j, s ^ i * b i ≤ D) :
    s ^ j * (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * a i * b (j - i)) ≤
      2 ^ j * C * D := by
  calc
    _ = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (s ^ i * a i) *
        (s ^ (j - i) * b (j - i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have he : s ^ j = s ^ i * s ^ (j - i) := by rw [← pow_add, Nat.add_sub_of_le hij]
      rw [he]
      ring
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * C * D := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hh := mul_le_mul (haB i hij) (hbB (j - i) (Nat.sub_le j i))
        (mul_nonneg (pow_nonneg hs _) (hb _)) hC
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (j.choose i))
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul, sum_choose_real]



lemma WeightedBound.bilinear {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ}
    {f : E → F} {g : E → G} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g)
    (B : F →L[ℝ] G →L[ℝ] H) :
    WeightedBound U s m (‖B‖ * (2 ^ m * C * D)) (fun x => B (f x) (g x)) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (‖B‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f U x‖ * ‖iteratedFDerivWithin ℝ (j - i) g U x‖) := by
      gcongr
      exact B.norm_iteratedFDerivWithin_le_of_bilinear (n := j) (N := ∞) hf hg hU hx (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ = ‖B‖ * (s ^ j * (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f U x‖ * ‖iteratedFDerivWithin ℝ (j - i) g U x‖)) := by ring
    _ ≤ ‖B‖ * (2 ^ j * C * D) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
      exact weighted_binomial_bound hs hC hD j _ _ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
        (fun i hi => hbf i (hi.trans hj) x hx) (fun i hi => hbg i (hi.trans hj) x hx)
    _ ≤ _ := by gcongr; norm_num


lemma WeightedBound.const_smul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ}
    {m : ℕ} {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℝ) :
    WeightedBound U s m (|a| * C) (fun x => a • f x) := by
  intro j hj x hx
  change s ^ j * ‖iteratedFDerivWithin ℝ j (a • f) U x‖ ≤ _
  rw [iteratedFDerivWithin_const_smul_apply
    ((hf.of_le (m := (j : ℕ∞ω)) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffWithinAt hx)
    hU hx, norm_smul, Real.norm_eq_abs]
  calc
    _ = |a| * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (abs_nonneg _)

lemma WeightedBound.neg {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun x => -f x) := by
  simpa using hb.const_smul hU hf (-1)

lemma WeightedBound.sub {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ} {f g : E → F}
    (hs : 0 ≤ s) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (C + D) (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hbf.add hU hs hf hg.neg (hbg.neg hU hg)

lemma WeightedBound.clm_apply {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ}
    {f : E → F →L[ℝ] G} {g : E → F} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (2 ^ m * C * D) (fun x => f x (g x)) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f U x‖ * ‖iteratedFDerivWithin ℝ (j - i) g U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_clm_apply (n := j) (N := ∞) hf hg hU hx
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ ≤ 2 ^ j * C * D := weighted_binomial_bound hs hC hD j _ _
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun i hi => hbf i (hi.trans hj) x hx) (fun i hi => hbg i (hi.trans hj) x hx)
    _ ≤ _ := by gcongr; norm_num

lemma WeightedBound.clm_apply_const {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ}
    {f : E → F →L[ℝ] G} (hs : 0 ≤ s) (hf : ContDiffOn ℝ ∞ f U)
    (hb : WeightedBound U s m C f) (v : F) :
    WeightedBound U s m (‖v‖ * C) (fun x => f x v) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (‖v‖ * ‖iteratedFDerivWithin ℝ j f U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_clm_apply_const (n := j) (N := ∞)
        (hf.contDiffWithinAt hx) hU hx (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ = ‖v‖ * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (norm_nonneg v)



def firstOrder (U : Set E) (A : E → F →L[ℝ] G) (B : E → (E →L[ℝ] F) →L[ℝ] G)
    (f : E → F) (x : E) : G := A x (f x) + B x (fderivWithin ℝ f U x)

lemma WeightedBound.firstOrder {U : Set E} (hU : UniqueDiffOn ℝ U) {s K C : ℝ} {m : ℕ}
    {A : E → F →L[ℝ] G} {B : E → (E →L[ℝ] F) →L[ℝ] G} {f : E → F}
    (hs : 0 < s) (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) (hf : ContDiffOn ℝ ∞ f U)
    (hbA : WeightedBound U s m K A) (hbB : WeightedBound U s m K B)
    (hbf : WeightedBound U s (m + 1) C f) :
    WeightedBound U s m (2 ^ (m + 1) * K * C / s) (firstOrder U A B f) := by
  have hd : ContDiffOn ℝ ∞ (_root_.fderivWithin ℝ f U) U := hf.fderivWithin hU (by exact le_rfl)
  have ha := (hbA.clm_apply hU hs.le hK hC hA hf (hbf.mono_order (Nat.le_succ m)))
  have hb := hbB.clm_apply hU hs.le hK (div_nonneg hC hs.le) hB hd (hbf.fderivWithin hU hs)
  have hh := ha.add hU hs.le (hA.clm_apply hf) (hB.clm_apply hd) hb
  apply hh.mono_const
  have hh1 : 2 ^ m * K * C ≤ 2 ^ m * K * C / s := (le_div_iff₀ hs).2
    (mul_le_of_le_one_right (mul_nonneg (mul_nonneg (by positivity) hK) hC) hs1)
  calc
    _ ≤ 2 ^ m * K * C / s + 2 ^ m * K * (C / s) := add_le_add hh1 le_rfl
    _ = _ := by rw [pow_succ]; ring



lemma WeightedBound.comp {U : Set E} {V : Set F} (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V)
    {s C D : ℝ} {m : ℕ} {f : E → F} {g : F → G} (hs : 0 < s) (hC : 1 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g V) (hUV : MapsTo f U V)
    (hbf : WeightedBound U s m C f)
    (hbg : ∀ j ≤ m, ∀ x ∈ U, ‖iteratedFDerivWithin ℝ j g V (f x)‖ ≤ D) :
    WeightedBound U s m ((m.factorial : ℝ) * D * C ^ m) (g ∘ f) := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  intro j hj x hx
  have hi (i : ℕ) (hi1 : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i f U x‖ ≤ (C / s) ^ i := by
    have hp : C ≤ C ^ i := by
      simpa only [pow_one] using pow_le_pow_right₀ hC hi1
    calc
      _ ≤ C / s ^ i := hbf.deriv_le hs (hij.trans hj) hx
      _ ≤ C ^ i / s ^ i := div_le_div_of_nonneg_right hp (pow_nonneg hs.le _)
      _ = _ := (div_pow C s i).symm
  have hn : (j : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)
  have hh := norm_iteratedFDerivWithin_comp_le hg hf hn hV hU hUV hx
    (fun i hij => hbg i (hij.trans hj) x hx) hi
  calc
    _ ≤ s ^ j * ((j.factorial : ℝ) * D * (C / s) ^ j) :=
      mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
    _ = (j.factorial : ℝ) * D * C ^ j := by
      rw [div_pow]
      field_simp
    _ ≤ _ := by
      gcongr




lemma compact_coefficient_bound {V K : Set F} (hV : UniqueDiffOn ℝ V) (hK : IsCompact K)
    (hKV : K ⊆ V) {g : F → G} (hg : ContDiffOn ℝ ∞ g V) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ j ≤ m, ∀ y ∈ K, ‖iteratedFDerivWithin ℝ j g V y‖ ≤ D := by
  have hb (j : ℕ) : ∃ C, ∀ y ∈ K, ‖iteratedFDerivWithin ℝ j g V y‖ ≤ C :=
    hK.exists_bound_of_continuousOn ((hg.continuousOn_iteratedFDerivWithin
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)) hV).mono hKV)
  induction m with
  | zero =>
    obtain ⟨C, hC⟩ := hb 0
    refine ⟨max 1 C, le_max_left _ _, ?_⟩
    intro j hj y hy
    have : j = 0 := by omega
    subst j
    exact (hC y hy).trans (le_max_right _ _)
  | succ m ih =>
    obtain ⟨D, hD, hd⟩ := ih
    obtain ⟨C, hC⟩ := hb (m + 1)
    refine ⟨max D C, hD.trans (le_max_left _ _), ?_⟩
    intro j hj y hy
    by_cases hjm : j ≤ m
    · exact (hd j hjm y hy).trans (le_max_left _ _)
    · have : j = m + 1 := by omega
      subst j
      exact (hC y hy).trans (le_max_right _ _)

lemma smooth_compact_weighted_bound {U : Set E} {V K : Set F}
    (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V) (hK : IsCompact K) (hKV : K ⊆ V)
    {g : F → G} (hg : ContDiffOn ℝ ∞ g V) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (f : E → F) (s C : ℝ), 0 < s → 1 ≤ C →
      ContDiffOn ℝ ∞ f U → MapsTo f U K → WeightedBound U s m C f →
      WeightedBound U s m ((m.factorial : ℝ) * D * C ^ m) (g ∘ f) := by
  obtain ⟨D, hD, hbD⟩ := compact_coefficient_bound hV hK hKV hg m
  refine ⟨D, hD, ?_⟩
  intro f s C hs hC hf hfk hbf
  exact hbf.comp hU hV hs hC (le_trans zero_le_one hD) hf hg
    (fun x hx => hKV (hfk hx)) (fun j hj x hx => hbD j hj (f x) (hfk hx))


lemma contDiffOn_firstOrder {U : Set E} (hU : UniqueDiffOn ℝ U)
    {A : E → F →L[ℝ] G} {B : E → (E →L[ℝ] F) →L[ℝ] G} {f : E → F}
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (firstOrder U A B f) U :=
  (hA.clm_apply hf).add (hB.clm_apply (hf.fderivWithin hU (by exact le_rfl)))



def scaledHierarchy (U : Set E) (A : E → F →L[ℝ] F)
    (B : E → (E →L[ℝ] F) →L[ℝ] F) (τ : ℝ) (f : E → F) : ℕ → E → F
  | 0 => f
  | q + 1 => fun x => τ • firstOrder U A B (scaledHierarchy U A B τ f q) x

lemma contDiffOn_scaledHierarchy {U : Set E} (hU : UniqueDiffOn ℝ U)
    {A : E → F →L[ℝ] F} {B : E → (E →L[ℝ] F) →L[ℝ] F} {f : E → F}
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) (hf : ContDiffOn ℝ ∞ f U)
    (τ : ℝ) (q : ℕ) : ContDiffOn ℝ ∞ (scaledHierarchy U A B τ f q) U := by
  induction q with
  | zero => exact hf
  | succ q ih => exact (contDiffOn_firstOrder hU hA hB ih).const_smul τ



lemma weighted_scaledHierarchy {U : Set E} (hU : UniqueDiffOn ℝ U)
    {A : E → F →L[ℝ] F} {B : E → (E →L[ℝ] F) →L[ℝ] F} {f : E → F}
    {s τ K C : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hτ : 0 ≤ τ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) (hf : ContDiffOn ℝ ∞ f U)
    (m q : ℕ) (hbA : WeightedBound U s (m + q) K A) (hbB : WeightedBound U s (m + q) K B)
    (hbf : WeightedBound U s (m + q) C f) :
    WeightedBound U s m ((2 ^ (m + q + 1) * K * (τ / s)) ^ q * C)
      (scaledHierarchy U A B τ f q) := by
  induction q generalizing m with
  | zero => simpa [scaledHierarchy] using hbf
  | succ q ih =>
    have hsub : m + 1 + q = m + (q + 1) := by omega
    have hh := ih (m + 1) (hsub ▸ hbA) (hsub ▸ hbB) (hsub ▸ hbf)
    have hc : 0 ≤ (2 ^ (m + 1 + q + 1) * K * (τ / s)) ^ q * C := by positivity
    have hbase := WeightedBound.firstOrder (m := m) hU hs hs1 hK hc hA hB
      (contDiffOn_scaledHierarchy hU hA hB hf τ q)
      (hbA.mono_order (by omega)) (hbB.mono_order (by omega)) hh
    have ht := hbase.const_smul hU
      (contDiffOn_firstOrder hU hA hB (contDiffOn_scaledHierarchy hU hA hB hf τ q)) τ
    change WeightedBound U s m _ (fun x => τ • firstOrder U A B (scaledHierarchy U A B τ f q) x)
    apply ht.mono_const
    rw [abs_of_nonneg hτ, pow_succ]
    have hp : (2 : ℝ) ^ (m + 1) ≤ 2 ^ (m + (q + 1) + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have he : m + 1 + q + 1 = m + (q + 1) + 1 := by omega
    rw [he]
    calc
      _ = (2 ^ (m + 1) * K * (τ / s)) *
          ((2 ^ (m + (q + 1) + 1) * K * (τ / s)) ^ q * C) := by ring
      _ ≤ (2 ^ (m + (q + 1) + 1) * K * (τ / s)) *
          ((2 ^ (m + (q + 1) + 1) * K * (τ / s)) ^ q * C) := by gcongr
      _ = _ := by ring




lemma WeightedBound.congr {U : Set E} {s C : ℝ} {m : ℕ} {f g : E → F}
    (hf : WeightedBound U s m C f) (he : EqOn g f U) : WeightedBound U s m C g := by
  intro j hj x hx
  rw [iteratedFDerivWithin_congr he hx]
  exact hf j hj x hx

lemma WeightedBound.mul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ}
    {f g : E → ℂ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (2 ^ m * C * D) (fun x => f x * g x) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f U x‖ * ‖iteratedFDerivWithin ℝ (j - i) g U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_mul_le (n := j) (N := ∞) hf hg hU hx
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ ≤ 2 ^ j * C * D := weighted_binomial_bound hs hC hD j _ _
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun i hi => hbf i (hi.trans hj) x hx) (fun i hi => hbg i (hi.trans hj) x hx)
    _ ≤ _ := by gcongr; norm_num

lemma WeightedBound.const_mul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ}
    {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℂ) :
    WeightedBound U s m (‖a‖ * C) (fun x => a * f x) := by
  intro j hj x hx
  change s ^ j * ‖iteratedFDerivWithin ℝ j (a • f) U x‖ ≤ _
  rw [iteratedFDerivWithin_const_smul_apply
    ((hf.of_le (m := (j : ℕ∞ω)) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffWithinAt hx)
    hU hx, norm_smul]
  calc
    _ = ‖a‖ * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (norm_nonneg a)

lemma WeightedBound.directional {U : Set E} (hU : IsOpen U) {s C : ℝ} {m : ℕ}
    {f : E → F} (hs : 0 < s) (hf : ContDiffOn ℝ ∞ f U)
    (hb : WeightedBound U s (m + 1) C f) (v : E) :
    WeightedBound U s m (‖v‖ * (C / s)) (fun x => fderiv ℝ f x v) := by
  have hd := hb.fderivWithin hU.uniqueDiffOn hs
  have hdsm : ContDiffOn ℝ ∞ (_root_.fderivWithin ℝ f U) U :=
    hf.fderivWithin hU.uniqueDiffOn (by exact le_rfl)
  apply (hd.clm_apply_const hU.uniqueDiffOn hs.le hdsm v).congr
  intro x hx
  dsimp only
  rw [fderivWithin_of_isOpen hU hx]

lemma iteratedFDerivWithin_pi_smooth {ι : Type*} [Fintype ι] {U : Set E}
    (hU : UniqueDiffOn ℝ U) {f : ι → E → F} (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U)
    {x : E} (hx : x ∈ U) (j : ℕ) :
    iteratedFDerivWithin ℝ j (fun x i => f i x) U x =
      ContinuousMultilinearMap.pi (fun i => iteratedFDerivWithin ℝ j (f i) U x) := by
  have hp : ContDiffOn ℝ ∞ (fun x i => f i x) U := contDiffOn_pi.2 hf
  ext v i
  have he := (ContinuousLinearMap.proj i : (ι → F) →L[ℝ] F).iteratedFDerivWithin_comp_left
    (hp.contDiffWithinAt hx) hU hx (i := j)
    (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
  simpa only [Function.comp_def, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe,
    ContinuousMultilinearMap.pi_apply] using congrArg (fun T => T v) he.symm

lemma WeightedBound.pi {ι : Type*} [Fintype ι] {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C : ℝ} {m : ℕ} {f : ι → E → F} (hs : 0 < s) (hC : 0 ≤ C)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U) (hb : ∀ i, WeightedBound U s m C (f i)) :
    WeightedBound U s m C (fun x i => f i x) := by
  intro j hj x hx
  rw [iteratedFDerivWithin_pi_smooth hU hf hx j, ContinuousMultilinearMap.opNorm_pi]
  rw [mul_comm]
  apply (le_div_iff₀ (pow_pos hs j)).1
  exact (pi_norm_le_iff_of_nonneg (div_nonneg hC (pow_nonneg hs.le _))).2
    (fun i => (hb i).deriv_le hs hj hx)

lemma WeightedBound.component {ι : Type*} [Fintype ι] {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C : ℝ} {m : ℕ} {f : E → ι → F} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (i : ι) :
    WeightedBound U s m C (fun x => f x i) := by
  have hh := hb.linear hU hs hf (ContinuousLinearMap.proj i)
  apply hh.mono_const
  apply mul_le_of_le_one_left hC
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul, ContinuousLinearMap.proj_apply] using norm_le_pi_norm x i

lemma weightedBound_zero (U : Set E) (s : ℝ) (m : ℕ) :
    WeightedBound U s m 0 (fun _ : E => (0 : F)) := by
  intro j hj x hx
  simp

lemma WeightedBound.finset_sum {ι : Type*} {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s : ℝ} {m : ℕ} (hs : 0 ≤ s) (a : Finset ι) (C : ι → ℝ) (f : ι → E → F)
    (hf : ∀ i ∈ a, ContDiffOn ℝ ∞ (f i) U)
    (hb : ∀ i ∈ a, WeightedBound U s m (C i) (f i)) :
    WeightedBound U s m (∑ i ∈ a, C i) (fun x => ∑ i ∈ a, f i x) := by
  classical
  induction a using Finset.induction_on with
  | empty => simpa using weightedBound_zero U s m
  | @insert i a hi ih =>
    have ha := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hb j (Finset.mem_insert_of_mem hj))
    have hh := (hb i (Finset.mem_insert_self i a)).add hU hs
      (hf i (Finset.mem_insert_self i a))
      (ContDiffOn.sum (fun j hj => hf j (Finset.mem_insert_of_mem hj))) ha
    simpa only [Finset.sum_insert hi] using hh

lemma WeightedBound.dot {ι : Type*} [Fintype ι] {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C D : ℝ} {m : ℕ} {f g : E → ι → ℂ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m ((Fintype.card ι : ℝ) * (2 ^ m * C * D))
      (fun x => dotProduct (f x) (g x)) := by
  have hfsm (i : ι) := contDiffOn_pi.mp hf i
  have hgsm (i : ι) := contDiffOn_pi.mp hg i
  have hh := WeightedBound.finset_sum hU hs Finset.univ (fun _ : ι => 2 ^ m * C * D)
    (fun i x => f x i * g x i) (fun i _ => (hfsm i).mul (hgsm i)) (fun i _ =>
      (hbf.component hU hs hC hf i).mul hU hs hC hD (hfsm i) (hgsm i)
        (hbg.component hU hs hD hg i))
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, dotProduct] using hh

lemma WeightedBound.complex_smul_pi {ι : Type*} [Fintype ι] {U : Set E}
    (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} {f : E → ι → ℂ} (hs : 0 < s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℂ) :
    WeightedBound U s m (‖a‖ * C) (fun x => a • f x) := by
  apply WeightedBound.pi hU hs (mul_nonneg (norm_nonneg _) hC)
  · intro i
    exact contDiffOn_const.mul (contDiffOn_pi.mp hf i)
  · intro i
    exact (hb.component hU hs.le hC hf i).const_mul hU (contDiffOn_pi.mp hf i) a

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
