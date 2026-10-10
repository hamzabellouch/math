import OAI.Analysis.IrrationalRotation.Sampling.ScalarSamplingShear

namespace OAI

open Set

namespace Invariant233.ScalarSampling

lemma variation_add_le {f g : ℝ → ℝ} {s : Set ℝ} :
    eVariationOn (fun x => f x + g x) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  calc
    (∑ i ∈ Finset.range n, edist (f (u (i+1)) + g (u (i+1))) (f (u i) + g (u i))) ≤
        ∑ i ∈ Finset.range n, (edist (f (u (i+1))) (f (u i)) +
          edist (g (u (i+1))) (g (u i))) := by
      exact Finset.sum_le_sum (fun i _ => edist_add_add_le _ _ _ _)
    _ = (∑ i ∈ Finset.range n, edist (f (u (i+1))) (f (u i))) +
        (∑ i ∈ Finset.range n, edist (g (u (i+1))) (g (u i))) := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

lemma variation_mul_le {f g : ℝ → ℝ} {s : Set ℝ} {F G : ℝ}
    (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hf : ∀ x ∈ s, |f x| ≤ F) (hg : ∀ x ∈ s, |g x| ≤ G) :
    eVariationOn (fun x => f x * g x) s ≤
      ENNReal.ofReal F * eVariationOn g s + ENNReal.ofReal G * eVariationOn f s := by
  have hp (x y : ℝ) (hx : x ∈ s) (hy : y ∈ s) :
      edist (f x * g x) (f y * g y) ≤
        ENNReal.ofReal F * edist (g x) (g y) +
        ENNReal.ofReal G * edist (f x) (f y) := by
    simp only [edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_mul hF, ← ENNReal.ofReal_mul hG,
      ← ENNReal.ofReal_add (mul_nonneg hF (abs_nonneg _)) (mul_nonneg hG (abs_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    calc
      |f x * g x - f y * g y| = |f x * (g x - g y) + g y * (f x - f y)| := by ring_nf
      _ ≤ |f x * (g x - g y)| + |g y * (f x - f y)| := abs_add_le _ _
      _ = |f x| * |g x - g y| + |g y| * |f x - f y| := by rw [abs_mul, abs_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (hf x hx) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (hg y hy) (abs_nonneg _))
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  calc
    (∑ i ∈ Finset.range n, edist (f (u (i+1)) * g (u (i+1))) (f (u i) * g (u i))) ≤
        ∑ i ∈ Finset.range n, (ENNReal.ofReal F * edist (g (u (i+1))) (g (u i)) +
          ENNReal.ofReal G * edist (f (u (i+1))) (f (u i))) :=
      Finset.sum_le_sum (fun i _ => hp _ _ (hus _) (hus _))
    _ = ENNReal.ofReal F * (∑ i ∈ Finset.range n, edist (g (u (i+1))) (g (u i))) +
        ENNReal.ofReal G * (∑ i ∈ Finset.range n, edist (f (u (i+1))) (f (u i))) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_right (eVariationOn.sum_le hu hus) _)
      (mul_le_mul_right (eVariationOn.sum_le hu hus) _)

lemma monotone_variation_le_height {f : ℝ → ℝ} {C : ℝ}
    (hf : MonotoneOn f (Icc (0 : ℝ) 1))
    (hbound : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x ∧ f x ≤ C) :
    eVariationOn f (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal C := by
  have h := (hf.eVariationOn_eq (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)).le
  simp only [inter_self] at h
  exact h.trans (ENNReal.ofReal_le_ofReal (by linarith [(hbound 0 (by norm_num)).1,
    (hbound 1 (by norm_num)).2]))

lemma antitone_variation_le_height {f : ℝ → ℝ} {C : ℝ}
    (hf : AntitoneOn f (Icc (0 : ℝ) 1))
    (hbound : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x ∧ f x ≤ C) :
    eVariationOn f (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal C := by
  exact (antitone_variation_Icc_le hf).trans (ENNReal.ofReal_le_ofReal
    (by linarith [(hbound 0 (by norm_num)).2, (hbound 1 (by norm_num)).1]))

structure VariationControl (f : ℝ → ℝ) (C V : ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ f x
  le_height : ∀ x, f x ≤ C
  variation : eVariationOn f (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal V

lemma variation_step_le (P : ℝ → Prop) [DecidablePred P]
    (hP : (∀ x y, x ≤ y → P x → P y) ∨ (∀ x y, x ≤ y → P y → P x)) :
    eVariationOn (fun x => if P x then (1 : ℝ) else 0) (Icc (0 : ℝ) 1) ≤ 1 := by
  have hb (x : ℝ) (_ : x ∈ Icc (0 : ℝ) 1) :
      0 ≤ (if P x then (1 : ℝ) else 0) ∧ (if P x then (1 : ℝ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  rcases hP with hP | hP
  · have hm : MonotoneOn (fun x => if P x then (1 : ℝ) else 0) (Icc (0 : ℝ) 1) := by
      intro x _ y _ hxy
      by_cases hx : P x
      · simp [hx, hP x y hxy hx]
      · simp [hx]; split_ifs <;> norm_num
    simpa using monotone_variation_le_height hm hb
  · have hm : AntitoneOn (fun x => if P x then (1 : ℝ) else 0) (Icc (0 : ℝ) 1) := by
      intro x _ y _ hxy
      by_cases hy : P y
      · simp [hy, hP x y hxy hy]
      · simp [hy]; split_ifs <;> norm_num
    simpa using antitone_variation_le_height hm hb

lemma VariationControl.mask {f : ℝ → ℝ} {C V : ℝ}
    (hf : VariationControl f C V) (hC : 0 ≤ C) (hV : 0 ≤ V)
    (P : ℝ → Prop) [DecidablePred P]
    (hP : (∀ x y, x ≤ y → P x → P y) ∨ (∀ x y, x ≤ y → P y → P x)) :
    VariationControl (fun x => if P x then f x else 0) C (V + C) := by
  constructor
  · intro x; split_ifs; exact hf.nonneg x; exact le_rfl
  · intro x; split_ifs; exact hf.le_height x; exact hC
  · let g : ℝ → ℝ := fun x => if P x then 1 else 0
    have heq : (fun x => if P x then f x else 0) = fun x => f x * g x := by
      funext x; simp only [g]; split_ifs <;> simp
    rw [heq]
    have hb : ∀ x ∈ Icc (0 : ℝ) 1, |g x| ≤ 1 := by
      intro x _; simp only [g]; split_ifs <;> norm_num
    calc
      eVariationOn (fun x => f x * g x) (Icc (0 : ℝ) 1) ≤
          ENNReal.ofReal C * eVariationOn g (Icc (0 : ℝ) 1) +
          ENNReal.ofReal 1 * eVariationOn f (Icc (0 : ℝ) 1) :=
        variation_mul_le hC (by norm_num)
          (fun x _ => by rw [abs_of_nonneg (hf.nonneg x)]; exact hf.le_height x) hb
      _ ≤ ENNReal.ofReal C * 1 + ENNReal.ofReal 1 * ENNReal.ofReal V :=
        add_le_add (mul_le_mul_right (variation_step_le P hP) _) (mul_le_mul_right hf.variation _)
      _ = ENNReal.ofReal (V + C) := by
        simp only [ENNReal.ofReal_one, mul_one, one_mul]
        rw [← ENNReal.ofReal_add hC hV, add_comm]

lemma clipped_reciprocal_control {h α : ℝ} (hh : 0 < h) (hα : 0 < α)
    (g : ℝ → ℝ) (hg : Monotone g ∨ Antitone g) :
    VariationControl (fun x => (h * max α (g x))⁻¹) (h * α)⁻¹ (h * α)⁻¹ := by
  have hpos (x : ℝ) : 0 < h * max α (g x) := mul_pos hh (hα.trans_le (le_max_left _ _))
  have hn (x : ℝ) : 0 ≤ (h * max α (g x))⁻¹ := inv_nonneg.mpr (hpos x).le
  have hb (x : ℝ) : (h * max α (g x))⁻¹ ≤ (h * α)⁻¹ := by
    exact inv_anti₀ (mul_pos hh hα) (mul_le_mul_of_nonneg_left (le_max_left _ _) hh.le)
  refine ⟨hn, hb, ?_⟩
  rcases hg with hg | hg
  · apply antitone_variation_le_height
    · intro x _ y _ hxy
      exact inv_anti₀ (hpos x) (mul_le_mul_of_nonneg_left (max_le_max_left α (hg hxy)) hh.le)
    · exact fun x _ => ⟨hn x, hb x⟩
  · apply monotone_variation_le_height
    · intro x _ y _ hxy
      exact inv_anti₀ (hpos y) (mul_le_mul_of_nonneg_left (max_le_max_left α (hg hxy)) hh.le)
    · exact fun x _ => ⟨hn x, hb x⟩

noncomputable def leftEndpointPiece (h α s v : ℝ) : ℝ :=
  if 0 < v then if v < h * (s - v) then if α ≤ s - v then
    if s - v ≤ 1 / 2 then (h * max α (s - v))⁻¹ else 0 else 0 else 0 else 0

noncomputable def rightEndpointPiece (h α s v : ℝ) : ℝ :=
  if 0 < v then if v < h * (1 - s + v) then if α ≤ 1 - s + v then
    if 1 / 2 < s - v then (h * max α (1 - s + v))⁻¹ else 0 else 0 else 0 else 0

lemma leftEndpointPiece_control {h α : ℝ} (hh : 0 < h) (hα : 0 < α) (s : ℝ) :
    VariationControl (leftEndpointPiece h α s) (h * α)⁻¹ (5 * (h * α)⁻¹) := by
  have hC : 0 ≤ (h * α)⁻¹ := by positivity
  have hb := clipped_reciprocal_control hh hα (fun v => s - v)
    (Or.inr (show Antitone (fun v : ℝ => s - v) from fun _ _ hxy => sub_le_sub_left hxy s))
  have h1 := hb.mask hC hC (fun v => s - v ≤ 1 / 2)
    (Or.inl (by intro x y hxy hx; linarith))
  have h2 := h1.mask hC (by positivity) (fun v => α ≤ s - v)
    (Or.inr (by intro x y hxy hy; linarith))
  have h3 := h2.mask hC (by positivity) (fun v => v < h * (s - v))
    (Or.inr (by intro x y hxy hy; nlinarith))
  have h4 := h3.mask hC (by positivity) (fun v => 0 < v)
    (Or.inl (by intro x y hxy hx; exact hx.trans_le hxy))
  convert h4 using 1
  · rfl
  · ring

lemma rightEndpointPiece_control {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (s : ℝ) :
    VariationControl (rightEndpointPiece h α s) (h * α)⁻¹ (5 * (h * α)⁻¹) := by
  have hC : 0 ≤ (h * α)⁻¹ := by positivity
  have hb := clipped_reciprocal_control hh hα (fun v => 1 - s + v)
    (Or.inl (show Monotone (fun v : ℝ => 1 - s + v) from by intro x y hxy; dsimp; linarith))
  have h1 := hb.mask hC hC (fun v => 1 / 2 < s - v)
    (Or.inr (by intro x y hxy hy; linarith))
  have h2 := h1.mask hC (by positivity) (fun v => α ≤ 1 - s + v)
    (Or.inl (by intro x y hxy hx; linarith))
  have h3 := h2.mask hC (by positivity) (fun v => v < h * (1 - s + v))
    (Or.inr (by intro x y hxy hy; nlinarith))
  have h4 := h3.mask hC (by positivity) (fun v => 0 < v)
    (Or.inl (by intro x y hxy hx; exact hx.trans_le hxy))
  convert h4 using 1
  · rfl
  · ring

lemma rawEndpoint_eq_pieces (h α s v : ℝ) :
    rawKernel h α (s - v) v = leftEndpointPiece h α s v + rightEndpointPiece h α s v := by
  by_cases hm : s - v ≤ 1 / 2
  · have hd : delta (s - v) = s - v := by
      unfold delta; rw [min_eq_left (by linarith)]
    have hn : ¬ 1 / 2 < s - v := not_lt.mpr hm
    by_cases hc : α ≤ s - v
    · simp only [rawKernel, hd, ite_eq_left hc, max_eq_right hc,
        leftEndpointPiece, rightEndpointPiece, ite_eq_left hm, ite_eq_right hn,
        Set.indicator_apply, mem_Ioo]
      split_ifs <;> simp_all
    · simp only [rawKernel, hd, ite_eq_right hc, leftEndpointPiece, rightEndpointPiece,
        ite_eq_left hm, ite_eq_right hn]
      split_ifs <;> simp_all
  · have hm' : 1 / 2 < s - v := lt_of_not_ge hm
    have hd : delta (s - v) = 1 - s + v := by
      unfold delta; rw [min_eq_right (by linarith)]; ring
    by_cases hc : α ≤ 1 - s + v
    · simp only [rawKernel, hd, ite_eq_left hc, leftEndpointPiece, rightEndpointPiece,
        ite_eq_right hm, ite_eq_left hm', max_eq_right hc, Set.indicator_apply, mem_Ioo]
      split_ifs <;> simp_all
    · simp only [rawKernel, hd, ite_eq_right hc, leftEndpointPiece, rightEndpointPiece,
        ite_eq_right hm, ite_eq_left hm']
      split_ifs <;> simp_all

theorem rawEndpoint_variation_le {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (s : ℝ) :
    eVariationOn (fun v => rawKernel h α (s - v) v) (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (10 * (h * α)⁻¹) := by
  have hl := (leftEndpointPiece_control hh hα s).variation
  have hr := (rightEndpointPiece_control hh hhone hα s).variation
  have heq : (fun v => rawKernel h α (s - v) v) =
      fun v => leftEndpointPiece h α s v + rightEndpointPiece h α s v := by
    funext v; exact rawEndpoint_eq_pieces h α s v
  rw [heq]
  calc
    _ ≤ eVariationOn (leftEndpointPiece h α s) (Icc (0 : ℝ) 1) +
        eVariationOn (rightEndpointPiece h α s) (Icc (0 : ℝ) 1) := variation_add_le
    _ ≤ ENNReal.ofReal (5 * (h * α)⁻¹) + ENNReal.ofReal (5 * (h * α)⁻¹) := add_le_add hl hr
    _ = ENNReal.ofReal (10 * (h * α)⁻¹) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; ring

theorem endpoint_no_wrap_on_unit {h α s v : ℝ} (_hh : 0 ≤ h) (hhone : h ≤ 1)
    (hα : 0 < α) (hs : s ∈ Ico (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    circleKernel h α (s - v) v = rawKernel h α (s - v) v := by
  rcases lt_or_eq_of_le hv.2 with hvone | hvone
  · unfold circleKernel
    rw [Int.fract_eq_self.mpr ⟨hv.1, hvone⟩]
    by_cases hvs : v ≤ s
    · rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith [hs.2, hv.1]⟩]
    · have hsv : s < v := lt_of_not_ge hvs
      have hcut : ¬ α ≤ delta (s - v) := by
        have hd : delta (s - v) ≤ s - v := min_le_left _ _
        linarith
      have hfloor : ⌊s - v⌋ = -1 := by
        apply Int.floor_eq_iff.mpr
        norm_num
        constructor <;> linarith [hs.1]
      have hfract : Int.fract (s - v) = s - v + 1 := by
        rw [Int.fract, hfloor]; norm_num
      rw [hfract]
      unfold rawKernel
      rw [ite_eq_right hcut]
      split_ifs
      · apply Set.indicator_of_notMem
        intro hmem
        have hd0 : 0 ≤ delta (s - v + 1) := by
          apply delta_nonneg; constructor <;> linarith [hs.1]
        have hd : delta (s - v + 1) ≤ v - s := by
          exact (min_le_right _ _).trans (by linarith)
        have hm : h * delta (s - v + 1) ≤ delta (s - v + 1) := by
          nlinarith
        linarith [hmem.2, hs.1]
      · rfl
  · subst v
    have hcut : ¬ α ≤ delta (s - 1) := by
      have hd : delta (s - 1) ≤ s - 1 := min_le_left _ _
      linarith [hs.2]
    simp only [circleKernel, Int.fract_one]
    rw [rawKernel_zero]
    simp only [rawKernel, ite_eq_right hcut]

lemma circleEndpoint_fract (h α z v : ℝ) :
    circleKernel h α (z - v) v = circleKernel h α (Int.fract z - v) v := by
  have heq : Int.fract z - v = (z - v) - (⌊z⌋ : ℤ) := by
    rw [Int.fract]; ring
  simp only [circleKernel, heq, Int.fract_sub_intCast]

theorem circleEndpoint_variation_le {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (z : ℝ) :
    eVariationOn (fun v => circleKernel h α (z - v) v) (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (10 * (h * α)⁻¹) := by
  have heq : EqOn (fun v => circleKernel h α (z - v) v)
      (fun v => rawKernel h α (Int.fract z - v) v) (Icc (0 : ℝ) 1) := by
    intro v hv
    dsimp only
    rw [circleEndpoint_fract]
    exact endpoint_no_wrap_on_unit hh.le hhone hα ⟨Int.fract_nonneg z, Int.fract_lt_one z⟩ hv
  rw [eVariationOn.congr heq]
  exact rawEndpoint_variation_le hh hhone hα _

theorem manuscriptEndpointKernel_variation_le {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    eVariationOn (manuscriptEndpointKernel m z) (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (10 * (m : ℝ) ^ (13 / 5 : ℝ)) := by
  obtain ⟨hh, hhone, hα, _⟩ := manuscript_parameters hm
  change eVariationOn (fun v => circleKernel _ _ (z - v) v) _ ≤ _
  simpa only [manuscript_reciprocal_height hm] using
    circleEndpoint_variation_le hh hhone hα z

theorem manuscriptEndpointKernel_sup_le {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    sSup (Set.range (fun v : ℝ => |manuscriptEndpointKernel m z v|)) ≤
      (m : ℝ) ^ (13 / 5 : ℝ) := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨v, rfl⟩
  have hh := (manuscript_parameters hm).1
  have hn : 0 ≤ manuscriptKernel m (z-v) v :=
    rawKernel_nonneg hh.le ⟨Int.fract_nonneg (z-v), (Int.fract_lt_one (z-v)).le⟩
  dsimp only [manuscriptEndpointKernel]
  rw [abs_of_nonneg hn]
  exact manuscriptKernel_le_height hm _ _

theorem manuscriptEndpointKernel_BV_bound {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    BoundedVariationOn (manuscriptEndpointKernel m z) (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun v : ℝ => |manuscriptEndpointKernel m z v|)) +
          (eVariationOn (manuscriptEndpointKernel m z) (Icc (0 : ℝ) 1)).toReal ≤
        11 * (m : ℝ) ^ (13 / 5 : ℝ) := by
  constructor
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (manuscriptEndpointKernel_variation_le hm z)
  · have hv := ENNReal.toReal_le_of_le_ofReal
      (by positivity) (manuscriptEndpointKernel_variation_le hm z)
    have hf := manuscriptEndpointKernel_sup_le hm z
    linarith

theorem manuscriptEndpointKernel_BV_bound_ten {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    sSup (Set.range (fun v : ℝ => |manuscriptEndpointKernel m z v|)) +
        (eVariationOn (manuscriptEndpointKernel m z) (Icc (0 : ℝ) 1)).toReal ≤
      11 * (m : ℝ)^10 := by
  calc
    _ ≤ 11 * (m : ℝ) ^ (13 / 5 : ℝ) := (manuscriptEndpointKernel_BV_bound hm z).2
    _ ≤ 11 * (m : ℝ)^10 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ m))
        (by norm_num)

end Invariant233.ScalarSampling

end OAI
