import OAI.Geometry.Kahler.HartogsPinching

namespace OAI

universe uKahler16710_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
noncomputable section

open Set Filter Topology Metric
open scoped ContDiff NNReal

namespace CompactODE

variable {E : Type uKahler16710_1} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def CurveOn (V : E → E) (S : Set E) (γ : ℝ → E) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, HasDerivAt γ (V (γ t)) t ∧ γ t ∈ S

omit [CompleteSpace E] in
lemma CurveOn.mono [CompleteSpace E] {V : E → E} {S : Set E} {γ : ℝ → E} {J K : Set ℝ}
    (h : CurveOn V S γ J) (hK : K ⊆ J) : CurveOn V S γ K :=
  fun t ht => h t (hK ht)

lemma local_uniform {V : E → E} {S : Set E} {x₀ : E}
    (hS : IsOpen S) (hx₀ : x₀ ∈ S) (hV : ContDiffAt ℝ 1 V x₀) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ x ∈ closedBall x₀ r,
      ∃ γ : ℝ → E, γ 0 = x ∧ CurveOn V S γ (Ioo (-ε) ε) := by
  obtain ⟨K, s, hs, hl⟩ := hV.exists_lipschitzOnWith
  obtain ⟨a, ha, has⟩ := Metric.mem_nhds_iff.mp (inter_mem hs (hS.mem_nhds hx₀))
  have has' : ball x₀ a ⊆ s := fun _ h => (has h).1
  have haS : closedBall x₀ (a / 2) ⊆ S := fun _ h =>
    (has (closedBall_subset_ball (half_lt_self ha) h)).2
  set L := K * a + ‖V x₀‖ + 1 with hL
  have hL0 : 0 < L := by positivity
  have hb (x : E) (hx : x ∈ closedBall x₀ (a / 2)) : ‖V x‖ ≤ L := by
    rw [hL]
    calc
      ‖V x‖ ≤ ‖V x - V x₀‖ + ‖V x₀‖ := norm_le_norm_sub_add _ _
      _ ≤ K * ‖x - x₀‖ + ‖V x₀‖ := by
        gcongr
        apply hl.norm_sub_le _ (mem_of_mem_nhds hs)
        exact has' (closedBall_subset_ball (half_lt_self ha) hx)
      _ ≤ K * a + ‖V x₀‖ := by
        gcongr
        rw [← mem_closedBall_iff_norm]
        exact closedBall_subset_closedBall (half_le_self ha.le) hx
      _ ≤ L := le_add_of_nonneg_right zero_le_one
  let ε := a / L / 2 / 2
  have hε : 0 < ε := by positivity
  let A : ℝ≥0 := ⟨a / 2, (half_pos ha).le⟩
  let LL : ℝ≥0 := ⟨L, hL0.le⟩
  let tzero : Icc (-ε) ε := ⟨0, by simp [hε.le]⟩
  have hpl : IsPicardLindelof (fun _ => V) (tmin := -ε) (tmax := ε)
      tzero x₀ A (A / 2) LL K := by
    apply IsPicardLindelof.of_time_independent hb
      (hl.mono (subset_trans (closedBall_subset_ball (half_lt_self ha)) has'))
    change L * max (ε - 0) (0 - -ε) ≤ (a / 2) - (a / 2 / 2)
    simp only [sub_zero, sub_neg_eq_add, zero_add, max_self]
    dsimp [ε]
    field_simp
    nlinarith
  refine ⟨a / 2 / 2, by positivity, ε, hε, fun x hx => ?_⟩
  have hx' : x ∈ closedBall x₀ ((A / 2 : ℝ≥0) : ℝ) := hx
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hpl hx'
  refine ⟨α.compProj, ?_, fun t ht => ⟨?_, ?_⟩⟩
  · change α.compProj (tzero : ℝ) = x
    rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · have hd : HasDerivWithinAt α.compProj (V (α.compProj t)) (Icc (-ε) ε) t := by
      apply ODE.hasDerivWithinAt_picard_Icc (show (0 : ℝ) ∈ Icc (-ε) ε by simp [hε.le])
        hpl.continuousOn_uncurry α.continuous_compProj.continuousOn
        (fun _ ht' => α.compProj_mem_closedBall hpl.mul_max_le) x (Ioo_subset_Icc_self ht)
        |>.congr_of_mem _ (Ioo_subset_Icc_self ht)
      intro t' ht'
      nth_rw 1 [← hα]
      rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
    exact hd.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  · exact haS (α.compProj_mem_closedBall hpl.mul_max_le)

omit [CompleteSpace E] in
lemma local_unique [CompleteSpace E] {V : E → E} {γ δ : ℝ → E} {t₀ : ℝ}
    (hV : ContDiffAt ℝ 1 V (γ t₀))
    (hγ : ∀ᶠ t in 𝓝 t₀, HasDerivAt γ (V (γ t)) t)
    (hδ : ∀ᶠ t in 𝓝 t₀, HasDerivAt δ (V (δ t)) t)
    (heq : γ t₀ = δ t₀) : γ =ᶠ[𝓝 t₀] δ := by
  obtain ⟨K, s, hs, hL⟩ := hV.exists_lipschitzOnWith
  have hγs : ∀ᶠ t in 𝓝 t₀, γ t ∈ s := (hγ.self_of_nhds.continuousAt) hs
  have hδs : ∀ᶠ t in 𝓝 t₀, δ t ∈ s := (hδ.self_of_nhds.continuousAt) (heq ▸ hs)
  exact ODE_solution_unique_of_eventually (v := fun _ => V) (s := fun _ => s)
    (Eventually.of_forall fun _ => hL) (hγ.and hγs) (hδ.and hδs) heq

lemma unique_Ioo {V : E → E} {S : Set E} {γ δ : ℝ → E} {a b t₀ : ℝ}
    (hV : ∀ x ∈ S, ContDiffAt ℝ 1 V x) (ht₀ : t₀ ∈ Ioo a b)
    (hγ : CurveOn V S γ (Ioo a b)) (hδ : CurveOn V S δ (Ioo a b))
    (heq : γ t₀ = δ t₀) : EqOn γ δ (Ioo a b) := by
  set s := {t | γ t = δ t} ∩ Ioo a b with hs
  suffices hsub : Ioo a b ⊆ s from fun t ht => (hsub ht).1
  apply isPreconnected_Ioo.subset_of_closure_inter_subset (s := Ioo a b) (u := s) _
    ⟨t₀, ⟨ht₀, ⟨heq, ht₀⟩⟩⟩
  · rw [hs, inter_comm, ← Subtype.image_preimage_val, inter_comm, ← Subtype.image_preimage_val,
      image_subset_image_iff Subtype.val_injective, preimage_ofPred_eq]
    intro t ht
    rw [mem_preimage, ← closure_subtype] at ht
    revert ht t
    apply IsClosed.closure_subset (isClosed_eq _ _)
    · rw [continuous_iff_continuousAt]
      rintro ⟨t, ht⟩
      exact (hγ t ht).1.continuousAt.comp continuousAt_subtype_val
    · rw [continuous_iff_continuousAt]
      rintro ⟨t, ht⟩
      exact (hδ t ht).1.continuousAt.comp continuousAt_subtype_val
  · rw [isOpen_iff_mem_nhds]
    intro t ht
    have hmem := Ioo_mem_nhds ht.2.1 ht.2.2
    have hloc : γ =ᶠ[𝓝 t] δ := local_unique (hV (γ t) (hγ t ht.2).2)
      (Filter.Eventually.mono hmem fun t' ht' => (hγ t' ht').1)
      (Filter.Eventually.mono hmem fun t' ht' => (hδ t' ht').1) ht.1
    exact (hloc.and hmem).mono fun _ h => h

lemma compact_uniform {V : E → E} {S K : Set E} (hS : IsOpen S)
    (hV : ∀ x ∈ S, ContDiffAt ℝ 1 V x) (hK : IsCompact K) (hKS : K ⊆ S) :
    ∃ ε > (0 : ℝ), ∀ x ∈ K, ∃ γ : ℝ → E, γ 0 = x ∧ CurveOn V S γ (Ioo (-ε) ε) := by
  classical
  have hl (x : K) := local_uniform hS (hKS x.2) (hV x (hKS x.2))
  choose r hr ε hε H using hl
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => ball (x : E) (r x))
    (fun _ => isOpen_ball) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr _)⟩)
  have hmin : ∃ d > (0 : ℝ), ∀ x ∈ t, d ≤ ε x := by
    clear ht
    induction t using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert x t hx ih =>
      obtain ⟨d, hd, hdt⟩ := ih
      exact ⟨min d (ε x), lt_min hd (hε x), fun y hy => by
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hdt y hy)⟩
  obtain ⟨d, hd, hdt⟩ := hmin
  refine ⟨d, hd, fun x hx => ?_⟩
  obtain ⟨z, hzt, hzx⟩ := mem_iUnion₂.mp (ht hx)
  obtain ⟨γ, hγ0, hγ⟩ := H z x (ball_subset_closedBall hzx)
  exact ⟨γ, hγ0, hγ.mono (Ioo_subset_Ioo (neg_le_neg (hdt z hzt)) (hdt z hzt))⟩

lemma eqOn_piecewise {V : E → E} {S : Set E} {γ δ : ℝ → E} {a b a' b' t₀ : ℝ}
    (hV : ∀ x ∈ S, ContDiffAt ℝ 1 V x)
    (hγ : CurveOn V S γ (Ioo a b)) (hδ : CurveOn V S δ (Ioo a' b'))
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo a' b') (heq : γ t₀ = δ t₀) :
    EqOn (piecewise (Ioo a b) γ δ) δ (Ioo a' b') := by
  classical
  have H : EqOn γ δ (Ioo (max a a') (min b b')) :=
    unique_Ioo hV ⟨max_lt ht₀.1.1 ht₀.2.1, lt_min ht₀.1.2 ht₀.2.2⟩
      (hγ.mono (Ioo_subset_Ioo (le_max_left ..) (min_le_left ..)))
      (hδ.mono (Ioo_subset_Ioo (le_max_right ..) (min_le_right ..))) heq
  intro t ht
  by_cases hmem : t ∈ Ioo a b
  · rw [piecewise, ite_eq_left hmem]
    exact H ⟨max_lt hmem.1 ht.1, lt_min hmem.2 ht.2⟩
  · rw [piecewise, ite_eq_right hmem]

lemma curveOn_piecewise {V : E → E} {S : Set E} {γ δ : ℝ → E} {a b a' b' t₀ : ℝ}
    (hV : ∀ x ∈ S, ContDiffAt ℝ 1 V x)
    (hγ : CurveOn V S γ (Ioo a b)) (hδ : CurveOn V S δ (Ioo a' b'))
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo a' b') (heq : γ t₀ = δ t₀) :
    CurveOn V S (piecewise (Ioo a b) γ δ) (Ioo a b ∪ Ioo a' b') := by
  classical
  intro t ht
  by_cases hmem : t ∈ Ioo a b
  · have hev : piecewise (Ioo a b) γ δ =ᶠ[𝓝 t] γ := by
      filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with s hs
      exact piecewise_eq_of_mem _ _ _ hs
    rw [hev.self_of_nhds]
    exact ⟨(hγ t hmem).1.congr_of_eventuallyEq hev, (hγ t hmem).2⟩
  · have hmem' : t ∈ Ioo a' b' := ht.resolve_left hmem
    have hev : piecewise (Ioo a b) γ δ =ᶠ[𝓝 t] δ := by
      filter_upwards [Ioo_mem_nhds hmem'.1 hmem'.2] with s hs
      exact eqOn_piecewise hV hγ hδ ht₀ heq hs
    rw [hev.self_of_nhds]
    exact ⟨(hδ t hmem').1.congr_of_eventuallyEq hev, (hδ t hmem').2⟩

omit [CompleteSpace E] in
lemma curveOn_shift [CompleteSpace E] {V : E → E} {S : Set E} {γ : ℝ → E} {ε s : ℝ}
    (hγ : CurveOn V S γ (Ioo (-ε) ε)) :
    CurveOn V S (fun t => γ (t - s)) (Ioo (s - ε) (s + ε)) := by
  intro t ht
  have hm : t - s ∈ Ioo (-ε) ε := by constructor <;> linarith [ht.1, ht.2]
  refine ⟨?_, (hγ (t - s) hm).2⟩
  simpa [Function.comp_def] using! (hγ (t - s) hm).1.scomp t ((hasDerivAt_id t).sub_const s)

lemma global_from_intervals {V : E → E} {S : Set E} {x : E}
    (hV : ∀ p ∈ S, ContDiffAt ℝ 1 V p)
    (h : ∀ a : ℝ, ∃ γ : ℝ → E, γ 0 = x ∧ CurveOn V S γ (Ioo (-a) a)) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (V (γ t)) t ∧ γ t ∈ S := by
  choose γ hγ0 hγ using h
  have hEq {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) : EqOn (γ b) (γ a) (Ioo (-b) b) := by
    apply unique_Ioo hV ⟨by linarith, hb⟩ (hγ b)
      ((hγ a).mono (Ioo_subset_Ioo (neg_le_neg hba) hba))
    rw [hγ0, hγ0]
  let Γ : ℝ → E := fun t => γ (|t| + 1) t
  have hΓ {a : ℝ} : EqOn Γ (γ a) (Ioo (-a) a) := by
    intro t ht
    by_cases hlt : |t| + 1 < a
    · exact hEq (by positivity) hlt.le (abs_lt.mp (lt_add_one _))
    · exact (hEq (by linarith [ht.1, ht.2]) (le_of_not_gt hlt) ht).symm
  refine ⟨Γ, hγ0 _, fun t => ?_⟩
  have ht : t ∈ Ioo (-(|t| + 1)) (|t| + 1) := abs_lt.mp (lt_add_one _)
  have hev : Γ =ᶠ[𝓝 t] γ (|t| + 1) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hΓ hs
  rw [hev.self_of_nhds]
  exact ⟨(hγ _ t ht).1.congr_of_eventuallyEq hev, (hγ _ t ht).2⟩

theorem global_of_compact_containment {V : E → E} {S : Set E} {x : E}
    (hS : IsOpen S) (hx : x ∈ S) (hV : ∀ p ∈ S, ContDiffAt ℝ 1 V p)
    (hcontain : ∀ T : ℝ, 0 < T → ∃ K : Set E, IsCompact K ∧ K ⊆ S ∧
      ∀ (a : ℝ) (γ : ℝ → E), 0 < a → γ 0 = x → CurveOn V S γ (Ioo (-a) a) →
        ∀ t ∈ Ioo (-a) a, |t| ≤ T → γ t ∈ K) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (V (γ t)) t ∧ γ t ∈ S := by
  classical
  let s : Set ℝ := {a | ∃ γ : ℝ → E, γ 0 = x ∧ CurveOn V S γ (Ioo (-a) a)}
  obtain ⟨r, hr, ε₀, hε₀, H₀⟩ := local_uniform hS hx (hV x hx)
  have hs₀ : ε₀ ∈ s := H₀ x (mem_closedBall_self hr.le)
  suffices hn : ¬BddAbove s by
    rw [not_bddAbove_iff] at hn
    apply global_from_intervals hV
    intro a
    obtain ⟨b, ⟨γ, hγ0, hγ⟩, hab⟩ := hn a
    exact ⟨γ, hγ0, hγ.mono (Ioo_subset_Ioo (neg_le_neg hab.le) hab.le)⟩
  intro hbdd
  let T := sSup s
  have hε₀T : ε₀ ≤ T := le_csSup hbdd hs₀
  have hT : 0 < T := hε₀.trans_le hε₀T
  obtain ⟨K, hK, hKS, hbound⟩ := hcontain T hT
  obtain ⟨d, hd, H⟩ := compact_uniform hS hV hK hKS
  let ε := min d T
  have hε : 0 < ε := lt_min hd hT
  have hεd : ε ≤ d := min_le_left _ _
  have hεT : ε ≤ T := min_le_right _ _
  have H' : ∀ y ∈ K, ∃ γ : ℝ → E, γ 0 = y ∧ CurveOn V S γ (Ioo (-ε) ε) := by
    intro y hy
    obtain ⟨γ, hγ0, hγ⟩ := H y hy
    exact ⟨γ, hγ0, hγ.mono (Ioo_subset_Ioo (neg_le_neg hεd) hεd)⟩
  obtain ⟨a, ha, hlt⟩ := Real.add_neg_lt_sSup (⟨ε₀, hs₀⟩ : s.Nonempty)
    (ε := -(ε / 2)) (by linarith)
  change T + -(ε / 2) < a at hlt
  obtain ⟨γ, hγ0, hγ⟩ := ha
  have ha0 : 0 < a := by linarith
  have htpos : 0 < T - ε / 2 := by linarith
  have ht : T - ε / 2 ∈ Ioo (-a) a := by constructor <;> linarith
  have hnt : -(T - ε / 2) ∈ Ioo (-a) a := by constructor <;> linarith
  obtain ⟨γ₁, hγ₁0, hγ₁⟩ := H' (γ (-(T - ε / 2)))
    (hbound a γ ha0 hγ0 hγ _ hnt (by rw [abs_neg, abs_of_pos htpos]; linarith))
  obtain ⟨γ₂, hγ₂0, hγ₂⟩ := H' (γ (T - ε / 2))
    (hbound a γ ha0 hγ0 hγ _ ht (by rw [abs_of_pos htpos]; linarith))
  let δ₁ : ℝ → E := fun t => γ₁ (t - -(T - ε / 2))
  let δ₂ : ℝ → E := fun t => γ₂ (t - (T - ε / 2))
  have hd₁ : CurveOn V S δ₁ (Ioo (-(T - ε / 2) - ε) (-(T - ε / 2) + ε)) :=
    curveOn_shift hγ₁
  have hd₂ : CurveOn V S δ₂ (Ioo ((T - ε / 2) - ε) ((T - ε / 2) + ε)) :=
    curveOn_shift hγ₂
  have he₁ : γ (-(T - ε / 2)) = δ₁ (-(T - ε / 2)) := by simp [δ₁, hγ₁0]
  have he₂ : γ (T - ε / 2) = δ₂ (T - ε / 2) := by simp [δ₂, hγ₂0]
  let γleft : ℝ → E := piecewise (Ioo (-a) a) γ δ₁
  have hleft : CurveOn V S γleft (Ioo (-(T + ε / 2)) a) := by
    apply (curveOn_piecewise hV hγ hd₁ ⟨hnt, ⟨by linarith, by linarith⟩⟩ he₁).mono
    intro t ht'
    by_cases hta : -a < t
    · exact Or.inl ⟨hta, ht'.2⟩
    · right
      constructor <;> linarith [ht'.1, le_of_not_gt hta]
  let Γ : ℝ → E := piecewise (Ioo (-(T + ε / 2)) a) γleft δ₂
  have hext : CurveOn V S Γ (Ioo (-(T + ε / 2)) (T + ε / 2)) := by
    apply (curveOn_piecewise hV hleft hd₂
      ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
      (show γleft (T - ε / 2) = δ₂ (T - ε / 2) from by
        simpa only [γleft, piecewise, ite_eq_left ht] using he₂)).mono
    intro t ht'
    by_cases hta : t < a
    · exact Or.inl ⟨ht'.1, hta⟩
    · right
      constructor <;> linarith [ht'.2, le_of_not_gt hta]
  have hΓ0 : Γ 0 = x := by
    have houter : (0 : ℝ) ∈ Ioo (-(T + ε / 2)) a := ⟨by linarith, ha0⟩
    have hinner : (0 : ℝ) ∈ Ioo (-a) a := ⟨by linarith, ha0⟩
    simp only [Γ, γleft, piecewise, ite_eq_left houter, ite_eq_left hinner, hγ0]
  have hend : T + ε / 2 ∈ s := ⟨Γ, hΓ0, hext⟩
  have := le_csSup hbdd hend
  change T + ε / 2 ≤ T at this
  linarith

omit [CompleteSpace E] in
lemma contDiff_of_hasDerivAt [CompleteSpace E] {V : E → E} {γ : ℝ → E}
    (hV : ∀ t, ContDiffAt ℝ ∞ V (γ t))
    (hγ : ∀ t, HasDerivAt γ (V (γ t)) t) : ContDiff ℝ ∞ γ := by
  have hd : deriv γ = V ∘ γ := funext fun t => (hγ t).deriv
  apply contDiff_infty.mpr
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun t => (hγ t).continuousAt)
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
    refine ⟨fun t => (hγ t).differentiableAt, by simp, ?_⟩
    rw [hd]
    apply contDiff_iff_contDiffAt.mpr
    intro t
    exact ((hV t).of_le (by exact WithTop.coe_le_coe.mpr le_top)).comp t ih.contDiffAt

end CompactODE

namespace PinchedHartogs

theorem hartogsMetric_geodesicallyComplete {φ : Base → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ ball) (hpsh : IsPshBase φ) {lam : ℝ} (hlam : 0 < lam) :
    GeodesicallyComplete (hartogs φ) (hartogsMetric φ lam) := by
  intro p hp v
  let g := hartogsMetric φ lam
  have hg := hartogsMetric_isKahler hφ hpsh hlam
  have hM := hartogs_isOpen_smooth hφ
  have hS : IsOpen (hartogs φ ×ˢ (univ : Set Ambient)) := hM.prod isOpen_univ
  have hV (y : Ambient × Ambient) (hy : y ∈ hartogs φ ×ˢ (univ : Set Ambient)) :
      ContDiffAt ℝ 1 (geodesicField g) y :=
    (geodesicField_contDiffAt hM hg hy.1).of_le (by simp)
  obtain ⟨y, hy0, hy⟩ := CompactODE.global_of_compact_containment hS
    (show (p, v) ∈ hartogs φ ×ˢ (univ : Set Ambient) from ⟨hp, mem_univ _⟩) hV (by
      intro T hT
      obtain ⟨K, hK, hKS, hB⟩ := hartogs_geodesic_compact_containment hφ hpsh hlam hp v hT
      refine ⟨K, hK, hKS, ?_⟩
      intro a y ha hy0 hy t ht htT
      exact hB a y ha hy0 (fun s hs => ⟨(hy s hs).1, (hy s hs).2.1⟩) t ht htT)
  have hys : ContDiff ℝ ∞ y := CompactODE.contDiff_of_hasDerivAt
    (fun t => geodesicField_contDiffAt hM hg (hy t).2.1) (fun t => (hy t).1)
  let γ : ℝ → Ambient := fun t => (y t).1
  have hγ (t : ℝ) : HasDerivAt γ (y t).2 t := (hy t).1.fst
  have hν (t : ℝ) : HasDerivAt (fun s => (y s).2) (geodesicAcceleration g (y t).1 (y t).2) t :=
    (hy t).1.snd
  have hdγ : deriv γ = fun t => (y t).2 := funext fun t => (hγ t).deriv
  refine ⟨γ, contDiff_fst.comp hys, (fun t => (hy t).2.1), ?_, ?_, ?_⟩
  · exact congrArg Prod.fst hy0
  · rw [hdγ]
    exact congrArg Prod.snd hy0
  · intro t k
    rw [hdγ, (hν t).deriv]
    simp only [geodesicAcceleration, coordinates_equiv_symm, g, γ, neg_add_cancel]

end PinchedHartogs

end

end OAI
