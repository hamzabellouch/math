import OAI.Geometry.Immersion.ClosedSurface.PhaseStock

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes



lemma dominant_power_ratio {ε a : ℝ} (ha : 1 ≤ a) (haε : 1 < ε * a)
    {i j : ℕ} (hij : i < j) : |a^i / a^j| < ε := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hp : a^(i+1) ≤ a^j := pow_le_pow_right₀ ha hij
  have ht : a^i / a^j ≤ 1 / a := by
    rw [div_le_div_iff₀ (pow_pos ha0 j) ha0]
    simpa [pow_succ] using hp
  have hε : 1 / a < ε := by
    rw [div_lt_iff₀ ha0]
    exact haε
  rw [abs_of_pos (div_pos (pow_pos ha0 i) (pow_pos ha0 j))]
  exact ht.trans_lt hε



lemma power_weight_pairs {n : ℕ} {B : Fin 3 → RVec n} {ξ υ : Base}
    {ε a : ℝ} (ha : 1 ≤ a) (haε : 1 < ε * a)
    (hmargin : ∀ t : ℝ, |t| < ε → Good B (ξ + t • υ))
    {i j : ℕ} (hij : i < j) :
    Good B (a^i • υ + a^j • ξ) ∧ Good B (a^i • υ - a^j • ξ) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hp := dominant_power_ratio ha haε hij
  have hplus := good_smul (pow_ne_zero j ha0.ne') (hmargin (a^i/a^j) hp)
  have hminus := good_smul (pow_ne_zero j ha0.ne')
    (hmargin (-(a^i/a^j)) (by simpa using hp))
  constructor
  · convert hplus using 1
    rw [smul_add, smul_smul, mul_div_cancel₀ _ (pow_ne_zero j ha0.ne')]
    exact add_comm _ _
  · have hn := good_neg hminus
    convert hn using 1
    rw [smul_add, smul_smul, mul_neg, mul_div_cancel₀ _ (pow_ne_zero j ha0.ne')]
    simp only [neg_smul, neg_add_rev, neg_neg, sub_eq_add_neg]



theorem bounded_label_weights {ι X : Type*} {n N : ℕ} (label : ι → Fin N)
    (B : X → Fin 3 → RVec n) (ξ : ι → X → Base) (overlap : ι → ι → X → Prop)
    {ε : ℝ} (hε : 0 < ε)
    (hlabels : ∀ i j x, overlap i j x → (label i).val < (label j).val)
    (hmargin : ∀ i j x, overlap i j x → ∀ t : ℝ, |t| < ε →
      Good (B x) (ξ j x + t • ξ i x)) :
    ∃ w : ι → ℝ, (∀ i, 0 < w i) ∧
      (∀ i, w i ≤ (1 + 1/ε)^N) ∧
      (∀ i j x, overlap i j x →
        Good (B x) (w i • ξ i x + w j • ξ j x) ∧
        Good (B x) (w i • ξ i x - w j • ξ j x)) := by
  let a : ℝ := 1 + 1/ε
  have ha : 1 ≤ a := by dsimp [a]; linarith [one_div_pos.mpr hε]
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have haε : 1 < ε * a := by
    dsimp [a]
    rw [mul_add, mul_one, mul_one_div_cancel hε.ne']
    linarith
  refine ⟨fun i => a^(label i).val, fun i => pow_pos ha0 _, ?_, ?_⟩
  · intro i
    exact pow_le_pow_right₀ ha (label i).isLt.le
  · intro i j x hx
    exact power_weight_pairs ha haε (hmargin i j x hx) (hlabels i j x hx)




theorem bounded_label_weights_symmetric {ι X : Type*} {n N : ℕ} (label : ι → Fin N)
    (B : X → Fin 3 → RVec n) (ξ : ι → X → Base) (overlap : ι → ι → X → Prop)
    {ε : ℝ} (hε : 0 < ε)
    (hsym : ∀ i j x, overlap i j x → overlap j i x)
    (hlabels : ∀ i j x, overlap i j x → label i ≠ label j)
    (hmargin : ∀ i j x, overlap i j x → ∀ t : ℝ, |t| < ε →
      Good (B x) (ξ j x + t • ξ i x)) :
    ∃ w : ι → ℝ, (∀ i, 0 < w i) ∧
      (∀ i, w i ≤ (1 + 1/ε)^N) ∧
      (∀ i j x, overlap i j x →
        Good (B x) (w i • ξ i x + w j • ξ j x) ∧
        Good (B x) (w i • ξ i x - w j • ξ j x)) := by
  let ordered (i j : ι) (x : X) := overlap i j x ∧ (label i).val < (label j).val
  obtain ⟨w,hwp,hwb,hw⟩ := bounded_label_weights label B ξ ordered hε
    (fun _ _ _ h => h.2) (fun i j x h => hmargin i j x h.1)
  refine ⟨w,hwp,hwb,fun i j x hij => ?_⟩
  have hne : (label i).val ≠ (label j).val :=
    fun he => hlabels i j x hij (Fin.ext he)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hw i j x ⟨hij,hlt⟩
  · obtain ⟨hp,hm⟩ := hw j i x ⟨hsym i j x hij,hgt⟩
    exact ⟨by simpa only [add_comm] using hp,
      by simpa only [neg_sub] using good_neg hm⟩

end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes Set Metric




theorem universal_normalized_phase_margin {n : ℕ} {ε C : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (B : Fin 3 → RVec n) (ξ υ : Base),
      ‖B‖ = 1 → ‖ξ‖ ≤ C → ‖υ‖ ≤ C →
      ε ≤ ‖secondQuadratic B (-ξ.2,ξ.1)‖ →
      ∀ t : ℝ, |t| < δ → Good B (ξ+t • υ) := by
  let K₀ : Set ((Fin 3 → RVec n) × Base) :=
    (sphere 0 1 ×ˢ closedBall 0 C) ∩
      {p | ε ≤ ‖secondQuadratic p.1 (-p.2.2,p.2.1)‖}
  have hc : Continuous (fun p : (Fin 3 → RVec n) × Base =>
      secondQuadratic p.1 (-p.2.2,p.2.1)) :=
    continuous_secondQuadratic.comp
      (continuous_fst.prodMk ((continuous_snd.snd.neg).prodMk continuous_snd.fst))
  have hK₀ : IsCompact K₀ := ((isCompact_sphere _ _).prod (isCompact_closedBall _ _)).inter_right
    (isClosed_le continuous_const hc.norm)
  let K : Set (((Fin 3 → RVec n) × Base) × Base) := K₀ ×ˢ closedBall 0 C
  have hgood (p : ((Fin 3 → RVec n) × Base) × Base) (hp : p ∈ K) : Good p.1.1 p.1.2 := by
    have hn : secondQuadratic p.1.1 (-p.1.2.2,p.1.2.1) ≠ 0 :=
      norm_pos_iff.mp (hε.trans_le hp.1.2)
    refine ⟨?_,hn⟩
    intro hz
    apply hn
    simp [hz,secondQuadratic]
  obtain ⟨δ,hδ,hd⟩ := uniform_good_perturbation (K := K)
    (hK₀.prod (isCompact_closedBall _ _)) continuous_fst.fst continuous_fst.snd continuous_snd hgood
  refine ⟨δ,hδ,fun B ξ υ hB hξ hυ hm t ht => hd t ht ((B,ξ),υ) ?_⟩
  exact ⟨⟨⟨by simpa [mem_sphere,dist_zero_right] using hB,
    by simpa [mem_closedBall,dist_zero_right] using hξ⟩,hm⟩,
    by simpa [mem_closedBall,dist_zero_right] using hυ⟩



theorem universal_relative_phase_margin {n : ℕ} {ε C : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (B : Fin 3 → RVec n) (ξ υ : Base),
      B ≠ 0 → ‖ξ‖ ≤ C → ‖υ‖ ≤ C →
      ε * ‖B‖ ≤ ‖secondQuadratic B (-ξ.2,ξ.1)‖ →
      ∀ t : ℝ, |t| < δ → Good B (ξ+t • υ) := by
  obtain ⟨δ,hδ,hd⟩ := universal_normalized_phase_margin (n := n) (C := C) hε
  refine ⟨δ,hδ,fun B ξ υ hB hξ hυ hm t ht => ?_⟩
  have hn : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have hu : ‖(‖B‖⁻¹ : ℝ) • B‖ = 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hn,inv_mul_cancel₀ hn.ne']
  have hm' : ε ≤ ‖secondQuadratic ((‖B‖⁻¹ : ℝ) • B) (-ξ.2,ξ.1)‖ := by
    rw [secondQuadratic_smul_form,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hn]
    have hl := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hn.le)
    simpa [mul_assoc,← mul_assoc (‖B‖⁻¹) ε,mul_comm (‖B‖⁻¹) ε,
      mul_assoc,inv_mul_cancel₀ hn.ne'] using hl
  exact (good_smul_form_iff (inv_ne_zero hn.ne')).mp (hd _ ξ υ hu hξ hυ hm' t ht)




theorem uniform_bounded_coframe_weights {n N : ℕ} {ε C : ℝ} (hε : 0 < ε) :
    ∃ W : ℝ, 0 < W ∧ ∀ (ι X : Type*) (label : ι → Fin N)
      (B : X → Fin 3 → RVec n) (ξ : ι → X → Base) (support : ι → Set X),
      (∀ i x, x ∈ support i → ‖ξ i x‖ ≤ C) →
      (∀ i x, x ∈ support i → B x ≠ 0 ∧ ε*‖B x‖ ≤ ‖secondQuadratic (B x) (-(ξ i x).2,(ξ i x).1)‖) →
      (∀ i j x, i ≠ j → x ∈ support i → x ∈ support j → label i ≠ label j) →
      ∃ w : ι → ℝ, (∀ i, 0 < w i ∧ w i ≤ W) ∧
        ∀ i j x, i ≠ j → x ∈ support i → x ∈ support j →
          Good (B x) (w i • ξ i x+w j • ξ j x) ∧
          Good (B x) (w i • ξ i x-w j • ξ j x) := by
  obtain ⟨δ,hδ,hd⟩ := universal_relative_phase_margin (n := n) (C := C) hε
  refine ⟨(1+1/δ)^N,by positivity,fun ι X label B ξ S hC hm hl => ?_⟩
  let O (i j : ι) (x : X) := i ≠ j ∧ x ∈ S i ∧ x ∈ S j
  obtain ⟨w,hwp,hwb,hw⟩ := bounded_label_weights_symmetric label B ξ O hδ
    (fun i j x hij => ⟨hij.1.symm,hij.2.2,hij.2.1⟩)
    (fun i j x hij => hl i j x hij.1 hij.2.1 hij.2.2)
    (fun i j x hij t ht => hd (B x) (ξ j x) (ξ i x) (hm j x hij.2.2).1
      (hC j x hij.2.2) (hC i x hij.2.1) (hm j x hij.2.2).2 t ht)
  exact ⟨w,fun i => ⟨hwp i,hwb i⟩,fun i j x hij hi hj => hw i j x ⟨hij,hi,hj⟩⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
