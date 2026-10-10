import OAI.Geometry.Immersion.ClosedSurface.WeightMargins

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes Set Metric



theorem universal_normalized_length_margin {n : ℕ} {ε C : ℝ} (hε : 0 < ε) :
    ∃ δ κ : ℝ, 0 < δ ∧ 0 < κ ∧ ∀ (B : Fin 3 → RVec n) (ξ υ : Base),
      ‖B‖ = 1 → ‖ξ‖ ≤ C → ‖υ‖ ≤ C →
      ε ≤ ‖secondQuadratic B (-ξ.2,ξ.1)‖ →
      ∀ t : ℝ, |t| ≤ δ → κ ≤ ‖secondQuadratic B (-(ξ+t • υ).2,(ξ+t • υ).1)‖ := by
  obtain ⟨d,hd,hgood⟩ := universal_normalized_phase_margin (n := n) (C := C) hε
  let δ := d/2
  have hδ : 0 < δ := half_pos hd
  let K₀ : Set ((Fin 3 → RVec n) × Base) :=
    (sphere 0 1 ×ˢ closedBall 0 C) ∩ {p | ε ≤ ‖secondQuadratic p.1 (-p.2.2,p.2.1)‖}
  have hc : Continuous (fun p : (Fin 3 → RVec n) × Base =>
      secondQuadratic p.1 (-p.2.2,p.2.1)) :=
    continuous_secondQuadratic.comp
      (continuous_fst.prodMk ((continuous_snd.snd.neg).prodMk continuous_snd.fst))
  have hK₀ : IsCompact K₀ := ((isCompact_sphere _ _).prod (isCompact_closedBall _ _)).inter_right
    (isClosed_le continuous_const hc.norm)
  let K : Set (((Fin 3 → RVec n) × Base) × (Base × ℝ)) :=
    K₀ ×ˢ (closedBall 0 C ×ˢ Icc (-δ) δ)
  have hK : IsCompact K := hK₀.prod ((isCompact_closedBall _ _).prod isCompact_Icc)
  let f : (((Fin 3 → RVec n) × Base) × (Base × ℝ)) → ℝ := fun p =>
    ‖secondQuadratic p.1.1 (-(p.1.2+p.2.2 • p.2.1).2,(p.1.2+p.2.2 • p.2.1).1)‖
  have hg : Continuous (fun p : (((Fin 3 → RVec n) × Base) × (Base × ℝ)) =>
      (p.1.1, (-(p.1.2+p.2.2 • p.2.1).2,(p.1.2+p.2.2 • p.2.1).1))) := by fun_prop
  have hf : Continuous f := (continuous_secondQuadratic.comp hg).norm
  have hpos : ∀ p ∈ K, 0 < f p := by
    intro p hp
    have hb : ‖p.1.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hp.1.1.1
    have hξ : ‖p.1.2‖ ≤ C := by simpa only [mem_closedBall,dist_zero_right] using hp.1.1.2
    have hυ : ‖p.2.1‖ ≤ C := by simpa only [mem_closedBall,dist_zero_right] using hp.2.1
    have ht : |p.2.2| < d := (abs_le.mpr hp.2.2).trans_lt (by dsimp [δ]; linarith)
    exact norm_pos_iff.mpr (hgood p.1.1 p.1.2 p.2.1 hb hξ hυ hp.1.2 p.2.2 ht).2
  obtain ⟨κ,hκ,hb⟩ := hK.exists_forall_le' hf.continuousOn hpos
  refine ⟨δ,κ,hδ,hκ,fun B ξ υ hB hξ hυ hm t ht => ?_⟩
  apply hb ((B,ξ),(υ,t))
  exact ⟨⟨⟨by simpa [mem_sphere,dist_zero_right] using hB,
    by simpa [mem_closedBall,dist_zero_right] using hξ⟩,hm⟩,
    by simpa [mem_closedBall,dist_zero_right] using hυ,abs_le.mp ht⟩



theorem universal_relative_length_margin {n : ℕ} {ε C : ℝ} (hε : 0 < ε) :
    ∃ δ κ : ℝ, 0 < δ ∧ 0 < κ ∧ ∀ (B : Fin 3 → RVec n) (ξ υ : Base),
      B ≠ 0 → ‖ξ‖ ≤ C → ‖υ‖ ≤ C →
      ε*‖B‖ ≤ ‖secondQuadratic B (-ξ.2,ξ.1)‖ →
      ∀ t : ℝ, |t| ≤ δ → κ*‖B‖ ≤ ‖secondQuadratic B (-(ξ+t • υ).2,(ξ+t • υ).1)‖ := by
  obtain ⟨δ,κ,hδ,hκ,hm⟩ := universal_normalized_length_margin (n := n) (C := C) hε
  refine ⟨δ,κ,hδ,hκ,fun B ξ υ hB hξ hυ hmargin t ht => ?_⟩
  have hn : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have hu : ‖(‖B‖⁻¹ : ℝ) • B‖ = 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hn,inv_mul_cancel₀ hn.ne']
  have hmargin' : ε ≤ ‖secondQuadratic ((‖B‖⁻¹ : ℝ) • B) (-ξ.2,ξ.1)‖ := by
    rw [secondQuadratic_smul_form,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hn]
    have hl := mul_le_mul_of_nonneg_left hmargin (inv_nonneg.mpr hn.le)
    simpa [mul_assoc,← mul_assoc (‖B‖⁻¹) ε,mul_comm (‖B‖⁻¹) ε,
      mul_assoc,inv_mul_cancel₀ hn.ne'] using hl
  have hh := hm _ ξ υ hu hξ hυ hmargin' t ht
  rw [secondQuadratic_smul_form,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hn] at hh
  have hl := mul_le_mul_of_nonneg_left hh hn.le
  simpa [← mul_assoc,mul_inv_cancel₀ hn.ne',mul_comm κ ‖B‖] using hl

end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma norm_secondQuadratic_rotated_smul {n : ℕ} (B : Fin 3 → RVec n) (ξ : Base) (a : ℝ) :
    ‖secondQuadratic B (-(a • ξ).2,(a • ξ).1)‖ =
      a^2*‖secondQuadratic B (-ξ.2,ξ.1)‖ := by
  have he : (-(a • ξ).2,(a • ξ).1) = a • (-ξ.2,ξ.1) := by
    ext <;> simp [mul_neg]
  rw [he,secondQuadratic_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg a)]

lemma norm_secondQuadratic_rotated_neg {n : ℕ} (B : Fin 3 → RVec n) (ξ : Base) :
    ‖secondQuadratic B (-(-ξ).2,(-ξ).1)‖ = ‖secondQuadratic B (-ξ.2,ξ.1)‖ := by
  simpa only [neg_one_smul,neg_sq,one_pow,one_mul] using
    norm_secondQuadratic_rotated_smul B ξ (-1)

lemma power_weight_length_pairs {n : ℕ} (B : Fin 3 → RVec n) (ξ υ : Base)
    {δ a κ : ℝ} (ha : 1 ≤ a) (haδ : 1 < δ*a)
    (hmargin : ∀ t : ℝ, |t| < δ → κ*‖B‖ ≤ ‖secondQuadratic B (-(ξ+t • υ).2,(ξ+t • υ).1)‖)
    {i j : ℕ} (hij : i < j) :
    κ*‖B‖ ≤ ‖secondQuadratic B (-(a^i • υ+a^j • ξ).2,(a^i • υ+a^j • ξ).1)‖ ∧
    κ*‖B‖ ≤ ‖secondQuadratic B (-(a^i • υ-a^j • ξ).2,(a^i • υ-a^j • ξ).1)‖ := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hp := dominant_power_ratio ha haδ hij
  have hpj : 1 ≤ a^j := one_le_pow₀ ha
  have hsq : 1 ≤ (a^j)^2 := by nlinarith
  have lift (v : Base) : ‖secondQuadratic B (-v.2,v.1)‖ ≤
      ‖secondQuadratic B (-(a^j • v).2,(a^j • v).1)‖ := by
    rw [norm_secondQuadratic_rotated_smul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hsq (norm_nonneg (secondQuadratic B (-v.2,v.1)))
  have heplus : a^j • (ξ+(a^i/a^j) • υ) = a^i • υ+a^j • ξ := by
    rw [smul_add,smul_smul,mul_div_cancel₀ _ (pow_ne_zero j ha0.ne')]
    exact add_comm _ _
  have heminus : a^j • (ξ+(-(a^i/a^j)) • υ) = -(a^i • υ-a^j • ξ) := by
    rw [smul_add,smul_smul,mul_neg,mul_div_cancel₀ _ (pow_ne_zero j ha0.ne')]
    simp only [neg_smul]
    abel
  constructor
  · have hh := (hmargin _ hp).trans (lift _)
    simpa only [heplus] using hh
  · have hh := (hmargin (-(a^i/a^j)) (by simpa only [abs_neg] using hp)).trans (lift _)
    simpa only [heminus,norm_secondQuadratic_rotated_neg] using hh

lemma good_of_direction_length_pos {n : ℕ} (B : Fin 3 → RVec n) (ξ : Base)
    (h : 0 < ‖secondQuadratic B (-ξ.2,ξ.1)‖) : Good B ξ := by
  refine ⟨?_, norm_pos_iff.mp h⟩
  intro hξ
  simp [hξ,secondQuadratic] at h





theorem quantitative_labeled_phase_lengths_with_catalog {ι X : Type*} {n N : ℕ}
    (label : ι → Fin N) {ε C : ℝ} (hε : 0 < ε) :
    ∃ stock : Finset ℝ, ∃ W κ : ℝ, 0 < W ∧ 0 < κ ∧
      ∀ (B : X → Fin 3 → RVec n) (ξ : ι → X → Base) (active : ι → X → Prop),
      (∀ i j x, i ≠ j → active i x → active j x → label i ≠ label j) →
      (∀ i x, active i x → B x ≠ 0 ∧ ‖ξ i x‖ ≤ C ∧
        ε*‖B x‖ ≤ ‖secondQuadratic (B x) (-(ξ i x).2,(ξ i x).1)‖) →
      ∃ w : ι → ℝ, (∀ i, w i ∈ stock) ∧ (∀ i, 1 ≤ w i ∧ w i ≤ W) ∧
      ∀ i j x, i ≠ j → active i x → active j x →
        κ*‖B x‖ ≤ ‖secondQuadratic (B x) (-(w i • ξ i x+w j • ξ j x).2,(w i • ξ i x+w j • ξ j x).1)‖ ∧
        κ*‖B x‖ ≤ ‖secondQuadratic (B x) (-(w i • ξ i x-w j • ξ j x).2,(w i • ξ i x-w j • ξ j x).1)‖ ∧
        Good (B x) (w i • ξ i x+w j • ξ j x) ∧ Good (B x) (w i • ξ i x-w j • ξ j x) := by
  classical
  obtain ⟨δ,κ,hδ,hκ,hm⟩ := universal_relative_length_margin (n := n) (C := C) hε
  let a : ℝ := 1+1/δ
  have ha : 1 ≤ a := by dsimp [a]; linarith [one_div_pos.mpr hδ]
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have haδ : 1 < δ*a := by
    dsimp [a]
    rw [mul_add,mul_one,mul_one_div_cancel hδ.ne']
    linarith
  let stock : Finset ℝ := Finset.univ.image (fun j : Fin N => a^j.val)
  refine ⟨stock,a^N,κ,pow_pos ha0 N,hκ,?_⟩
  intro B ξ active hlabels hdata
  let w : ι → ℝ := fun i => a^(label i).val
  refine ⟨w,(fun i => Finset.mem_image.mpr ⟨label i,Finset.mem_univ _,rfl⟩),fun i => ⟨one_le_pow₀ ha,pow_le_pow_right₀ ha (label i).isLt.le⟩,?_⟩
  intro i j x hij hi hj
  have hw (i j : ι) (hi : active i x) (hj : active j x) (hl : (label i).val < (label j).val) :
      κ*‖B x‖ ≤ ‖secondQuadratic (B x) (-(w i • ξ i x+w j • ξ j x).2,(w i • ξ i x+w j • ξ j x).1)‖ ∧
      κ*‖B x‖ ≤ ‖secondQuadratic (B x) (-(w i • ξ i x-w j • ξ j x).2,(w i • ξ i x-w j • ξ j x).1)‖ := by
    exact power_weight_length_pairs (B x) (ξ j x) (ξ i x) ha haδ
      (fun t ht => hm (B x) (ξ j x) (ξ i x) (hdata j x hj).1
        (hdata j x hj).2.1 (hdata i x hi).2.1 (hdata j x hj).2.2 t ht.le) hl
  have hlengths :
      κ*‖B x‖ ≤ ‖secondQuadratic (B x) (-(w i • ξ i x+w j • ξ j x).2,(w i • ξ i x+w j • ξ j x).1)‖ ∧
      κ*‖B x‖ ≤ ‖secondQuadratic (B x) (-(w i • ξ i x-w j • ξ j x).2,(w i • ξ i x-w j • ξ j x).1)‖ := by
    have hne : (label i).val ≠ (label j).val := fun he => hlabels i j x hij hi hj (Fin.ext he)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hw i j hi hj hlt
    · obtain ⟨hp,hm⟩ := hw j i hj hi hgt
      constructor
      · simpa only [add_comm] using hp
      · have he : w j • ξ j x-w i • ξ i x = -(w i • ξ i x-w j • ξ j x) := by abel
        simpa only [he,norm_secondQuadratic_rotated_neg] using hm
  have hn : 0 < κ*‖B x‖ := mul_pos hκ (norm_pos_iff.mpr (hdata i x hi).1)
  exact ⟨hlengths.1,hlengths.2,good_of_direction_length_pos _ _ (hn.trans_le hlengths.1),
    good_of_direction_length_pos _ _ (hn.trans_le hlengths.2)⟩

theorem quantitative_labeled_phase_lengths {ι X : Type*} {n N : ℕ}
    (label : ι → Fin N) {ε C : ℝ} (hε : 0 < ε) :
    ∃ W κ : ℝ, 0 < W ∧ 0 < κ ∧
      ∀ (B : X → Fin 3 → RVec n) (ξ : ι → X → Base) (active : ι → X → Prop),
      (∀ i j x, i ≠ j → active i x → active j x → label i ≠ label j) →
      (∀ i x, active i x → B x ≠ 0 ∧ ‖ξ i x‖ ≤ C ∧
        ε*‖B x‖ ≤ ‖secondQuadratic (B x) (-(ξ i x).2,(ξ i x).1)‖) →
      ∃ w : ι → ℝ, (∀ i, 1 ≤ w i ∧ w i ≤ W) ∧
      ∀ i j x, i ≠ j → active i x → active j x →
        κ*‖B x‖ ≤ ‖secondQuadratic (B x) (-(w i • ξ i x+w j • ξ j x).2,(w i • ξ i x+w j • ξ j x).1)‖ ∧
        κ*‖B x‖ ≤ ‖secondQuadratic (B x) (-(w i • ξ i x-w j • ξ j x).2,(w i • ξ i x-w j • ξ j x).1)‖ ∧
        Good (B x) (w i • ξ i x+w j • ξ j x) ∧ Good (B x) (w i • ξ i x-w j • ξ j x) := by
  obtain ⟨stock,W,κ,hW,hκ,h⟩ := quantitative_labeled_phase_lengths_with_catalog
    (n := n) (C := C) label hε
  refine ⟨W,κ,hW,hκ,?_⟩
  intro B ξ active hlabels hdata
  obtain ⟨w,_,hw,hm⟩ := h B ξ active hlabels hdata
  exact ⟨w,hw,hm⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
