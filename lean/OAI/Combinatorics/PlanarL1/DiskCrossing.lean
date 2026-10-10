import OAI.Combinatorics.PlanarL1.Noncrossing

namespace OAI

section

/-! ## Planar disk crossing by covering-angle lifting. -/

namespace PlanarL1.Topology
open Complex Real

/-- The planar rectangle crossing obstruction, proved by lifting angles rather
than assuming a Jordan separation theorem. -/
lemma rectangle_zero (F : C(unitInterval × unitInterval, ℂ))
    (hleft : ∀ t, (F (0,t)).re < 0)
    (hright : ∀ t, 0 < (F (1,t)).re)
    (hbottom : ∀ s, 0 < (F (s,0)).im)
    (htop : ∀ s, (F (s,1)).im < 0) :
    ∃ p, F p=0 := by
  by_contra! hn
  let cov : IsCoveringMap ((↑) : ℝ → Real.Angle) := AddCircle.isCoveringMap_coe (2*π)
  let H : C(unitInterval × unitInterval, Real.Angle) :=
    ⟨fun p => (Complex.arg (F p) : Real.Angle), by
      apply continuous_iff_continuousAt.mpr
      intro p
      exact (Complex.continuousAt_arg_coe_angle (hn p)).comp F.continuous.continuousAt⟩
  have left_cont : Continuous (fun t : unitInterval => Complex.arg (-F (0,t))+π) := by
    apply Continuous.add_const
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (Complex.continuousAt_arg (by
      left
      simpa using neg_pos.mpr (hleft t))).comp
      ((F.continuous.comp (continuous_const.prodMk continuous_id)).neg.continuousAt)
  let L : C(unitInterval, ℝ) := ⟨fun t => Complex.arg (-F (0,t))+π,left_cont⟩
  have hL (t : unitInterval) : H (0,t) = (L t : Real.Angle) := by
    dsimp [H,L]
    rw [Complex.arg_neg_coe_angle (hn _)]
    simp only [add_assoc,Real.Angle.coe_pi_add_coe_pi,add_zero]
  let θ := cov.liftHomotopy H L hL
  have θ_left : ∀ t, θ (0,t)=L t := cov.liftHomotopy_zero H L hL
  have θ_lifts (p : unitInterval × unitInterval) : (θ p : Real.Angle)=H p :=
    congr_fun (cov.liftHomotopy_lifts H L hL) p
  have arg_cont (f : C(unitInterval, ℂ)) (hf : ∀ t, f t ∈ Complex.slitPlane) :
      Continuous (fun t => Complex.arg (f t)) := by
    exact continuous_iff_continuousAt.mpr fun t =>
      (Complex.continuousAt_arg (hf t)).comp f.continuous.continuousAt
  have bottom_cont : Continuous (fun s : unitInterval => Complex.arg (F (s,0))) := by
    apply arg_cont ⟨fun s => F (s,0),F.continuous.comp (continuous_id.prodMk continuous_const)⟩
    intro s
    exact Or.inr (ne_of_gt (hbottom s))
  have top_cont : Continuous (fun s : unitInterval => Complex.arg (F (s,1))) := by
    apply arg_cont ⟨fun s => F (s,1),F.continuous.comp (continuous_id.prodMk continuous_const)⟩
    intro s
    exact Or.inr (ne_of_lt (htop s))
  have right_cont : Continuous (fun t : unitInterval => Complex.arg (F (1,t))) := by
    apply arg_cont ⟨fun t => F (1,t),F.continuous.comp (continuous_const.prodMk continuous_id)⟩
    intro t
    exact Or.inl (hright t)
  have hbottom_eq : (fun s : unitInterval => θ (s,0)) = fun s => Complex.arg (F (s,0)) := by
    refine cov.eq_of_comp_eq
      (θ.continuous.comp (continuous_id.prodMk continuous_const)) bottom_cont ?_ 0 ?_
    · exact funext fun s => θ_lifts (s,0)
    · rw [θ_left]
      dsimp [L]
      rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos (hbottom 0)]
      ring
  have hright_eq : (fun t : unitInterval => θ (1,t)) = fun t => Complex.arg (F (1,t)) := by
    refine cov.eq_of_comp_eq
      (θ.continuous.comp (continuous_const.prodMk continuous_id)) right_cont ?_ 0 ?_
    · exact funext fun t => θ_lifts (1,t)
    · exact congr_fun hbottom_eq 1
  have htop_eq : (fun s : unitInterval => θ (s,1)) =
      fun s => Complex.arg (F (s,1))+2*π := by
    refine cov.eq_of_comp_eq
      (θ.continuous.comp (continuous_id.prodMk continuous_const)) (top_cont.add_const _) ?_ 0 ?_
    · funext s
      change (θ (s,1) : Real.Angle) = ((Complex.arg (F (s,1))+2*π : ℝ) : Real.Angle)
      rw [Real.Angle.coe_add,Real.Angle.coe_two_pi,add_zero]
      exact θ_lifts (s,1)
    · rw [θ_left]
      dsimp [L]
      rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg (htop 0)]
      ring
  have hb := congr_fun htop_eq 1
  have hr := congr_fun hright_eq 1
  have := Real.pi_pos
  linarith

lemma disk_re_lt_one {z : ℂ} (h : ‖z‖ ≤ 1) (hne : z ≠ 1) : z.re < 1 := by
  have hre := Complex.re_le_norm z
  have hs := Complex.sq_norm_sub_sq_re z
  have hn := norm_nonneg z
  by_contra! hc
  have he : z.re=1 := by linarith
  have hi : z.im=0 := by nlinarith [sq_nonneg z.im]
  exact hne (Complex.ext (by simpa using he) (by simpa using hi))

lemma disk_im_lt_one {z : ℂ} (h : ‖z‖ ≤ 1) (hne : z ≠ Complex.I) : z.im < 1 := by
  have him := Complex.im_le_norm z
  have hs := Complex.sq_norm_sub_sq_im z
  have hn := norm_nonneg z
  by_contra! hc
  have he : z.im=1 := by linarith
  have hr : z.re=0 := by nlinarith [sq_nonneg z.re]
  exact hne (Complex.ext (by simpa using hr) (by simpa using he))

/-- Opposite endpoints in a disk force two continuous arcs to meet. This is
one normal form of nonalternation. -/
lemma disk_opposite_arcs_meet (f g : C(unitInterval, ℂ))
    (hf : ∀ s, ‖f s‖ ≤ 1) (hg : ∀ t, ‖g t‖ ≤ 1)
    (hf0 : f 0 = -1) (hf1 : f 1 = 1)
    (hg0 : g 0 = -Complex.I) (hg1 : g 1 = Complex.I) :
    ∃ s t, f s=g t := by
  by_contra! hn
  let F : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => f p.1-g p.2,(f.continuous.comp continuous_fst).sub
      (g.continuous.comp continuous_snd)⟩
  have hleft (t : unitInterval) : (F (0,t)).re < 0 := by
    have hne : -g t ≠ (1 : ℂ) := by
      intro he
      apply hn 0 t
      rw [hf0]
      exact (neg_eq_iff_eq_neg.mp he).symm
    have hh := disk_re_lt_one (z := -g t) (by simpa using hg t) hne
    dsimp [F]
    simp only [Complex.neg_re] at hh
    simp only [hf0,Complex.neg_re,Complex.one_re]
    linarith
  have hright (t : unitInterval) : 0 < (F (1,t)).re := by
    have hh := disk_re_lt_one (hg t) (by
      intro he
      exact hn 1 t (hf1.trans he.symm))
    dsimp [F]
    simp only [hf1,Complex.one_re]
    linarith
  have hbottom (s : unitInterval) : 0 < (F (s,0)).im := by
    have hne : -f s ≠ Complex.I := by
      intro he
      exact hn s 0 ((neg_eq_iff_eq_neg.mp he).trans hg0.symm)
    have hh := disk_im_lt_one (z := -f s) (by simpa using hf s) hne
    dsimp [F]
    simp only [hg0,Complex.neg_im,Complex.I_im] at *
    linarith
  have htop (s : unitInterval) : (F (s,1)).im < 0 := by
    have hh := disk_im_lt_one (hf s) (by
      intro he
      exact hn s 1 (he.trans hg1.symm))
    dsimp [F]
    simp only [hg1,Complex.I_im]
    linarith
  obtain ⟨⟨s,t⟩,h⟩ := rectangle_zero F hleft hright hbottom htop
  exact hn s t (sub_eq_zero.mp h)

end PlanarL1.Topology



end

section

/-! ## General cyclic-endpoint disk separation -/

namespace PlanarL1.Topology
open Complex Real Set

/- An explicit annular extension reduces arbitrary cyclic boundary endpoints
  to the already-proved cardinal-endpoint disk crossing obstruction. -/
noncomputable def annularConnector (a b : ℝ) :
    Path (Circle.exp a : ℂ) ((2 : ℂ) * (Circle.exp b : ℂ)) where
  toFun t := ((1 + (t : ℝ) : ℝ) : ℂ) *
    (Circle.exp ((1 - (t : ℝ)) * a + (t : ℝ) * b) : ℂ)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by norm_num

lemma norm_annularConnector (a b : ℝ) (t : unitInterval) :
    ‖annularConnector a b t‖ = 1 + (t : ℝ) := by
  change ‖((1 + (t : ℝ) : ℝ) : ℂ) *
    (Circle.exp ((1 - (t : ℝ)) * a + (t : ℝ) * b) : ℂ)‖ = _
  rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by linarith [t.2.1])]

lemma annularConnector_disjoint {a a' b b' : ℝ}
    (ha : a < a') (ha' : a' - a < 2 * π)
    (hb : b < b') (hb' : b' - b < 2 * π) :
    Disjoint (range (annularConnector a b)) (range (annularConnector a' b')) := by
  rw [Set.disjoint_left]
  rintro z ⟨s, hs⟩ ⟨t, ht⟩
  have he : annularConnector a b s = annularConnector a' b' t := hs.trans ht.symm
  have hn := congrArg norm he
  rw [norm_annularConnector, norm_annularConnector] at hn
  have hst : s = t := Subtype.ext (by linarith)
  subst t
  have hs0 := s.2.1
  have hs1 := s.2.2
  let u := (1 - (s : ℝ)) * a + (s : ℝ) * b
  let v := (1 - (s : ℝ)) * a' + (s : ℝ) * b'
  have huv : u < v := by
    dsimp [u,v]
    by_cases hz : (s : ℝ) = 0
    · simpa [hz] using ha
    · have hp : 0 < (s : ℝ) := lt_of_le_of_ne hs0 (Ne.symm hz)
      exact add_lt_add_of_le_of_lt
        (mul_le_mul_of_nonneg_left ha.le (sub_nonneg.mpr hs1))
        (mul_lt_mul_of_pos_left hb hp)
  have hspan : v - u < 2 * π := by
    dsimp [u,v]
    by_cases hz : (s : ℝ) = 0
    · simpa [hz] using ha'
    · have hp : 0 < (s : ℝ) := lt_of_le_of_ne hs0 (Ne.symm hz)
      have h₁ := mul_le_mul_of_nonneg_left ha'.le (sub_nonneg.mpr hs1)
      have h₂ := mul_lt_mul_of_pos_left hb' hp
      nlinarith
  have hrad : ((1 + (s : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : 0 < 1 + (s : ℝ)))
  have he' : Circle.exp u = Circle.exp v := by
    apply Subtype.ext
    exact mul_left_cancel₀ hrad he
  have heq := Circle.exp_injOn_Icc hspan
    (show u ∈ Icc u v from ⟨le_rfl,huv.le⟩)
    (show v ∈ Icc u v from ⟨huv.le,le_rfl⟩) he'
  exact (ne_of_lt huv) heq

/-- An annular connector meets the closed unit disk only at its source. -/
lemma annularConnector_disk {a b : ℝ} {z : ℂ}
    (hz : z ∈ range (annularConnector a b)) (hn : ‖z‖ ≤ 1) :
    z = (Circle.exp a : ℂ) := by
  rcases hz with ⟨t,rfl⟩
  rw [norm_annularConnector] at hn
  have ht : t = 0 := Subtype.ext (by change (t : ℝ) = 0; linarith [t.2.1])
  subst t
  exact (annularConnector a b).source

lemma annularConnector_disjoint_disk {a b : ℝ} {S : Set ℂ}
    (hS : ∀ z ∈ S, ‖z‖ ≤ 1) (ha : (Circle.exp a : ℂ) ∉ S) :
    Disjoint (range (annularConnector a b)) S := by
  rw [Set.disjoint_left]
  intro z hz hzS
  exact ha ((annularConnector_disk hz (hS z hzS)) ▸ hzS)

lemma annular_extension_bound {a c : ℝ}
    (p : Path (Circle.exp a : ℂ) (Circle.exp c : ℂ))
    (hp : ∀ t, ‖p t‖ ≤ 1) (b d : ℝ) :
    ∀ t, ‖((annularConnector a b).symm.trans
      (p.trans (annularConnector c d))) t‖ ≤ 2 := by
  intro t
  have hm := Set.mem_range_self
    (f := ((annularConnector a b).symm.trans (p.trans (annularConnector c d)))) t
  rw [Path.trans_range, Path.symm_range, Path.trans_range] at hm
  rcases hm with hm | hm | hm
  · rcases hm with ⟨s,hs⟩
    rw [← hs, norm_annularConnector]
    linarith [s.2.2]
  · rcases hm with ⟨s,hs⟩
    rw [← hs]
    exact (hp s).trans (by norm_num)
  · rcases hm with ⟨s,hs⟩
    rw [← hs, norm_annularConnector]
    linarith [s.2.2]

/-- Arbitrary four boundary endpoints in strict cyclic order, with no
  injectivity requirement on either of the two disk paths. -/
lemma disk_cyclic_arcs_meet (a₀ a₁ a₂ a₃ : ℝ)
    (h₀₁ : a₀ < a₁) (h₁₂ : a₁ < a₂) (h₂₃ : a₂ < a₃)
    (hspan : a₃ < a₀ + 2 * π)
    (f : Path (Circle.exp a₀ : ℂ) (Circle.exp a₂ : ℂ))
    (g : Path (Circle.exp a₁ : ℂ) (Circle.exp a₃ : ℂ))
    (hf : ∀ s, ‖f s‖ ≤ 1) (hg : ∀ s, ‖g s‖ ≤ 1) :
    ∃ s t, f s = g t := by
  by_contra! hn
  have hfg : Disjoint (range f) (range g) := by
    rw [Set.disjoint_left]
    rintro z ⟨s,rfl⟩ ⟨t,ht⟩
    exact hn s t ht.symm
  let q₀ := annularConnector a₀ (-π)
  let q₁ := annularConnector a₁ (-π/2)
  let q₂ := annularConnector a₂ 0
  let q₃ := annularConnector a₃ (π/2)
  have hq₀₁ : Disjoint (range q₀) (range q₁) := by
    apply annularConnector_disjoint h₀₁ <;> linarith [Real.pi_pos]
  have hq₀₃ : Disjoint (range q₀) (range q₃) := by
    apply annularConnector_disjoint <;> linarith [Real.pi_pos]
  have hq₂₁ : Disjoint (range q₂) (range q₁) := by
    apply Disjoint.symm
    apply annularConnector_disjoint h₁₂ <;> linarith [Real.pi_pos]
  have hq₂₃ : Disjoint (range q₂) (range q₃) := by
    apply annularConnector_disjoint h₂₃ <;> linarith [Real.pi_pos]
  have hfg₀ : (Circle.exp a₀ : ℂ) ∉ range g := by
    exact fun hm => Set.disjoint_left.mp hfg f.source_mem_range hm
  have hfg₂ : (Circle.exp a₂ : ℂ) ∉ range g := by
    exact fun hm => Set.disjoint_left.mp hfg f.target_mem_range hm
  have hgf₁ : (Circle.exp a₁ : ℂ) ∉ range f := by
    exact fun hm => Set.disjoint_left.mp hfg hm g.source_mem_range
  have hgf₃ : (Circle.exp a₃ : ℂ) ∉ range f := by
    exact fun hm => Set.disjoint_left.mp hfg hm g.target_mem_range
  have hf' : ∀ z ∈ range f, ‖z‖ ≤ 1 := by rintro z ⟨s,rfl⟩; exact hf s
  have hg' : ∀ z ∈ range g, ‖z‖ ≤ 1 := by rintro z ⟨s,rfl⟩; exact hg s
  have hq₀g := annularConnector_disjoint_disk (b := -π) hg' hfg₀
  have hq₂g := annularConnector_disjoint_disk (b := 0) hg' hfg₂
  have hfq₁ := (annularConnector_disjoint_disk (b := -π/2) hf' hgf₁).symm
  have hfq₃ := (annularConnector_disjoint_disk (b := π/2) hf' hgf₃).symm
  let F := q₀.symm.trans (f.trans q₂)
  let G := q₁.symm.trans (g.trans q₃)
  have hFG : Disjoint (range F) (range G) := by
    simp only [F,G,Path.trans_range,Path.symm_range,
      Set.disjoint_union_left,Set.disjoint_union_right]
    exact ⟨⟨hq₀₁,hfq₁,hq₂₁⟩,⟨hq₀g,hfg,hq₂g⟩,hq₀₃,hfq₃,hq₂₃⟩
  let F' : C(unitInterval, ℂ) := ⟨fun s => F s / 2,by fun_prop⟩
  let G' : C(unitInterval, ℂ) := ⟨fun t => G t / 2,by fun_prop⟩
  have hF : ∀ s, ‖F' s‖ ≤ 1 := by
    intro s
    change ‖F s / 2‖ ≤ 1
    rw [norm_div, Complex.norm_ofNat]
    exact (div_le_one (by norm_num)).mpr (annular_extension_bound f hf (-π) 0 s)
  have hG : ∀ s, ‖G' s‖ ≤ 1 := by
    intro s
    change ‖G s / 2‖ ≤ 1
    rw [norm_div, Complex.norm_ofNat]
    exact (div_le_one (by norm_num)).mpr
      (annular_extension_bound g hg (-π/2) (π/2) s)
  have hF₀ : F' 0 = -1 := by
    change F 0 / 2 = -1
    rw [F.source]
    simp [Circle.coe_exp]
  have hF₁ : F' 1 = 1 := by
    change F 1 / 2 = 1
    rw [F.target]
    simp
  have hG₀ : G' 0 = -Complex.I := by
    change G 0 / 2 = -Complex.I
    rw [G.source]
    simp only [Circle.coe_exp, Complex.ofReal_div, Complex.ofReal_neg,
      Complex.ofReal_ofNat, Complex.exp_neg_pi_div_two_mul_I]
    ring
  have hG₁ : G' 1 = Complex.I := by
    change G 1 / 2 = Complex.I
    rw [G.target]
    simp [Circle.coe_exp, Complex.exp_pi_div_two_mul_I]
  obtain ⟨s,t,hst⟩ := disk_opposite_arcs_meet F' G' hF hG hF₀ hF₁ hG₀ hG₁
  have he : F s = G t := (div_left_inj' (by norm_num : (2 : ℂ) ≠ 0)).mp hst
  exact Set.disjoint_left.mp hFG (Set.mem_range_self s) (he ▸ Set.mem_range_self t)

/-- Disjoint disk arcs with cyclically ordered boundary positions give exactly
  the combinatorial noncrossing relation used by column models. This is the
  final step of the complementary-disk argument. -/
lemma noncrossing_of_disk_arcs {n : ℕ} (G : SimpleGraph (Fin n))
    (angle : Fin n → ℝ) (horder : StrictMono angle)
    (hspan : ∀ i j, angle j - angle i < 2 * π)
    (arc : ∀ i j, G.Adj i j → Path (Circle.exp (angle i) : ℂ)
      (Circle.exp (angle j) : ℂ))
    (hdisk : ∀ i j h t, ‖arc i j h t‖ ≤ 1)
    (hdisjoint : ∀ i j h k l h', i ≠ k → i ≠ l → j ≠ k → j ≠ l →
      Disjoint (range (arc i j h)) (range (arc k l h'))) :
    PlanarL1.ColumnOrder.Noncrossing G := by
  intro a b c d hab hbc hcd h
  obtain ⟨s,t,hst⟩ := disk_cyclic_arcs_meet
    (angle a) (angle b) (angle c) (angle d)
    (horder hab) (horder hbc) (horder hcd) (by linarith [hspan a d])
    (arc a c h.1) (arc b d h.2) (hdisk a c h.1) (hdisk b d h.2)
  have hd := hdisjoint a c h.1 b d h.2 (ne_of_lt hab)
    (ne_of_lt (hab.trans (hbc.trans hcd))) (ne_of_gt hbc) (ne_of_lt hcd)
  exact Set.disjoint_left.mp hd (Set.mem_range_self s) (hst ▸ Set.mem_range_self t)

end PlanarL1.Topology



end

end OAI
