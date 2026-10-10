import OAI.Combinatorics.HalvingLines.SeparatedWindows

namespace OAI

open Filter Topology

namespace PlanarHalving.Zoom
open Set

noncomputable def columnMap (u v : Point) : Point →L[ℝ] Point :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight u + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight v

@[simp] lemma columnMap_apply (u v x : Point) : columnMap u v x=x.1 • u+x.2 • v := rfl

noncomputable def columnEquiv (u v : Point) (h : detPair u v ≠ 0) : Point ≃L[ℝ] Point :=
  ContinuousLinearEquiv.ofBijective (columnMap u v)
    (LinearMap.ker_eq_bot.mpr (by
      intro x y hxy
      have he : (x.1-y.1) • u=(y.2-x.2) • v := by
        dsimp [columnMap] at hxy
        rw [sub_smul,sub_smul]
        linear_combination hxy
      have hz := parallel_scalars_zero u v h _ _ he
      exact Prod.ext (sub_eq_zero.mp hz.1) (sub_eq_zero.mp hz.2).symm))
    (LinearMap.range_eq_top.mpr (by
      intro x
      obtain ⟨a,b,hab⟩ := plane_span u v h x
      exact ⟨(a,b),hab.symm⟩))

@[simp] lemma columnEquiv_apply (u v : Point) (h : detPair u v ≠ 0) (x : Point) :
    columnEquiv u v h x=x.1 • u+x.2 • v := rfl

lemma detPair_smul (u v : Point) (a b : ℝ) :
    detPair (a • u) (b • v)=a*b*detPair u v := by
  dsimp [detPair]; ring

lemma three_frame (u v w : Point) (huv : detPair u v ≠ 0)
    (huw : detPair u w ≠ 0) (hwv : detPair w v ≠ 0) :
    ∃ (E : Point ≃L[ℝ] Point) (a b : ℝ), a≠0 ∧ b≠0 ∧
      E (1,0)=a • u ∧ E (0,1)=b • v ∧ E (1,1)=w := by
  obtain ⟨a,b,he⟩ := plane_span u v huv w
  have ha : a≠0 := by
    intro ha
    rw [ha,zero_smul,zero_add] at he
    apply hwv
    rw [he]
    dsimp [detPair]; ring
  have hb : b≠0 := by
    intro hb
    rw [hb,zero_smul,add_zero] at he
    apply huw
    rw [he]
    dsimp [detPair]; ring
  have hab : detPair (a • u) (b • v) ≠ 0 := by
    rw [detPair_smul]; exact mul_ne_zero (mul_ne_zero ha hb) huv
  refine ⟨columnEquiv (a • u) (b • v) hab,a,b,ha,hb,?_,?_,?_⟩
  · simp
  · simp
  · simpa using he.symm

lemma slope_frame {s₁ s₂ s₃ : ℝ} (h12 : s₁<s₂) (h23 : s₂<s₃) :
    ∃ (E : Point ≃L[ℝ] Point) (a b : ℝ), 0<a ∧ 0<b ∧
      E (1,0)=a • (1,s₁) ∧ E (0,1)=b • (1,s₃) ∧ E (1,1)=(1,s₂) := by
  let a := (s₃-s₂)/(s₃-s₁)
  let b := (s₂-s₁)/(s₃-s₁)
  have hden : 0<s₃-s₁ := sub_pos.mpr (h12.trans h23)
  have ha : 0<a := div_pos (sub_pos.mpr h23) hden
  have hb : 0<b := div_pos (sub_pos.mpr h12) hden
  have he : a • ((1,s₁) : Point)+b • ((1,s₃) : Point)=((1,s₂) : Point) := by
    ext <;> dsimp [a,b] <;> field_simp [hden.ne'] <;> ring
  have hdet : detPair (a • (1,s₁)) (b • (1,s₃)) ≠ 0 := by
    rw [detPair_smul]
    exact mul_ne_zero (mul_ne_zero ha.ne' hb.ne') (by simpa [detPair] using hden.ne')
  refine ⟨columnEquiv _ _ hdet,a,b,ha,hb,?_,?_,?_⟩
  · simp
  · simp
  · simpa using he

end PlanarHalving.Zoom

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

noncomputable def affineHomeomorph (p : Point) (q : ℝ) (hq : q≠0)
    (E : Point ≃L[ℝ] Point) : Point ≃ₜ Point where
  toFun x := p+q • E x
  invFun y := E.symm (q⁻¹ • (y-p))
  left_inv x := by simp only [add_sub_cancel_left,smul_smul,inv_mul_cancel₀ hq,one_smul,E.symm_apply_apply]
  right_inv y := by
    dsimp only
    rw [E.apply_symm_apply,smul_smul,mul_inv_cancel₀ hq,one_smul]
    abel
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] lemma affineHomeomorph_apply (p : Point) (q : ℝ) (hq : q≠0)
    (E : Point ≃L[ℝ] Point) (x : Point) : affineHomeomorph p q hq E x=p+q • E x := rfl

@[simp] lemma affineHomeomorph_symm_apply (p : Point) (q : ℝ) (hq : q≠0)
    (E : Point ≃L[ℝ] Point) (y : Point) : (affineHomeomorph p q hq E).symm y=E.symm (q⁻¹ • (y-p)) := rfl

noncomputable def affineZoom (f : OpenPartialHomeomorph Point Point)
    (E B : Point ≃L[ℝ] Point) (p x₀ : Point) (q h : ℝ) (hq : q≠0) (hh : h≠0) :
    OpenPartialHomeomorph Point Point :=
  ((affineHomeomorph x₀ q hq E).transOpenPartialHomeomorph f).transHomeomorph
    (affineHomeomorph p h hh B.symm).symm

@[simp] lemma affineZoom_apply (f : OpenPartialHomeomorph Point Point)
    (E B : Point ≃L[ℝ] Point) (p x₀ : Point) (q h : ℝ) (hq : q≠0) (hh : h≠0) (x : Point) :
    affineZoom f E B p x₀ q h hq hh x=B (h⁻¹ • (f (x₀+q • E x)-p)) := rfl

lemma affineZoom_source (f : OpenPartialHomeomorph Point Point) (hs : f.source=univ)
    (E B : Point ≃L[ℝ] Point) (p x₀ : Point) (q h : ℝ) (hq : q≠0) (hh : h≠0) :
    (affineZoom f E B p x₀ q h hq hh).source=univ := by
  ext x
  change (x₀+q • E x∈f.source) ↔ x∈univ
  rw [hs]; simp

@[simp] lemma affineZoom_target (f : OpenPartialHomeomorph Point Point)
    (E B : Point ≃L[ℝ] Point) (p x₀ : Point) (q h : ℝ) (hq : q≠0) (hh : h≠0) :
    (affineZoom f E B p x₀ q h hq hh).target={w | p+h • B.symm w∈f.target} := rfl

lemma affineZoom_zero (f : OpenPartialHomeomorph Point Point)
    (E B : Point ≃L[ℝ] Point) {p : Point} (hp : p∈f.target)
    (q h : ℝ) (hq : q≠0) (hh : h≠0) :
    affineZoom f E B p (f.symm p) q h hq hh 0=0 := by
  simp [f.right_inv hp]

lemma affineZoom_exhaust (f : ℕ → OpenPartialHomeomorph Point Point)
    (E : ℕ → Point ≃L[ℝ] Point) (B : Point ≃L[ℝ] Point) (p : Point)
    (x₀ : ℕ → Point) (q h : ℕ → ℝ) (hq : ∀ n, q n≠0) (hh : ∀ n, h n≠0)
    (U : Set Point) (hU : IsOpen U) (hp : p∈U) (hUt : ∀ n, U ⊆ (f n).target)
    (hlim : Tendsto h atTop (𝓝 0)) (K : Set Point) (hK : IsCompact K) :
    ∀ᶠ n in atTop, K ⊆ (affineZoom (f n) (E n) B p (x₀ n) (q n) (h n) (hq n) (hh n)).target := by
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Point)).mp
    ((hK.image B.symm.continuous).isBounded)
  have ht : Tendsto (fun n => |h n| * max R 0) atTop (𝓝 0) := by
    simpa using hlim.abs.mul_const (max R 0)
  filter_upwards [ht.eventually (gt_mem_nhds hr)] with n hn w hw
  change p+h n • B.symm w ∈ (f n).target
  apply hUt n
  apply hrsub
  rw [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs]
  have hw' : ‖B.symm w‖ ≤ max R 0 := by
    apply le_trans _ (le_max_left _ _)
    simpa using hR (mem_image_of_mem _ hw)
  exact (mul_le_mul_of_nonneg_left hw' (abs_nonneg _)).trans_lt hn

lemma affineZoom_normalizing_scale (f : OpenPartialHomeomorph Point Point) (hs : f.source=univ)
    (E B : Point ≃L[ℝ] Point) {p : Point} (hp : p∈f.target)
    (h : ℝ) (hh : h≠0)
    (hball : closedBall (0:Point) 1 ⊆ {w | p+h • B.symm w∈f.target}) :
    ∃ q : ℝ, ∃ hq : 0<q, ‖affineZoom f E B p (f.symm p) q h hq.ne' hh (1,0)‖=1 := by
  let F := affineZoom f E B p (f.symm p) 1 h one_ne_zero hh
  have hF0 : F 0=0 := affineZoom_zero f E B hp 1 h one_ne_zero hh
  have hFs : F.source=univ := affineZoom_source f hs E B p (f.symm p) 1 h one_ne_zero hh
  have hFt : (0:Point)∈F.target := by
    apply hball
    simp
  obtain ⟨q,hq,hqe⟩ := Directions.ray_exit_at_radius F hFs hFt
    (v:=(1,0)) (by norm_num) (by norm_num : (0:ℝ)<1) hball
  have hfInv : F.symm 0=0 := by
    have hi := F.left_inv (show (0:Point) ∈ F.source by rw [hFs]; trivial)
    simpa only [hF0] using hi
  rw [hfInv,zero_add,dist_zero_right] at hqe
  have hqp : 0<q := lt_of_le_of_ne hq (by
    intro he
    rw [← he,zero_smul,hF0,norm_zero] at hqe
    norm_num at hqe)
  refine ⟨q,hqp,?_⟩
  simpa only [F,affineZoom_apply,map_smul,one_smul] using hqe

end PlanarHalving.Zoom

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates Zoom
open scoped Topology unitInterval

lemma affine_rank_monotone (F : Configuration) {A B : Window}
    (hAB : Before A B) (hA : 0 < length F.R A) (hB : 0 < length F.R B)
    (E B' : Point ≃L[ℝ] Point) (p x₀ : Point) (q h : ℝ) (hq : 0<q) (hh : 0<h)
    (v : Point) (t : I) (htA : t ≤ lower A) (htB : t ≤ lower B)
    (s : ℝ) (hs : 0 ≤ s) (hE : E v=s • (1,F.timeSlope t)) (x : Point) :
    Monotone (fun r : ℝ =>
      ((B'.symm.trans reflectFirst) (affineZoom (F.rankChart hAB hA hB) E B' p x₀ q h hq.ne' hh.ne' (x+r • v))).1) ∧
    Monotone (fun r : ℝ =>
      ((B'.symm.trans reflectFirst) (affineZoom (F.rankChart hAB hA hB) E B' p x₀ q h hq.ne' hh.ne' (x+r • v))).2) := by
  have harg (r : ℝ) : x₀+q • E (x+r • v)=(x₀+q • E x)+(q*r*s) • (1,F.timeSlope t) := by
    rw [map_add,map_smul,hE,smul_add,smul_smul,smul_smul]
    simp only [mul_assoc,add_assoc]
  have h₁ := F.rank_forward_before hA htA (x₀+q • E x)
  have h₂ := F.rank_forward_before hB htB (x₀+q • E x)
  have hsc : Monotone (fun r : ℝ => q*r*s) := fun a b hab =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hab hq.le) hs
  constructor
  · intro a b hab
    simp only [affineZoom_apply,ContinuousLinearEquiv.trans_apply,B'.symm_apply_apply,
      reflectFirst_apply,F.rankChart_apply]
    change -(h⁻¹*((F.system.labels F.generic (x₀+q • E (x+a • v)) A : ℝ)-p.1)) ≤
      -(h⁻¹*((F.system.labels F.generic (x₀+q • E (x+b • v)) A : ℝ)-p.1))
    rw [harg,harg]
    exact neg_le_neg (mul_le_mul_of_nonneg_left (sub_le_sub_right (h₁ (hsc hab)) _) (inv_nonneg.mpr hh.le))
  · intro a b hab
    simp only [affineZoom_apply,ContinuousLinearEquiv.trans_apply,B'.symm_apply_apply,
      reflectFirst_apply,F.rankChart_apply]
    change h⁻¹*(-(F.system.labels F.generic (x₀+q • E (x+a • v)) B : ℝ)-p.2) ≤
      h⁻¹*(-(F.system.labels F.generic (x₀+q • E (x+b • v)) B : ℝ)-p.2)
    rw [harg,harg]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right (neg_le_neg (h₂ (hsc hab))) _) (inv_nonneg.mpr hh.le)

lemma affine_rank_direction {ι : Type*} (F : ℕ → Configuration) {A B : Window}
    (hAB : Before A B) (hA : ∀ n, 0 < length (F n).R A)
    (hB : ∀ n, 0 < length (F n).R B) (C : ι → Window)
    (hCB : ∀ i, Before (C i) A ∧ Before (C i) B)
    (hC : ∀ i, ∀ᶠ n in atTop, 0 < length (F n).R (C i))
    (D : ι → Point →L[ℝ] ℝ) (c : ι → ℝ) (p : Point)
    (h q : ℕ → ℝ) (hh : ∀ n, 0<h n) (hq : ∀ n, 0<q n)
    (E : ℕ → Point ≃L[ℝ] Point) (B' : Point ≃L[ℝ] Point) (x₀ : ℕ → Point)
    (t : I) (htA : t ≤ lower A) (htB : t ≤ lower B) (z : ℝ)
    (hz : Directions.allowed reflectFirst D
      (fun i => (lower (C i) : ℝ)) (fun i => (upper (C i) : ℝ)) t = {z})
    (v w : Point) (s : ℕ → ℝ) (d : ℝ)
    (hE : ∀ n, E n v=s n • (1,(F n).timeSlope t))
    (hB' : B' (reflectFirst (Directions.simplex z))=d • w)
    (hj : ∀ i R, 0 ≤ R → TendstoUniformlyOn
      (fun n u => (((F n).extendedRank true A B (C i) (p+h n • u) : ℝ)-c i)/h n)
      (D i) atTop (closedBall 0 R)) :
    DirectionalLimit (fun n => affineZoom ((F n).rankChart hAB (hA n) (hB n))
      (E n) B' p (x₀ n) (q n) (h n) (hq n).ne' (hh n).ne') v w := by
  intro ρ hρ x y hxy a b ha hb
  choose r hr using hxy
  let X := fun n => x₀ (ρ n)+q (ρ n) • E (ρ n) (x n)
  let Y := fun n => x₀ (ρ n)+q (ρ n) • E (ρ n) (y n)
  have hXY (n : ℕ) : Y n=X n+(q (ρ n)*r n*s (ρ n)) • (1,(F (ρ n)).timeSlope t) := by
    dsimp only [X,Y]
    rw [hr,map_add,map_smul,hE,smul_add,smul_smul,smul_smul]
    simp only [mul_assoc,add_assoc]
  have hxa : Tendsto (fun n => (h (ρ n))⁻¹ •
      ((F (ρ n)).rankChart hAB (hA (ρ n)) (hB (ρ n)) (X n)-p)) atTop (𝓝 (B'.symm a)) := by
    have hv := (B'.symm.continuous.tendsto a).comp ha
    simpa only [Function.comp_def,affineZoom_apply,B'.symm_apply_apply,X,Y] using hv
  have hyb : Tendsto (fun n => (h (ρ n))⁻¹ •
      ((F (ρ n)).rankChart hAB (hA (ρ n)) (hB (ρ n)) (Y n)-p)) atTop (𝓝 (B'.symm b)) := by
    have hv := (B'.symm.continuous.tendsto b).comp hb
    simpa only [Function.comp_def,affineZoom_apply,B'.symm_apply_apply,X,Y] using hv
  have hj' (i : ι) (R : ℝ) (hR : 0 ≤ R) : TendstoUniformlyOn
      (fun n u => (((F (ρ n)).extendedRank true A B (C i) (p+h (ρ n) • u) : ℝ)-c i)/h (ρ n))
      (D i) atTop (closedBall 0 R) := (hj i R hR).seq_tendstoUniformlyOn ρ hρ.tendsto_atTop
  obtain ⟨e,he⟩ := actual_unoriented_limit (F ∘ ρ) hAB (fun n => hA (ρ n)) (fun n => hB (ρ n)) C
    (fun i => hρ.tendsto_atTop.eventually (hC i)) D c p (h ∘ ρ) (fun n => hh (ρ n))
    t htA htB z hz X Y (fun n => q (ρ n)*r n*s (ρ n)) hXY (B'.symm a) (B'.symm b) hxa hyb
    (fun i => jet_at_physical (F ∘ ρ) hAB (hCB i) (fun n => hA (ρ n)) (fun n => hB (ρ n))
      (hρ.tendsto_atTop.eventually (hC i)) (D i) (c i) p (h ∘ ρ) (fun n => hh (ρ n)) (hj' i) X (B'.symm a) hxa)
    (fun i => jet_at_physical (F ∘ ρ) hAB (hCB i) (fun n => hA (ρ n)) (fun n => hB (ρ n))
      (hρ.tendsto_atTop.eventually (hC i)) (D i) (c i) p (h ∘ ρ) (fun n => hh (ρ n)) (hj' i) Y (B'.symm b) hyb)
  have he' := congrArg B' he
  simp only [map_sub,map_smul,B'.apply_symm_apply,hB',smul_smul] at he'
  exact ⟨e*d,he'⟩

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates Zoom
open scoped Topology unitInterval

lemma actual_zoom_compactness {ι : Type*} (F : ℕ → Configuration) {A B : Window}
    (hAB : Before A B) (hA : ∀ n, 0 < length (F n).R A)
    (hB : ∀ n, 0 < length (F n).R B) (C : ι → Window)
    (hCB : ∀ i, Before (C i) A ∧ Before (C i) B)
    (hC : ∀ i, ∀ᶠ n in atTop, 0 < length (F n).R (C i))
    (D : ι → Point →L[ℝ] ℝ) (c : ι → ℝ) (p : Point)
    (hp : p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (h q : ℕ → ℝ) (hh : ∀ n, 0<h n) (hq : ∀ n, 0<q n)
    (hlim : Tendsto h atTop (𝓝 0))
    (E : ℕ → Point ≃L[ℝ] Point) (B' : Point ≃L[ℝ] Point)
    (t : Foliation → I) (htA : ∀ i, t i ≤ lower A) (htB : ∀ i, t i ≤ lower B)
    (z : Foliation → ℝ)
    (hz : ∀ j, Directions.allowed reflectFirst D
      (fun i => (lower (C i) : ℝ)) (fun i => (upper (C i) : ℝ)) (t j) = {z j})
    (s : ℕ → Foliation → ℝ) (hs : ∀ n i, 0 ≤ s n i) (d : Foliation → ℝ)
    (hE : ∀ n i, E n i.direction=s n i • (1,(F n).timeSlope (t i)))
    (hB' : ∀ i, B' (reflectFirst (Directions.simplex (z i)))=d i • i.direction)
    (hj : ∀ i R, 0 ≤ R → TendstoUniformlyOn
      (fun n u => (((F n).extendedRank true A B (C i) (p+h n • u) : ℝ)-c i)/h n)
      (D i) atTop (closedBall 0 R))
    (hone : ∀ n, ‖affineZoom ((F n).rankChart hAB (hA n) (hB n)) (E n) B' p
      (((F n).rankChart hAB (hA n) (hB n)).symm p) (q n) (h n) (hq n).ne' (hh n).ne' (1,0)‖=1) :
    ∃ (ρ : ℕ → ℕ), StrictMono ρ ∧ ∃ sgn : ℝ, (sgn = 1 ∨ sgn = -1) ∧
      (∀ K : Set Point, IsCompact K → TendstoUniformlyOn
        (fun n => affineZoom ((F (ρ n)).rankChart hAB (hA (ρ n)) (hB (ρ n))) (E (ρ n)) B' p
          (((F (ρ n)).rankChart hAB (hA (ρ n)) (hB (ρ n))).symm p)
          (q (ρ n)) (h (ρ n)) (hq (ρ n)).ne' (hh (ρ n)).ne')
        (fun x => sgn • x) atTop K) ∧
      (∀ K : Set Point, IsCompact K → TendstoUniformlyOn
        (fun n => (affineZoom ((F (ρ n)).rankChart hAB (hA (ρ n)) (hB (ρ n))) (E (ρ n)) B' p
          (((F (ρ n)).rankChart hAB (hA (ρ n)) (hB (ρ n))).symm p)
          (q (ρ n)) (h (ρ n)) (hq (ρ n)).ne' (hh (ρ n)).ne').symm)
        (fun x => sgn • x) atTop K) := by
  let f := fun n => (F n).rankChart hAB (hA n) (hB n)
  let x₀ := fun n => (f n).symm p
  let Z := fun n => affineZoom (f n) (E n) B' p (x₀ n) (q n) (h n) (hq n).ne' (hh n).ne'
  have hsrc (n : ℕ) : (Z n).source=univ :=
    affineZoom_source (f n) ((F n).rankChart_source hAB (hA n) (hB n)) _ _ _ _ _ _ _ _
  have hpt (n : ℕ) : p∈(f n).target := by
    rw [(F n).rankChart_target]; exact hp
  let S : FoliatedSequence := {
    map := Z
    source := hsrc
    exhaust := affineZoom_exhaust f E B' p x₀ q h (fun n => (hq n).ne') (fun n => (hh n).ne')
      (Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0) (isOpen_Ioo.prod isOpen_Ioo) hp
      (fun n => by rw [(F n).rankChart_target]) hlim
    control i := LineControl.of_monotone Z hsrc i.direction i.direction_ne_zero (B'.symm.trans reflectFirst)
      (fun n x => (affine_rank_monotone (F n) hAB (hA n) (hB n) (E n) B' p (x₀ n)
        (q n) (h n) (hq n) (hh n) i.direction (t i) (htA i) (htB i) (s n i) (hs n i) (hE n i) x).1)
      (fun n x => (affine_rank_monotone (F n) hAB (hA n) (hB n) (E n) B' p (x₀ n)
        (q n) (h n) (hq n) (hh n) i.direction (t i) (htA i) (htB i) (s n i) (hs n i) (hE n i) x).2)
    direction i := affine_rank_direction F hAB hA hB C hCB hC D c p h q hh hq E B' x₀
      (t i) (htA i) (htB i) (z i) (hz i) i.direction i.direction (fun n => s n i) (d i)
      (fun n => hE n i) (hB' i) hj }
  exact S.normalized_compactness (fun n => affineZoom_zero (f n) (E n) B' (hpt n) _ _ _ _) hone

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates Zoom
open scoped Topology unitInterval

lemma timeSlope_eventually_lt (F : ℕ → Configuration)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) {s t : I} (hst : s<t) :
    ∀ᶠ n in atTop, (F n).timeSlope s < (F n).timeSlope t := by
  have hst' : 0<(t:ℝ)-s := sub_pos.mpr hst
  have htR : Tendsto (fun n => ((F n).R:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hR
  filter_upwards [htR.eventually_gt_atTop (2/((t:ℝ)-s))] with n hn
  apply (F n).system.increasing
  have hs := (abs_le.mp (cut_time_error (F n).R s)).2
  have ht := (abs_le.mp (cut_time_error (F n).R t)).1
  have hp := (div_lt_iff₀ hst').mp hn
  have hc : (cut (time (F n).R) s : ℝ)<(cut (time (F n).R) t : ℝ) := by nlinarith
  exact_mod_cast hc

def foliationTriple {α : Type*} (a b c : α) : Foliation → α
  | .horizontal => a
  | .vertical => c
  | .diagonal => b

lemma positive_slope_frames (F : ℕ → Configuration) (t₁ t₂ t₃ : I)
    (h12 : ∀ n, (F n).timeSlope t₁ < (F n).timeSlope t₂)
    (h23 : ∀ n, (F n).timeSlope t₂ < (F n).timeSlope t₃) :
    ∃ (E : ℕ → Point ≃L[ℝ] Point) (s : ℕ → Foliation → ℝ),
      (∀ n i, 0<s n i) ∧ ∀ n i,
        E n i.direction=s n i • (1,(F n).timeSlope (foliationTriple t₁ t₂ t₃ i)) := by
  choose E a b ha hb hE1 hE2 hE3 using fun n => slope_frame (h12 n) (h23 n)
  refine ⟨E,fun n => foliationTriple (a n) 1 (b n),?_,?_⟩
  · intro n i; cases i <;> simp only [foliationTriple] <;> first | exact ha n | exact hb n | norm_num
  · intro n i; cases i
    · exact hE1 n
    · exact hE2 n
    · simpa only [one_smul,foliationTriple,Foliation.direction] using hE3 n

lemma singleton_target_frame (z₁ z₂ z₃ : ℝ)
    (h12 : z₁≠z₂) (h23 : z₂≠z₃) (h13 : z₁≠z₃) :
    ∃ (B : Point ≃L[ℝ] Point) (d : Foliation → ℝ),
      (∀ i, d i≠0) ∧ ∀ i,
        B (reflectFirst (Directions.simplex (foliationTriple z₁ z₂ z₃ i)))=d i • i.direction := by
  let u := fun z => reflectFirst (Directions.simplex z)
  have hd (a b : ℝ) : detPair (u a) (u b)=b-a := by
    dsimp [u,detPair,Directions.simplex]; ring
  obtain ⟨E,a,b,ha,hb,hE1,hE2,hE3⟩ := three_frame (u z₁) (u z₃) (u z₂)
    (by rw [hd]; exact sub_ne_zero.mpr h13.symm)
    (by rw [hd]; exact sub_ne_zero.mpr h12.symm)
    (by rw [hd]; exact sub_ne_zero.mpr h23.symm)
  refine ⟨E.symm,foliationTriple a⁻¹ 1 b⁻¹,?_,?_⟩
  · intro i; cases i <;> simp only [foliationTriple] <;> first | exact inv_ne_zero ha | exact inv_ne_zero hb | norm_num
  · intro i
    cases i
    · change E.symm (u z₁)=a⁻¹ • (1,0)
      apply E.injective
      rw [E.apply_symm_apply,map_smul,hE1,smul_smul,inv_mul_cancel₀ ha,one_smul]
    · change E.symm (u z₃)=b⁻¹ • (0,1)
      apply E.injective
      rw [E.apply_symm_apply,map_smul,hE2,smul_smul,inv_mul_cancel₀ hb,one_smul]
    · change E.symm (u z₂)=1 • (1,1)
      rw [one_smul]
      apply E.injective
      rw [E.apply_symm_apply,hE3]

end PlanarHalving.RankLimits

end OAI
