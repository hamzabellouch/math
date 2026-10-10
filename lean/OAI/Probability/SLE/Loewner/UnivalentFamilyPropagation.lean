import OAI.Probability.SLE.Loewner.UnivalentLocalBound
import OAI.Probability.SLE.Geometry.HolomorphicFamilyCompactness

namespace OAI

/-! A local bound for an injective holomorphic family propagates throughout
 the half-plane. Only the coarse, proved Bloch bound is used. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

def familyBoundedLocus (f : ℕ → ℂ → ℂ) : Set ℂ :=
  {z | ∃ r : ℝ, 0<r ∧ ∃ C : ℝ, ∀ n, ∀ w∈ball z r, ‖f n w‖≤C}

lemma isOpen_familyBoundedLocus (f : ℕ → ℂ → ℂ) : IsOpen (familyBoundedLocus f) := by
  apply Metric.isOpen_iff.mpr
  rintro z ⟨r,hr,C,hC⟩
  refine ⟨r/2,by positivity,?_⟩
  intro w hw
  refine ⟨r/2,by positivity,C,fun n v hv => hC n v ?_⟩
  have h := dist_triangle v w z
  rw [mem_ball] at hw hv ⊢
  linarith

lemma univalent_family_enlarged_bound
    (f : ℕ → ℂ → ℂ) (hf : ∀ n, DifferentiableOn ℂ (f n) upperHalfPlane)
    (hi : ∀ n, InjOn (f n) upperHalfPlane) {z : ℂ} (hz : z∈upperHalfPlane)
    (hb : z∈familyBoundedLocus f) :
    ∃ B : ℝ, ∀ n, ∀ w∈ball z (z.im/(2*(128*Real.pi)^2)), ‖f n w‖≤B := by
  obtain ⟨r,hr,C,hC⟩ := hb
  let t := min (r/2) (z.im/2)
  have ht : 0<t := lt_min (half_pos hr) (half_pos hz)
  have htr : t<r := (min_le_left _ _).trans_lt (by linarith)
  have htH : closedBall z t ⊆ upperHalfPlane := by
    intro w hw
    have him := Complex.abs_im_le_norm (w-z)
    have hd : ‖w-z‖≤t := by simpa only [mem_closedBall,dist_eq_norm] using hw
    have htz : t≤z.im/2 := min_le_right _ _
    rw [Complex.sub_im] at him
    change 0<w.im
    have := (abs_le.mp (him.trans hd)).1
    linarith
  have hder (n : ℕ) : ‖deriv (f n) z‖≤C/t := by
    rw [← Complex.cderiv_eq_deriv isOpen_upperHalfPlane (hf n) ht htH]
    apply Complex.norm_cderiv_le ht
    intro w hw
    apply hC n w
    exact mem_ball.mpr ((mem_sphere.mp hw).trans_lt htr)
  let R := z.im/2
  have hR : 0<R := half_pos hz
  have hRH : ball z R ⊆ upperHalfPlane := by
    intro w hw
    have him := Complex.abs_im_le_norm (w-z)
    have hd : ‖w-z‖<R := by simpa only [mem_ball,dist_eq_norm] using hw
    rw [Complex.sub_im] at him
    change 0<w.im
    have := (abs_le.mp (him.trans hd.le)).1
    dsimp [R] at *
    linarith
  refine ⟨R*(C/t)/(128*Real.pi)+C,fun n w hw => ?_⟩
  have hsmall : w∈ball z (R/(128*Real.pi)^2) := by
    have he : R/(128*Real.pi)^2=z.im/(2*(128*Real.pi)^2) := by dsimp [R]; ring
    rw [he]
    exact hw
  have h := univalent_coarse_local_bound hR ((hf n).mono hRH) ((hi n).mono hRH) hsmall
  calc
    ‖f n w‖ ≤ ‖f n w-f n z‖+‖f n z‖ := norm_le_norm_sub_add _ _
    _ ≤ R*‖deriv (f n) z‖/(128*Real.pi)+C :=
      add_le_add h.le (hC n z (mem_ball_self hr))
    _ ≤ R*(C/t)/(128*Real.pi)+C := by gcongr; exact hder n

lemma univalent_family_bound_propagates
    (f : ℕ → ℂ → ℂ) (hf : ∀ n, DifferentiableOn ℂ (f n) upperHalfPlane)
    (hi : ∀ n, InjOn (f n) upperHalfPlane)
    (hseed : (upperHalfPlane ∩ familyBoundedLocus f).Nonempty) :
    upperHalfPlane ⊆ familyBoundedLocus f := by
  have hconn : IsPreconnected upperHalfPlane :=
    (convex_halfSpace_im_gt (0:ℝ)).isPreconnected
  apply hconn.subset_of_closure_inter_subset (isOpen_familyBoundedLocus f) hseed
  rintro x ⟨hx,hxH⟩
  let Q : ℝ := (128*Real.pi)^2
  have hQ : 1≤Q := by dsimp [Q]; nlinarith [Real.pi_gt_three]
  have hQpos : 0<Q := lt_of_lt_of_le zero_lt_one hQ
  let δ := x.im/(8*Q)
  have hδ : 0<δ := div_pos hxH (by positivity)
  have hδle : δ≤x.im/8 :=
    div_le_div_of_nonneg_left hxH.le (by norm_num) (by nlinarith)
  obtain ⟨y,hy,hxy⟩ := Metric.mem_closure_iff.mp hx δ hδ
  have him : |y.im-x.im|<δ := by
    have h := Complex.abs_im_le_norm (y-x)
    rw [Complex.sub_im] at h
    exact h.trans_lt (by simpa only [dist_eq_norm,norm_sub_rev] using hxy)
  have hyH : y∈upperHalfPlane := by
    change 0<y.im
    have := (abs_lt.mp him).1
    linarith
  obtain ⟨B,hB⟩ := univalent_family_enlarged_bound f hf hi hyH hy
  have hxy' : dist x y<y.im/(2*Q) := by
    apply hxy.trans
    apply (div_lt_div_iff₀ (by positivity : 0<8*Q) (by positivity : 0<2*Q)).mpr
    have := (abs_lt.mp him).1
    nlinarith
  have hrad : 0<y.im/(2*Q)-dist x y := sub_pos.mpr hxy'
  refine ⟨y.im/(2*Q)-dist x y,hrad,B,fun n w hw => hB n w ?_⟩
  rw [mem_ball] at hw ⊢
  have htri := dist_triangle w x y
  change dist w y<y.im/(2*Q)
  linarith

lemma familyBoundedLocus_compact_bound (f : ℕ → ℂ → ℂ)
    {K : Set ℂ} (hK : IsCompact K) (hb : K⊆familyBoundedLocus f) :
    ∃ C : ℝ, ∀ n, ∀ z∈K, ‖f n z‖≤C := by
  classical
  choose r hr C hC using fun z : K => hb z.property
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover (fun z : K => ball z.1 (r z))
    (fun _ => isOpen_ball) (fun z hz => mem_iUnion.mpr ⟨⟨z,hz⟩,mem_ball_self (hr ⟨z,hz⟩)⟩)
  refine ⟨∑ z∈t, max (C z) 0,fun n z hz => ?_⟩
  obtain ⟨a,ha,hza⟩ := mem_iUnion₂.mp (ht hz)
  exact (hC a n z hza).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun a _ => le_max_right (C a) 0) ha))

end SLEExactGauge

end

end OAI
