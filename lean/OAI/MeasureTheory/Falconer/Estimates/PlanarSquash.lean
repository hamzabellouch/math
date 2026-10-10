import OAI.MeasureTheory.Falconer.Incidence.QuarterPencilGeometry

namespace OAI

/-! A fixed anisotropic change of coordinates narrows every bounded slope.
The same map acts on points and line parameters; incidence widths contract
by four and both maps have inverse Lipschitz constant sixteen. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def planarSquash (p : Space 2) : Space 2 := rowPoint (p 0/4) (p 1/16)
noncomputable def planarUnsquash (p : Space 2) : Space 2 := rowPoint (4*p 0) (16*p 1)

theorem planarSquash_leftInverse : Function.LeftInverse planarUnsquash planarSquash := by
  intro p
  ext i
  fin_cases i <;> simp [planarSquash,planarUnsquash,rowPoint] <;> ring

theorem planarSquash_rightInverse : Function.RightInverse planarUnsquash planarSquash := by
  intro p
  ext i
  fin_cases i <;> simp [planarSquash,planarUnsquash,rowPoint]

theorem planarSquash_injective : Function.Injective planarSquash :=
  planarSquash_leftInverse.injective

theorem planarSquash_dist_bounds (p q : Space 2) :
    dist (planarSquash p) (planarSquash q) ≤ dist p q/4 ∧
      dist p q ≤ 16*dist (planarSquash p) (planarSquash q) := by
  have h := EuclideanSpace.dist_sq_eq p q
  have h' := EuclideanSpace.dist_sq_eq (planarSquash p) (planarSquash q)
  simp only [Fin.sum_univ_two,Real.dist_eq,sq_abs] at h h'
  change dist (planarSquash p) (planarSquash q)^2 =
    (p 0/4-q 0/4)^2+(p 1/16-q 1/16)^2 at h'
  constructor <;> nlinarith [sq_nonneg (p 0-q 0),sq_nonneg (p 1-q 1),
    dist_nonneg (x := p) (y := q),dist_nonneg (x := planarSquash p) (y := planarSquash q)]

theorem planarSquash_separated {δ : ℝ} (P : Finset (Space 2))
    (hP : FiniteSeparatedAt (4*δ) P) :
    FiniteSeparatedAt (δ/4) (P.image planarSquash) := by
  intro x hx y hy hxy
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hy
  have hs := hP p hp q hq (fun he => hxy (congrArg planarSquash he))
  linarith only [hs,(planarSquash_dist_bounds p q).2]

theorem planarSquash_chart (P : Finset (Space 2)) (hP : InBoundedLineChart P) :
    InBoundedLineChart (P.image planarSquash) := by
  intro x hx
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
  change |p 0/4| ≤ 1 ∧ |p 1/16| ≤ 1
  rw [abs_div,abs_div]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 4),abs_of_pos (by norm_num : (0:ℝ) < 16)]
  constructor <;> linarith only [(hP p hp).1,(hP p hp).2]

theorem planarSquash_slope {p : Space 2} (hp : |p 0| ≤ 1) :
    |planarSquash p 0| ≤ 1/2 := by
  change |p 0/4| ≤ 1/2
  rw [abs_div]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 4)]
  linarith only [hp]

theorem planarSquash_incident {δ : ℝ} (hδ : 0 ≤ δ) {p l : Space 2}
    (h : TubeIncident δ p l) : TubeIncident (δ/4) (planarSquash p) (planarSquash l) := by
  have hd : 0 < Real.sqrt (1+(l 0)^2) := Real.sqrt_pos.2 (by positivity)
  have hd' : 0 < Real.sqrt (1+(l 0/4)^2) := Real.sqrt_pos.2 (by positivity)
  have hb : Real.sqrt (1+(l 0)^2) ≤ 4*Real.sqrt (1+(l 0/4)^2) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 1+(l 0)^2 by positivity),
      Real.sq_sqrt (show 0 ≤ 1+(l 0/4)^2 by positivity)]
  have hh := (div_le_iff₀ hd).1 h
  change |p 1/16-(l 0/4)*(p 0/4)-l 1/16|/Real.sqrt (1+(l 0/4)^2) ≤ δ/4
  rw [show p 1/16-(l 0/4)*(p 0/4)-l 1/16 = (p 1-l 0*p 0-l 1)/16 by ring,
    abs_div,abs_of_pos (by norm_num : (0:ℝ) < 16)]
  apply (div_le_iff₀ hd').2
  nlinarith only [hh,mul_le_mul_of_nonneg_left hb hδ]

theorem planarSquash_regular {δ s K : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (P : Finset (Space 2)) (hP : NormalizedFiniteBallBound δ s K P) :
    NormalizedFiniteBallBound (δ/4) s (K*16^s) (P.image planarSquash) := by
  intro z r hr _
  have hr0 : 0 < r := (by linarith : 0 < δ/4).trans_le hr
  have hsub : (P.image planarSquash).filter (fun p => dist p z ≤ r) ⊆
      (P.filter (fun p => dist p (planarUnsquash z) ≤ 16*r)).image planarSquash := by
    intro p hp
    obtain ⟨hp,hpr⟩ := Finset.mem_filter.mp hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩,rfl⟩
    have hh := (planarSquash_dist_bounds x (planarUnsquash z)).2
    rw [planarSquash_rightInverse z] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hpr (by norm_num))
  have hc : (((P.image planarSquash).filter (fun p => dist p z ≤ r)).card:ℝ) ≤
      ((P.filter (fun p => dist p (planarUnsquash z) ≤ 16*r)).card:ℝ) :=
    Nat.cast_le.mpr ((Finset.card_le_card hsub).trans Finset.card_image_le)
  have hb := normalized_ball_bound_all_radii hs hK hP (planarUnsquash z) (16*r)
    (by linarith only [hr,hδ])
  rw [Finset.card_image_of_injective _ planarSquash_injective]
  calc
    _ ≤ ((P.filter (fun p => dist p (planarUnsquash z) ≤ 16*r)).card:ℝ) := hc
    _ ≤ K*(16*r)^s*(P.card:ℝ) := hb
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 16) hr0.le]; ring

end Falconer

end OAI
