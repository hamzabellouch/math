import OAI.Geometry.Symplectic.MorseBounds.Conjugacy
import OAI.Geometry.Symplectic.MorseBounds.CapHamiltonian

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.CapEnd
open MorseArnold.SphereCaps MorseArnold.CapProduct MorseArnold.CapGluing
open scoped Manifold ContDiff
open Set
noncomputable section
variable {X : Type*} [TopologicalSpace X]

def chart (l : ℝ) (hl : 0 < l) (nu : Choices) :
    OpenPartialHomeomorph (X × SphereFour) (X × PlaneFour) :=
  (OpenPartialHomeomorph.refl X).prod (fourChart l hl nu)

def ambient (l eps t : ℝ) (q : X × SphereFour) : X × SphereFour :=
  (q.1,fourFlow l eps t q.2)

def quadratic (t : ℝ) (q : X × PlaneFour) : X × PlaneFour :=
  (q.1,quadFlow t q.2)

def correction (eps : ℝ) (phi : ℝ × (X × PlaneFour) → X × PlaneFour)
    (q : ℝ × (X × PlaneFour)) : X × PlaneFour :=
  phi (eps * q.1,quadratic (-eps * q.1) q.2)

def closedPath (l : ℝ) (hl : 0 < l) (eps : ℝ)
    (phi : ℝ × (X × PlaneFour) → X × PlaneFour)
    (q : ℝ × (X × SphereFour)) : X × SphereFour :=
  insert (chart l hl) (correction eps phi) (q.1,ambient l eps q.1 q.2)

lemma plane_inverse (t : ℝ) (z : Plane) :
    rotatePlane (-t) (rotatePlane t z) = z := by
  have h := Real.sin_sq_add_cos_sq t
  ext <;> simp only [rotatePlane, Real.sin_neg, Real.cos_neg]
  · calc
      _ = (Real.sin t ^ 2 + Real.cos t ^ 2) * z.1 := by ring
      _ = z.1 := by rw [h, one_mul]
  · calc
      _ = (Real.sin t ^ 2 + Real.cos t ^ 2) * z.2 := by ring
      _ = z.2 := by rw [h, one_mul]

lemma quad_inverse (t : ℝ) (z : PlaneFour) :
    quadFlow (-t) (quadFlow t z) = z := by
  exact Prod.ext (Prod.ext (plane_inverse t z.1.1) (plane_inverse t z.1.2))
    (Prod.ext (by simpa [quadFlow] using plane_inverse (-t) z.2.1)
      (by simpa [quadFlow] using plane_inverse (-t) z.2.2))

omit [TopologicalSpace X] in
lemma ambient_inverse (l eps t : ℝ) (q : X × SphereFour) :
    ambient l eps (-t) (ambient l eps t q) = q := by
  have h (s : ℝ) (p : S2) : sphereFlow l eps s (-t) (sphereFlow l eps s t p) = p := by
    rw [← (sphereFlow_laws l eps s).2, neg_add_cancel, (sphereFlow_laws l eps s).1]
  exact Prod.ext rfl (Prod.ext
    (Prod.ext (h (-1) q.2.1.1) (h (-1) q.2.1.2))
    (Prod.ext (h 1 q.2.2.1) (h 1 q.2.2.2)))

lemma chart_disjoint (l : ℝ) (hl : 25 / 2 < l) :
    Pairwise (fun i j : Choices =>
      Disjoint (chart (X := X) l (by linarith) i).source (chart l (by linarith) j).source) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hj
  exact Set.disjoint_left.mp (four_caps_disjoint l hl hij) hx.2 hj.2

lemma ambient_preserves (l eps t : ℝ) (hl : 25 / 2 < l) (i : Choices) :
    MapsTo (ambient (X := X) l eps t)
      (chart l (by linarith) i).source (chart l (by linarith) i).source := by
  intro x hx
  exact ⟨Set.mem_univ _,four_preserves l eps t hl i _ hx.2⟩

lemma ambient_outside (l eps : ℝ) (hl : 25 / 2 < l) (x : X × SphereFour)
    (hx : ∀ i, x ∉ (chart l (by linarith) i).source) :
    ∀ i, ambient l eps 1 x ∉ (chart l (by linarith) i).source := by
  intro i hi
  have h := ambient_preserves l eps (-1) hl i hi
  rw [ambient_inverse] at h
  exact hx i h

lemma correction_endpoint (l eps : ℝ) (hl : 25 / 2 < l)
    (phi : ℝ × (X × PlaneFour) → X × PlaneFour) (i : Choices)
    (x : X × SphereFour) (hx : x ∈ (chart l (by linarith) i).source) :
    correction eps phi (1,chart l (by linarith) i (ambient l eps 1 x)) =
      phi (eps,chart l (by linarith) i x) := by
  have h := four_endpoint l eps hl i x.2 hx.2
  change phi (eps * 1,(x.1,quadFlow (-eps * 1)
    (fourChart l (by linarith) i (fourFlow l eps 1 x.2)))) = _
  rw [mul_one, mul_one, h, quad_inverse]
  rfl

 theorem endpoint_count (l eps : ℝ) (hl : 25 / 2 < l)
    (heps : 0 < eps) (hepspi : eps < Real.pi)
    (phi : ℝ × (X × PlaneFour) → X × PlaneFour)
    (hmap : MapsTo (fun y => phi (eps,y)) (univ ×ˢ box) (univ ×ˢ box))
    (hsub : ∀ y, phi (eps,y) = y → y.2 ∈ box)
    (hfinite : {y | phi (eps,y) = y}.Finite) :
    {x | closedPath l (by linarith) eps phi (1,x) = x}.Finite ∧
      {x | closedPath l (by linarith) eps phi (1,x) = x}.ncard =
        16 * {y | phi (eps,y) = y}.ncard := by
  have htarget : ∀ i : Choices,
      (chart (X := X) l (by linarith) i).target = univ ×ˢ box := by
    intro i
    change univ ×ˢ (fourChart l (by linarith) i).target = _
    rw [four_chart_target l hl]
  have h := inserted_fixed_count (chart l (by linarith)) (chart_disjoint l hl)
    (correction eps phi) (ambient l eps 1) (fun y => phi (eps,y))
    (ambient_preserves l eps 1 hl) (correction_endpoint l eps hl phi)
    (by intro i; rw [htarget]; exact hmap)
    (ambient_outside l eps hl)
    (by
      intro x hx heq
      have hn : ∀ i, x.2 ∉ (fourChart l (by linarith) i).source := by
        intro i hi
        exact hx i ⟨Set.mem_univ _,hi⟩
      exact exterior_not_fixed l eps hl heps hepspi _ hn (congrArg Prod.snd heq))
    (by intro i y hy; rw [htarget]; exact ⟨Set.mem_univ _,hsub y hy⟩) hfinite
  simpa only [closedPath, Nat.card_prod, Nat.card_eq_fintype_card, Choices, Fintype.card_prod, Fintype.card_bool,
    show (2 * 2) * (2 * 2) = 16 by norm_num] using h

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [ChartedSpace H X] [I.Boundaryless] [IsManifold I ∞ X]

lemma chart_target (l : ℝ) (hl : 25 / 2 < l) (i : Choices) :
    (chart (X := X) l (by linarith) i).target = univ ×ˢ box := by
  change univ ×ˢ (fourChart l (by linarith) i).target = _
  rw [four_chart_target l hl]

omit [I.Boundaryless] [IsManifold I ∞ X] in
lemma chart_smooth (l : ℝ) (hl : 25 / 2 < l) (i : Choices) :
    ContMDiffOn (I.prod SP) (I.prod PP) ∞ (chart (X := X) l (by linarith) i)
      (chart l (by linarith) i).source ∧
    ContMDiffOn (I.prod PP) (I.prod SP) ∞ (chart (X := X) l (by linarith) i).symm
      (chart l (by linarith) i).target := by
  constructor
  · exact (contMDiffOn_id (I := I)).prodMap (four_chart_smooth l hl i).1
  · rw [chart_target l hl]
    exact (contMDiffOn_id (I := I)).prodMap (four_chart_smooth l hl i).2

 theorem endpoint_nondegenerate (l eps : ℝ) (hl : 25 / 2 < l)
    (heps : 0 < eps) (hepspi : eps < Real.pi)
    (phi : ℝ × (X × PlaneFour) → X × PlaneFour)
    (hphi : ContMDiff (𝓘(ℝ).prod (I.prod PP)) (I.prod PP) ∞ phi)
    (hmap : MapsTo (fun y => phi (eps,y)) (univ ×ˢ box) (univ ×ˢ box))
    (hnd : ∀ y, phi (eps,y) = y →
      MorseArnold.Conjugacy.NondegenerateAt (I.prod PP) (fun z => phi (eps,z)) y) :
    ∀ x, closedPath l (by linarith) eps phi (1,x) = x →
      MorseArnold.Conjugacy.NondegenerateAt (I.prod SP)
        (fun z => closedPath l (by linarith) eps phi (1,z)) x := by
  intro x hx
  have hcover : ∃ i : Choices, x ∈ (chart l (by linarith) i).source := by
    by_contra hn
    have ho := not_exists.mp hn
    have hg : ambient l eps 1 x = x := by
      change insert (chart l (by linarith)) (correction eps phi) (1,ambient l eps 1 x) = x at hx
      rwa [insert_outside _ _ _ _ (ambient_outside l eps hl x ho)] at hx
    apply exterior_not_fixed l eps hl heps hepspi x.2 _ (congrArg Prod.snd hg)
    intro i hi
    exact ho i ⟨Set.mem_univ _,hi⟩
  obtain ⟨i,hi⟩ := hcover
  let e := chart (X := X) l (by linarith) i
  have het : e.target = univ ×ˢ box := chart_target l hl i
  have hlocal : ∀ z ∈ e.source, closedPath l (by linarith) eps phi (1,z) =
      e.symm (phi (eps,e z)) := by
    intro z hz
    exact inserted_in_source (chart l (by linarith)) (chart_disjoint l hl)
      (correction eps phi) (ambient l eps 1) (fun y => phi (eps,y))
      (ambient_preserves l eps 1 hl) (correction_endpoint l eps hl phi) i z hz
  have hmodelfix : phi (eps,e x) = e x := by
    have hh := congrArg e ((hlocal x hi).symm.trans hx)
    have hm : phi (eps,e x) ∈ e.target := by
      rw [het]
      apply hmap
      rw [← het]
      exact e.map_source hi
    rwa [e.right_inv hm] at hh
  have hconj : ∀ᶠ z in nhds x,
      closedPath l (by linarith) eps phi (1,z) = e.symm (phi (eps,e z)) := by
    filter_upwards [e.open_source.mem_nhds hi] with z hz
    exact hlocal z hz
  apply MorseArnold.Conjugacy.nondegenerate_manifold_conjugate (I.prod SP) (I.prod PP) e
    (chart_smooth I l hl i).1 (chart_smooth I l hl i).2
    (fun z => closedPath l (by linarith) eps phi (1,z)) (fun z => phi (eps,z))
    x hi _ hmodelfix hconj (hnd _ hmodelfix)
  exact (hphi.comp (contMDiff_const.prodMk contMDiff_id)).contMDiffAt

end
end MorseArnold.CapEnd

end

end OAI
