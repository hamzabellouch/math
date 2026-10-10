import OAI.GroupTheory.ArtinCAT0.Refinement

namespace OAI

namespace ArtinCAT0.SixSector
open SectorMetric

variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X] [ProperSpace X] [Nonempty X]

noncomputable def rayLength (y : X) (i : Fin 6) := stableLengthAt y (ray i)
noncomputable def chart (y : X) (i : Fin 6) (p : Point) : TriangleGroup :=
  lattice (ray i) (ray (i+1)) (rayLength y i) (rayLength y (i+1)) p
noncomputable def axis (y : X) (i : Fin 6) (R : ℝ) : TriangleGroup := (ray i)^⌊R/rayLength y i⌋
noncomputable def circle (y : X) (R : ℝ) (i : Fin 6) (t : ℝ) : TriangleGroup :=
  chart y i (R*(unit (cosine y i) t).1,R*(unit (cosine y i) t).2)

omit [ProperSpace X] [Nonempty X] in
@[simp] lemma chart_zero (y : X) (i : Fin 6) : chart y i (0,0) = 1 := lattice_origin _ _ _ _
omit [ProperSpace X] [Nonempty X] in
@[simp] lemma chart_axis1 (y : X) (i : Fin 6) (R : ℝ) : chart y i (R,0) = axis y i R := by
  simp [chart,lattice,axis]
omit [ProperSpace X] [Nonempty X] in
@[simp] lemma chart_axis2 (y : X) (i : Fin 6) (R : ℝ) : chart y i (0,R) = axis y (i+1) R := by
  simp [chart,lattice,axis]

lemma cosine_abs (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y) (i : Fin 6) :
    |cosine y i| ≤ 1 := abs_le.mpr ⟨by linarith [cosine_lower hG y hR i],cosine_le_one hG y hR i⟩

omit [ProperSpace X] [Nonempty X] in
lemma circle_zero (y : X) (R : ℝ) (i : Fin 6) : circle y R i 0 = axis y i R := by
  simp [circle]
lemma circle_one (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y)
    (R : ℝ) (i : Fin 6) : circle y R i 1 = axis y (i+1) R := by
  simp [circle,unit_one _ (cosine_abs hG y hR i)]

theorem chart_uniform (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y) :
    ∃ C : ℝ, 0≤C ∧ ∀ i p q,
      |dist (chart y i p • y) (chart y i q • y)-‖vec (cosine y i) (q.1-p.1,q.2-p.2)‖| ≤ C := by
  have hh i : ∃ C : ℝ, 0≤C ∧ ∀ p q : Point,
      |dist (chart y i p • y) (chart y i q • y)-‖vec (cosine y i) (q.1-p.1,q.2-p.2)‖| ≤ C := by
    apply lattice_metric hG y (ray_length_pos hG y hR i) (ray_length_pos hG y hR (i+1))
      (ray_commute i) (cosine_abs hG y hR i)
    unfold cosine
    field_simp [ne_of_gt (ray_length_pos hG y hR i),ne_of_gt (ray_length_pos hG y hR (i+1))]
  choose C hC hh using hh
  refine ⟨∑ i, C i,Finset.sum_nonneg (fun i _ => hC i),?_⟩
  intro i p q
  exact (hh i p q).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))

section Estimates
variable (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y)
  {C : ℝ} (hC : 0≤C)
  (hchart : ∀ i p q, |dist (chart y i p • y) (chart y i q • y)-
    ‖vec (cosine y i) (q.1-p.1,q.2-p.2)‖| ≤ C)
include hG hR hchart

lemma circle_radius {R : ℝ} (hR0 : 0≤R) (i : Fin 6) {t : ℝ} (ht : t∈Set.Icc 0 1) :
    |dist y (circle y R i t • y)-R| ≤ C := by
  have h := hchart i (0,0) (R*(unit (cosine y i) t).1,R*(unit (cosine y i) t).2)
  rw [chart_zero,one_smul] at h
  simp only [sub_zero] at h
  rw [vec_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hR0,
    unit_vec (cosine_lower hG y hR i).le (cosine_le_one hG y hR i) ht,mul_one] at h
  exact h

lemma circle_lipschitz {R : ℝ} (hR0 : 0≤R) (i : Fin 6) {s t : ℝ}
    (hs : s∈Set.Icc 0 1) (ht : t∈Set.Icc 0 1) :
    dist (circle y R i s • y) (circle y R i t • y) ≤ 20*R*|s-t|+C := by
  have h := (abs_le.mp (hchart i (R*(unit (cosine y i) s).1,R*(unit (cosine y i) s).2)
    (R*(unit (cosine y i) t).1,R*(unit (cosine y i) t).2))).2
  have hb := vec_bound (cosine y i) (cosine_abs hG y hR i)
    (R*(unit (cosine y i) t).1-R*(unit (cosine y i) s).1,
      R*(unit (cosine y i) t).2-R*(unit (cosine y i) s).2)
  have hu := unit_lipschitz (cosine_lower hG y hR i).le (cosine_le_one hG y hR i) ht hs
  simp only [← mul_sub,abs_mul,abs_of_nonneg hR0] at hb
  rw [abs_sub_comm t s] at hu
  change dist (circle y R i s • y) (circle y R i t • y)-_ ≤ C at h
  simp only [← mul_sub] at h
  nlinarith [mul_le_mul_of_nonneg_left hu.1 hR0,mul_le_mul_of_nonneg_left hu.2 hR0]

lemma axis_radius {R : ℝ} (hR0 : 0≤R) (i : Fin 6) :
    |dist y (axis y i R • y)-R| ≤ C := by
  simpa only [circle_zero] using circle_radius hG y hR hchart hR0 i (by norm_num : (0:ℝ)∈Set.Icc 0 1)

lemma circle_axis_chord {c r R : ℝ} (hc : ∀ i, c≤cosine y i) (hr : 0≤r) (hR0 : 0≤R)
    (i : Fin 6) {t : ℝ} (ht : t∈Set.Icc 0 1) :
    dist (axis y i (r*R) • y) (circle y R i t • y) ≤ R*Real.sqrt (1+r^2-2*c*r)+C ∧
    dist (axis y (i+1) (r*R) • y) (circle y R i t • y) ≤ R*Real.sqrt (1+r^2-2*c*r)+C := by
  have hca := (cosine_lower hG y hR i).le
  have hcb := cosine_le_one hG y hR i
  have h1 := chord_axis1 hca hcb ht hr
  have h2 := chord_axis2 hca hcb ht hr
  have hd : 1+r^2-2*cosine y i*r ≤ 1+r^2-2*c*r := by nlinarith [hc i]
  have hn1 : ‖vec (cosine y i) ((unit (cosine y i) t).1-r,(unit (cosine y i) t).2)‖ ≤
      Real.sqrt (1+r^2-2*c*r) := by
    exact (Real.le_sqrt (norm_nonneg _) (by linarith [sq_nonneg ‖vec (cosine y i) ((unit (cosine y i) t).1-r,(unit (cosine y i) t).2)‖])).mpr (h1.trans hd)
  have hn2 : ‖vec (cosine y i) ((unit (cosine y i) t).1,(unit (cosine y i) t).2-r)‖ ≤
      Real.sqrt (1+r^2-2*c*r) := by
    exact (Real.le_sqrt (norm_nonneg _) (by linarith [sq_nonneg ‖vec (cosine y i) ((unit (cosine y i) t).1,(unit (cosine y i) t).2-r)‖])).mpr (h2.trans hd)
  constructor
  · have h := (abs_le.mp (hchart i (r*R,0) (R*(unit (cosine y i) t).1,R*(unit (cosine y i) t).2))).2
    rw [chart_axis1] at h
    change dist (axis y i (r*R) • y) (circle y R i t • y)-_ ≤ C at h
    rw [show R*(unit (cosine y i) t).1-r*R = R*((unit (cosine y i) t).1-r) by ring,
      sub_zero,vec_mul (cosine y i) R ((unit (cosine y i) t).1-r,(unit (cosine y i) t).2),norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hR0] at h
    nlinarith [mul_le_mul_of_nonneg_left hn1 hR0]
  · have h := (abs_le.mp (hchart i (0,r*R) (R*(unit (cosine y i) t).1,R*(unit (cosine y i) t).2))).2
    rw [chart_axis2] at h
    change dist (axis y (i+1) (r*R) • y) (circle y R i t • y)-_ ≤ C at h
    rw [show R*(unit (cosine y i) t).2-r*R = R*((unit (cosine y i) t).2-r) by ring,
      sub_zero,vec_mul (cosine y i) R ((unit (cosine y i) t).1,(unit (cosine y i) t).2-r),norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hR0] at h
    nlinarith [mul_le_mul_of_nonneg_left hn2 hR0]

lemma axis_adjacent {R : ℝ} (hR0 : 0≤R) (i : Fin 6) :
    dist (axis y i R • y) (axis y (i+1) R • y) ≤ R+C := by
  have h := (abs_le.mp (hchart i (R,0) (0,R))).2
  rw [chart_axis1,chart_axis2] at h
  have hs := vec_sq (cosine y i) (cosine_abs hG y hR i) (0-R,R-0)
  have hl := cosine_lower hG y hR i
  have hn : ‖vec (cosine y i) (0-R,R-0)‖ ≤ R := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hl.le) (sq_nonneg R),norm_nonneg (vec (cosine y i) (0-R,R-0))]
  linarith

end Estimates
end ArtinCAT0.SixSector

namespace ArtinCAT0.SixSector
open SectorMetric
variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X] [ProperSpace X] [Nonempty X]

lemma common_cosine (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y) :
    ∃ c : ℝ, 1/2<c ∧ c≤1 ∧ ∀ i, c≤cosine y i := by
  classical
  let c := Finset.univ.inf' Finset.univ_nonempty (cosine y)
  refine ⟨c,?_,?_,?_⟩
  · exact (Finset.lt_inf'_iff _).mpr (fun i _ => cosine_lower hG y hR i)
  · exact (Finset.inf'_le _ (Finset.mem_univ (0 : Fin 6))).trans (cosine_le_one hG y hR 0)
  · intro i
    exact Finset.inf'_le _ (Finset.mem_univ i)

lemma circle_detour (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y)
    {C : ℝ} (hC : 0≤C)
    (hchart : ∀ i p q, |dist (chart y i p • y) (chart y i q • y)-
      ‖vec (cosine y i) (q.1-p.1,q.2-p.2)‖| ≤ C)
    {c r R : ℝ} (hc : ∀ i, c≤cosine y i) (hr : 0≤r) (hR0 : 0≤R)
    (i : Fin 6) {t : ℝ} (ht : t∈Set.Icc 0 1) :
    dist (axis y 0 R • y) (circle y R i t • y) ≤
      (2*Real.sqrt (1+r^2-2*c*r)+r)*R+3*C := by
  have hleft : dist (axis y 0 R • y) (axis y 1 (r*R) • y) ≤ R*Real.sqrt (1+r^2-2*c*r)+C := by
    have h := (circle_axis_chord hG y hR hchart hc hr hR0 0 (by norm_num : (0:ℝ)∈Set.Icc 0 1)).2
    simpa only [circle_zero,Fin.reduceAdd,dist_comm] using h
  have hright : dist (axis y 0 R • y) (axis y 5 (r*R) • y) ≤ R*Real.sqrt (1+r^2-2*c*r)+C := by
    have h := (circle_axis_chord hG y hR hchart hc hr hR0 5 (by norm_num : (1:ℝ)∈Set.Icc 0 1)).1
    simpa only [circle_one hG y hR,Fin.reduceAdd,dist_comm] using h
  have h12 := axis_adjacent hG y hR hchart (mul_nonneg hr hR0) 1
  have h45 := axis_adjacent hG y hR hchart (mul_nonneg hr hR0) 4
  have hi := circle_axis_chord hG y hR hchart hc hr hR0 i ht
  rcases hi with ⟨hia,hib⟩
  fin_cases i
  · change dist (axis y 0 R • y) (circle y R 0 t • y) ≤ _
    change dist (axis y 0 (r*R) • y) (circle y R 0 t • y) ≤ _ at hia
    change dist (axis y 1 (r*R) • y) (circle y R 0 t • y) ≤ _ at hib
    have hh := dist_triangle (axis y 0 R • y) (axis y 1 (r*R) • y) (circle y R 0 t • y)
    nlinarith [mul_nonneg hr hR0]
  · change dist (axis y 0 R • y) (circle y R 1 t • y) ≤ _
    change dist (axis y 1 (r*R) • y) (circle y R 1 t • y) ≤ _ at hia
    change dist (axis y 2 (r*R) • y) (circle y R 1 t • y) ≤ _ at hib
    have hh := dist_triangle (axis y 0 R • y) (axis y 1 (r*R) • y) (circle y R 1 t • y)
    nlinarith [mul_nonneg hr hR0]
  · change dist (axis y 0 R • y) (circle y R 2 t • y) ≤ _
    change dist (axis y 2 (r*R) • y) (circle y R 2 t • y) ≤ _ at hia
    change dist (axis y 3 (r*R) • y) (circle y R 2 t • y) ≤ _ at hib
    have hh := dist_triangle4 (axis y 0 R • y) (axis y 1 (r*R) • y) (axis y 2 (r*R) • y) (circle y R 2 t • y)
    change dist (axis y 1 (r*R) • y) (axis y 2 (r*R) • y) ≤ r*R+C at h12
    nlinarith
  · change dist (axis y 0 R • y) (circle y R 3 t • y) ≤ _
    change dist (axis y 3 (r*R) • y) (circle y R 3 t • y) ≤ _ at hia
    change dist (axis y 4 (r*R) • y) (circle y R 3 t • y) ≤ _ at hib
    have hh := dist_triangle4 (axis y 0 R • y) (axis y 5 (r*R) • y) (axis y 4 (r*R) • y) (circle y R 3 t • y)
    change dist (axis y 4 (r*R) • y) (axis y 5 (r*R) • y) ≤ r*R+C at h45
    rw [dist_comm (axis y 4 (r*R) • y)] at h45
    nlinarith
  · change dist (axis y 0 R • y) (circle y R 4 t • y) ≤ _
    change dist (axis y 4 (r*R) • y) (circle y R 4 t • y) ≤ _ at hia
    change dist (axis y 5 (r*R) • y) (circle y R 4 t • y) ≤ _ at hib
    have hh := dist_triangle (axis y 0 R • y) (axis y 5 (r*R) • y) (circle y R 4 t • y)
    nlinarith [mul_nonneg hr hR0]
  · change dist (axis y 0 R • y) (circle y R 5 t • y) ≤ _
    change dist (axis y 5 (r*R) • y) (circle y R 5 t • y) ≤ _ at hia
    change dist (axis y 0 (r*R) • y) (circle y R 5 t • y) ≤ _ at hib
    have hh := dist_triangle (axis y 0 R • y) (axis y 5 (r*R) • y) (circle y R 5 t • y)
    nlinarith [mul_nonneg hr hR0]

end ArtinCAT0.SixSector

namespace ArtinCAT0.WordDiagram

lemma eval_surjective : Function.Surjective eval := by
  let H : Subgroup TriangleGroup :=
    { carrier := Set.range eval
      one_mem' := ⟨1,map_one eval⟩
      mul_mem' := by rintro a b ⟨u,rfl⟩ ⟨v,rfl⟩; exact ⟨u*v,map_mul eval u v⟩
      inv_mem' := by rintro a ⟨u,rfl⟩; exact ⟨inverseWord u,eval_inverseWord u⟩ }
  have hh (i : Fin 3) : (PresentedGroup.of i : TriangleGroup) ∈ H := by
    refine ⟨positive i,?_⟩
    simp [positive,eval,signed,triangleGen]
  intro g
  exact PresentedGroup.generated_by triangleRelators H hh g

noncomputable def representative (g : TriangleGroup) : Word := (eval_surjective g).choose
@[simp] lemma eval_representative (g : TriangleGroup) : eval (representative g) = g :=
  (eval_surjective g).choose_spec

section FiniteLibrary
variable {E : Type*} [Fintype E] (e : E → TriangleGroup)

abbrev SmallSide := E × Bool
noncomputable def smallSide (s : SmallSide (E:=E)) : Side := (representative (e s.1),s.2)
def smallFlip (s : SmallSide (E:=E)) : SmallSide (E:=E) := (s.1,!s.2)

omit [Fintype E] in
@[simp] lemma smallSide_flip (s : SmallSide (E:=E)) :
    smallSide e (smallFlip s) = sideFlip (smallSide e s) := rfl

abbrev SmallLoop := {s : Fin 3 → SmallSide (E:=E) // closedSides (smallSide e ∘ s)}

noncomputable instance : Fintype (SmallLoop e) := Fintype.ofFinite _

noncomputable def loopSides (s : SmallLoop e) : Fin 3 → Side := smallSide e ∘ s.val
omit [Fintype E] in
lemma loops_closed (s : SmallLoop e) : closedSides (loopSides e s) := s.property

end FiniteLibrary

section Controlled
variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X] [ProperSpace X]

lemma finite_short_elements (hG : GeometricAction TriangleGroup X) (y : X)
    (B : ℝ) (hB : 0≤B) : {g : TriangleGroup | dist y (g•y) ≤ B}.Finite := by
  have h := finite_movers_of_compact hG.2.2.1 (isCompact_singleton : IsCompact ({y}:Set X)) y B hB
  simpa using h

variable (hG : GeometricAction TriangleGroup X) (y : X) (B : ℝ) (hB : 0≤B)
abbrev ShortElement := {g : TriangleGroup // dist y (g•y) ≤ B}
@[instance_reducible] noncomputable def shortElementFintype : Fintype (ShortElement y B) :=
  (finite_short_elements hG y B hB).fintype

omit [ProperSpace X] in
include hG in
lemma action_displacement (g h : TriangleGroup) :
    dist y ((g⁻¹*h)•y) = dist (g•y) (h•y) := (action_dist hG.2.1 y g h).symm

section Orient
variable {F V : Type*} [Fintype F] (M : TriangleMesh F V) (z : V → TriangleGroup)
  (hz : ∀ f i, dist (z (M.tail (f,i))•y) (z (M.tail (f,i+1))•y) ≤ B)

noncomputable def chooseForward (d : F × Fin 3) : Bool := by
  classical
  exact decide (Fintype.equivFin (F × Fin 3) d < Fintype.equivFin (F × Fin 3) (M.mate d))

lemma chooseForward_mate (d : F × Fin 3) : chooseForward M (M.mate d) = !chooseForward M d := by
  classical
  simp only [chooseForward,M.mate_involutive d]
  have hn : Fintype.equivFin (F × Fin 3) d ≠ Fintype.equivFin (F × Fin 3) (M.mate d) :=
    fun h => (M.mate_ne d).symm ((Fintype.equivFin _).injective h)
  by_cases h : Fintype.equivFin (F × Fin 3) d < Fintype.equivFin (F × Fin 3) (M.mate d)
  · simp [h,not_lt.mpr h.le]
  · have h' := lt_of_le_of_ne (le_of_not_gt h) hn.symm
    simp [h,h']

noncomputable def orientedSide (d : F × Fin 3) : ShortElement y B × Bool :=
  if chooseForward M d then
    (⟨(z (M.tail d))⁻¹*z (M.tail (d.1,d.2+1)),by rw [action_displacement hG y]; exact hz _ _⟩,false)
  else
    (⟨(z (M.tail (d.1,d.2+1)))⁻¹*z (M.tail d),by
      rw [action_displacement hG y,dist_comm]; exact hz _ _⟩,true)

omit [ProperSpace X] in
lemma orientedSide_mate (d : F × Fin 3) :
    orientedSide hG y B M z hz (M.mate d) = smallFlip (orientedSide hG y B M z hz d) := by
  classical
  unfold orientedSide
  rw [chooseForward_mate]
  have ht := M.tail_mate d
  have hh := M.tail_rotate_mate d
  change M.tail ((M.mate d).1,(M.mate d).2+1) = M.tail d at hh
  cases h : chooseForward M d <;> simp [smallFlip,ht,hh]

omit [ProperSpace X] in
lemma orientedSide_value (d : F × Fin 3) :
    eval (sideWord (smallSide (Subtype.val : ShortElement y B → TriangleGroup)
      (orientedSide hG y B M z hz d))) = (z (M.tail d))⁻¹*z (M.tail (d.1,d.2+1)) := by
  classical
  unfold orientedSide
  cases h : chooseForward M d <;> simp [smallSide,sideWord,mul_inv_rev]

noncomputable def faceLoop (f : F) : SmallLoop (Subtype.val : ShortElement y B → TriangleGroup) := by
  refine ⟨fun i => orientedSide hG y B M z hz (f,i),?_⟩
  change eval (sideWord (smallSide _ _))*eval (sideWord (smallSide _ _))*eval (sideWord (smallSide _ _)) = 1
  simp only [orientedSide_value]
  change (z (M.tail (f,0)))⁻¹*z (M.tail (f,1))*
    ((z (M.tail (f,1)))⁻¹*z (M.tail (f,2)))*
    ((z (M.tail (f,2)))⁻¹*z (M.tail (f,0))) = 1
  group

omit [ProperSpace X] in
lemma faceLoop_start (f : F) (i : Fin 3) :
    z (M.tail (f,0))*startLabel (loopSides _ (faceLoop hG y B M z hz f)) i = z (M.tail (f,i)) := by
  fin_cases i <;> simp [startLabel,loopSides,faceLoop,orientedSide_value,
    show (2:Fin 3)≠1 by decide,mul_assoc]

omit [ProperSpace X] in
lemma faceLoop_mate (f : F) (i : Fin 3) :
    loopSides _ (faceLoop hG y B M z hz (M.mate (f,i)).1) (M.mate (f,i)).2 =
      sideFlip (loopSides _ (faceLoop hG y B M z hz f) i) := by
  change smallSide _ (orientedSide hG y B M z hz (M.mate (f,i))) = _
  rw [orientedSide_mate,smallSide_flip]
  rfl

end Orient
end Controlled
end ArtinCAT0.WordDiagram

namespace ArtinCAT0.WordDiagram
open TriangleMesh

variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X] [ProperSpace X]

/-- The constants are chosen before the mesh: refinement has uniformly bounded
metric displacement and uniformly bounded error in every mirror coordinate. -/
theorem controlled_refinement (hG : GeometricAction TriangleGroup X) (y : X)
    (B : ℝ) (hB : 0≤B) :
    ∃ K H : ℕ, ∃ hK : 0<K, letI : NeZero K := ⟨by omega⟩;
      ∃ C D : ℝ, 0≤C ∧ 0≤D ∧
      ∀ (F V : Type) [Fintype F] (M : TriangleMesh F V) (z : V → TriangleGroup),
      (∀ f i, dist (z (M.tail (f,i))•y) (z (M.tail (f,i+1))•y) ≤ B) →
      ∃ L : (Replacement.mesh M (GridDisk.patch H (3*K)) (GridDisk.sides H K)).SimplicialLabeling,
        (∀ f p,
          dist (L.vertex (Replacement.vertex M (GridDisk.patch H (3*K)) (GridDisk.sides H K) (f,p)) • y)
            (z (M.tail (f,0))•y) ≤ C) ∧
        (∀ f p d,
          |mirrorVector (L.vertex (Replacement.vertex M (GridDisk.patch H (3*K)) (GridDisk.sides H K) (f,p))) d-
            mirrorVector (z (M.tail (f,0))) d| ≤ D) ∧
        (∀ f i, L.vertex (Replacement.vertex M (GridDisk.patch H (3*K)) (GridDisk.sides H K)
            (f,(GridDisk.sides H K).point (i,0))) = z (M.tail (f,i))) := by
  classical
  let E := ShortElement y B
  let : Fintype E := shortElementFintype hG y B hB
  let e : E → TriangleGroup := Subtype.val
  let I := SmallLoop e
  let s := loopSides e
  obtain ⟨K,H,hK,hbound,v,hv,hl⟩ := finite_template_fillers s (loops_closed e)
  let : NeZero K := ⟨by omega⟩
  choose D hD hd using fun i p => mirrorVector_bounded (v i p)
  let C₀ : ℝ := ∑ i, ∑ p, dist y (v i p • y)
  let D₀ : ℝ := ∑ i, ∑ p, D i p
  have hC₀ : 0≤C₀ := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => dist_nonneg))
  have hD₀ : 0≤D₀ := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun p _ => hD i p))
  have hc (i : I) (p : GridDisk.Vertex H (3*K)) : dist y (v i p • y) ≤ C₀ := by
    have h₁ : dist y (v i p • y) ≤ ∑ q, dist y (v i q • y) :=
      Finset.single_le_sum (f:=fun q => dist y (v i q • y)) (fun _ _ => dist_nonneg) (Finset.mem_univ p)
    exact h₁.trans (Finset.single_le_sum (f:=fun j => ∑ q, dist y (v j q • y))
      (fun _ _ => Finset.sum_nonneg (fun _ _ => dist_nonneg)) (Finset.mem_univ i))
  have hd₀ (i : I) (p : GridDisk.Vertex H (3*K)) (d : Mirror) : |mirrorVector (v i p) d| ≤ D₀ := by
    exact (hd i p d).trans ((Finset.single_le_sum (fun q _ => hD i q) (Finset.mem_univ p)).trans
      (Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun q _ => hD j q)) (Finset.mem_univ i)))
  refine ⟨K,H,hK,C₀,D₀,hC₀,hD₀,?_⟩
  intro F V _ M z hz
  let τ : F → I := faceLoop hG y B M z hz
  let b : F → TriangleGroup := fun f => z (M.tail (f,0))
  have hb : ∀ f i, b f * startLabel (s (τ f)) i = z (M.tail (f,i)) :=
    faceLoop_start hG y B M z hz
  have hm : ∀ f i, s (τ (M.mate (f,i)).1) (M.mate (f,i)).2 = sideFlip (s (τ f) i) :=
    faceLoop_mate hG y B M z hz
  let w := refinedLabels M s (loops_closed e) K H hbound v hv τ b z hb hm
  have hw := refinedLabels_legal M s (loops_closed e) K H hbound v hv τ b z hb hm hl
  let L := SimplicialLabeling.ofVertices _ w hw
  refine ⟨L,?_,?_,?_⟩
  · intro f p
    change dist ((b f*v (τ f) p)•y) (b f•y) ≤ C₀
    rw [mul_smul,(hG.2.1 (b f)).dist_eq,dist_comm]
    exact hc _ _
  · intro f p d
    change |mirrorVector (b f*v (τ f) p) d-mirrorVector (b f) d| ≤ D₀
    rw [mirrorVector_mul,add_sub_cancel_left]
    exact hd₀ _ _ _
  · intro f i
    change b f*v (τ f) ((GridDisk.sides H K).point (i,0)) = _
    change b f*v (τ f) (Sum.inl (Fin.last (H+1),GridDisk.sideIndex K i 0)) = _
    rw [hv,sideBoundary_get _ (loops_closed e _) K (hbound _)]
    have hh := sideFull_head (startLabel (s (τ f)) i) (s (τ f) i) K (hbound _ i)
    rw [List.getD,show (0 : Fin (K+1)).val = 0 from rfl,← List.head?_eq_getElem?,hh,Option.getD_some]
    exact hb f i

end ArtinCAT0.WordDiagram

namespace ArtinCAT0.SixSector
open SectorMetric

lemma product_next {N : ℕ} [NeZero N] (a : Fin 6) (j : Fin N) :
    finProdFinEquiv (a,j)+1 =
      if h : j.val+1<N then finProdFinEquiv (a,⟨j.val+1,h⟩)
      else finProdFinEquiv (a+1,0) := by
  have hN : 0<N := NeZero.pos N
  have h6 : 1<6*N := by omega
  split_ifs with h
  · apply Fin.ext
    change (j.val+N*a.val+1%(6*N))%(6*N) = j.val+1+N*a.val
    rw [Nat.mod_eq_of_lt h6]
    have hm := Nat.mul_le_mul_left N (show a.val≤5 by omega)
    have hb : j.val+N*a.val+1<6*N := by omega
    rw [Nat.mod_eq_of_lt hb]
    omega
  · have hj : j.val+1=N := by omega
    apply Fin.ext
    change (j.val+N*a.val+1%(6*N))%(6*N) = 0+N*((a.val+1)%6)
    rw [Nat.mod_eq_of_lt h6,zero_add]
    have he : j.val+N*a.val+1 = (a.val+1)*N := by nlinarith
    rw [he]
    by_cases ha : a.val+1<6
    · rw [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt (Nat.mul_lt_mul_of_pos_right ha hN)]
      exact Nat.mul_comm _ _
    · have ha' : a.val=5 := by omega
      simp [ha',Nat.mul_comm]

variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X]

noncomputable def ringCircle (y : X) (N : ℕ) [NeZero N] (R : ℝ) (j : Fin (6*N)) : TriangleGroup :=
  let p := finProdFinEquiv.symm j
  circle y R p.1 (p.2.val/N)

lemma ringCircle_product (y : X) (N : ℕ) [NeZero N] (R : ℝ) (a : Fin 6) (j : Fin N) :
    ringCircle y N R (finProdFinEquiv (a,j)) = circle y R a (j.val/N) := by
  simp [ringCircle]

lemma angular_parameter {N : ℕ} [NeZero N] (j : Fin N) : (j.val/(N:ℝ)) ∈ Set.Icc 0 1 := by
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (NeZero.pos N)
  exact ⟨div_nonneg (Nat.cast_nonneg _) hN.le,(div_le_iff₀ hN).mpr (by rw [one_mul]; exact_mod_cast j.isLt.le)⟩

section Action
variable [ProperSpace X] [Nonempty X]
variable (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y)
  {C : ℝ} (hchart : ∀ i p q, |dist (chart y i p • y) (chart y i q • y)-
    ‖vec (cosine y i) (q.1-p.1,q.2-p.2)‖| ≤ C)
include hG hR hchart

lemma ringCircle_radius (N : ℕ) [NeZero N] {R : ℝ} (hR0 : 0≤R) (j : Fin (6*N)) :
    |dist y (ringCircle y N R j •y)-R| ≤ C :=
  circle_radius hG y hR hchart hR0 _ (angular_parameter _)

lemma circle_radial (i : Fin 6) {t : ℝ} (ht : t∈Set.Icc 0 1) (R S : ℝ) :
    dist (circle y R i t •y) (circle y S i t •y) ≤ |R-S|+C := by
  have h := (abs_le.mp (hchart i (R*(unit (cosine y i) t).1,R*(unit (cosine y i) t).2)
    (S*(unit (cosine y i) t).1,S*(unit (cosine y i) t).2))).2
  change dist (circle y R i t •y) (circle y S i t •y)-_ ≤ C at h
  simp only [← sub_mul] at h
  rw [vec_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    unit_vec (cosine_lower hG y hR i).le (cosine_le_one hG y hR i) ht,mul_one,abs_sub_comm S R] at h
  linarith

lemma ringCircle_radial (N : ℕ) [NeZero N] (R S : ℝ) (j : Fin (6*N)) :
    dist (ringCircle y N R j •y) (ringCircle y N S j •y) ≤ |R-S|+C :=
  circle_radial hG y hR hchart _ (angular_parameter _) R S

lemma ringCircle_step (N : ℕ) [NeZero N] {R : ℝ} (hR0 : 0≤R) (j : Fin (6*N)) :
    dist (ringCircle y N R j •y) (ringCircle y N R (j+1) •y) ≤ 20*R/N+C := by
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨⟨a,k⟩,rfl⟩ := finProdFinEquiv.surjective j
  rw [product_next]
  split_ifs with h
  · rw [ringCircle_product,ringCircle_product]
    have hk : ((k.val+1:ℕ):ℝ)/N ∈ Set.Icc 0 1 := angular_parameter (⟨k.val+1,h⟩ : Fin N)
    have hh := circle_lipschitz hG y hR hchart hR0 a (angular_parameter k) hk
    have he : |(k.val:ℝ)/N-(k.val+1:ℕ)/N| = 1/N := by
      rw [abs_sub_comm]
      push_cast
      rw [← sub_div,add_sub_cancel_left,abs_div,abs_one,abs_of_pos hN]
    simpa only [he,mul_one_div] using hh
  · have hk : k.val+1=N := by omega
    rw [ringCircle_product,ringCircle_product]
    simp only [Fin.val_zero,Nat.cast_zero,zero_div,circle_zero]
    rw [← circle_one hG y hR R a]
    have hh := circle_lipschitz hG y hR hchart hR0 a (angular_parameter k)
      (by norm_num : (1:ℝ)∈Set.Icc 0 1)
    have he : |(k.val:ℝ)/N-1| = 1/N := by
      have hk' : (k.val:ℝ)+1=N := by exact_mod_cast hk
      rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (angular_parameter k).2)]
      apply (eq_div_iff hN.ne').mpr
      field_simp
      linarith
    simpa only [he,mul_one_div] using hh

end Action
end ArtinCAT0.SixSector

end OAI
