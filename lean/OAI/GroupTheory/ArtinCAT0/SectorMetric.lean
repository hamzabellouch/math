import OAI.GroupTheory.ArtinCAT0.WordDiagram

namespace OAI

namespace ArtinCAT0.SectorMetric
open Complex
abbrev Point := ℝ × ℝ

noncomputable def vec (c : ℝ) (p : Point) : ℂ :=
  (p.1 + c*p.2) + (Real.sqrt (1-c^2)*p.2)*I

@[simp] lemma vec_zero (c : ℝ) : vec c (0,0) = 0 := by simp [vec]
lemma vec_add (c : ℝ) (p q : Point) : vec c (p.1+q.1,p.2+q.2) = vec c p + vec c q := by
  simp only [vec,ofReal_add]
  ring
lemma vec_sub (c : ℝ) (p q : Point) : vec c (p.1-q.1,p.2-q.2) = vec c p - vec c q := by
  simp only [vec,ofReal_sub]
  ring
lemma vec_mul (c a : ℝ) (p : Point) : vec c (a*p.1,a*p.2) = (a : ℂ)*vec c p := by
  simp only [vec,ofReal_mul]
  ring

lemma vec_sq (c : ℝ) (hc : |c| ≤ 1) (p : Point) :
    ‖vec c p‖^2 = p.1^2+p.2^2+2*c*p.1*p.2 := by
  have hcs : 0 ≤ 1-c^2 := by nlinarith [sq_abs c,abs_nonneg c]
  rw [← Complex.normSq_eq_norm_sq]
  simp only [vec,Complex.normSq_apply,add_re,ofReal_re,mul_re,I_re,ofReal_im,I_im,
    zero_mul,mul_zero,sub_zero,add_zero,add_im,mul_im,zero_add,ofReal_im]
  nlinarith [Real.sq_sqrt hcs]

lemma vec_basis1 (c : ℝ) : ‖vec c (1,0)‖ = 1 := by simp [vec]
lemma vec_basis2 (c : ℝ) (hc : |c| ≤ 1) : ‖vec c (0,1)‖ = 1 := by
  have h := vec_sq c hc (0,1)
  have hs : ‖vec c (0,1)‖^2 = 1 := by simpa only [zero_pow (by decide : 2 ≠ 0),one_pow,mul_zero,zero_mul,zero_add,add_zero] using h
  nlinarith [norm_nonneg (vec c (0,1))]

lemma vec_bound (c : ℝ) (hc : |c| ≤ 1) (p : Point) : ‖vec c p‖ ≤ |p.1|+|p.2| := by
  have he : vec c p = (p.1 : ℂ)*vec c (1,0)+(p.2 : ℂ)*vec c (0,1) := by
    simp [vec]
    ring
  rw [he]
  calc
    _ ≤ ‖(p.1 : ℂ)*vec c (1,0)‖ + ‖(p.2 : ℂ)*vec c (0,1)‖ := norm_add_le _ _
    _ = _ := by simp [vec_basis1,vec_basis2 c hc,Complex.norm_real,Real.norm_eq_abs]

lemma vec_lipschitz (c : ℝ) (hc : |c| ≤ 1) (p q : Point) :
    |‖vec c p‖-‖vec c q‖| ≤ |p.1-q.1|+|p.2-q.2| := by
  calc
    _ ≤ ‖vec c p-vec c q‖ := abs_norm_sub_norm_le _ _
    _ = ‖vec c (p.1-q.1,p.2-q.2)‖ := congrArg norm (vec_sub c p q).symm
    _ ≤ _ := vec_bound c hc _

noncomputable def mixNorm (c t : ℝ) : ℝ := ‖vec c (1-t,t)‖
noncomputable def unit (c t : ℝ) : Point := ((1-t)/mixNorm c t,t/mixNorm c t)

lemma mixNorm_bounds {c t : ℝ} (hc : 1/2 ≤ c) (hc' : c ≤ 1) (ht : t ∈ Set.Icc 0 1) :
    1/2 ≤ mixNorm c t ∧ mixNorm c t ≤ 1 := by
  have hca : |c| ≤ 1 := abs_le.mpr ⟨by linarith,hc'⟩
  have hsq := vec_sq c hca (1-t,t)
  have hnon : 0 ≤ mixNorm c t := norm_nonneg _
  constructor
  · have hre : (vec c (1-t,t)).re = 1-t+c*t := by simp [vec]
    have hr := Complex.re_le_norm (vec c (1-t,t))
    rw [hre] at hr
    dsimp only [mixNorm]
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) ht.1]
  · have h := vec_bound c hca (1-t,t)
    simpa only [mixNorm,abs_of_nonneg ht.1,abs_of_nonneg (sub_nonneg.mpr ht.2),sub_add_cancel] using h

lemma unit_vec {c t : ℝ} (hc : 1/2 ≤ c) (hc' : c ≤ 1) (ht : t ∈ Set.Icc 0 1) :
    ‖vec c (unit c t)‖ = 1 := by
  have hm := mixNorm_bounds hc hc' ht
  have hp : 0 < mixNorm c t := by linarith
  simp only [unit,div_eq_mul_inv]
  rw [mul_comm (1-t),mul_comm t]
  rw [vec_mul c (mixNorm c t)⁻¹ (1-t,t),norm_mul]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
  exact inv_mul_cancel₀ (ne_of_gt hp)

lemma unit_nonneg {c t : ℝ} (hc : 1/2 ≤ c) (hc' : c ≤ 1) (ht : t ∈ Set.Icc 0 1) :
    0 ≤ (unit c t).1 ∧ 0 ≤ (unit c t).2 := by
  have hm := mixNorm_bounds hc hc' ht
  exact ⟨div_nonneg (sub_nonneg.mpr ht.2) (by linarith),div_nonneg ht.1 (by linarith)⟩

lemma unit_sum {c t : ℝ} (hc : 1/2 ≤ c) (hc' : c ≤ 1) (ht : t ∈ Set.Icc 0 1) :
    1 ≤ (unit c t).1+(unit c t).2 ∧ (unit c t).1+(unit c t).2 ≤ 2 := by
  have hm := mixNorm_bounds hc hc' ht
  have hp : 0 < mixNorm c t := by linarith
  change 1 ≤ (1-t)/mixNorm c t+t/mixNorm c t ∧ (1-t)/mixNorm c t+t/mixNorm c t ≤ 2
  rw [← add_div,sub_add_cancel]
  constructor
  · exact (le_div_iff₀ hp).mpr (by linarith)
  · exact (div_le_iff₀ hp).mpr (by linarith)

lemma unit_pairing1 {c t : ℝ} (hc : 1/2 ≤ c) (hc' : c ≤ 1) (ht : t ∈ Set.Icc 0 1) :
    c ≤ (unit c t).1+c*(unit c t).2 := by
  have hm := mixNorm_bounds hc hc' ht
  have hp : 0 < mixNorm c t := by linarith
  change c ≤ (1-t)/mixNorm c t+c*(t/mixNorm c t)
  rw [← mul_div_assoc,← add_div]
  apply (le_div_iff₀ hp).mpr
  have h1 : c*mixNorm c t ≤ c := mul_le_of_le_one_right (by linarith) hm.2
  nlinarith [mul_nonneg (sub_nonneg.mpr hc') (sub_nonneg.mpr ht.2)]

lemma unit_pairing2 {c t : ℝ} (hc : 1/2 ≤ c) (hc' : c ≤ 1) (ht : t ∈ Set.Icc 0 1) :
    c ≤ c*(unit c t).1+(unit c t).2 := by
  have hm := mixNorm_bounds hc hc' ht
  have hp : 0 < mixNorm c t := by linarith
  change c ≤ c*((1-t)/mixNorm c t)+t/mixNorm c t
  rw [← mul_div_assoc,← add_div]
  apply (le_div_iff₀ hp).mpr
  have h1 : c*mixNorm c t ≤ c := mul_le_of_le_one_right (by linarith) hm.2
  nlinarith [mul_nonneg (sub_nonneg.mpr hc') ht.1]

/-- The short chord needed for the outside cap, with no trigonometry. -/
lemma detour_gap {c : ℝ} (hc : 1/2 < c) (hc' : c ≤ 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ 0 < 1+r^2-2*c*r ∧
      2*Real.sqrt (1+r^2-2*c*r)+r < 2 := by
  let r := (2*c-1)/4
  have hr : 0 < r := by dsimp [r]; linarith
  have hr1 : r ≤ 1/4 := by dsimp [r]; linarith
  have hpos : 0 < 1+r^2-2*c*r := by nlinarith
  have hs := Real.sq_sqrt hpos.le
  have hn := Real.sqrt_nonneg (1+r^2-2*c*r)
  have hcR : 4*r = 2*c-1 := by dsimp [r]; ring
  refine ⟨r,hr,by linarith,hpos,?_⟩
  nlinarith

lemma quotient_lipschitz {a b u v : ℝ} (_ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hu : 1/2 ≤ u) (hv : 1/2 ≤ v) :
    |a/u-b/v| ≤ 2*|a-b|+4*|u-v| := by
  have hup : 0 < u := by linarith
  have hvp : 0 < v := by linarith
  have he : a/u-b/v = (a-b)/u+b*(v-u)/(u*v) := by field_simp; ring
  rw [he]
  calc
    _ ≤ |(a-b)/u|+|b*(v-u)/(u*v)| := abs_add_le _ _
    _ = |a-b|/u + |b| * |u-v|/(u*v) := by
      rw [abs_div,abs_div,abs_mul,abs_mul,abs_of_pos hup,abs_of_pos hvp,abs_sub_comm v u]
    _ ≤ 2*|a-b|+4*|u-v| := by
      have h1 : |a-b|/u ≤ 2*|a-b| := (div_le_iff₀ hup).mpr (by nlinarith [abs_nonneg (a-b)])
      have huv : 1/4 ≤ u*v := by nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hv)]
      have h2 : |b| * |u-v|/(u*v) ≤ 4*|u-v| :=
        (div_le_iff₀ (mul_pos hup hvp)).mpr (by nlinarith [abs_nonneg (u-v)])
      linarith

lemma mixNorm_lipschitz {c : ℝ} (hc : |c| ≤ 1) (s t : ℝ) :
    |mixNorm c s-mixNorm c t| ≤ 2*|s-t| := by
  have h := vec_lipschitz c hc (1-s,s) (1-t,t)
  have he : (1-s)-(1-t) = -(s-t) := by ring
  simpa only [mixNorm,he,abs_neg,two_mul] using h

lemma unit_lipschitz {c s t : ℝ} (hc : 1/2 ≤ c) (hc' : c ≤ 1)
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    |(unit c s).1-(unit c t).1| ≤ 10*|s-t| ∧
    |(unit c s).2-(unit c t).2| ≤ 10*|s-t| := by
  have hms := (mixNorm_bounds hc hc' hs).1
  have hmt := (mixNorm_bounds hc hc' ht).1
  have hca : |c| ≤ 1 := abs_le.mpr ⟨by linarith,hc'⟩
  have hm := mixNorm_lipschitz hca s t
  have h0 := quotient_lipschitz
    (show |1-s| ≤ 1 by rw [abs_of_nonneg (sub_nonneg.mpr hs.2)]; linarith [hs.1])
    (show |1-t| ≤ 1 by rw [abs_of_nonneg (sub_nonneg.mpr ht.2)]; linarith [ht.1]) hms hmt
  have h1 := quotient_lipschitz (show |s| ≤ 1 by simpa only [abs_of_nonneg hs.1] using hs.2)
    (show |t| ≤ 1 by simpa only [abs_of_nonneg ht.1] using ht.2) hms hmt
  have he : (1-s)-(1-t) = -(s-t) := by ring
  rw [he,abs_neg] at h0
  exact ⟨by change |(1-s)/mixNorm c s-(1-t)/mixNorm c t| ≤ _; linarith,
    by change |s/mixNorm c s-t/mixNorm c t| ≤ _; linarith⟩

@[simp] lemma unit_zero (c : ℝ) : unit c 0 = (1,0) := by simp [unit,mixNorm,vec]
@[simp] lemma unit_one (c : ℝ) (hc : |c| ≤ 1) : unit c 1 = (0,1) := by
  simp only [unit,mixNorm,sub_self,vec_basis2 c hc,div_one]

lemma chord_axis1 {c t r : ℝ} (hc : 1/2 ≤ c) (hc' : c ≤ 1)
    (ht : t ∈ Set.Icc 0 1) (hr : 0 ≤ r) :
    ‖vec c ((unit c t).1-r,(unit c t).2)‖^2 ≤ 1+r^2-2*c*r := by
  have hca : |c| ≤ 1 := abs_le.mpr ⟨by linarith,hc'⟩
  have h1 := vec_sq c hca (unit c t)
  rw [unit_vec hc hc' ht] at h1
  rw [vec_sq c hca]
  nlinarith [mul_nonneg hr (sub_nonneg.mpr (unit_pairing1 hc hc' ht))]

lemma chord_axis2 {c t r : ℝ} (hc : 1/2 ≤ c) (hc' : c ≤ 1)
    (ht : t ∈ Set.Icc 0 1) (hr : 0 ≤ r) :
    ‖vec c ((unit c t).1,(unit c t).2-r)‖^2 ≤ 1+r^2-2*c*r := by
  have hca : |c| ≤ 1 := abs_le.mpr ⟨by linarith,hc'⟩
  have h1 := vec_sq c hca (unit c t)
  rw [unit_vec hc hc' ht] at h1
  rw [vec_sq c hca]
  nlinarith [mul_nonneg hr (sub_nonneg.mpr (unit_pairing2 hc hc' ht))]

end ArtinCAT0.SectorMetric

namespace ArtinCAT0
section PairingCauchy
variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]
  [ProperSpace X] [Nonempty X]

lemma lengthPairing_abs_le (hG : GeometricAction G X) (y : X) {g h : G} (hc : Commute g h) :
    |lengthPairing y g h| ≤ stableLengthAt y g * stableLengthAt y h := by
  by_cases hz : stableLengthAt y g = 0
  · rw [hz,zero_mul,lengthPairing_zero_of_length_zero hG.1 hG.2.1 y hc hz,abs_zero]
  · have hp : 0 < stableLengthAt y g := lt_of_le_of_ne (stableLength_nonneg hG.2.1 y g) (Ne.symm hz)
    obtain ⟨x,hx⟩ := exists_displacement_minimizer hG g
    have hxL : dist x (g • x) = stableLengthAt y g := by
      rw [← stableLength_minimizer hG.1 hG.2.1 g hx]
      exact stableLength_basepoint hG.2.1 x y g
    have ha (n : ℕ) : dist x ((g^n) • x) = n*stableLengthAt y g := by
      rw [minimizer_displacement_pow hG.1 hG.2.1 g hx,hxL]
    rw [← lengthPairing_basepoint hG.2.1 x y g h,
      lengthPairing_eq_orbitCharacter hG.1 hG.2.1 x g _ hp ha
        (stableLength_basepoint hG.2.1 x y g) hc,abs_mul,abs_of_pos hp]
    rw [← stableLength_basepoint hG.2.1 x y h]
    exact mul_le_mul_of_nonneg_left (orbitCharacter_abs_le hG.1 hG.2.1 x g _ hp ha hc) hp.le

end PairingCauchy

section BraidThree
variable {G : Type*} [Group G] {a b : G}

def twoBraid (a b : G) (i : ℕ) : G := if i = 0 then a else b
lemma twoBraid_relations (h : a*b*a = b*a*b) : BraidRelations 2 (twoBraid a b) := by
  constructor
  · intro i hi
    have he : i = 0 := by omega
    subst i
    simpa [twoBraid] using h
  · intro i j hi hj hij
    omega

lemma braid_three_commute (h : a*b*a = b*a*b) : Commute a ((a*b)^3) ∧ Commute b ((a*b)^3) := by
  have hc (i : ℕ) (hi : i < 2) := braidCenter_commute (twoBraid_relations h) (by omega : 2 ≤ 2) hi
  have he : braidCenter (twoBraid a b) 2 = (a*b)^3 := by
    simpa [twoBraid] using braidCenter_two (s := twoBraid a b) (by simpa [twoBraid] using h)
  exact ⟨by simpa [he,twoBraid] using hc 0 (by decide),
    by simpa [he,twoBraid] using hc 1 (by decide)⟩

variable {X : Type*} [MetricSpace X] [MulAction G X] [ProperSpace X] [Nonempty X]
lemma braid_three_pairing (hG : GeometricAction G X) (y : X) (h : a*b*a = b*a*b) :
    lengthPairing y (a^2) ((a*b)^3) = stableLengthAt y ((a*b)^3)^2/3 ∧
    lengthPairing y (b^2) ((a*b)^3) = stableLengthAt y ((a*b)^3)^2/3 := by
  have hs := twoBraid_relations h
  have he : braidCenter (twoBraid a b) 2 = (a*b)^3 := by
    simpa [twoBraid] using braidCenter_two (s := twoBraid a b) (by simpa [twoBraid] using h)
  have h0 := braidCenter_length_sq hG y hs (by omega : 2 ≤ 2) (by decide : 0 < 2)
  have h1 := braidCenter_length_sq hG y hs (by omega : 2 ≤ 2) (by decide : 1 < 2)
  simp only [he,twoBraid,ite_true,show ¬(1 = (0 : ℕ)) by decide,ite_false] at h0 h1
  have hc := braid_three_commute h
  rw [lengthPairing_pow_left hG.1 hG.2.1 y hc.1,
    lengthPairing_pow_left hG.1 hG.2.1 y hc.2]
  norm_num at h0 h1 ⊢
  constructor <;> linarith
end BraidThree

namespace SixSector

def ray (i : Fin 6) : TriangleGroup :=
  if i.val % 2 = 0 then triangleGen ⟨i.val/2,by omega⟩ ^ 2
    else triangleH ⟨i.val/2,by omega⟩ ^ 3

lemma ray_even (i : Fin 3) : ray ⟨2*i.val,by omega⟩ = triangleGen i ^ 2 := by
  simp only [ray,Nat.mul_mod_right,ite_true]
  congr 2
  apply Fin.ext
  change 2*i.val/2 = i.val
  omega
lemma ray_odd (i : Fin 3) : ray ⟨2*i.val+1,by omega⟩ = triangleH i ^ 3 := by
  simp only [ray,show (2*i.val+1)%2 = 1 by omega,show ¬(1 = (0 : ℕ)) by decide,ite_false]
  congr 2
  apply Fin.ext
  change (2*i.val+1)/2 = i.val
  omega

lemma ray_commute (i : Fin 6) : Commute (ray i) (ray (i+1)) := by
  have h0 := braid_three_commute (triangle_braid 0)
  have h1 := braid_three_commute (triangle_braid 1)
  have h2 := braid_three_commute (triangle_braid 2)
  fin_cases i
  · exact h0.1.pow_left 2
  · exact (h0.2.pow_left 2).symm
  · exact h1.1.pow_left 2
  · exact (h1.2.pow_left 2).symm
  · exact h2.1.pow_left 2
  · exact (h2.2.pow_left 2).symm

section Action
variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X] [ProperSpace X] [Nonempty X]

lemma generator_square_length_pos (hG : GeometricAction TriangleGroup X) (y : X) (i : Fin 3) :
    0 < stableLengthAt y (triangleGen i ^ 2) := by
  have hp : 0 < stableLengthAt y (triangleGen i) := by
    apply lt_of_le_of_ne (stableLength_nonneg hG.2.1 y _)
    intro h
    exact triangle_generator_infinite_order i ((stableLength_eq_zero_iff_finiteOrder hG y _).mp h.symm)
  rw [stableLength_pow hG.2.1]
  positivity

omit [ProperSpace X] [Nonempty X] in
lemma adjacent_square_length (hG : GeometricAction TriangleGroup X) (y : X) (i : Fin 3) :
    stableLengthAt y (triangleGen (i+1)^2) = stableLengthAt y (triangleGen i^2) := by
  rw [stableLength_pow hG.2.1,stableLength_pow hG.2.1,← braid_conjugate (triangle_braid i),
    stableLength_conjugate hG.2.1]

def StrictRatios (y : X) : Prop := ∀ i : Fin 3,
  (1 : ℝ)/2 < stableLengthAt y (triangleH i^3)/(3*stableLengthAt y (triangleGen i^2))

lemma ray_length_pos (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y) (i : Fin 6) :
    0 < stableLengthAt y (ray i) := by
  have he k := generator_square_length_pos hG y k
  have ho k : 0 < stableLengthAt y (triangleH k^3) := by
    have h := (lt_div_iff₀ (mul_pos (by norm_num) (generator_square_length_pos hG y k) : 0 < 3*stableLengthAt y (triangleGen k^2))).mp (hR k)
    linarith [he k]
  fin_cases i
  · exact he 0
  · exact ho 0
  · exact he 1
  · exact ho 1
  · exact he 2
  · exact ho 2

noncomputable def cosine (y : X) (i : Fin 6) : ℝ :=
  lengthPairing y (ray i) (ray (i+1))/(stableLengthAt y (ray i)*stableLengthAt y (ray (i+1)))

lemma cosine_lower (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y) (i : Fin 6) :
    1/2 < cosine y i := by
  have hL k := ray_length_pos hG y hR k
  have hc (k : Fin 3) :
      lengthPairing y (triangleGen k^2) (triangleH k^3) = stableLengthAt y (triangleH k^3)^2/3 ∧
      lengthPairing y (triangleGen (k+1)^2) (triangleH k^3) = stableLengthAt y (triangleH k^3)^2/3 :=
    braid_three_pairing hG y (triangle_braid k)
  have hcomm (k : Fin 3) : Commute (triangleH k^3) (triangleGen (k+1)^2) :=
    ((braid_three_commute (triangle_braid k)).2.pow_left 2).symm
  have hp (k : Fin 3) : 3*stableLengthAt y (triangleGen k^2)/2 < stableLengthAt y (triangleH k^3) := by
    have h := (lt_div_iff₀ (mul_pos (by norm_num) (generator_square_length_pos hG y k) : 0 < 3*stableLengthAt y (triangleGen k^2))).mp (hR k)
    linarith
  have hnext k := adjacent_square_length hG y k
  unfold cosine
  apply (lt_div_iff₀ (mul_pos (hL i) (hL (i+1)))).mpr
  have hpair (k : Fin 3) :
      stableLengthAt y (triangleGen k^2)*stableLengthAt y (triangleH k^3)/2 <
        stableLengthAt y (triangleH k^3)^2/3 := by
    have hz := ray_length_pos hG y hR ⟨2*k.val+1,by omega⟩
    rw [ray_odd] at hz
    nlinarith [mul_pos (sub_pos.mpr (hp k)) hz]
  fin_cases i
  · change 1/2*(stableLengthAt y (triangleGen 0^2)*stableLengthAt y (triangleH 0^3)) <
      lengthPairing y (triangleGen 0^2) (triangleH 0^3)
    rw [(hc 0).1]
    linarith [hpair 0]
  · change 1/2*(stableLengthAt y (triangleH 0^3)*stableLengthAt y (triangleGen (0+1)^2)) <
      lengthPairing y (triangleH 0^3) (triangleGen (0+1)^2)
    rw [lengthPairing_symmetric y (hcomm 0),
      (hc 0).2,hnext 0]
    nlinarith [hpair 0]
  · change 1/2*(stableLengthAt y (triangleGen 1^2)*stableLengthAt y (triangleH 1^3)) <
      lengthPairing y (triangleGen 1^2) (triangleH 1^3)
    rw [(hc 1).1]
    linarith [hpair 1]
  · change 1/2*(stableLengthAt y (triangleH 1^3)*stableLengthAt y (triangleGen (1+1)^2)) <
      lengthPairing y (triangleH 1^3) (triangleGen (1+1)^2)
    rw [lengthPairing_symmetric y (hcomm 1),
      (hc 1).2,hnext 1]
    nlinarith [hpair 1]
  · change 1/2*(stableLengthAt y (triangleGen 2^2)*stableLengthAt y (triangleH 2^3)) <
      lengthPairing y (triangleGen 2^2) (triangleH 2^3)
    rw [(hc 2).1]
    linarith [hpair 2]
  · change 1/2*(stableLengthAt y (triangleH 2^3)*stableLengthAt y (triangleGen (2+1)^2)) <
      lengthPairing y (triangleH 2^3) (triangleGen (2+1)^2)
    rw [lengthPairing_symmetric y (hcomm 2),
      (hc 2).2,hnext 2]
    nlinarith [hpair 2]

lemma cosine_le_one (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y) (i : Fin 6) :
    cosine y i ≤ 1 := by
  apply (div_le_iff₀ (mul_pos (ray_length_pos hG y hR i) (ray_length_pos hG y hR (i+1)))).mpr
  simpa only [one_mul] using
    (le_abs_self (lengthPairing y (ray i) (ray (i+1)))).trans (lengthPairing_abs_le hG y (ray_commute i))

end Action
end SixSector
end ArtinCAT0

namespace ArtinCAT0.SectorMetric

lemma floor_error {L : ℝ} (hL : 0<L) (x : ℝ) :
    |(⌊x/L⌋ : ℝ)*L-x| ≤ L := by
  have h1 : (⌊x/L⌋ : ℝ) ≤ x/L := Int.floor_le _
  have h2 : x/L < (⌊x/L⌋ : ℝ)+1 := Int.lt_floor_add_one _
  have h3 := (le_div_iff₀ hL).mp h1
  have h4 := (div_lt_iff₀ hL).mp h2
  rw [abs_of_nonpos (by linarith)]
  nlinarith

variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]
  [ProperSpace X] [Nonempty X]

noncomputable def lattice (g h : G) (L M : ℝ) (p : Point) : G :=
  g^⌊p.1/L⌋ * h^⌊p.2/M⌋

lemma lattice_origin (g h : G) (L M : ℝ) : lattice g h L M (0,0) = 1 := by
  simp [lattice]

lemma powers_difference {g h : G} (hc : Commute g h) (i j k l : ℤ) :
    (g^i*h^j)⁻¹*(g^k*h^l) = g^(k-i)*h^(l-j) := by
  calc
    _ = h^(-j) * g^(k-i) * h^l := by simp only [zpow_sub,zpow_neg]; group
    _ = g^(k-i) * h^(-j) * h^l := by rw [(hc.zpow_zpow (k-i) (-j)).eq]
    _ = _ := by simp only [zpow_sub,zpow_neg]; group

omit [ProperSpace X] [Nonempty X] in
lemma lattice_length (hG : GeometricAction G X) (y : X) {g h : G}
    (hcomm : Commute g h) {c : ℝ} (hc : |c| ≤ 1)
    (hp : lengthPairing y g h = c*stableLengthAt y g*stableLengthAt y h) (i j : ℤ) :
    stableLengthAt y (g^i*h^j) =
      ‖vec c ((i:ℝ)*stableLengthAt y g,(j:ℝ)*stableLengthAt y h)‖ := by
  have he := stableLength_product_sq y (g^i) (h^j)
  rw [stableLength_zpow hG.2.1,stableLength_zpow hG.2.1,
    lengthPairing_zpow_left hG.1 hG.2.1 y (hcomm.zpow_right j),
    lengthPairing_zpow_right hG.1 hG.2.1 y hcomm,hp] at he
  have hv := vec_sq c hc ((i:ℝ)*stableLengthAt y g,(j:ℝ)*stableLengthAt y h)
  have hsq : stableLengthAt y (g^i*h^j)^2 =
      ‖vec c ((i:ℝ)*stableLengthAt y g,(j:ℝ)*stableLengthAt y h)‖^2 := by
    rw [he,hv]
    simp only [mul_pow,sq_abs]
    ring
  nlinarith [stableLength_nonneg hG.2.1 y (g^i*h^j),
    norm_nonneg (vec c ((i:ℝ)*stableLengthAt y g,(j:ℝ)*stableLengthAt y h))]

/-- Rounding a flat-coordinate lattice introduces a bounded additive metric
error, uniformly for all pairs of real points, not just a fixed finite net. -/
theorem lattice_metric (hG : GeometricAction G X) (y : X) {g h : G}
    (hg : 0<stableLengthAt y g) (hh : 0<stableLengthAt y h) (hcomm : Commute g h)
    {c : ℝ} (hc : |c|≤1)
    (hp : lengthPairing y g h = c*stableLengthAt y g*stableLengthAt y h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p q : Point,
      |dist (lattice g h (stableLengthAt y g) (stableLengthAt y h) p • y)
          (lattice g h (stableLengthAt y g) (stableLengthAt y h) q • y) -
        ‖vec c (q.1-p.1,q.2-p.2)‖| ≤ C := by
  obtain ⟨C,hC,hbound⟩ := commuting_orbit_uniform hG y hcomm
  let L := stableLengthAt y g
  let M := stableLengthAt y h
  refine ⟨C+2*L+2*M,by dsimp [L,M]; positivity,?_⟩
  intro p q
  let i := ⌊p.1/L⌋; let j := ⌊p.2/M⌋
  let k := ⌊q.1/L⌋; let l := ⌊q.2/M⌋
  have h0 := hbound (k-i) (l-j)
  rw [lattice_length hG y hcomm hc hp] at h0
  have h1 := vec_lipschitz c hc (((k-i:ℤ):ℝ)*L,((l-j:ℤ):ℝ)*M) (q.1-p.1,q.2-p.2)
  have hx : |((k-i:ℤ):ℝ)*L-(q.1-p.1)| ≤ 2*L := by
    have hpi := floor_error hg p.1
    have hqk := floor_error hg q.1
    have he : ((k-i:ℤ):ℝ)*L-(q.1-p.1) = ((k:ℝ)*L-q.1)-((i:ℝ)*L-p.1) := by
      rw [Int.cast_sub]; ring
    rw [he]
    exact (abs_sub _ _).trans (by dsimp [i,k,L] at *; linarith)
  have hy : |((l-j:ℤ):ℝ)*M-(q.2-p.2)| ≤ 2*M := by
    have hpj := floor_error hh p.2
    have hql := floor_error hh q.2
    have he : ((l-j:ℤ):ℝ)*M-(q.2-p.2) = ((l:ℝ)*M-q.2)-((j:ℝ)*M-p.2) := by
      rw [Int.cast_sub]; ring
    rw [he]
    exact (abs_sub _ _).trans (by dsimp [j,l,M] at *; linarith)
  rw [action_dist hG.2.1]
  change |dist y (((g^i*h^j)⁻¹*(g^k*h^l)) • y)-_| ≤ _
  rw [powers_difference hcomm]
  calc
    _ ≤ |dist y ((g^(k-i)*h^(l-j)) • y)-‖vec c (((k-i:ℤ):ℝ)*L,((l-j:ℤ):ℝ)*M)‖| +
        |‖vec c (((k-i:ℤ):ℝ)*L,((l-j:ℤ):ℝ)*M)‖-‖vec c (q.1-p.1,q.2-p.2)‖| :=
      abs_sub_le _ _ _
    _ ≤ _ := by dsimp only [L,M] at *; linarith

end ArtinCAT0.SectorMetric

end OAI
