import OAI.Combinatorics.Coboundary.Links

namespace OAI

/-!
Rank-two incidence geometry, weighted Rayleigh inequalities, and spectral bounds for links.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.RankTwoGeometry

section
open MatrixOpposition TypedCosetFaces Elementary
open scoped Matrix
variable {K : Type} [Field K]

def matrix3 (a b c : K) : Matrix (Fin 3) (Fin 3) K := !![1,a,c; 0,1,b; 0,0,1]
lemma matrix3_det (a b c : K) : (matrix3 a b c).det = 1 := by
  simp [matrix3,Matrix.det_fin_three]
def upper3 (a b c : K) : upperGroup K 3 :=
  ⟨⟨matrix3 a b c,matrix3_det a b c⟩,by
    apply (mem_upperGroup _).mpr
    intro i j hji
    fin_cases i <;> fin_cases j <;> norm_num [matrix3,Matrix.one_apply,Fin.le_iff_val_le_val] at *⟩

def ca (g : upperGroup K 3) : K := g.val 0 1
def cb (g : upperGroup K 3) : K := g.val 1 2
def cc (g : upperGroup K 3) : K := g.val 0 2

@[simp] lemma ca_upper3 (a b c : K) : ca (upper3 a b c) = a := rfl
@[simp] lemma cb_upper3 (a b c : K) : cb (upper3 a b c) = b := rfl
@[simp] lemma cc_upper3 (a b c : K) : cc (upper3 a b c) = c := rfl

lemma upper3_coords (g : upperGroup K 3) : upper3 (ca g) (cb g) (cc g) = g := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hg := (mem_upperGroup g.val).mp g.property
  change matrix3 (ca g) (cb g) (cc g) i j = g.val i j
  fin_cases i <;> fin_cases j <;>
    first | rfl | rw [hg _ _ (by decide)]; rfl

@[ext] lemma upper_ext {g h : upperGroup K 3}
    (ha : ca g = ca h) (hb : cb g = cb h) (hc : cc g = cc h) : g = h := by
  rw [←upper3_coords g,←upper3_coords h,ha,hb,hc]

lemma upper3_mul (a b c a' b' c' : K) :
    upper3 a b c * upper3 a' b' c' = upper3 (a+a') (b+b') (c+c'+a*b') := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change (matrix3 a b c * matrix3 a' b' c') i j = matrix3 (a+a') (b+b') (c+c'+a*b') i j
  fin_cases i <;> fin_cases j <;> simp [matrix3,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring

@[simp] lemma ca_mul (g h : upperGroup K 3) : ca (g*h) = ca g+ca h := by
  rw [←upper3_coords g,←upper3_coords h,upper3_mul]; rfl
@[simp] lemma cb_mul (g h : upperGroup K 3) : cb (g*h) = cb g+cb h := by
  rw [←upper3_coords g,←upper3_coords h,upper3_mul]; rfl
@[simp] lemma cc_mul (g h : upperGroup K 3) : cc (g*h) = cc g+cc h+ca g*cb h := by
  rw [←upper3_coords g,←upper3_coords h,upper3_mul]; rfl
@[simp] lemma ca_one : ca (1 : upperGroup K 3) = 0 := by simp [ca]
@[simp] lemma cb_one : cb (1 : upperGroup K 3) = 0 := by simp [cb]
@[simp] lemma cc_one : cc (1 : upperGroup K 3) = 0 := by simp [cc]
@[simp] lemma ca_inv (g : upperGroup K 3) : ca g⁻¹ = -ca g := by
  have h := ca_mul g⁻¹ g
  simp only [inv_mul_cancel,ca_one] at h
  linear_combination -h
@[simp] lemma cb_inv (g : upperGroup K 3) : cb g⁻¹ = -cb g := by
  have h := cb_mul g⁻¹ g
  simp only [inv_mul_cancel,cb_one] at h
  linear_combination -h
@[simp] lemma cc_inv (g : upperGroup K 3) : cc g⁻¹ = -cc g+ca g*cb g := by
  have h := cc_mul g⁻¹ g
  simp only [inv_mul_cancel,cc_one,ca_inv] at h
  linear_combination -h

def pointCut : Cut 3 := ⟨2,by decide⟩
def lineCut : Cut 3 := ⟨1,by decide⟩
lemma mem_pointGroup (g : upperGroup K 3) :
    g ∈ cutGroups K 3 pointCut ↔ cb g = 0 ∧ cc g = 0 := by
  simp only [cutGroups,mem_suffixGroup,pointCut]
  refine ⟨fun h => ⟨h 1 2 (by decide) (by decide), h 0 2 (by decide) (by decide)⟩,?_⟩
  rintro ⟨hb,hc⟩ i j hi hj
  fin_cases i <;> fin_cases j <;> simp_all [cb,cc]
lemma mem_lineGroup (g : upperGroup K 3) :
    g ∈ cutGroups K 3 lineCut ↔ ca g = 0 ∧ cc g = 0 := by
  simp only [cutGroups,mem_suffixGroup,lineCut]
  refine ⟨fun h => ⟨h 0 1 (by decide) (by decide), h 0 2 (by decide) (by decide)⟩,?_⟩
  rintro ⟨ha,hc⟩ i j hi hj
  fin_cases i <;> fin_cases j <;> simp_all [ca,cc]

lemma point_rel (g h : upperGroup K 3) :
    g⁻¹*h ∈ cutGroups K 3 pointCut ↔ cb g = cb h ∧ cc g = cc h := by
  rw [mem_pointGroup]; simp only [cb_mul,cb_inv,cc_mul,cc_inv,ca_inv]
  constructor
  · rintro ⟨hb,hc⟩
    have he : cb g = cb h := by linear_combination -hb
    refine ⟨he,?_⟩
    rw [he] at hc
    linear_combination -hc
  · rintro ⟨hb,hc⟩; rw [hb,hc]; constructor <;> ring
lemma line_rel (g h : upperGroup K 3) :
    g⁻¹*h ∈ cutGroups K 3 lineCut ↔
      ca g = ca h ∧ cc g-ca g*cb g = cc h-ca h*cb h := by
  rw [mem_lineGroup]; simp only [ca_mul,ca_inv,cc_mul,cc_inv]
  constructor
  · rintro ⟨ha,hc⟩
    have he : ca g = ca h := by linear_combination -ha
    refine ⟨he,?_⟩
    rw [he] at hc ⊢
    linear_combination -hc
  · rintro ⟨ha,hc⟩; rw [ha]; constructor
    · ring
    · rw [ha] at hc; linear_combination -hc

end

open MatrixOpposition TypedCosetFaces InfiniteChains Cone
variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq _

abbrev Vert (K : Type) := (K × K) ⊕ (K × K)

def cosetVertex : Vert K → Vertex (cutGroups K 3)
  | .inl P => vertex (cutGroups K 3) (upper3 0 P.1 P.2) pointCut
  | .inr L => vertex (cutGroups K 3) (upper3 L.1 0 L.2) lineCut

lemma point_vertex (g : upperGroup K 3) :
    cosetVertex (.inl (cb g,cc g)) = vertex (cutGroups K 3) g pointCut := by
  dsimp only [cosetVertex,vertex]
  apply congrArg (Sigma.mk _)
  apply Quotient.sound
  apply QuotientGroup.leftRel_apply.mpr
  exact (point_rel _ _).mpr ⟨rfl,rfl⟩
lemma line_vertex (g : upperGroup K 3) :
    cosetVertex (.inr (ca g,cc g-ca g*cb g)) = vertex (cutGroups K 3) g lineCut := by
  dsimp only [cosetVertex,vertex]
  apply congrArg (Sigma.mk _)
  apply Quotient.sound
  apply QuotientGroup.leftRel_apply.mpr
  apply (line_rel _ _).mpr
  simp

lemma cuts3 (i : Cut 3) : i = pointCut ∨ i = lineCut := by
  have hi := i.property
  by_cases h : i.val = 2
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext (by dsimp [lineCut]; omega))

lemma cosetVertex_injective : Function.Injective (cosetVertex (K:=K)) := by
  intro x y h
  cases x with
  | inl P =>
    cases y with
    | inl Q =>
      have hh := QuotientGroup.leftRel_apply.mp
        (Quotient.exact (eq_of_heq (Sigma.mk.inj_iff.mp h).2))
      have he := (point_rel _ _).mp hh
      congr 1
      exact Prod.ext he.1 he.2
    | inr L =>
      have he := congrArg (fun v => v.1.val) h
      norm_num [cosetVertex,vertex,pointCut,lineCut] at he
  | inr L =>
    cases y with
    | inl P =>
      have he := congrArg (fun v => v.1.val) h
      norm_num [cosetVertex,vertex,pointCut,lineCut] at he
    | inr M =>
      have hh := QuotientGroup.leftRel_apply.mp
        (Quotient.exact (eq_of_heq (Sigma.mk.inj_iff.mp h).2))
      have he := (line_rel _ _).mp hh
      congr 1
      apply Prod.ext he.1
      simpa using he.2

lemma cosetVertex_surjective : Function.Surjective (cosetVertex (K:=K)) := by
  rintro ⟨i,q⟩
  induction q using Quotient.inductionOn with | h g =>
  rcases cuts3 i with rfl | rfl
  · exact ⟨.inl (cb g,cc g),point_vertex g⟩
  · exact ⟨.inr (ca g,cc g-ca g*cb g),line_vertex g⟩

def vertexEquiv : Vert K ≃ Vertex (cutGroups K 3) :=
  Equiv.ofBijective cosetVertex ⟨cosetVertex_injective,cosetVertex_surjective⟩

def incident (P L : K × K) : Prop := P.2 = L.1*P.1+L.2

def incidenceComplex (K : Type) [Field K] : CoboundaryExpanders.InfiniteChains.Complex (Vert K) where
  faces := {s | ∃ P L : K×K, incident P L ∧ s ⊆ {Sum.inl P,Sum.inr L}}
  empty_mem := ⟨(0,0),(0,0),by simp [incident],Finset.empty_subset _⟩
  downward := by
    rintro s t ⟨P,L,hPL,hs⟩ ht
    exact ⟨P,L,hPL,ht.trans hs⟩

lemma fullFace (g : upperGroup K 3) :
    ({Sum.inl (cb g,cc g),Sum.inr (ca g,cc g-ca g*cb g)} : Finset (Vert K)).image cosetVertex =
      face (cutGroups K 3) g {pointCut,lineCut} := by
  simp only [Finset.image_insert,Finset.image_singleton,point_vertex,line_vertex,face]

lemma face_subset_fullFace (g : upperGroup K 3) (A : Finset (Cut 3)) :
    face (cutGroups K 3) g A ⊆ face (cutGroups K 3) g {pointCut,lineCut} := by
  apply Finset.image_subset_image
  intro i _
  rcases cuts3 i with rfl | rfl <;> simp

lemma cosetVertex_face_iff (s : Finset (Vert K)) :
    s.image cosetVertex ∈ (TypedCosetFaces.complex (cutGroups K 3)).faces ↔
      s ∈ (incidenceComplex K).faces := by
  constructor
  · rintro ⟨g,A,hg⟩
    refine ⟨(cb g,cc g),(ca g,cc g-ca g*cb g),?_,?_⟩
    · dsimp [incident]; ring
    · apply (Finset.image_subset_image_iff cosetVertex_injective).mp
      rw [fullFace,←hg]
      exact face_subset_fullFace g A
  · rintro ⟨P,L,hPL,hs⟩
    have he : (ca (upper3 L.1 P.1 P.2),cc (upper3 L.1 P.1 P.2)-
        ca (upper3 L.1 P.1 P.2)*cb (upper3 L.1 P.1 P.2)) = L := by
      apply Prod.ext
      · rfl
      · change P.2-L.1*P.1 = L.2
        rw [hPL]; ring
    have hf := fullFace (upper3 L.1 P.1 P.2)
    simp only [ca_upper3,cb_upper3,cc_upper3] at he hf
    rw [he] at hf
    apply IsFace.downward (H:=cutGroups K 3) ⟨_,_,rfl⟩
    rw [←hf]
    exact Finset.image_subset_image hs

def incidenceModel : FaceModel (incidenceComplex K) (TypedCosetFaces.complex (cutGroups K 3)) where
  vertex := cosetVertex
  injective := cosetVertex_injective
  face_iff := cosetVertex_face_iff
  cover := by
    intro t ht
    let s := t.image vertexEquiv.symm
    have he : s.image cosetVertex = t := by
      change s.image vertexEquiv = t
      simp only [s,Finset.image_image,Function.comp_def,Equiv.apply_symm_apply,Finset.image_id']
    exact ⟨s,by rwa [←cosetVertex_face_iff,he],he⟩

end CoboundaryExpanders.RankTwoGeometry

namespace CoboundaryExpanders.RankTwo
variable {K : Type} [Field K] [Fintype K]
local instance : DecidableEq K := Classical.decEq _

def lineSum (f : K → K → ℝ) (a b : K) : ℝ := ∑ x, f x (a*x+b)
def pointSum (g : K → K → ℝ) (x y : K) : ℝ := ∑ a, g a (y-a*x)
def energy (f : K → K → ℝ) : ℝ := ∑ x, ∑ y, (f x y)^2

def pairing (f g : K → K → ℝ) : ℝ := ∑ x, ∑ y, f x y * g x y

omit [Field K] in
lemma energy_nonneg (f : K → K → ℝ) : 0 ≤ energy f := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma affine_sum (x y x' : K) (h : x' ≠ x) (f : K → ℝ) :
    ∑ a, f (a*x'+(y-a*x)) = ∑ z, f z := by
  let e := (Equiv.mulRight₀ (x'-x) (sub_ne_zero.mpr h)).trans (Equiv.addRight y)
  apply Fintype.sum_equiv e
  intro a
  congr 1
  change a*x'+(y-a*x) = a*(x'-x)+y
  ring

lemma adjoint (f g : K → K → ℝ) : pairing (lineSum f) g = pairing f (pointSum g) := by
  unfold pairing lineSum pointSum
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Fintype.sum_equiv (Equiv.addLeft (a*x))
  intro b
  simp

lemma gram (f : K → K → ℝ) (x y : K) :
    pointSum (lineSum f) x y =
      (Fintype.card K : ℝ) * f x y + ∑ x' ∈ Finset.univ.erase x, ∑ y', f x' y' := by
  classical
  unfold pointSum lineSum
  rw [Finset.sum_comm, ← Finset.sum_erase_add _ _ (Finset.mem_univ x)]
  have he (x' : K) (hx' : x' ∈ Finset.univ.erase x) :
      ∑ a, f x' (a*x'+(y-a*x)) = ∑ y', f x' y' :=
    affine_sum x y x' (Finset.mem_erase.mp hx').1 (f x')
  rw [Finset.sum_congr rfl he]
  have hy (a : K) : a*x+(y-a*x) = y := by ring
  simp only [hy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

lemma gram_mean_zero (f : K → K → ℝ) (hf : ∑ x, ∑ y, f x y = 0) (x y : K) :
    pointSum (lineSum f) x y = (Fintype.card K : ℝ) * f x y - ∑ y', f x y' := by
  classical
  rw [gram]
  have h := Finset.sum_erase_add Finset.univ (fun x => ∑ y, f x y) (Finset.mem_univ x)
  rw [hf] at h
  linarith

omit [Field K] in
lemma energy_eq_pairing (f : K → K → ℝ) : energy f = pairing f f := by
  simp only [energy, pairing, pow_two]

theorem incidence_energy_identity (f : K → K → ℝ) (hf : ∑ x, ∑ y, f x y = 0) :
    energy (lineSum f) = (Fintype.card K : ℝ) * energy f - ∑ x, (∑ y, f x y)^2 := by
  rw [energy_eq_pairing, adjoint]
  simp only [pairing, gram_mean_zero f hf, mul_sub, Finset.sum_sub_distrib]
  simp only [← Finset.sum_mul]
  have h (x : K) : ∑ y, f x y * ((Fintype.card K : ℝ) * f x y) =
      (Fintype.card K : ℝ) * ∑ y, (f x y)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  simp only [h, ← Finset.mul_sum, ← pow_two, energy]

theorem incidence_energy_bound (f : K → K → ℝ) (hf : ∑ x, ∑ y, f x y = 0) :
    energy (lineSum f) ≤ (Fintype.card K : ℝ) * energy f := by
  rw [incidence_energy_identity f hf]
  have : 0 ≤ ∑ x, (∑ y, f x y)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

omit [Field K] in
lemma pairing_sq_le (f g : K → K → ℝ) : pairing f g ^ 2 ≤ energy f * energy g := by
  simpa only [Fintype.sum_prod_type, pairing, energy] using
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (K × K))
      (fun z => f z.1 z.2) (fun z => g z.1 z.2)

theorem incidence_pairing_bound (f g : K → K → ℝ) (hf : ∑ x, ∑ y, f x y = 0) :
    pairing (lineSum f) g ^ 2 ≤ (Fintype.card K : ℝ) * energy f * energy g := by
  exact (pairing_sq_le (lineSum f) g).trans
    (mul_le_mul_of_nonneg_right (incidence_energy_bound f hf) (energy_nonneg g))

def total (f : K → K → ℝ) : ℝ := ∑ x, ∑ y, f x y

def center (f : K → K → ℝ) (x y : K) : ℝ :=
  f x y - total f / (Fintype.card K : ℝ)^2

lemma card_pos : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos

lemma total_center (f : K → K → ℝ) : total (center f) = 0 := by
  have hq := card_pos (K := K)
  simp only [total, center, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

lemma energy_center (f : K → K → ℝ) :
    energy (center f) = energy f - (total f)^2 / (Fintype.card K : ℝ)^2 := by
  have hq := card_pos (K := K)
  have he (x y : K) : (center f x y)^2 = (f x y)^2 -
      (2 * total f / (Fintype.card K : ℝ)^2) * f x y +
      (total f / (Fintype.card K : ℝ)^2)^2 := by unfold center; ring
  simp only [energy, he, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change energy f - (2*total f/(Fintype.card K : ℝ)^2)*total f +
    (Fintype.card K : ℝ)*((Fintype.card K : ℝ)*(total f/(Fintype.card K : ℝ)^2)^2) = _
  unfold energy
  field_simp
  ring

lemma energy_center_le (f : K → K → ℝ) : energy (center f) ≤ energy f := by
  rw [energy_center]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (sq_nonneg _))

lemma total_lineSum (f : K → K → ℝ) :
    total (lineSum f) = (Fintype.card K : ℝ) * total f := by
  unfold total lineSum
  calc
    (∑ a, ∑ b, ∑ x, f x (a*x+b)) = ∑ a, ∑ x, ∑ b, f x (a*x+b) := by
      apply Finset.sum_congr rfl; intro a _; exact Finset.sum_comm
    _ = ∑ a : K, ∑ x, ∑ y, f x y := by
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro x _
      exact Equiv.sum_comp (Equiv.addLeft (a*x)) (f x)
    _ = _ := by simp

lemma lineSum_center (f : K → K → ℝ) (a b : K) :
    lineSum (center f) a b = lineSum f a b - total f / (Fintype.card K : ℝ) := by
  have hq := card_pos (K := K)
  simp only [lineSum, center, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  congr 1
  field_simp

lemma incidence_center (f g : K → K → ℝ) :
    pairing (lineSum (center f)) (center g) =
      pairing (lineSum f) g - total f * total g / (Fintype.card K : ℝ) := by
  have hq := card_pos (K := K)
  have he (a b : K) : lineSum (center f) a b * center g a b =
      lineSum f a b * g a b - (total g / (Fintype.card K : ℝ)^2) * lineSum f a b -
      (total f / (Fintype.card K : ℝ)) * g a b +
      total f * total g / (Fintype.card K : ℝ)^3 := by
    rw [lineSum_center]
    unfold center
    field_simp
    ring
  simp only [pairing, he, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change pairing (lineSum f) g - (total g / (Fintype.card K : ℝ)^2)*total (lineSum f) -
    (total f / (Fintype.card K : ℝ))*total g +
    (Fintype.card K : ℝ)*((Fintype.card K : ℝ)*(total f*total g/(Fintype.card K : ℝ)^3)) = _
  rw [total_lineSum]
  unfold pairing
  field_simp
  ring

theorem opposition_rayleigh (f g : K → K → ℝ) (hfg : total f + total g = 0) :
    2 * pairing (lineSum f) g ≤
      Real.sqrt (Fintype.card K : ℝ) * (energy f + energy g) := by
  have hq := card_pos (K := K)
  have hsq := Real.sq_sqrt hq.le
  have hsqp := Real.sqrt_pos.mpr hq
  let c := pairing (lineSum (center f)) (center g)
  have hc : c^2 ≤ (Fintype.card K : ℝ) * energy (center f) * energy (center g) :=
    incidence_pairing_bound (center f) (center g) (total_center f)
  have he : 2*c ≤ Real.sqrt (Fintype.card K : ℝ) *
      (energy (center f) + energy (center g)) := by
    have h0 := energy_nonneg (center f)
    have h1 := energy_nonneg (center g)
    have h2 := sq_nonneg (energy (center f) - energy (center g))
    have h3 : 0 ≤ Real.sqrt (Fintype.card K : ℝ) *
        (energy (center f)+energy (center g)) := by positivity
    apply le_of_sq_le_sq _ h3
    simp only [mul_pow, hsq]
    nlinarith only [hc, mul_nonneg hq.le h2]
  have hcent : pairing (lineSum f) g ≤ c := by
    dsimp [c]
    rw [incidence_center]
    have hh : total f * total g ≤ 0 := by
      have hg : total g = -total f := by linarith only [hfg]
      rw [hg, mul_neg, ← pow_two]
      exact neg_nonpos.mpr (sq_nonneg _)
    have hd := div_nonpos_of_nonpos_of_nonneg hh hq.le
    linarith
  calc
    2*pairing (lineSum f) g ≤ 2*c := by linarith
    _ ≤ _ := he
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (energy_center_le f) (energy_center_le g)) hsqp.le

end CoboundaryExpanders.RankTwo

namespace CoboundaryExpanders.EdgeMixing
variable {V : Type*} [Fintype V]
def mass (e : V → V → ℝ) (x : V) : ℝ := ∑ y, e x y
def energy (e : V → V → ℝ) (f : V → ℝ) : ℝ := ∑ x, mass e x * (f x)^2
def pairing (e : V → V → ℝ) (f g : V → ℝ) : ℝ := ∑ x, ∑ y, e x y * f x * g y
def Rayleigh (e : V → V → ℝ) (lam : ℝ) : Prop :=
  ∀ f : V → ℝ, (∑ x, mass e x * f x) = 0 → pairing e f f ≤ lam*energy e f
end CoboundaryExpanders.EdgeMixing

namespace CoboundaryExpanders.RankTwo
variable {K : Type} [Field K] [Fintype K]
local instance : DecidableEq K := Classical.decEq _
abbrev Vert (K : Type) := (K×K) ⊕ (K×K)
def edge : Vert K → Vert K → ℝ
  | .inl P, .inr L => if P.2 = L.1*P.1+L.2 then 1 else 0
  | .inr L, .inl P => if P.2 = L.1*P.1+L.2 then 1 else 0
  | _, _ => 0

omit [Fintype K] in
lemma edge_symm (x y : Vert K) : edge x y = edge y x := by
  cases x <;> cases y <;> rfl
omit [Fintype K] in
lemma edge_nonneg (x y : Vert K) : 0 ≤ edge x y := by
  cases x <;> cases y <;> dsimp [edge] <;> positivity

lemma point_degree (P : K×K) : EdgeMixing.mass edge (.inl P) = Fintype.card K := by
  simp only [EdgeMixing.mass,Fintype.sum_sum_type,edge,Finset.sum_const_zero,zero_add,
    Fintype.sum_prod_type]
  have he (a b : K) : P.2 = a*P.1+b ↔ b = P.2-a*P.1 := by
    constructor <;> intro h <;> linear_combination -h
  simp only [he]
  simp
lemma line_degree (L : K×K) : EdgeMixing.mass edge (.inr L) = Fintype.card K := by
  simp only [EdgeMixing.mass,Fintype.sum_sum_type,edge,Finset.sum_const_zero,add_zero,
    Fintype.sum_prod_type]
  simp
lemma edge_degree (v : Vert K) : EdgeMixing.mass edge v = Fintype.card K := by
  cases v with
  | inl P => exact point_degree P
  | inr L => exact line_degree L

lemma cross_pairing (f g : K → K → ℝ) :
    (∑ P : K×K, ∑ L : K×K,
      (if P.2 = L.1*P.1+L.2 then (1:ℝ) else 0)*f P.1 P.2*g L.1 L.2) =
      pairing (lineSum f) g := by
  rw [Finset.sum_comm]
  simp only [Fintype.sum_prod_type]
  unfold pairing lineSum
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  simp

lemma edge_pairing (F : Vert K → ℝ) :
    EdgeMixing.pairing edge F F = 2 * pairing
      (lineSum (fun x y => F (.inl (x,y)))) (fun a b => F (.inr (a,b))) := by
  let f : K → K → ℝ := fun x y => F (.inl (x,y))
  let g : K → K → ℝ := fun x y => F (.inr (x,y))
  change _ = 2*pairing (lineSum f) g
  have hleft := cross_pairing f g
  have hright : (∑ L : K×K, ∑ P : K×K,
      (if P.2 = L.1*P.1+L.2 then (1:ℝ) else 0)*g L.1 L.2*f P.1 P.2) =
      pairing (lineSum f) g := by
    rw [Finset.sum_comm]
    convert hleft using 1
    apply Finset.sum_congr rfl
    intro P _
    apply Finset.sum_congr rfl
    intro L _
    ring
  simp only [EdgeMixing.pairing,Fintype.sum_sum_type,edge,zero_mul,Finset.sum_const_zero,
    zero_add,add_zero]
  change (∑ P : K×K, ∑ L : K×K,
    (if P.2=L.1*P.1+L.2 then (1:ℝ) else 0)*f P.1 P.2*g L.1 L.2) +
    (∑ L : K×K, ∑ P : K×K,
    (if P.2=L.1*P.1+L.2 then (1:ℝ) else 0)*g L.1 L.2*f P.1 P.2) = _
  rw [hleft,hright]
  ring

lemma edge_energy (F : Vert K → ℝ) : EdgeMixing.energy edge F =
    (Fintype.card K : ℝ) * (energy (fun x y => F (.inl (x,y))) +
      energy (fun x y => F (.inr (x,y)))) := by
  simp only [EdgeMixing.energy,edge_degree,Fintype.sum_sum_type,Fintype.sum_prod_type,
    ←Finset.mul_sum,energy]

lemma edge_mean (F : Vert K → ℝ) : (∑ v,EdgeMixing.mass edge v*F v) =
    (Fintype.card K : ℝ) * (total (fun x y => F (.inl (x,y))) +
      total (fun x y => F (.inr (x,y)))) := by
  simp only [edge_degree,Fintype.sum_sum_type,Fintype.sum_prod_type,←Finset.mul_sum,total]

theorem edge_rayleigh : EdgeMixing.Rayleigh (edge (K:=K))
    (Real.sqrt (Fintype.card K : ℝ)/(Fintype.card K : ℝ)) := by
  intro F hF
  have hq : (Fintype.card K : ℝ) ≠ 0 := ne_of_gt card_pos
  rw [edge_mean] at hF
  have hmean := (mul_eq_zero.mp hF).resolve_left hq
  rw [edge_pairing,edge_energy]
  have he := opposition_rayleigh (fun x y => F (.inl (x,y))) (fun x y => F (.inr (x,y))) hmean
  convert he using 1
  field_simp

end CoboundaryExpanders.RankTwo

namespace CoboundaryExpanders.EdgeMixing
variable {V W : Type} [Fintype V] [Fintype W]
lemma sum_embedding (f : V → W) (hf : Function.Injective f) (F : W → ℝ)
    (hF : ∀ y, y ∉ Set.range f → F y = 0) : (∑ y,F y) = ∑ x,F (f x) := by
  classical
  rw [←Finset.sum_image (s:=Finset.univ) (f:=F) (g:=f) (fun _ _ _ _ h => hf h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro y _ hy
  exact hF y (by simpa only [Finset.mem_image,Finset.mem_univ,true_and,Set.mem_range] using hy)

structure Embedding (e : V → V → ℝ) (d : W → W → ℝ) where
  vertex : V → W
  injective : Function.Injective vertex
  edge_eq : ∀ x y, d (vertex x) (vertex y) = e x y
  outside_zero : ∀ y, y ∉ Set.range vertex → ∀ z, d y z = 0

namespace Embedding
variable {e : V → V → ℝ} {d : W → W → ℝ} (M : Embedding e d)
  (hd : ∀ x y,d x y = d y x)
include M hd

lemma mass_map (x : V) : mass d (M.vertex x) = mass e x := by
  unfold mass
  rw [sum_embedding M.vertex M.injective _ (fun y hy => by rw [hd,M.outside_zero y hy])]
  simp only [M.edge_eq]
omit hd [Fintype V] in
lemma mass_outside (y : W) (hy : y ∉ Set.range M.vertex) : mass d y = 0 := by
  simp only [mass,M.outside_zero y hy,Finset.sum_const_zero]
lemma mean_pull (F : W → ℝ) : (∑ y,mass d y*F y) = ∑ x,mass e x*F (M.vertex x) := by
  rw [sum_embedding M.vertex M.injective _ (fun y hy => by rw [M.mass_outside y hy,zero_mul])]
  simp only [M.mass_map hd]
lemma energy_pull (F : W → ℝ) : energy d F = energy e (F ∘ M.vertex) := by
  unfold energy
  rw [sum_embedding M.vertex M.injective _ (fun y hy => by rw [M.mass_outside y hy,zero_mul])]
  simp only [M.mass_map hd,Function.comp_apply]
lemma pairing_pull (F H : W → ℝ) : pairing d F H = pairing e (F ∘ M.vertex) (H ∘ M.vertex) := by
  unfold pairing
  rw [sum_embedding M.vertex M.injective _ (fun y hy => by
    simp only [M.outside_zero y hy,zero_mul,Finset.sum_const_zero])]
  apply Finset.sum_congr rfl
  intro x _
  rw [sum_embedding M.vertex M.injective _ (fun y hy => by
    rw [hd,M.outside_zero y hy,zero_mul,zero_mul])]
  simp only [M.edge_eq,Function.comp_apply]

theorem push {lam : ℝ} (he : Rayleigh e lam) : Rayleigh d lam := by
  intro F hF
  rw [M.mean_pull hd] at hF
  rw [M.pairing_pull hd,M.energy_pull hd]
  exact he (F ∘ M.vertex) hF
end Embedding
end CoboundaryExpanders.EdgeMixing

namespace CoboundaryExpanders.InfiniteChains
namespace FiniteWeights
variable {V : Type} [Fintype V] [DecidableEq V]
def level (X : CoboundaryExpanders.InfiniteChains.Complex V) (r : ℕ) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (fun s => s ∈ X.faces ∧ s.card = r)

omit [DecidableEq V] in
@[simp] lemma mem_level (X : CoboundaryExpanders.InfiniteChains.Complex V) (r : ℕ) (s : Finset V) :
    s ∈ level X r ↔ s ∈ X.faces ∧ s.card = r := by simp [level]

def cofaces (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) (s : Finset V) : ℕ :=
  ((level X N).filter (fun t => s ⊆ t)).card

def Pure (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) : Prop :=
  (level X N).Nonempty ∧ ∀ s ∈ X.faces, ∃ t ∈ level X N, s ⊆ t

lemma cofaces_zero_of_not_face (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) {s : Finset V} (hs : s ∉ X.faces) :
    cofaces X N s = 0 := by
  unfold cofaces
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨ht,hst⟩ := Finset.mem_filter.mp ht
  exact hs (X.downward ((mem_level X N t).mp ht).1 hst)

lemma cofaces_link (X : CoboundaryExpanders.InfiniteChains.Complex V) {N : ℕ} {s : Finset V} (hs : s ∈ X.faces)
    (hN : s.card ≤ N) {a : Finset V} (hd : Disjoint s a) :
    cofaces (X.faceLink s hs) (N-s.card) a = cofaces X N (s∪a) := by
  unfold cofaces
  apply Finset.card_bij (fun t _ => s∪t)
  · intro t ht
    obtain ⟨ht,hat⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht,hcard⟩ := (mem_level _ _ _).mp ht
    refine Finset.mem_filter.mpr ⟨(mem_level _ _ _).mpr ⟨ht.2,?_⟩,
      Finset.union_subset_union (Finset.Subset.refl _) hat⟩
    rw [Finset.card_union_of_disjoint ht.1,hcard]
    omega
  · intro t ht u hu he
    have hd1 := ((mem_level _ _ _).mp (Finset.mem_filter.mp ht).1).1.1
    have hd2 := ((mem_level _ _ _).mp (Finset.mem_filter.mp hu).1).1.1
    have hh := congrArg (fun t : Finset V => t\s) he
    simpa only [Finset.union_sdiff_cancel_left hd1,Finset.union_sdiff_cancel_left hd2] using hh
  · intro t ht
    obtain ⟨ht,hat⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht,hcard⟩ := (mem_level _ _ _).mp ht
    have hst : s ⊆ t := Finset.subset_union_left.trans hat
    have hdis : Disjoint s (t\s) := Finset.disjoint_left.mpr (fun v hv hv' => (Finset.mem_sdiff.mp hv').2 hv)
    refine ⟨t\s,Finset.mem_filter.mpr ⟨(mem_level _ _ _).mpr ⟨⟨hdis,?_⟩,?_⟩,?_⟩,?_⟩
    · rwa [Finset.union_sdiff_of_subset hst]
    · rw [Finset.card_sdiff_of_subset hst,hcard]
    · intro v hv
      exact Finset.mem_sdiff.mpr ⟨hat (Finset.mem_union_right _ hv),fun h => Finset.disjoint_left.mp hd h hv⟩
    · exact Finset.union_sdiff_of_subset hst

lemma pure_link {X : CoboundaryExpanders.InfiniteChains.Complex V} {N : ℕ} (hP : Pure X N) {s : Finset V} (hs : s ∈ X.faces) :
    Pure (X.faceLink s hs) (N-s.card) := by
  have extension : ∀ a ∈ (X.faceLink s hs).faces,
      ∃ t ∈ level (X.faceLink s hs) (N-s.card), a ⊆ t := by
    intro a ha
    obtain ⟨t,ht,hat⟩ := hP.2 _ ha.2
    have ht' := (mem_level X N t).mp ht
    have hst := Finset.subset_union_left.trans hat
    refine ⟨t\s,(mem_level _ _ _).mpr ⟨⟨?_,?_⟩,?_⟩,?_⟩
    · exact Finset.disjoint_left.mpr (fun v hv hv' => (Finset.mem_sdiff.mp hv').2 hv)
    · rw [Finset.union_sdiff_of_subset hst]; exact ht'.1
    · rw [Finset.card_sdiff_of_subset hst,ht'.2]
    · intro v hv
      exact Finset.mem_sdiff.mpr ⟨hat (Finset.mem_union_right _ hv), fun h => Finset.disjoint_left.mp ha.1 h hv⟩
  obtain ⟨t,ht,_⟩ := extension ∅ (X.faceLink s hs).empty_mem
  exact ⟨⟨t,ht⟩,extension⟩

end FiniteWeights

open FiniteWeights
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
attribute [local instance] Classical.propDecidable

namespace Cone.FaceModel
variable {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} (M : FaceModel X Y)

lemma cofaces_image (N : ℕ) (s : Finset V) :
    cofaces Y N (s.image M.vertex) = cofaces X N s := by
  unfold cofaces
  symm
  apply Finset.card_bij (fun t _ => t.image M.vertex)
  · intro t ht
    obtain ⟨ht,hst⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht,hcard⟩ := (mem_level _ _ _).mp ht
    exact Finset.mem_filter.mpr ⟨(mem_level _ _ _).mpr
      ⟨(M.face_iff t).mpr ht,by rwa [Finset.card_image_of_injective t M.injective]⟩,
      Finset.image_subset_image hst⟩
  · intro t ht u hu he
    exact Finset.image_injective M.injective he
  · intro t ht
    obtain ⟨ht,hst⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht,hcard⟩ := (mem_level _ _ _).mp ht
    obtain ⟨u,hu,he⟩ := M.cover t ht
    refine ⟨u,Finset.mem_filter.mpr ⟨(mem_level _ _ _).mpr ⟨hu,?_⟩,?_⟩,he⟩
    · rw [←he,Finset.card_image_of_injective u M.injective] at hcard
      exact hcard
    · rw [←he] at hst
      exact (Finset.image_subset_image_iff M.injective).mp hst

omit [Fintype V] [Fintype W] [DecidableEq V] in
lemma vertex_in_range {y : W} (hy : ({y}:Finset W) ∈ Y.faces) : y ∈ Set.range M.vertex := by
  obtain ⟨s,hs,he⟩ := M.cover {y} hy
  have h : y ∈ s.image M.vertex := by rw [he]; simp
  obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp h
  exact ⟨x,hxy⟩

end Cone.FaceModel

namespace FiniteWeights

def edge (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) (x y : V) : ℝ :=
  if x ≠ y then (cofaces X N {x,y}:ℝ) else 0
lemma edge_symm (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) (x y : V) : edge X N x y = edge X N y x := by
  simp only [edge,ne_comm,Finset.pair_comm]
lemma edge_nonneg (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) (x y : V) : 0 ≤ edge X N x y := by
  unfold edge; split_ifs <;> positivity
lemma edge_zero_of_not_face (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) {x : V} (hx : ({x}:Finset V) ∉ X.faces)
    (y : V) : edge X N x y = 0 := by
  unfold edge
  split_ifs
  · rw [cofaces_zero_of_not_face X N (fun h => hx (X.downward h (by simp))),Nat.cast_zero]
  · rfl

lemma cofaces_pos {X : CoboundaryExpanders.InfiniteChains.Complex V} {N : ℕ} (hP : Pure X N) {s : Finset V} (hs : s ∈ X.faces) :
    0 < cofaces X N s := by
  obtain ⟨t,ht,hst⟩ := hP.2 s hs
  exact Finset.card_pos.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,hst⟩⟩
lemma cofaces_pos_iff {X : CoboundaryExpanders.InfiniteChains.Complex V} {N : ℕ} (hP : Pure X N) (s : Finset V) :
    0 < cofaces X N s ↔ s ∈ X.faces := by
  refine ⟨fun h => ?_,cofaces_pos hP⟩
  by_contra hs
  rw [cofaces_zero_of_not_face X N hs] at h
  omega

end FiniteWeights

namespace Cone.FaceModel
variable {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} (M : FaceModel X Y)

def spectralEmbedding (N : ℕ) : EdgeMixing.Embedding (edge X N) (edge Y N) where
  vertex := M.vertex
  injective := M.injective
  edge_eq := by
    intro x y
    simp only [edge,M.injective.ne_iff]
    split_ifs
    · have h := M.cofaces_image N {x,y}
      simpa only [Finset.image_insert,Finset.image_singleton] using congrArg (fun a : ℕ => (a:ℝ)) h
    · rfl
  outside_zero := by
    intro y hy z
    apply edge_zero_of_not_face Y N
    exact fun h => hy (M.vertex_in_range h)

include M in
theorem rayleigh_push {N : ℕ} {lam : ℝ} (hX : EdgeMixing.Rayleigh (edge X N) lam) :
    EdgeMixing.Rayleigh (edge Y N) lam :=
  (M.spectralEmbedding N).push (edge_symm Y N) hX
end Cone.FaceModel
end CoboundaryExpanders.InfiniteChains

namespace CoboundaryExpanders.InfiniteChains.FiniteWeights
variable {V : Type} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable
lemma cofaces_top (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) (s : Finset V) (hs : s.card = N) :
    cofaces X N s = if s ∈ X.faces then 1 else 0 := by
  by_cases hf : s ∈ X.faces
  · rw [ite_eq_left hf]
    have he : (level X N).filter (fun t => s ⊆ t) = {s} := by
      ext t
      simp only [Finset.mem_filter,mem_level,Finset.mem_singleton]
      constructor
      · rintro ⟨⟨ht,hcard⟩,hst⟩
        exact (Finset.eq_of_subset_of_card_le hst (by omega)).symm
      · rintro rfl
        exact ⟨⟨hf,hs⟩,Finset.Subset.refl _⟩
    simp only [cofaces,he,Finset.card_singleton]
  · rw [ite_eq_right hf,cofaces_zero_of_not_face X N hf]
end CoboundaryExpanders.InfiniteChains.FiniteWeights

namespace CoboundaryExpanders.RankTwoGeometry
open InfiniteChains FiniteWeights MatrixOpposition
variable {K : Type} [Field K] [Fintype K]
local instance : DecidableEq K := Classical.decEq _

omit [Fintype K] in
lemma point_line_face (P L : K×K) :
    ({Sum.inl P,Sum.inr L}:Finset (Vert K)) ∈ (incidenceComplex K).faces ↔ incident P L := by
  constructor
  · rintro ⟨P',L',hPL,hs⟩
    have hP := hs (Finset.mem_insert_self _ _)
    have hL := hs (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    simp only [Finset.mem_insert,Finset.mem_singleton,Sum.inl.injEq,Sum.inr.injEq,
      Sum.inl_ne_inr,Sum.inr_ne_inl,false_or,or_false] at hP hL
    simpa only [hP,hL] using hPL
  · intro hPL
    exact ⟨P,L,hPL,Finset.Subset.refl _⟩
omit [Fintype K] in
lemma point_point_not_face (P Q : K×K) (hPQ : P ≠ Q) :
    ({Sum.inl P,Sum.inl Q}:Finset (Vert K)) ∉ (incidenceComplex K).faces := by
  rintro ⟨P',L',hPL,hs⟩
  have hP := hs (Finset.mem_insert_self _ _)
  have hQ := hs (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  simp only [Finset.mem_insert,Finset.mem_singleton,Sum.inl.injEq,Sum.inl_ne_inr,or_false] at hP hQ
  exact hPQ (hP.trans hQ.symm)
omit [Fintype K] in
lemma line_line_not_face (L M : K×K) (hLM : L ≠ M) :
    ({Sum.inr L,Sum.inr M}:Finset (Vert K)) ∉ (incidenceComplex K).faces := by
  rintro ⟨P',L',hPL,hs⟩
  have hL := hs (Finset.mem_insert_self _ _)
  have hM := hs (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  simp only [Finset.mem_insert,Finset.mem_singleton,Sum.inr.injEq,Sum.inr_ne_inl,false_or] at hL hM
  exact hLM (hL.trans hM.symm)

lemma incidence_edge (x y : Vert K) : edge (incidenceComplex K) 2 x y = RankTwo.edge x y := by
  cases x with
  | inl P =>
    cases y with
    | inl Q =>
      by_cases h : P = Q
      · subst Q; simp [edge,RankTwo.edge]
      · simp [edge,RankTwo.edge,h,cofaces_zero_of_not_face _ 2 (point_point_not_face P Q h)]
    | inr L =>
      rw [edge,ite_eq_left (by simp),cofaces_top _ 2 _ (by simp),point_line_face]
      simp only [RankTwo.edge,incident]
      split_ifs <;> simp_all
  | inr L =>
    cases y with
    | inl P =>
      rw [edge_symm,RankTwo.edge_symm]
      rw [edge,ite_eq_left (by simp),cofaces_top _ 2 _ (by simp),point_line_face]
      simp only [RankTwo.edge,incident]
      split_ifs <;> simp_all
    | inr M =>
      by_cases h : L = M
      · subst M; simp [edge,RankTwo.edge]
      · simp [edge,RankTwo.edge,h,cofaces_zero_of_not_face _ 2 (line_line_not_face L M h)]

theorem incidence_rayleigh : EdgeMixing.Rayleigh (edge (incidenceComplex K) 2)
    (Real.sqrt (Fintype.card K : ℝ)/(Fintype.card K : ℝ)) := by
  convert RankTwo.edge_rayleigh (K:=K) using 1
  funext x y
  exact incidence_edge x y

end CoboundaryExpanders.RankTwoGeometry

namespace CoboundaryExpanders.MatrixOpposition
open InfiniteChains FiniteWeights TypedCosetFaces
variable {K : Type} [Field K] [Fintype K]
noncomputable instance cutVertexFintype (N : ℕ) : Fintype (Vertex (cutGroups K N)) := Fintype.ofFinite _

theorem cut3_rayleigh : EdgeMixing.Rayleigh (edge (TypedCosetFaces.complex (cutGroups K 3)) 2)
    (Real.sqrt (Fintype.card K : ℝ)/(Fintype.card K : ℝ)) := by
  classical
  exact RankTwoGeometry.incidenceModel.rayleigh_push RankTwoGeometry.incidence_rayleigh
end CoboundaryExpanders.MatrixOpposition

namespace CoboundaryExpanders.EdgeMixing

section
variable {V W : Type} [Fintype V] [Fintype W]
attribute [local instance] Classical.propDecidable
namespace Embedding
variable {e : V → V → ℝ} {d : W → W → ℝ} (M : Embedding e d)
def extend (f : V → ℝ) (y : W) : ℝ :=
  if h : y ∈ Set.range M.vertex then f h.choose else 0
omit [Fintype W] in
lemma extend_map (f : V → ℝ) (x : V) : M.extend f (M.vertex x) = f x := by
  dsimp [extend]
  rw [dite_eq_left (show M.vertex x ∈ Set.range M.vertex from ⟨x,rfl⟩)]
  congr 1
  exact M.injective (Exists.choose_spec (show M.vertex x ∈ Set.range M.vertex from ⟨x,rfl⟩))
omit [Fintype W] in
lemma extend_comp (f : V → ℝ) : M.extend f ∘ M.vertex = f := funext (M.extend_map f)
include M in
theorem pull (hd : ∀ x y,d x y = d y x) {lam : ℝ} (h : Rayleigh d lam) : Rayleigh e lam := by
  intro f hf
  have hh := h (M.extend f) (by
    rw [M.mean_pull hd]
    simpa only [M.extend_map] using hf)
  rwa [M.pairing_pull hd,M.energy_pull hd,M.extend_comp] at hh
end Embedding

end

variable {A B : Type} [Fintype A] [Fintype B]
def bipartiteEdge : A ⊕ B → A ⊕ B → ℝ
  | Sum.inl _,Sum.inr _ => 1
  | Sum.inr _,Sum.inl _ => 1
  | _,_ => 0
@[simp] lemma bipartite_mass_left (a : A) : mass (bipartiteEdge (B:=B)) (Sum.inl a) = Fintype.card B := by
  simp [mass,Fintype.sum_sum_type,bipartiteEdge]
@[simp] lemma bipartite_mass_right (b : B) : mass (bipartiteEdge (A:=A)) (Sum.inr b) = Fintype.card A := by
  simp [mass,Fintype.sum_sum_type,bipartiteEdge]

lemma bipartite_rayleigh : Rayleigh (bipartiteEdge (A:=A) (B:=B)) 0 := by
  intro f hf
  have hm : (Fintype.card B:ℝ)*(∑a,f (Sum.inl a))+(Fintype.card A:ℝ)*(∑b,f (Sum.inr b)) = 0 := by
    simpa only [Fintype.sum_sum_type,bipartite_mass_left,bipartite_mass_right,←Finset.mul_sum] using hf
  have hp : pairing bipartiteEdge f f = 2*(∑a,f (Sum.inl a))*(∑b,f (Sum.inr b)) := by
    simp only [pairing,Fintype.sum_sum_type,bipartiteEdge,zero_mul,one_mul,
      Finset.sum_const_zero,zero_add,add_zero,←Finset.mul_sum,←Finset.sum_mul]
    ring
  rw [hp,zero_mul]
  by_cases ha : IsEmpty A
  · let := ha
    simp
  · have han : 0 < (Fintype.card A:ℝ) := by exact_mod_cast Fintype.card_pos_iff.mpr (not_isEmpty_iff.mp ha)
    have hmult := congrArg (fun r : ℝ => r*(∑a,f (Sum.inl a))) hm
    have hsq := mul_nonneg (Nat.cast_nonneg (Fintype.card B) : (0:ℝ) ≤ _) (sq_nonneg (∑a,f (Sum.inl a)))
    have hprod : (∑a,f (Sum.inl a))*(∑b,f (Sum.inr b)) ≤ 0 := by
      apply (mul_le_mul_iff_right₀ han).mp
      change (Fintype.card A:ℝ)*((∑a,f (Sum.inl a))*(∑b,f (Sum.inr b))) ≤ (Fintype.card A:ℝ)*0
      nlinarith [hmult,hsq]
    linarith
end CoboundaryExpanders.EdgeMixing

namespace CoboundaryExpanders.InfiniteChains.Join
open Cone FiniteWeights
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
attribute [local instance] Classical.propDecidable
omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
@[simp] lemma left_single_inl (x : V) : ({Sum.inl x}:Finset (V ⊕ W)).toLeft = {x} := by ext y; simp
omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
@[simp] lemma right_single_inl (x : V) : ({Sum.inl x}:Finset (V ⊕ W)).toRight = ∅ := by ext y; simp
omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
@[simp] lemma left_single_inr (x : W) : ({Sum.inr x}:Finset (V ⊕ W)).toLeft = ∅ := by ext y; simp
omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
@[simp] lemma right_single_inr (x : W) : ({Sum.inr x}:Finset (V ⊕ W)).toRight = {x} := by ext y; simp

abbrev TrueVertex (X : CoboundaryExpanders.InfiniteChains.Complex V) := {x : V // ({x}:Finset V) ∈ X.faces}

def rankOneEmbedding {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W}
    (hX : RankBound X 1) (hY : RankBound Y 1) :
    EdgeMixing.Embedding (EdgeMixing.bipartiteEdge (A:=TrueVertex X) (B:=TrueVertex Y))
      (edge (complex X Y) 2) where
  vertex := Sum.map Subtype.val Subtype.val
  injective := Sum.map_injective.mpr ⟨Subtype.val_injective,Subtype.val_injective⟩
  edge_eq := by
    intro x y
    cases x with
    | inl a =>
      cases y with
      | inl b =>
        change edge (complex X Y) 2 (Sum.inl a.val) (Sum.inl b.val) = 0
        by_cases hab : a = b
        · subst b; simp [edge]
        · have hv : a.val ≠ b.val := fun h => hab (Subtype.ext h)
          have hne : Sum.inl a.val ≠ (Sum.inl b.val : V ⊕ W) := fun h => hv (Sum.inl.inj h)
          have hnot : ({Sum.inl a.val,Sum.inl b.val}:Finset (V ⊕ W)) ∉ (complex X Y).faces := by
            intro h
            have hh := hX {a.val,b.val} (by simpa [complex] using h.1)
            rw [Finset.card_pair hv] at hh
            omega
          simp [edge,hne,cofaces_zero_of_not_face _ _ hnot]
      | inr b =>
        change edge (complex X Y) 2 (Sum.inl a.val) (Sum.inr b.val) = 1
        rw [edge,ite_eq_left (by simp),cofaces_top _ _ _ (Finset.card_pair (by simp))]
        have hf : ({Sum.inl a.val,Sum.inr b.val}:Finset (V ⊕ W)) ∈ (complex X Y).faces := by
          simpa [complex] using And.intro a.property b.property
        simp [hf]
    | inr a =>
      cases y with
      | inl b =>
        change edge (complex X Y) 2 (Sum.inr a.val) (Sum.inl b.val) = 1
        rw [edge,ite_eq_left (by simp),cofaces_top _ _ _ (Finset.card_pair (by simp))]
        have hf : ({Sum.inr a.val,Sum.inl b.val}:Finset (V ⊕ W)) ∈ (complex X Y).faces := by
          simpa [complex] using And.intro b.property a.property
        simp [hf]
      | inr b =>
        change edge (complex X Y) 2 (Sum.inr a.val) (Sum.inr b.val) = 0
        by_cases hab : a = b
        · subst b; simp [edge]
        · have hv : a.val ≠ b.val := fun h => hab (Subtype.ext h)
          have hne : Sum.inr a.val ≠ (Sum.inr b.val : V ⊕ W) := fun h => hv (Sum.inr.inj h)
          have hnot : ({Sum.inr a.val,Sum.inr b.val}:Finset (V ⊕ W)) ∉ (complex X Y).faces := by
            intro h
            have hh := hY {a.val,b.val} (by simpa [complex] using h.2)
            rw [Finset.card_pair hv] at hh
            omega
          simp [edge,hne,cofaces_zero_of_not_face _ _ hnot]
  outside_zero := by
    intro x hx y
    apply edge_zero_of_not_face
    intro h
    cases x with
    | inl a =>
      have ha : ({a}:Finset V) ∈ X.faces := by simpa [complex] using h.1
      exact hx ⟨Sum.inl ⟨a,ha⟩,rfl⟩
    | inr b =>
      have hb : ({b}:Finset W) ∈ Y.faces := by simpa [complex] using h.2
      exact hx ⟨Sum.inr ⟨b,hb⟩,rfl⟩

lemma rankOne_rayleigh {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W}
    (hX : RankBound X 1) (hY : RankBound Y 1) : EdgeMixing.Rayleigh (edge (complex X Y) 2) 0 :=
  (rankOneEmbedding hX hY).push (edge_symm _ _) EdgeMixing.bipartite_rayleigh
end CoboundaryExpanders.InfiniteChains.Join

namespace CoboundaryExpanders.EdgeMixing
variable {V : Type} [Fintype V]
lemma rayleigh_mono {e : V → V → ℝ} (he : ∀ x y,0 ≤ e x y) {a b : ℝ}
    (h : Rayleigh e a) (hab : a ≤ b) : Rayleigh e b := by
  intro f hf
  apply (h f hf).trans
  apply mul_le_mul_of_nonneg_right hab
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (Finset.sum_nonneg (fun y _ => he x y)) (sq_nonneg _))
end CoboundaryExpanders.EdgeMixing

namespace CoboundaryExpanders.InfiniteChains
open Cone FiniteWeights
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

def TopSpectral (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) (lam : ℝ) : Prop :=
  ∀ s : Finset V, ∀ hs : s ∈ X.faces, s.card+2 = N →
    EdgeMixing.Rayleigh (edge (X.faceLink s hs) 2) lam

lemma Cone.FaceModel.rayleigh_pull {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} (M : FaceModel X Y)
    (N : ℕ) {lam : ℝ} (hY : EdgeMixing.Rayleigh (edge Y N) lam) :
    EdgeMixing.Rayleigh (edge X N) lam :=
  (M.spectralEmbedding N).pull (edge_symm Y N) hY

lemma Cone.FaceModel.pushTopSpectral {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} (M : FaceModel X Y)
    {N : ℕ} {lam : ℝ} (h : TopSpectral X N lam) : TopSpectral Y N lam := by
  intro t ht hn
  obtain ⟨s,hs,rfl⟩ := M.cover t ht
  rw [Finset.card_image_of_injective _ M.injective] at hn
  exact (M.linkModel s hs).rayleigh_push (h s hs hn)
lemma Cone.FaceModel.pullTopSpectral {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} (M : FaceModel X Y)
    {N : ℕ} {lam : ℝ} (h : TopSpectral Y N lam) : TopSpectral X N lam := by
  intro s hs hn
  apply (M.linkModel s hs).rayleigh_pull 2
  apply h
  rwa [Finset.card_image_of_injective _ M.injective]

theorem Join.topSpectral {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} {A B : ℕ} {lam : ℝ}
    (hX : RankBound X A) (hY : RankBound Y B) (h0 : 0 ≤ lam)
    (hTX : TopSpectral X A lam) (hTY : TopSpectral Y B lam) :
    TopSpectral (Join.complex X Y) (A+B) lam := by
  intro s hs hn
  have hL := hX s.toLeft hs.1
  have hR := hY s.toRight hs.2
  have hC := Finset.card_toLeft_add_card_toRight (u:=s)
  rw [Join.link_eq hs]
  by_cases hA : s.toLeft.card = A
  · have hB : s.toRight.card+2 = B := by omega
    exact (Join.emptyLeftModel (hX.terminal hs.1 hA)).rayleigh_push (hTY _ hs.2 hB)
  by_cases hB : s.toRight.card = B
  · have hAl : s.toLeft.card+2 = A := by omega
    exact (Join.emptyRightModel (hY.terminal hs.2 hB)).rayleigh_push (hTX _ hs.1 hAl)
  have hAl : A-s.toLeft.card = 1 := by omega
  have hBl : B-s.toRight.card = 1 := by omega
  apply EdgeMixing.rayleigh_mono (edge_nonneg _ _) _ h0
  exact Join.rankOne_rayleigh (hAl ▸ hX.link hs.1) (hBl ▸ hY.link hs.2)

lemma TopSpectral.vertexCriterion {X : CoboundaryExpanders.InfiniteChains.Complex V} {N : ℕ} {lam : ℝ}
    (hBase : N = 2 → EdgeMixing.Rayleigh (edge X 2) lam)
    (hVertex : ∀ v : V, ∀ hv : {v} ∈ X.faces, TopSpectral (X.faceLink {v} hv) (N-1) lam) :
    TopSpectral X N lam := by
  intro s hs hn
  by_cases he : s = ∅
  · subst s
    simpa only [faceLink_empty] using hBase (by simpa using hn.symm)
  obtain ⟨v,hv⟩ := Finset.nonempty_iff_ne_empty.mpr he
  have hvx : {v} ∈ X.faces := X.downward hs (Finset.singleton_subset_iff.mpr hv)
  have hu : {v} ∪ s.erase v = s := by simp [Finset.insert_erase hv]
  have ht : s.erase v ∈ (X.faceLink {v} hvx).faces := by
    constructor
    · simp
    · rwa [hu]
  have hc : (s.erase v).card = s.card-1 := Finset.card_erase_of_mem hv
  have hp := Finset.card_pos.mpr ⟨v,hv⟩
  have HH := hVertex v hvx (s.erase v) ht (by omega)
  rw [faceLink_iterated] at HH
  have heq : X.faceLink ({v} ∪ s.erase v) ht.2 = X.faceLink s hs := by
    apply complex_eq
    ext a
    simp only [Complex.faceLink, hu]
  rwa [heq] at HH
end CoboundaryExpanders.InfiniteChains

namespace CoboundaryExpanders.MatrixOpposition
open SphericalOpposition SphericalOpposition.CompleteFlag TypedCosetFaces InfiniteChains Cone
open scoped Pointwise
variable {K : Type} [Field K] {N : ℕ}
lemma cut_middle_topSpectral [Fintype K] {a b : ℕ} {lam : ℝ}
    (ha : 0 < a) (hb : 0 < b) (h0 : 0 ≤ lam)
    (hA : TopSpectral (TypedCosetFaces.complex (cutGroups K a)) (a-1) lam)
    (hB : TopSpectral (TypedCosetFaces.complex (cutGroups K b)) (b-1) lam) :
    TopSpectral (linkComplex (cutGroups K (a+b)) {middleCut ha hb}) ((a-1)+(b-1)) lam := by
  classical
  let : Fintype (Vertex (productGroups (cutGroups K a) (cutGroups K b))) := Fintype.ofFinite _
  let : Fintype (Vertex (vertexLinkGroups (cutGroups K (a+b)) (middleCut ha hb))) := Fintype.ofFinite _
  have hj := Join.topSpectral cut_rankBound cut_rankBound h0 hA hB
  exact (singleLinkModel _ _).pushTopSpectral
    ((cutProductLinkModel ha hb).pushTopSpectral
      ((productModel (cutGroups K a) (cutGroups K b)).pullTopSpectral hj))

theorem cut_topSpectral [Fintype K] (N : ℕ) :
    TopSpectral (TypedCosetFaces.complex (cutGroups K N)) (N-1)
      (Real.sqrt (Fintype.card K : ℝ)/(Fintype.card K : ℝ)) := by
  classical
  induction N using Nat.strong_induction_on with | h N ih =>
  apply TopSpectral.vertexCriterion
  · intro hbase
    have hN : N = 3 := by omega
    subst N
    exact cut3_rayleigh
  intro v hv
  rcases v with ⟨c,v⟩
  induction v using Quotient.inductionOn with | h g =>
  have hstandard : TopSpectral (linkComplex (cutGroups K N) {c}) (N-1-1)
      (Real.sqrt (Fintype.card K : ℝ)/(Fintype.card K : ℝ)) := by
    rcases c with ⟨a,ha,haN⟩
    obtain ⟨b,hNb⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt haN)
    subst N
    have hb : 0 < b := by omega
    have hbN : b < a+b := by omega
    have hc := cut_middle_topSpectral ha hb (by positivity)
      (ih a haN) (ih b hbN)
    have he : (a-1)+(b-1) = a+b-1-1 := by omega
    rwa [he] at hc
  rw [standard_link_eq] at hstandard
  have hm := (actionModel (cutGroups K N) g).linkModel {vertex (cutGroups K N) 1 c}
    (standard_singleton_face _ _)
  have hh := hm.pushTopSpectral hstandard
  have he : (actionModel (cutGroups K N) g).vertex (vertex (cutGroups K N) 1 c) =
      vertex (cutGroups K N) g c := by
    change g • vertex (cutGroups K N) 1 c = _
    rw [smul_vertex,mul_one]
  have hi : ({vertex (cutGroups K N) 1 c} : Finset _).image
      (actionModel (cutGroups K N) g).vertex = {vertex (cutGroups K N) g c} := by
    rw [Finset.image_singleton,he]

  rw [faceLink_congr _ hv hi] at hh
  exact hh

end CoboundaryExpanders.MatrixOpposition

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains Cone
open scoped Pointwise
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)
  [Fintype (Vertex H)]
lemma allVertexTopSpectral_of_standard {N : ℕ} {lam : ℝ}
    (hs : ∀ i : I, TopSpectral (linkComplex H {i}) N lam) :
    ∀ v : Vertex H, ∀ hv : {v} ∈ (complex H).faces,
      TopSpectral ((complex H).faceLink {v} hv) N lam := by
  rintro ⟨i,v⟩ hv
  induction v using Quotient.inductionOn with | h g =>
  have hh := hs i
  rw [standard_link_eq] at hh
  have hh' := ((actionModel H g).linkModel {vertex H 1 i} (standard_singleton_face H i)).pushTopSpectral hh
  have he : (actionModel H g).vertex (vertex H 1 i) = vertex H g i := by
    change g • vertex H 1 i = _
    rw [smul_vertex,mul_one]
  have hi : ({vertex H 1 i} : Finset _).image (actionModel H g).vertex = {vertex H g i} := by
    rw [Finset.image_singleton,he]
  rw [faceLink_congr _ hv hi] at hh'
  exact hh'
end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.Construction
open InfiniteChains Cone TypedCosetFaces SphericalOpposition.CompleteFlag MatrixOpposition
noncomputable local instance finiteFintype (A : Type) [Finite A] : Fintype A := Fintype.ofFinite A

theorem actual_topSpectral (n : ℕ) (hn : 2 ≤ n) (p : ℕ) [Fact p.Prime]
    (m : ℕ) (hm : 2 ≤ m) :
    TopSpectral (TypedCosetFaces.complex (reducedLocalGroup p n (by omega) m)) (n+1)
      (Real.sqrt (p:ℝ)/(p:ℝ)) := by
  let : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
  have hspherical := (cutSphericalModel (K:=ZMod p) (N:=n+1)).pushTopSpectral
    (cut_topSpectral (K:=ZMod p) (n+1))
  have hspherical' : TopSpectral (stdFlag (ZMod p) (n+1)).complex n
      (Real.sqrt (p:ℝ)/(p:ℝ)) := by
    simpa only [Nat.add_sub_cancel,ZMod.card] using hspherical
  apply TopSpectral.vertexCriterion
  · omega
  apply allVertexTopSpectral_of_standard
  intro cut
  have hc := (sphericalLinkModel p n (by omega) hm cut).pullTopSpectral hspherical'
  have ha := (actualVertexLinkModel p n (by omega) m cut).pushTopSpectral hc
  simpa only [Nat.add_sub_cancel] using ha
end CoboundaryExpanders.Construction

end

end OAI
