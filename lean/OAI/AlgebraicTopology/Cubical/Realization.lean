import OAI.AlgebraicTopology.Cubical.Descending
import OAI.GroupTheory.RightAngledArtin.CubeDescents
import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.Topology.Covering.Quotient

namespace OAI

noncomputable section

open Classical Set Topology

namespace EilenbergGanea
open Classical TraceWords
variable {V : Type*} [Fintype V] (L : SimpleGraph V)

/-- Actual right-angled Artin descending cubes supplied by the proved signed
trace normal form. None of the contractibility hypotheses are postulated. -/
def artinDescendingData : DescendingCube.Data
    (fun x : Letter V => letterValue (artinGenerator L) (invLetter x)) where
  length := artinLength L
  desc g := (rightDescents L g).toFinset
  decrease g a ha := (rightDescents_length L g a).mp (by simpa using ha)
  preserve g a b ha hb hab := by
    have ha' : a ∈ rightDescents L g := by simpa using ha
    have hb' : b ∈ rightDescents L g := by simpa using hb
    have hi := rightDescents_pairwise L g ha' hb' hab
    have hh := (descent_independent_step L g (x := invLetter a) (y := b)
      (show Independent L (invLetter a) b from hi)).mpr hb'
    simpa using hh
  commute g a b ha hb hab := by
    have ha' : a ∈ rightDescents L g := by simpa using ha
    have hb' : b ∈ rightDescents L g := by simpa using hb
    have hi : Independent L a b := rightDescents_pairwise L g ha' hb' hab
    exact letterValue_commute (L := L) (fun _ _ h => adjacent_generators_commute L h)
      (show Independent L (invLetter a) (invLetter b) from hi)
  nonempty g hg := by
    have hne : g ≠ 1 := by
      intro he
      have hz := (artinLength_eq_zero_iff L g).mpr he
      omega
    obtain ⟨a,ha⟩ := rightDescents_nonempty L hne
    exact ⟨a,by simpa using ha⟩
  zero := artinLength_eq_zero_iff L

abbrev ArtinDescendingRealization := (artinDescendingData L).Point

variable [Nonempty V]

/-- Contractibility of the actual weak descending-cube realization of the
Artin group, proved by an explicit globally continuous radial-shell flow. -/
theorem artinDescending_contractible : ContractibleSpace (ArtinDescendingRealization L) :=
  (artinDescendingData L).contractibleSpace

end EilenbergGanea

open Classical Set Topology
namespace EilenbergGanea.CubeRealization
variable {G V : Type*} [Group G] [Fintype V]
variable (L : SimpleGraph V) (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))

/-- Positive closed cubes of the actual Cayley cubical model. -/
structure Cell where
  base : G
  directions : Finset V
  clique : (directions : Set V).Pairwise L.Adj

/-- Points are represented by the unique open cube containing them. -/
@[ext] structure Point (f : V → G)
    (comm : ∀ v w, L.Adj v w → Commute (f v) (f w)) where
  base : G
  coord : V → ℝ
  nonneg : ∀ v, 0 ≤ coord v
  lt_one : ∀ v, coord v < 1
  clique : {v | coord v ≠ 0}.Pairwise L.Adj

variable {L f comm}

def active (p : Point (G := G) L f comm) : Finset V := Finset.univ.filter (fun v => p.coord v ≠ 0)

@[simp] theorem mem_active (p : Point (G := G) L f comm) (v : V) :
    v ∈ active p ↔ p.coord v ≠ 0 := by simp [active]

def pointCell (p : Point (G := G) L f comm) : Cell (G := G) L :=
  ⟨p.base, active p, fun _ hv _ hw hne => p.clique
    ((mem_active _ _).mp hv) ((mem_active _ _).mp hw) hne⟩

variable (f comm)

def product (s : Finset V) (hs : (s : Set V).Pairwise L.Adj) : G :=
  s.noncommProd f (fun v hv w hw hne => comm v w (hs hv hw hne))

omit [Fintype V] in
@[simp] theorem product_empty : product f comm ∅ (by simp) = 1 := by
  exact Finset.noncommProd_empty _ _

abbrev Coordinates (c : Cell (G := G) L) := c.directions → Set.Icc (0 : ℝ) 1

def ones (c : Cell (G := G) L) (x : Coordinates c) : Finset V :=
  c.directions.attach.filter (fun v => (x v : ℝ) = 1) |>.image Subtype.val

omit [Group G] [Fintype V] in
@[simp] theorem mem_ones (c : Cell (G := G) L) (x : Coordinates c) (v : V) :
    v ∈ ones c x ↔ ∃ h : v ∈ c.directions, (x ⟨v,h⟩ : ℝ) = 1 := by
  simp [ones]

omit [Group G] [Fintype V] in
theorem ones_subset (c : Cell (G := G) L) (x : Coordinates c) :
    ones c x ⊆ c.directions := by
  intro v hv
  exact ((mem_ones c x v).mp hv).1

def normalizedCoord (c : Cell (G := G) L) (x : Coordinates c) (v : V) : ℝ :=
  if h : v ∈ c.directions then if (x ⟨v,h⟩ : ℝ) = 1 then 0 else x ⟨v,h⟩ else 0

omit [Group G] [Fintype V] in
@[simp] theorem normalizedCoord_mem (c : Cell (G := G) L) (x : Coordinates c)
    (v : c.directions) :
    normalizedCoord c x v = if (x v : ℝ) = 1 then (0 : ℝ) else (x v : ℝ) := by
  simp [normalizedCoord,v.property]

omit [Group G] [Fintype V] in
@[simp] theorem normalizedCoord_notMem (c : Cell (G := G) L) (x : Coordinates c)
    {v : V} (hv : v ∉ c.directions) : normalizedCoord c x v = 0 := by
  simp [normalizedCoord,hv]

/-- Boundary coordinates equal to1 translate the initial vertex; coordinates0
or1 are dropped from the unique open face. -/
def characteristic (c : Cell (G := G) L) (x : Coordinates c) : Point (G := G) L f comm where
  base := c.base * product f comm (ones c x) (c.clique.mono (ones_subset c x))
  coord := normalizedCoord c x
  nonneg v := by
    by_cases h : v ∈ c.directions
    · simp only [normalizedCoord,dite_eq_left h]
      split_ifs
      · exact le_rfl
      · exact (x ⟨v,h⟩).property.1
    · simp [normalizedCoord,h]
  lt_one v := by
    by_cases h : v ∈ c.directions
    · simp only [normalizedCoord,dite_eq_left h]
      split_ifs with he
      · norm_num
      · exact lt_of_le_of_ne (x ⟨v,h⟩).property.2 he
    · simp [normalizedCoord,h]
  clique := by
    intro v hv w hw hne
    have hv' : v ∈ c.directions := by
      by_contra h
      exact hv (normalizedCoord_notMem c x h)
    have hw' : w ∈ c.directions := by
      by_contra h
      exact hw (normalizedCoord_notMem c x h)
    exact c.clique hv' hw' hne

omit [Fintype V] in
@[simp] theorem characteristic_coord (c : Cell (G := G) L) (x : Coordinates c) (v : V) :
    (characteristic f comm c x).coord v = normalizedCoord c x v := rfl

variable {f comm}

/-- Canonical coordinates in the unique open cell. -/
def pointCoordinates (p : Point (G := G) L f comm) : Coordinates (pointCell p) :=
  fun v => ⟨p.coord v, p.nonneg v, (p.lt_one v).le⟩

@[simp] theorem pointCoordinates_coe (p : Point (G := G) L f comm) (v : (pointCell p).directions) :
    (pointCoordinates p v : ℝ) = p.coord v := rfl

@[simp] theorem ones_pointCoordinates (p : Point (G := G) L f comm) :
    ones (pointCell p) (pointCoordinates p) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨h,hh⟩ := (mem_ones _ _ _).mp hv
  exact (p.lt_one v).ne hh

variable (f comm)

@[simp] theorem characteristic_point (p : Point (G := G) L f comm) :
    characteristic f comm (pointCell p) (pointCoordinates p) = p := by
  apply Point.ext
  · change p.base * product f comm (ones (pointCell p) (pointCoordinates p)) _ = p.base
    simp only [product,ones_pointCoordinates,Finset.noncommProd_empty,mul_one]
  · funext v
    by_cases h : p.coord v = 0
    · simp [characteristic,normalizedCoord,pointCell,h]
    · simp [characteristic,normalizedCoord,pointCell,h,pointCoordinates,(p.lt_one v).ne]

abbrev CubeSum := (c : Cell (G := G) L) × Coordinates c

def evaluation : CubeSum (G := G) (L := L) → Point (G := G) L f comm :=
  fun z => characteristic f comm z.1 z.2

 theorem evaluation_surjective : Function.Surjective (evaluation f comm (L := L)) := by
  intro p
  exact ⟨⟨pointCell p,pointCoordinates p⟩, characteristic_point f comm p⟩

/-- The weak topology of the actual closed cubes, without asserting any missing
geometric/homological properties of this construction. -/
instance pointTopology : TopologicalSpace (Point (G := G) L f comm) :=
  TopologicalSpace.coinduced (evaluation f comm) inferInstance

 theorem evaluation_quotient : IsQuotientMap (evaluation f comm (L := L)) :=
  ⟨⟨rfl⟩,evaluation_surjective f comm⟩

 theorem characteristic_continuous (c : Cell (G := G) L) :
    Continuous (characteristic f comm c) :=
  (evaluation_quotient f comm).continuous.comp (continuous_sigmaMk (i := c))

end EilenbergGanea.CubeRealization

open Classical Set Topology
namespace EilenbergGanea.CubeInterpolation
variable {G V : Type*} [Group G]

def translation : G →* Module.End ℝ (G → ℝ) where
  toFun g :=
    { toFun := fun φ a => φ (a*g)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext φ a; simp
  map_mul' g h := by ext φ a; simp [mul_assoc]

@[simp] theorem translation_apply (g a : G) (φ : G → ℝ) :
    translation g φ a = φ (a*g) := rfl

def blend (g : G) (x : ℝ) : Module.End ℝ (G → ℝ) :=
  (1-x) • 1 + x • translation g

@[simp] theorem blend_apply (g a : G) (x : ℝ) (φ : G → ℝ) :
    blend g x φ a = (1-x)*φ a + x*φ (a*g) := rfl

@[simp] theorem blend_zero (g : G) : blend g 0 = 1 := by simp [blend]
@[simp] theorem blend_one (g : G) : blend g 1 = translation g := by simp [blend]

theorem blend_commute {g h : G} (hgh : Commute g h) (x y : ℝ) :
    Commute (blend g x) (blend h y) := by
  unfold blend
  exact ((Commute.one_left _).smul_left _).add_left
    (((Commute.one_right _).smul_right _).add_right
      (((hgh.map translation).smul_left _).smul_right _))

variable (f : V → G)

def operator (s : Finset V) (hs : (s : Set V).Pairwise (fun v w => Commute (f v) (f w)))
    (x : V → ℝ) : Module.End ℝ (G → ℝ) :=
  s.noncommProd (fun v => blend (f v) (x v))
    (fun _ hv _ hw hne => blend_commute (hs hv hw hne) _ _)

@[simp] theorem operator_empty (x : V → ℝ) : operator f ∅ (by simp) x = 1 := rfl

@[simp] theorem operator_insert (s : Finset V) (v : V) (hv : v ∉ s)
    (hs : (↑(insert v s) : Set V).Pairwise (fun v w => Commute (f v) (f w))) (x : V → ℝ) :
    operator f (insert v s) hs x = blend (f v) (x v) *
      operator f s (hs.mono (by simp)) x := by
  exact Finset.noncommProd_insert_of_notMem s v _ _ hv

theorem operator_congr (s : Finset V) (hs) {x y : V → ℝ}
    (h : ∀ v ∈ s, x v = y v) : operator f s hs x = operator f s hs y := by
  apply Finset.noncommProd_congr rfl
  intro v hv
  rw [h v hv]

/-- Every cubical interpolation coordinate is a genuine finite polynomial. -/
theorem operator_continuous {Z : Type*} [TopologicalSpace Z]
    (s : Finset V) (hs) (x : Z → V → ℝ) (hx : ∀ v ∈ s, Continuous (fun z => x z v))
    (φ : G → ℝ) (a : G) : Continuous (fun z => operator f s hs (x z) φ a) := by
  induction s using Finset.induction_on generalizing a with
  | empty => simpa using (continuous_const : Continuous (fun _ : Z => φ a))
  | @insert v s hv ih =>
    simp only [operator_insert f s v hv, Module.End.mul_apply,blend_apply]
    exact (((continuous_const.sub (hx v (by simp))).mul
      (ih _ (fun w hw => hx w (by simp [hw])) a)).add
      ((hx v (by simp)).mul (ih _ (fun w hw => hx w (by simp [hw])) (a*f v))))

/-- Zero coordinates may be deleted without changing the interpolation. -/
theorem operator_subset (s t : Finset V) (ht : (t : Set V).Pairwise (fun v w => Commute (f v) (f w)))
    (hst : s ⊆ t) (x : V → ℝ) (hx : ∀ v ∈ t, v ∉ s → x v = 0) :
    operator f t ht x = operator f s (ht.mono hst) x := by
  induction t using Finset.induction_on generalizing s with
  | empty => have : s = ∅ := Finset.subset_empty.mp hst; subst s; rfl
  | @insert v t hv ih =>
    have ht' : (t : Set V).Pairwise (fun v w => Commute (f v) (f w)) :=
      ht.mono (by simp)
    by_cases hvs : v ∈ s
    · have hsub : s.erase v ⊆ t := by
        intro w hw
        exact Finset.mem_of_mem_insert_of_ne (hst (Finset.mem_erase.mp hw).2)
          (Finset.mem_erase.mp hw).1
      have hx' : ∀ w ∈ t, w ∉ s.erase v → x w = 0 := by
        intro w hw hn
        apply hx w (by simp [hw])
        intro hws
        exact hn (Finset.mem_erase.mpr ⟨ne_of_mem_of_not_mem hw hv,hws⟩)
      have he := ih (s.erase v) ht' hsub hx'
      have hs' : (↑(insert v (s.erase v)) : Set V).Pairwise
          (fun v w => Commute (f v) (f w)) := by
        simpa only [Finset.insert_erase hvs] using ht.mono hst
      have hr : operator f s (ht.mono hst) x = blend (f v) (x v) *
          operator f (s.erase v) (ht'.mono hsub) x := by
        simpa only [Finset.insert_erase hvs] using
          operator_insert f (s.erase v) v (Finset.notMem_erase _ _) hs' x
      rw [operator_insert f t v hv,hr,he]
    · have hsub : s ⊆ t := by
        intro w hw
        exact Finset.mem_of_mem_insert_of_ne (hst hw)
          (by intro he; exact hvs (he ▸ hw))
      rw [operator_insert f t v hv,hx v (by simp) hvs,blend_zero,one_mul]
      exact ih s ht' hsub (fun w hw hn => hx w (by simp [hw]) hn)

variable {f}
theorem commute_ite_one (g h : G) (hgh : Commute g h) (P Q : Prop) :
    Commute (if P then g else 1) (if Q then h else 1) := by
  split_ifs <;> first | exact hgh | exact Commute.one_left _ | exact Commute.one_right _
theorem noncommProd_ite (s : Finset V) (hs : (s : Set V).Pairwise
    (fun v w => Commute (f v) (f w))) (P : V → Prop) :
    s.noncommProd (fun v => if P v then f v else 1)
      (fun _ hv _ hw he => commute_ite_one _ _ (hs hv hw he) _ _) =
    (s.filter P).noncommProd f (hs.mono (Finset.filter_subset _ _)) := by
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert v s hv ih =>
    erw [Finset.noncommProd_insert_of_notMem _ _ _ _ hv]
    by_cases hp : P v
    · simp only [Finset.filter_insert, ite_eq_left hp]
      erw [Finset.noncommProd_insert_of_notMem _ _ _ _
        (fun h => hv (Finset.mem_of_mem_filter _ h)), ih (hs.mono (by simp))]
    · simp only [Finset.filter_insert, ite_eq_right hp, one_mul]
      exact ih (hs.mono (by simp))

def normalize (x : V → ℝ) (v : V) : ℝ := if x v = 1 then 0 else x v

theorem translation_blend_commute {a b : G} (h : Commute a b) (x : ℝ) :
    Commute (translation a) (blend b x) :=
  ((Commute.one_right _).smul_right _).add_right ((h.map translation).smul_right _)

variable (f)
theorem operator_normalize (s : Finset V) (hs : (s : Set V).Pairwise
    (fun v w => Commute (f v) (f w))) (x : V → ℝ) :
    operator f s hs x =
      translation ((s.filter (fun v => x v = 1)).noncommProd f
        (hs.mono (Finset.filter_subset _ _))) * operator f s hs (normalize x) := by
  let a : V → G := fun v => if x v = 1 then f v else 1
  have ha : (s : Set V).Pairwise (fun v w => Commute (a v) (a w)) :=
    fun _ hv _ hw he => commute_ite_one _ _ (hs hv hw he) _ _
  have ht : (s : Set V).Pairwise (fun v w => Commute (translation (a v)) (translation (a w))) :=
    fun _ hv _ hw he => (ha hv hw he).map translation
  have hb : (s : Set V).Pairwise (fun v w =>
      Commute (blend (f v) (normalize x v)) (blend (f w) (normalize x w))) :=
    fun _ hv _ hw he => blend_commute (hs hv hw he) _ _
  have hbt : (s : Set V).Pairwise (fun v w =>
      Commute (blend (f v) (normalize x v)) (translation (a w))) := by
    intro v hv w hw he
    dsimp [a]
    split_ifs
    · exact (translation_blend_commute (hs hw hv he.symm) _).symm
    · simp only [map_one]; exact Commute.one_right _
  have hfactor : operator f s hs x =
      s.noncommProd ((fun v => translation (a v)) * (fun v => blend (f v) (normalize x v)))
        (Finset.noncommProd_mul_distrib_aux ht hb hbt) := by
    apply Finset.noncommProd_congr rfl
    intro v _
    dsimp [a,normalize]
    split_ifs with hv
    · simp [hv]
    · simp
  rw [hfactor,Finset.noncommProd_mul_distrib _ _ ht hb hbt,
    ← Finset.map_noncommProd s a ha translation]
  congr 1
  congr 1
  exact noncommProd_ite s hs (fun v => x v = 1)

/-- Nonnegative vertex data interpolate nonnegatively throughout every cube. -/
theorem operator_nonneg (s : Finset V) (hs) (x : V → ℝ)
    (hx : ∀ v ∈ s, x v ∈ Set.Icc (0 : ℝ) 1)
    (φ : G → ℝ) (hφ : ∀ a, 0 ≤ φ a) (a : G) : 0 ≤ operator f s hs x φ a := by
  induction s using Finset.induction_on generalizing a with
  | empty => exact hφ a
  | @insert v s hv ih =>
    rw [operator_insert f s v hv,Module.End.mul_apply,blend_apply]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr (hx v (by simp)).2)
      (ih _ (fun w hw => hx w (by simp [hw])) a))
      (mul_nonneg (hx v (by simp)).1 (ih _ (fun w hw => hx w (by simp [hw])) (a*f v)))

/-- The initial vertex has strictly positive weight in its own open cube. -/
theorem operator_pos (s : Finset V) (hs) (x : V → ℝ)
    (hx : ∀ v ∈ s, x v ∈ Set.Ico (0 : ℝ) 1)
    (φ : G → ℝ) (hφ : ∀ a, 0 ≤ φ a) (a : G) (ha : 0 < φ a) :
    0 < operator f s hs x φ a := by
  induction s using Finset.induction_on generalizing a with
  | empty => exact ha
  | @insert v s hv ih =>
    rw [operator_insert f s v hv,Module.End.mul_apply,blend_apply]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr (hx v (by simp)).2)
        (ih _ (fun w hw => hx w (by simp [hw])) a ha))
      (mul_nonneg (hx v (by simp)).1
        (operator_nonneg f s _ x (fun w hw => ⟨(hx w (by simp [hw])).1,
          (hx w (by simp [hw])).2.le⟩) φ hφ (a*f v)))

/-- No interpolation value detects a vertex below its initial height. At the
initial height it detects only the initial vertex itself. -/
theorem operator_vanish (h : G →* Multiplicative ℤ) (hf : ∀ v, (h (f v)).toAdd = 1)
    (s : Finset V) (hs) (x : V → ℝ) (φ : G → ℝ) (a : G)
    (ha : φ a = 0) (hφ : ∀ b, (h a).toAdd < (h b).toAdd → φ b = 0) :
    operator f s hs x φ a = 0 := by
  induction s using Finset.induction_on generalizing a with
  | empty => exact ha
  | @insert v s hv ih =>
    rw [operator_insert f s v hv,Module.End.mul_apply,blend_apply,ih _ a ha hφ]
    have hstep : (h a).toAdd < (h (a * f v)).toAdd := by
      simp only [map_mul,toAdd_mul,hf]
      omega
    rw [ih _ (a*f v) (hφ _ hstep) (fun b hb => hφ b (hstep.trans hb))]
    ring

/-- Interpolation of a group homomorphism is the ordinary affine coordinate. -/
theorem operator_linear (h : G →* Multiplicative ℝ) (s : Finset V) (hs)
    (x : V → ℝ) (a : G) :
    operator f s hs x (fun a => (h a).toAdd) a =
      (h a).toAdd + ∑ v ∈ s, x v * (h (f v)).toAdd := by
  induction s using Finset.induction_on generalizing a with
  | empty => simp
  | @insert v s hv ih =>
    rw [operator_insert f s v hv,Module.End.mul_apply,blend_apply,
      ih _ a,ih _ (a*f v),Finset.sum_insert hv]
    simp only [map_mul,toAdd_mul]
    ring

end EilenbergGanea.CubeInterpolation

namespace EilenbergGanea.CubeRealization

section
open CubeInterpolation
variable {G V : Type*} [Group G] [Fintype V]
variable (L : SimpleGraph V) (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))

include comm in
omit [Fintype V] in
theorem cellComm (c : Cell (G := G) L) : (c.directions : Set V).Pairwise
    (fun v w => Commute (f v) (f w)) :=
  fun _ hv _ hw he => comm _ _ (c.clique hv hw he)

variable {L}

def fullCoord (c : Cell (G := G) L) (x : Coordinates c) (v : V) : ℝ :=
  if h : v ∈ c.directions then x ⟨v,h⟩ else 0

omit [Group G] [Fintype V] in
@[simp] theorem fullCoord_mem (c : Cell (G := G) L) (x : Coordinates c) (v : c.directions) :
    fullCoord c x v = (x v : ℝ) := by simp [fullCoord,v.property]

omit [Group G] [Fintype V] in
@[simp] theorem fullCoord_notMem (c : Cell (G := G) L) (x : Coordinates c) {v : V}
    (hv : v ∉ c.directions) : fullCoord c x v = 0 := by simp [fullCoord,hv]

omit [Group G] [Fintype V] in
theorem fullCoord_continuous (c : Cell (G := G) L) (v : V) :
    Continuous (fun x : Coordinates c => fullCoord c x v) := by
  unfold fullCoord
  split_ifs
  · exact continuous_subtype_val.comp (continuous_apply _)
  · exact continuous_const

omit [Group G] [Fintype V] in
theorem ones_eq_filter (c : Cell (G := G) L) (x : Coordinates c) :
    ones c x = c.directions.filter (fun v => fullCoord c x v = 1) := by
  ext v
  simp only [mem_ones,Finset.mem_filter]
  constructor
  · rintro ⟨hv,hx⟩
    exact ⟨hv,by simpa only [fullCoord,dite_eq_left hv] using hx⟩
  · rintro ⟨hv,hx⟩
    exact ⟨hv,by simpa only [fullCoord,dite_eq_left hv] using hx⟩

omit [Group G] [Fintype V] in
theorem normalize_fullCoord (c : Cell (G := G) L) (x : Coordinates c) :
    CubeInterpolation.normalize (fullCoord c x) = normalizedCoord c x := by
  funext v
  by_cases hv : v ∈ c.directions
  · simp only [CubeInterpolation.normalize,fullCoord,normalizedCoord,dite_eq_left hv]
  · simp [CubeInterpolation.normalize,fullCoord,normalizedCoord,hv]

variable (L)

def interpolation (p : Point (G := G) L f comm) (φ : G → ℝ) : ℝ :=
  operator f (active p) (cellComm L f comm (pointCell p)) p.coord φ p.base

theorem active_characteristic_subset (c : Cell (G := G) L) (x : Coordinates c) :
    active (characteristic f comm c x) ⊆ c.directions := by
  intro v hv
  by_contra h
  exact ((mem_active _ _).mp hv) (normalizedCoord_notMem c x h)

/-- Literal face compatibility of multilinear vertex interpolation. -/
theorem interpolation_characteristic (c : Cell (G := G) L) (x : Coordinates c) (φ : G → ℝ) :
    interpolation L f comm (characteristic f comm c x) φ =
      operator f c.directions (cellComm L f comm c) (fullCoord c x) φ c.base := by
  have hsub := active_characteristic_subset L f comm c x
  have he := operator_subset f (active (characteristic f comm c x)) c.directions
    (cellComm L f comm c) hsub (normalizedCoord c x) (by
      intro v _ hn
      exact not_not.mp (by simpa only [mem_active,characteristic_coord] using hn))
  have hn := operator_normalize f c.directions (cellComm L f comm c) (fullCoord c x)
  simp only [normalize_fullCoord,← ones_eq_filter] at hn
  have hh := congrArg (fun T : Module.End ℝ (G → ℝ) => T φ c.base) hn
  rw [Module.End.mul_apply,translation_apply,he] at hh
  exact hh.symm

/-- These separating coordinates are continuous for the actual weak topology. -/
theorem interpolation_continuous (φ : G → ℝ) :
    Continuous (fun p : Point (G := G) L f comm => interpolation L f comm p φ) := by
  apply (evaluation_quotient f comm).continuous_iff.mpr
  apply continuous_sigma
  intro c
  change Continuous (fun x : Coordinates c => interpolation L f comm (characteristic f comm c x) φ)
  simp only [interpolation_characteristic]
  exact operator_continuous f c.directions _ (fullCoord c)
    (fun v _ => fullCoord_continuous c v) φ c.base

variable (h : G →* Multiplicative ℤ) (hf : ∀ v, (h (f v)).toAdd = 1)

theorem interpolation_vertex_pos (p : Point (G := G) L f comm) :
    0 < interpolation L f comm p (fun a => if a = p.base then 1 else 0) := by
  apply operator_pos
  · intro v _; exact ⟨p.nonneg v,p.lt_one v⟩
  · intro a; split_ifs <;> norm_num
  · simp

include hf in
theorem interpolation_vertex_zero (p : Point (G := G) L f comm) (b : G)
    (hb : (h b).toAdd ≤ (h p.base).toAdd) (hne : b ≠ p.base) :
    interpolation L f comm p (fun a => if a = b then 1 else 0) = 0 := by
  apply operator_vanish f h hf
  · simp [hne.symm]
  · intro a ha
    have hab : a ≠ b := by intro he; subst a; omega
    simp [hab]

include h hf in
theorem interpolation_base_eq (p q : Point (G := G) L f comm)
    (he : ∀ φ, interpolation L f comm p φ = interpolation L f comm q φ) :
    p.base = q.base := by
  have height_le (p q : Point (G := G) L f comm)
      (he : ∀ φ, interpolation L f comm p φ = interpolation L f comm q φ) :
      (h p.base).toAdd ≤ (h q.base).toAdd := by
    by_contra hn
    have hlt : (h q.base).toAdd < (h p.base).toAdd := lt_of_not_ge hn
    have hne : q.base ≠ p.base := by intro eq; rw [eq] at hlt; exact lt_irrefl _ hlt
    have hz := interpolation_vertex_zero L f comm h hf p q.base hlt.le hne
    have hp := interpolation_vertex_pos L f comm q
    rw [← he,hz] at hp
    exact lt_irrefl _ hp
  have h₁ := height_le p q he
  by_contra hne
  have hz := interpolation_vertex_zero L f comm h hf q p.base h₁ hne
  have hp := interpolation_vertex_pos L f comm p
  rw [he,hz] at hp
  exact lt_irrefl _ hp

variable (exponent : V → G →* Multiplicative ℝ)
variable (hexponent : ∀ v w, (exponent v (f w)).toAdd = if v = w then 1 else 0)

include hexponent in
theorem interpolation_exponent (p : Point (G := G) L f comm) (v : V) :
    interpolation L f comm p (fun a => (exponent v a).toAdd) =
      (exponent v p.base).toAdd + p.coord v := by
  unfold interpolation
  erw [operator_linear]
  congr 1
  simp only [hexponent,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq]
  by_cases hv : p.coord v = 0
  · simp [hv]
  · simp [mem_active,hv]

include h hf exponent hexponent in
/-- Interpolation distances separate actual points, not merely vertices. -/
theorem interpolation_injective : Function.Injective
    (fun p : Point (G := G) L f comm => fun φ : G → ℝ => interpolation L f comm p φ) := by
  intro p q he
  have he' : ∀ φ, interpolation L f comm p φ = interpolation L f comm q φ :=
    fun φ => congrFun he φ
  have hb := interpolation_base_eq L f comm h hf p q he'
  apply Point.ext hb
  funext v
  have hv := he' (fun a => (exponent v a).toAdd)
  rw [interpolation_exponent L f comm exponent hexponent,
    interpolation_exponent L f comm exponent hexponent,hb] at hv
  exact add_left_cancel hv

include h hf exponent hexponent in
/-- Hausdorffness follows from continuous multilinear vertex functions. -/
theorem point_t2 : T2Space (Point (G := G) L f comm) :=
  T2Space.of_injective_continuous
    (interpolation_injective L f comm h hf exponent hexponent)
    (continuous_pi (fun φ => interpolation_continuous L f comm φ))

end

section
open Metric
variable {G V : Type*} [Group G] [Fintype V]
variable {L : SimpleGraph V} (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))

omit [Group G] [Fintype V] in
@[ext] theorem Cell.ext {c d : Cell (G := G) L} (hb : c.base = d.base)
    (hd : c.directions = d.directions) : c = d := by
  cases c; cases d; simp_all

abbrev DimCell (n : ℕ) := {c : Cell (G := G) L // c.directions.card = n}

variable {f comm}
def coordEquiv {n : ℕ} (c : DimCell (G := G) (L := L) n) : c.val.directions ≃ Fin n :=
  Finset.equivFinOfCardEq c.property

def chartCoordinates {n : ℕ} (c : DimCell (G := G) (L := L) n) (t : Fin n → ℝ) :
    Coordinates c.val := fun v => projIcc 0 1 (by norm_num) ((t (coordEquiv c v) + 1) / 2)

def cubeCoordinatesInv {n : ℕ} (c : DimCell (G := G) (L := L) n) (x : Coordinates c.val) :
    Fin n → ℝ := fun i => 2 * (x ((coordEquiv c).symm i) : ℝ) - 1

omit [Group G] [Fintype V] in
theorem chartCoordinates_continuous {n : ℕ} (c : DimCell (G := G) (L := L) n) :
    Continuous (chartCoordinates c) := by
  apply continuous_pi
  intro v
  exact continuous_projIcc.comp (((continuous_apply _).add continuous_const).div_const 2)

omit [Group G] [Fintype V] in
theorem cubeCoordinatesInv_continuous {n : ℕ} (c : DimCell (G := G) (L := L) n) :
    Continuous (cubeCoordinatesInv c) := by
  apply continuous_pi
  intro i
  exact (continuous_const.mul (continuous_subtype_val.comp (continuous_apply _))).sub continuous_const

omit [Group G] [Fintype V] in
theorem cubeCoordinatesInv_mem_disk {n : ℕ} (c : DimCell (G := G) (L := L) n)
    (x : Coordinates c.val) : cubeCoordinatesInv c x ∈ closedBall 0 1 := by
  rw [mem_closedBall_zero_iff,pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  rw [Real.norm_eq_abs,abs_le]
  have hx := (x ((coordEquiv c).symm i)).property
  dsimp [cubeCoordinatesInv]
  constructor <;> linarith [hx.1,hx.2]

omit [Group G] [Fintype V] in
theorem chartCoordinates_cubeCoordinatesInv {n : ℕ} (c : DimCell (G := G) (L := L) n)
    (x : Coordinates c.val) : chartCoordinates c (cubeCoordinatesInv c x) = x := by
  funext v
  simp only [chartCoordinates,cubeCoordinatesInv,Equiv.symm_apply_apply]
  have ha : (2 * (x v : ℝ) - 1 + 1) / 2 = (x v : ℝ) := by ring
  rw [ha,projIcc_val]

omit [Group G] [Fintype V] in
theorem chartCoordinates_disk {n : ℕ} (c : DimCell (G := G) (L := L) n)
    {t : Fin n → ℝ} (ht : t ∈ closedBall 0 1) (v : c.val.directions) :
    (chartCoordinates c t v : ℝ) = (t (coordEquiv c v) + 1) / 2 := by
  rw [mem_closedBall_zero_iff,pi_norm_le_iff_of_nonneg (by norm_num)] at ht
  have hv := (abs_le.mp (show |t (coordEquiv c v)| ≤ 1 from ht _))
  unfold chartCoordinates
  rw [projIcc_of_mem (by norm_num) (show (t (coordEquiv c v) + 1) / 2 ∈ Icc (0 : ℝ) 1 by
    constructor <;> linarith [hv.1,hv.2])]

omit [Group G] [Fintype V] in
theorem chartCoordinates_open {n : ℕ} (c : DimCell (G := G) (L := L) n)
    {t : Fin n → ℝ} (ht : t ∈ ball 0 1) (v : c.val.directions) :
    (chartCoordinates c t v : ℝ) ∈ Ioo (0 : ℝ) 1 := by
  rw [chartCoordinates_disk c (ball_subset_closedBall ht)]
  rw [mem_ball_zero_iff,pi_norm_lt_iff (by norm_num)] at ht
  have hv := abs_lt.mp (show |t (coordEquiv c v)| < 1 from ht _)
  constructor <;> linarith [hv.1,hv.2]

omit [Group G] [Fintype V] in
theorem cubeCoordinatesInv_open {n : ℕ} (c : DimCell (G := G) (L := L) n)
    (x : Coordinates c.val) (hx : ∀ v, (x v : ℝ) ∈ Ioo (0 : ℝ) 1) :
    cubeCoordinatesInv c x ∈ ball 0 1 := by
  rw [mem_ball_zero_iff,pi_norm_lt_iff (by norm_num)]
  intro i
  rw [Real.norm_eq_abs,abs_lt]
  dsimp [cubeCoordinatesInv]
  constructor <;> linarith [(hx ((coordEquiv c).symm i)).1,(hx ((coordEquiv c).symm i)).2]

variable (f comm)
theorem characteristic_open_cell (c : Cell (G := G) L) (x : Coordinates c)
    (hx : ∀ v, (x v : ℝ) ∈ Ioo (0 : ℝ) 1) :
    pointCell (characteristic f comm c x) = c := by
  have ho : ones c x = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨h,hh⟩ := (mem_ones c x v).mp hv
    exact (hx ⟨v,h⟩).2.ne hh
  apply Cell.ext
  · change c.base * product f comm (ones c x) _ = c.base
    simp only [product,ho,Finset.noncommProd_empty,mul_one]
  · ext v
    simp only [pointCell,mem_active,characteristic_coord]
    constructor
    · intro hv
      by_contra hh
      exact hv (normalizedCoord_notMem c x hh)
    · intro hv
      simp only [normalizedCoord,dite_eq_left hv,ite_eq_right (hx ⟨v,hv⟩).2.ne]
      exact (hx ⟨v,hv⟩).1.ne'

/-- Real inverse coordinates of an open cube, without any assumed chart. -/
def chartInverse {n : ℕ} (c : DimCell (G := G) (L := L) n)
    (p : Point (G := G) L f comm) : Fin n → ℝ :=
  fun i => 2 * p.coord ((coordEquiv c).symm i) - 1

omit [Fintype V] in
theorem chart_left_inv {n : ℕ} (c : DimCell (G := G) (L := L) n)
    {t : Fin n → ℝ} (ht : t ∈ ball 0 1) :
    chartInverse f comm c (characteristic f comm c.val (chartCoordinates c t)) = t := by
  funext i
  have he := (chartCoordinates_open c ht ((coordEquiv c).symm i)).2.ne
  simp only [chartInverse, characteristic_coord, normalizedCoord_mem]
  rw [ite_eq_right he,chartCoordinates_disk c (ball_subset_closedBall ht),Equiv.apply_symm_apply]
  ring

theorem chart_right_inv {n : ℕ} (c : DimCell (G := G) (L := L) n)
    (p : Point (G := G) L f comm) (hp : pointCell p = c.val) :
    characteristic f comm c.val (chartCoordinates c (chartInverse f comm c p)) = p := by
  obtain ⟨c,hc⟩ := c
  dsimp at hp
  subst c
  have he : chartInverse f comm ⟨pointCell p,hc⟩ p =
      cubeCoordinatesInv ⟨pointCell p,hc⟩ (pointCoordinates p) := rfl
  rw [he,chartCoordinates_cubeCoordinatesInv,characteristic_point]

theorem chartInverse_mem_source {n : ℕ} (c : DimCell (G := G) (L := L) n)
    (p : Point (G := G) L f comm) (hp : pointCell p = c.val) :
    chartInverse f comm c p ∈ ball 0 1 := by
  obtain ⟨c,hc⟩ := c
  dsimp at hp
  subst c
  apply cubeCoordinatesInv_open ⟨pointCell p,hc⟩ (pointCoordinates p)
  intro v
  exact ⟨lt_of_le_of_ne (p.nonneg v) (by
    exact ((mem_active p v).mp v.property).symm),p.lt_one v⟩

/-- The actual positive-cube open chart. -/
def chart {n : ℕ} (c : DimCell (G := G) (L := L) n) :
    PartialEquiv (Fin n → ℝ) (Point (G := G) L f comm) where
  toFun t := characteristic f comm c.val (chartCoordinates c t)
  invFun := chartInverse f comm c
  source := ball 0 1
  target := {p | pointCell p = c.val}
  map_source' := fun _ ht => characteristic_open_cell f comm _ _ (chartCoordinates_open c ht)
  map_target' := chartInverse_mem_source f comm c
  left_inv' := fun _ ht => chart_left_inv f comm c ht
  right_inv' := chart_right_inv f comm c

theorem chart_continuous {n : ℕ} (c : DimCell (G := G) (L := L) n) :
    Continuous (chart f comm c) :=
  (characteristic_continuous f comm c.val).comp (chartCoordinates_continuous c)

variable (exponent : V → G →* Multiplicative ℝ)
variable (hexponent : ∀ v w, (exponent v (f w)).toAdd = if v = w then 1 else 0)
include exponent hexponent in
theorem chartInverse_continuousOn {n : ℕ} (c : DimCell (G := G) (L := L) n) :
    ContinuousOn (chart f comm c).symm (chart f comm c).target := by
  have hh : Continuous (fun p : Point (G := G) L f comm => fun i : Fin n =>
      2 * (interpolation L f comm p (fun a => (exponent ((coordEquiv c).symm i) a).toAdd) -
        (exponent ((coordEquiv c).symm i) c.val.base).toAdd) - 1) := by
    apply continuous_pi
    intro i
    exact (continuous_const.mul ((interpolation_continuous L f comm _).sub continuous_const)).sub
      continuous_const
  apply hh.continuousOn.congr
  intro p hp
  have hb : p.base = c.val.base := congrArg Cell.base hp
  funext i
  simp only [chart,PartialEquiv.coe_symm_mk,chartInverse,
    interpolation_exponent L f comm exponent hexponent,hb]
  ring

end

open Metric
variable {G V : Type*} [Group G] [Fintype V]
variable {L : SimpleGraph V} (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))

omit [Group G] [Fintype V] in
theorem cubeCoordinatesInv_chart {n : ℕ} (c : DimCell (G := G) (L := L) n)
    {t : Fin n → ℝ} (ht : t ∈ closedBall 0 1) :
    cubeCoordinatesInv c (chartCoordinates c t) = t := by
  funext i
  simp only [cubeCoordinatesInv,chartCoordinates_disk c ht,Equiv.apply_symm_apply]
  ring

@[simp] theorem chart_image_disk {n : ℕ} (c : DimCell (G := G) (L := L) n) :
    chart f comm c '' closedBall 0 1 = Set.range (characteristic f comm c.val) := by
  ext p
  constructor
  · rintro ⟨t,_,rfl⟩
    exact ⟨chartCoordinates c t,rfl⟩
  · rintro ⟨x,rfl⟩
    exact ⟨cubeCoordinatesInv c x,cubeCoordinatesInv_mem_disk c x,
      congrArg (characteristic f comm c.val) (chartCoordinates_cubeCoordinatesInv c x)⟩

@[simp] theorem chart_image_ball {n : ℕ} (c : DimCell (G := G) (L := L) n) :
    chart f comm c '' ball 0 1 = {p | pointCell p = c.val} :=
  (chart f comm c).image_source_eq_target

/-- Finite collection containing every closed face of a fixed cube. -/
def faceCell (c : Cell (G := G) L) (o a : Finset V) : Cell (G := G) L where
  base := c.base * product f comm (c.directions ∩ o) (c.clique.mono Finset.inter_subset_left)
  directions := c.directions ∩ a
  clique := c.clique.mono Finset.inter_subset_left

def faces (c : Cell (G := G) L) : Finset (Cell (G := G) L) :=
  Finset.univ.image (fun p : Finset V × Finset V => faceCell f comm c p.1 p.2)

def dimFaces (c : Cell (G := G) L) (m : ℕ) : Finset (DimCell (G := G) (L := L) m) :=
  (faces f comm c).subtype (fun d => d.directions.card = m)

theorem pointCell_characteristic_mem_faces (c : Cell (G := G) L) (x : Coordinates c) :
    pointCell (characteristic f comm c x) ∈ faces f comm c := by
  apply Finset.mem_image.mpr
  refine ⟨(ones c x,active (characteristic f comm c x)),Finset.mem_univ _,?_⟩
  apply Cell.ext
  · simp only [faceCell,Finset.inter_eq_right.mpr (ones_subset c x)]
    rfl
  · simp only [faceCell,Finset.inter_eq_right.mpr (active_characteristic_subset L f comm c x)]
    rfl

/-- Every point on a characteristic sphere lies in a strictly lower open cube. -/
theorem boundary_dimension_lt {n : ℕ} (c : DimCell (G := G) (L := L) n)
    {t : Fin n → ℝ} (ht : t ∈ sphere 0 1) :
    (pointCell (chart f comm c t)).directions.card < n := by
  let x := chartCoordinates c t
  have hs := active_characteristic_subset L f comm c.val x
  by_contra h
  change ¬ (active (characteristic f comm c.val x)).card < n at h
  have he : active (characteristic f comm c.val x) = c.val.directions :=
    Finset.eq_of_subset_of_card_le hs (by simpa only [c.property] using le_of_not_gt h)
  have hx : ∀ v : c.val.directions, (x v : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    intro v
    have hv : normalizedCoord c.val x v ≠ 0 := by
      have hv' : v.val ∈ active (characteristic f comm c.val x) := he.symm ▸ v.property
      exact (mem_active _ _).mp hv'
    rw [normalizedCoord_mem] at hv
    have hne : (x v : ℝ) ≠ 1 := by
      intro hh
      exact hv (by simp only [hh,ite_true])
    rw [ite_eq_right hne] at hv
    exact ⟨lt_of_le_of_ne (x v).property.1 (Ne.symm hv),
      lt_of_le_of_ne (x v).property.2 hne⟩
  have hi := cubeCoordinatesInv_open c x hx
  rw [show x = chartCoordinates c t from rfl,
    cubeCoordinatesInv_chart c (mem_closedBall.mpr (mem_sphere.mp ht).le)] at hi
  exact (ne_of_lt (mem_ball.mp hi)) (mem_sphere.mp ht)

theorem chart_mapsTo (n : ℕ) (c : DimCell (G := G) (L := L) n) :
    ∃ I : Π m, Finset (DimCell (G := G) (L := L) m),
      MapsTo (chart f comm c) (sphere 0 1)
        (⋃ (m < n) (j ∈ I m), chart f comm j '' closedBall 0 1) := by
  refine ⟨dimFaces f comm c.val,?_⟩
  intro t ht
  let p := chart f comm c t
  let d : DimCell (G := G) (L := L) (pointCell p).directions.card := ⟨pointCell p,rfl⟩
  have hd : d ∈ dimFaces f comm c.val _ := by
    rw [dimFaces,Finset.mem_subtype]
    exact pointCell_characteristic_mem_faces f comm c.val (chartCoordinates c t)
  refine Set.mem_iUnion.mpr ⟨_,Set.mem_iUnion.mpr ⟨boundary_dimension_lt f comm c ht,
    Set.mem_iUnion.mpr ⟨d,Set.mem_iUnion.mpr ⟨hd,?_⟩⟩⟩⟩
  rw [chart_image_disk]
  exact ⟨pointCoordinates p,characteristic_point f comm p⟩

variable (exponent : V → G →* Multiplicative ℝ)
variable (hexponent : ∀ v w, (exponent v (f w)).toAdd = if v = w then 1 else 0)

/-- The ordinary CW structure follows from the genuine normalized-cube gluing;
no combinatorial homology or contractibility assertion enters this definition. -/
@[instance_reducible] def cwComplex : CWComplex (univ : Set (Point (G := G) L f comm)) where
  cell := DimCell (G := G) (L := L)
  map := fun _ c => chart f comm c
  source_eq := fun _ _ => rfl
  continuousOn := fun _ c => (chart_continuous f comm c).continuousOn
  continuousOn_symm := fun _ c => chartInverse_continuousOn f comm exponent hexponent c
  pairwiseDisjoint' := by
    intro a _ b _ hab
    change Disjoint (chart f comm a.2 '' ball 0 1) (chart f comm b.2 '' ball 0 1)
    rw [chart_image_ball,chart_image_ball]
    apply Set.disjoint_left.mpr
    intro p ha hb
    apply hab
    have he : a.2.val = b.2.val := ha.symm.trans hb
    have hn : a.1 = b.1 := a.2.property.symm.trans ((congrArg (fun c => c.directions.card) he).trans b.2.property)
    cases a with | mk n a =>
      cases b with | mk m b =>
        dsimp at hn
        subst m
        exact congrArg (Sigma.mk n) (Subtype.ext he)
  mapsTo' := chart_mapsTo f comm
  closed' := by
    intro A _ hA
    apply (evaluation_quotient f comm).isClosed_preimage.mp
    rw [isClosed_sigma_iff]
    intro c
    let d : DimCell (G := G) (L := L) c.directions.card := ⟨c,rfl⟩
    have hh := (hA _ d).preimage (characteristic_continuous f comm c)
    rw [chart_image_disk] at hh
    change IsClosed (characteristic f comm c ⁻¹' (A ∩ Set.range (characteristic f comm c))) at hh
    change IsClosed (characteristic f comm c ⁻¹' A)
    simpa only [Set.preimage_inter,Set.preimage_range,Set.inter_univ] using hh
  union' := by
    apply Set.eq_univ_of_forall
    intro p
    let d : DimCell (G := G) (L := L) (pointCell p).directions.card := ⟨pointCell p,rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨_,Set.mem_iUnion.mpr ⟨d,?_⟩⟩
    rw [chart_image_disk]
    exact ⟨pointCoordinates p,characteristic_point f comm p⟩

end EilenbergGanea.CubeRealization

namespace EilenbergGanea.CubeInterpolation
variable {G V : Type*} [Group G] (f : V → G)

/-- A nonzero interpolation value comes from one of the finitely many corners. -/
theorem operator_support (s : Finset V)
    (hs : (s : Set V).Pairwise (fun v w => Commute (f v) (f w)))
    (x : V → ℝ) (φ : G → ℝ) (a : G) (h : operator f s hs x φ a ≠ 0) :
    ∃ (t : Finset V) (ht : t ⊆ s), φ (a * t.noncommProd f (hs.mono ht)) ≠ 0 := by
  induction s using Finset.induction_on generalizing a with
  | empty => exact ⟨∅,Finset.Subset.refl _,by simpa using h⟩
  | @insert v s hv ih =>
      let hs' : (s : Set V).Pairwise (fun v w => Commute (f v) (f w)) :=
        hs.mono (by simp)
      rw [operator_insert f s v hv] at h
      simp only [Module.End.mul_apply,blend_apply] at h
      by_cases ha : operator f s hs' x φ a = 0
      · have hb : operator f s hs' x φ (a*f v) ≠ 0 := by
          intro hh
          exact h (by rw [ha,hh]; ring)
        obtain ⟨t,ht,hh⟩ := ih hs' (a*f v) hb
        have hvt : v ∉ t := fun hm => hv (ht hm)
        refine ⟨insert v t,Finset.insert_subset_insert _ ht,?_⟩
        rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hvt,← mul_assoc]
        exact hh
      · obtain ⟨t,ht,hh⟩ := ih hs' a ha
        exact ⟨t,ht.trans (Finset.subset_insert _ _),hh⟩

end EilenbergGanea.CubeInterpolation

namespace EilenbergGanea.CubeRealization

section
open CubeInterpolation
variable {G V : Type*} [Group G] [Fintype V]
variable (L : SimpleGraph V) (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))

/-- Actual finite cliques, including the empty clique. -/
abbrev CliqueIndex := {s : Finset V // (s : Set V).Pairwise L.Adj}

def cliqueProduct (s : CliqueIndex L) : G := product f comm s.val s.property

def vertexStar (b : G) : Set (Point (G := G) L f comm) :=
  {p | interpolation L f comm p (fun a => if a = b then 1 else 0) ≠ 0}

theorem vertexStar_open (b : G) : IsOpen (vertexStar L f comm b) :=
  isOpen_ne.preimage (interpolation_continuous L f comm _)

theorem mem_vertexStar_self (p : Point (G := G) L f comm) :
    p ∈ vertexStar L f comm p.base := (interpolation_vertex_pos L f comm p).ne'

theorem vertexStar_base {b : G} {p : Point (G := G) L f comm}
    (hp : p ∈ vertexStar L f comm b) :
    ∃ s : CliqueIndex L, p.base = b * (cliqueProduct L f comm s)⁻¹ := by
  obtain ⟨s,hs,he⟩ := operator_support f (active p) ((pointCell p).clique.imp
    (fun {_ _} h => comm _ _ h)) p.coord (fun a => if a = b then 1 else 0) p.base hp
  have hh : p.base * product f comm s ((pointCell p).clique.mono hs) = b := by
    by_contra h
    exact he (ite_eq_right h)
  exact ⟨⟨s,(pointCell p).clique.mono hs⟩,eq_mul_inv_of_mul_eq hh⟩

/-- Only finitely many initial vertices occur in an open vertex star. -/
theorem vertexStar_finite_bases (b : G) :
    (Point.base '' vertexStar L f comm b).Finite := by
  apply (Set.finite_range (fun s : CliqueIndex L => b * (cliqueProduct L f comm s)⁻¹)).subset
  rintro _ ⟨p,hp,rfl⟩
  obtain ⟨s,hs⟩ := vertexStar_base L f comm hp
  exact ⟨s,hs.symm⟩

/-- Every compact set in the actual realization has finitely many initial
vertices. The initial-vertex function itself need not be continuous. -/
theorem compact_finite_bases {K : Set (Point (G := G) L f comm)} (hK : IsCompact K) :
    (Point.base '' K).Finite := by
  have hcover : K ⊆ ⋃ b : G, vertexStar L f comm b := by
    intro p _
    exact Set.mem_iUnion.mpr ⟨p.base,mem_vertexStar_self L f comm p⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (vertexStar L f comm)
    (vertexStar_open L f comm) hcover
  apply (Set.Finite.biUnion s.finite_toSet (fun b _ => vertexStar_finite_bases L f comm b)).subset
  rintro _ ⟨p,hp,rfl⟩
  obtain ⟨b,hbs,hpb⟩ := by simpa only [Set.mem_iUnion] using hs hp
  exact Set.mem_iUnion.mpr ⟨b,Set.mem_iUnion.mpr ⟨hbs,⟨p,hpb,rfl⟩⟩⟩

/-- Every point with prescribed initial vertex belongs to some closed positive
cube at that vertex. -/
def cliqueCell (b : G) (s : CliqueIndex L) : Cell (G := G) L := ⟨b,s.val,s.property⟩

theorem vertexStar_compact_neighborhood (p : Point (G := G) L f comm) :
    ∃ K : Set (Point (G := G) L f comm), K ∈ 𝓝 p ∧ IsCompact K := by
  let C (st : CliqueIndex L × CliqueIndex L) : Cell (G := G) L :=
    cliqueCell L (p.base * (cliqueProduct L f comm st.1)⁻¹) st.2
  let K := ⋃ st, Set.range (characteristic f comm (C st))
  refine ⟨K,?_,?_⟩
  · apply Filter.mem_of_superset ((vertexStar_open L f comm p.base).mem_nhds
      (mem_vertexStar_self L f comm p))
    intro q hq
    obtain ⟨s,hs⟩ := vertexStar_base L f comm hq
    refine Set.mem_iUnion.mpr ⟨(s,⟨active q,(pointCell q).clique⟩),?_⟩
    have he : C (s,⟨active q,(pointCell q).clique⟩) = pointCell q := by
      apply Cell.ext
      · exact hs.symm
      · rfl
    rw [he]
    exact ⟨pointCoordinates q,characteristic_point f comm q⟩
  · apply isCompact_iUnion
    intro st
    exact isCompact_range (characteristic_continuous f comm (C st))

/-- Local compactness is proved from finite generator stars and the actual
closed-cube maps, not asserted as a cubical-model input. -/
theorem point_weaklyLocallyCompact : WeaklyLocallyCompactSpace (Point (G := G) L f comm) :=
  ⟨fun p => by
    obtain ⟨K,hK,hcompact⟩ := vertexStar_compact_neighborhood L f comm p
    exact ⟨K,hcompact,hK⟩⟩

end

variable {G V : Type*} [Group G] [Fintype V]
variable {L : SimpleGraph V} (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))

/-- Deck translations on the literal positive-cube realization. -/
instance pointMulAction : MulAction G (Point (G := G) L f comm) where
  smul g p := {p with base := g * p.base}
  one_smul p := by apply Point.ext (one_mul p.base); rfl
  mul_smul g h p := by apply Point.ext (mul_assoc g h p.base); rfl

omit [Fintype V] in
@[simp] theorem smul_base (g : G) (p : Point (G := G) L f comm) :
    (g • p).base = g * p.base := rfl

omit [Fintype V] in
@[simp] theorem smul_coord (g : G) (p : Point (G := G) L f comm) :
    (g • p).coord = p.coord := rfl

def translateCell (g : G) (c : Cell (G := G) L) : Cell (G := G) L :=
  {c with base := g * c.base}

omit [Fintype V] in
@[simp] theorem smul_characteristic (g : G) (c : Cell (G := G) L) (x : Coordinates c) :
    g • characteristic f comm c x = characteristic f comm (translateCell g c) x := by
  apply Point.ext (mul_assoc _ _ _).symm
  rfl

instance pointContinuousConstSMul : ContinuousConstSMul G (Point (G := G) L f comm) where
  continuous_const_smul g := by
    apply (evaluation_quotient f comm).continuous_iff.mpr
    apply continuous_sigma
    intro c
    change Continuous (fun x : Coordinates c => g • characteristic f comm c x)
    simp only [smul_characteristic]
    change Continuous (characteristic f comm (translateCell g c))
    exact characteristic_continuous f comm (translateCell g c)

instance pointIsCancelSMul : IsCancelSMul G (Point (G := G) L f comm) where
  left_cancel' g p q he := by
    apply Point.ext
    · exact mul_left_cancel (congrArg Point.base he)
    · simpa only [smul_coord] using congrArg (fun r : Point (G := G) L f comm => r.coord) he
  right_cancel' g h p he := mul_right_cancel (congrArg Point.base he)

instance pointProperlyDiscontinuousSMul :
    ProperlyDiscontinuousSMul G (Point (G := G) L f comm) where
  finite_disjoint_inter_image := by
    intro K D hK hD
    apply (((compact_finite_bases L f comm hD).prod
      (compact_finite_bases L f comm hK)).image (fun p : G × G => p.1 * p.2⁻¹)).subset
    intro g hg
    obtain ⟨q,⟨p,hp,hpq⟩,hq⟩ := hg
    refine ⟨(q.base,p.base),⟨⟨q,hq,rfl⟩,⟨p,hp,rfl⟩⟩,?_⟩
    have he : g * p.base = q.base := congrArg Point.base hpq
    change q.base * p.base⁻¹ = g
    rw [← he,mul_inv_cancel_right]

variable (h : G →* Multiplicative ℤ) (hf : ∀ v, (h (f v)).toAdd = 1)
variable (exponent : V → G →* Multiplicative ℝ)
variable (hexponent : ∀ v w, (exponent v (f w)).toAdd = if v = w then 1 else 0)

instance subgroupContinuousConstSMul (H : Subgroup G) :
    ContinuousConstSMul H (Point (G := G) L f comm) where
  continuous_const_smul g := show Continuous (fun p : Point (G := G) L f comm => (g : G) • p) from
    continuous_const_smul (g : G)

instance subgroupProperlyDiscontinuousSMul (H : Subgroup G) :
    ProperlyDiscontinuousSMul H (Point (G := G) L f comm) where
  finite_disjoint_inter_image := by
    intro K D hK hD
    exact Set.Finite.preimage (f := fun g : H => (g : G)) Subtype.val_injective.injOn
      (finite_disjoint_inter_image (Γ := G) hK hD)

include h hf exponent hexponent in
/-- The actual quotient by any subgroup is a covering map. No contractibility
or classifying-space identification is assumed in this theorem. -/
theorem subgroup_quotient_covering (H : Subgroup G) :
    IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel H (Point (G := G) L f comm))) H := by
  let := point_t2 L f comm h hf exponent hexponent
  let := point_weaklyLocallyCompact L f comm
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

end EilenbergGanea.CubeRealization

end

end OAI
