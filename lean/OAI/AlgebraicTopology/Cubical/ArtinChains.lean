import OAI.AlgebraicTopology.Cubical.Chains
import OAI.GroupTheory.RightAngledArtin.CubeDescents

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.TraceWords.CubeDescents
open CubicalChains
variable {V : Type*} (L : SimpleGraph V) [Fintype V] [Nonempty V] [LinearOrder (Letter V)]

def descentFinset (g : ArtinGroup L) : Finset (Letter V) :=
  Finset.univ.filter (fun x => x ∈ rightDescents L g)

omit [Nonempty V] [LinearOrder (Letter V)] in
@[simp] theorem mem_descentFinset (g : ArtinGroup L) (x : Letter V) :
    x ∈ descentFinset L g ↔ x ∈ rightDescents L g := by simp [descentFinset]

def leastDescent (g : ArtinGroup L) : Letter V :=
  if h : (descentFinset L g).Nonempty then (descentFinset L g).min' h
  else Classical.choice (inferInstance : Nonempty (Letter V))

theorem leastDescent_le (g : ArtinGroup L) (x : Letter V) (hx : x ∈ rightDescents L g) :
    leastDescent L g ≤ x := by
  have hm : x ∈ descentFinset L g := (mem_descentFinset L g x).mpr hx
  rw [leastDescent,dite_eq_left ⟨x,hm⟩]
  exact Finset.min'_le _ _ hm

theorem leastDescent_mem (g : ArtinGroup L) (hg : 0 < artinLength L g) :
    leastDescent L g ∈ rightDescents L g := by
  have hne : g ≠ 1 := fun h => by
    have := (artinLength_eq_zero_iff L g).mpr h
    omega
  obtain ⟨x,hx⟩ := rightDescents_nonempty L hne
  have hm : (descentFinset L g).Nonempty := ⟨x,(mem_descentFinset L g x).mpr hx⟩
  rw [leastDescent,dite_eq_left hm]
  exact (mem_descentFinset L _ _).mp (Finset.min'_mem _ _)

/-- The actual RAAG satisfies every hypothesis of the descending-chain
contraction, as a consequence of the independently proved trace normal form. -/
def artinDescentSystem : DescentSystem (fun x => letterValue (artinGenerator L) (invLetter x)) where
  length := artinLength L
  desc := rightDescents L
  step := fun g x hx => (rightDescents_length L g x).mp hx
  preserve := by
    intro g x y hx hy hxy
    have hi := rightDescents_pairwise L g hx hy hxy
    exact (descent_independent_step L g (show Independent L (invLetter x) y from hi)).mpr hy
  commute := by
    intro g x y hx hy hxy
    have hi := rightDescents_pairwise L g hx hy hxy
    exact letterValue_commute (fun _ _ h => adjacent_generators_commute L h)
      (show Independent L (invLetter x) (invLetter y) from hi)
  choose := leastDescent L
  choose_mem := leastDescent_mem L
  choose_le := leastDescent_le L

def descendingChains (k : ℕ) : Submodule ℤ (Chains (ArtinGroup L) (Letter V)) :=
  Finsupp.supported ℤ ℤ {p | (artinDescentSystem L).Valid p.1 p.2 ∧ p.2.length = k}

theorem descending_finite_bound {k : ℕ} {c : Chains (ArtinGroup L) (Letter V)}
    (hc : c ∈ descendingChains L k) :
    ∃ N, c ∈ (artinDescentSystem L).admissible k N := by
  refine ⟨c.support.sup (fun p => artinLength L p.1),?_⟩
  apply (Finsupp.mem_supported ℤ c).mpr
  intro p hp
  have hv := (Finsupp.mem_supported ℤ c).mp hc hp
  refine ⟨hv.1,hv.2,?_⟩
  exact Finset.le_sup (f := fun p => artinLength L p.1) hp

/-- Exactness of the genuine descending cubical chain complex in every
positive degree, with no finite-support bound imposed on the cycle. -/
theorem descending_cycle_bounds {k : ℕ} (hk : 0 < k)
    (c : Chains (ArtinGroup L) (Letter V)) (hc : c ∈ descendingChains L k)
    (hz : boundary (fun x => letterValue (artinGenerator L) (invLetter x)) c = 0) :
    ∃ b ∈ descendingChains L (k+1),
      boundary (fun x => letterValue (artinGenerator L) (invLetter x)) b = c := by
  obtain ⟨N,hN⟩ := descending_finite_bound L hc
  obtain ⟨b,hb,hdb⟩ := (artinDescentSystem L).cycle_bounds hk c hN hz
  refine ⟨b,?_,hdb⟩
  apply Finsupp.supported_mono _ hb
  rintro p ⟨hv,hl,_⟩
  exact ⟨hv,hl⟩

end EilenbergGanea.TraceWords.CubeDescents

namespace CubicalChains
variable {G A : Type*} [Group G]
namespace Reorientation
variable {V : Type*} (f : V → G)

abbrev Signed (V : Type*) := V × Bool

def step (x : Signed V) : G := if x.2 then (f x.1)⁻¹ else f x.1

def origin (g : G) : List (Signed V) → G
  | [] => g
  | x::w => if x.2 then origin (g * (f x.1)⁻¹) w else origin g w

def sign : List (Signed V) → ℤ
  | [] => 1
  | x::w => (if x.2 then -1 else 1) * sign w

@[simp] theorem origin_nil (g : G) : origin f g [] = g := rfl
@[simp] theorem sign_nil : sign ([] : List (Signed V)) = 1 := rfl

@[simp] theorem sign_sq (w : List (Signed V)) : sign w * sign w = 1 := by
  induction w with
  | nil => rfl
  | cons x w ih => cases hx : x.2 <;> simp [sign,hx,ih]

theorem origin_shift (g k : G) (w : List (Signed V))
    (hw : ∀ x ∈ w, Commute k (f x.1)) :
    origin f (g*k) w = origin f g w * k := by
  induction w generalizing g with
  | nil => rfl
  | cons x w ih =>
      have hx := (hw x (by simp)).inv_right
      have hh : ∀ y ∈ w, Commute k (f y.1) := fun y hy => hw y (by simp [hy])
      simp only [origin]
      split
      · rw [mul_assoc,hx.eq,← mul_assoc,ih _ hh]
      · exact ih _ hh

def normalTerm (g : G) (w : List (Signed V)) : Chains G V :=
  sign w • Finsupp.single (origin f g w,w.map Prod.fst) 1

def normalize : Chains G (Signed V) →ₗ[ℤ] Chains G V :=
  Finsupp.linearCombination ℤ (fun p => normalTerm f p.1 p.2)

@[simp] theorem normalize_single (g : G) (w : List (Signed V)) (n : ℤ) :
    normalize f (Finsupp.single (g,w) n) = n • normalTerm f g w := by simp [normalize]

theorem normalize_front (x : Signed V) (c : Chains G (Signed V)) :
    normalize f (front x c) = if x.2 then
      -front x.1 (normalize f (shift (step f) x c)) else front x.1 (normalize f c) := by
  induction c using Finsupp.induction_linear with
  | zero => cases x.2 <;> simp
  | add c d hc hd =>
      simp only [map_add,hc,hd]
      cases x.2
      all_goals simp only [Bool.false_eq_true,↓reduceIte]
      all_goals abel
  | single p n =>
      rcases p with ⟨g,w⟩
      cases hx : x.2 <;> simp only [front_single,normalize_single,shift_single,normalTerm,
        origin,sign,step,hx,Bool.false_eq_true,↓reduceIte,List.map_cons,map_smul,
        neg_mul,smul_neg,neg_smul,one_mul]

/-- Reversing selected coordinates changes the signs and origin but not the
actual integral cubical boundary. No asphericity input is used here. -/
theorem normalize_boundaryTerm (g : G) (w : List (Signed V))
    (hw : w.Pairwise (fun x y => Commute (f x.1) (f y.1))) :
    normalize f (boundaryTerm (step f) g w) = boundary f (normalTerm f g w) := by
  induction w generalizing g with
  | nil => simp [normalTerm]
  | cons x w ih =>
      obtain ⟨hx,hw⟩ := List.pairwise_cons.mp hw
      have hi : ∀ y ∈ w, Commute (step f x) (step f y) := by
        intro y hy
        have hh := hx y hy
        cases hx' : x.2 <;> cases hy' : y.2 <;> simp only [step,hx',hy',Bool.false_eq_true,↓reduceIte]
        · exact hh
        · exact hh.inv_right
        · exact hh.inv_left
        · exact hh.inv_left.inv_right
      cases hxb : x.2
      · simp only [boundaryTerm_cons,map_sub,normalize_single,one_smul,normalize_front,hxb,
          Bool.false_eq_true,↓reduceIte,ih _ hw,normalTerm,sign,one_mul,origin,List.map_cons,
          map_smul,boundary_single,boundaryTerm_cons]
        have ho := origin_shift f g (f x.1) w hx
        simp only [step,hxb,Bool.false_eq_true,↓reduceIte] at ho ⊢
        rw [ho]
        simp only [smul_sub,Finsupp.smul_single,smul_eq_mul,mul_one]
      · simp only [boundaryTerm_cons,map_sub,normalize_single,one_smul,normalize_front,hxb,
          ↓reduceIte]
        rw [← boundaryTerm_shift (step f) x g w hi,ih _ hw]
        simp only [normalTerm,sign,hxb,↓reduceIte,neg_mul,one_mul,origin,List.map_cons,
          map_smul,boundary_single,boundaryTerm_cons,step]
        have ho : origin f (g * (f x.1)⁻¹) w * f x.1 = origin f g w := by
          rw [origin_shift f g (f x.1)⁻¹ w (fun y hy => (hx y hy).inv_left)]
          group
        rw [ho]
        simp only [smul_sub,neg_smul,Finsupp.smul_single,smul_eq_mul,mul_one]
        abel

end Reorientation
end CubicalChains

namespace EilenbergGanea.TraceWords.CubeDescents
open CubicalChains CubicalChains.Reorientation
variable {V : Type*} (L : SimpleGraph V)

theorem reverse_step_descent (g : ArtinGroup L) (x : Letter V) :
    x ∈ rightDescents L (g * letterValue (artinGenerator L) x) ↔
      invLetter x ∉ rightDescents L g := by
  rw [rightDescents_length]
  simp only [letterValue_inverse,mul_inv_cancel_right]
  have hs := artinLength_step L g x
  by_cases h : invLetter x ∈ rightDescents L g
  · simp only [h,↓reduceIte,not_true_eq_false,iff_false] at hs ⊢
    omega
  · simp only [h,↓reduceIte,not_false_eq_true,iff_true] at hs ⊢
    omega

theorem origin_descent_invariant (g : ArtinGroup L) (w : Word V) (y : Letter V)
    (hw : ∀ x ∈ w, Independent L x y) :
    y ∈ rightDescents L (origin (artinGenerator L) g w) ↔ y ∈ rightDescents L g := by
  induction w generalizing g with
  | nil => rfl
  | cons x w ih =>
      have hh : ∀ z ∈ w, Independent L z y := fun z hz => hw z (by simp [hz])
      simp only [origin]
      split
      · rw [ih _ hh]
        exact descent_independent_step L g (x := (x.1,false)) (hw x (by simp))
      · exact ih _ hh

/-- Orient a positive cube toward its unique word-length maximum. -/
def orient (g : ArtinGroup L) : List V → ArtinGroup L × Word V
  | [] => (g,[])
  | q::w => if (q,false) ∈ rightDescents L g then
      let t := orient g w
      (t.1,(q,false)::t.2)
    else
      let t := orient (g * artinGenerator L q) w
      (t.1,(q,true)::t.2)

@[simp] theorem orient_nil (g : ArtinGroup L) : orient L g [] = (g,[]) := rfl

@[simp] theorem orient_map (g : ArtinGroup L) (w : List V) :
    (orient L g w).2.map Prod.fst = w := by
  induction w generalizing g with
  | nil => rfl
  | cons q w ih => simp only [orient]; split <;> simp [ih]

theorem orient_descent_invariant (g : ArtinGroup L) (w : List V) (x : Letter V)
    (hw : ∀ q ∈ w, L.Adj q x.1) :
    x ∈ rightDescents L (orient L g w).1 ↔ x ∈ rightDescents L g := by
  induction w generalizing g with
  | nil => rfl
  | cons q w ih =>
      have hh : ∀ r ∈ w, L.Adj r x.1 := fun r hr => hw r (by simp [hr])
      simp only [orient]
      split
      · exact ih _ hh
      · rw [ih _ hh]
        exact descent_independent_step L g (x := (q,true)) (hw q (by simp))

theorem orient_descents (g : ArtinGroup L) (w : List V) (hw : w.Pairwise L.Adj) :
    ∀ x ∈ (orient L g w).2, x ∈ rightDescents L (orient L g w).1 := by
  induction w generalizing g with
  | nil => simp
  | cons q w ih =>
      obtain ⟨hq,hw⟩ := List.pairwise_cons.mp hw
      simp only [orient]
      split
      · rename_i hd
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact (orient_descent_invariant L g w (q,false)
            (fun r hr => (hq r hr).symm)).mpr hd
        · exact ih g hw x hx
      · rename_i hd
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · apply (orient_descent_invariant L (g * artinGenerator L q) w (q,true)
            (fun r hr => (hq r hr).symm)).mpr
          exact (reverse_step_descent L g (q,true)).mpr hd
        · exact ih _ hw x hx

theorem origin_orient (g : ArtinGroup L) (w : List V) (hw : w.Pairwise L.Adj) :
    origin (artinGenerator L) (orient L g w).1 (orient L g w).2 = g := by
  induction w generalizing g with
  | nil => rfl
  | cons q w ih =>
      obtain ⟨hq,hw⟩ := List.pairwise_cons.mp hw
      simp only [orient]
      split
      · exact ih g hw
      · simp only [origin,↓reduceIte]
        rw [origin_shift]
        · rw [ih _ hw,mul_inv_cancel_right]
        · intro x hx
          apply Commute.inv_left
          apply adjacent_generators_commute
          have hm : x.1 ∈ w := by
            rw [← orient_map L (g * artinGenerator L q) w]
            exact List.mem_map.mpr ⟨x,hx,rfl⟩
          exact hq x.1 hm

/-- Reorientation is invertible on every actual descending cube. -/
theorem orient_origin (g : ArtinGroup L) (w : Word V)
    (hw : w.Pairwise (Independent L)) (hd : ∀ x ∈ w, x ∈ rightDescents L g) :
    orient L (origin (artinGenerator L) g w) (w.map Prod.fst) = (g,w) := by
  induction w generalizing g with
  | nil => rfl
  | cons x w ih =>
      obtain ⟨hx,hwtail⟩ := List.pairwise_cons.mp hw
      have hdw : ∀ y ∈ w, y ∈ rightDescents L g := fun y hy => hd y (by simp [hy])
      have hdx := hd x (by simp)
      rcases x with ⟨q,b⟩
      cases b
      · have hp : (q,false) ∈ rightDescents L (origin (artinGenerator L) g w) :=
          (origin_descent_invariant L g w (q,false) (fun y hy => (hx y hy).symm)).mpr hdx
        simp only [origin,Bool.false_eq_true,↓reduceIte,List.map_cons,orient,ite_eq_left hp]
        rw [ih g hwtail hdw]
      · have hp : (q,false) ∉ rightDescents L (origin (artinGenerator L) (g * (artinGenerator L q)⁻¹) w) := by
          rw [origin_descent_invariant L _ w (q,false) (fun y hy => (hx y hy).symm)]
          have hh := reverse_step_descent L g (q,false)
          simpa only [letterValue,invLetter,Bool.not_false,Bool.false_eq_true,ite_false] using (not_congr hh).mpr (not_not.mpr hdx)
        simp only [origin,↓reduceIte,List.map_cons,orient,ite_eq_right hp]
        have he : origin (artinGenerator L) (g * (artinGenerator L q)⁻¹) w * artinGenerator L q =
            origin (artinGenerator L) g w := by
          rw [origin_shift]
          · group
          · intro y hy
            exact (adjacent_generators_commute L (hx y hy)).inv_left
        rw [he,ih g hwtail hdw]

end EilenbergGanea.TraceWords.CubeDescents

namespace EilenbergGanea.TraceWords.CubeDescents
open CubicalChains CubicalChains.Reorientation
variable {V : Type*} (L : SimpleGraph V) [Fintype V] [Nonempty V] [LinearOrder V]
local instance signedLexOrder : LinearOrder (Letter V) :=
  LinearOrder.lift' (toLex : V × Bool → Lex (V × Bool)) toLex.injective
local instance signedPreorder : Preorder (Letter V) := signedLexOrder.toPartialOrder.toPreorder

def positiveChains (k : ℕ) : Submodule ℤ (Chains (ArtinGroup L) V) :=
  Finsupp.supported ℤ ℤ {p | p.2.Pairwise (· < ·) ∧ p.2.Pairwise L.Adj ∧ p.2.length = k}

theorem descending_independent {g : ArtinGroup L} {w : Word V}
    (hw : (artinDescentSystem L).Valid g w) : w.Pairwise (Independent L) := by
  apply hw.1.imp_of_mem
  intro x y hx hy hlt
  exact rightDescents_pairwise L g (hw.2 x hx) (hw.2 y hy) (ne_of_lt hlt)

omit [Fintype V] [Nonempty V] in
theorem signed_sorted_iff {w : Word V} (hw : w.Pairwise (Independent L)) :
    w.Pairwise (· < ·) ↔ (w.map Prod.fst).Pairwise (· < ·) := by
  rw [List.pairwise_map]
  constructor
  · intro hs
    exact (hs.and hw).imp (fun {x y} h => by
      have hh : toLex x < toLex y := h.1
      rcases Prod.Lex.toLex_lt_toLex.mp hh with hlt | ⟨he,_⟩
      · exact hlt
      · exact False.elim (h.2.ne he))
  · intro hs
    exact hs.imp (fun {_ _} hh => Prod.Lex.toLex_lt_toLex.mpr (Or.inl hh))

theorem normalize_descending {k : ℕ} {c : Chains (ArtinGroup L) (Letter V)}
    (hc : c ∈ descendingChains L k) : normalize (artinGenerator L) c ∈ positiveChains L k := by
  apply supported_map _ _ _ _ hc
  rintro ⟨g,w⟩ ⟨hv,hl⟩
  rw [normalize_single,one_smul,normalTerm]
  apply Submodule.smul_mem
  apply Finsupp.single_mem_supported
  have hi := descending_independent L hv
  exact ⟨(signed_sorted_iff L hi).mp hv.1,by rw [List.pairwise_map]; exact hi,
    by simpa using hl⟩

def denormalTerm (g : ArtinGroup L) (w : List V) : Chains (ArtinGroup L) (Letter V) :=
  sign (orient L g w).2 • Finsupp.single (orient L g w) 1

def denormalize : Chains (ArtinGroup L) V →ₗ[ℤ] Chains (ArtinGroup L) (Letter V) :=
  Finsupp.linearCombination ℤ (fun p => denormalTerm L p.1 p.2)

omit [Fintype V] [Nonempty V] [LinearOrder V] in
@[simp] theorem denormalize_single (g : ArtinGroup L) (w : List V) (n : ℤ) :
    denormalize L (Finsupp.single (g,w) n) = n • denormalTerm L g w := by
  simp [denormalize]

theorem denormalize_positive {k : ℕ} {c : Chains (ArtinGroup L) V}
    (hc : c ∈ positiveChains L k) : denormalize L c ∈ descendingChains L k := by
  apply supported_map _ _ _ _ hc
  rintro ⟨g,w⟩ ⟨hs,ha,hl⟩
  rw [denormalize_single,one_smul,denormalTerm]
  apply Submodule.smul_mem
  apply Finsupp.single_mem_supported
  have hm := orient_map L g w
  have hi : (orient L g w).2.Pairwise (Independent L) := by
    rw [← hm] at ha
    rw [List.pairwise_map] at ha
    exact ha
  refine ⟨⟨(signed_sorted_iff L hi).mpr (by rw [hm]; exact hs),
    orient_descents L g w ha⟩,?_⟩
  rw [← hm,List.length_map] at hl
  exact hl

omit [Fintype V] [Nonempty V] [LinearOrder V] in
theorem normal_denormal_term (g : ArtinGroup L) (w : List V) (hw : w.Pairwise L.Adj) :
    normalize (artinGenerator L) (denormalTerm L g w) = Finsupp.single (g,w) 1 := by
  rw [denormalTerm,map_smul]
  rcases he : orient L g w with ⟨g',u⟩
  simp only [normalize_single,normalTerm,smul_smul,one_mul,sign_sq,one_smul]
  have ho := origin_orient L g w hw
  have hm := orient_map L g w
  simp only [he] at ho hm
  rw [ho,hm]

theorem denormal_normal_term {g : ArtinGroup L} {w : Word V}
    (hw : (artinDescentSystem L).Valid g w) :
    denormalize L (normalTerm (artinGenerator L) g w) = Finsupp.single (g,w) 1 := by
  simp only [normalTerm,map_smul,denormalize_single,one_smul,denormalTerm]
  rw [orient_origin L g w (descending_independent L hw) hw.2]
  simp only [smul_smul,sign_sq,one_smul]

omit [Fintype V] [Nonempty V] in
theorem normal_denormal {k : ℕ} {c : Chains (ArtinGroup L) V}
    (hc : c ∈ positiveChains L k) : normalize (artinGenerator L) (denormalize L c) = c := by
  rw [positiveChains,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ =>
    normalize (artinGenerator L) (denormalize L c) = c) _ _ _ _ hc
  · rintro _ ⟨⟨g,w⟩,⟨_,ha,_⟩,rfl⟩
    simpa only [denormalize_single,one_smul] using normal_denormal_term L g w ha
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd]
  · intro n c _ hc; simp only [map_smul,hc]

theorem denormal_normal {k : ℕ} {c : Chains (ArtinGroup L) (Letter V)}
    (hc : c ∈ descendingChains L k) : denormalize L (normalize (artinGenerator L) c) = c := by
  rw [descendingChains,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ =>
    denormalize L (normalize (artinGenerator L) c) = c) _ _ _ _ hc
  · rintro _ ⟨⟨g,w⟩,⟨hv,_⟩,rfl⟩
    simpa only [normalize_single,one_smul] using denormal_normal_term L hv
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd]
  · intro n c _ hc; simp only [map_smul,hc]

omit [Fintype V] [Nonempty V] [LinearOrder V] in
theorem step_eq_inverse_letter : step (artinGenerator L) =
    fun x => letterValue (artinGenerator L) (invLetter x) := by
  funext x
  cases hx : x.2 <;> simp [step,letterValue,invLetter,hx]

theorem descending_boundary {k : ℕ} {c : Chains (ArtinGroup L) (Letter V)}
    (hc : c ∈ descendingChains L k) :
    boundary (step (artinGenerator L)) c ∈ descendingChains L (k-1) := by
  obtain ⟨N,hN⟩ := descending_finite_bound L hc
  have hb := (artinDescentSystem L).boundary_admissible hN
  rw [step_eq_inverse_letter]
  apply Finsupp.supported_mono _ hb
  rintro p ⟨hv,hl,_⟩
  exact ⟨hv,hl⟩

theorem normalize_boundary {k : ℕ} {c : Chains (ArtinGroup L) (Letter V)}
    (hc : c ∈ descendingChains L k) :
    normalize (artinGenerator L) (boundary (step (artinGenerator L)) c) =
      boundary (artinGenerator L) (normalize (artinGenerator L) c) := by
  rw [descendingChains,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ =>
    normalize (artinGenerator L) (boundary (step (artinGenerator L)) c) =
      boundary (artinGenerator L) (normalize (artinGenerator L) c)) _ _ _ _ hc
  · rintro _ ⟨⟨g,w⟩,⟨hv,_⟩,rfl⟩
    simp only [boundary_single,normalize_single,one_smul]
    exact normalize_boundaryTerm _ g w ((descending_independent L hv).imp
      (fun {_ _} h => adjacent_generators_commute L h))
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd]
  · intro n c _ hc; simp only [map_smul,hc]

/-- Exactness of the standard positively oriented RAAG cube chains. This is
an actual finite integral filling, derived from the descending contraction. -/
theorem positive_cycle_bounds {k : ℕ} (hk : 0 < k)
    (c : Chains (ArtinGroup L) V) (hc : c ∈ positiveChains L k)
    (hz : boundary (artinGenerator L) c = 0) :
    ∃ b ∈ positiveChains L (k+1), boundary (artinGenerator L) b = c := by
  have hd := denormalize_positive L hc
  have hdz : boundary (step (artinGenerator L)) (denormalize L c) = 0 := by
    have hn : normalize (artinGenerator L)
        (boundary (step (artinGenerator L)) (denormalize L c)) = 0 := by
      rw [normalize_boundary L hd,normal_denormal L hc,hz]
    have he := denormal_normal L (descending_boundary L hd)
    rw [hn,map_zero] at he
    exact he.symm
  obtain ⟨b,hb,hdb⟩ := descending_cycle_bounds L hk (denormalize L c) hd (by rwa [← step_eq_inverse_letter])
  refine ⟨normalize (artinGenerator L) b,normalize_descending L hb,?_⟩
  rw [← normalize_boundary L hb,step_eq_inverse_letter,hdb,normal_denormal L hc]

end EilenbergGanea.TraceWords.CubeDescents


end

end OAI
