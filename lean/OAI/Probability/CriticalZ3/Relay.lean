import OAI.Probability.CriticalZ3.Scales

namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology

open scoped ENNReal BigOperators Matrix

namespace LatticeRelay
open Set
abbrev Vertex := Fin 3 → ℤ

def Rect (c w : Vertex) : Set Vertex := {x | ∀ i, |x i - c i| ≤ w i}
def Cube (c : Vertex) (s : ℤ) : Set Vertex := Rect c (fun _ => s)
def Expand (c w : Vertex) (R : ℤ) : Set Vertex := Rect c (fun i => w i + R)
def DirectedInterval (a s : ℤ) (positive : Bool) (b : ℤ) : Prop :=
  if positive then a ≤ b ∧ b ≤ a+s else a-s ≤ b ∧ b ≤ a

def QuarterFace (u : Vertex) (s : ℤ) (normal : Fin 3) (signs : Fin 3 → Bool) : Set Vertex :=
  {x | x normal = u normal + (if signs normal then s else -s) ∧
    ∀ i, i ≠ normal → DirectedInterval (u i) s (signs i) (x i)}

def inward (u : Vertex) : Fin 3 → Bool := fun i => decide (u i < 0)

def Prism (r : ℤ) : Set Vertex :=
  {x | -10*r ≤ x 0 ∧ x 0 ≤ 30*r+1 ∧
    ∀ i : Fin 3, i ≠ 0 → |x i| ≤ 10*r}

theorem inward_endpoint_bound {a s W : ℤ} (_hs : 0 ≤ s) (hW : s ≤ W)
    (ha : |a| ≤ W+s) : |a + (if decide (a < 0) then s else -s)| ≤ W := by
  rw [abs_le] at ha ⊢
  by_cases h : a < 0 <;> simp [h] <;> omega

theorem inward_interval_bound {a b s W : ℤ} (hW : s ≤ W) (ha : |a| ≤ W)
    (hb : DirectedInterval a s (decide (a < 0)) b) : |b| ≤ W := by
  rw [abs_le] at ha ⊢
  by_cases h : a < 0 <;> simp [DirectedInterval,h] at hb <;> omega

theorem quarterFace_subset_cube {u : Vertex} {s : ℤ} (hs : 0 ≤ s)
    (h : Fin 3) (signs : Fin 3 → Bool) : QuarterFace u s h signs ⊆ Cube u s := by
  intro x hx i
  by_cases hi : i = h
  · subst i
    rw [hx.1]
    dsimp
    cases signs h <;> simp [abs_of_nonneg hs]
  · have hh := hx.2 i hi
    change |x i - u i| ≤ s
    rw [abs_le]
    unfold DirectedInterval at hh
    cases hsi : signs i <;> simp [hsi] at hh <;> omega

theorem quarterFace_nonempty {u : Vertex} {s : ℤ} (hs : 0 ≤ s)
    (h : Fin 3) (signs : Fin 3 → Bool) : (QuarterFace u s h signs).Nonempty := by
  let x : Vertex := fun i => if i = h then u i + (if signs h then s else -s) else u i
  refine ⟨x,by simp [x],?_⟩
  intro i hi
  dsimp [x]
  rw [ite_eq_right hi]
  cases signs i <;> simp [DirectedInterval] <;> omega

/-- Generic form of one of the three contraction steps. -/
theorem contraction_face {r a : ℤ} (hr : 0 ≤ r) (ha : 0 ≤ a) (h : Fin 3)
    {u : Vertex}
    (hu : ∀ i, |u i| ≤ if i < h then 2*r+a else 4*r+a) :
    QuarterFace u (2*r) h (inward u) ⊆
      Rect 0 (fun i => if i ≤ h then 2*r+a else 4*r+a) := by
  intro x hx i
  change |x i - 0| ≤ _
  rw [sub_zero]
  by_cases hi : i = h
  · subst i
    rw [hx.1]
    simp only [le_refl,ite_true,inward]
    apply inward_endpoint_bound (by omega) (by omega)
    have huu := hu h
    simp only [lt_self_iff_false,ite_false] at huu
    omega
  · have hh := hx.2 i hi
    dsimp [inward] at hh
    apply inward_interval_bound (by dsimp; split_ifs <;> omega) _ hh
    have hhi : (i < h) ↔ (i ≤ h) := by omega
    simpa only [hhi] using hu i

theorem contraction_cube {r a : ℤ} (_hr : 0 ≤ r) (ha : 0 ≤ a)
    (ha' : 6*r+a < 10*r) (h : Fin 3) {u : Vertex}
    (hu : ∀ i, |u i| ≤ if i < h then 2*r+a else 4*r+a) :
    Cube u (2*r) ⊆ Prism r := by
  intro x hx
  have hu' (i : Fin 3) : |u i| ≤ 4*r+a := by
    have hu' := hu i
    split_ifs at hu' <;> omega
  have hxi (i : Fin 3) : |x i| < 10*r := by
    have hxu := hx i
    change |x i-u i| ≤ 2*r at hxu
    have huu := hu' i
    rw [abs_le] at hxu huu
    rw [abs_lt]
    omega
  have h0 := (abs_lt.mp (hxi 0))
  refine ⟨by omega,by omega,?_⟩
  intro i _
  exact (hxi i).le

def axisCenter (a : ℤ) : Vertex := fun i => if i = 0 then a else 0

def forwardInward (u : Vertex) : Fin 3 → Bool :=
  fun i => if i = 0 then true else decide (u i < 0)

/-- Generic form of each of the ten translation steps, including the final
length 2r+1 step. -/
theorem translation_face {a s w : ℤ} (hs : s ≤ w) {u : Vertex}
    (hu : u ∈ Cube (axisCenter a) w) :
    QuarterFace u s 0 (forwardInward u) ⊆ Cube (axisCenter (a+s)) w := by
  intro x hx i
  by_cases hi : i = 0
  · subst i
    have huu := hu 0
    rw [hx.1]
    simpa [forwardInward,axisCenter] using huu
  · have huu := hu i
    have hxx := hx.2 i hi
    simp only [forwardInward,hi,ite_false] at hxx
    simp only [axisCenter,hi,ite_false,sub_zero] at huu ⊢
    exact inward_interval_bound hs huu hxx

theorem translation_cube {r R a s w : ℤ}
    (_hR : 0 < R) (hr : 100*(R+1) < r)
    (ha0 : 0 ≤ a) (ha : a ≤ 18*r) (hw : w ≤ 2*r+13*R) (hs : s ≤ 2*r+1)
    {u : Vertex} (hu : u ∈ Cube (axisCenter a) w) :
    Cube u s ⊆ Prism r := by
  intro x hx
  have bounds (i : Fin 3) : -(w+s) ≤ x i-axisCenter a i ∧
      x i-axisCenter a i ≤ w+s := by
    have hu' := (abs_le.mp (hu i))
    have hx' := (abs_le.mp (hx i))
    dsimp at hu' hx'
    omega
  have h0 := bounds 0
  simp only [axisCenter,ite_true] at h0
  refine ⟨by omega,by omega,?_⟩
  intro i hi
  have h := bounds i
  simp only [axisCenter,hi,ite_false,sub_zero] at h
  rw [abs_le]
  constructor <;> omega

def contractionWidths (r R : ℤ) (t : ℕ) : Vertex :=
  fun h => if h.val < t then 2*r+(t : ℤ)*R else 4*r+(t : ℤ)*R

def HasInterface (r R : ℤ) (c w : Vertex) (T : Set Vertex) : Prop :=
  ∀ u ∈ Expand c w R, ∃ s : ℤ, s ∈ ({2*r,2*r+1,10*r} : Set ℤ) ∧
    Cube u s ⊆ Prism r ∧ ∃ h signs, QuarterFace u s h signs ⊆ T

theorem contraction_interface {r R : ℤ} (hR : 0 < R) (hr : 100*(R+1) < r)
    {t : ℕ} (ht : t < 3) :
    HasInterface r R 0 (contractionWidths r R t)
      (Rect 0 (contractionWidths r R (t+1))) := by
  intro u hu
  let h : Fin 3 := ⟨t,ht⟩
  let a : ℤ := (t+1)*R
  have ht' : (t : ℤ) < 3 := by exact_mod_cast ht
  have ht0 : (0 : ℤ) ≤ t := by positivity
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha3 : a ≤ 3*R := by dsimp [a]; nlinarith
  have huu : ∀ i, |u i| ≤ if i < h then 2*r+a else 4*r+a := by
    intro i
    have hh := hu i
    change |u i-0| ≤ (if i.val < t then 2*r+(t : ℤ)*R else 4*r+(t : ℤ)*R)+R at hh
    change |u i| ≤ if i.val < t then 2*r+a else 4*r+a
    dsimp [a]
    rw [add_mul]
    by_cases hi : i.val < t <;> simp only [hi,ite_true,ite_false,sub_zero,one_mul] at * <;> omega
  refine ⟨2*r,by simp,contraction_cube (by omega) ha0 (by omega) h huu,h,inward u,?_⟩
  intro x hx i
  have hb := contraction_face (by omega) ha0 h huu hx i
  change |x i-0| ≤ if i.val < t+1 then 2*r+(↑(t+1) : ℤ)*R else 4*r+(↑(t+1) : ℤ)*R
  have hi : (i ≤ h) ↔ i.val < t+1 := by change (i.val ≤ t) ↔ _; omega
  simpa only [hi,a,Nat.cast_add,Nat.cast_one,Pi.zero_apply] using hb

theorem translation_interface {r R a s w : ℤ}
    (hR : 0 < R) (hr : 100*(R+1) < r)
    (ha0 : 0 ≤ a) (ha : a ≤ 18*r) (hw : w ≤ 2*r+13*R)
    (hs : s = 2*r ∨ s = 2*r+1) (hsw : s ≤ w) :
    HasInterface r R (axisCenter a) (fun _ => w-R) (Cube (axisCenter (a+s)) w) := by
  intro u hu
  have huu : u ∈ Cube (axisCenter a) w := by
    intro i
    simpa only [Expand,Rect,sub_add_cancel] using hu i
  refine ⟨s,?_,translation_cube hR hr ha0 ha hw (by rcases hs with rfl|rfl <;> omega) huu,
    0,forwardInward u,translation_face hsw huu⟩
  rcases hs with rfl|rfl <;> simp

def routeCenter (r : ℤ) (i : ℕ) : Vertex :=
  if i ≤ 3 then 0 else axisCenter (if i ≤ 12 then 2*r*(i-3 : ℕ) else 20*r+1)
def routeWidths (r R : ℤ) (i : ℕ) : Vertex :=
  if i ≤ 3 then contractionWidths r R i else fun _ => 2*r+(i : ℤ)*R

def P (r R : ℤ) (i : ℕ) : Set Vertex := Rect (routeCenter r i) (routeWidths r R i)

@[simp] theorem axisCenter_zero : axisCenter 0 = 0 := by ext i; simp [axisCenter]

theorem routeCenter_translation {r : ℤ} {i : ℕ} (hi : 3 ≤ i) (hi' : i ≤ 12) :
    routeCenter r i = axisCenter (2*r*(i-3 : ℕ)) := by
  by_cases h : i ≤ 3
  · have : i = 3 := by omega
    subst i
    simp [routeCenter]
  · simp [routeCenter,h,hi']

theorem routeWidths_translation {r R : ℤ} {i : ℕ} (hi : 3 ≤ i) :
    routeWidths r R i = fun _ => 2*r+(i : ℤ)*R := by
  by_cases h : i ≤ 3
  · have : i = 3 := by omega
    subst i
    funext j
    simp [routeWidths,contractionWidths,j.isLt]
  · simp [routeWidths,h]

def stepSize (r : ℤ) (i : ℕ) : ℤ := if i < 12 then 2*r else 2*r+1

theorem routeCenter_next {r : ℤ} {i : ℕ} (hi : 3 ≤ i) (hi' : i ≤ 12) :
    routeCenter r (i+1) = axisCenter (2*r*(i-3 : ℕ)+stepSize r i) := by
  by_cases h : i < 12
  · rw [routeCenter_translation (by omega) (by omega)]
    congr 1
    simp only [stepSize,h,ite_true,Nat.cast_sub (by omega : 3 ≤ i),
      Nat.cast_sub (by omega : 3 ≤ i+1),Nat.cast_add,Nat.cast_one]
    ring
  · have : i = 12 := by omega
    subst i
    simp only [routeCenter,show ¬13 ≤ 3 by omega,ite_false,show ¬13 ≤ 12 by omega,
      stepSize,lt_self_iff_false]
    congr 1
    norm_num
    ring

theorem thirteen_interfaces {r R : ℤ} (hR : 0 < R) (hr : 100*(R+1) < r)
    {i : ℕ} (hi : i < 13) :
    HasInterface r R (routeCenter r i) (routeWidths r R i) (P r R (i+1)) := by
  by_cases hi3 : i < 3
  · simpa only [P,routeCenter,routeWidths,show i ≤ 3 by omega,show i+1 ≤ 3 by omega,
      ite_true] using contraction_interface hR hr hi3
  · have hil : 3 ≤ i := by omega
    have hii : i ≤ 12 := by omega
    rw [routeCenter_translation hil hii,routeWidths_translation hil]
    unfold P
    rw [routeCenter_next hil hii,routeWidths_translation (by omega)]
    let a : ℤ := 2*r*(i-3 : ℕ)
    let w : ℤ := 2*r+(↑(i+1) : ℤ)*R
    have hir : (i : ℤ) ≤ 12 := by exact_mod_cast hii
    have hilr : (3 : ℤ) ≤ i := by exact_mod_cast hil
    have hr0 : 0 ≤ r := by omega
    have ha0 : 0 ≤ a := by dsimp [a]; positivity
    have ha : a ≤ 18*r := by
      dsimp [a]
      rw [Nat.cast_sub hil]
      norm_num
      nlinarith
    have hw : w ≤ 2*r+13*R := by dsimp [w]; nlinarith
    have hs : stepSize r i = 2*r ∨ stepSize r i = 2*r+1 := by
      unfold stepSize; split_ifs <;> simp
    have hsw : stepSize r i ≤ w := by
      dsimp [w]
      rcases hs with h|h <;> rw [h] <;> nlinarith
    have he : (fun _ : Fin 3 => 2*r+(i : ℤ)*R) = fun _ => w-R := by
      funext j
      dsimp [w]
      ring
    rw [he]
    exact translation_interface hR hr ha0 ha hw hs hsw

@[simp] theorem P_zero (r R : ℤ) : P r R 0 = Cube 0 (4*r) := by
  simp only [P,routeCenter,routeWidths,Nat.zero_le,show 0 ≤ 3 by omega,ite_true,Cube]
  congr 1
  funext i
  simp [contractionWidths]

theorem P_thirteen_subset {r R : ℤ} (_hR : 0 < R) (hr : 100*(R+1) < r) :
    P r R 13 ⊆ Cube (axisCenter (20*r+1)) (4*r) := by
  intro x hx i
  have h := hx i
  simp only [routeCenter,routeWidths,show ¬13 ≤ 3 by omega,ite_false,
    show ¬13 ≤ 12 by omega] at h
  change |x i-axisCenter (20*r+1) i| ≤ 4*r
  dsimp at h
  omega

theorem expanded_route_subset_prism {r R : ℤ} (hR : 0 < R) (hr : 100*(R+1) < r)
    {i : ℕ} (hi : i < 13) :
    Expand (routeCenter r i) (routeWidths r R i) R ⊆ Prism r := by
  intro u hu
  obtain ⟨s,hs,hsub,_⟩ := thirteen_interfaces hR hr hi u hu
  apply hsub
  intro j
  change |u j-u j| ≤ s
  simp only [sub_self,abs_zero]
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hs
  rcases hs with rfl|rfl|rfl <;> omega

end LatticeRelay

end OAI
