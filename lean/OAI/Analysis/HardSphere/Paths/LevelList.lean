import Mathlib
import OAI.Analysis.HardSphere.Paths.NearPotential

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.DyadicSkeleton

lemma refineStep_mem (a b x : Vertex) (hx : x ∈ refineStep a b) :
    x 0 = b 0 ∧ ∀j, |x j-b j| ≤ |a j-b j| := by
  simp only [refineStep,List.mem_append,List.mem_singleton,List.mem_map] at hx
  rcases hx with (rfl|⟨c,hc,rfl⟩)|⟨c,hc,rfl⟩
  · refine ⟨rfl,?_⟩
    intro j
    fin_cases j <;> simp
  · refine ⟨rfl,?_⟩
    intro j
    fin_cases j
    · simp
    · exact axisSteps_near_final _ _ _ hc
    · simp
  · refine ⟨rfl,?_⟩
    intro j
    fin_cases j
    · simp
    · simp
    · exact axisSteps_near_final _ _ _ hc

def levelList (n : ℕ) (d : Fin 2 → ℤ) (ω : Noise) : ℕ → List Vertex
  | 0 => [baseVertex n d ω 0]
  | t+1 => refineStep (baseVertex n d ω t) (baseVertex n d ω (t+1))

def occurrenceList (n : ℕ) (d : Fin 2 → ℤ) (ω : Noise) : List Vertex :=
  (List.range (n+1)).flatMap (levelList n d ω)

lemma levelList_length (n : ℕ) (hn : 0 < n) (d : Fin 2 → ℤ)
    (hd : ∀j, |d j| ≤ n) (ω : Noise) (t : ℕ) (ht : t ≤ n) :
    (levelList n d ω t).length ≤ 5 := by
  cases t with
  | zero => simp [levelList]
  | succ t => exact refineStep_length _ _ (baseVertex_step n hn d hd ω t (by omega))

lemma levelList_mem (n : ℕ) (hn : 0 < n) (d : Fin 2 → ℤ)
    (hd : ∀j, |d j| ≤ n) (ω : Noise) (t : ℕ) (ht : t ≤ n)
    (x : Vertex) (hx : x ∈ levelList n d ω t) :
    x 0 = (t:ℤ) ∧ ∀j, |x j-baseVertex n d ω t j| ≤ 2 := by
  cases t with
  | zero =>
    have he : x = baseVertex n d ω 0 := by simpa only [levelList,List.mem_singleton] using hx
    subst x
    simp [baseVertex]
  | succ t =>
    obtain ⟨h0,hb⟩ := refineStep_mem _ _ x hx
    refine ⟨h0,fun j ↦ (hb j).trans ?_⟩
    rw [abs_sub_comm]
    exact baseVertex_step n hn d hd ω t (by omega) j

lemma occurrenceList_initial (n : ℕ) (d : Fin 2 → ℤ) (ω : Noise) :
    (0:Vertex) ∈ occurrenceList n d ω := by
  apply List.mem_flatMap.mpr
  refine ⟨0,by simp,?_⟩
  simp [levelList,baseVertex_initial]

lemma integer_step_lipschitz (f : ℕ → ℤ) (H : ℕ) (L : ℤ)
    (hstep : ∀ i<H, |f (i+1)-f i|≤L) {i j : ℕ} (hi : i≤H) (hj : j≤H) :
    |f i-f j|≤L*|(i:ℤ)-j| := by
  have hforward : ∀ a b, a≤b → b≤H → |f b-f a|≤L*((b:ℤ)-a) := by
    intro a b hab hb
    induction b,hab using Nat.le_induction with
    | base => simp
    | @succ b hab ih =>
      have h := hstep b (by omega)
      have hh := ih (by omega)
      calc
        |f (b+1)-f a| ≤ |f (b+1)-f b|+|f b-f a| := abs_sub_le _ _ _
        _ ≤ L+L*((b:ℤ)-a) := add_le_add h hh
        _ = _ := by push_cast; ring
  rcases le_total i j with h|h
  · rw [abs_sub_comm (f i),abs_sub_comm (i:ℤ),abs_of_nonneg (by omega : 0≤(j:ℤ)-i)]
    exact hforward i j h hj
  · rw [abs_of_nonneg (by omega : 0≤(i:ℤ)-j)]
    exact hforward j i h hi

lemma baseVertex_lipschitz (n : ℕ) (hn : 0 < n) (d : Fin 2 → ℤ)
    (hd : ∀j, |d j| ≤ n) (ω : Noise) (s t : ℕ) (hs : s ≤ n) (ht : t ≤ n) (j : Fin 3) :
    |baseVertex n d ω s j-baseVertex n d ω t j| ≤ 2*|(s:ℤ)-t| :=
  integer_step_lipschitz (fun u ↦ baseVertex n d ω u j) n 2
    (fun k hk ↦ baseVertex_step n hn d hd ω k hk j) hs ht

lemma real_sub_floor_le (x y : ℝ) : |x-y| ≤ |(⌊x⌋:ℝ)-(⌊y⌋:ℝ)|+1 := by
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have h3 := Int.floor_le y
  have h4 := Int.lt_floor_add_one y
  have hl := neg_abs_le ((⌊x⌋:ℝ)-(⌊y⌋:ℝ))
  have hu := le_abs_self ((⌊x⌋:ℝ)-(⌊y⌋:ℝ))
  apply abs_le.mpr
  constructor <;> linarith

lemma floor_sub_real_le (x y : ℝ) : |(⌊x⌋:ℝ)-(⌊y⌋:ℝ)| ≤ |x-y|+1 := by
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have h3 := Int.floor_le y
  have h4 := Int.lt_floor_add_one y
  have hl := neg_abs_le (x-y)
  have hu := le_abs_self (x-y)
  apply abs_le.mpr
  constructor <;> linarith

lemma same_time_position_bound (n t : ℕ) (ht : t ≤ n) (ω ω' : Noise) (j : Fin 2) :
    |position ω j (min t (n-t))-position ω' j (min t (n-t))| ≤ (n:ℝ)/2 := by
  have hu : 2*(min t (n-t)) ≤ n := by omega
  have hu' : 2*((min t (n-t):ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast hu
  calc
    _ ≤ |position ω j (min t (n-t))|+|position ω' j (min t (n-t))| := abs_sub _ _
    _ ≤ ((min t (n-t):ℕ):ℝ)/2+((min t (n-t):ℕ):ℝ)/2 :=
      add_le_add (position_abs_le ω j _) (position_abs_le ω' j _)
    _ ≤ _ := by linarith

lemma same_time_floor_bound (n t : ℕ) (ht : t ≤ n) (d : Fin 2 → ℤ)
    (ω ω' : Noise) (j : Fin 3) :
    |(baseVertex n d ω t j:ℝ)-(baseVertex n d ω' t j:ℝ)| ≤ (n:ℝ)/2+1 := by
  have hh (i : Fin 2) : |(⌊baseTrans n d ω t i⌋:ℝ)-(⌊baseTrans n d ω' t i⌋:ℝ)| ≤
      (n:ℝ)/2+1 := by
    have h := floor_sub_real_le (baseTrans n d ω t i) (baseTrans n d ω' t i)
    have he : baseTrans n d ω t i-baseTrans n d ω' t i =
        position ω i (min t (n-t))-position ω' i (min t (n-t)) := by unfold baseTrans; ring
    rw [he] at h
    exact h.trans (add_le_add (same_time_position_bound n t ht ω ω' i) le_rfl)
  fin_cases j
  · change |(t:ℝ)-(t:ℝ)| ≤ _
    rw [sub_self,abs_zero]
    positivity
  · exact hh 0
  · exact hh 1

def periodicProjection (K : ℕ) (x : Vertex) : Fin 3 → AddCircle (K:ℝ) :=
  fun j ↦ ((x j:ℝ) : AddCircle (K:ℝ))

def periodicDistance (K : ℕ) (x y : Vertex) : ℝ :=
  dist (periodicProjection K x) (periodicProjection K y)

lemma periodicDistance_nonneg (K : ℕ) (x y : Vertex) : 0 ≤ periodicDistance K x y := dist_nonneg
lemma periodicDistance_symm (K : ℕ) (x y : Vertex) :
    periodicDistance K x y = periodicDistance K y x := dist_comm _ _
lemma periodicDistance_triangle (K : ℕ) (x y z : Vertex) :
    periodicDistance K x z ≤ periodicDistance K x y+periodicDistance K y z := dist_triangle _ _ _

lemma periodicDistance_le (K : ℕ) (x y : Vertex) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀j, |(x j:ℝ)-(y j:ℝ)| ≤ r) : periodicDistance K x y ≤ r := by
  apply (dist_pi_le_iff hr).mpr
  intro j
  change dist ((x j:ℝ):AddCircle (K:ℝ)) ((y j:ℝ):AddCircle (K:ℝ)) ≤ r
  rw [dist_eq_norm,← QuotientAddGroup.mk_sub]
  exact QuotientAddGroup.norm_mk_le_norm.trans (by simpa only [Real.norm_eq_abs] using h j)

lemma periodicDistance_coord (K : ℕ) (hK : 0 < K) (x y : Vertex) (j : Fin 3)
    (h : |(x j:ℝ)-(y j:ℝ)| ≤ (K:ℝ)/2) :
    |(x j:ℝ)-(y j:ℝ)| ≤ periodicDistance K x y := by
  have hK' : 0 < (K:ℝ) := by exact_mod_cast hK
  have he : dist ((x j:ℝ):AddCircle (K:ℝ)) ((y j:ℝ):AddCircle (K:ℝ)) =
      |(x j:ℝ)-(y j:ℝ)| := by
    rw [dist_eq_norm,← QuotientAddGroup.mk_sub]
    exact (AddCircle.norm_coe_eq_abs_iff (K:ℝ) (ne_of_gt hK')).mpr
      (by simpa only [abs_of_pos hK'] using h)
  rw [← he]
  exact dist_le_pi_dist (periodicProjection K x) (periodicProjection K y) j

lemma periodicDistance_le_half (K : ℕ) (hK : 0 < K) (x y : Vertex) :
    periodicDistance K x y ≤ (K:ℝ)/2 := by
  have hK' : 0 < (K:ℝ) := by exact_mod_cast hK
  apply (dist_pi_le_iff (by positivity : 0 ≤ (K:ℝ)/2)).mpr
  intro j
  rw [dist_eq_norm]
  simpa only [abs_of_pos hK'] using AddCircle.norm_le_half_period (K:ℝ) (x :=
    periodicProjection K x j-periodicProjection K y j) (ne_of_gt hK')

lemma same_time_deviation_le (K n : ℕ) (hn : 0 < n) (hnK : 8*n ≤ K)
    (d : Fin 2 → ℤ) (ω ω' : Noise) (t : ℕ) (ht : t ≤ n) :
    twoCopyDistance (min t (n-t)) (ω,ω') ≤
      periodicDistance K (baseVertex n d ω t) (baseVertex n d ω' t)+1 := by
  have hK : 0 < K := by omega
  have htrans (i : Fin 2) (j : Fin 3)
      (he : baseVertex n d ω t j = ⌊baseTrans n d ω t i⌋)
      (he' : baseVertex n d ω' t j = ⌊baseTrans n d ω' t i⌋) :
      |position ω i (min t (n-t))-position ω' i (min t (n-t))| ≤
        periodicDistance K (baseVertex n d ω t) (baseVertex n d ω' t)+1 := by
    have hp := periodicDistance_coord K hK (baseVertex n d ω t) (baseVertex n d ω' t) j
      ((same_time_floor_bound n t ht d ω ω' j).trans (by
        have hnr : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
        have hkr : 8*(n:ℝ) ≤ (K:ℝ) := by exact_mod_cast hnK
        linarith))
    rw [he,he'] at hp
    have hh := real_sub_floor_le (baseTrans n d ω t i) (baseTrans n d ω' t i)
    have heq : baseTrans n d ω t i-baseTrans n d ω' t i =
        position ω i (min t (n-t))-position ω' i (min t (n-t)) := by unfold baseTrans; ring
    rw [heq] at hh
    exact hh.trans (add_le_add hp le_rfl)
  exact max_le (htrans 0 1 rfl rfl) (htrans 1 2 rfl rfl)

lemma occurrence_deviation_le (K n : ℕ) (hn : 0 < n) (hnK : 8*n ≤ K)
    (d : Fin 2 → ℤ) (hd : ∀j, |d j| ≤ n) (ω ω' : Noise)
    (s t : ℕ) (hs : s ≤ n) (ht : t ≤ n) (x y : Vertex)
    (hx : x ∈ levelList n d ω s) (hy : y ∈ levelList n d ω' t) :
    twoCopyDistance (min s (n-s)) (ω,ω') ≤ 3*periodicDistance K x y+5 := by
  obtain ⟨hx0,hxb⟩ := levelList_mem n hn d hd ω s hs x hx
  obtain ⟨hy0,hyb⟩ := levelList_mem n hn d hd ω' t ht y hy
  have hK : 0 < K := by omega
  have hst : |(s:ℝ)-(t:ℝ)| ≤ periodicDistance K x y := by
    have h := periodicDistance_coord K hK x y 0 (by
      rw [hx0,hy0]; push_cast
      apply (abs_le.mpr ⟨by
        have hn' : 8*(n:ℝ) ≤ (K:ℝ) := by exact_mod_cast hnK
        have hs' : (s:ℝ) ≤ n := by exact_mod_cast hs
        have ht' : (t:ℝ) ≤ n := by exact_mod_cast ht
        have hsz : (0:ℝ) ≤ s := by positivity
        linarith,by
        have hn' : 8*(n:ℝ) ≤ (K:ℝ) := by exact_mod_cast hnK
        have hs' : (s:ℝ) ≤ n := by exact_mod_cast hs
        have ht' : (t:ℝ) ≤ n := by exact_mod_cast ht
        have htz : (0:ℝ) ≤ t := by positivity
        linarith⟩))
    simpa only [hx0,hy0,Int.cast_natCast] using h
  have hxb' : periodicDistance K (baseVertex n d ω s) x ≤ 2 := by
    apply periodicDistance_le _ _ _ 2 (by norm_num)
    intro j
    rw [abs_sub_comm]
    exact_mod_cast hxb j
  have hyb' : periodicDistance K y (baseVertex n d ω' t) ≤ 2 := by
    apply periodicDistance_le _ _ _ 2 (by norm_num)
    intro j
    exact_mod_cast hyb j
  have hbb : periodicDistance K (baseVertex n d ω' t) (baseVertex n d ω' s) ≤
      2*periodicDistance K x y := by
    apply periodicDistance_le _ _ _ _ (mul_nonneg (by norm_num) (periodicDistance_nonneg _ _ _))
    intro j
    have h : |(baseVertex n d ω' t j:ℝ)-(baseVertex n d ω' s j:ℝ)| ≤
        2*|(t:ℝ)-(s:ℝ)| := by
      exact_mod_cast baseVertex_lipschitz n hn d hd ω' t s ht hs j
    rw [abs_sub_comm (t:ℝ)] at h
    linarith
  have htri1 := periodicDistance_triangle K (baseVertex n d ω s) x y
  have htri2 := periodicDistance_triangle K (baseVertex n d ω s) y (baseVertex n d ω' t)
  have htri3 := periodicDistance_triangle K (baseVertex n d ω s)
    (baseVertex n d ω' t) (baseVertex n d ω' s)
  have hdev := same_time_deviation_le K n hn hnK d ω ω' s hs
  linarith

def distanceToList (K : ℕ) (x : Vertex) (l : List Vertex) : ℝ :=
  l.foldr (fun y r ↦ min (periodicDistance K x y) r) ((K:ℝ)/2)

lemma distanceToList_nonneg (K : ℕ) (x : Vertex) (l : List Vertex) :
    0 ≤ distanceToList K x l := by
  induction l with
  | nil => simp only [distanceToList,List.foldr_nil]; positivity
  | cons y l ih => exact le_min (periodicDistance_nonneg _ _ _) ih

lemma distanceToList_le (K : ℕ) (x y : Vertex) (l : List Vertex) (hy : y ∈ l) :
    distanceToList K x l ≤ periodicDistance K x y := by
  induction l with
  | nil => simp at hy
  | cons z l ih =>
    rcases List.mem_cons.mp hy with rfl|hy
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hy)

lemma distanceToList_attained (K : ℕ) (hK : 0 < K) (x : Vertex) (l : List Vertex)
    (hne : l ≠ []) : ∃ y ∈ l, distanceToList K x l = periodicDistance K x y := by
  induction l with
  | nil => exact False.elim (hne rfl)
  | cons z l ih =>
    by_cases hl : l = []
    · subst l
      refine ⟨z,by simp,?_⟩
      exact min_eq_left (periodicDistance_le_half K hK x z)
    · obtain ⟨y,hy,he⟩ := ih hl
      change ∃ y ∈ z::l, min (periodicDistance K x z) (distanceToList K x l) = _
      rcases le_total (periodicDistance K x z) (distanceToList K x l) with h|h
      · exact ⟨z,by simp,min_eq_left h⟩
      · exact ⟨y,by simp [hy],(min_eq_right h).trans he⟩

lemma occurrenceList_ne_nil (n : ℕ) (d : Fin 2 → ℤ) (ω : Noise) :
    occurrenceList n d ω ≠ [] := List.ne_nil_of_mem (occurrenceList_initial n d ω)

lemma distanceToList_deviation_le (K n : ℕ) (hn : 0 < n) (hnK : 8*n ≤ K)
    (d : Fin 2 → ℤ) (hd : ∀j, |d j| ≤ n) (ω ω' : Noise)
    (s : ℕ) (hs : s ≤ n) (x : Vertex) (hx : x ∈ levelList n d ω s) :
    twoCopyDistance (min s (n-s)) (ω,ω') ≤
      3*distanceToList K x (occurrenceList n d ω')+5 := by
  obtain ⟨y,hy,he⟩ := distanceToList_attained K (by omega) x _ (occurrenceList_ne_nil n d ω')
  obtain ⟨t,ht,hy⟩ := List.mem_flatMap.mp hy
  rw [List.mem_range] at ht
  rw [he]
  exact occurrence_deviation_le K n hn hnK d hd ω ω' s t hs (by omega) x y hx hy

def foldIndex (n : ℕ) (j : Fin (n+1)) : Fin (n/2+1) × Bool :=
  if hj : j.val ≤ n/2 then (⟨j.val, by omega⟩, false)
  else (⟨n-j.val, by omega⟩, true)

lemma foldIndex_value (n : ℕ) (j : Fin (n+1)) :
    (foldIndex n j).1.val = min j.val (n-j.val) := by
  unfold foldIndex
  split_ifs with h <;> simp only
  · omega
  · omega

lemma foldIndex_injective (n : ℕ) : Function.Injective (foldIndex n) := by
  intro i j h
  have h₁ := congrArg (fun x : Fin (n/2+1) × Bool ↦ x.1.val) h
  have h₂ := congrArg Prod.snd h
  unfold foldIndex at h₁ h₂
  split_ifs at h₁ h₂ <;> simp_all only
  all_goals apply Fin.ext; omega

lemma folded_sum_le (n : ℕ) (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) :
    (∑ j ∈ Finset.range (n+1), f (min j (n-j))) ≤
      2 * ∑ j ∈ Finset.range (n/2+1), f j := by
  let g : Fin (n/2+1) × Bool → ℝ := fun x ↦ f x.1.val
  have hs : (∑ x ∈ Finset.univ.image (foldIndex n), g x) ≤ ∑ x, g x := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ ↦ hf _)
  rw [Finset.sum_image (fun i _ j _ hij ↦ foldIndex_injective n hij)] at hs
  have hleft : (∑ i : Fin (n+1), g (foldIndex n i)) =
      ∑ j ∈ Finset.range (n+1), f (min j (n-j)) := by
    simp only [g, foldIndex_value]
    exact Fin.sum_univ_eq_sum_range (fun j ↦ f (min j (n-j))) (n+1)
  have hright : (∑ x : Fin (n/2+1) × Bool, g x) =
      2 * ∑ j ∈ Finset.range (n/2+1), f j := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, g, ← two_mul, ← Finset.mul_sum,
      Fin.sum_univ_eq_sum_range]
  simpa only [hleft, hright] using hs

lemma nearPotential_eq_if (u : ℕ) (R : ℝ) (z : Noise × Noise) :
    nearPotential u (fun j ↦ position z.2 j u) R z.1 =
      if twoCopyDistance u z ≤ R then 1 else 0 := by
  unfold nearPotential nearTest coordinateTest twoCopyDistance transverseDistance
  by_cases h0 : |position z.1 0 u-position z.2 0 u| ≤ R <;>
    by_cases h1 : |position z.1 1 u-position z.2 1 u| ≤ R <;>
    simp [h0,h1]

lemma twoCopyDistance_swap (u : ℕ) (z : Noise × Noise) :
    twoCopyDistance u z.swap = twoCopyDistance u z := by
  simp only [twoCopyDistance,transverseDistance,Prod.swap]
  rw [abs_sub_comm (position z.2 0 u),abs_sub_comm (position z.2 1 u)]

lemma nearPotential_swap (u : ℕ) (R : ℝ) (ω ω' : Noise) :
    nearPotential u (fun j ↦ position ω j u) R ω' =
      nearPotential u (fun j ↦ position ω' j u) R ω := by
  rw [nearPotential_eq_if (z := (ω',ω)),nearPotential_eq_if (z := (ω,ω'))]
  rw [show twoCopyDistance u (ω',ω) = twoCopyDistance u (ω,ω') from
    twoCopyDistance_swap u (ω,ω')]

def oneSideHit (K : ℕ) (R : ℝ) (l l' : List Vertex) : ℝ :=
  (l.map (fun x ↦ if distanceToList K x l' ≤ R then 1 else 0)).sum

def occurrenceHit (K : ℕ) (R : ℝ) (l l' : List Vertex) : ℝ :=
  oneSideHit K R l l'+oneSideHit K R l' l

def occurrenceSoft (K : ℕ) (B : ℝ) (l l' : List Vertex) : ℝ :=
  (l.map (fun x ↦ Real.exp (-distanceToList K x l'/B))).sum

lemma oneSideHit_nonneg (K : ℕ) (R : ℝ) (l l' : List Vertex) :
    0 ≤ oneSideHit K R l l' := by
  apply List.sum_nonneg
  intro a ha
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
  split_ifs <;> norm_num

lemma occurrenceHit_nonneg (K : ℕ) (R : ℝ) (l l' : List Vertex) :
    0 ≤ occurrenceHit K R l l' := add_nonneg
      (oneSideHit_nonneg _ _ _ _) (oneSideHit_nonneg _ _ _ _)

lemma level_sum_le (n : ℕ) (hn : 0 < n) (d : Fin 2 → ℤ)
    (hd : ∀j, |d j| ≤ n) (ω : Noise) (f : Vertex → ℝ) (g : ℕ → ℝ)
    (hg : ∀t, 0 ≤ g t)
    (hfg : ∀t ≤ n, ∀x ∈ levelList n d ω t, f x ≤ g t) :
    ((occurrenceList n d ω).map f).sum ≤
      5*∑ t ∈ Finset.range (n+1), g t := by
  have hlevel (t : ℕ) (ht : t ≤ n) :
      ((levelList n d ω t).map f).sum ≤ 5*g t := by
    calc
      _ ≤ ((levelList n d ω t).map (fun _ ↦ g t)).sum := by
        apply List.sum_le_sum
        intro x hx
        exact hfg t ht x hx
      _ = ((levelList n d ω t).length:ℝ)*g t := by simp [nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        exact_mod_cast levelList_length n hn d hd ω t ht) (hg t)
  unfold occurrenceList
  rw [List.flatMap_def,List.map_flatten,List.sum_flatten]
  simp only [List.map_map]
  calc
    _ ≤ ((List.range (n+1)).map (fun t ↦ 5*g t)).sum := by
      apply List.sum_le_sum
      intro t ht
      exact hlevel t (Nat.le_of_lt_succ (List.mem_range.mp ht))
    _ = _ := by
      rw [List.sum_map_mul_left,← List.sum_toFinset g List.nodup_range,List.toFinset_range]

lemma oneSideHit_le (K n : ℕ) (hn : 0 < n) (hnK : 8*n ≤ K)
    (d : Fin 2 → ℤ) (hd : ∀j, |d j| ≤ n) (ω ω' : Noise) (R : ℝ) :
    oneSideHit K R (occurrenceList n d ω) (occurrenceList n d ω') ≤
      10*∑ u ∈ Finset.range (n/2+1),
        nearPotential u (fun j ↦ position ω' j u) (3*R+5) ω := by
  have h := level_sum_le n hn d hd ω
    (fun x ↦ if distanceToList K x (occurrenceList n d ω') ≤ R then 1 else 0)
    (fun t ↦ nearPotential (min t (n-t))
      (fun j ↦ position ω' j (min t (n-t))) (3*R+5) ω)
    (fun _ ↦ nearPotential_nonneg _ _ _ _) (by
      intro t ht x hx
      split_ifs with h
      · rw [nearPotential_eq_if (z := (ω,ω'))]
        rw [ite_eq_left (by linarith [distanceToList_deviation_le K n hn hnK d hd ω ω' t ht x hx])]
      · exact nearPotential_nonneg _ _ _ _)
  have hf := folded_sum_le n
    (fun u ↦ nearPotential u (fun j ↦ position ω' j u) (3*R+5) ω)
    (fun _ ↦ nearPotential_nonneg _ _ _ _)
  change oneSideHit K R _ _ ≤ _ at h
  linarith

end HardSphere.DyadicSkeleton
end
end

end OAI
