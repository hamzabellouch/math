import Mathlib
import OAI.Combinatorics.UniformKServer.BalancedStar

namespace OAI

section
namespace UniformKServer.TreeRounding
open UniformKServer.BalancedStar
noncomputable section

structure Shape (n : ℕ) where
  parent : Fin (n+1) → Fin (n+1)
  earlier : ∀ v, v ≠ 0 → (parent v).val < v.val

abbrev Vertex (n : ℕ) := Fin (n+1)

def Children {n : ℕ} (S : Shape n) (v : Vertex n) :=
  {u : Vertex n // u ≠ 0 ∧ S.parent u = v}

instance {n : ℕ} (S : Shape n) (v : Vertex n) : Fintype (Children S v) :=
  by
  classical
  unfold Children
  infer_instance

def park {n : ℕ} (S : Shape n) (q : Vertex n → ℝ) (v : Vertex n) : ℝ :=
  q v - ∑ i : Children S v, q i.val

def intPark {n : ℕ} (S : Shape n) (x : Vertex n → ℤ) (v : Vertex n) : ℤ :=
  x v - ∑ i : Children S v, x i.val

structure Allocation {n : ℕ} (S : Shape n) (k : ℕ) where
  amount : Vertex n → ℝ
  nonneg : ∀ v, 0 ≤ amount v
  park_nonneg : ∀ v, 0 ≤ park S amount v
  root : amount 0 = k

def Rounded {n k : ℕ} {S : Shape n} (a : Allocation S k)
    (x : Vertex n → ℤ) : Prop :=
  x 0 = k ∧ (∀ v, Balanced (a.amount v) (x v)) ∧
    ∀ v, Balanced (park S a.amount v) (intPark S x v)

structure Law where
  State : Type
  finite : Fintype State
  mass : State → ℝ
  nonneg : ∀ s, 0 ≤ mass s
  total : letI := finite; ∑ s, mass s = 1

attribute [instance] Law.finite

def mean (L : Law) (f : L.State → ℝ) : ℝ := ∑ s, L.mass s * f s

structure Extension (L : Law) (n : ℕ) where
  law : Law
  original : law.State → L.State
  preserves : ∀ f : L.State → ℝ, mean law (f ∘ original) = mean L f
  value : law.State → Vertex n → ℤ

def movement {n : ℕ} (S : Shape n) (w : Vertex n → ℝ)
    (L : Law) (X : L.State → Vertex n → ℤ) (E : Extension L n) : ℝ :=
  ∑ v : Vertex n, if v = 0 then 0 else
    w (S.parent v) * mean E.law (fun s => |(E.value s v : ℝ) - (X (E.original s) v : ℝ)|)

def variation {n k : ℕ} {S : Shape n} (w : Vertex n → ℝ)
    (a b : Allocation S k) : ℝ :=
  ∑ v : Vertex n, if v = 0 then 0 else
    w (S.parent v) * |b.amount v - a.amount v|


abbrev Local {n : ℕ} (S : Shape n) (v : Vertex n) := Children S v ⊕ Unit

def localReal {n : ℕ} (S : Shape n) (q : Vertex n → ℝ) (v : Vertex n) : Local S v → ℝ
  | .inl i => q i.val
  | .inr _ => park S q v

def localInt {n : ℕ} (S : Shape n) (x : Vertex n → ℤ) (v : Vertex n) : Local S v → ℤ
  | .inl i => x i.val
  | .inr _ => intPark S x v

theorem sum_localReal {n : ℕ} (S : Shape n) (q : Vertex n → ℝ) (v : Vertex n) :
    ∑ i, localReal S q v i = q v := by
  rw [Fintype.sum_sum_type]
  simp [localReal, park]

theorem sum_localInt {n : ℕ} (S : Shape n) (x : Vertex n → ℤ) (v : Vertex n) :
    ∑ i, localInt S x v i = x v := by
  rw [Fintype.sum_sum_type]
  simp [localInt, intPark]

theorem cast_intPark {n : ℕ} (S : Shape n) (x : Vertex n → ℤ) (v : Vertex n) :
    (intPark S x v : ℝ) = (x v : ℝ) - ∑ i : Children S v, (x i.val : ℝ) := by
  simp [intPark]

theorem mean_sub (L : Law) (f g : L.State → ℝ) :
    mean L (fun s => f s-g s) = mean L f-mean L g := by
  simp [mean,mul_sub,Finset.sum_sub_distrib]

theorem mean_sum {ι : Type} [Fintype ι] (L : Law) (f : ι → L.State → ℝ) :
    mean L (fun s => ∑ i, f i s) = ∑ i, mean L (f i) := by
  simp only [mean,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem mean_congr (L : Law) {f g : L.State → ℝ} (h : ∀ s, f s = g s) :
    mean L f = mean L g := by
  simp only [mean,h]

theorem mean_const (L : Law) (c : ℝ) : mean L (fun _ => c) = c := by
  rw [mean,← Finset.sum_mul,L.total,one_mul]

theorem mean_mono (L : Law) {f g : L.State → ℝ} (h : ∀ s, f s ≤ g s) :
    mean L f ≤ mean L g :=
  Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h s) (L.nonneg s)

theorem mean_nonneg (L : Law) {f : L.State → ℝ} (h : ∀ s, 0 ≤ f s) :
    0 ≤ mean L f :=
  Finset.sum_nonneg fun s _ => mul_nonneg (L.nonneg s) (h s)

/-- Make the kernel valid even at probability-zero states. -/
theorem star_kernel {Ω ι : Type} [Fintype Ω] [Fintype ι]
    (I : BalancedStar.Input Ω ι) :
    ∃ (g : Ω × Finset ι → ℝ) (y : Ω × Finset ι → ι → ℤ),
      (∀ z, 0 ≤ g z) ∧ (∀ ω, ∑ A, g (ω,A) = I.μ ω) ∧
      (∀ z i, Balanced (I.b i) (y z i)) ∧
      (∀ z, ∑ i, y z i = I.N z.1) ∧
      (∀ i, ∑ z, g z * (y z i : ℝ) = I.b i) ∧
      (∑ z, g z * ∑ i, |(y z i : ℝ) - (I.X z.1 i : ℝ)|) ≤
        32*BalancedStar.T I + 11*BalancedStar.imbalance I := by
  classical
  obtain ⟨hv,g,hg,hrow,hvalid,hmean,hcost⟩ := BalancedStar.rounding_star I
  choose fallback hfb using hv
  let y := fun z : Ω × Finset ι => if 0 < g z then realized I.b z.2 else
    realized I.b (fallback z.1)
  have he (z : Ω × Finset ι) (i : ι) :
      g z * (y z i : ℝ) = g z * (realized I.b z.2 i : ℝ) := by
    dsimp only [y]
    split_ifs with hp
    · rfl
    · have hz : g z = 0 := le_antisymm (le_of_not_gt hp) (hg z)
      simp [hz]
  refine ⟨g,y,hg,hrow,?_,?_,?_,?_⟩
  · intro z i
    dsimp only [y]
    split_ifs with hp
    · exact (hvalid z hp).1 i
    · exact (hfb z.1).1 i
  · intro z
    dsimp only [y]
    split_ifs with hp
    · exact (hvalid z hp).2
    · exact (hfb z.1).2
  · intro i
    simpa only [he] using hmean i
  · calc
      _ = BalancedStar.jointCost I g := by
        apply Finset.sum_congr rfl
        intro z _
        dsimp only [y]
        split_ifs with hp
        · rfl
        · have hz : g z = 0 := le_antisymm (le_of_not_gt hp) (hg z)
          simp [hz]
      _ ≤ _ := hcost

/-- An extension of an already generated joint state preserves every old
observable and permits completely correlated prescribed parent totals. -/
theorem extended_star (L : Law) {ι : Type} [Fintype ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (X : L.State → ι → ℤ) (N : L.State → ℤ)
    (hX : ∀ s i, Balanced (a i) (X s i))
    (hN : ∀ s, Balanced (∑ i, b i) (N s))
    (hXm : ∀ i, mean L (fun s => (X s i : ℝ)) = a i)
    (hNm : mean L (fun s => (N s : ℝ)) = ∑ i, b i) :
    ∃ (L' : Law) (π : L'.State → L.State) (Y : L'.State → ι → ℤ),
      (∀ f : L.State → ℝ, mean L' (f ∘ π) = mean L f) ∧
      (∀ s i, Balanced (b i) (Y s i)) ∧
      (∀ s, ∑ i, Y s i = N (π s)) ∧
      (∀ i, mean L' (fun s => (Y s i : ℝ)) = b i) ∧
      mean L' (fun s => ∑ i, |(Y s i : ℝ) - (X (π s) i : ℝ)|) ≤
        32*(∑ i, |a i-b i|) + 11*mean L (fun s => |(N s : ℝ)-∑ i,(X s i : ℝ)|) := by
  classical
  let I : BalancedStar.Input L.State ι :=
    ⟨L.mass,L.nonneg,L.total,a,b,ha,hb,X,N,hX,hN,hXm,hNm⟩
  obtain ⟨g,y,hg,hrow,hy,hsum,hm,hcost⟩ := star_kernel I
  let L' : Law := ⟨L.State × Finset ι, inferInstance, g, hg, by
    rw [Fintype.sum_prod_type]
    simp only [hrow]
    exact L.total⟩
  refine ⟨L',Prod.fst,y,?_,hy,hsum,hm,hcost⟩
  intro f
  dsimp only [mean,L',Function.comp_def]
  rw [Fintype.sum_prod_type]
  simp only [← Finset.sum_mul,hrow]
  rfl


def assigned {n : ℕ} (S : Shape n) (s : ℕ) (u : Vertex n) : Prop :=
  u = 0 ∨ (S.parent u).val < s

def localMovement {n : ℕ} (S : Shape n) (L : Law)
    (X : L.State → Vertex n → ℤ) (E : Extension L n) (v : Vertex n) : ℝ :=
  mean E.law (fun s => ∑ i : Local S v,
    |(localInt S (E.value s) v i : ℝ) - (localInt S (X (E.original s)) v i : ℝ)|)

def nodeMovement {n : ℕ} (L : Law) (X : L.State → Vertex n → ℤ)
    (E : Extension L n) (v : Vertex n) : ℝ :=
  mean E.law (fun s => |(E.value s v : ℝ) - (X (E.original s) v : ℝ)|)

def localVariation {n k : ℕ} {S : Shape n} (a b : Allocation S k) (v : Vertex n) : ℝ :=
  ∑ i : Local S v, |localReal S a.amount v i - localReal S b.amount v i|

structure Good {n k : ℕ} {S : Shape n} (a b : Allocation S k)
    (L : Law) (X : L.State → Vertex n → ℤ) (s : ℕ) (E : Extension L n) : Prop where
  root : ∀ z, E.value z 0 = k
  balanced : ∀ u, assigned S s u → ∀ z, Balanced (b.amount u) (E.value z u)
  mean : ∀ u, assigned S s u → mean E.law (fun z => (E.value z u : ℝ)) = b.amount u
  parks : ∀ v, v.val < s → ∀ z,
    Balanced (park S b.amount v) (intPark S (E.value z) v)
  bound : ∀ v, v.val < s → localMovement S L X E v ≤
    32*localVariation a b v + 11*nodeMovement L X E v

def assignChildren {n : ℕ} (S : Shape n) (v : Vertex n)
    (old : Vertex n → ℤ) (y : Local S v → ℤ) (u : Vertex n) : ℤ := by
  classical
  exact if h : u ≠ 0 ∧ S.parent u = v then y (.inl ⟨u,h⟩) else old u

theorem parent_ne_self {n : ℕ} (S : Shape n) (u : Vertex n) (hu : u ≠ 0) :
    S.parent u ≠ u := by
  intro he
  have := S.earlier u hu
  rw [he] at this
  exact (lt_irrefl _ this)

theorem assigned_current {n : ℕ} (S : Shape n) (v : Vertex n) : assigned S v.val v := by
  by_cases hv : v=0
  · exact Or.inl hv
  · exact Or.inr (S.earlier v hv)

theorem assign_child {n : ℕ} (S : Shape n) (v : Vertex n)
    (old : Vertex n → ℤ) (y : Local S v → ℤ) (u : Children S v) :
    assignChildren S v old y u.val = y (.inl u) := by
  classical
  simp only [assignChildren, dite_eq_left u.property]
  congr 2

theorem assign_unchanged {n : ℕ} (S : Shape n) (v : Vertex n)
    (old : Vertex n → ℤ) (y : Local S v → ℤ) (u : Vertex n)
    (hu : u = 0 ∨ S.parent u ≠ v) : assignChildren S v old y u = old u := by
  classical
  rcases hu with rfl | hu
  · simp [assignChildren]
  · simp [assignChildren,hu]

theorem assign_earlier {n : ℕ} (S : Shape n) (v : Vertex n)
    (old : Vertex n → ℤ) (y : Local S v → ℤ) (u : Vertex n) (hu : u.val ≤ v.val) :
    assignChildren S v old y u = old u := by
  apply assign_unchanged
  by_cases hz : u=0
  · exact Or.inl hz
  · right
    intro he
    have := S.earlier u hz
    rw [he] at this
    omega

theorem assign_local {n : ℕ} (S : Shape n) (v : Vertex n)
    (old : Vertex n → ℤ) (y : Local S v → ℤ)
    (hy : ∑ i, y i = old v) :
    ∀ i, localInt S (assignChildren S v old y) v i = y i := by
  intro i
  cases i with
  | inl i => exact assign_child S v old y i
  | inr u =>
    cases u
    dsimp only [localInt,intPark]
    rw [assign_earlier S v old y v le_rfl]
    simp only [assign_child]
    rw [Fintype.sum_sum_type] at hy
    simp only [Fintype.sum_unique] at hy
    rw [sub_eq_iff_eq_add]
    simpa only [add_comm] using hy.symm

theorem assign_old_local {n : ℕ} (S : Shape n) (v : Vertex n)
    (old : Vertex n → ℤ) (y : Local S v → ℤ) (j : Vertex n) (hj : j.val < v.val) :
    ∀ i, localInt S (assignChildren S v old y) j i = localInt S old j i := by
  have hne : j ≠ v := by intro he; subst j; exact lt_irrefl _ hj
  have hc (i : Children S j) : assignChildren S v old y i.val = old i.val :=
    assign_unchanged S v old y i.val (Or.inr (by rw [i.property.2]; exact hne))
  intro i
  cases i with
  | inl i => exact hc i
  | inr u => simp only [localInt,intPark,assign_earlier S v old y j hj.le,hc]

theorem old_local_mean {n k : ℕ} (S : Shape n) (a : Allocation S k)
    (L : Law) (X : L.State → Vertex n → ℤ)
    (hm : ∀ v, mean L (fun s => (X s v : ℝ)) = a.amount v)
    (E : Extension L n) (v : Vertex n) :
    ∀ i, mean E.law (fun s => (localInt S (X (E.original s)) v i : ℝ)) =
      localReal S a.amount v i := by
  intro i
  rw [show (fun s => (localInt S (X (E.original s)) v i : ℝ)) =
    (fun s => (localInt S (X s) v i : ℝ)) ∘ E.original from rfl,E.preserves]
  cases i with
  | inl i => exact hm i.val
  | inr u =>
    simp only [localInt,cast_intPark,mean_sub,mean_sum,hm,localReal,park]


theorem good_step {n k : ℕ} (S : Shape n) (a b : Allocation S k)
    (L : Law) (X : L.State → Vertex n → ℤ)
    (hX : ∀ s, Rounded a (X s))
    (hm : ∀ v, mean L (fun s => (X s v : ℝ)) = a.amount v)
    (v : Vertex n) (E : Extension L n) (hE : Good a b L X v.val E) :
    ∃ E' : Extension L n, Good a b L X (v.val+1) E' := by
  classical
  have hpos (q : Allocation S k) (i : Local S v) : 0 ≤ localReal S q.amount v i := by
    cases i with
    | inl i => exact q.nonneg i.val
    | inr _ => exact q.park_nonneg v
  have hxb (s : E.law.State) (i : Local S v) :
      Balanced (localReal S a.amount v i) (localInt S (X (E.original s)) v i) := by
    cases i with
    | inl i => exact (hX (E.original s)).2.1 i.val
    | inr _ => exact (hX (E.original s)).2.2 v
  obtain ⟨L',π,Y,hpres,hy,hsum,hym,hcost⟩ := extended_star E.law
    (localReal S a.amount v) (localReal S b.amount v) (hpos a) (hpos b)
    (fun s => localInt S (X (E.original s)) v) (fun s => E.value s v)
    hxb (by simpa only [sum_localReal] using hE.balanced v (assigned_current S v))
    (old_local_mean S a L X hm E v)
    (by simpa only [sum_localReal] using hE.mean v (assigned_current S v))
  let E' : Extension L n := {
    law := L'
    original := E.original ∘ π
    preserves := by
      intro f
      change mean L' ((f ∘ E.original) ∘ π) = mean L f
      rw [hpres,E.preserves]
    value := fun z => assignChildren S v (E.value (π z)) (Y z) }
  have hnew (z : L'.State) (i : Local S v) : localInt S (E'.value z) v i = Y z i :=
    assign_local S v (E.value (π z)) (Y z) (hsum z) i
  have hval (u : Vertex n) (hu : assigned S v.val u) (z : L'.State) :
      E'.value z u = E.value (π z) u := by
    apply assign_unchanged
    rcases hu with hu | hu
    · exact Or.inl hu
    · right
      intro he
      rw [he] at hu
      exact lt_irrefl _ hu
  have hprev (j : Vertex n) (hj : j.val < v.val) (z : L'.State) (i : Local S j) :
      localInt S (E'.value z) j i = localInt S (E.value (π z)) j i :=
    assign_old_local S v _ _ j hj i
  have hnode (j : Vertex n) (hj : assigned S v.val j) :
      nodeMovement L X E' j = nodeMovement L X E j := by
    dsimp only [nodeMovement]
    simp only [hval j hj]
    exact hpres (fun z => |(E.value z j : ℝ) - (X (E.original z) j : ℝ)|)
  have hloc (j : Vertex n) (hj : j.val < v.val) :
      localMovement S L X E' j = localMovement S L X E j := by
    dsimp only [localMovement]
    simp only [hprev j hj]
    exact hpres (fun z => ∑ i : Local S j,
      |(localInt S (E.value z) j i : ℝ) - (localInt S (X (E.original z)) j i : ℝ)|)
  have hcase (u : Vertex n) (hu : assigned S (v.val+1) u) :
      assigned S v.val u ∨ u ≠ 0 ∧ S.parent u = v := by
    by_cases hp : assigned S v.val u
    · exact Or.inl hp
    right
    have hz : u ≠ 0 := fun he => hp (Or.inl he)
    refine ⟨hz,Fin.ext ?_⟩
    have ht : (S.parent u).val < v.val+1 := hu.resolve_left hz
    have hn : ¬ (S.parent u).val < v.val := fun he => hp (Or.inr he)
    omega
  refine ⟨E',?_⟩
  constructor
  · intro z
    rw [hval 0 (Or.inl rfl)]
    exact hE.root (π z)
  · intro u hu z
    rcases hcase u hu with hp | hp
    · rw [hval u hp]
      exact hE.balanced u hp (π z)
    · change Balanced (b.amount u) (assignChildren S v _ _ u)
      rw [show assignChildren S v (E.value (π z)) (Y z) u = Y z (.inl ⟨u,hp⟩) from
        assign_child S v _ _ ⟨u,hp⟩]
      exact hy z (.inl ⟨u,hp⟩)
  · intro u hu
    rcases hcase u hu with hp | hp
    · simp only [hval u hp]
      rw [show (fun z => (E.value (π z) u : ℝ)) =
        (fun z => (E.value z u : ℝ)) ∘ π from rfl,hpres]
      exact hE.mean u hp
    · have hc (z : L'.State) : E'.value z u = Y z (.inl ⟨u,hp⟩) :=
        assign_child S v _ _ ⟨u,hp⟩
      simp only [hc]
      exact hym (.inl ⟨u,hp⟩)
  · intro j hj z
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · change Balanced _ (localInt S (E'.value z) j (.inr ()))
      rw [hprev j hj]
      exact hE.parks j hj (π z)
    · have he : j=v := Fin.ext hj
      subst j
      change Balanced _ (localInt S (E'.value z) v (.inr ()))
      rw [hnew]
      exact hy z (.inr ())
  · intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · rw [hloc j hj,hnode j (by
        by_cases hz : j=0
        · exact Or.inl hz
        · exact Or.inr (lt_trans (S.earlier j hz) hj))]
      exact hE.bound j hj
    · have he : j=v := Fin.ext hj
      subst j
      rw [hnode v (assigned_current S v)]
      have hi : mean E.law (fun s => |(E.value s v : ℝ) -
          ∑ i : Local S v, (localInt S (X (E.original s)) v i : ℝ)|) =
          nodeMovement L X E v := by
        apply mean_congr
        intro s
        rw [← Int.cast_sum,sum_localInt]
      rw [hi] at hcost
      change mean L' _ ≤ _
      simpa only [hnew,localVariation,E',Function.comp_def] using hcost

theorem good_zero {n k : ℕ} (S : Shape n) (a b : Allocation S k)
    (L : Law) (X : L.State → Vertex n → ℤ) :
    ∃ E : Extension L n, Good a b L X 0 E := by
  classical
  let E : Extension L n := {
    law := L, original := id, preserves := fun _ => rfl
    value := fun _ v => if v = 0 then (k:ℤ) else 0 }
  refine ⟨E,?_⟩
  constructor
  · intro z; simp [E]
  · intro u hu z
    have he : u=0 := hu.resolve_right (by omega)
    subst u
    simp only [E,b.root]
    unfold BalancedStar.Balanced
    exact Or.inl (by simp)
  · intro u hu
    have he : u=0 := hu.resolve_right (by omega)
    subst u
    simp only [E,b.root]
    exact mean_const L _
  · intro v hv; omega
  · intro v hv; omega

theorem good_all {n k : ℕ} (S : Shape n) (a b : Allocation S k)
    (L : Law) (X : L.State → Vertex n → ℤ)
    (hX : ∀ s, Rounded a (X s))
    (hm : ∀ v, mean L (fun s => (X s v : ℝ)) = a.amount v) :
    ∃ E : Extension L n, Good a b L X (n+1) E := by
  have hi (s : ℕ) (hs : s ≤ n+1) : ∃ E : Extension L n, Good a b L X s E := by
    induction s with
    | zero => exact good_zero S a b L X
    | succ s ih =>
      obtain ⟨E,hE⟩ := ih (by omega)
      exact good_step S a b L X hX hm ⟨s,by omega⟩ E hE
  exact hi (n+1) le_rfl


theorem sum_children {n : ℕ} (S : Shape n) (v : Vertex n) (f : Vertex n → ℝ) :
    ∑ i : Children S v, f i.val = ∑ u, if u ≠ 0 ∧ S.parent u = v then f u else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by intro u; simp) f).symm

theorem weighted_children {n : ℕ} (S : Shape n) (w f : Vertex n → ℝ) :
    (∑ v, w v * ∑ i : Children S v, f i.val) =
      ∑ u, if u=0 then 0 else w (S.parent u)*f u := by
  classical
  have he (v : Vertex n) : w v * (∑ i : Children S v, f i.val) =
      ∑ u, if u ≠ 0 ∧ S.parent u = v then w v*f u else 0 := by
    rw [sum_children S v f,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> simp
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : u=0
  · simp [hu]
  · simp [hu,eq_comm]

theorem weight_separation {n : ℕ} (S : Shape n) (w f : Vertex n → ℝ)
    (hsep : ∀ v, v ≠ 0 → 22*w v ≤ w (S.parent v))
    (hf : ∀ v, 0 ≤ f v) (hf0 : f 0 = 0) :
    22*(∑ v, w v*f v) ≤ ∑ v, if v=0 then 0 else w (S.parent v)*f v := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : v=0
  · simp [hv,hf0]
  · simp only [ite_eq_right hv]
    nlinarith [mul_le_mul_of_nonneg_right (hsep v hv) (hf v)]

theorem localVariation_le {n k : ℕ} (S : Shape n) (a b : Allocation S k)
    (v : Vertex n) :
    localVariation a b v ≤ 2*(∑ i : Children S v, |b.amount i.val-a.amount i.val|) +
      |b.amount v-a.amount v| := by
  have hp : |park S a.amount v - park S b.amount v| ≤
      |a.amount v-b.amount v| + ∑ i : Children S v, |a.amount i.val-b.amount i.val| := by
    calc
      _ = |(a.amount v-b.amount v) -
        ∑ i : Children S v, (a.amount i.val-b.amount i.val)| := by
          congr 1
          simp only [park,Finset.sum_sub_distrib]
          ring
      _ ≤ |a.amount v-b.amount v| + |∑ i : Children S v,
          (a.amount i.val-b.amount i.val)| := abs_sub _ _
      _ ≤ _ := by
        have ht := Finset.abs_sum_le_sum_abs
          (fun i : Children S v => a.amount i.val-b.amount i.val) Finset.univ
        linarith
  dsimp only [localVariation]
  rw [Fintype.sum_sum_type]
  simp only [localReal,Fintype.sum_unique]
  simp_rw [abs_sub_comm (b.amount _) (a.amount _)]
  linarith

theorem childMovement_le {n : ℕ} (S : Shape n) (L : Law)
    (X : L.State → Vertex n → ℤ) (E : Extension L n) (v : Vertex n) :
    (∑ i : Children S v, nodeMovement L X E i.val) ≤ localMovement S L X E v := by
  dsimp only [nodeMovement,localMovement]
  rw [← mean_sum]
  apply mean_mono
  intro s
  rw [Fintype.sum_sum_type]
  simp only [localInt,Fintype.sum_unique]
  exact le_add_of_nonneg_right (abs_nonneg _)

/-- Exact companion proposition rounding-global for one conditional finite
update. Geometric separation tau ≥22 is stated as 22*w_child ≤ w_parent,
which includes the exact source weights r_j. No local kernels are assumed. -/
theorem tree_rounding {n k : ℕ} (S : Shape n) (w : Vertex n → ℝ)
    (hw : ∀ v, 0 ≤ w v)
    (hsep : ∀ v, v ≠ 0 → 22*w v ≤ w (S.parent v))
    (a b : Allocation S k) (L : Law) (X : L.State → Vertex n → ℤ)
    (hX : ∀ s, Rounded a (X s))
    (hmean : ∀ v, mean L (fun s => (X s v : ℝ)) = a.amount v) :
    ∃ E : Extension L n,
      (∀ s, Rounded b (E.value s)) ∧
      (∀ v, mean E.law (fun s => (E.value s v : ℝ)) = b.amount v) ∧
      movement S w L X E ≤ 132 * variation w a b := by
  classical
  obtain ⟨E,hE⟩ := good_all S a b L X hX hmean
  have hall (v : Vertex n) : assigned S (n+1) v := Or.inr (S.parent v).isLt
  refine ⟨E,?_,?_,?_⟩
  · intro s
    exact ⟨hE.root s,fun v => hE.balanced v (hall v) s,
      fun v => hE.parks v v.isLt s⟩
  · exact fun v => hE.mean v (hall v)
  let f : Vertex n → ℝ := nodeMovement L X E
  let g : Vertex n → ℝ := fun v => |b.amount v-a.amount v|
  have hf (v : Vertex n) : 0 ≤ f v := mean_nonneg E.law fun _ => abs_nonneg _
  have hg (v : Vertex n) : 0 ≤ g v := abs_nonneg _
  have hf0 : f 0 = 0 := by
    dsimp only [f,nodeMovement]
    calc
      _ = mean E.law (fun _ => 0) := by
        apply mean_congr
        intro s
        rw [hE.root s,(hX (E.original s)).1]
        simp
      _ = 0 := mean_const _ _
  have hg0 : g 0 = 0 := by simp [g,a.root,b.root]
  have hlocal (v : Vertex n) : (∑ i : Children S v, f i.val) ≤
      32*(2*(∑ i : Children S v,g i.val)+g v)+11*f v := by
    calc
      _ ≤ localMovement S L X E v := childMovement_le S L X E v
      _ ≤ 32*localVariation a b v+11*f v := hE.bound v v.isLt
      _ ≤ _ := by
        have ht := localVariation_le S a b v
        dsimp only [g]
        linarith
  have hrec := Finset.sum_le_sum (s := Finset.univ)
    (fun v _ => mul_le_mul_of_nonneg_left (hlocal v) (hw v))
  have hleft : (∑ v, w v * ∑ i : Children S v, f i.val) = movement S w L X E :=
    weighted_children S w f
  have hright : (∑ v, w v * (32*(2*(∑ i : Children S v,g i.val)+g v)+11*f v)) =
      64*variation w a b+32*(∑ v,w v*g v)+11*(∑ v,w v*f v) := by
    calc
      _ = ∑ v, (64*(w v*(∑ i : Children S v,g i.val))+
          32*(w v*g v)+11*(w v*f v)) := by
            apply Finset.sum_congr rfl
            intro v _
            ring
      _ = 64*(∑ v,w v*(∑ i : Children S v,g i.val))+
          32*(∑ v,w v*g v)+11*(∑ v,w v*f v) := by
            rw [Finset.sum_add_distrib,Finset.sum_add_distrib,
              ← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum]
      _ = _ := by rw [weighted_children]; rfl
  rw [hleft,hright] at hrec
  have hfs : 22*(∑ v,w v*f v) ≤ movement S w L X E :=
    weight_separation S w f hsep hf hf0
  have hgs : 22*(∑ v,w v*g v) ≤ variation w a b :=
    weight_separation S w g hsep hg hg0
  have hgV : 0 ≤ variation w a b := by
    apply Finset.sum_nonneg
    intro v _
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hw _) (abs_nonneg _)
  linarith


/-- The independent BalancedRepair.initial rounding: no movement is charged for selecting it. -/
theorem tree_initialization {n k : ℕ} (S : Shape n) (a : Allocation S k) :
    ∃ (L : Law) (X : L.State → Vertex n → ℤ),
      (∀ s, Rounded a (X s)) ∧
      (∀ v, mean L (fun s => (X s v : ℝ)) = a.amount v) := by
  classical
  let x : Vertex n → ℤ := fun v => if v=0 then k else 0
  have hc (v : Vertex n) (i : Children S v) : x i.val = 0 := by
    simp [x,i.property.1]
  have hsum (v : Vertex n) : ∑ i : Children S v, (x i.val : ℝ) = 0 := by
    simp only [hc,Int.cast_zero,Finset.sum_const_zero]
  have hnonneg (v : Vertex n) : 0 ≤ (x v : ℝ) := by
    dsimp [x]
    split_ifs <;> positivity
  let b : Allocation S k := {
    amount := fun v => (x v : ℝ)
    nonneg := hnonneg
    park_nonneg := by intro v; simpa only [park,hsum,sub_zero] using hnonneg v
    root := by simp [x] }
  let L : Law := {
    State := Unit
    finite := inferInstance
    mass := fun _ => 1
    nonneg := by intro; norm_num
    total := by simp }
  let X : L.State → Vertex n → ℤ := fun _ => x
  have hr : ∀ s, Rounded b (X s) := by
    intro s
    refine ⟨by simp [X,x],?_,?_⟩
    · intro v
      left
      exact (Int.floor_intCast (x v)).symm
    · intro v
      left
      simp only [b,park,sub_zero,intPark,X,hc,Finset.sum_const_zero]
      simp
  have hm : ∀ v, mean L (fun s => (X s v : ℝ)) = b.amount v := by
    intro v
    exact mean_const L _
  obtain ⟨E,hE,hmE,_⟩ := tree_rounding S (fun _ => 0) (by simp) (by simp)
    b a L X hr hm
  exact ⟨E.law,E.value,hE,hmE⟩

end
end UniformKServer.TreeRounding

end

end OAI
