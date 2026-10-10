import Mathlib
import OAI.Combinatorics.Chromatic.Walls.IncomingEquality

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics

lemma period_total_nonpos (B K : ℕ → ℤ) (hB : ∀ n, 0 ≤ B n)
    (hK : Monotone K) (step : ∀ n, B (n+1) = B n - K (n+1)) (n : ℕ) :
    K n ≤ 0 := by
  by_contra hn
  have hk : 1 ≤ K n := by omega
  have hb : ∀ t : ℕ, B (n+t) ≤ B n - (t:ℤ) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hm := hK (show n ≤ n+t+1 by omega)
      have hs := step (n+t)
      simp only [Nat.add_succ, Nat.add_zero, Nat.cast_succ] at *
      omega
  have H := hb ((B n).toNat+1)
  have H0 := hB (n+((B n).toNat+1))
  have Hn := Int.toNat_of_nonneg (hB n)
  omega

lemma monotone_int_stabilizes (a : ℕ → ℤ) (ha : Monotone a)
    (hb : ∃ b, ∀ n, a n ≤ b) : ∃ N, ∀ n, N ≤ n → a n = a N := by
  obtain ⟨v,⟨N,hN⟩,hv⟩ := Int.exists_greatest_of_bdd
    (P := fun z => ∃ n, a n = z)
    (by obtain ⟨b,hb⟩ := hb; exact ⟨b,fun z ⟨n,hn⟩ => hn ▸ hb n⟩)
    ⟨a 0,0,rfl⟩
  refine ⟨N,fun n hn => le_antisymm ?_ (ha hn)⟩
  rw [hN]
  exact hv (a n) ⟨n,rfl⟩

lemma finite_coordinates_stabilize {ι : Type*} [Fintype ι]
    (a : ℕ → ι → ℤ) (ha : ∀ i, Monotone (fun n => a n i))
    (hs : ∀ n, ∑ i, a n i ≤ 0) :
    ∃ N, ∀ n, N ≤ n → ∀ i, a n i = a N i := by
  classical
  have hb : ∀ i, ∃ b, ∀ n, a n i ≤ b := by
    intro i
    refine ⟨-∑ j ∈ Finset.univ.erase i, a 0 j,fun n => ?_⟩
    have H := Finset.sum_le_sum (s := Finset.univ.erase i)
      (fun j _ => ha j (show 0 ≤ n by omega))
    have he := Finset.sum_erase_add (Finset.univ : Finset ι) (a n) (Finset.mem_univ i)
    have Hn := hs n
    dsimp only at H he
    omega
  choose N hN using fun i => monotone_int_stabilizes (fun n => a n i) (ha i) (hb i)
  refine ⟨Finset.univ.sup N,fun n hn i => ?_⟩
  have hi : N i ≤ Finset.univ.sup N := Finset.le_sup (f := N) (Finset.mem_univ i)
  rw [hN i n (hi.trans hn),hN i _ hi]

lemma nonnegative_affine_slope (a b : ℤ) (h : ∃ N : ℕ, ∀ L, N ≤ L →
    0 ≤ a + (L:ℤ)*b) : 0 ≤ b := by
  obtain ⟨N,hN⟩ := h
  by_contra hb
  have hb' : b ≤ -1 := by omega
  let L := max N (a.toNat+1)
  have hL := hN L (le_max_left _ _)
  have hLa : a < (L:ℤ) := by
    have hh : a.toNat+1 ≤ L := le_max_right _ _
    have ha : a ≤ (a.toNat:ℤ) := by omega
    omega
  have hL0 : (0:ℤ) ≤ L := Int.natCast_nonneg L
  nlinarith

lemma concave_nonpositive_zero (D : ℕ) (K : ℕ → ℤ)
    (h0 : K 0 = 0) (hD : K D = 0)
    (hn : ∀ i, i ≤ D → K i ≤ 0)
    (hc : ∀ i, 0 < i → i < D → 0 ≤ 2*K i-K (i-1)-K (i+1)) :
    ∀ i, i ≤ D → K i = 0 := by
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image (Finset.range (D+1)) K
    (by exact ⟨0,by simp⟩)
  have hjD : j ≤ D := by
    have h := Finset.mem_range.mp hj
    omega
  have hm : ∀ i, i ≤ D → K j ≤ K i := by
    intro i hi
    exact hmin i (Finset.mem_range.mpr (by omega))
  have propagate : ∀ i, i ≤ D → K i = K j → K j = 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi he
      by_cases hz : i = 0
      · simpa [hz,h0] using he.symm
      by_cases hd : i = D
      · simpa [hd,hD] using he.symm
      have H := hc i (by omega) (by omega)
      have Hl := hm (i-1) (by omega)
      have Hr := hm (i+1) (by omega)
      have he' : K (i-1) = K j := by omega
      exact ih (i-1) (by omega) (by omega) he'
  have hj0 := propagate j hjD rfl
  intro i hi
  have hh := hm i hi
  have hh' := hn i hi
  omega
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open ElementaryPositivity.QuantumTorus
variable {n : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
abbrev Vertex (n : ℕ) (B : Type*) := Sum (Fin (n+1)) B
abbrev Lattice (n : ℕ) (B : Type*) := Vertex n B → ℤ

def anchor (i : Fin (n+1)) : Lattice n B := Pi.single (Sum.inl i) 1
def bridge (b : B) : Lattice n B := Pi.single (Sum.inr b) 1

def delta (level : B → Fin n) (b : B) : Lattice n B :=
  anchor (level b).succ - anchor (level b).castSucc

def eventRoot (level : B → Fin n) (L : ℕ) (b : B) : Lattice n B :=
  bridge b - anchor (level b).castSucc + (L:ℤ) • delta level b

def levelTotal (level : B → Fin n) (i : Fin n) : Lattice n B →+ ℤ where
  toFun m := ∑ b, if level b = i then m (Sum.inr b) else 0
  map_zero' := by simp
  map_add' m m' := by
    change (∑ b, if level b = i then m (Sum.inr b)+m' (Sum.inr b) else 0) = _
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> simp

def cutContains (level : B → Fin n) (i : Fin n) : Vertex n B → Prop
  | Sum.inl a => a.val ≤ i.val
  | Sum.inr b => (level b).val ≤ i.val

instance cutContains_decidable (level : B → Fin n) (i : Fin n) :
    DecidablePred (cutContains level i) := fun a => by
  cases a <;> unfold cutContains <;> infer_instance

def cutPrefix (level : B → Fin n) (i : Fin n) : Lattice n B →+ ℤ where
  toFun m := ∑ a, if cutContains level i a then m a else 0
  map_zero' := by simp
  map_add' m m' := by
    change (∑ a, if cutContains level i a then m a+m' a else 0) = _
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> simp

@[simp] lemma cutPrefix_single (level : B → Fin n) (i : Fin n) (a : Vertex n B) (z : ℤ) :
    cutPrefix level i (Pi.single a z) = if cutContains level i a then z else 0 := by
  classical
  change (∑ v, if cutContains level i v then Pi.single a z v else 0) = _
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

@[simp] lemma levelTotal_anchor (level : B → Fin n) (i : Fin n) (a : Fin (n+1)) :
    levelTotal level i (anchor a) = 0 := by
  simp [levelTotal,anchor]
@[simp] lemma levelTotal_bridge (level : B → Fin n) (i : Fin n) (b : B) :
    levelTotal level i (bridge b) = if level b = i then 1 else 0 := by
  change (∑ c, if level c = i then bridge b (Sum.inr c) else 0) = _
  rw [Finset.sum_eq_single b]
  · simp [bridge]
  · intro c _ hc
    simp [bridge,hc]
  · simp

omit [DecidableEq B] in
lemma total_levels (level : B → Fin n) (m : Lattice n B) :
    ∑ i, levelTotal level i m = ∑ b, m (Sum.inr b) := by
  simp only [levelTotal,AddMonoidHom.coe_mk,ZeroHom.coe_mk]
  rw [Finset.sum_comm]
  simp

omit [Fintype B] in
@[simp] lemma eventRoot_bridge (level : B → Fin n) (L : ℕ) (b c : B) :
    eventRoot level L b (Sum.inr c) = if c = b then 1 else 0 := by
  simp [eventRoot,bridge,anchor,delta,Pi.single_apply]

@[simp] lemma cutPrefix_eventRoot (level : B → Fin n) (i : Fin n) (L : ℕ) (b : B) :
    cutPrefix level i (eventRoot level L b) = if level b = i then -(L:ℤ) else 0 := by
  simp only [eventRoot,delta,map_add,map_sub,map_zsmul,anchor,bridge,cutPrefix_single,
    cutContains,Fin.val_succ,Fin.val_castSucc,smul_eq_mul]
  by_cases h : level b = i
  · simp [h]
  · have hne : (level b).val ≠ i.val := fun hh => h (Fin.ext hh)
    split_ifs <;> simp_all <;> omega

@[simp] lemma levelTotal_eventRoot (level : B → Fin n) (i : Fin n) (L : ℕ) (b : B) :
    levelTotal level i (eventRoot level L b) = if level b = i then 1 else 0 := by
  simp only [eventRoot,delta,map_add,map_sub,map_zsmul,levelTotal_bridge,levelTotal_anchor,
    sub_self,smul_zero,add_zero,sub_zero]

def periodFunctional (level : B → Fin n) (i : Fin n) (L : ℕ) : Lattice n B →+ ℤ :=
  cutPrefix level i + (L:ℤ) • levelTotal level i

@[simp] lemma periodFunctional_eventRoot (level : B → Fin n) (i : Fin n) (L : ℕ) (b : B) :
    periodFunctional level i L (eventRoot level L b) = 0 := by
  simp only [periodFunctional,AddMonoidHom.add_apply,AddMonoidHom.zsmul_apply,
    cutPrefix_eventRoot,levelTotal_eventRoot,smul_eq_mul]
  split_ifs <;> ring

variable (Ω : Lattice n B →+ Lattice n B →+ ℤ)

def rotate (level : B → Fin n) (L : ℕ) (m : Lattice n B) (b : B) : Lattice n B :=
  mutationIncomingLabel Ω (eventRoot level L b) m

def period (level : B → Fin n) (cycle : List B) (L : ℕ) (m : Lattice n B) : Lattice n B :=
  cycle.foldl (rotate Ω level L) m

def history (level : B → Fin n) (cycle : List B) (m : Lattice n B) : ℕ → Lattice n B
  | 0 => m
  | L+1 => period Ω level cycle L (history level cycle m L)

omit [Fintype B] in
lemma rotate_bridge_mono (level : B → Fin n) (L : ℕ) (m : Lattice n B) (b c : B) :
    m (Sum.inr c) ≤ rotate Ω level L m b (Sum.inr c) := by
  simp only [rotate,mutationIncomingLabel,Pi.add_apply,Pi.smul_apply,eventRoot_bridge,
    smul_eq_mul]
  split_ifs <;> simp

omit [Fintype B] in
lemma period_bridge_mono (level : B → Fin n) (cycle : List B) (L : ℕ) (m : Lattice n B) (c : B) :
    m (Sum.inr c) ≤ period Ω level cycle L m (Sum.inr c) := by
  induction cycle generalizing m with
  | nil => exact le_rfl
  | cons b bs ih =>
    exact (rotate_bridge_mono Ω level L m b c).trans (ih (rotate Ω level L m b))

lemma periodFunctional_rotate (level : B → Fin n) (i : Fin n) (L : ℕ) (m : Lattice n B) (b : B) :
    periodFunctional level i L (rotate Ω level L m b) = periodFunctional level i L m := by
  simp only [rotate,mutationIncomingLabel,map_add,map_zsmul,periodFunctional_eventRoot,
    smul_zero,add_zero]

lemma periodFunctional_period (level : B → Fin n) (i : Fin n) (cycle : List B)
    (L : ℕ) (m : Lattice n B) :
    periodFunctional level i L (period Ω level cycle L m) = periodFunctional level i L m := by
  induction cycle generalizing m with
  | nil => rfl
  | cons b bs ih =>
    change periodFunctional level i L (period Ω level bs L (rotate Ω level L m b)) = _
    rw [ih,periodFunctional_rotate]

omit [Fintype B] in
lemma history_bridge_mono (level : B → Fin n) (cycle : List B) (m : Lattice n B) (b : B) :
    Monotone (fun L => history Ω level cycle m L (Sum.inr b)) := by
  apply monotone_nat_of_le_succ
  intro L
  exact period_bridge_mono Ω level cycle L _ b

lemma history_total_mono (level : B → Fin n) (cycle : List B) (m : Lattice n B) (i : Fin n) :
    Monotone (fun L => levelTotal level i (history Ω level cycle m L)) := by
  intro L L' h
  apply Finset.sum_le_sum
  intro b _
  split_ifs
  · exact history_bridge_mono Ω level cycle m b h
  · rfl

def cutDeficit (level : B → Fin n) (i : Fin n) (N L : ℕ) (m : Lattice n B) : ℤ :=
  (N:ℤ)-periodFunctional level i L m

lemma history_deficit_step (level : B → Fin n) (cycle : List B) (m : Lattice n B)
    (i : Fin n) (N L : ℕ) :
    cutDeficit level i N (L+1) (history Ω level cycle m (L+1)) =
      cutDeficit level i N L (history Ω level cycle m L) -
        levelTotal level i (history Ω level cycle m (L+1)) := by
  have h := periodFunctional_period Ω level i cycle L (history Ω level cycle m L)
  change periodFunctional level i L (history Ω level cycle m (L+1)) = _ at h
  simp only [cutDeficit,periodFunctional,AddMonoidHom.add_apply,AddMonoidHom.zsmul_apply,
    smul_eq_mul,Nat.cast_add,Nat.cast_one] at *
  linear_combination -h

lemma history_total_nonpos (level : B → Fin n) (cycle : List B) (m : Lattice n B)
    (N : ℕ) (hs : ∀ L i, 0 ≤ cutDeficit level i N L (history Ω level cycle m L))
    (L : ℕ) (i : Fin n) : levelTotal level i (history Ω level cycle m L) ≤ 0 :=
  period_total_nonpos (fun L => cutDeficit level i N L (history Ω level cycle m L))
    (fun L => levelTotal level i (history Ω level cycle m L)) (fun L => hs L i)
    (history_total_mono Ω level cycle m i) (history_deficit_step Ω level cycle m i N) L

lemma history_bridge_stabilizes (level : B → Fin n) (cycle : List B) (m : Lattice n B)
    (N : ℕ) (hs : ∀ L i, 0 ≤ cutDeficit level i N L (history Ω level cycle m L)) :
    ∃ T, ∀ L, T ≤ L → ∀ b, history Ω level cycle m L (Sum.inr b) =
      history Ω level cycle m T (Sum.inr b) := by
  apply finite_coordinates_stabilize (fun L b => history Ω level cycle m L (Sum.inr b))
    (history_bridge_mono Ω level cycle m)
  intro L
  rw [←total_levels level]
  exact Finset.sum_nonpos (fun i _ => history_total_nonpos Ω level cycle m N hs L i)
end ElementaryPositivity.TriangularDynamics

end

end OAI
