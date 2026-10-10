import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped ENNReal NNReal
namespace HardSphere.Lattice

def binaryValue : (n : ℕ) → (Fin n → Bool) → ℕ
  | 0, _ => 0
  | n + 1, b => (b 0).toNat + 2 * binaryValue n (fun i ↦ b i.succ)

lemma binaryValue_injective (n : ℕ) : Function.Injective (binaryValue n) := by
  induction n with
  | zero => intro b c _; exact Subsingleton.elim _ _
  | succ n ih =>
    intro b c h
    have h0 : b 0 = c 0 := by
      unfold binaryValue at h
      cases hb : b 0 <;> cases hc : c 0 <;> simp_all <;> omega
    have ht : (fun i : Fin n ↦ b i.succ) = (fun i : Fin n ↦ c i.succ) := by
      apply ih
      simp only [binaryValue, h0] at h
      omega
    funext i
    refine Fin.cases h0 (fun j ↦ congrFun ht j) i

def signedValue (n : ℕ) (b : Fin n → Bool) : ℤ :=
  2 * (binaryValue n b : ℤ) - ((2 : ℤ) ^ n - 1)

lemma signedValue_injective (n : ℕ) : Function.Injective (signedValue n) := by
  intro b c h
  apply binaryValue_injective n
  have h' : (binaryValue n b : ℤ) = (binaryValue n c : ℤ) := by
    unfold signedValue at h
    omega
  exact_mod_cast h'

lemma pmf_map_injective_atom_le {A B : Type*} (p : PMF A) (f : A → B)
    (hf : Function.Injective f) (b : B) (a : ℝ≥0∞) (ha : ∀ x, p x ≤ a) :
    p.map f b ≤ a := by
  classical
  rw [PMF.map_apply]
  by_cases hb : ∃ x, b = f x
  · obtain ⟨x, hx⟩ := hb
    rw [tsum_eq_single x]
    · simpa [hx] using ha x
    · intro y hy
      have hby : b ≠ f y := fun h ↦ hy (hf (hx.symm.trans h)).symm
      simp [hby]
  · have hz : ∀ x, b ≠ f x := by simpa using hb
    simp only [ite_eq_right (hz _), tsum_zero]
    exact zero_le

theorem signed_uniform_atom (n : ℕ) (z : ℤ) :
    (PMF.uniformOfFintype (Fin n → Bool)).map (signedValue n) z ≤
      ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  apply pmf_map_injective_atom_le _ _ (signedValue_injective n)
  intro b
  simp [PMF.uniformOfFintype_apply]

lemma pmf_independent_shift_atom_le {A : Type*} (q : PMF A) (p : PMF ℤ)
    (f : A → ℤ) (a : ℝ≥0∞) (ha : ∀ z, p z ≤ a) (z : ℤ) :
    (q.bind fun x ↦ p.map (fun y ↦ y + f x)) z ≤ a := by
  rw [PMF.bind_apply]
  calc
    (∑' x, q x * (p.map (fun y ↦ y + f x)) z) ≤ ∑' x, q x * a := by
      apply ENNReal.tsum_le_tsum
      intro x
      exact mul_le_mul_right
        (pmf_map_injective_atom_le p _ (fun _ _ h ↦ add_right_cancel h) z a ha) _
    _ = a := by rw [ENNReal.tsum_mul_right, q.tsum_coe, one_mul]

def spin (b : Bool) : ℤ := 2 * (b.toNat : ℤ) - 1

@[simp] lemma abs_spin (b : Bool) : |spin b| = 1 := by cases b <;> norm_num [spin]

lemma binaryValue_snoc (n : ℕ) (b : Fin n → Bool) (c : Bool) :
    binaryValue (n+1) (Fin.snoc b c) = binaryValue n b + 2^n * c.toNat := by
  induction n with
  | zero =>
    change (Fin.snoc (α := fun _ ↦ Bool) b c (Fin.last 0)).toNat + 2*0 = 0 + 1*c.toNat
    rw [Fin.snoc_last]
    omega
  | succ n ih =>
    have ht : (fun i : Fin (n+1) ↦ Fin.snoc (α := fun _ ↦ Bool) b c i.succ) =
        Fin.snoc (α := fun _ ↦ Bool) (fun i : Fin n ↦ b i.succ) c := by
      funext i
      refine Fin.lastCases ?_ (fun i ↦ ?_) i
      · simp
      · rw [Fin.snoc_castSucc]
        exact Fin.snoc_castSucc (α := fun _ ↦ Bool) c b i.succ
    change (Fin.snoc (α := fun _ ↦ Bool) b c 0).toNat +
      2 * binaryValue (n+1) (fun i ↦ Fin.snoc (α := fun _ ↦ Bool) b c i.succ) =
      (b 0).toNat + 2 * binaryValue n (fun i ↦ b i.succ) + 2^(n+1)*c.toNat
    rw [ht, ih, Fin.snoc_apply_zero, pow_succ]
    ring

lemma signedValue_snoc (n : ℕ) (b : Fin n → Bool) (c : Bool) :
    signedValue (n+1) (Fin.snoc b c) = signedValue n b + (2 : ℤ)^n * spin c := by
  rw [signedValue, binaryValue_snoc]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
  unfold signedValue spin
  ring

def OffSpine : ℕ → Type
  | 0 => Unit
  | n+1 => OffSpine n × (((Fin n → Bool) × OffSpine n) × ((Fin n → Bool) × OffSpine n))

instance offSpineFintype : ∀ n, Fintype (OffSpine n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => by
    let : Fintype (OffSpine n) := offSpineFintype n
    exact inferInstanceAs (Fintype (OffSpine n ×
      (((Fin n → Bool) × OffSpine n) × ((Fin n → Bool) × OffSpine n))))

instance offSpineNonempty : ∀ n, Nonempty (OffSpine n)
  | 0 => ⟨()⟩
  | n+1 => by
    let : Nonempty (OffSpine n) := offSpineNonempty n
    exact inferInstanceAs (Nonempty (OffSpine n ×
      (((Fin n → Bool) × OffSpine n) × ((Fin n → Bool) × OffSpine n))))

abbrev TreeNoise (n : ℕ) := (Fin n → Bool) × OffSpine n

def leaves : (n : ℕ) → ℤ → TreeNoise n → List ℤ
  | 0, s, _ => [s]
  | n+1, s, w =>
    leaves n s (Fin.init w.1, w.2.1) ++ leaves n s w.2.2.1 ++
      leaves n (spin (w.1 (Fin.last n))) w.2.2.2

@[simp] lemma length_leaves (n : ℕ) (s : ℤ) (w : TreeNoise n) :
    (leaves n s w).length = 3^n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [leaves, List.length_append, ih, pow_succ]; omega

lemma abs_of_mem_leaves {n : ℕ} {s : ℤ} (hs : |s| = 1) (w : TreeNoise n)
    {x : ℤ} (hx : x ∈ leaves n s w) : |x| = 1 := by
  induction n generalizing s with
  | zero =>
    simp only [leaves, List.mem_singleton] at hx
    exact hx ▸ hs
  | succ n ih =>
    simp only [leaves, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact ih hs _ hx
    · exact ih hs _ hx
    · exact ih (abs_spin _) _ hx

def offSum : (n : ℕ) → OffSpine n → ℤ
  | 0, _ => 0
  | n+1, w => offSum n w.1 +
    (signedValue n w.2.1.1 + offSum n w.2.1.2) +
    (signedValue n w.2.2.1 + offSum n w.2.2.2)

lemma sum_leaves (n : ℕ) (s : ℤ) (w : TreeNoise n) :
    (leaves n s w).sum = (2 : ℤ)^n * s + signedValue n w.1 + offSum n w.2 := by
  induction n generalizing s with
  | zero => simp [leaves, signedValue, binaryValue, offSum]
  | succ n ih =>
    simp only [leaves, List.sum_append, ih, offSum]
    have hsnoc : Fin.snoc (Fin.init w.1) (w.1 (Fin.last n)) = w.1 := Fin.snoc_init_self _
    have hsv := signedValue_snoc n (Fin.init w.1) (w.1 (Fin.last n))
    rw [hsnoc] at hsv
    rw [hsv, pow_succ]
    ring

lemma uniform_product {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    PMF.uniformOfFintype (A × B) =
      (PMF.uniformOfFintype B).bind (fun b ↦
        (PMF.uniformOfFintype A).map (fun a ↦ (a,b))) := by
  classical
  ext ⟨a,b⟩
  simp [PMF.bind_apply, PMF.map_apply, PMF.uniformOfFintype_apply,
    Fintype.card_prod, ENNReal.mul_inv, Prod.mk.injEq, ite_and, mul_comm]

theorem leaf_sum_atom (n : ℕ) (s x : ℤ) :
    ((PMF.uniformOfFintype (TreeNoise n)).map (fun w ↦ (leaves n s w).sum)) x ≤
      ((2 : ℝ≥0∞)^n)⁻¹ := by
  rw [uniform_product, PMF.map_bind]
  simp_rw [PMF.map_comp, Function.comp_def, sum_leaves]
  have h : (fun w : OffSpine n ↦
      (PMF.uniformOfFintype (Fin n → Bool)).map
        (fun b ↦ (2:ℤ)^n * s + signedValue n b + offSum n w)) =
      (fun w : OffSpine n ↦
        ((PMF.uniformOfFintype (Fin n → Bool)).map (signedValue n)).map
          (fun y ↦ y + ((2:ℤ)^n * s + offSum n w))) := by
    funext w
    rw [PMF.map_comp]
    congr 1
    funext b
    dsimp
    ring
  rw [h]
  exact pmf_independent_shift_atom_le _ _ _ _ (signed_uniform_atom n) x

def branchEquiv (n : ℕ) : TreeNoise (n+1) ≃
    Bool × (TreeNoise n × (TreeNoise n × TreeNoise n)) where
  toFun w := (w.1 (Fin.last n), ((Fin.init w.1, w.2.1), w.2.2))
  invFun w := (Fin.snoc w.2.1.1 w.1, (w.2.1.2, w.2.2))
  left_inv w := by rcases w with ⟨b, c, d⟩; simp
  right_inv w := by simp

abbrev BranchContext (n : ℕ) := Bool × (TreeNoise n × TreeNoise n)

def branchAt (n : ℕ) (d : Fin 3) : TreeNoise (n+1) ≃ TreeNoise n × BranchContext n :=
  (branchEquiv n).trans (match d with
    | ⟨0, _⟩ =>
      { toFun := fun w ↦ (w.2.1, (w.1, w.2.2))
        invFun := fun w ↦ (w.2.1, (w.1, w.2.2))
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    | ⟨1, _⟩ =>
      { toFun := fun w ↦ (w.2.2.1, (w.1, (w.2.1, w.2.2.2)))
        invFun := fun w ↦ (w.2.1, (w.2.2.1, (w.1, w.2.2.2)))
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    | ⟨2, _⟩ =>
      { toFun := fun w ↦ (w.2.2.2, (w.1, (w.2.1, w.2.2.1)))
        invFun := fun w ↦ (w.2.1, (w.2.2.1, (w.2.2.2, w.1)))
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl })

def branchRoot (d : Fin 3) (s : ℤ) (b : Bool) : ℤ :=
  if d = 2 then spin b else s

def branchBefore (n : ℕ) (d : Fin 3) (s : ℤ) (c : BranchContext n) : List ℤ :=
  match d with
  | ⟨0, _⟩ => []
  | ⟨1, _⟩ => leaves n s c.2.1
  | ⟨2, _⟩ => leaves n s c.2.1 ++ leaves n s c.2.2

def branchAfter (n : ℕ) (d : Fin 3) (s : ℤ) (c : BranchContext n) : List ℤ :=
  match d with
  | ⟨0, _⟩ => leaves n s c.2.1 ++ leaves n (spin c.1) c.2.2
  | ⟨1, _⟩ => leaves n (spin c.1) c.2.2
  | ⟨2, _⟩ => []

lemma leaves_branchAt (n : ℕ) (d : Fin 3) (s : ℤ) (w : TreeNoise n)
    (c : BranchContext n) :
    leaves (n+1) s ((branchAt n d).symm (w,c)) =
      branchBefore n d s c ++ leaves n (branchRoot d s c.1) w ++ branchAfter n d s c := by
  fin_cases d <;> simp [branchAt, branchEquiv, branchRoot, branchBefore, branchAfter,
    leaves, List.append_assoc]

lemma length_branchBefore (n : ℕ) (d : Fin 3) (s : ℤ) (c : BranchContext n) :
    (branchBefore n d s c).length = d.val * 3^n := by
  fin_cases d <;> simp [branchBefore, two_mul]

def BlockContext (q : ℕ) : ℕ → Type
  | 0 => Unit
  | h+1 => BranchContext (q+h) × BlockContext q h

instance blockContextFintype (q : ℕ) : ∀ h, Fintype (BlockContext q h)
  | 0 => inferInstanceAs (Fintype Unit)
  | h+1 => by
    let : Fintype (BlockContext q h) := blockContextFintype q h
    exact inferInstanceAs (Fintype (BranchContext (q+h) × BlockContext q h))

instance blockContextNonempty (q : ℕ) : ∀ h, Nonempty (BlockContext q h)
  | 0 => ⟨()⟩
  | h+1 => by
    let : Nonempty (BlockContext q h) := blockContextNonempty q h
    exact inferInstanceAs (Nonempty (BranchContext (q+h) × BlockContext q h))

private def rotateProd (A B C : Type*) : (A × B) × C ≃ A × (C × B) where
  toFun w := (w.1.1, (w.2, w.1.2))
  invFun w := ((w.1,w.2.2),w.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

def extractNoise (q : ℕ) : (h : ℕ) → (Fin h → Fin 3) →
    TreeNoise (q+h) ≃ TreeNoise q × BlockContext q h
  | 0, _ =>
      { toFun := fun w ↦ (w, ())
        invFun := Prod.fst
        left_inv := fun _ ↦ rfl
        right_inv := fun w ↦ by rcases w with ⟨w,⟨⟩⟩; rfl }
  | h+1, a => (branchAt (q+h) (a 0)).trans
      ((Equiv.prodCongr (extractNoise q h (fun i ↦ a i.succ)) (Equiv.refl _)).trans
        (rotateProd _ _ _))

def blockRoot (q : ℕ) : (h : ℕ) → (Fin h → Fin 3) → ℤ → BlockContext q h → ℤ
  | 0, _, s, _ => s
  | h+1, a, s, c => blockRoot q h (fun i ↦ a i.succ) (branchRoot (a 0) s c.1.1) c.2

def blockBefore (q : ℕ) : (h : ℕ) → (Fin h → Fin 3) → ℤ → BlockContext q h → List ℤ
  | 0, _, _, _ => []
  | h+1, a, s, c => branchBefore (q+h) (a 0) s c.1 ++
      blockBefore q h (fun i ↦ a i.succ) (branchRoot (a 0) s c.1.1) c.2

def blockAfter (q : ℕ) : (h : ℕ) → (Fin h → Fin 3) → ℤ → BlockContext q h → List ℤ
  | 0, _, _, _ => []
  | h+1, a, s, c => blockAfter q h (fun i ↦ a i.succ) (branchRoot (a 0) s c.1.1) c.2 ++
      branchAfter (q+h) (a 0) s c.1

lemma leaves_extractNoise (q h : ℕ) (a : Fin h → Fin 3) (s : ℤ) (w : TreeNoise q)
    (c : BlockContext q h) :
    leaves (q+h) s ((extractNoise q h a).symm (w,c)) =
      blockBefore q h a s c ++ leaves q (blockRoot q h a s c) w ++ blockAfter q h a s c := by
  induction h generalizing s with
  | zero => simp [extractNoise, blockBefore, blockRoot, blockAfter]
  | succ h ih =>
    change leaves (q+h+1) s ((branchAt (q+h) (a 0)).symm
      ((extractNoise q h (fun i ↦ a i.succ)).symm (w,c.2), c.1)) = _
    rw [leaves_branchAt, ih]
    simp only [blockBefore, blockRoot, blockAfter, List.append_assoc]

def addressIndex : (h : ℕ) → (Fin h → Fin 3) → ℕ
  | 0, _ => 0
  | h+1, a => (a 0).val * 3^h + addressIndex h (fun i ↦ a i.succ)

lemma length_blockBefore (q h : ℕ) (a : Fin h → Fin 3) (s : ℤ) (c : BlockContext q h) :
    (blockBefore q h a s c).length = addressIndex h a * 3^q := by
  induction h generalizing s with
  | zero => simp [blockBefore, addressIndex]
  | succ h ih =>
    simp only [blockBefore, List.length_append, length_branchBefore, ih, addressIndex, pow_add]
    ring

lemma uniform_equiv {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (e : A ≃ B) : PMF.uniformOfFintype A = (PMF.uniformOfFintype B).map e.symm := by
  classical
  ext a
  rw [PMF.map_apply, tsum_eq_single (e a)]
  · simp [PMF.uniformOfFintype_apply, Fintype.card_congr e]
  · intro b hb
    have h : a ≠ e.symm b := fun h ↦ hb ((congrArg e h).trans (e.apply_symm_apply b)).symm
    simp [h]

lemma pair_map_apply {A B C : Type*} [DecidableEq B] (p : PMF A) (b : B) (f : A → C) (y : B) (z : C) :
    (p.map (fun x ↦ (b, f x))) (y,z) = if y = b then (p.map f) z else 0 := by
  classical
  by_cases h : y = b
  · simp [PMF.map_apply, Prod.mk.injEq, h]
  · simp [PMF.map_apply, Prod.mk.injEq, h]

lemma conditional_atom {A B C : Type*} (p : PMF A) (q : B → PMF C)
    (c : A → B) (f : A → C → ℤ) (a : ℝ≥0∞)
    (ha : ∀ w z, ((q (c w)).map (f w)) z ≤ a) (H : B) (z : ℤ) :
    (p.bind (fun w ↦ (q (c w)).map (fun x ↦ (c w, f w x)))) (H,z) ≤
      a * (p.map c) H := by
  classical
  rw [PMF.bind_apply, PMF.map_apply, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro w
  rw [pair_map_apply]
  split_ifs with h
  · simpa [mul_comm] using mul_le_mul_right (ha w z) (p w)
  · simp

lemma addressIndex_lt (h : ℕ) (a : Fin h → Fin 3) : addressIndex h a < 3^h := by
  induction h with
  | zero => simp [addressIndex]
  | succ h ih =>
    have hd := (a 0).isLt
    rw [addressIndex, pow_succ]
    have := ih (fun i ↦ a i.succ)
    nlinarith

lemma addressIndex_surjective (h : ℕ) (b : ℕ) (hb : b < 3^h) :
    ∃ a : Fin h → Fin 3, addressIndex h a = b := by
  induction h generalizing b with
  | zero =>
    have : b = 0 := by simpa using hb
    exact ⟨Fin.elim0, this.symm⟩
  | succ h ih =>
    have hp : 0 < 3^h := pow_pos (by omega) _
    have hd : b / 3^h < 3 := (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [pow_succ, mul_comm] using hb)
    obtain ⟨a, ha⟩ := ih (b % 3^h) (Nat.mod_lt _ hp)
    refine ⟨Fin.cons ⟨b / 3^h, hd⟩ a, ?_⟩
    simp only [addressIndex, Fin.cons_zero, Fin.cons_succ, ha]
    simpa [mul_comm] using Nat.div_add_mod b (3^h)

lemma take_sum_block (l b r : List ℤ) (v : ℕ) (hv : l.length + b.length ≤ v) :
    ((l ++ b ++ r).take v).sum = b.sum +
      (l.sum + (r.take (v - (l.length + b.length))).sum) := by
  rw [List.take_append, List.take_of_length_le (by simpa using hv), List.sum_append,
    List.sum_append, List.length_append]
  ring

def walk (m : ℕ) (w : TreeNoise m) (j : ℕ) : ℤ := (leaves m 1 w |>.take j).sum

def incrementHistory (m u : ℕ) (w : TreeNoise m) : List ℤ := (leaves m 1 w).take u

theorem aligned_prediction (q h : ℕ) (b u v : ℕ) (hb : b < 3^h)
    (hu : u ≤ b * 3^q) (hv : (b+1) * 3^q ≤ v) (H : List ℤ) (x : ℤ) :
    ((PMF.uniformOfFintype (TreeNoise (q+h))).map
      (fun w ↦ (incrementHistory (q+h) u w, walk (q+h) w v))) (H,x) ≤
    ((2 : ℝ≥0∞)^q)⁻¹ *
      ((PMF.uniformOfFintype (TreeNoise (q+h))).map (incrementHistory (q+h) u)) H := by
  classical
  obtain ⟨a, ha⟩ := addressIndex_surjective h b hb
  let pre (c : BlockContext q h) := blockBefore q h a 1 c
  let post (c : BlockContext q h) := blockAfter q h a 1 c
  let root (c : BlockContext q h) := blockRoot q h a 1 c
  let hist (c : BlockContext q h) := (pre c).take u
  let shift (c : BlockContext q h) := (pre c).sum + (post c |>.take (v - (b+1)*3^q)).sum
  have hp (c : BlockContext q h) : (pre c).length = b * 3^q := by
    simp [pre, length_blockBefore, ha]
  have hhist (w : TreeNoise q) (c : BlockContext q h) :
      incrementHistory (q+h) u ((extractNoise q h a).symm (w,c)) = hist c := by
    simp only [incrementHistory, leaves_extractNoise, List.append_assoc]
    exact List.take_append_of_le_length (by change u ≤ (pre c).length; rw [hp]; exact hu)
  have hwalk (w : TreeNoise q) (c : BlockContext q h) :
      walk (q+h) ((extractNoise q h a).symm (w,c)) v = (leaves q (root c) w).sum + shift c := by
    rw [walk, leaves_extractNoise, take_sum_block]
    · simp only [root, shift, pre, post, length_blockBefore, ha, length_leaves, add_mul, one_mul]
    · change (pre c).length + (leaves q (root c) w).length ≤ v
      rw [hp, length_leaves]
      simpa [add_mul] using hv
  rw [uniform_equiv (extractNoise q h a)]
  simp only [PMF.map_comp]
  rw [uniform_product]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, hhist, hwalk]
  have hr : (PMF.uniformOfFintype (BlockContext q h)).bind
      (fun c ↦ (PMF.uniformOfFintype (TreeNoise q)).map (fun _ ↦ hist c)) =
      (PMF.uniformOfFintype (BlockContext q h)).map hist := by
    change (PMF.uniformOfFintype (BlockContext q h)).bind
      (fun c ↦ (PMF.uniformOfFintype (TreeNoise q)).map (Function.const _ (hist c))) = _
    simp only [PMF.map_const]
    rfl
  rw [hr]

  rw [PMF.bind_apply, PMF.map_apply, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro c
  rw [pair_map_apply]
  split_ifs with hc
  · have hh : ((PMF.uniformOfFintype (TreeNoise q)).map
        (fun w ↦ (leaves q (root c) w).sum + shift c)) x ≤ ((2:ℝ≥0∞)^q)⁻¹ := by
      change ((PMF.uniformOfFintype (TreeNoise q)).map
        ((fun y ↦ y + shift c) ∘ (fun w ↦ (leaves q (root c) w).sum))) x ≤ _
      rw [← PMF.map_comp]
      exact pmf_map_injective_atom_le _ _ (fun _ _ e ↦ add_right_cancel e) _ _
        (leaf_sum_atom q (root c))
    simpa [mul_comm] using mul_le_mul_right hh ((PMF.uniformOfFintype (BlockContext q h)) c)
  · simp

end HardSphere.Lattice
end

end OAI
