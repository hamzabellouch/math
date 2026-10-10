import OAI.GroupTheory.BooneHigman.BinaryCategory
import OAI.GroupTheory.BooneHigman.AdjacentPermutations

namespace OAI

noncomputable section

/-!
Binary combs, folds, permutations, and coherent exchanges.
-/

namespace FiniteAlgebraicEnvelopes.BinaryGroupCategory

section
universe u
variable {H : Type u} [Group H] (d : Data H) (q : SymmetryData d)

def left : H →* H where
  toFun g := d.tensor (g,1)
  map_one' := map_one d.tensor
  map_mul' g h := by simpa only [Prod.mk_mul_mk,mul_one] using d.tensor.map_mul (g,1) (h,1)
def right : H →* H where
  toFun g := d.tensor (1,g)
  map_one' := map_one d.tensor
  map_mul' g h := by simpa only [Prod.mk_mul_mk,mul_one] using d.tensor.map_mul (1,g) (1,h)

lemma left_right (g h : H) : Commute (left d g) (right d h) := by
  change d.tensor (g,1)*d.tensor (1,h)=d.tensor (1,h)*d.tensor (g,1)
  rw [← map_mul,← map_mul]
  simp only [Prod.mk_mul_mk,one_mul,mul_one]

lemma assoc_LL (g : H) : d.a * left d g * d.a⁻¹ = left d (left d g) := by
  change d.a*d.tensor (g,1)*d.a⁻¹=d.tensor (d.tensor (g,1),1)
  simpa only [show d.tensor (1,1)=1 from map_one d.tensor] using d.naturality g 1 1
lemma assoc_LR (g : H) : d.a * right d (left d g) * d.a⁻¹ = left d (right d g) :=
  d.naturality 1 g 1
lemma assoc_RR (g : H) : d.a * right d (right d g) * d.a⁻¹ = right d g := by
  change d.a*d.tensor (1,d.tensor (1,g))*d.a⁻¹=d.tensor (1,g)
  simpa only [show d.tensor (1,1)=1 from map_one d.tensor] using d.naturality 1 1 g

/-- The first adjacent swap on a right-associated comb with at least three leaves. -/
def combHead : H := d.a⁻¹*left d q.c*d.a

lemma combHead_square : combHead d q * combHead d q = 1 := by
  have h : left d q.c * left d q.c = 1 := by rw [← map_mul,q.square,map_one]
  dsimp only [combHead]
  calc
    _=d.a⁻¹*(left d q.c*left d q.c)*d.a := by group
    _=1 := by rw [h,mul_one,inv_mul_cancel]

lemma combHead_distant (g : H) : Commute (combHead d q) (right d (right d g)) := by
  have ha := assoc_RR d g
  have hb : right d (right d g) = d.a⁻¹ * right d g * d.a := by
    calc
      _ = d.a⁻¹ * (d.a * right d (right d g) * d.a⁻¹) * d.a := by group
      _ = _ := by rw [ha]
  rw [hb,combHead]
  simpa only [inv_inv] using (left_right d q.c g).conj d.a⁻¹

lemma combHead_braid_last :
    combHead d q * right d q.c * combHead d q =
      right d q.c * combHead d q * right d q.c := by
  have h := adjacent_braid d q
  dsimp only [firstSwap,secondSwap] at h
  change left d q.c * (d.a * right d q.c * d.a⁻¹) * left d q.c =
    (d.a * right d q.c * d.a⁻¹) * left d q.c * (d.a * right d q.c * d.a⁻¹) at h
  have hh := congrArg (fun z : H => d.a⁻¹*z*d.a) h
  dsimp only [combHead]
  convert hh using 1 <;> group

lemma combHead_conj_first :
    (d.a*d.a) * combHead d q * (d.a*d.a)⁻¹ = left d (firstSwap d q) := by
  dsimp only [combHead,firstSwap]
  calc
    _=d.a * left d q.c * d.a⁻¹ := by group
    _=_ := assoc_LL d q.c

lemma combHead_conj_second :
    (d.a*d.a) * right d (combHead d q) * (d.a*d.a)⁻¹ = left d (secondSwap d q) := by
  have hp : d.a*d.a=left d d.a*d.a*right d d.a := d.pentagon
  rw [hp,combHead,map_mul,map_mul,map_inv]
  calc
    _=left d d.a * (d.a * right d (left d q.c) * d.a⁻¹) * (left d d.a)⁻¹ := by group
    _=left d d.a * left d (right d q.c) * (left d d.a)⁻¹ := by rw [assoc_LR]
    _=_ := by rw [← map_inv,← map_mul,← map_mul]; rfl

lemma combHead_braid :
    combHead d q * right d (combHead d q) * combHead d q =
      right d (combHead d q) * combHead d q * right d (combHead d q) := by
  apply (MulAut.conj (d.a*d.a)).injective
  change (d.a*d.a) * (_*_*_) * (d.a*d.a)⁻¹ = (d.a*d.a) * (_*_*_) * (d.a*d.a)⁻¹
  have hh (g h k : H) : (d.a*d.a) * (g*h*k) * (d.a*d.a)⁻¹ =
      ((d.a*d.a)*g*(d.a*d.a)⁻¹) * ((d.a*d.a)*h*(d.a*d.a)⁻¹) *
      ((d.a*d.a)*k*(d.a*d.a)⁻¹) := by group
  rw [hh,hh,combHead_conj_first,combHead_conj_second,← map_mul,← map_mul,
    ← map_mul,← map_mul,adjacent_braid]

/-- Whisker an endomorphism past `n` initial leaves of a right comb. -/
def rightPower : ℕ → H →* H
  | 0 => MonoidHom.id H
  | n+1 => (right d).comp (rightPower n)

@[simp] lemma rightPower_zero (g : H) : rightPower d 0 g = g := rfl
@[simp] lemma rightPower_succ (n : ℕ) (g : H) :
    rightPower d (n+1) g = right d (rightPower d n g) := rfl
lemma rightPower_add (m n : ℕ) (g : H) :
    rightPower d (m+n) g = rightPower d m (rightPower d n g) := by
  induction m with
  | zero => simp only [Nat.zero_add,rightPower_zero]
  | succ m ih => rw [Nat.succ_add,rightPower_succ,rightPower_succ,ih]
lemma rightPower_succ' (n : ℕ) (g : H) :
    rightPower d (n+1) g = rightPower d n (right d g) := by
  rw [rightPower_add]; rfl

/-- `n` adjacent generators acting on the `n+1` leaf right comb. -/
def combSwap (n i : ℕ) : H :=
  if i < n then rightPower d i (if i+1=n then q.c else combHead d q) else 1

lemma combSwap_last (n : ℕ) : combSwap d q (n+1) n = rightPower d n q.c := by
  simp only [combSwap,Nat.lt_succ_self,↓reduceIte]
lemma combSwap_internal {n i : ℕ} (hi : i+1<n) :
    combSwap d q n i = rightPower d i (combHead d q) := by
  simp only [combSwap,show i<n by omega,show ¬ i+1=n by omega,↓reduceIte]

lemma combSwap_square {n i : ℕ} (hi : i<n) : combSwap d q n i * combSwap d q n i=1 := by
  rw [combSwap,ite_eq_left hi]
  split_ifs <;> rw [← map_mul]
  · rw [q.square,map_one]
  · rw [combHead_square,map_one]

lemma combSwap_braid {n i : ℕ} (hi : i+1<n) :
    combSwap d q n (i+1) * combSwap d q n i * combSwap d q n (i+1) =
      combSwap d q n i * combSwap d q n (i+1) * combSwap d q n i := by
  rw [combSwap_internal d q hi]
  by_cases ht : i+2=n
  · subst n
    rw [show i+2=i+1+1 from rfl,combSwap_last,rightPower_succ',← map_mul,← map_mul,
      ← map_mul,← map_mul,combHead_braid_last]
  · rw [combSwap_internal d q (by omega),rightPower_succ',← map_mul,← map_mul,
      ← map_mul,← map_mul,combHead_braid]

lemma combSwap_distant {n i j : ℕ} (hij : i+1<j) (hj : j<n) :
    Commute (combSwap d q n i) (combSwap d q n j) := by
  rw [combSwap_internal d q (by omega),combSwap,ite_eq_left hj]
  let z := if j+1=n then q.c else combHead d q
  change Commute (rightPower d i (combHead d q)) (rightPower d j z)
  have hn : j=i+(2+(j-i-2)) := by omega
  rw [hn,rightPower_add,show 2+(j-i-2)=(j-i-2)+2 by omega,
    rightPower_succ,rightPower_succ]
  exact (combHead_distant d q (rightPower d (j-i-2) z)).map (rightPower d i)

lemma combSwap_relations (n : ℕ) : Adjacent.Relations (combSwap d q n) n :=
  ⟨fun _ hi => combSwap_square d q hi,
   fun _ hi => combSwap_braid d q hi,
   fun _ _ hij hj => combSwap_distant d q hij hj⟩

/-- The literal symmetric-group action on every nonempty right comb. -/
def combPermutation (n : ℕ) : Equiv.Perm (Fin (n+1)) →* H :=
  Adjacent.permutationLift (combSwap_relations d q n)

@[simp] lemma combPermutation_swap (n : ℕ) (i : Fin n) :
    combPermutation d q n (Equiv.swap i.castSucc i.succ) = combSwap d q n i :=
  Adjacent.permutationLift_swap _ i

end

section
universe u
variable {H : Type u} [Group H] (d : Data H)

/-- Flatten `(comb (m+1), comb (n+1))` to the right comb. As every nonempty
object is positive, the value only depends on the size of the left block. -/
def merge : ℕ → H
  | 0 => 1
  | m+1 => right d (merge m) * d.a⁻¹

@[simp] lemma merge_zero : merge d 0=1 := rfl
@[simp] lemma merge_succ (m : ℕ) : merge d (m+1)=right d (merge d m)*d.a⁻¹ := rfl

lemma merge_coherence (m n : ℕ) :
    merge d (m+n+1) * left d (merge d m) = merge d m * right d (merge d n) * d.a⁻¹ := by
  induction m with
  | zero => simp only [Nat.zero_add,merge_zero,map_one,mul_one,one_mul,merge_succ]
  | succ m ih =>
    rw [Nat.succ_add]
    change (right d (merge d (m+n+1))*d.a⁻¹) * left d (right d (merge d m)*d.a⁻¹) =
      (right d (merge d m)*d.a⁻¹) * right d (merge d n)*d.a⁻¹
    rw [map_mul,map_inv]
    have ht : d.a⁻¹*left d (right d (merge d m))=
        right d (left d (merge d m))*d.a⁻¹ := by
      rw [← assoc_LR d (merge d m)]; group
    have hp : (right d d.a)⁻¹*d.a⁻¹*(left d d.a)⁻¹=d.a⁻¹*d.a⁻¹ := by
      simpa only [mul_inv_rev,left,right,MonoidHom.coe_mk,OneHom.coe_mk,mul_assoc] using
        (congrArg (fun z : H=>z⁻¹) d.pentagon).symm
    calc
      _=right d (merge d (m+n+1)) * right d (left d (merge d m)) *
          d.a⁻¹*(left d d.a)⁻¹ := by
        calc
          _=right d (merge d (m+n+1)) * (d.a⁻¹*left d (right d (merge d m))) *
            (left d d.a)⁻¹ := by group
          _=_ := by rw [ht]; group
      _=right d (merge d m * right d (merge d n) * d.a⁻¹) * d.a⁻¹*(left d d.a)⁻¹ := by
        rw [← map_mul,ih]
      _=right d (merge d m) * right d (right d (merge d n)) * (d.a⁻¹*d.a⁻¹) := by
        rw [map_mul,map_mul,map_inv]; rw [← hp]; group
      _=right d (merge d m) * d.a⁻¹ * right d (merge d n) * d.a⁻¹ := by
        have hh := assoc_RR d (merge d n)
        calc
          _=right d (merge d m) * d.a⁻¹ *
             (d.a*right d (right d (merge d n))*d.a⁻¹) * d.a⁻¹ := by group
          _=_ := by rw [hh]

def blockMap (m p : ℕ) (f g : H) : H :=
  merge d p * d.tensor (f,g) * (merge d m)⁻¹

@[simp] lemma blockMap_id (m : ℕ) : blockMap d m m 1 1=1 := by
  rw [blockMap,show d.tensor (1,1)=1 from map_one d.tensor,mul_one,mul_inv_cancel]

lemma blockMap_comp (m p q : ℕ) (f₁ f₂ g₁ g₂ : H) :
    blockMap d p q f₂ g₂ * blockMap d m p f₁ g₁ = blockMap d m q (f₂*f₁) (g₂*g₁) := by
  dsimp only [blockMap]
  rw [show d.tensor (f₂*f₁,g₂*g₁)=d.tensor (f₂,g₂)*d.tensor (f₁,g₁) from
    d.tensor.map_mul (f₂,g₂) (f₁,g₁)]
  group

lemma blockMap_assoc (m n p q : ℕ) (f g h : H) :
    blockMap d (m+n+1) (p+q+1) (blockMap d m p f g) h =
      blockMap d m p f (blockMap d n q g h) := by
  have ha (a b c : H) : d.tensor (a*b*c,h)=
      left d a * d.tensor (b,h) * left d c := by
    change d.tensor (a*b*c,h)=d.tensor (a,1)*d.tensor (b,h)*d.tensor (c,1)
    rw [← map_mul,← map_mul]; simp only [Prod.mk_mul_mk,one_mul,mul_one]
  have hb (a b c : H) : d.tensor (f,a*b*c)=
      right d a * d.tensor (f,b) * right d c := by
    change d.tensor (f,a*b*c)=d.tensor (1,a)*d.tensor (f,b)*d.tensor (1,c)
    rw [← map_mul,← map_mul]; simp only [Prod.mk_mul_mk,one_mul,mul_one]
  dsimp only [blockMap]
  rw [ha,hb,map_inv,map_inv]
  have hs := merge_coherence d m n
  have ht := merge_coherence d p q
  have hn := d.naturality f g h
  calc
    _=(merge d (p+q+1)*left d (merge d p)) * d.tensor (d.tensor (f,g),h) *
        (merge d (m+n+1)*left d (merge d m))⁻¹ := by group
    _=(merge d p*right d (merge d q)*d.a⁻¹) *
        (d.a*d.tensor (f,d.tensor (g,h))*d.a⁻¹) *
        (merge d m*right d (merge d n)*d.a⁻¹)⁻¹ := by rw [ht,hs,hn]
    _=_ := by group

end

universe u
variable {H : Type u} [Group H] (d : Data H) (q : SymmetryData d)

/-- Tensor a nonempty string of `n+1` labels in the right comb. -/
def combFold : ℕ → (ℕ → H) → H
  | 0,f => f 0
  | n+1,f => d.tensor (f 0, combFold n (fun i=>f (i+1)))

lemma combFold_congr {n : ℕ} {f g : ℕ → H} (h : ∀ i,i≤n → f i=g i) :
    combFold d n f=combFold d n g := by
  induction n generalizing f g with
  | zero => exact h 0 le_rfl
  | succ n ih => exact congrArg (d.tensor) (Prod.ext (h 0 (by omega))
      (ih (fun i hi=>h (i+1) (by omega))))

lemma combHead_naturality (g h k : H) :
    combHead d q * d.tensor (g,d.tensor (h,k)) * (combHead d q)⁻¹ =
      d.tensor (h,d.tensor (g,k)) := by
  have hn := firstSwap_naturality d q g h k
  have h₁ := d.naturality g h k
  have h₂ := d.naturality h g k
  dsimp only [firstSwap] at hn
  rw [← h₁,← h₂] at hn
  have hh := congrArg (fun z:H=>d.a⁻¹*z*d.a) hn
  dsimp only [combHead,left,MonoidHom.coe_mk,OneHom.coe_mk]
  convert hh using 1 <;> group

lemma combSwap_succ {n i : ℕ} (hi : i<n) :
    combSwap d q (n+1) (i+1) = right d (combSwap d q n i) := by
  simp only [combSwap,show i+1<n+1 by omega,hi,↓reduceIte,
    Nat.add_right_cancel_iff,rightPower_succ]

lemma natSwap_succ_apply (i j : ℕ) :
    Adjacent.natSwap (i+1) (j+1)=Adjacent.natSwap i j+1 := by
  simp only [Adjacent.natSwap,Equiv.swap_apply_def]
  split_ifs <;> omega

lemma combSwap_fold {n i : ℕ} (hi : i<n) (f : ℕ → H) :
    combSwap d q n i * combFold d n f * (combSwap d q n i)⁻¹ =
      combFold d n (fun j=>f (Adjacent.natSwap i j)) := by
  induction n generalizing i f with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero =>
      cases n with
      | zero =>
        simpa only [combSwap_last,rightPower_zero,combFold,Adjacent.natSwap,
          Equiv.swap_apply_left,Equiv.swap_apply_right] using q.naturality (f 0) (f 1)
      | succ n =>
        rw [combSwap_internal d q (by omega),rightPower_zero]
        have ht (j : ℕ) : Equiv.swap 0 1 (j+1+1)=j+1+1 := by
          apply Equiv.swap_apply_of_ne_of_ne <;> omega
        simpa only [combFold,Adjacent.natSwap,Equiv.swap_apply_left,Equiv.swap_apply_right,ht] using
          combHead_naturality d q (f 0) (f 1) (combFold d n (fun j=>f (j+1+1)))
    | succ i =>
      rw [combSwap_succ d q (by omega),combFold,combFold]
      have hh := ih (show i<n by omega) (fun j=>f (j+1))
      have he : Adjacent.natSwap (i+1) 0=0 := by
        apply Equiv.swap_apply_of_ne_of_ne <;> omega
      rw [he]
      change d.tensor (1,combSwap d q n i)*d.tensor (f 0,combFold d n (fun j=>f (j+1)))*
        (d.tensor (1,combSwap d q n i))⁻¹ = _
      rw [← map_inv,← map_mul,← map_mul]
      simp only [Prod.mk_mul_mk,Prod.inv_mk,inv_one,one_mul,mul_one,hh,natSwap_succ_apply]

lemma merge_right (m : ℕ) (g : H) :
    merge d m * right d g * (merge d m)⁻¹ = rightPower d (m+1) g := by
  induction m with
  | zero => simp only [merge_zero,one_mul,mul_one,inv_one,rightPower_succ,rightPower_zero]
  | succ m ih =>
    rw [merge_succ,rightPower_succ]
    have ha : d.a⁻¹ * right d g * d.a = right d (right d g) := by
      calc
        _ = d.a⁻¹ * (d.a * right d (right d g) * d.a⁻¹) * d.a := by rw [assoc_RR]
        _ = _ := by group
    calc
      _=right d (merge d m) * (d.a⁻¹*right d g*d.a) * (right d (merge d m))⁻¹ := by group
      _=right d (merge d m * right d g * (merge d m)⁻¹) := by
        rw [ha,map_mul,map_mul,map_inv]
      _=_ := congrArg (right d) ih

lemma merge_left_right (m : ℕ) (g : H) :
    merge d (m+1) * left d (right d g) * (merge d (m+1))⁻¹ =
      right d (merge d m * left d g * (merge d m)⁻¹) := by
  have ha : d.a⁻¹ * left d (right d g) * d.a = right d (left d g) := by
    rw [← assoc_LR d g]; group
  rw [merge_succ]
  calc
    _=right d (merge d m) * (d.a⁻¹*left d (right d g)*d.a) * (right d (merge d m))⁻¹ := by group
    _=_ := by rw [ha,map_mul,map_mul,map_inv]

lemma merge_left_head_base :
    merge d 2 * left d (combHead d q) * (merge d 2)⁻¹ = combHead d q := by
  have hM : merge d 2 = (d.a*d.a)⁻¹ * left d d.a := by
    have hp : d.a*d.a = left d d.a*d.a*right d d.a := d.pentagon
    rw [merge_succ,merge_succ,merge_zero,map_one,one_mul,map_inv,hp]
    group
  have hH := combHead_conj_first d q
  change (d.a*d.a)*combHead d q*(d.a*d.a)⁻¹=left d (left d q.c) at hH
  rw [hM,combHead,map_mul,map_mul,map_inv]
  calc
    _=(d.a*d.a)⁻¹ * left d (left d q.c) * (d.a*d.a) := by group; simp only [zpow_ofNat, pow_two, mul_assoc]
    _=_ := by rw [← hH]; dsimp only [combHead]; group

lemma merge_left_head (m : ℕ) :
    merge d (m+2) * left d (combHead d q) * (merge d (m+2))⁻¹ = combHead d q := by
  have hm : merge d (m+2)=right d (right d (merge d m))*merge d 2 := by
    simp only [merge_succ,map_mul,merge_zero,map_one,one_mul]
    group
  rw [hm]
  calc
    _=right d (right d (merge d m)) *
      (merge d 2*left d (combHead d q)*(merge d 2)⁻¹) *
      (right d (right d (merge d m)))⁻¹ := by group
    _=right d (right d (merge d m))*combHead d q*(right d (right d (merge d m)))⁻¹ := by
      rw [merge_left_head_base]
    _=combHead d q := by
      rw [← (combHead_distant d q (merge d m)).eq,mul_assoc,mul_inv_cancel,mul_one]

lemma combSwap_left {m i : ℕ} (hi : i < m) (n : ℕ) :
    merge d m * left d (combSwap d q m i) * (merge d m)⁻¹ =
      combSwap d q (m+n+1) i := by
  induction m generalizing i with
  | zero => omega
  | succ m ih =>
    cases i with
    | zero =>
      cases m with
      | zero =>
        rw [combSwap_last,rightPower_zero,merge_succ,merge_zero,map_one,one_mul,
          inv_inv,combSwap_internal d q (by omega),rightPower_zero]
        rfl
      | succ m =>
        rw [combSwap_internal d q (by omega),rightPower_zero,merge_left_head,
          combSwap_internal d q (by omega),rightPower_zero]
    | succ i =>
      rw [combSwap_succ d q (by omega),merge_left_right,ih (by omega),
        show m+1+n+1=(m+n+1)+1 by omega,combSwap_succ d q (by omega)]

lemma combSwap_shift {n i : ℕ} (hi : i<n) (m : ℕ) :
    rightPower d m (combSwap d q n i) = combSwap d q (m+n) (m+i) := by
  simp only [combSwap,hi,show m+i < m+n by omega,↓reduceIte,
    show m+i+1=m+(i+1) by omega,Nat.add_left_cancel_iff,rightPower_add]

lemma combSwap_right {n i : ℕ} (hi : i<n) (m : ℕ) :
    merge d m * right d (combSwap d q n i) * (merge d m)⁻¹ =
      combSwap d q (m+n+1) (m+1+i) := by
  rw [merge_right,combSwap_shift d q hi]
  congr 1; omega

end FiniteAlgebraicEnvelopes.BinaryGroupCategory

namespace FiniteAlgebraicEnvelopes
namespace Adjacent
lemma permutation_induction {n : ℕ} {P : Equiv.Perm (Fin (n+1)) → Prop}
    (hone : P 1) (hswap : ∀ i : Fin n, P (Equiv.swap i.castSucc i.succ))
    (hmul : ∀ p q, P p → P q → P (p*q)) (p : Equiv.Perm (Fin (n+1))) : P p := by
  have hp : p ∈ Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
  induction hp using Submonoid.closure_induction with
  | mem p hp => obtain ⟨i,rfl⟩ := hp; exact hswap i
  | one => exact hone
  | mul p q hp hq ihp ihq => exact hmul p q ihp ihq

@[simp] lemma natExtend_apply (n : ℕ) (p : Equiv.Perm (Fin n)) (i : Fin n) :
    natExtend n p i = (p i : ℕ) := by
  change Equiv.Perm.ofSubtype ((Equiv.permCongrHom Fin.equivSubtype) p) (↑(Fin.equivSubtype i)) = _
  rw [Equiv.Perm.ofSubtype_apply_coe]
  rfl

lemma natExtend_of_lt {n i : ℕ} (hi : i<n) (p : Equiv.Perm (Fin n)) :
    natExtend n p i = (p ⟨i,hi⟩ : ℕ) := natExtend_apply n p ⟨i,hi⟩
end Adjacent
namespace BinaryGroupCategory
universe u
variable {H : Type u} [Group H] (d : Data H) (q : SymmetryData d)

lemma combPermutation_fold (n : ℕ) (p : Equiv.Perm (Fin (n+1))) (f : ℕ → H) :
    combPermutation d q n p * combFold d n f * (combPermutation d q n p)⁻¹ =
      combFold d n (fun i=>f (Adjacent.natExtend (n+1) p⁻¹ i)) := by
  induction p using Adjacent.permutation_induction generalizing f with
  | hone => simp only [map_one,inv_one,one_mul,mul_one,Equiv.Perm.one_apply]
  | hswap i =>
    simpa only [combPermutation_swap,Equiv.swap_inv,Adjacent.natExtend_swap,Adjacent.natSwap,Fin.val_castSucc,Fin.val_succ] using
      combSwap_fold d q i.isLt f
  | hmul p r hp hr =>
    rw [map_mul]
    calc
      _=combPermutation d q n p *
          (combPermutation d q n r * combFold d n f * (combPermutation d q n r)⁻¹) *
          (combPermutation d q n p)⁻¹ := by group
      _=_ := by rw [hr,hp]; simp only [mul_inv_rev,map_mul,Equiv.Perm.mul_apply]

/-- The same labelled right-comb tensor with its exact finite indexing. -/
def finFold (n : ℕ) (f : Fin (n+1) → H) : H :=
  combFold d n (fun i=>if hi : i<n+1 then f ⟨i,hi⟩ else 1)

lemma finFold_nat (n : ℕ) (f : ℕ → H) :
    finFold d n (fun i=>f i) = combFold d n f := by
  apply combFold_congr
  intro i hi
  simp only [show i<n+1 by omega,↓reduceDIte]

lemma finFold_zero (f : Fin 1 → H) : finFold d 0 f=f 0 := rfl

lemma finFold_succ (n : ℕ) (f : Fin (n+2) → H) :
    finFold d (n+1) f=d.tensor (f 0,finFold d n (fun i=>f i.succ)) := by
  unfold finFold
  rw [combFold]
  congr 1
  apply Prod.ext
  · simp only [Nat.zero_lt_succ,↓reduceDIte]; rfl
  · apply combFold_congr
    intro i hi
    simp only [show i+1<n+1+1 by omega,show i<n+1 by omega,↓reduceDIte,Fin.succ]

lemma finFold_mul (n : ℕ) (f g : Fin (n+1) → H) :
    finFold d n (fun i=>f i*g i)=finFold d n f*finFold d n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [finFold_succ,finFold_succ,finFold_succ,ih,← map_mul]
    rfl

@[simp] lemma finFold_one (n : ℕ) : finFold d n (fun _=>1)=1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [finFold_succ,ih]; exact map_one d.tensor

lemma combPermutation_finFold (n : ℕ) (p : Equiv.Perm (Fin (n+1))) (f : Fin (n+1) → H) :
    combPermutation d q n p * finFold d n f * (combPermutation d q n p)⁻¹ =
      finFold d n (fun i=>f (p⁻¹ i)) := by
  unfold finFold
  rw [combPermutation_fold]
  apply combFold_congr
  intro i hi
  simp only [Adjacent.natExtend_of_lt (show i<n+1 by omega),
    (p⁻¹ ⟨i,by omega⟩).isLt,show i<n+1 by omega,↓reduceDIte]

end BinaryGroupCategory
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.BinaryGroupCategory
universe u
variable {H : Type u} [Group H] (d : Data H) (q : SymmetryData d)

/-- Consecutive indexing of two positive blocks, in predecessor-size notation. -/
def sumIndex (m n : ℕ) : Fin (m+1) ⊕ Fin (n+1) ≃ Fin (m+n+1+1) :=
  finSumFinEquiv.trans (finCongr (by omega))

@[simp] lemma sumIndex_left_val (m n : ℕ) (i : Fin (m+1)) :
    (sumIndex m n (Sum.inl i) : ℕ)=i := rfl
@[simp] lemma sumIndex_right_val (m n : ℕ) (i : Fin (n+1)) :
    (sumIndex m n (Sum.inr i) : ℕ)=m+1+i := rfl

def sumPermutation (m n : ℕ) :
    Equiv.Perm (Fin (m+1)) × Equiv.Perm (Fin (n+1)) →* Equiv.Perm (Fin (m+n+1+1)) :=
  (Equiv.permCongrHom (sumIndex m n)).toMonoidHom.comp (Equiv.Perm.sumCongrHom _ _)

lemma sumPermutation_swap_left (m n : ℕ) (i j : Fin (m+1)) :
    sumPermutation m n (Equiv.swap i j,1)=
      Equiv.swap (sumIndex m n (Sum.inl i)) (sumIndex m n (Sum.inl j)) := by
  change (Equiv.permCongrHom (sumIndex m n)) (Equiv.Perm.sumCongr (Equiv.swap i j) 1)=_
  rw [Equiv.Perm.sumCongr_swap_one]
  exact Equiv.symm_trans_swap_trans _ _ _

lemma sumPermutation_swap_right (m n : ℕ) (i j : Fin (n+1)) :
    sumPermutation m n (1,Equiv.swap i j)=
      Equiv.swap (sumIndex m n (Sum.inr i)) (sumIndex m n (Sum.inr j)) := by
  change (Equiv.permCongrHom (sumIndex m n)) (Equiv.Perm.sumCongr 1 (Equiv.swap i j))=_
  rw [Equiv.Perm.sumCongr_one_swap]
  exact Equiv.symm_trans_swap_trans _ _ _

lemma combPermutation_sum_left (m n : ℕ) (p : Equiv.Perm (Fin (m+1))) :
    combPermutation d q (m+n+1) (sumPermutation m n (p,1)) =
      merge d m * left d (combPermutation d q m p) * (merge d m)⁻¹ := by
  induction p using Adjacent.permutation_induction with
  | hone => simp only [show (1,1)= (1 : Equiv.Perm (Fin (m+1)) × Equiv.Perm (Fin (n+1))) from rfl,
      map_one,mul_one,mul_inv_cancel]
  | hswap i =>
    let j : Fin (m+n+1) := ⟨i,by omega⟩
    have hh : sumPermutation m n (Equiv.swap i.castSucc i.succ,1)=
        Equiv.swap j.castSucc j.succ := by
      rw [sumPermutation_swap_left]
      congr 1
    rw [hh,combPermutation_swap,combPermutation_swap,combSwap_left d q i.isLt]
  | hmul p r hp hr =>
    have hh : sumPermutation m n (p*r,1)=sumPermutation m n (p,1)*sumPermutation m n (r,1) :=
      (sumPermutation m n).map_mul (p,1) (r,1)
    rw [hh,map_mul,hp,hr,map_mul,map_mul]
    group

lemma combPermutation_sum_right (m n : ℕ) (p : Equiv.Perm (Fin (n+1))) :
    combPermutation d q (m+n+1) (sumPermutation m n (1,p)) =
      merge d m * right d (combPermutation d q n p) * (merge d m)⁻¹ := by
  induction p using Adjacent.permutation_induction with
  | hone => simp only [show (1,1)= (1 : Equiv.Perm (Fin (m+1)) × Equiv.Perm (Fin (n+1))) from rfl,
      map_one,mul_one,mul_inv_cancel]
  | hswap i =>
    let j : Fin (m+n+1) := ⟨m+1+i,by omega⟩
    have hh : sumPermutation m n (1,Equiv.swap i.castSucc i.succ)=
        Equiv.swap j.castSucc j.succ := by
      rw [sumPermutation_swap_right]
      congr 1
    rw [hh,combPermutation_swap,combPermutation_swap,combSwap_right d q i.isLt]
  | hmul p r hp hr =>
    have hh : sumPermutation m n (1,p*r)=sumPermutation m n (1,p)*sumPermutation m n (1,r) :=
      (sumPermutation m n).map_mul (1,p) (1,r)
    rw [hh,map_mul,hp,hr,map_mul,map_mul]
    group

lemma combPermutation_sum (m n : ℕ) (p : Equiv.Perm (Fin (m+1))) (r : Equiv.Perm (Fin (n+1))) :
    combPermutation d q (m+n+1) (sumPermutation m n (p,r)) =
      blockMap d m m (combPermutation d q m p) (combPermutation d q n r) := by
  have hh : sumPermutation m n (p,r)=sumPermutation m n (p,1)*sumPermutation m n (1,r) :=
    (sumPermutation m n).map_mul (p,1) (1,r)
  rw [hh,map_mul,combPermutation_sum_left,combPermutation_sum_right]
  dsimp only [blockMap,left,right,MonoidHom.coe_mk,OneHom.coe_mk]
  rw [show d.tensor (combPermutation d q m p,combPermutation d q n r)=
      d.tensor (combPermutation d q m p,1)*d.tensor (1,combPermutation d q n r) from
        by simpa only [Prod.mk_mul_mk,mul_one,one_mul] using map_mul d.tensor (combPermutation d q m p,1) (1,combPermutation d q n r)]
  group

lemma equiv_size {m n : ℕ} (e : Fin (m+1) ≃ Fin (n+1)) : m=n := by
  have h := Fintype.card_congr e
  simpa only [Fintype.card_fin,Nat.add_right_cancel_iff] using h

/-- The symmetric coherence value of a bijection of two positive finite ordinals.
Both sides may use different (provably equal) numeral expressions. -/
def equivVal {m n : ℕ} (e : Fin (m+1) ≃ Fin (n+1)) : H :=
  combPermutation d q m (e.trans (finCongr (congrArg (fun k=>k+1) (equiv_size e).symm)))

@[simp] lemma equivVal_same {m : ℕ} (e : Equiv.Perm (Fin (m+1))) :
    equivVal d q e=combPermutation d q m e := rfl

@[simp] lemma equivVal_refl (m : ℕ) : equivVal d q (Equiv.refl (Fin (m+1)))=1 :=
  map_one (combPermutation d q m)

@[simp] lemma equivVal_cast {m n : ℕ} (h : m=n) :
    equivVal d q (finCongr (congrArg (fun k=>k+1) h))=1 := by
  subst n
  exact equivVal_refl d q m

lemma equivVal_trans {m n k : ℕ} (e : Fin (m+1) ≃ Fin (n+1)) (f : Fin (n+1) ≃ Fin (k+1)) :
    equivVal d q (e.trans f)=equivVal d q f*equivVal d q e := by
  have hm := equiv_size e
  have hn := equiv_size f
  subst n k
  exact map_mul (combPermutation d q m) f e

@[simp] lemma equivVal_symm {m n : ℕ} (e : Fin (m+1) ≃ Fin (n+1)) :
    equivVal d q e.symm=(equivVal d q e)⁻¹ := by
  have hm := equiv_size e
  subst n
  exact map_inv (combPermutation d q m) e

def sumEquiv {m n p q : ℕ} (e : Fin (m+1) ≃ Fin (p+1)) (f : Fin (n+1) ≃ Fin (q+1)) :
    Fin (m+n+1+1) ≃ Fin (p+q+1+1) :=
  (sumIndex m n).symm.trans ((Equiv.sumCongr e f).trans (sumIndex p q))

@[simp] lemma sumEquiv_left {m n p q : ℕ} (e : Fin (m+1) ≃ Fin (p+1)) (f : Fin (n+1) ≃ Fin (q+1))
    (i : Fin (m+1)) : sumEquiv e f (sumIndex m n (Sum.inl i))=sumIndex p q (Sum.inl (e i)) := by
  simp only [sumEquiv,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.sumCongr_apply,Sum.map_inl]

@[simp] lemma sumEquiv_right {m n p q : ℕ} (e : Fin (m+1) ≃ Fin (p+1)) (f : Fin (n+1) ≃ Fin (q+1))
    (i : Fin (n+1)) : sumEquiv e f (sumIndex m n (Sum.inr i))=sumIndex p q (Sum.inr (f i)) := by
  simp only [sumEquiv,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.sumCongr_apply,Sum.map_inr]

lemma sumEquiv_self (m n : ℕ) (e : Equiv.Perm (Fin (m+1))) (f : Equiv.Perm (Fin (n+1))) :
    sumEquiv e f=sumPermutation m n (e,f) := rfl

lemma equivVal_sum {m n p r : ℕ} (e : Fin (m+1) ≃ Fin (p+1)) (f : Fin (n+1) ≃ Fin (r+1)) :
    equivVal d q (sumEquiv e f)=blockMap d m p (equivVal d q e) (equivVal d q f) := by
  have hm := equiv_size e
  have hn := equiv_size f
  subst p r
  exact combPermutation_sum d q m n e f

/-- Exchange two consecutive positive blocks. -/
def exchangeEquiv (m n : ℕ) : Fin (m+n+1+1) ≃ Fin (n+m+1+1) :=
  (sumIndex m n).symm.trans ((Equiv.sumComm _ _).trans (sumIndex n m))

@[simp] lemma exchangeEquiv_left (m n : ℕ) (i : Fin (m+1)) :
    exchangeEquiv m n (sumIndex m n (Sum.inl i))=sumIndex n m (Sum.inr i) := by
  simp only [exchangeEquiv,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.sumComm_apply,Sum.swap_inl]

@[simp] lemma exchangeEquiv_right (m n : ℕ) (i : Fin (n+1)) :
    exchangeEquiv m n (sumIndex m n (Sum.inr i))=sumIndex n m (Sum.inl i) := by
  simp only [exchangeEquiv,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.sumComm_apply,Sum.swap_inr]

end FiniteAlgebraicEnvelopes.BinaryGroupCategory

namespace FiniteAlgebraicEnvelopes
namespace Adjacent
universe u
variable {H : Type u} [Group H]
lemma descending_congr (r s : ℕ → H) (i n : ℕ) (h : ∀ j,j<n → r j=s j) :
    descending r i n=descending s i n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [descending]
    split_ifs
    · rw [h n (by omega),ih (fun j hj=>h j (by omega))]
    · rfl

lemma descending_head (r : ℕ → H) (n : ℕ) :
    descending r 0 (n+1)=descending (fun i=>r (i+1)) 0 n*r 0 := by
  induction n with
  | zero => simp only [descending,Nat.zero_le,↓reduceIte,mul_one,one_mul]
  | succ n ih =>
    rw [descending_step r (Nat.zero_le _),ih,
      descending_step (fun i=>r (i+1)) (Nat.zero_le _),mul_assoc]

lemma descending_nat_zero_apply (n k : ℕ) :
    descending natSwap 0 n k = if k=0 then n else if k≤n then k-1 else k := by
  induction n with
  | zero => simp only [descending_zero,Equiv.Perm.one_apply]; split_ifs <;> omega
  | succ n ih =>
    rw [descending_step natSwap (Nat.zero_le _),Equiv.Perm.mul_apply,ih]
    simp only [natSwap,Equiv.swap_apply_def]
    split_ifs <;> omega

lemma natExtend_descending (n i k : ℕ) (hk : k≤n) :
    natExtend (n+1) (descending (finSwap n) i k)=descending natSwap i k := by
  rw [map_descending]
  apply descending_congr
  intro j hj
  exact natExtend_finSwap (by omega)
end Adjacent
namespace BinaryGroupCategory
universe u
variable {H : Type u} [Group H] (d : Data H) (q : SymmetryData d)

lemma equivVal_transport {m n p r : ℕ} (e : Fin (m+1) ≃ Fin (n+1)) (f : Fin (p+1) ≃ Fin (r+1))
    (hm : m=p) (hn : n=r)
    (h : ∀ (i : Fin (m+1)) (j : Fin (p+1)),(i:ℕ)=(j:ℕ) → (e i : ℕ)=(f j : ℕ)) :
    equivVal d q e=equivVal d q f := by
  subst p r
  congr 1
  apply Equiv.ext
  intro i
  exact Fin.ext (h i i rfl)

lemma equivVal_order {m n : ℕ} (e : Fin (m+1) ≃ Fin (n+1))
    (h : ∀ i,(e i : ℕ)=i) : equivVal d q e=1 := by
  have he := equiv_size e
  subst n
  have hh : e=Equiv.refl _ := by apply Equiv.ext; intro i; exact Fin.ext (h i)
  rw [hh,equivVal_refl]

lemma combPermutation_finSwap (n i : ℕ) :
    combPermutation d q n (Adjacent.finSwap n i) = combSwap d q n i := by
  by_cases hi : i<n
  · rw [Adjacent.finSwap_lt hi]
    exact combPermutation_swap d q n ⟨i,hi⟩
  · simp only [Adjacent.finSwap,hi,↓reduceDIte,map_one,combSwap,↓reduceIte]

lemma combPermutation_descending (n i k : ℕ) :
    combPermutation d q n (Adjacent.descending (Adjacent.finSwap n) i k)=
      Adjacent.descending (combSwap d q n) i k := by
  rw [Adjacent.map_descending]
  congr 1
  funext j
  exact combPermutation_finSwap d q n j

lemma descending_comb_head (n : ℕ) :
    Adjacent.descending (combSwap d q (n+1)) 0 (n+1)=merge d n*q.c := by
  induction n with
  | zero => simp only [Adjacent.descending,Nat.zero_le,↓reduceIte,mul_one,combSwap_last,
      rightPower_zero,merge_zero,one_mul]
  | succ n ih =>
    rw [Adjacent.descending_head]
    have hh : Adjacent.descending (fun i=>combSwap d q (n+1+1) (i+1)) 0 (n+1)=
        right d (Adjacent.descending (combSwap d q (n+1)) 0 (n+1)) := by
      rw [Adjacent.map_descending]
      apply Adjacent.descending_congr
      intro j hj
      exact combSwap_succ d q hj
    rw [hh,ih,map_mul,combSwap_internal d q (by omega),rightPower_zero,merge_succ]
    have hx : right d q.c * combHead d q=d.a⁻¹*q.c := by
      have h := congrArg (fun z:H=>d.a⁻¹*z) q.hexagon
      change d.a⁻¹*q.c=d.a⁻¹*(d.a*right d q.c*d.a⁻¹*left d q.c*d.a) at h
      dsimp only [combHead]
      calc
        _=d.a⁻¹*(d.a*right d q.c*d.a⁻¹*left d q.c*d.a) := by group
        _=_ := h.symm
    rw [mul_assoc,hx,mul_assoc]

lemma equivVal_exchange_zero (n : ℕ) :
    equivVal d q (exchangeEquiv 0 n)=merge d n*q.c := by
  let p := Adjacent.descending (Adjacent.finSwap (n+1)) 0 (n+1)
  have hp (i : Fin (n+1+1)) :
      (p i : ℕ)=if (i:ℕ)=0 then n+1 else if (i:ℕ)≤n+1 then i-1 else i := by
    rw [← Adjacent.natExtend_apply (n+1+1) p i]
    rw [Adjacent.natExtend_descending _ _ _ le_rfl,Adjacent.descending_nat_zero_apply]
  have he : equivVal d q (exchangeEquiv 0 n)=equivVal d q p := by
    apply equivVal_transport d q _ _ (by omega) (by omega)
    intro i j hij
    obtain ⟨k,rfl⟩ := (sumIndex 0 n).surjective i
    cases k with
    | inl k =>
      rw [exchangeEquiv_left,sumIndex_right_val,hp]
      have hk : (k:ℕ)=0 := by omega
      simp only [sumIndex_left_val] at hij
      simp only [show (j:ℕ)=0 by omega,↓reduceIte,hk]
    | inr k =>
      rw [exchangeEquiv_right,sumIndex_left_val,hp]
      simp only [sumIndex_right_val] at hij
      simp only [show ¬ (j:ℕ)=0 by omega,show (j:ℕ)≤n+1 by omega,↓reduceIte]
      omega
  rw [he,equivVal_same,combPermutation_descending,descending_comb_head]

end BinaryGroupCategory
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.BinaryGroupCategory
universe u
variable {H : Type u} [Group H] (d : Data H) (q : SymmetryData d)

lemma exchangeEquiv_val (m n : ℕ) (i : Fin (m+n+1+1)) :
    (exchangeEquiv m n i : ℕ)=if (i:ℕ)< m+1 then n+1+i else i-(m+1) := by
  obtain ⟨j,rfl⟩ := (sumIndex m n).surjective i
  cases j with
  | inl j => simp only [exchangeEquiv_left,sumIndex_left_val,sumIndex_right_val,j.isLt,↓reduceIte]
  | inr j => simp only [exchangeEquiv_right,sumIndex_left_val,sumIndex_right_val,
      show ¬ m+1+(j:ℕ)< m+1 by omega,↓reduceIte,Nat.add_sub_cancel_left]

lemma sumEquiv_valWith {m n p r : ℕ} (e : Fin (m+1) ≃ Fin (p+1)) (f : Fin (n+1) ≃ Fin (r+1))
    (E F : ℕ → ℕ) (he : ∀ i,(e i : ℕ)=E i) (hf : ∀ i,(f i : ℕ)=F i)
    (i : Fin (m+n+1+1)) :
    (sumEquiv e f i : ℕ)=if (i:ℕ)< m+1 then E i else p+1+F (i-(m+1)) := by
  obtain ⟨j,rfl⟩ := (sumIndex m n).surjective i
  cases j with
  | inl j => simp only [sumEquiv_left,sumIndex_left_val,he,j.isLt,↓reduceIte]
  | inr j => simp only [sumEquiv_right,sumIndex_right_val,hf,
      show ¬ m+1+(j:ℕ)< m+1 by omega,↓reduceIte,Nat.add_sub_cancel_left]

lemma merge_left_merge (n : ℕ) : merge d (n+1)*left d (merge d n)=merge d n*d.a⁻¹ := by
  simpa only [Nat.add_zero,merge_zero,map_one,mul_one] using merge_coherence d n 0

lemma exchange_scalar_step (m n : ℕ) :
    blockMap d (n+1) (n+1) (merge d n*q.c) 1 *
      right d (merge d n*q.c*(merge d m)⁻¹) =
        merge d n*q.c*(merge d (m+1))⁻¹ := by
  have hx : d.a⁻¹*left d q.c*d.a*right d q.c=q.c*d.a := by
    have h := hexagon_equation_reverse d q
    change d.a*q.c*d.a=left d q.c*d.a*right d q.c at h
    calc
      _=d.a⁻¹*(left d q.c*d.a*right d q.c) := by group
      _=_ := by rw [← h]; group
  change merge d (n+1)*left d (merge d n*q.c)*(merge d (n+1))⁻¹*
    right d (merge d n*q.c*(merge d m)⁻¹)=_
  rw [map_mul,map_mul,map_mul,map_inv]
  calc
    _=(merge d (n+1)*left d (merge d n))*left d q.c*
        (merge d (n+1))⁻¹*right d (merge d n)*right d q.c*(right d (merge d m))⁻¹ := by group
    _=merge d n*(d.a⁻¹*left d q.c*d.a*right d q.c)*(right d (merge d m))⁻¹ := by
      rw [merge_left_merge,merge_succ]; group
    _=_ := by rw [hx,merge_succ]; group

lemma equivVal_exchange (m n : ℕ) :
    equivVal d q (exchangeEquiv m n)=merge d n*q.c*(merge d m)⁻¹ := by
  induction m with
  | zero => simpa only [merge_zero,inv_one,mul_one] using equivVal_exchange_zero d q n
  | succ m ih =>
    let e₁ := sumEquiv (Equiv.refl (Fin 1)) (exchangeEquiv m n)
    let c := finCongr (congrArg (fun k=>k+1) (show 0+(n+m+1)+1=(0+n+1)+m+1 by omega))
    let e₂ := sumEquiv (exchangeEquiv 0 n) (Equiv.refl (Fin (m+1)))
    let e := e₁.trans (c.trans e₂)
    have he : equivVal d q (exchangeEquiv (m+1) n)=equivVal d q e := by
      apply equivVal_transport d q _ _ (by omega) (by omega)
      intro i j hij
      rw [exchangeEquiv_val]
      have h₁ : (e₁ j : ℕ)=if (j:ℕ)<1 then (j:ℕ) else
          1+(if (j:ℕ)-1< m+1 then n+1+((j:ℕ)-1) else (j:ℕ)-1-(m+1)) := by
        exact sumEquiv_valWith (Equiv.refl (Fin 1)) (exchangeEquiv m n) id
          (fun k=>if k< m+1 then n+1+k else k-(m+1)) (fun _=>rfl)
          (exchangeEquiv_val m n) j
      have h₂ : (e₂ (c (e₁ j)) : ℕ)=if (c (e₁ j) : ℕ)< n+2 then
          (if (c (e₁ j) : ℕ)<1 then n+1+(c (e₁ j) : ℕ) else (c (e₁ j) : ℕ)-1)
        else n+2+((c (e₁ j) : ℕ)-(n+2)) := by
        simpa only [Nat.zero_add,Nat.add_zero,Nat.add_assoc,id_eq,show 1+1=2 from rfl] using
          sumEquiv_valWith (exchangeEquiv 0 n) (Equiv.refl (Fin (m+1)))
            (fun k=>if k<1 then n+1+k else k-1) id
            (exchangeEquiv_val 0 n) (fun _=>rfl) (c (e₁ j))
      change _=(e₂ (c (e₁ j)) : ℕ)
      rw [h₂]
      change _=if (e₁ j : ℕ)< n+2 then
        (if (e₁ j : ℕ)<1 then n+1+(e₁ j : ℕ) else (e₁ j : ℕ)-1)
        else n+2+((e₁ j : ℕ)-(n+2))
      rw [h₁]
      split_ifs <;> omega
    rw [he]
    change equivVal d q (e₁.trans (c.trans e₂))=_
    have hc : equivVal d q c=1 := equivVal_cast d q (by omega)
    rw [equivVal_trans,equivVal_trans,hc,mul_one]
    dsimp only [e₁,e₂]
    rw [equivVal_sum,equivVal_sum,equivVal_refl,equivVal_refl,equivVal_exchange_zero,ih]
    simp only [Nat.zero_add]
    have hb (g : H) : blockMap d 0 0 1 g=right d g := by
      simp only [blockMap,merge_zero,one_mul,inv_one,mul_one]; rfl
    rw [hb]
    exact exchange_scalar_step d q m n

lemma exchange_naturality (m n p r : ℕ) (f g : H) :
    equivVal d q (exchangeEquiv p r)*blockMap d m p f g =
      blockMap d n r g f*equivVal d q (exchangeEquiv m n) := by
  rw [equivVal_exchange,equivVal_exchange]
  dsimp only [blockMap]
  have hn := q.naturality f g
  calc
    _=merge d r*(q.c*d.tensor (f,g)*q.c⁻¹)*q.c*(merge d m)⁻¹ := by group
    _=_ := by rw [hn]; group

end FiniteAlgebraicEnvelopes.BinaryGroupCategory

end

end OAI
