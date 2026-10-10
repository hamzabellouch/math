import OAI.NumberTheory.SingleFold.Binary

namespace OAI

namespace SingleFold.Packed

def digit (B x t : ℕ) : ℕ := x/B^t%B

def pack (B k : ℕ) (f : ℕ → ℕ) : ℕ := ∑ t∈Finset.range k, f t*B^t

def Bits (x y : ℕ) : Prop := ∀ i, x/2^i%2 ≤ y/2^i%2
lemma bits_testBit (x y : ℕ) : Bits x y ↔ ∀ i, x.testBit i=true → y.testBit i=true := by
  simp only [Bits,Nat.testBit_eq_decide_div_mod_eq,decide_eq_true_eq]
  constructor
  · intro h i hi
    have := h i
    have := Nat.mod_lt (y/2^i) (by omega : 0 < 2)
    omega
  · intro h i
    have hx := Nat.mod_lt (x/2^i) (by omega : 0 < 2)
    have hy := Nat.mod_lt (y/2^i) (by omega : 0 < 2)
    by_cases hh : x/2^i%2=1
    · have := h i hh; omega
    · omega

lemma testBit_digit (w x t j : ℕ) :
    (digit (2^w) x t).testBit j=(decide (j < w) && x.testBit (w*t+j)) := by
  unfold digit
  rw [Nat.testBit_mod_two_pow,←pow_mul]
  congr 1
  simp only [Nat.testBit_eq_decide_div_mod_eq,Nat.div_div_eq_div_mul,←pow_add]

lemma bits_blocks {w : ℕ} (hw : 0 < w) (x y : ℕ) :
    Bits x y ↔ ∀t, Bits (digit (2^w) x t) (digit (2^w) y t) := by
  simp only [bits_testBit,testBit_digit,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · intro h t j hj
    exact ⟨hj.1,h _ hj.2⟩
  · intro h i hi
    have hh := h (i/w) (i%w) ⟨Nat.mod_lt i hw, by simpa [Nat.div_add_mod] using hi⟩
    simpa [Nat.div_add_mod] using hh.2

lemma digit_lt {B : ℕ} (hB : 0 < B) (x t : ℕ) : digit B x t < B := Nat.mod_lt _ hB
lemma digit_zero (B t : ℕ) : digit B 0 t=0 := by simp [digit]
lemma digit_of_lt {B x : ℕ} (hx : x < B) : digit B x 0=x := by simp [digit,Nat.mod_eq_of_lt hx]
lemma digit_high {B x t : ℕ} (hx : x < B^t) : digit B x t=0 := by simp [digit,Nat.div_eq_of_lt hx]

lemma pack_succ (B k : ℕ) (f : ℕ → ℕ) : pack B (k+1) f=pack B k f+f k*B^k := by
  simp [pack,Finset.sum_range_succ]
lemma pack_cons (B k : ℕ) (f : ℕ → ℕ) : pack B (k+1) f=f 0+B*pack B k (fun t=>f (t+1)) := by
  simp only [pack,Finset.sum_range_succ',pow_zero,mul_one,Finset.mul_sum,pow_succ]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intros; ring
lemma pack_zero (B : ℕ) (f : ℕ → ℕ) : pack B 0 f=0 := by simp [pack]
lemma pack_add (B k : ℕ) (f g : ℕ → ℕ) :
    pack B k (fun t=>f t+g t)=pack B k f+pack B k g := by simp [pack,add_mul,Finset.sum_add_distrib]
lemma pack_mul (B k c : ℕ) (f : ℕ → ℕ) :
    pack B k (fun t=>c*f t)=c*pack B k f := by simp [pack,Finset.mul_sum,mul_assoc]
lemma pack_lt {B k : ℕ} (_hB : 0 < B) {f : ℕ → ℕ} (hf : ∀ t < k,f t < B) : pack B k f < B^k := by
  induction k with
  | zero => simp [pack]
  | succ k ih =>
    rw [pack_succ,pow_succ]
    have hi := ih (fun t ht=>hf t (by omega))
    have hh := hf k (by omega)
    nlinarith only [hi,hh,pow_pos _hB k]

lemma digit_pack {B k : ℕ} (hB : 0 < B) {f : ℕ → ℕ} (hf : ∀ t < k,f t < B) (i : ℕ) :
    digit B (pack B k f) i=if i < k then f i else 0 := by
  induction k generalizing f i with
  | zero => simp [pack_zero,digit_zero]
  | succ k ih =>
    rw [pack_cons]
    cases i with
    | zero => simp [digit,Nat.mod_eq_of_lt (hf 0 (by omega))]
    | succ i =>
      rw [digit,pow_succ',←Nat.div_div_eq_div_mul,Nat.add_mul_div_left _ _ hB,
        Nat.div_eq_of_lt (hf 0 (by omega)),zero_add]
      simpa only [digit, Nat.add_lt_add_iff_right] using ih (fun t ht=>hf (t+1) (by omega)) i

lemma pack_digits {B k x : ℕ} (hB : 0 < B) (hx : x < B^k) : pack B k (digit B x)=x := by
  induction k generalizing x with
  | zero =>
    have : x=0 := by simpa using hx
    simp [this,pack_zero]
  | succ k ih =>
    rw [pack_cons]
    have he : (fun t=>digit B x (t+1))=digit B (x/B) := by
      funext t
      simp [digit,pow_succ',Nat.div_div_eq_div_mul]
    rw [he,ih]
    · simp [digit,Nat.mod_add_div]
    · rw [pow_succ'] at hx
      exact (Nat.div_lt_iff_lt_mul hB).mpr (by simpa [mul_comm] using hx)

lemma digits_ext {B k x y : ℕ} (hB : 0 < B) (hx : x < B^k) (hy : y < B^k)
    (h : ∀t < k,digit B x t=digit B y t) : x=y := by
  rw [←pack_digits hB hx,←pack_digits hB hy]
  apply Finset.sum_congr rfl
  intro t ht
  rw [h t (Finset.mem_range.mp ht)]

lemma bits_and (x y : ℕ) : Bits x y ↔ x&&&y=x := by
  rw [bits_testBit]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hx : x.testBit i  <;> simp [hx,h i]
  · intro h i hi
    have hh := congrArg (fun n=>Nat.testBit n i) h
    simpa [Nat.testBit_and,hi] using hh
lemma bits_le {x y : ℕ} (h : Bits x y) : x ≤ y := by
  rw [←(bits_and x y).mp h]
  exact Nat.and_le_right
lemma bits_refl (x : ℕ) : Bits x x := fun _=>le_rfl
lemma bits_zero_left (x : ℕ) : Bits 0 x := by intro i; simp
lemma bits_zero_right (x : ℕ) : Bits x 0 ↔ x=0 := by
  exact ⟨fun h=>Nat.eq_zero_of_le_zero (bits_le h),fun h=>h ▸ bits_refl 0⟩
lemma bits_one (x : ℕ) : Bits x 1 ↔ x ≤ 1 := by
  constructor
  · exact bits_le
  · intro h
    interval_cases x
    · exact bits_zero_left 1
    · exact bits_refl 1
lemma bits_full (x h : ℕ) : Bits x (2^h-1) ↔ x < 2^h := by
  constructor
  · intro hh
    have := bits_le hh
    have := Nat.two_pow_pos h
    omega
  · intro hh
    rw [bits_and]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow hh

def ones (B k : ℕ) : ℕ := pack B k (fun _=>1)
lemma ones_mul (B k c : ℕ) : c*ones B k=pack B k (fun _=>c) := by
  simpa [ones] using (pack_mul B k c (fun _=>1)).symm
lemma geometric {B : ℕ} (hB : 1 < B) (k : ℕ) : (B-1)*ones B k=B^k-1 := by
  induction k with
  | zero => simp [ones,pack_zero]
  | succ k ih =>
    change (B-1)*pack B (k+1) (fun _=>1)=B^(k+1)-1
    rw [pack_succ,mul_add,one_mul,pow_succ]
    change (B-1)*ones B k+(B-1)*B^k=B^k*B-1
    rw [ih]
    have hp := pow_pos (by omega : 0 < B) k
    nlinarith only [hp, hB, Nat.sub_add_cancel (by omega : 1 ≤ B), Nat.sub_add_cancel (by omega : 1 ≤ B^k), Nat.sub_add_cancel (show 1 ≤ B^k*B by exact Nat.mul_pos hp (by omega))]
lemma bits_mask {w k c x : ℕ} (hw : 0 < w) (hc : c < 2^w) :
    Bits x (c*ones (2^w) k) ↔ x < (2^w)^k ∧ ∀t < k, Bits (digit (2^w) x t) c := by
  rw [ones_mul]
  have hpos := Nat.two_pow_pos w
  have hlt := pack_lt hpos (fun _ _=>hc : ∀t < k,c < 2^w)
  constructor
  · intro h
    refine ⟨lt_of_le_of_lt (bits_le h) hlt,?_⟩
    intro t ht
    have hh := (bits_blocks hw x _).mp h t
    rwa [digit_pack hpos (fun _ _=>hc),ite_eq_left ht] at hh
  · rintro ⟨hx,h⟩
    apply (bits_blocks hw x _).mpr
    intro t
    rw [digit_pack hpos (fun _ _=>hc)]
    split_ifs with ht
    · exact h t ht
    · rw [bits_zero_right]
      apply digit_high
      exact lt_of_lt_of_le hx (Nat.pow_le_pow_right hpos (by omega))
lemma bits_ones {w k x : ℕ} (hw : 0 < w) :
    Bits x (ones (2^w) k) ↔ x < (2^w)^k ∧ ∀t < k,digit (2^w) x t ≤ 1 := by
  simpa [bits_one] using bits_mask (x:=x) (k:=k) hw (Nat.one_lt_two_pow (by omega : w≠0))

lemma pack_sum {ι : Type} [Fintype ι] (B k : ℕ) (f : ι → ℕ → ℕ) :
    pack B k (fun t=>∑i,f i t)=∑i,pack B k (f i) := by
  simp only [pack, Finset.sum_mul]
  rw [Finset.sum_comm]
lemma digit_sum {ι : Type} [Fintype ι] {B k : ℕ} (hB : 0 < B) (x : ι → ℕ)
    (hx : ∀i,x i < B^k) (hc : ∀t < k,∑i,digit B (x i) t < B) (t : ℕ) :
    digit B (∑i,x i) t=if t < k then ∑i,digit B (x i) t else 0 := by
  have he : (∑i,x i)=pack B k (fun t=>∑i,digit B (x i) t) := by
    rw [pack_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (pack_digits hB (hx i)).symm
  rw [he,digit_pack hB hc]

lemma pack_injective {B k : ℕ} (hB : 0 < B) {f g : ℕ → ℕ}
    (hf : ∀t < k,f t < B) (hg : ∀t < k,g t < B) (he : pack B k f=pack B k g) :
    ∀t < k,f t=g t := by
  intro t ht
  have hh := congrArg (fun x=>digit B x t) he
  simpa [digit_pack hB hf,digit_pack hB hg,ht] using hh

lemma unique_scale {L : ℕ} (hL : 0 < L) : ∃! w : ℕ, 2*L < 2^w ∧ 2^w ≤ 4*L := by
  let w:=Nat.log 2 (2*L)+1
  have hl : 2*L < 2^w := Nat.lt_pow_succ_log_self (by omega) (2*L)
  have hu : 2^w ≤ 4*L := by
    have h := Nat.pow_log_le_self 2 (x:=2*L) (by omega)
    dsimp [w]; rw [pow_succ]; omega
  refine ⟨w,⟨hl,hu⟩,?_⟩
  intro v ⟨hv,hv'⟩
  apply le_antisymm
  · by_contra hh
    have hpow := Nat.pow_le_pow_right (by omega : 0 < 2) (show w+1 ≤ v by omega)
    rw [pow_succ] at hpow
    omega
  · by_contra hh
    have hpow := Nat.pow_le_pow_right (by omega : 0 < 2) (show v+1 ≤ w by omega)
    rw [pow_succ] at hpow
    omega

lemma bits_trans {x y z : ℕ} (hxy : Bits x y) (hyz : Bits y z) : Bits x z :=
  fun i=>(hxy i).trans (hyz i)
lemma pack_congr {B k : ℕ} {f g : ℕ → ℕ} (h : ∀t < k,f t=g t) : pack B k f=pack B k g := by
  apply Finset.sum_congr rfl
  intro t ht
  rw [h t (Finset.mem_range.mp ht)]
lemma pack_const_zero (B k : ℕ) : pack B k (fun _=>0)=0 := by simp [pack]
lemma pack_shift (B k : ℕ) (f : ℕ → ℕ) :
    pack B (k+1) (fun t=>if t=0 then 0 else f (t-1))=B*pack B k f := by
  rw [pack_cons]
  simp
lemma pack_init (B k a : ℕ) (f : ℕ → ℕ) :
    pack B (k+1) (fun t=>if t=0 then a else f (t-1))=a+B*pack B k f := by
  rw [pack_cons]
  simp
lemma pack_last {B T : ℕ} {f : ℕ → ℕ} (hf : f T=0) : pack B (T+1) f=pack B T f := by
  rw [pack_succ,hf,zero_mul,add_zero]

lemma division_last {B T R ρ η : ℕ} (hB : 0 < B) (hR : R < B^(T+1))
    (he : R=ρ*B^T+η) (hη : η < B^T) :
    ρ=digit B R T ∧ η=pack B T (digit B R) := by
  have hp := pack_digits hB hR
  rw [pack_succ] at hp
  have hl : pack B T (digit B R) < B^T := pack_lt hB (fun t _=>digit_lt hB R t)
  have hq : R/B^T=ρ := by rw [he,Nat.add_comm,Nat.add_mul_div_right _ _ (pow_pos hB T),Nat.div_eq_of_lt hη,zero_add]
  have hq' : R/B^T=digit B R T := by nth_rw 1 [←hp]; rw [Nat.add_mul_div_right _ _ (pow_pos hB T),Nat.div_eq_of_lt hl,zero_add]
  have hr : ρ=digit B R T := hq.symm.trans hq'
  exact ⟨hr,by rw [hr] at he; omega⟩

lemma update_coefficients {B T m d : ℕ} (hB : 2*m ≤ B) (hd : d < m)
    (r a f : ℕ → ℕ) (hr : ∀t < T+1,r t < m) (ha : ∀t < T,a t ≤ 1) (hf : ∀t < T,f t ≤ 1)
    (he : pack B (T+1) r+B*pack B T f=d+B*(pack B T r+pack B T a)) :
    r 0=d ∧ ∀t < T,r (t+1)+f t=r t+a t := by
  have hpos : 0 < B := by omega
  let l := fun t=>r t+(if t=0 then 0 else f (t-1))
  let u := fun t=>if t=0 then d else r (t-1)+a (t-1)
  have he' : pack B (T+1) l=pack B (T+1) u := by
    dsimp [l,u]
    rw [pack_add,pack_shift]
    rw [pack_init B T d (fun u=>r u+a u),pack_add]
    exact he
  have hl : ∀t < T+1,l t < B := by
    intro t ht
    dsimp [l]
    split_ifs with ht0
    · have := hr t ht; omega
    · have hh := hr t ht
      have hh' := hf (t-1) (by omega)
      omega
  have hu : ∀t < T+1,u t < B := by
    intro t ht
    dsimp [u]
    split_ifs with ht0
    · omega
    · have hh := hr (t-1) (by omega)
      have hh' := ha (t-1) (by omega)
      omega
  have hh := pack_injective hpos hl hu he'
  refine ⟨by simpa [l,u] using hh 0 (by omega),?_⟩
  intro t ht
  simpa [l,u] using hh (t+1) (by omega)

lemma update_identity {B T d : ℕ} (r a f : ℕ → ℕ) (h0 : r 0=d)
    (hstep : ∀t < T,r (t+1)+f t=r t+a t) :
    pack B (T+1) r+B*pack B T f=d+B*(pack B T r+pack B T a) := by
  rw [←pack_shift B T f,←pack_add,←pack_add,←pack_init B T d (fun t=>r t+a t)]
  apply pack_congr
  intro t ht
  by_cases he : t=0
  · simp [he,h0]
  · have hh := hstep (t-1) (by omega)
    simpa [he,show t-1+1=t by omega] using hh
end SingleFold.Packed

end OAI
