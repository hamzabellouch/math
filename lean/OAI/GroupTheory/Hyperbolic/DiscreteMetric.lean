import OAI.GroupTheory.Hyperbolic.Torsion

namespace OAI

namespace Release075.Discrete

structure Metric (V : Type) where
  dist : V → V → ℕ
  self : ∀ x, dist x x = 0
  symm : ∀ x y, dist x y = dist y x
  triangle : ∀ x y z, dist x z ≤ dist x y + dist y z

variable {V : Type} (M : Metric V)

structure Path (a b : V) where
  length : ℕ
  point : ℕ → V
  zero : point 0 = a
  stable : ∀ i, length ≤ i → point i = b
  step : ∀ i, i < length → M.dist (point i) (point (i+1)) ≤ 1

namespace Path
variable {M} {a b c : V}

@[simp] theorem last (p : Path M a b) : p.point p.length = b := p.stable _ le_rfl

@[simp] theorem at_min (p : Path M a b) (i : ℕ) : p.point (min i p.length) = p.point i := by
  by_cases h : i ≤ p.length
  · rw [min_eq_left h]
  · rw [min_eq_right (by omega),p.last,p.stable i (by omega)]

def Geodesic (p : Path M a b) : Prop := p.length = M.dist a b

def Mem (p : Path M a b) (x : V) : Prop := ∃ i ≤ p.length, p.point i = x

@[simp] theorem start_mem (p : Path M a b) : p.Mem a := ⟨0,Nat.zero_le _,p.zero⟩
@[simp] theorem end_mem (p : Path M a b) : p.Mem b := ⟨p.length,le_rfl,p.last⟩

def nil (a : V) : Path M a a where
  length := 0
  point _ := a
  zero := rfl
  stable _ _ := rfl
  step := by intro i hi; omega

def append (p : Path M a b) (q : Path M b c) : Path M a c where
  length := p.length + q.length
  point i := if i < p.length then p.point i else q.point (i-p.length)
  zero := by
    split_ifs with h
    · exact p.zero
    · simpa only [Nat.zero_sub,q.zero] using
        (p.stable 0 (by omega)).symm.trans p.zero
  stable i hi := by
    rw [ite_eq_right (by omega),q.stable _ (by omega)]
  step i hi := by
    by_cases h : i+1 < p.length
    · simpa only [ite_eq_left h,ite_eq_left (show i < p.length by omega)] using p.step i (by omega)
    · by_cases h' : i < p.length
      · have he : i+1 = p.length := by omega
        simpa only [ite_eq_left h',ite_eq_right h,he,Nat.sub_self,q.zero,p.last,ite_self] using p.step i h'
      · simpa only [ite_eq_right h',ite_eq_right h,show i+1-p.length = (i-p.length)+1 by omega] using
          q.step (i-p.length) (by omega)

@[simp] theorem length_append (p : Path M a b) (q : Path M b c) :
    (p.append q).length = p.length+q.length := rfl

@[simp] theorem append_at_left (p : Path M a b) (q : Path M b c) {i : ℕ} (hi : i ≤ p.length) :
    (p.append q).point i = p.point i := by
  change (if i < p.length then _ else _) = _
  split_ifs with h
  · rfl
  · have he : i = p.length := by omega
    simp only [he,Nat.sub_self,q.zero,p.last]

@[simp] theorem append_at_right (p : Path M a b) (q : Path M b c) (i : ℕ) :
    (p.append q).point (p.length+i) = q.point i := by
  change (if p.length+i < p.length then _ else _) = _
  simp

def reverse (p : Path M a b) : Path M b a where
  length := p.length
  point i := p.point (p.length-i)
  zero := by simpa only [Nat.sub_zero] using p.last
  stable i hi := by simpa only [Nat.sub_eq_zero_of_le hi] using p.zero
  step i hi := by
    rw [M.symm]
    have he : p.length-i = (p.length-(i+1))+1 := by omega
    rw [he]
    exact p.step _ (by omega)

def sub (p : Path M a b) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ p.length) :
    Path M (p.point i) (p.point j) where
  length := j-i
  point k := p.point (min (i+k) j)
  zero := by simp only [Nat.add_zero,min_eq_left hij]
  stable k hk := by rw [min_eq_right (by omega)]
  step k hk := by
    rw [min_eq_left (show i+k ≤ j by omega),min_eq_left (show i+(k+1) ≤ j by omega)]
    simpa only [Nat.add_assoc] using p.step (i+k) (by omega)

@[simp] theorem sub_at (p : Path M a b) {i j k : ℕ} (hij : i ≤ j) (hj : j ≤ p.length)
    (hk : k ≤ j-i) : (p.sub i j hij hj).point k = p.point (i+k) := by
  change p.point (min (i+k) j) = _
  rw [min_eq_left (by omega)]

theorem mem_reverse_iff (p : Path M a b) (x : V) : p.reverse.Mem x ↔ p.Mem x := by
  constructor
  · rintro ⟨i,hi,hx⟩; exact ⟨p.length-i,Nat.sub_le _ _,hx⟩
  · rintro ⟨i,hi,hx⟩
    exact ⟨p.length-i,Nat.sub_le _ _,by simpa only [reverse,Nat.sub_sub_self hi] using hx⟩

theorem mem_sub (p : Path M a b) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length)
    {x : V} (hx : (p.sub i j hij hj).Mem x) : p.Mem x := by
  obtain ⟨k,hk,hx⟩ := hx
  exact ⟨i+k,by change k ≤ j-i at hk; omega,(p.sub_at hij hj hk).symm.trans hx⟩

theorem mem_append_iff (p : Path M a b) (q : Path M b c) (x : V) :
    (p.append q).Mem x ↔ p.Mem x ∨ q.Mem x := by
  constructor
  · rintro ⟨i,hi,hx⟩
    by_cases h : i ≤ p.length
    · exact Or.inl ⟨i,h,(p.append_at_left q h).symm.trans hx⟩
    · refine Or.inr ⟨i-p.length,by change i ≤ p.length+q.length at hi; omega,?_⟩
      have he : p.length+(i-p.length) = i := by omega
      have hh := p.append_at_right q (i-p.length)
      rw [he] at hh
      exact hh.symm.trans hx
  · rintro (⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩)
    · exact ⟨i,by change i ≤ p.length+q.length; omega,p.append_at_left q hi⟩
    · exact ⟨p.length+i,by change p.length+i ≤ p.length+q.length; omega,p.append_at_right q i⟩

theorem dist_at_le (p : Path M a b) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) :
    M.dist (p.point i) (p.point j) ≤ j-i := by
  induction j, hij using Nat.le_induction with
  | base => simp only [M.self,Nat.sub_self,le_refl]
  | succ j hij ih =>
    have h := M.triangle (p.point i) (p.point j) (p.point (j+1))
    have h' := p.step j (by omega)
    have hh := ih (by omega)
    omega

theorem dist_le_length (p : Path M a b) : M.dist a b ≤ p.length := by
  simpa only [p.zero,p.last,Nat.sub_zero] using p.dist_at_le (Nat.zero_le _) le_rfl

theorem geodesic_dist_at (p : Path M a b) (hp : p.Geodesic)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) :
    M.dist (p.point i) (p.point j) = j-i := by
  have h₁ := p.dist_at_le (i:=0) (j:=i) (Nat.zero_le _) (hij.trans hj)
  have h₂ := p.dist_at_le (i:=j) (j:=p.length) hj le_rfl
  have h₃ := p.dist_at_le hij hj
  rw [p.zero,Nat.sub_zero] at h₁
  rw [p.last] at h₂
  have h₄ := M.triangle a (p.point i) b
  have h₅ := M.triangle (p.point i) (p.point j) b
  change p.length = M.dist a b at hp
  omega

theorem geodesic_start_dist (p : Path M a b) (hp : p.Geodesic) {i : ℕ} (hi : i ≤ p.length) :
    M.dist a (p.point i) = i := by
  simpa only [p.zero,Nat.sub_zero] using p.geodesic_dist_at hp (Nat.zero_le _) hi

theorem geodesic_end_dist (p : Path M a b) (hp : p.Geodesic) {i : ℕ} (hi : i ≤ p.length) :
    M.dist (p.point i) b = p.length-i := by
  simpa only [p.last] using p.geodesic_dist_at hp hi le_rfl

theorem geodesic_reverse (p : Path M a b) (hp : p.Geodesic) : p.reverse.Geodesic := by
  change p.length = M.dist b a
  rw [M.symm]
  exact hp

theorem geodesic_sub (p : Path M a b) (hp : p.Geodesic)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) : (p.sub i j hij hj).Geodesic :=
  (p.geodesic_dist_at hp hij hj).symm

def integral (p : Path M a b) (F : V → V → ℤ) : ℤ :=
  ∑ i ∈ Finset.range p.length, F (p.point i) (p.point (i+1))

@[simp] theorem integral_nil (a : V) (F : V → V → ℤ) : (nil (M:=M) a).integral F = 0 := by
  simp [integral,nil]

theorem integral_append (p : Path M a b) (q : Path M b c) (F : V → V → ℤ) :
    (p.append q).integral F = p.integral F+q.integral F := by
  unfold integral
  rw [length_append,Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [p.append_at_left q (by have := Finset.mem_range.mp hi; omega),
      p.append_at_left q (by have := Finset.mem_range.mp hi; omega)]
  · apply Finset.sum_congr rfl
    intro i _
    rw [p.append_at_right q i,show p.length+i+1 = p.length+(i+1) by omega,p.append_at_right]

end Path

namespace Metric
variable {M}

theorem int_dist_sub_le (x y z : V) : |(M.dist x y : ℤ)-M.dist x z| ≤ M.dist y z := by
  have h₁ := M.triangle x y z
  have h₂ := M.triangle x z y
  rw [M.symm z y] at h₂
  rw [abs_le]
  constructor <;> omega

def tent (o : V) (R : ℕ) (x : V) : ℤ := max 0 ((R:ℤ)-M.dist o x)

theorem tent_nonneg (o : V) (R : ℕ) (x : V) : 0 ≤ M.tent o R x := le_max_left _ _

theorem tent_zero {o x : V} {R : ℕ} (h : R ≤ M.dist o x) : M.tent o R x = 0 := by
  unfold tent
  omega

theorem tent_lipschitz (o : V) (R : ℕ) (x y : V) :
    |M.tent o R x - M.tent o R y| ≤ M.dist x y := by
  have h := M.int_dist_sub_le o x y
  unfold tent
  rw [abs_le] at h ⊢
  omega

def form (o a : V) (R : ℕ) (x y : V) : ℤ :=
  (M.tent o R x+M.tent o R y)*((M.dist a y:ℤ)-M.dist a x)

theorem form_flip (o a : V) (R : ℕ) (x y : V) : M.form o a R y x = -M.form o a R x y := by
  unfold form
  ring

theorem form_self (o a x : V) (R : ℕ) : M.form o a R x x = 0 := by simp [form]

theorem form_zero {o a x y : V} {R : ℕ} (hx : R ≤ M.dist o x) (hy : R ≤ M.dist o y) :
    M.form o a R x y = 0 := by rw [form,M.tent_zero hx,M.tent_zero hy,zero_add,zero_mul]

theorem form_triangle_bound (o a x y z : V) (R : ℕ)
    (hxy : M.dist x y ≤ 1) (_hyz : M.dist y z ≤ 1) (hzx : M.dist z x ≤ 1) :
    |M.form o a R x y+M.form o a R y z+M.form o a R z x| ≤ 2 := by
  have hF₁ : |M.tent o R y-M.tent o R x| ≤ 1 :=
    (M.tent_lipschitz o R y x).trans (by rw [M.symm y x]; exact_mod_cast hxy)
  have hF₂ : |M.tent o R z-M.tent o R x| ≤ 1 :=
    (M.tent_lipschitz o R z x).trans (by exact_mod_cast hzx)
  have hG₁ : |(M.dist a y:ℤ)-M.dist a x| ≤ 1 :=
    (M.int_dist_sub_le a y x).trans (by rw [M.symm y x]; exact_mod_cast hxy)
  have hG₂ : |(M.dist a z:ℤ)-M.dist a x| ≤ 1 :=
    (M.int_dist_sub_le a z x).trans (by exact_mod_cast hzx)
  have he : M.form o a R x y+M.form o a R y z+M.form o a R z x =
      (M.tent o R y-M.tent o R x)*((M.dist a z:ℤ)-M.dist a x) -
      (M.tent o R z-M.tent o R x)*((M.dist a y:ℤ)-M.dist a x) := by unfold form; ring
  rw [he]
  calc
    _ ≤ |(M.tent o R y-M.tent o R x)*((M.dist a z:ℤ)-M.dist a x)| +
        |(M.tent o R z-M.tent o R x)*((M.dist a y:ℤ)-M.dist a x)| := abs_sub _ _
    _ ≤ 1*1+1*1 := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul hF₁ hG₂ (abs_nonneg _) (by omega))
        (mul_le_mul hF₂ hG₁ (abs_nonneg _) (by omega))
    _ = 2 := by norm_num

end Metric
end Release075.Discrete

namespace Release075.Discrete
variable {V : Type} {M : Metric V}

namespace Path
variable {a b c d e f : V}

theorem dist_start_mem (p : Path M a b) {x : V} (hx : p.Mem x) : M.dist a x ≤ p.length := by
  obtain ⟨i,hi,rfl⟩ := hx
  have h := p.dist_at_le (Nat.zero_le i) hi
  rw [p.zero,Nat.sub_zero] at h
  omega

theorem dist_end_mem (p : Path M a b) {x : V} (hx : p.Mem x) : M.dist b x ≤ p.length := by
  exact p.reverse.dist_start_mem ((p.mem_reverse_iff x).mpr hx)

def SideNear (T : ℕ) (p : Path M a b) (q : Path M c d) (s : Path M e f) : Prop :=
  ∀ x, p.Mem x → ∃ y, (q.Mem y ∨ s.Mem y) ∧ M.dist x y ≤ T

theorem SideNear.reverse (T : ℕ) {p : Path M a b} {q : Path M c d} {s : Path M e f}
    (h : SideNear T p q s) : SideNear T p.reverse q s := by
  intro x hx
  exact h x ((p.mem_reverse_iff x).mp hx)

theorem SideNear.swap (T : ℕ) {p : Path M a b} {q : Path M c d} {s : Path M e f}
    (h : SideNear T p q s) : SideNear T p s q := by
  intro x hx
  obtain ⟨y,hy,hd⟩ := h x hx
  exact ⟨y,hy.symm,hd⟩

theorem SideNear.reverse_left (T : ℕ) {p : Path M a b} {q : Path M c d} {s : Path M e f}
    (h : SideNear T p q s) : SideNear T p q.reverse s := by
  intro x hx
  obtain ⟨y,hy,hd⟩ := h x hx
  exact ⟨y,hy.imp ((q.mem_reverse_iff y).mpr) id,hd⟩

theorem SideNear.reverse_right (T : ℕ) {p : Path M a b} {q : Path M c d} {s : Path M e f}
    (h : SideNear T p q s) : SideNear T p q s.reverse := by
  exact ((h.swap T).reverse_left T).swap T

def TriangleNear (T : ℕ) (p : Path M a b) (q : Path M b c) (s : Path M a c) : Prop :=
  SideNear T p q s ∧ SideNear T q s p ∧ SideNear T s p q

theorem synchronous_of_near {p : Path M a b} {s : Path M a c}
    (hp : p.Geodesic) (hs : s.Geodesic) {i j T : ℕ}
    (hi : i ≤ p.length) (hi' : i ≤ s.length) (hj : j ≤ s.length)
    (h : M.dist (p.point i) (s.point j) ≤ T) :
    M.dist (p.point i) (s.point i) ≤ 2*T := by
  have h₁ := M.triangle a (p.point i) (s.point j)
  have h₂ := M.triangle a (s.point j) (p.point i)
  rw [p.geodesic_start_dist hp hi,s.geodesic_start_dist hs hj] at h₁ h₂
  rw [M.symm (s.point j) (p.point i)] at h₂
  have h₃ := M.triangle (p.point i) (s.point j) (s.point i)
  by_cases hij : i ≤ j
  · rw [M.symm (s.point j) (s.point i),s.geodesic_dist_at hs hij hj] at h₃
    omega
  · rw [s.geodesic_dist_at hs (by omega : j ≤ i) hi'] at h₃
    omega

/-- The elementary tripod comparison: synchronous precentral points have width O(T). -/
theorem synchronous {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic) {T i : ℕ}
    (hthin : SideNear T p q s) (hi : i ≤ (p.length+s.length-q.length)/2) :
    M.dist (p.point i) (s.point i) ≤ 4*T+2 := by
  have hA : p.length ≤ q.length+s.length := by
    have h := M.triangle a c b
    change p.length = M.dist a b at hp
    change q.length = M.dist b c at hq
    change s.length = M.dist a c at hs
    rw [M.symm c b] at h
    omega
  have hC : s.length ≤ p.length+q.length := by
    have h := M.triangle a b c
    change p.length = M.dist a b at hp
    change q.length = M.dist b c at hq
    change s.length = M.dist a c at hs
    omega
  have hB : q.length ≤ p.length+s.length := by
    have h := M.triangle b a c
    change p.length = M.dist a b at hp
    change q.length = M.dist b c at hq
    change s.length = M.dist a c at hs
    rw [M.symm b a] at h
    omega
  let α := (p.length+s.length-q.length)/2
  have hiA : i ≤ p.length := by omega
  have hiC : i ≤ s.length := by omega
  by_cases hsmall : α ≤ T
  · have h := M.triangle (p.point i) a (s.point i)
    rw [M.symm (p.point i) a,p.geodesic_start_dist hp hiA,
      s.geodesic_start_dist hs hiC] at h
    change i ≤ α at hi
    omega
  · let k := min i (α-(T+1))
    have hki : k ≤ i := min_le_left _ _
    have hkA : k ≤ p.length := hki.trans hiA
    have hkC : k ≤ s.length := hki.trans hiC
    obtain ⟨x,hx,hd⟩ := hthin (p.point k) ⟨k,hkA,rfl⟩
    have hnq : ¬ q.Mem x := by
      rintro ⟨j,hj,rfl⟩
      have h₁ := M.triangle a (p.point k) b
      have h₂ := M.triangle (p.point k) (q.point j) b
      have h₃ := M.triangle a (p.point k) c
      have h₄ := M.triangle (p.point k) (q.point j) c
      rw [p.geodesic_start_dist hp hkA] at h₁ h₃
      rw [M.symm (q.point j) b,q.geodesic_start_dist hq hj] at h₂
      rw [q.geodesic_end_dist hq hj] at h₄
      change p.length = M.dist a b at hp
      change s.length = M.dist a c at hs
      dsimp [k,α] at *
      omega
    obtain ⟨j,hj,hjx⟩ := hx.resolve_left hnq
    rw [←hjx] at hd
    have hsync := synchronous_of_near hp hs hkA hkC hj hd
    have h₁ := M.triangle (p.point i) (p.point k) (s.point i)
    have h₂ := M.triangle (p.point k) (s.point k) (s.point i)
    rw [M.symm (p.point i) (p.point k),p.geodesic_dist_at hp hki hiA] at h₁
    rw [s.geodesic_dist_at hs hki hiC] at h₂
    change i ≤ α at hi
    dsimp [k] at *
    omega

theorem integral_form_nonneg (p : Path M a b) (hp : p.Geodesic) (o : V) (T : ℕ) :
    0 ≤ p.integral (M.form o a T) := by
  apply Finset.sum_nonneg
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [Metric.form,p.geodesic_start_dist hp (by omega : i+1 ≤ p.length),
    p.geodesic_start_dist hp (by omega : i ≤ p.length)]
  have h₁ := M.tent_nonneg o T (p.point i)
  have h₂ := M.tent_nonneg o T (p.point (i+1))
  push_cast
  nlinarith

theorem integral_form_quadratic (p : Path M a b) (hp : p.Geodesic) {t T : ℕ}
    (ht : t ≤ p.length) (hend : T ≤ M.dist (p.point t) b) :
    ((T/2:ℕ):ℤ)^2 ≤ p.integral (M.form (p.point t) a T) := by
  let k := T/2
  have htk : t+k ≤ p.length := by
    rw [p.geodesic_end_dist hp ht] at hend
    dsimp [k]
    omega
  have hnneg : ∀ i ∈ Finset.range p.length,
      0 ≤ M.form (p.point t) a T (p.point i) (p.point (i+1)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [Metric.form,p.geodesic_start_dist hp (by omega : i+1 ≤ p.length),
      p.geodesic_start_dist hp (by omega : i ≤ p.length)]
    have h₁ := M.tent_nonneg (p.point t) T (p.point i)
    have h₂ := M.tent_nonneg (p.point t) T (p.point (i+1))
    push_cast
    nlinarith
  have hsub : Finset.Ico t (t+k) ⊆ Finset.range p.length := by
    intro i hi
    simp only [Finset.mem_Ico,Finset.mem_range] at *
    omega
  have hlarge : ∀ i ∈ Finset.Ico t (t+k),
      (k:ℤ) ≤ M.form (p.point t) a T (p.point i) (p.point (i+1)) := by
    intro i hi
    obtain ⟨hti,hit⟩ := Finset.mem_Ico.mp hi
    have hiA : i+1 ≤ p.length := by omega
    have hdi := p.geodesic_dist_at hp hti (by omega : i ≤ p.length)
    rw [Metric.form,p.geodesic_start_dist hp hiA,
      p.geodesic_start_dist hp (by omega : i ≤ p.length)]
    have h₁ : (k:ℤ) ≤ M.tent (p.point t) T (p.point i) := by
      rw [Metric.tent,hdi]
      dsimp [k] at *
      omega
    have h₂ := M.tent_nonneg (p.point t) T (p.point (i+1))
    push_cast
    nlinarith
  calc
    ((T/2:ℕ):ℤ)^2 = ∑ _i ∈ Finset.Ico t (t+k), (k:ℤ) := by
      simp [Nat.card_Ico,k,pow_two]
    _ ≤ ∑ i ∈ Finset.Ico t (t+k), M.form (p.point t) a T (p.point i) (p.point (i+1)) :=
      Finset.sum_le_sum hlarge
    _ ≤ p.integral (M.form (p.point t) a T) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hnneg i hi)

theorem integral_form_zero (p : Path M a b) {o z : V} {T : ℕ}
    (hfar : ∀ x, p.Mem x → T ≤ M.dist o x) : p.integral (M.form o z T) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hi' := Finset.mem_range.mp hi
  exact M.form_zero (hfar _ ⟨i,by omega,rfl⟩) (hfar _ ⟨i+1,by omega,rfl⟩)

end Path

/-- A linear bound on the integral, for every clipped distance cochain. -/
def CochainBound (M : Metric V) (B : ℕ) : Prop :=
  ∀ (o a x : V) (T : ℕ) (p : Path M x x),
    |p.integral (M.form o a T)| ≤ (B:ℤ)*p.length

/-- A geodesic arc through `o`, closed by a short bypass outside the open T-ball. -/
def ShortBypass (M : Metric V) (T : ℕ) (o : V) (K : ℕ) : Prop :=
  ∃ (a b : V) (p : Path M a b) (q : Path M b a),
    p.Geodesic ∧ p.Mem o ∧ (∀ x, q.Mem x → T ≤ M.dist o x) ∧
      p.length+q.length ≤ K

theorem shortBypass_quadratic {B T K : ℕ} {o : V}
    (hB : CochainBound M B) (h : ShortBypass M T o K) :
    ((T/2:ℕ):ℤ)^2 ≤ (B:ℤ)*K := by
  obtain ⟨a,b,p,q,hp,⟨t,ht,rfl⟩,hfar,hK⟩ := h
  have h₁ := p.integral_form_quadratic hp ht (hfar b q.start_mem)
  have h₂ := hB (p.point t) a a T (p.append q)
  rw [p.integral_append,q.integral_form_zero hfar,add_zero] at h₂
  have h₃ := le_abs_self (p.integral (M.form (p.point t) a T))
  have hlen : ((p.append q).length:ℤ) ≤ K := by exact_mod_cast hK
  have hmul := mul_le_mul_of_nonneg_left hlen (Nat.cast_nonneg B : (0:ℤ) ≤ B)
  omega

end Release075.Discrete

end OAI
