import OAI.Combinatorics.VariableWL.Model

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL

class FiniteNumbering (A : Type uVariable1) [Fintype A] where
  equiv : A ≃ Fin (Fintype.card A)

noncomputable instance (priority := 10) defaultFiniteNumbering (A : Type uVariable2) [Fintype A] :
    FiniteNumbering A := ⟨Fintype.equivFin A⟩
noncomputable instance (priority := 5) defaultFiniteNumberings (A : Type uVariable3) (B : A → Type uVariable6)
    [∀a,Fintype (B a)] : (a : A) → FiniteNumbering (B a) :=
  fun a=>defaultFiniteNumbering (B a)
noncomputable def enumeration (A : Type uVariable4) [Fintype A] [FiniteNumbering A] :
    A ≃ Fin (Fintype.card A) := FiniteNumbering.equiv
end VariableWL

namespace VariableWL.Affine

abbrev Bit := ZMod 2
abbrev Vec (d : ℕ) := Fin d → Bit
abbrev SquareVal (d e : ℕ) := (Vec d × Vec e) × (Bit × Bit)

open scoped CharTwo

variable {d e : ℕ}

def boundary (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit)
    (z : SquareVal d e) : Bit :=
  L z.1.1 + R z.1.2 + z.2.1 + z.2.2

def Fiber (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit) (c : Bit) :=
  { z : SquareVal d e | boundary L R z = c }

@[simp] theorem boundary_add (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit)
    (z w : SquareVal d e) : boundary L R (z + w) = boundary L R z + boundary L R w := by
  simp only [boundary, Prod.fst_add, Prod.snd_add, map_add]
  ring

@[simp] theorem boundary_zero (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit) :
    boundary L R 0 = 0 := by
  simp [boundary]

def kernel (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit) :
    Submodule Bit (SquareVal d e) where
  carrier := Fiber L R 0
  zero_mem' := boundary_zero L R
  add_mem' := by
    intro z w hz hw
    change boundary L R (z + w) = 0
    rw [boundary_add, hz, hw, add_zero]
  smul_mem' := by
    intro a z hz
    change boundary L R (a • z) = 0
    change boundary L R z = 0 at hz
    simp only [boundary, Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul] at *
    calc
      a * L z.1.1 + a * R z.1.2 + a * z.2.1 + a * z.2.2 =
          a * (L z.1.1 + R z.1.2 + z.2.1 + z.2.2) := by ring
      _ = 0 := by rw [hz, mul_zero]

theorem fiber_nonempty (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit) (c : Bit) :
    (Fiber L R c).Nonempty := by
  exact ⟨((0, 0), (c, 0)), by simp [Fiber, boundary]⟩

theorem fiber_translate (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit)
    {c : Bit} {ξ : SquareVal d e} (hξ : ξ ∈ Fiber L R c) :
    (fun z => z + ξ) '' Fiber L R 0 = Fiber L R c := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    change boundary L R (z + ξ) = c
    rw [boundary_add, hz, hξ, zero_add]
  · intro hw
    refine ⟨w - ξ, ?_, sub_add_cancel _ _⟩
    change boundary L R (w - ξ) = 0
    change boundary L R w = c at hw
    change boundary L R ξ = c at hξ
    have hsub : boundary L R (w - ξ) = boundary L R w - boundary L R ξ := by
      simp only [boundary, Prod.fst_sub, Prod.snd_sub, map_sub]
      ring
    rw [hsub, hw, hξ, sub_self]

theorem fiber_full_left (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit)
    (c : Bit) (x : Vec d) : ∃ z ∈ Fiber L R c, z.1.1 = x := by
  refine ⟨((x, 0), (c + L x, 0)), ?_, rfl⟩
  simp [Fiber, boundary, add_comm, add_left_comm]

theorem fiber_full_right (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit)
    (c : Bit) (x : Vec e) : ∃ z ∈ Fiber L R c, z.1.2 = x := by
  refine ⟨((0, x), (c + R x, 0)), ?_, rfl⟩
  simp [Fiber, boundary, add_comm, add_left_comm]

theorem fiber_full_vertical₀ (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit)
    (c y : Bit) : ∃ z ∈ Fiber L R c, z.2.1 = y := by
  refine ⟨((0, 0), (y, c + y)), ?_, rfl⟩
  simp [Fiber, boundary, add_comm, add_left_comm]

theorem fiber_full_vertical₁ (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit)
    (c y : Bit) : ∃ z ∈ Fiber L R c, z.2.2 = y := by
  refine ⟨((0, 0), (c + y, y)), ?_, rfl⟩
  simp [Fiber, boundary]

def fiberEquiv (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit) (c : Bit) :
    Fiber L R c ≃ Vec d × Vec e × Bit where
  toFun z := (z.1.1.1, z.1.1.2, z.1.2.1)
  invFun a := ⟨((a.1, a.2.1), (a.2.2, c + L a.1 + R a.2.1 + a.2.2)), by
    simp [Fiber, boundary, add_assoc, add_left_comm, add_comm]⟩
  left_inv z := by
    apply Subtype.ext
    rcases z with ⟨⟨⟨x,y⟩,⟨v,w⟩⟩, h⟩
    change ((x, y), (v, c + L x + R y + v)) = ((x, y), (v, w))
    change L x + R y + v + w = c at h
    have hw : c + L x + R y + v = w := by
      rw [← h]
      simp [add_left_comm, add_comm]
    rw [hw]
  right_inv a := rfl

theorem fiber_card (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit) (c : Bit) :
    Nat.card (Fiber L R c) = 2 ^ (d + e + 1) := by
  rw [Nat.card_congr (fiberEquiv L R c)]
  simp [pow_add, mul_assoc]

theorem fiber_card_le_sixteen (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit)
    (c : Bit) (internal : d + e ≤ 3) : Nat.card (Fiber L R c) ≤ 16 := by
  rw [fiber_card]
  calc
    2 ^ (d + e + 1) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 16 := by norm_num

end VariableWL.Affine

namespace VariableWL.Markers

abbrev Bit := ZMod 2
open scoped CharTwo

variable {V : Type uVariable5} {G : SimpleGraph V}

def walkSum (ω : V → V → Bit) : {u v : V} → G.Walk u v → Bit
  | _, _, .nil => 0
  | u, _, .cons (v := v) _ p => ω u v + walkSum ω p

@[simp] theorem walkSum_nil (ω : V → V → Bit) (u : V) :
    walkSum ω (SimpleGraph.Walk.nil : G.Walk u u) = 0 := rfl

@[simp] theorem walkSum_cons (ω : V → V → Bit) {u v w : V}
    (h : G.Adj u v) (p : G.Walk v w) :
    walkSum ω (.cons h p) = ω u v + walkSum ω p := rfl

@[simp] theorem walkSum_append (ω : V → V → Bit) {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) :
    walkSum ω (p.append q) = walkSum ω p + walkSum ω q := by
  induction p with
  | nil => simp [walkSum]
  | cons h p ih => simp [SimpleGraph.Walk.cons_append, walkSum, ih, add_assoc]

@[simp] theorem walkSum_reverse (ω : V → V → Bit)
    (hsym : ∀ u v, G.Adj u v → ω u v = ω v u) {u v : V} (p : G.Walk u v) :
    walkSum ω p.reverse = walkSum ω p := by
  induction p with
  | nil => simp [walkSum]
  | @cons u v w h p ih =>
      simp only [SimpleGraph.Walk.reverse_cons, walkSum_append, ih, walkSum_cons,
        walkSum_nil, add_zero]
      rw [← hsym u v h, add_comm]

theorem exists_potential (ω : V → V → Bit)
    (hsym : ∀ u v, G.Adj u v → ω u v = ω v u)
    (hconn : G.Preconnected) (root : V)
    (hzero : ∀ u (p : G.Walk u u), walkSum ω p = 0) :
    ∃ s : V → Bit, ∀ u v, G.Adj u v → s u + s v = ω u v := by
  classical
  let p : (v : V) → G.Walk root v := fun v => (hconn root v).some
  refine ⟨fun v => walkSum ω (p v), ?_⟩
  intro u v huv
  have hc := hzero root (((p u).append huv.toWalk).append (p v).reverse)
  simp only [walkSum_append, walkSum_reverse ω hsym, SimpleGraph.Adj.toWalk,
    walkSum_cons, walkSum_nil, add_zero] at hc
  calc
    walkSum ω (p u) + walkSum ω (p v) =
        (walkSum ω (p u) + ω u v + walkSum ω (p v)) + ω u v := by
      simp [add_comm, add_assoc]
    _ = ω u v := by rw [hc, zero_add]

theorem walkSum_of_potential (ω : V → V → Bit) (s : V → Bit)
    (hs : ∀ u v, G.Adj u v → s u + s v = ω u v) {u v : V} (p : G.Walk u v) :
    walkSum ω p = s u + s v := by
  induction p with
  | nil => simp [walkSum]
  | @cons u v w h p ih =>
    rw [walkSum_cons, ih, ← hs u v h]
    simp [add_assoc]

end VariableWL.Markers

namespace VariableWL.Affine
open scoped CharTwo

theorem gauge_horizontal {d : ℕ} (x y h h' : Vec d) (s t δ : Bit)
    (hmark : s + t = δ) :
    (x + s • (h' + h)) + (y + t • (h' + h)) + δ • h' = x + y + δ • h := by
  ext i
  change x i + s * (h' i + h i) + (y i + t * (h' i + h i)) + δ * h' i =
    x i + y i + δ * h i
  rw [← hmark]
  have htwo : (2 : Bit) = 0 := by decide
  linear_combination (h' i * (s + t)) * htwo

theorem gauge_vertical {d e : ℕ} (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit)
    (x : Vec d) (y : Vec e) (h h' : Vec d) (j j' : Vec e) (s t : Bit)
    (hs : s = t) (hdiff : L (h' + h) = R (j' + j)) :
    L (x + s • (h' + h)) + R (y + t • (j' + j)) = L x + R y := by
  subst t
  simp only [map_add, map_smul, smul_eq_mul]
  have hd : L h' + L h = R j' + R j := by simpa using hdiff
  rw [hd]
  simp [add_comm, add_left_comm]

theorem shift_difference {d e : ℕ} (L : Vec d →ₗ[Bit] Bit) (R : Vec e →ₗ[Bit] Bit)
    (h h' : Vec d) (j j' : Vec e) (b : Bit)
    (hh : L h + R j = b) (hh' : L h' + R j' = b) :
    L (h' + h) = R (j' + j) := by
  simp only [map_add]
  have htwo : (2 : Bit) = 0 := by decide
  linear_combination hh' + hh - (R j' + R j - b) * htwo

end VariableWL.Affine

namespace VariableWL.ScalarImages

abbrev Bit := ZMod 2
abbrev Pair := Bit × Bit

def sum (x : Pair) : Bit := x.1 + x.2

def buffer (D : Set Bit) : Set Pair := {x | sum x ∈ D}

open scoped CharTwo

theorem buffer_nonempty {D : Set Bit} (hD : D.Nonempty) : (buffer D).Nonempty := by
  rcases hD with ⟨a, ha⟩
  exact ⟨(0, a), by simpa [buffer, sum] using ha⟩

theorem buffer_image_sum (D : Set Bit) : sum '' buffer D = D := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro ha
    exact ⟨(0, a), by simpa [buffer, sum] using ha, by simp [sum]⟩

theorem buffer_image_fst {D : Set Bit} (hD : D.Nonempty) :
    Prod.fst '' buffer D = Set.univ := by
  rcases hD with ⟨d, hd⟩
  apply Set.eq_univ_of_forall
  intro a
  refine ⟨(a, d + a), ?_, rfl⟩
  simpa [buffer, sum, add_comm, add_left_comm] using hd

theorem buffer_image_snd {D : Set Bit} (hD : D.Nonempty) :
    Prod.snd '' buffer D = Set.univ := by
  rcases hD with ⟨d, hd⟩
  apply Set.eq_univ_of_forall
  intro a
  refine ⟨(d + a, a), ?_, rfl⟩
  simpa [buffer, sum, add_assoc] using hd

theorem zero_buffer_unique {B : Set Pair} (hB : B.Nonempty)
    (h₀ : Prod.fst '' B = {0}) (h₁ : Prod.snd '' B = {0}) : B = {(0, 0)} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  have hall : ∀ x ∈ B, x = (0, 0) := by
    intro x hx
    have hx₀ : x.1 ∈ ({0} : Set Bit) := h₀ ▸ Set.mem_image_of_mem Prod.fst hx
    have hx₁ : x.2 ∈ ({0} : Set Bit) := h₁ ▸ Set.mem_image_of_mem Prod.snd hx
    exact Prod.ext (Set.mem_singleton_iff.mp hx₀) (Set.mem_singleton_iff.mp hx₁)
  rcases hB with ⟨x, hx⟩
  exact ⟨hall x hx ▸ hx, hall⟩

theorem zero_propagates {B : Set Pair} {D : Set Bit} (hB : B.Nonempty)
    (h₀ : Prod.fst '' B = {0}) (h₁ : Prod.snd '' B = {0})
    (hD : sum '' B = D) : D = {0} := by
  rw [← hD, zero_buffer_unique hB h₀ h₁]
  simp [sum]

def andWitness (p q : Prop) : Set Pair :=
  {x | (p → x.1 = 0) ∧ (q → x.2 = 0)}

theorem andWitness_nonempty (p q : Prop) : (andWitness p q).Nonempty :=
  ⟨(0, 0), ⟨fun _ => rfl, fun _ => rfl⟩⟩

theorem andWitness_fst (p q : Prop) :
    Prod.fst '' andWitness p q = {a : Bit | p → a = 0} := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx.1
  · intro ha
    exact ⟨(a, 0), ⟨ha, fun _ => rfl⟩, rfl⟩

theorem andWitness_snd (p q : Prop) :
    Prod.snd '' andWitness p q = {a : Bit | q → a = 0} := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx.2
  · intro ha
    exact ⟨(0, a), ⟨fun _ => rfl, ha⟩, rfl⟩

theorem andWitness_sum (p q : Prop) :
    sum '' andWitness p q = {a : Bit | p ∧ q → a = 0} := by
  classical
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩ ⟨hp, hq⟩
    simp [sum, hx.1 hp, hx.2 hq]
  · intro ha
    by_cases hp : p
    · refine ⟨(0, a), ⟨fun _ => rfl, fun hq => ha ⟨hp, hq⟩⟩, ?_⟩
      simp [sum]
    · refine ⟨(a, 0), ⟨fun h => (hp h).elim, fun _ => rfl⟩, ?_⟩
      simp [sum]

end VariableWL.ScalarImages

end OAI
