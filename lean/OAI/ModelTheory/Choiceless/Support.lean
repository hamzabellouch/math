import OAI.ModelTheory.Choiceless.Model

namespace OAI

namespace CPTSeparation

namespace Support

abbrev Scalar := ZMod 3

abbrev Plane := Scalar × Scalar

def omega (u v : Plane) : Scalar := u.1 * v.2 - u.2 * v.1

@[simp] theorem omega_self (u : Plane) : omega u u = 0 := by simp [omega, mul_comm]

@[simp] theorem omega_zero_left (u : Plane) : omega 0 u = 0 := by simp [omega]

@[simp] theorem omega_zero_right (u : Plane) : omega u 0 = 0 := by simp [omega]

@[simp] theorem omega_add_left (u v w : Plane) :
    omega (u + v) w = omega u w + omega v w := by simp [omega]; ring

@[simp] theorem omega_add_right (u v w : Plane) :
    omega u (v + w) = omega u v + omega u w := by simp [omega]; ring

@[simp] theorem omega_neg_left (u v : Plane) : omega (-u) v = -omega u v := by
  simp [omega]; ring

@[simp] theorem omega_neg_right (u v : Plane) : omega u (-v) = -omega u v := by
  simp [omega]; ring

theorem omega_swap (u v : Plane) : omega v u = -omega u v := by
  simp [omega]; ring

@[simp] theorem omega_smul_left (a : Scalar) (u v : Plane) :
    omega (a • u) v = a * omega u v := by simp [omega]; ring

@[simp] theorem omega_smul_right (a : Scalar) (u v : Plane) :
    omega u (a • v) = a * omega u v := by simp [omega]; ring

variable {F K : Type} [finiteF : Fintype F] [AddCommGroup K] [scalarModuleK : Module Scalar K]

def correction (cycle : F → K) (a b : F → Plane) : K :=
  (2 : Scalar) • ∑ f, omega (a f) (b f) • cycle f

@[simp] theorem correction_self (cycle : F → K) (a : F → Plane) :
    correction cycle a a = 0 := by simp [correction]

@[simp] theorem correction_zero_left (cycle : F → K) (a : F → Plane) :
    correction cycle 0 a = 0 := by simp [correction]

@[simp] theorem correction_zero_right (cycle : F → K) (a : F → Plane) :
    correction cycle a 0 = 0 := by simp [correction]

@[simp] theorem correction_add_left (cycle : F → K) (a b c : F → Plane) :
    correction cycle (a + b) c = correction cycle a c + correction cycle b c := by
  simp [correction, add_smul, Finset.sum_add_distrib, smul_add]

@[simp] theorem correction_add_right (cycle : F → K) (a b c : F → Plane) :
    correction cycle a (b + c) = correction cycle a b + correction cycle a c := by
  simp [correction, add_smul, Finset.sum_add_distrib, smul_add]

@[simp] theorem correction_neg_left (cycle : F → K) (a b : F → Plane) :
    correction cycle (-a) b = -correction cycle a b := by
  simp [correction, Finset.sum_neg_distrib]

@[simp] theorem correction_neg_right (cycle : F → K) (a b : F → Plane) :
    correction cycle a (-b) = -correction cycle a b := by
  simp [correction, Finset.sum_neg_distrib]

theorem correction_swap (cycle : F → K) (a b : F → Plane) :
    correction cycle b a = -correction cycle a b := by
  unfold correction
  rw [← smul_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro f _
  rw [omega_swap, neg_smul]

@[ext]
structure H (cycle : F → K) where
  face : F → Plane
  flow : K

namespace H

variable (cycle : F → K)

instance : One (H cycle) := ⟨⟨0, 0⟩⟩

instance : Mul (H cycle) := ⟨fun x y =>
  ⟨x.face + y.face, x.flow + y.flow + correction cycle x.face y.face⟩⟩

instance : Inv (H cycle) := ⟨fun x => ⟨-x.face, -x.flow⟩⟩

omit F K cycle in
@[simp] theorem one_face
    {F : Type}
    {K : Type}
    [Fintype F]
    [AddCommGroup K]
    [_root_.Module Support.Scalar K]
    (cycle : F → K) : (1 : H cycle).face = 0 := rfl

omit F K cycle in
@[simp] theorem one_flow
    {F : Type}
    {K : Type}
    [Fintype F]
    [AddCommGroup K]
    [_root_.Module Support.Scalar K]
    (cycle : F → K) : (1 : H cycle).flow = 0 := rfl

@[simp] theorem mul_face (x y : H cycle) : (x * y).face = x.face + y.face := rfl

@[simp] theorem mul_flow (x y : H cycle) :
    (x * y).flow = x.flow + y.flow + correction cycle x.face y.face := rfl

omit F K cycle in
@[simp] theorem inv_face
    {F : Type}
    {K : Type}
    [Fintype F]
    [AddCommGroup K]
    [_root_.Module Support.Scalar K]
    (cycle : F → K) (x : H cycle) : x⁻¹.face = -x.face := rfl

omit F K cycle in
@[simp] theorem inv_flow
    {F : Type}
    {K : Type}
    [Fintype F]
    [AddCommGroup K]
    [_root_.Module Support.Scalar K]
    (cycle : F → K) (x : H cycle) : x⁻¹.flow = -x.flow := rfl

instance : Group (H cycle) := Group.ofLeftAxioms
  (by intro x y z; ext <;> simp [add_assoc] ; abel)
  (by intro x; ext <;> simp)
  (by intro x; ext <;> simp)

def central (k : K) : H cycle := ⟨0,k⟩

@[simp] theorem central_mul (k l : K) : central cycle k * central cycle l = central cycle (k+l) := by
  ext <;> simp [central]

omit F K cycle in
@[simp] theorem central_zero
    {F : Type}
    {K : Type}
    [Fintype F]
    [AddCommGroup K]
    [_root_.Module Support.Scalar K]
    (cycle : F → K) : central cycle (0 : K) = 1 := rfl

omit F K cycle in
@[simp] theorem central_neg
    {F : Type}
    {K : Type}
    [Fintype F]
    [AddCommGroup K]
    [_root_.Module Support.Scalar K]
    (cycle : F → K) (k : K) : central cycle (-k) = (central cycle k)⁻¹ := by
  apply H.ext <;> simp [central]

theorem central_commute (x : H cycle) (k : K) :
    x * central cycle k = central cycle k * x := by
  ext <;> simp [central, add_comm]

theorem commutator (x y : H cycle) :
    x * y * x⁻¹ * y⁻¹ = central cycle (∑ f, omega (x.face f) (y.face f) • cycle f) := by
  apply H.ext
  · simp only [mul_face, inv_face, central]
    abel
  · simp only [mul_flow, mul_face, inv_flow, inv_face,
      correction_add_left, correction_neg_left,
      correction_neg_right, correction_self,
      zero_add, add_zero, central]
    have hc : correction cycle x.face y.face + correction cycle x.face y.face =
        ∑ f, omega (x.face f) (y.face f) • cycle f := by
      rw [correction, ← add_smul]
      have h : (2 : Scalar) + 2 = 1 := by decide
      rw [h, one_smul]
    have hs := correction_swap cycle x.face y.face
    rw [hs]
    abel_nf at hc ⊢
    exact hc

def projectedAddSubgroup (S : Subgroup (H cycle)) : AddSubgroup (F → Plane) where
  carrier := {a | ∃ h ∈ S, h.face = a}
  zero_mem' := ⟨1, S.one_mem, rfl⟩
  add_mem' := by
    rintro a b ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x*y, S.mul_mem hx hy, rfl⟩
  neg_mem' := by
    rintro a ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, S.inv_mem hx, rfl⟩

def centralAddSubgroup (S : Subgroup (H cycle)) : AddSubgroup K where
  carrier := {k | central cycle k ∈ S}
  zero_mem' := S.one_mem
  add_mem' := by
    intro k l hk hl
    change central cycle (k+l) ∈ S
    simpa only [← central_mul] using S.mul_mem hk hl
  neg_mem' := by
    intro k hk
    change central cycle (-k) ∈ S
    simpa only [central_neg] using S.inv_mem hk

def projected (S : Subgroup (H cycle)) : Submodule Scalar (F → Plane) :=
  AddSubgroup.toZModSubmodule 3 (projectedAddSubgroup cycle S)

def centralPart (S : Subgroup (H cycle)) : Submodule Scalar K :=
  AddSubgroup.toZModSubmodule 3 (centralAddSubgroup cycle S)

@[simp] theorem mem_projected (S : Subgroup (H cycle)) (a : F → Plane) :
    a ∈ projected cycle S ↔ ∃ h ∈ S, h.face = a := Iff.rfl

@[simp] theorem mem_centralPart (S : Subgroup (H cycle)) (k : K) :
    k ∈ centralPart cycle S ↔ central cycle k ∈ S := Iff.rfl

theorem commutator_mem_centralPart (S : Subgroup (H cycle))
    {a b : F → Plane} (ha : a ∈ projected cycle S) (hb : b ∈ projected cycle S) :
    (∑ f, omega (a f) (b f) • cycle f) ∈ centralPart cycle S := by
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  rw [mem_centralPart, ← commutator]
  exact S.mul_mem (S.mul_mem (S.mul_mem hx hy) (S.inv_mem hx)) (S.inv_mem hy)

theorem stabilizer_isotropic (S : Subgroup (H cycle)) (lambda : K →ₗ[Scalar] Scalar)
    (hlambda : ∀ k ∈ centralPart cycle S, lambda k = 0)
    {a b : F → Plane} (ha : a ∈ projected cycle S) (hb : b ∈ projected cycle S) :
    (∑ f, lambda (cycle f) * omega (a f) (b f)) = 0 := by
  have h := hlambda _ (commutator_mem_centralPart cycle S ha hb)
  simpa only [map_sum, map_smul, smul_eq_mul, mul_comm] using h

def productEquiv : H cycle ≃ (F → Plane) × K where
  toFun x := (x.face,x.flow)
  invFun x := ⟨x.1,x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Finite K] : Finite (H cycle) :=
  Finite.of_equiv ((F → Plane) × K) (productEquiv cycle).symm

noncomputable def projectedLift (S : Subgroup (H cycle)) (a : projected cycle S) : H cycle :=
  Classical.choose a.property

theorem projectedLift_mem (S : Subgroup (H cycle)) (a : projected cycle S) :
    projectedLift cycle S a ∈ S := (Classical.choose_spec a.property).1

@[simp] theorem projectedLift_face (S : Subgroup (H cycle)) (a : projected cycle S) :
    (projectedLift cycle S a).face = a.val := (Classical.choose_spec a.property).2

theorem mul_inv_of_face_eq (x y : H cycle) (h : x.face = y.face) :
    x * y⁻¹ = central cycle (x.flow - y.flow) := by
  apply H.ext
  · simp [h, central]
  · simp [central, h, sub_eq_add_neg]

noncomputable def subgroupEquiv (S : Subgroup (H cycle)) :
    S ≃ projected cycle S × centralPart cycle S where
  toFun x := by
    let a : projected cycle S := ⟨x.val.face, x.val, x.property, rfl⟩
    refine (a, ⟨x.val.flow - (projectedLift cycle S a).flow, ?_⟩)
    rw [mem_centralPart, ← mul_inv_of_face_eq cycle x.val (projectedLift cycle S a)]
    · exact S.mul_mem x.property (S.inv_mem (projectedLift_mem cycle S a))
    · exact (projectedLift_face cycle S a).symm
  invFun p := ⟨central cycle p.2.val * projectedLift cycle S p.1,
    S.mul_mem ((mem_centralPart cycle S p.2.val).mp p.2.property) (projectedLift_mem cycle S p.1)⟩
  left_inv := by
    intro x
    apply Subtype.ext
    apply H.ext
    · simp [central]
    · simp [central]
  right_inv := by
    rintro ⟨a,k⟩
    apply Prod.ext
    · apply Subtype.ext
      simp [central]
    · apply Subtype.ext
      let a' : projected cycle S := ⟨(central cycle k.val * projectedLift cycle S a).face,
        central cycle k.val * projectedLift cycle S a,
        S.mul_mem ((mem_centralPart cycle S k.val).mp k.property) (projectedLift_mem cycle S a), rfl⟩
      have h : a' = a := by
        apply Subtype.ext
        simp [a', central]
      change (central cycle k.val * projectedLift cycle S a).flow -
        (projectedLift cycle S a').flow = k.val
      rw [h]
      simp [central]

theorem subgroup_card [FiniteDimensional Scalar K] (S : Subgroup (H cycle)) :
    Nat.card S = 3 ^ (Module.finrank Scalar (projected cycle S) +
      Module.finrank Scalar (centralPart cycle S)) := by
  rw [Nat.card_congr (subgroupEquiv cycle S), Nat.card_prod,
    Module.natCard_eq_pow_finrank (K := Scalar) (V := projected cycle S),
    Module.natCard_eq_pow_finrank (K := Scalar) (V := centralPart cycle S)]
  have h : Nat.card Scalar = 3 := by simp [Scalar, Nat.card_eq_fintype_card]
  rw [h, ← pow_add]

theorem ambient_card [FiniteDimensional Scalar K] :
    Nat.card (H cycle) = 3 ^ (Module.finrank Scalar (F → Plane) + Module.finrank Scalar K) := by
  rw [Nat.card_congr (productEquiv cycle), Nat.card_prod,
    Module.natCard_eq_pow_finrank (K := Scalar) (V := F → Plane),
    Module.natCard_eq_pow_finrank (K := Scalar) (V := K)]
  have h : Nat.card Scalar = 3 := by simp [Scalar, Nat.card_eq_fintype_card]
  rw [h, ← pow_add]

theorem subgroup_index [FiniteDimensional Scalar K] (S : Subgroup (H cycle)) :
    S.index = 3 ^ ((Module.finrank Scalar (F → Plane) - Module.finrank Scalar (projected cycle S)) +
      (Module.finrank Scalar K - Module.finrank Scalar (centralPart cycle S))) := by
  have hu := Submodule.finrank_le (projected cycle S)
  have hk := Submodule.finrank_le (centralPart cycle S)
  have hc := S.index_mul_card
  rw [subgroup_card cycle S, ambient_card cycle] at hc
  apply Nat.mul_right_cancel (m := 3 ^ (Module.finrank Scalar (projected cycle S) +
    Module.finrank Scalar (centralPart cycle S))) (by positivity)
  rw [hc, ← pow_add]
  congr 1
  omega

end H

def diagonalForm (weight : F → Scalar) : LinearMap.BilinForm Scalar (F → Plane) where
  toFun a := {
    toFun := fun b => ∑ f, weight f * omega (a f) (b f)
    map_add' := by intro b c; simp [mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro r b
      simp only [Pi.smul_apply, omega_smul_right, smul_eq_mul, RingHom.id_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      ring }
  map_add' := by
    intro a b
    ext c
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro r a
    ext b
    simp only [Pi.smul_apply, omega_smul_left, LinearMap.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    change (∑ f, weight f * (r * omega (a f) (b f))) =
      r * (∑ f, weight f * omega (a f) (b f))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    ring

@[simp] theorem diagonalForm_apply (weight : F → Scalar) (a b : F → Plane) :
    diagonalForm weight a b = ∑ f, weight f * omega (a f) (b f) := rfl

theorem mem_diagonalForm_ker (weight : F → Scalar) (a : F → Plane) :
    a ∈ (diagonalForm weight).ker ↔ ∀ f, weight f ≠ 0 → a f = 0 := by
  classical
  constructor
  · intro ha f hf
    have hzero : ∀ b, diagonalForm weight a b = 0 := by
      intro b
      exact LinearMap.congr_fun (LinearMap.mem_ker.mp ha) b
    have heval (b : Plane) : diagonalForm weight a (Pi.single f b) =
        weight f * omega (a f) b := by
      rw [diagonalForm_apply, Finset.sum_eq_single f]
      · simp
      · intro g _ hg
        simp [hg]
      · simp
    have hfst := hzero (Pi.single f (0,1))
    have hsnd := hzero (Pi.single f (1,0))
    simp only [heval, omega, mul_one, mul_zero, sub_zero, zero_sub, mul_neg, neg_eq_zero] at hfst hsnd
    apply Prod.ext
    · exact (mul_eq_zero.mp hfst).resolve_left hf
    · exact (mul_eq_zero.mp hsnd).resolve_left hf
  · intro ha
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro b
    change (∑ f, weight f * omega (a f) (b f)) = 0
    apply Finset.sum_eq_zero
    intro f _
    by_cases hf : weight f = 0
    · simp [hf]
    · simp [ha f hf]

noncomputable def diagonalKerEquiv (weight : F → Scalar) :
    (diagonalForm weight).ker ≃ₗ[Scalar] ({f : F // weight f = 0} → Plane) where
  toFun a f := a.val f.val
  invFun b := by
    classical
    refine ⟨fun f => if hf : weight f = 0 then b ⟨f,hf⟩ else 0, ?_⟩
    rw [mem_diagonalForm_ker]
    intro f hf
    simp [hf]
  left_inv := by
    intro a
    apply Subtype.ext
    funext f
    dsimp
    split_ifs with hf
    · rfl
    · exact ((mem_diagonalForm_ker weight a.val).mp a.property f hf).symm
  right_inv := by intro b; funext f; simp [f.property]
  map_add' := by intro a b; rfl
  map_smul' := by intro r a; rfl

theorem diagonalForm_finrank_ker (weight : F → Scalar) :
    Module.finrank Scalar (diagonalForm weight).ker =
      2 * Fintype.card {f : F // weight f = 0} := by
  classical
  rw [(diagonalKerEquiv weight).finrank_eq, Module.finrank_pi_fintype]
  simp [Plane, Module.finrank_prod, Nat.mul_comm]

theorem nonzero_blocks_le_codim (weight : F → Scalar)
    (U : Submodule Scalar (F → Plane))
    (hisotropic : ∀ a ∈ U, ∀ b ∈ U, diagonalForm weight a b = 0) :
    Fintype.card {f : F // weight f ≠ 0} ≤
      Module.finrank Scalar (F → Plane) - Module.finrank Scalar U := by
  classical
  have hle : U ≤ (diagonalForm weight).orthogonal U := by
    intro a ha
    exact fun b hb => hisotropic b hb a ha
  have hd := Submodule.finrank_mono hle
  have heq := LinearMap.BilinForm.finrank_add_finrank_orthogonal'
    (B := diagonalForm weight) U
  have hker := Submodule.finrank_mono
    (show U ⊓ (diagonalForm weight).ker ≤ (diagonalForm weight).ker from inf_le_right)
  have hcard : Fintype.card {f : F // weight f ≠ 0} =
      Fintype.card F - Fintype.card {f : F // weight f = 0} :=
    Fintype.card_subtype_compl (fun f : F => weight f = 0)
  have hcardle := Fintype.card_subtype_le (fun f : F => weight f = 0)
  have hdimu : Module.finrank Scalar U ≤ Module.finrank Scalar (F → Plane) :=
    Submodule.finrank_le U
  have hdim : Module.finrank Scalar (F → Plane) = 2 * Fintype.card F := by
    rw [Module.finrank_pi_fintype]
    simp [Plane, Module.finrank_prod, Nat.mul_comm]
  rw [diagonalForm_finrank_ker] at hker
  rw [hdim] at heq hdimu ⊢
  omega

end Support

end CPTSeparation

namespace CPTSeparation.Grid

abbrev Scalar := ZMod 3

abbrev Vertex (n : ℕ) := Fin (n+1) × Fin (n+1) × Fin (n+1)

abbrev EdgeX (n : ℕ) := Fin n × Fin (n+1) × Fin (n+1)

abbrev EdgeY (n : ℕ) := Fin (n+1) × Fin n × Fin (n+1)

abbrev EdgeZ (n : ℕ) := Fin (n+1) × Fin (n+1) × Fin n

abbrev Edge (n : ℕ) := EdgeX n ⊕ EdgeY n ⊕ EdgeZ n

abbrev FaceXY (n : ℕ) := Fin n × Fin n × Fin (n+1)

abbrev FaceXZ (n : ℕ) := Fin n × Fin (n+1) × Fin n

abbrev FaceYZ (n : ℕ) := Fin (n+1) × Fin n × Fin n

abbrev Face (n : ℕ) := FaceXY n ⊕ FaceXZ n ⊕ FaceYZ n

variable {n : ℕ}

def ex (i : Fin n) (j k : Fin (n+1)) : Edge n := .inl (i,j,k)

def ey (i : Fin (n+1)) (j : Fin n) (k : Fin (n+1)) : Edge n := .inr (.inl (i,j,k))

def ez (i j : Fin (n+1)) (k : Fin n) : Edge n := .inr (.inr (i,j,k))

def tail : Edge n → Vertex n
  | .inl (i,j,k) => (i.castSucc,j,k)
  | .inr (.inl (i,j,k)) => (i,j.castSucc,k)
  | .inr (.inr (i,j,k)) => (i,j,k.castSucc)

def head : Edge n → Vertex n
  | .inl (i,j,k) => (i.succ,j,k)
  | .inr (.inl (i,j,k)) => (i,j.succ,k)
  | .inr (.inr (i,j,k)) => (i,j,k.succ)

noncomputable def boundary : (Edge n → Scalar) →ₗ[Scalar] (Vertex n → Scalar) where
  toFun z := ∑ e, z e • (Pi.single (head e) (1 : Scalar) - Pi.single (tail e) 1)
  map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [smul_smul, Finset.smul_sum]

@[simp] theorem boundary_single (e : Edge n) (z : Scalar) :
    boundary (Pi.single e z) = Pi.single (head e) z - Pi.single (tail e) z := by
  classical
  change (∑ x, (Pi.single e z : Edge n → Scalar) x •
    (Pi.single (head x) 1 - Pi.single (tail x) 1)) = _
  rw [Finset.sum_eq_single e]
  · simp [smul_sub, ← Pi.single_smul]
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

def cycle : Face n → Edge n → Scalar
  | .inl (i,j,k) => Pi.single (ex i j.castSucc k) 1 + Pi.single (ey i.succ j k) 1 -
      Pi.single (ex i j.succ k) 1 - Pi.single (ey i.castSucc j k) 1
  | .inr (.inl (i,j,k)) => Pi.single (ex i j k.castSucc) 1 + Pi.single (ez i.succ j k) 1 -
      Pi.single (ex i j k.succ) 1 - Pi.single (ez i.castSucc j k) 1
  | .inr (.inr (i,j,k)) => Pi.single (ey i j k.castSucc) 1 + Pi.single (ez i j.succ k) 1 -
      Pi.single (ey i j k.succ) 1 - Pi.single (ez i j.castSucc k) 1

@[simp] theorem boundary_cycle (f : Face n) : boundary (cycle f) = 0 := by
  rcases f with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals
    simp only [cycle, map_sub, map_add, boundary_single, head, tail, ex, ey, ez]
    abel

def gradient (φ : Vertex n → Scalar) (e : Edge n) : Scalar := φ (head e) - φ (tail e)

def curl (l : Edge n → Scalar) (f : Face n) : Scalar := ∑ e, cycle f e * l e

theorem single_mul_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (z : Scalar) (l : ι → Scalar) :
    (∑ j, (Pi.single i z : ι → Scalar) j * l j) = z * l i := by
  classical
  simp only [Pi.single_apply, ite_mul, zero_mul]
  simp

@[simp] theorem curl_xy (l : Edge n → Scalar) (i j : Fin n) (k : Fin (n+1)) :
    curl l (.inl (i,j,k)) = l (ex i j.castSucc k) + l (ey i.succ j k) -
      l (ex i j.succ k) - l (ey i.castSucc j k) := by
  classical
  simp only [curl, cycle, Pi.sub_apply, Pi.add_apply, sub_mul, add_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, single_mul_sum, one_mul]

@[simp] theorem curl_xz (l : Edge n → Scalar) (i k : Fin n) (j : Fin (n+1)) :
    curl l (.inr (.inl (i,j,k))) = l (ex i j k.castSucc) + l (ez i.succ j k) -
      l (ex i j k.succ) - l (ez i.castSucc j k) := by
  classical
  simp only [curl, cycle, Pi.sub_apply, Pi.add_apply, sub_mul, add_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, single_mul_sum, one_mul]

@[simp] theorem curl_yz (l : Edge n → Scalar) (j k : Fin n) (i : Fin (n+1)) :
    curl l (.inr (.inr (i,j,k))) = l (ey i j k.castSucc) + l (ez i j.succ k) -
      l (ey i j k.succ) - l (ez i j.castSucc k) := by
  classical
  simp only [curl, cycle, Pi.sub_apply, Pi.add_apply, sub_mul, add_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, single_mul_sum, one_mul]

@[simp] theorem curl_gradient (φ : Vertex n → Scalar) (f : Face n) :
    curl (gradient φ) f = 0 := by
  rcases f with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals simp [gradient, head, tail, ex, ey, ez]

@[simp] theorem curl_sub (l r : Edge n → Scalar) (f : Face n) :
    curl (l-r) f = curl l f - curl r f := by
  simp [curl, mul_sub, Finset.sum_sub_distrib]

def prefixSum (l : Fin n → Scalar) (i : Fin (n+1)) : Scalar :=
  ∑ a : Fin n, if a.val < i.val then l a else 0

@[simp] theorem prefix_zero (l : Fin n → Scalar) : prefixSum l 0 = 0 := by simp [prefixSum]

theorem prefix_step (l : Fin n → Scalar) (i : Fin n) :
    prefixSum l i.succ - prefixSum l i.castSucc = l i := by
  classical
  have h : prefixSum l i.succ = prefixSum l i.castSucc + l i := by
    unfold prefixSum
    have hs : (∑ a : Fin n, if a = i then l a else 0) = l i := by simp
    rw [← hs, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Fin.val_succ, Fin.val_castSucc]
    by_cases hai : a.val < i.val
    · have hne : a ≠ i := by intro h; subst a; omega
      simp [hai, hne, show a.val < i.val+1 by omega]
    · by_cases heq : a = i
      · subst a; simp
      · have hge : i.val + 1 ≤ a.val := by
          have : a.val ≠ i.val := by intro h; exact heq (Fin.ext h)
          omega
        simp [hai, heq, show ¬a.val < i.val+1 by omega]
  rw [h]
  abel

def phi1 (l : Edge n → Scalar) (v : Vertex n) : Scalar :=
  prefixSum (fun a => l (ex a v.2.1 v.2.2)) v.1

def residual1 (l : Edge n → Scalar) : Edge n → Scalar := l - gradient (phi1 l)

def phi2 (l : Edge n → Scalar) (i0 : Fin (n+1)) (v : Vertex n) : Scalar :=
  prefixSum (fun b => residual1 l (ey i0 b v.2.2)) v.2.1

def residual2 (l : Edge n → Scalar) (i0 : Fin (n+1)) : Edge n → Scalar :=
  residual1 l - gradient (phi2 l i0)

def phi3 (l : Edge n → Scalar) (i0 : Fin (n+1)) (v : Vertex n) : Scalar :=
  prefixSum (fun c => residual2 l i0 (ez i0 0 c)) v.2.2

def residual (l : Edge n → Scalar) (i0 : Fin (n+1)) : Edge n → Scalar :=
  residual2 l i0 - gradient (phi3 l i0)

@[simp] theorem residual1_x (l : Edge n → Scalar) (i : Fin n) (j k : Fin (n+1)) :
    residual1 l (ex i j k) = 0 := by
  simp only [residual1, Pi.sub_apply, gradient, head, tail, ex, phi1, prefix_step, sub_self]

@[simp] theorem residual2_x (l : Edge n → Scalar) (i0 : Fin (n+1))
    (i : Fin n) (j k : Fin (n+1)) : residual2 l i0 (ex i j k) = 0 := by
  rw [residual2, Pi.sub_apply, residual1_x]
  simp only [gradient, phi2, head, tail, ex, sub_self]

@[simp] theorem residual2_y (l : Edge n → Scalar) (i0 : Fin (n+1))
    (j : Fin n) (k : Fin (n+1)) : residual2 l i0 (ey i0 j k) = 0 := by
  simp only [residual2, Pi.sub_apply, gradient, phi2, head, tail, ey,
    prefix_step, sub_self]

@[simp] theorem residual_x (l : Edge n → Scalar) (i0 : Fin (n+1))
    (i : Fin n) (j k : Fin (n+1)) : residual l i0 (ex i j k) = 0 := by
  rw [residual, Pi.sub_apply, residual2_x]
  simp only [gradient, phi3, head, tail, ex, sub_self]

@[simp] theorem residual_y (l : Edge n → Scalar) (i0 : Fin (n+1))
    (j : Fin n) (k : Fin (n+1)) : residual l i0 (ey i0 j k) = 0 := by
  rw [residual, Pi.sub_apply, residual2_y]
  simp only [gradient, phi3, head, tail, ey, sub_self]

@[simp] theorem residual_z (l : Edge n → Scalar) (i0 : Fin (n+1))
    (k : Fin n) : residual l i0 (ez i0 0 k) = 0 := by
  simp only [residual, Pi.sub_apply, gradient, phi3, head, tail, ez,
    prefix_step, sub_self]

@[simp] theorem curl_residual (l : Edge n → Scalar) (i0 : Fin (n+1)) (f : Face n) :
    curl (residual l i0) f = curl l f := by
  simp [residual, residual2, residual1]

theorem residual_as_gradient (l : Edge n → Scalar) (i0 : Fin (n+1)) :
    residual l i0 = l - gradient (phi1 l + phi2 l i0 + phi3 l i0) := by
  funext e
  simp only [residual, residual2, residual1, Pi.sub_apply, gradient, Pi.add_apply]
  ring

theorem line_constant {g : Fin (n+1) → Scalar}
    (h : ∀ a : Fin n, g a.succ = g a.castSucc) (i j : Fin (n+1)) : g i = g j := by
  have hz : ∀ a, g a = g 0 := by
    intro a
    induction a using Fin.induction with
    | zero => rfl
    | succ a ha => exact (h a).trans ha
  exact (hz i).trans (hz j).symm

theorem residual_y_witness (l : Edge n → Scalar) (i0 i : Fin (n+1))
    (j : Fin n) (k : Fin (n+1)) (h : residual l i0 (ey i j k) ≠ 0) :
    ∃ a : Fin n, curl l (.inl (a,j,k)) ≠ 0 := by
  by_contra hn
  push Not at hn
  have hd : ∀ a : Fin n, residual l i0 (ey a.succ j k) =
      residual l i0 (ey a.castSucc j k) := by
    intro a
    have hc := curl_residual l i0 (.inl (a,j,k))
    rw [curl_xy, residual_x, residual_x, hn a] at hc
    simpa using sub_eq_zero.mp hc
  have hc := line_constant (g := fun a => residual l i0 (ey a j k)) hd i i0
  exact h (hc.trans (residual_y l i0 j k))

theorem residual_z_witness (l : Edge n → Scalar) (i0 i j : Fin (n+1))
    (k : Fin n) (h : residual l i0 (ez i j k) ≠ 0) :
    (∃ a : Fin n, curl l (.inr (.inl (a,j,k))) ≠ 0) ∨
    (∃ b : Fin n, curl l (.inr (.inr (i0,b,k))) ≠ 0) := by
  by_contra hn
  push Not at hn
  have hx : ∀ a : Fin n, residual l i0 (ez a.succ j k) =
      residual l i0 (ez a.castSucc j k) := by
    intro a
    have hc := curl_residual l i0 (.inr (.inl (a,j,k)))
    rw [curl_xz, residual_x, residual_x, hn.1 a] at hc
    simpa using sub_eq_zero.mp hc
  have hy : ∀ b : Fin n, residual l i0 (ez i0 b.succ k) =
      residual l i0 (ez i0 b.castSucc k) := by
    intro b
    have hc := curl_residual l i0 (.inr (.inr (i0,b,k)))
    rw [curl_yz, residual_y, residual_y, hn.2 b] at hc
    simpa using sub_eq_zero.mp hc
  exact h ((line_constant (g := fun a => residual l i0 (ez a j k)) hx i i0).trans ((line_constant (g := fun b => residual l i0 (ez i0 b k)) hy j 0).trans
    (residual_z l i0 k)))

def nonzeroSet {ι : Type*} [Fintype ι] (f : ι → Scalar) : Finset ι :=
  Finset.univ.filter (fun i => f i ≠ 0)

@[simp] theorem mem_nonzeroSet {ι : Type*} [Fintype ι] (f : ι → Scalar) (i : ι) :
    i ∈ nonzeroSet f ↔ f i ≠ 0 := by simp [nonzeroSet]

theorem card_le_product_of_witness {α β γ : Type*} [DecidableEq α] [Fintype β]
    (s : Finset α) (t : Finset γ) (f : β → γ → α)
    (h : ∀ x ∈ s, ∃ b c, c ∈ t ∧ f b c = x) :
    s.card ≤ Fintype.card β * t.card := by
  classical
  have hs : s ⊆ (Finset.univ ×ˢ t).image (fun p => f p.1 p.2) := by
    intro x hx
    obtain ⟨b,c,hc,hbc⟩ := h x hx
    exact Finset.mem_image.mpr ⟨(b,c), by simp [hc], hbc⟩
  calc
    s.card ≤ ((Finset.univ ×ˢ t).image (fun p => f p.1 p.2)).card := Finset.card_le_card hs
    _ ≤ (Finset.univ ×ˢ t).card := Finset.card_image_le
    _ = Fintype.card β * t.card := by simp

theorem card_le_two_products_of_witness {α β γ δ ε : Type*} [DecidableEq α]
    [Fintype β] [Fintype δ] (s : Finset α) (t : Finset γ) (u : Finset ε)
    (f : β → γ → α) (g : δ → ε → α)
    (h : ∀ x ∈ s, (∃ b c, c ∈ t ∧ f b c = x) ∨ (∃ d e, e ∈ u ∧ g d e = x)) :
    s.card ≤ Fintype.card β * t.card + Fintype.card δ * u.card := by
  classical
  let sf := (Finset.univ ×ˢ t).image (fun p => f p.1 p.2)
  let sg := (Finset.univ ×ˢ u).image (fun p => g p.1 p.2)
  have hs : s ⊆ sf ∪ sg := by
    intro x hx
    rcases h x hx with ⟨b,c,hc,hbc⟩ | ⟨d,e,he,hde⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(b,c), by simp [hc], hbc⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(d,e), by simp [he], hde⟩)
  calc
    s.card ≤ (sf ∪ sg).card := Finset.card_le_card hs
    _ ≤ sf.card + sg.card := Finset.card_union_le _ _
    _ ≤ (Finset.univ ×ˢ t).card + (Finset.univ ×ˢ u).card :=
      Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = _ := by simp

def badXY (l : Edge n → Scalar) : Finset (FaceXY n) :=
  nonzeroSet (fun f => curl l (.inl f))

def badXZ (l : Edge n → Scalar) : Finset (FaceXZ n) :=
  nonzeroSet (fun f => curl l (.inr (.inl f)))

def badYZ (l : Edge n → Scalar) : Finset (FaceYZ n) :=
  nonzeroSet (fun f => curl l (.inr (.inr f)))

def badSlice (l : Edge n → Scalar) (i : Fin (n+1)) : Finset (Fin n × Fin n) :=
  nonzeroSet (fun f => curl l (.inr (.inr (i,f))))

theorem sum_badSlice (l : Edge n → Scalar) :
    (∑ i : Fin (n+1), (badSlice l i).card) = (badYZ l).card := by
  simp only [badSlice, badYZ, nonzeroSet, Finset.card_filter, Fintype.sum_prod_type]

theorem exists_sparse_slice (l : Edge n → Scalar) :
    ∃ i0 : Fin (n+1), (n+1) * (badSlice l i0).card ≤ (badYZ l).card := by
  obtain ⟨i0, _, hi⟩ := Finset.exists_min_image Finset.univ
    (fun i : Fin (n+1) => (badSlice l i).card) (by simp)
  refine ⟨i0, ?_⟩
  calc
    (n+1) * (badSlice l i0).card = ∑ _ : Fin (n+1), (badSlice l i0).card := by simp
    _ ≤ ∑ i : Fin (n+1), (badSlice l i).card := Finset.sum_le_sum hi
    _ = _ := sum_badSlice l

theorem count_residual_y (l : Edge n → Scalar) (i0 : Fin (n+1)) :
    (nonzeroSet (fun p : EdgeY n => residual l i0 (ey p.1 p.2.1 p.2.2))).card ≤
      (n+1) * (badXY l).card := by
  have h := card_le_product_of_witness (β := Fin (n+1))
    (nonzeroSet (fun p : EdgeY n => residual l i0 (ey p.1 p.2.1 p.2.2)))
    (badXY l) (fun i f => (i,f.2.1,f.2.2)) (by
      rintro ⟨i,j,k⟩ hx
      obtain ⟨a,ha⟩ := residual_y_witness l i0 i j k (by simpa only [mem_nonzeroSet] using hx)
      exact ⟨i,(a,j,k), by simpa [badXY] using ha, rfl⟩)
  simpa only [Fintype.card_fin] using h

theorem count_residual_z (l : Edge n → Scalar) (i0 : Fin (n+1)) :
    (nonzeroSet (fun p : EdgeZ n => residual l i0 (ez p.1 p.2.1 p.2.2))).card ≤
      (n+1) * (badXZ l).card + (n+1)^2 * (badSlice l i0).card := by
  have h := card_le_two_products_of_witness (β := Fin (n+1))
    (δ := Fin (n+1) × Fin (n+1))
    (nonzeroSet (fun p : EdgeZ n => residual l i0 (ez p.1 p.2.1 p.2.2)))
    (badXZ l) (badSlice l i0) (fun i f => (i,f.2.1,f.2.2))
    (fun p f => (p.1,p.2,f.2)) (by
      rintro ⟨i,j,k⟩ hx
      rcases residual_z_witness l i0 i j k (by simpa only [mem_nonzeroSet] using hx) with ⟨a,ha⟩ | ⟨b,hb⟩
      · exact Or.inl ⟨i,(a,j,k), by simpa [badXZ] using ha, rfl⟩
      · exact Or.inr ⟨(i,j),(b,k), by simpa [badSlice] using hb, rfl⟩)
  simpa only [Fintype.card_fin, Fintype.card_prod, pow_two] using h

theorem count_curl (l : Edge n → Scalar) :
    (nonzeroSet (curl l)).card = (badXY l).card + (badXZ l).card + (badYZ l).card := by
  simp only [nonzeroSet, badXY, badXZ, badYZ, Finset.card_filter, Fintype.sum_sum_type]
  omega

theorem count_residual (l : Edge n → Scalar) (i0 : Fin (n+1)) :
    (nonzeroSet (residual l i0)).card ≤
      (n+1) * ((badXY l).card + (badXZ l).card) + (n+1)^2 * (badSlice l i0).card := by
  have heq : (nonzeroSet (residual l i0)).card =
      (nonzeroSet (fun p : EdgeY n => residual l i0 (ey p.1 p.2.1 p.2.2))).card +
      (nonzeroSet (fun p : EdgeZ n => residual l i0 (ez p.1 p.2.1 p.2.2))).card := by
    simp only [nonzeroSet, Finset.card_filter, Fintype.sum_sum_type]
    have hx : (∑ p : EdgeX n, if residual l i0 (.inl p) ≠ 0 then 1 else 0) = (0 : ℕ) := by
      apply Finset.sum_eq_zero
      rintro ⟨i,j,k⟩ _
      change (if residual l i0 (ex i j k) ≠ 0 then 1 else 0) = 0
      simp only [residual_x, ne_eq, not_true_eq_false, ite_false]
    rw [hx, zero_add]
    rfl
  rw [heq, Nat.mul_add]
  have hy := count_residual_y l i0
  have hz := count_residual_z l i0
  omega

theorem sparse_cochain (l : Edge n → Scalar) :
    ∃ φ : Vertex n → Scalar,
      (nonzeroSet (l - gradient φ)).card ≤ (n+1) * (nonzeroSet (curl l)).card := by
  obtain ⟨i0,hi⟩ := exists_sparse_slice l
  refine ⟨phi1 l + phi2 l i0 + phi3 l i0, ?_⟩
  rw [← residual_as_gradient, count_curl]
  calc
    (nonzeroSet (residual l i0)).card ≤
      (n+1) * ((badXY l).card + (badXZ l).card) + (n+1)^2 * (badSlice l i0).card :=
        count_residual l i0
    _ ≤ (n+1) * ((badXY l).card + (badXZ l).card) + (n+1) * (badYZ l).card := by
      apply Nat.add_le_add_left
      simpa only [pow_two, Nat.mul_assoc] using Nat.mul_le_mul_left (n+1) hi
    _ = _ := by ring

end CPTSeparation.Grid

end OAI
