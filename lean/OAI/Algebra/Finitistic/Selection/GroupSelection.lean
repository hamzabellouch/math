import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

namespace OAI
/-! Group identities used in Section 2 of v5s9.15. -/

open scoped commutatorElement

namespace LittleFinitistic

section GroupTransfer

variable {G : Type*} [Group G]

/-- The commutator transfer identity establishing independence of the
internal index in the paper's central involutions. -/
theorem commutator_transfer (x y v u w : G)
    (hu : x*y = u*y*x) (hw : y*v = w*v*y)
    (hxv : Commute x v) (hwu : Commute w u) (hwv : Commute w v) :
    ⁅x,w⁆ = ⁅u,v⁆ := by
  have hconj : y*x*y⁻¹ = u⁻¹*x := by
    apply (mul_left_cancel_iff (a := u)).mp
    calc
      u*(y*x*y⁻¹) = (u*y*x)*y⁻¹ := by group
      _ = (x*y)*y⁻¹ := by rw [← hu]
      _ = u*(u⁻¹*x) := by group
  have hmove : x*w*v*y = u*w*v*y*x := by
    calc
      x*w*v*y = x*(y*v) := by rw [hw]; group
      _ = (x*y)*v := by group
      _ = (u*y*x)*v := by rw [hu]
      _ = u*y*(v*x) := by simp only [mul_assoc, hxv.eq]
      _ = u*(y*v)*x := by group
      _ = u*w*v*y*x := by rw [hw]; group
  have hxw : x*w = u*w*v*u⁻¹*v⁻¹*x := by
    calc
      x*w = (x*w*v*y)*y⁻¹*v⁻¹ := by group
      _ = (u*w*v*y*x)*y⁻¹*v⁻¹ := by rw [hmove]
      _ = u*w*v*(y*x*y⁻¹)*v⁻¹ := by group
      _ = u*w*v*(u⁻¹*x)*v⁻¹ := by rw [hconj]
      _ = u*w*v*u⁻¹*(v⁻¹*x) := by simp only [mul_assoc]; rw [hxv.inv_right.eq]
      _ = u*w*v*u⁻¹*v⁻¹*x := by group
  have hwc : Commute w (v*u⁻¹*v⁻¹) := by
    simpa only [mul_assoc] using hwv.mul_right (hwu.inv_right.mul_right hwv.inv_right)
  calc
    ⁅x,w⁆ = x*w*x⁻¹*w⁻¹ := rfl
    _ = u*w*v*u⁻¹*v⁻¹*w⁻¹ := by rw [hxw]; group
    _ = u*(w*(v*u⁻¹*v⁻¹))*w⁻¹ := by group
    _ = u*((v*u⁻¹*v⁻¹)*w)*w⁻¹ := by rw [hwc.eq]
    _ = ⁅u,v⁆ := by simp only [commutatorElement_def]; group

/-- A central commutator of an involution has order dividing two. -/
theorem central_commutator_involution (x y : G) (hx : x*x = 1)
    (hc : Commute x ⁅x,y⁆) : ⁅x,y⁆ * ⁅x,y⁆ = 1 := by
  calc
    ⁅x,y⁆ * ⁅x,y⁆ = x * ⁅x,y⁆ * x⁻¹ * ⁅x,y⁆ := by rw [hc.eq]; group
    _ = ⁅x*x,y⁆ := (commutatorElement_mul_left_eq_conj_mul x x y).symm
    _ = 1 := by rw [hx]; exact commutatorElement_one_left y

end GroupTransfer

/-- The relators used for the off-diagonal generators in Section 2. The
presentation and its finite-presentation reduction are separate obligations. -/
structure SelectionGroupData (G : Type*) [Group G] where
  T : Fin 3 → G
  U : Fin 3 → ℤ → G
  V : Fin 3 → ℤ → G
  W : Fin 3 → Fin 3 → ℤ → G
  square_U : ∀ i a, U i a * U i a = 1
  commute_UU : ∀ i j a b, i ≠ j → Commute (U i a) (U j b)
  commute_VV : ∀ i j a b, i ≠ j → Commute (V i a) (V j b)
  commute_UV : ∀ i j a b, i ≠ j → Commute (U i a) (V j b)
  commute_WU : ∀ i j h a b, h ≠ i → Commute (W i j a) (U h b)
  commute_WV : ∀ i j h a b, h ≠ j → Commute (W i j a) (V h b)
  commutator_UW : ∀ i j a b, i ≠ j → ⁅U i a, W i j b⁆ = U j (a+b)
  commutator_WV : ∀ i j a b, i ≠ j → ⁅W i j a, V j b⁆ = V i (a+b)
  commute_TT : ∀ i j, Commute (T i) (T j)
  conj_TU : ∀ l i a, T l * U i a * (T l)⁻¹ = U i (a - if l=i then 1 else 0)
  conj_TV : ∀ l i a, T l * V i a * (T l)⁻¹ = V i (a + if l=i then 1 else 0)
  conj_TW : ∀ l i j a, T l * W i j a * (T l)⁻¹ =
    W i j (a + (if l=i then 1 else 0) - if l=j then 1 else 0)
  diagonal_W : ∀ i a, W i i a = 1

namespace SelectionGroupData

variable {G : Type*} [Group G] (D : SelectionGroupData G)

theorem split_transfer (i j : Fin 3) (a b c d : ℤ)
    (hij : i ≠ j) (hsum : a+b = c+d) :
    ⁅D.U i a, D.V i b⁆ = ⁅D.U j c, D.V j d⁆ := by
  have hU : D.U i a * D.W i j (c-a) =
      D.U j c * D.W i j (c-a) * D.U i a := by
    have h := D.commutator_UW i j a (c-a) hij
    have hc : a + (c-a) = c := by omega
    rw [hc] at h
    rw [← h]
    simp [commutatorElement_def, mul_assoc]
  have hV : D.W i j (c-a) * D.V j d =
      D.V i b * D.V j d * D.W i j (c-a) := by
    have h := D.commutator_WV i j (c-a) d hij
    have hb : c-a+d = b := by omega
    rw [hb] at h
    rw [← h]
    simp [commutatorElement_def, mul_assoc]
  exact commutator_transfer (D.U i a) (D.W i j (c-a)) (D.V j d)
    (D.U j c) (D.V i b) hU hV (D.commute_UV i j a d hij)
    (D.commute_UV j i c b hij.symm).symm (D.commute_VV i j b d hij)

theorem splitting_independent (i j : Fin 3) (a b c d : ℤ)
    (hsum : a+b = c+d) : ⁅D.U i a,D.V i b⁆ = ⁅D.U j c,D.V j d⁆ := by
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide)
  calc
    ⁅D.U i a,D.V i b⁆ = ⁅D.U k 0,D.V k (a+b)⁆ :=
      D.split_transfer i k a b 0 (a+b) hki.symm (by omega)
    _ = ⁅D.U j c,D.V j d⁆ :=
      D.split_transfer k j 0 (a+b) c d hkj (by omega)

def centralZ (N : ℤ) : G := ⁅D.U 0 0,D.V 0 N⁆

theorem centralZ_eq (N : ℤ) (i : Fin 3) (a b : ℤ) (h : a+b=N) :
    D.centralZ N = ⁅D.U i a,D.V i b⁆ := by
  exact D.splitting_independent 0 i 0 N a b (by omega)

theorem centralZ_commute_U (N : ℤ) (h : Fin 3) (a : ℤ) :
    Commute (D.centralZ N) (D.U h a) := by
  obtain ⟨i, hih, _⟩ := Fin.exists_ne_and_ne_of_two_lt h h (by decide)
  rw [D.centralZ_eq N i 0 N (by omega), commutatorElement_def]
  have hU := D.commute_UU i h 0 a hih
  have hV := (D.commute_UV h i a N hih.symm).symm
  exact ((hU.mul_left hV).mul_left hU.inv_left).mul_left hV.inv_left

theorem centralZ_commute_V (N : ℤ) (h : Fin 3) (a : ℤ) :
    Commute (D.centralZ N) (D.V h a) := by
  obtain ⟨i, hih, _⟩ := Fin.exists_ne_and_ne_of_two_lt h h (by decide)
  rw [D.centralZ_eq N i 0 N (by omega), commutatorElement_def]
  have hU := D.commute_UV i h 0 a hih
  have hV := D.commute_VV i h N a hih
  exact ((hU.mul_left hV).mul_left hU.inv_left).mul_left hV.inv_left

theorem centralZ_commute_W (N : ℤ) (i j : Fin 3) (a : ℤ) :
    Commute (D.centralZ N) (D.W i j a) := by
  obtain ⟨h, hhi, hhj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide)
  rw [D.centralZ_eq N h 0 N (by omega), commutatorElement_def]
  have hU := (D.commute_WU i j h a 0 hhi).symm
  have hV := (D.commute_WV i j h a N hhj).symm
  exact ((hU.mul_left hV).mul_left hU.inv_left).mul_left hV.inv_left

theorem centralZ_involution (N : ℤ) : D.centralZ N * D.centralZ N = 1 := by
  apply central_commutator_involution (D.U 0 0) (D.V 0 N) (D.square_U 0 0)
  exact (D.centralZ_commute_U N 0 0).symm

theorem centralZ_commute_T (N : ℤ) (l : Fin 3) : Commute (D.centralZ N) (D.T l) := by
  have hconj : D.T l * D.centralZ N * (D.T l)⁻¹ = D.centralZ N := by
    rw [centralZ, conjugate_commutatorElement, D.conj_TU, D.conj_TV]
    exact (D.centralZ_eq N 0 _ _ (by omega)).symm
  show D.centralZ N * D.T l = D.T l * D.centralZ N
  calc
    D.centralZ N * D.T l = (D.T l * D.centralZ N * (D.T l)⁻¹) * D.T l := by rw [hconj]
    _ = D.T l * D.centralZ N := by group

end SelectionGroupData

namespace Presentation

inductive Generator where
  | T : Fin 3 → Generator
  | U : Fin 3 → ℤ → Generator
  | V : Fin 3 → ℤ → Generator
  | W : Fin 3 → Fin 3 → ℤ → Generator

private abbrev t (i : Fin 3) := FreeGroup.of (Generator.T i)
private abbrev u (i : Fin 3) (a : ℤ) := FreeGroup.of (Generator.U i a)
private abbrev v (i : Fin 3) (a : ℤ) := FreeGroup.of (Generator.V i a)
private abbrev w (i j : Fin 3) (a : ℤ) := FreeGroup.of (Generator.W i j a)

/-- Explicit equation patterns of the paper's infinite presentation.
Diagonal W generators are set to one, so the total-index notation introduces
no additional group generators compared with the manuscript. -/
inductive Equation : FreeGroup Generator → FreeGroup Generator → Prop where
  | squareU (i a) : Equation (u i a * u i a) 1
  | commuteUU (i j a b) (h : i ≠ j) : Equation (u i a * u j b) (u j b * u i a)
  | commuteVV (i j a b) (h : i ≠ j) : Equation (v i a * v j b) (v j b * v i a)
  | commuteUV (i j a b) (h : i ≠ j) : Equation (u i a * v j b) (v j b * u i a)
  | commuteWU (i j h a b) (hhi : h ≠ i) : Equation (w i j a * u h b) (u h b * w i j a)
  | commuteWV (i j h a b) (hhj : h ≠ j) : Equation (w i j a * v h b) (v h b * w i j a)
  | commutatorUW (i j a b) (h : i ≠ j) : Equation ⁅u i a,w i j b⁆ (u j (a+b))
  | commutatorWV (i j a b) (h : i ≠ j) : Equation ⁅w i j a,v j b⁆ (v i (a+b))
  | commuteTT (i j) : Equation (t i * t j) (t j * t i)
  | conjTU (l i a) : Equation (t l * u i a * (t l)⁻¹) (u i (a-if l=i then 1 else 0))
  | conjTV (l i a) : Equation (t l * v i a * (t l)⁻¹) (v i (a+if l=i then 1 else 0))
  | conjTW (l i j a) : Equation (t l * w i j a * (t l)⁻¹)
      (w i j (a+(if l=i then 1 else 0)-if l=j then 1 else 0))
  | diagonalW (i a) : Equation (w i i a) 1

def relators : Set (FreeGroup Generator) := {r | ∃ a b, Equation a b ∧ r=a*b⁻¹}
abbrev AuxiliaryGroup := PresentedGroup relators

private theorem equation_holds {a b : FreeGroup Generator} (h : Equation a b) :
    PresentedGroup.mk relators a = PresentedGroup.mk relators b :=
  PresentedGroup.mk_eq_mk_of_mul_inv_mem ⟨a,b,h,rfl⟩

def data : SelectionGroupData AuxiliaryGroup where
  T i := PresentedGroup.of (.T i)
  U i a := PresentedGroup.of (.U i a)
  V i a := PresentedGroup.of (.V i a)
  W i j a := PresentedGroup.of (.W i j a)
  square_U i a := by simpa [u, PresentedGroup.of] using equation_holds (.squareU i a)
  commute_UU i j a b h := by
    simpa [u, PresentedGroup.of, Commute, SemiconjBy] using equation_holds (.commuteUU i j a b h)
  commute_VV i j a b h := by
    simpa [v, PresentedGroup.of, Commute, SemiconjBy] using equation_holds (.commuteVV i j a b h)
  commute_UV i j a b h := by
    simpa [u,v, PresentedGroup.of, Commute, SemiconjBy] using equation_holds (.commuteUV i j a b h)
  commute_WU i j h a b hhi := by
    simpa [w,u, PresentedGroup.of, Commute, SemiconjBy] using equation_holds (.commuteWU i j h a b hhi)
  commute_WV i j h a b hhj := by
    simpa [w,v, PresentedGroup.of, Commute, SemiconjBy] using equation_holds (.commuteWV i j h a b hhj)
  commutator_UW i j a b h := by
    simpa [u,w, PresentedGroup.of] using equation_holds (.commutatorUW i j a b h)
  commutator_WV i j a b h := by
    simpa [w,v, PresentedGroup.of] using equation_holds (.commutatorWV i j a b h)
  commute_TT i j := by
    simpa [t, PresentedGroup.of, Commute, SemiconjBy] using equation_holds (.commuteTT i j)
  conj_TU l i a := by simpa [t,u,PresentedGroup.of] using equation_holds (.conjTU l i a)
  conj_TV l i a := by simpa [t,v,PresentedGroup.of] using equation_holds (.conjTV l i a)
  conj_TW l i j a := by simpa [t,w,PresentedGroup.of] using equation_holds (.conjTW l i j a)
  diagonal_W i a := by simpa [w,PresentedGroup.of] using equation_holds (.diagonalW i a)

def z (N : ℤ) : AuxiliaryGroup := data.centralZ N

theorem z_involution (N : ℤ) : z N * z N = 1 := data.centralZ_involution N

theorem z_central (N : ℤ) (g : AuxiliaryGroup) : Commute (z N) g := by
  have hg : g ∈ Subgroup.closure (Set.range (PresentedGroup.of : Generator → AuxiliaryGroup)) := by
    rw [PresentedGroup.closure_range_of]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      obtain ⟨s,rfl⟩ := hg
      cases s with
      | T i => exact data.centralZ_commute_T N i
      | U i a => exact data.centralZ_commute_U N i a
      | V i a => exact data.centralZ_commute_V N i a
      | W i j a => exact data.centralZ_commute_W N i j a
  | one => exact Commute.one_right _
  | mul a b ha hb ia ib => exact ia.mul_right ib
  | inv a ha ia => exact ia.inv_right

def evaluate {G : Type*} [Group G] (D : SelectionGroupData G) : Generator → G
  | .T i => D.T i
  | .U i a => D.U i a
  | .V i a => D.V i a
  | .W i j a => D.W i j a

theorem evaluate_equation {G : Type*} [Group G] (D : SelectionGroupData G)
    {a b : FreeGroup Generator} (h : Equation a b) :
    FreeGroup.lift (evaluate D) a = FreeGroup.lift (evaluate D) b := by
  cases h with
  | squareU i a => simpa [u,evaluate] using D.square_U i a
  | commuteUU i j a b h => simpa [u,evaluate] using (D.commute_UU i j a b h).eq
  | commuteVV i j a b h => simpa [v,evaluate] using (D.commute_VV i j a b h).eq
  | commuteUV i j a b h => simpa [u,v,evaluate] using (D.commute_UV i j a b h).eq
  | commuteWU i j h a b hh => simpa [w,u,evaluate] using (D.commute_WU i j h a b hh).eq
  | commuteWV i j h a b hh => simpa [w,v,evaluate] using (D.commute_WV i j h a b hh).eq
  | commutatorUW i j a b h => simpa [u,w,evaluate] using D.commutator_UW i j a b h
  | commutatorWV i j a b h => simpa [w,v,evaluate] using D.commutator_WV i j a b h
  | commuteTT i j => simpa [t,evaluate] using (D.commute_TT i j).eq
  | conjTU l i a => simpa [t,u,evaluate] using D.conj_TU l i a
  | conjTV l i a => simpa [t,v,evaluate] using D.conj_TV l i a
  | conjTW l i j a => simpa [t,w,evaluate] using D.conj_TW l i j a
  | diagonalW i a => simpa [w,evaluate] using D.diagonal_W i a

def ofData {G : Type*} [Group G] (D : SelectionGroupData G) : AuxiliaryGroup →* G :=
  PresentedGroup.toGroup (f := evaluate D) (by
    intro r hr
    obtain ⟨a,b,h,rfl⟩ := hr
    rw [map_mul,map_inv,evaluate_equation D h,mul_inv_cancel])

@[simp] theorem ofData_of {G : Type*} [Group G] (D : SelectionGroupData G) (s : Generator) :
    ofData D (PresentedGroup.of s) = evaluate D s := PresentedGroup.toGroup.of _

def shiftData {G : Type*} [Group G] (D : SelectionGroupData G) (k : ℤ) :
    SelectionGroupData G where
  T := D.T
  U i a := D.U i (a+k)
  V := D.V
  W := D.W
  square_U i a := D.square_U i (a+k)
  commute_UU i j a b h := D.commute_UU i j (a+k) (b+k) h
  commute_VV := D.commute_VV
  commute_UV i j a b h := D.commute_UV i j (a+k) b h
  commute_WU i j h a b hh := D.commute_WU i j h a (b+k) hh
  commute_WV := D.commute_WV
  commutator_UW i j a b h := by
    simpa only [add_assoc,add_comm k b] using D.commutator_UW i j (a+k) b h
  commutator_WV := D.commutator_WV
  commute_TT := D.commute_TT
  conj_TU l i a := by
    simpa only [add_sub_assoc,sub_add_eq_add_sub] using D.conj_TU l i (a+k)
  conj_TV := D.conj_TV
  conj_TW := D.conj_TW
  diagonal_W := D.diagonal_W

def shiftHom (k : ℤ) : AuxiliaryGroup →* AuxiliaryGroup := ofData (shiftData data k)

@[simp] theorem shiftHom_T (k : ℤ) (i : Fin 3) : shiftHom k (data.T i) = data.T i := by
  simp [shiftHom,data,shiftData,evaluate]

@[simp] theorem shiftHom_U (k : ℤ) (i : Fin 3) (a : ℤ) :
    shiftHom k (data.U i a) = data.U i (a+k) := by
  simp [shiftHom,data,shiftData,evaluate]

@[simp] theorem shiftHom_V (k : ℤ) (i : Fin 3) (a : ℤ) :
    shiftHom k (data.V i a) = data.V i a := by
  simp [shiftHom,data,shiftData,evaluate]

@[simp] theorem shiftHom_W (k : ℤ) (i j : Fin 3) (a : ℤ) :
    shiftHom k (data.W i j a) = data.W i j a := by
  simp [shiftHom,data,shiftData,evaluate]

theorem shiftHom_comp (k l : ℤ) : (shiftHom k).comp (shiftHom l) = shiftHom (l+k) := by
  apply PresentedGroup.ext
  intro s
  cases s <;> simp [MonoidHom.comp_apply,shiftHom,shiftData,data,evaluate,add_assoc]

theorem shiftHom_zero : shiftHom 0 = MonoidHom.id AuxiliaryGroup := by
  apply PresentedGroup.ext
  intro s
  cases s <;> simp [shiftHom,shiftData,data,evaluate]

def shiftAut (k : ℤ) : AuxiliaryGroup ≃* AuxiliaryGroup where
  toFun := shiftHom k
  invFun := shiftHom (-k)
  left_inv a := by
    have h := DFunLike.congr_fun (shiftHom_comp (-k) k) a
    simpa only [add_neg_cancel,shiftHom_zero,MonoidHom.id_apply,MonoidHom.comp_apply] using h
  right_inv a := by
    have h := DFunLike.congr_fun (shiftHom_comp k (-k)) a
    simpa only [neg_add_cancel,shiftHom_zero,MonoidHom.id_apply,MonoidHom.comp_apply] using h
  map_mul' := (shiftHom k).map_mul

theorem shiftAut_z (k N : ℤ) : shiftAut k (z N) = z (N+k) := by
  change shiftHom k ⁅data.U 0 0,data.V 0 N⁆ = data.centralZ (N+k)
  rw [map_commutatorElement,shiftHom_U,shiftHom_V,zero_add]
  exact (data.centralZ_eq (N+k) 0 k N (by omega)).symm

end Presentation

end LittleFinitistic

end OAI
