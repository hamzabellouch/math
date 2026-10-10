import OAI.Algebra.OddKaplansky.GraphEdges

namespace OAI

section
noncomputable section
open scoped Classical
namespace OddKaplansky

abbrev LocalGroup (p M : ℕ) :=
  RegularWreathProduct (Multiplicative (ZMod M)) (Multiplicative (Fin 3 → ZMod p))

namespace LocalGroup
variable (p M : ℕ)
abbrev Point := Fin 3 → ZMod p

instance [NeZero p] [NeZero M] : Fintype (LocalGroup p M) :=
  Fintype.ofFinite _

def u : Multiplicative (Point p) →* LocalGroup p M := RegularWreathProduct.inl

def c : LocalGroup p M :=
  ⟨fun x => Multiplicative.ofAdd (if x.toAdd = 0 then 1 else 0), 1⟩

def v : Multiplicative (Point p) →* LocalGroup p M :=
  (MulAut.conj (c p M)).toMonoidHom.comp (u p M)

lemma u_injective : Function.Injective (u p M) := by
  intro x y h
  exact congrArg RegularWreathProduct.right h

lemma v_injective : Function.Injective (v p M) :=
  (MulAut.conj (c p M)).injective.comp (u_injective p M)

@[simp] lemma u_right (x : Multiplicative (Point p)) :
    (u p M x).right = x := rfl
@[simp] lemma v_right (x : Multiplicative (Point p)) :
    (v p M x).right = x := by
  simp [v, MulAut.conj_apply, c]

lemma v_left_zero (x : Multiplicative (Point p)) (hx : x ≠ 1) :
    ((v p M x).left 1).toAdd = 1 := by
  simp [v, MulAut.conj_apply, c, u, RegularWreathProduct.inl, hx]

lemma v_eq_u [NeZero M] (hM : 1 < M) (x y : Multiplicative (Point p))
    (h : v p M x = u p M y) : x = 1 ∧ y = 1 := by
  have hxy : x = y := by
    have hh := congrArg RegularWreathProduct.right h
    simpa only [v_right, u_right] using hh
  have hx : x = 1 := by
    by_contra hx
    have hh := congrArg (fun z : LocalGroup p M => (z.left 1).toAdd) h
    rw [v_left_zero p M x hx] at hh
    change (1 : ZMod M) = 0 at hh
    have hcast : M ∣ 1 := (ZMod.natCast_eq_zero_iff 1 M).mp (by simpa only [Nat.cast_one] using hh)
    exact (ne_of_gt hM) (Nat.dvd_one.mp hcast)
  exact ⟨hx, hxy.symm.trans hx⟩

def direction (j : ZMod p) : Point p := ![1, j, j^2]

def line (j : ZMod p) : ZMod p →+ Point p where
  toFun a := a • direction p j
  map_zero' := zero_smul _ _
  map_add' _ _ := add_smul _ _ _

lemma line_injective (j : ZMod p) : Function.Injective (line p j) := by
  intro a b h
  have hh := congrFun h 0
  simpa [line, direction] using hh

def edgeHom (outgoing : Bool) (j : ZMod p) :
    Multiplicative (ZMod p) →* LocalGroup p M :=
  (if outgoing then v p M else u p M).comp (line p j).toMultiplicative

lemma edgeHom_injective (outgoing : Bool) (j : ZMod p) :
    Function.Injective (edgeHom p M outgoing j) := by
  have hline : Function.Injective (line p j).toMultiplicative := line_injective p j
  cases outgoing with
  | false => exact (u_injective p M).comp hline
  | true => exact (v_injective p M).comp hline

@[simp] lemma edgeHom_right (outgoing : Bool) (j : ZMod p)
    (a : Multiplicative (ZMod p)) :
    (edgeHom p M outgoing j a).right = Multiplicative.ofAdd (line p j a.toAdd) := by
  cases outgoing <;> simp [edgeHom]

section Independence
variable [Fact p.Prime]

lemma two_directions {x y a b : ZMod p} (hxy : x ≠ y)
    (h : line p x a + line p y b = 0) : a = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [line, direction] at h0 h1
  have hz : a * (x-y) = 0 := by linear_combination h1 - y * h0
  exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hxy)

lemma three_directions {x y z a b c : ZMod p} (hxy : x ≠ y) (hxz : x ≠ z)
    (h : line p x a + line p y b + line p z c = 0) : a = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [line, direction] at h0 h1 h2
  have hz : a * ((x-y)*(x-z)) = 0 := by
    linear_combination h2 - (y+z) * h1 + y*z * h0
  exact (mul_eq_zero.mp hz).resolve_right
    (mul_ne_zero (sub_ne_zero.mpr hxy) (sub_ne_zero.mpr hxz))

lemma edge_word_one (o : Bool) (j : ZMod p) (a : Multiplicative (ZMod p))
    (ha : a ≠ 1) : edgeHom p M o j a ≠ 1 := by
  intro h
  exact ha (edgeHom_injective p M o j (h.trans (map_one _).symm))

lemma edge_word_two (o₁ o₂ : Bool) (j₁ j₂ : ZMod p)
    (a₁ a₂ : Multiplicative (ZMod p)) (ha : a₁ ≠ 1) (hj : j₁ ≠ j₂) :
    edgeHom p M o₁ j₁ a₁ * edgeHom p M o₂ j₂ a₂ ≠ 1 := by
  intro h
  have hr := congrArg (fun q : LocalGroup p M => q.right.toAdd) h
  simp only [RegularWreathProduct.mul_right, edgeHom_right, RegularWreathProduct.one_right] at hr
  change line p j₁ a₁.toAdd + line p j₂ a₂.toAdd = 0 at hr
  exact ha (congrArg Multiplicative.ofAdd (two_directions p hj hr))

lemma edge_word_three (o₁ o₂ o₃ : Bool) (j₁ j₂ j₃ : ZMod p)
    (a₁ a₂ a₃ : Multiplicative (ZMod p)) (ha : a₁ ≠ 1)
    (h₁₂ : j₁ ≠ j₂) (h₁₃ : j₁ ≠ j₃) :
    edgeHom p M o₁ j₁ a₁ * edgeHom p M o₂ j₂ a₂ * edgeHom p M o₃ j₃ a₃ ≠ 1 := by
  intro h
  have hr := congrArg (fun q : LocalGroup p M => q.right.toAdd) h
  simp only [RegularWreathProduct.mul_right, edgeHom_right, RegularWreathProduct.one_right] at hr
  change line p j₁ a₁.toAdd + line p j₂ a₂.toAdd + line p j₃ a₃.toAdd = 0 at hr
  exact ha (congrArg Multiplicative.ofAdd (three_directions p h₁₂ h₁₃ hr))

end Independence
end LocalGroup
end OddKaplansky

end
end

end OAI
