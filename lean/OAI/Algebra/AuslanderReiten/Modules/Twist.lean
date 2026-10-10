import OAI.Algebra.AuslanderReiten.Algebras.TrivialExtension

namespace OAI

namespace ArExplicit.TrivialExtension

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

def twist (h : kˣ) : TrivialExtension k A ≃ₐ[k] TrivialExtension k A where
  toFun a := ⟨a.base, (h : k) • a.dual⟩
  invFun a := ⟨a.base, (↑h⁻¹ : k) • a.dual⟩
  left_inv a := by
    apply TrivialExtension.ext
    · rfl
    · simp [smul_smul]
  right_inv a := by
    apply TrivialExtension.ext
    · rfl
    · simp [smul_smul]
  map_add' a b := by
    apply TrivialExtension.ext
    · rfl
    · exact smul_add _ _ _
  map_mul' a b := by
    apply TrivialExtension.ext
    · rfl
    · ext c
      change (h : k) * (b.dual (c * a.base) + a.dual (b.base * c)) =
        (h : k) * b.dual (c * a.base) + (h : k) * a.dual (b.base * c)
      exact mul_add _ _ _
  commutes' c := by
    apply TrivialExtension.ext
    · rfl
    · change (h : k) • (algebraMap k (TrivialExtension k A) c).dual =
        (algebraMap k (TrivialExtension k A) c).dual
      simp only [Algebra.algebraMap_eq_smul_one, dual_smul, dual_one, smul_zero]

@[simp] theorem twist_base (h : kˣ) (a : TrivialExtension k A) :
    (twist h a).base = a.base := rfl

@[simp] theorem twist_dual (h : kˣ) (a : TrivialExtension k A) :
    (twist h a).dual = (h : k) • a.dual := rfl

@[simp] theorem twist_inl (h : kˣ) (a : A) : twist h (inl a) = inl a := by
  apply TrivialExtension.ext
  · rfl
  · exact smul_zero _

@[simp] theorem twist_inr (h : kˣ) (φ : Module.Dual k A) :
    twist h (inr φ) = inr ((h : k) • φ) := rfl

theorem trace_twist (h : kˣ) (a : TrivialExtension k A) :
    trace (twist h a) = (h : k) * trace a := rfl

theorem twist_mul (g h : kˣ) (a : TrivialExtension k A) :
    twist (g * h) a = twist g (twist h a) := by
  apply TrivialExtension.ext
  · rfl
  · exact mul_smul _ _ _

end ArExplicit.TrivialExtension

end OAI
