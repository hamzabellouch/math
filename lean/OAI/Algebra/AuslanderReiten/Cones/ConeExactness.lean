import OAI.Algebra.AuslanderReiten.Complete.CompleteResolution
import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Prod

namespace OAI

namespace ArExplicit

variable {R Q₁ Q₀ Q₂ P₁ P₀ P₂ : Type*} [Ring R]
variable [AddCommGroup Q₁] [Module R Q₁] [AddCommGroup Q₀] [Module R Q₀]
variable [AddCommGroup Q₂] [Module R Q₂] [AddCommGroup P₁] [Module R P₁]
variable [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₂] [Module R P₂]

def coneBlock (dQ : Q₀ →ₗ[R] Q₂) (dP : P₀ →ₗ[R] P₂) (f : P₀ →ₗ[R] Q₂) :
    (Q₀ × P₀) →ₗ[R] (Q₂ × P₂) :=
  (dQ.coprod f).prod ((-dP).comp (LinearMap.snd R Q₀ P₀))

@[simp] theorem coneBlock_apply (dQ : Q₀ →ₗ[R] Q₂) (dP : P₀ →ₗ[R] P₂)
    (f : P₀ →ₗ[R] Q₂) (x : Q₀) (y : P₀) :
    coneBlock dQ dP f (x, y) = (dQ x + f y, -dP y) := rfl

theorem coneBlock_comp_zero (eQ : Q₁ →ₗ[R] Q₀) (dQ : Q₀ →ₗ[R] Q₂)
    (eP : P₁ →ₗ[R] P₀) (dP : P₀ →ₗ[R] P₂)
    (f₁ : P₁ →ₗ[R] Q₀) (f₀ : P₀ →ₗ[R] Q₂)
    (hQ : dQ.comp eQ = 0) (hP : dP.comp eP = 0)
    (hf : dQ.comp f₁ = f₀.comp eP) :
    (coneBlock dQ dP f₀).comp (coneBlock eQ eP f₁) = 0 := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  apply Prod.ext
  · change dQ (eQ x + f₁ y) + f₀ (-eP y) = 0
    rw [map_add, show dQ (eQ x) = 0 from DFunLike.congr_fun hQ x, zero_add,
      show dQ (f₁ y) = f₀ (eP y) from DFunLike.congr_fun hf y, map_neg, add_neg_cancel]
  · change -dP (-eP y) = 0
    rw [map_neg, neg_neg]
    exact DFunLike.congr_fun hP y

theorem coneBlock_exact (eQ : Q₁ →ₗ[R] Q₀) (dQ : Q₀ →ₗ[R] Q₂)
    (eP : P₁ →ₗ[R] P₀) (dP : P₀ →ₗ[R] P₂)
    (f₁ : P₁ →ₗ[R] Q₀) (f₀ : P₀ →ₗ[R] Q₂)
    (hQ : Function.Exact eQ dQ) (hP : Function.Exact eP dP)
    (hf : dQ.comp f₁ = f₀.comp eP) :
    Function.Exact (coneBlock eQ eP f₁) (coneBlock dQ dP f₀) := by
  rintro ⟨x, y⟩
  constructor
  · intro hz
    have hy : dP y = 0 := neg_eq_zero.mp (congrArg Prod.snd hz)
    obtain ⟨v, hv⟩ := (hP y).mp hy
    have hx : dQ (x + f₁ v) = 0 := by
      have hxy : dQ x + f₀ y = 0 := congrArg Prod.fst hz
      rw [map_add, show dQ (f₁ v) = f₀ (eP v) from DFunLike.congr_fun hf v, hv, hxy]
    obtain ⟨u, hu⟩ := (hQ (x + f₁ v)).mp hx
    refine ⟨(u, -v), ?_⟩
    simp [coneBlock_apply, hu, hv]
  · rintro ⟨⟨u, v⟩, huv⟩
    rw [← huv]
    apply Prod.ext
    · change dQ (eQ u + f₁ v) + f₀ (-eP v) = 0
      rw [map_add, (hQ (eQ u)).mpr ⟨u, rfl⟩, zero_add,
        show dQ (f₁ v) = f₀ (eP v) from DFunLike.congr_fun hf v, map_neg, add_neg_cancel]
    · change -dP (-eP v) = 0
      rw [map_neg, neg_neg, (hP (eP v)).mpr ⟨v, rfl⟩]

theorem coneBlock_homExact (eQ : Q₁ →ₗ[R] Q₀) (dQ : Q₀ →ₗ[R] Q₂)
    (eP : P₁ →ₗ[R] P₀) (dP : P₀ →ₗ[R] P₂)
    (f₁ : P₁ →ₗ[R] Q₀) (f₀ : P₀ →ₗ[R] Q₂)
    (hQ : HomExactAt eQ dQ) (hP : HomExactAt eP dP)
    (hf : dQ.comp f₁ = f₀.comp eP) :
    HomExactAt (coneBlock eQ eP f₁) (coneBlock dQ dP f₀) := by
  intro g hg
  let a := g.comp (LinearMap.inl R Q₀ P₀)
  let b := g.comp (LinearMap.inr R Q₀ P₀)
  have ha : a.comp eQ = 0 := by
    ext x
    have h := DFunLike.congr_fun hg (x, 0)
    simpa [coneBlock, a] using h
  obtain ⟨u, hu⟩ := hQ a ha
  have hb : (b - u.comp f₀).comp eP = 0 := by
    ext y
    have h := DFunLike.congr_fun hg (0, y)
    have hab : a (f₁ y) = b (eP y) := by
      have hsplit : g (f₁ y, -eP y) = a (f₁ y) - b (eP y) := by
        rw [show (f₁ y, -eP y) = (f₁ y, 0) + (0, -eP y) by ext <;> simp]
        rw [map_add]
        change a (f₁ y) + b (-eP y) = _
        rw [map_neg, sub_eq_add_neg]
      apply sub_eq_zero.mp
      rw [← hsplit]
      simpa [coneBlock] using h
    change b (eP y) - u (f₀ (eP y)) = 0
    rw [← show dQ (f₁ y) = f₀ (eP y) from DFunLike.congr_fun hf y,
      show u (dQ (f₁ y)) = a (f₁ y) from DFunLike.congr_fun hu (f₁ y), hab, sub_self]
  obtain ⟨v, hv⟩ := hP (b - u.comp f₀) hb
  refine ⟨u.coprod (-v), ?_⟩
  apply LinearMap.ext
  rintro ⟨x, y⟩
  change u (dQ x + f₀ y) + -v (-dP y) = g (x, y)
  rw [map_add, map_neg, neg_neg,
    show u (dQ x) = a x from DFunLike.congr_fun hu x,
    show v (dP y) = b y - u (f₀ y) from DFunLike.congr_fun hv y]
  have hsplit : a x + b y = g (x, y) := by
    change g (x, 0) + g (0, y) = _
    rw [← map_add]
    simp
  rw [← hsplit]
  abel

end ArExplicit

end OAI
