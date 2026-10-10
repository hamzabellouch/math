import OAI.GroupTheory.PolycyclicRecognition.Lattices.RealActionIntegerLattice

namespace OAI

/-! # The integral semidirect product is the lattice in its real extension -/

noncomputable section
namespace PolycyclicRecognition
variable {H N : Type*} [Group H] [Group N]

def integerPowerAction (a : MulAut H) : Multiplicative ℤ →* MulAut H where
  toFun n := a ^ n.toAdd
  map_one' := zpow_zero a
  map_mul' n m := zpow_add a n.toAdd m.toAdd

def integerTimeHom : Multiplicative ℤ →* Multiplicative ℝ where
  toFun n := Multiplicative.ofAdd (n.toAdd : ℝ)
  map_one' := by apply Multiplicative.ext; exact Int.cast_zero
  map_mul' n m := by apply Multiplicative.ext; exact Int.cast_add _ _

theorem integerTimeHom_injective : Function.Injective integerTimeHom := by
  intro n m h
  apply Multiplicative.ext
  have he : (n.toAdd : ℝ) = (m.toAdd : ℝ) := congrArg Multiplicative.toAdd h
  exact_mod_cast he

theorem realAction_int (φ : Multiplicative ℝ →* MulAut N) (n : ℤ) :
    φ (Multiplicative.ofAdd (n : ℝ)) = φ (Multiplicative.ofAdd 1) ^ n := by
  have he : (Multiplicative.ofAdd (1 : ℝ)) ^ n = Multiplicative.ofAdd (n : ℝ) := by
    apply Multiplicative.ext
    change n • (1 : ℝ) = (n : ℝ)
    simp
  rw [← he, map_zpow]

theorem mulAut_zpow_semiconj (a : MulAut H) (b : MulAut N) (e : H → N)
    (he : ∀ x, e (a x) = b (e x)) (n : ℤ) (x : H) :
    e ((a ^ n) x) = (b ^ n) (e x) := by
  have hi (y : H) : e (a.symm y) = b.symm (e y) := by
    apply b.injective
    rw [← he, a.apply_symm_apply, b.apply_symm_apply]
  have hp (a' : MulAut H) (b' : MulAut N) (h : ∀ y, e (a' y) = b' (e y)) (k : ℕ) :
      ∀ y, e ((a' ^ k) y) = (b' ^ k) (e y) := by
    induction k with
    | zero => exact fun _ => rfl
    | succ k ih =>
      intro y
      rw [pow_succ', pow_succ']
      change e (a' ((a' ^ k) y)) = b' ((b' ^ k) (e y))
      rw [h, ih]
  cases n with
  | ofNat n => exact hp a b he n x
  | negSucc n =>
    change e ((a ^ (-((n + 1 : ℕ) : ℤ))) x) = (b ^ (-((n + 1 : ℕ) : ℤ))) (e x)
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, ← inv_pow, ← inv_pow]
    exact hp a.symm b.symm hi (n + 1) x

def realIntegerSemidirectMap (φ : Multiplicative ℝ →* MulAut N) (a : MulAut H)
    (e : H →* N) (he : ∀ x, e (a x) = φ (Multiplicative.ofAdd 1) (e x)) :
    (H ⋊[integerPowerAction a] Multiplicative ℤ) →* (N ⋊[φ] Multiplicative ℝ) :=
  SemidirectProduct.map e integerTimeHom (by
    intro n
    ext x
    change e ((a ^ n.toAdd) x) = φ (Multiplicative.ofAdd (n.toAdd : ℝ)) (e x)
    rw [realAction_int]
    exact mulAut_zpow_semiconj a _ e he n.toAdd x)

theorem realIntegerSemidirectMap_injective
    (φ : Multiplicative ℝ →* MulAut N) (a : MulAut H)
    (e : H →* N) (he : ∀ x, e (a x) = φ (Multiplicative.ofAdd 1) (e x))
    (hej : Function.Injective e) : Function.Injective (realIntegerSemidirectMap φ a e he) := by
  intro x y h
  apply SemidirectProduct.ext
  · exact hej (congrArg SemidirectProduct.left h)
  · exact integerTimeHom_injective (congrArg SemidirectProduct.right h)

variable [TopologicalSpace N]
attribute [local instance] semidirectProductTopology

theorem integer_semidirect_lattice_realization_with_coordinates
    (φ : Multiplicative ℝ →* MulAut N) (a : MulAut H)
    (Λ : Subgroup N) (hΛ : IsUniformLattice Λ) (e : H ≃* Λ)
    (he : ∀ x, (e (a x) : N) = φ (Multiplicative.ofAdd 1) (e x)) :
    ∃ Γ : Subgroup (N ⋊[φ] Multiplicative ℝ), IsUniformLattice Γ ∧
      ∃ f : (H ⋊[integerPowerAction a] Multiplicative ℤ) ≃* Γ,
        ∀ x, (f x : N ⋊[φ] Multiplicative ℝ) =
          realIntegerSemidirectMap φ a (Λ.subtype.comp e.toMonoidHom) he x := by
  let j : H →* N := Λ.subtype.comp e.toMonoidHom
  have hstable : ∀ t ∈ integerTimeLattice, ∀ x ∈ Λ, φ t x ∈ Λ := by
    intro t ht x hx
    obtain ⟨n, rfl⟩ := integerTimeLattice_exists ht
    obtain ⟨y, hy⟩ := e.surjective ⟨x, hx⟩
    have hj : j y = x := congrArg Subtype.val hy
    rw [← hj, realAction_int, ← mulAut_zpow_semiconj a _ j he]
    exact (e ((a ^ n) y)).property
  let Γ := semidirectLattice φ Λ integerTimeLattice hstable
  let f := realIntegerSemidirectMap φ a j he
  have hf (x) : f x ∈ Γ := ⟨(e x.left).property, integerTimeLattice_mem x.right.toAdd⟩
  let f' : (H ⋊[integerPowerAction a] Multiplicative ℤ) →* Γ := f.codRestrict Γ hf
  have hinj : Function.Injective f' := by
    intro x y h
    exact realIntegerSemidirectMap_injective φ a j he
      (Λ.subtype_injective.comp e.injective) (congrArg Subtype.val h)
  have hsurj : Function.Surjective f' := by
    intro z
    obtain ⟨x, hx⟩ := e.surjective ⟨z.val.left, z.property.1⟩
    obtain ⟨n, hn⟩ := integerTimeLattice_exists z.property.2
    refine ⟨⟨x, Multiplicative.ofAdd n⟩, ?_⟩
    apply Subtype.ext
    apply SemidirectProduct.ext
    · exact congrArg Subtype.val hx
    · exact hn.symm
  exact ⟨Γ, semidirectLattice_uniform φ Λ integerTimeLattice hstable hΛ
    integerTimeLattice_uniform, MulEquiv.ofBijective f' ⟨hinj, hsurj⟩, fun _ => rfl⟩

theorem integer_semidirect_lattice_realization
    (φ : Multiplicative ℝ →* MulAut N) (a : MulAut H)
    (Λ : Subgroup N) (hΛ : IsUniformLattice Λ) (e : H ≃* Λ)
    (he : ∀ x, (e (a x) : N) = φ (Multiplicative.ofAdd 1) (e x)) :
    ∃ Γ : Subgroup (N ⋊[φ] Multiplicative ℝ), IsUniformLattice Γ ∧
      Nonempty ((H ⋊[integerPowerAction a] Multiplicative ℤ) ≃* Γ) := by
  obtain ⟨Γ, hΓ, f, _⟩ :=
    integer_semidirect_lattice_realization_with_coordinates φ a Λ hΛ e he
  exact ⟨Γ, hΓ, ⟨f⟩⟩

end PolycyclicRecognition

end

end OAI
