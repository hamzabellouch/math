import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicSquareIndex

namespace OAI

/-! # Finite-index cyclic subgroups for an arbitrary positive power -/

noncomputable section
namespace PolycyclicRecognition
variable {H : Type} [Group H]

def integerScaleHom (m : ℕ) : Multiplicative ℤ →* Multiplicative ℤ where
  toFun n := Multiplicative.ofAdd ((m : ℤ) * n.toAdd)
  map_one' := by apply Multiplicative.ext; simp
  map_mul' n k := by apply Multiplicative.ext; exact mul_add _ n.toAdd k.toAdd

theorem integerScaleHom_injective {m : ℕ} (hm : 0 < m) :
    Function.Injective (integerScaleHom m) := by
  intro n k h
  apply Multiplicative.ext
  have he := congrArg Multiplicative.toAdd h
  change (m : ℤ) * n.toAdd = (m : ℤ) * k.toAdd at he
  exact mul_left_cancel₀ (by exact_mod_cast Nat.ne_of_gt hm) he

theorem integerScaleHom_range_finiteIndex {m : ℕ} (hm : 0 < m) :
    (integerScaleHom m).range.FiniteIndex := by
  let g := Multiplicative.ofAdd (1 : ℤ)
  have hg : Subgroup.zpowers g = ⊤ := by
    apply top_unique
    intro z _
    refine ⟨z.toAdd, ?_⟩
    apply Multiplicative.ext
    simp [g]
  have hr : (integerScaleHom m).range = Subgroup.zpowers (g ^ (m : ℤ)) := by
    rw [MonoidHom.range_eq_map, ← hg, MonoidHom.map_zpowers]
    congr 1
  refine ⟨?_⟩
  rw [hr, Subgroup.index_zpowers_zpow hg]
  exact ne_of_gt (Int.gcd_pos_of_ne_zero_left (orderOf g)
    (by exact_mod_cast Nat.ne_of_gt hm))

def cyclicPowerMap (a : MulAut H) (m : ℕ) :
    (H ⋊[integerPowerAction (a ^ m)] Multiplicative ℤ) →*
      (H ⋊[integerPowerAction a] Multiplicative ℤ) :=
  SemidirectProduct.map (MonoidHom.id H) (integerScaleHom m) (by
    intro n
    ext x
    change ((a ^ m) ^ n.toAdd) x = (a ^ ((m : ℤ) * n.toAdd)) x
    rw [← zpow_natCast a m, ← zpow_mul])

theorem cyclicPowerMap_injective (a : MulAut H) {m : ℕ} (hm : 0 < m) :
    Function.Injective (cyclicPowerMap a m) := by
  intro x y h
  apply SemidirectProduct.ext
  · exact congrArg (fun z : H ⋊[integerPowerAction a] Multiplicative ℤ => z.left) h
  · exact integerScaleHom_injective hm
      (congrArg (fun z : H ⋊[integerPowerAction a] Multiplicative ℤ => z.right) h)

theorem cyclicPowerMap_range (a : MulAut H) (m : ℕ) :
    (cyclicPowerMap a m).range =
      (integerScaleHom m).range.comap SemidirectProduct.rightHom := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.right, rfl⟩
  · rintro ⟨n, hn⟩
    refine ⟨⟨g.left, n⟩, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact hn

theorem cyclicPowerMap_range_finiteIndex (a : MulAut H) {m : ℕ} (hm : 0 < m) :
    (cyclicPowerMap a m).range.FiniteIndex := by
  let := integerScaleHom_range_finiteIndex hm
  rw [cyclicPowerMap_range]
  infer_instance

def cyclicPowerRangeEquiv (a : MulAut H) {m : ℕ} (hm : 0 < m) :
    (H ⋊[integerPowerAction (a ^ m)] Multiplicative ℤ) ≃* (cyclicPowerMap a m).range :=
  MulEquiv.ofBijective (cyclicPowerMap a m).rangeRestrict ⟨by
    intro x y h
    exact cyclicPowerMap_injective a hm (congrArg Subtype.val h), by
    rintro ⟨g, x, rfl⟩
    exact ⟨x, rfl⟩⟩

end PolycyclicRecognition

end

end OAI
