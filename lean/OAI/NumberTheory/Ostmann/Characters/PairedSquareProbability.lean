import OAI.NumberTheory.Ostmann.Arithmetic.CompositeSquareRootsDensity
import OAI.NumberTheory.Ostmann.Characters.HaarCounting

namespace OAI

noncomputable section
namespace Ostmann.Characters

def pairUnitsReduction (m n : ℕ) :
    (ZMod (m.lcm n))ˣ →* (ZMod m)ˣ × (ZMod n)ˣ :=
  (ZMod.unitsMap (Nat.dvd_lcm_left m n)).prod
    (ZMod.unitsMap (Nat.dvd_lcm_right m n))

theorem pairUnitsReduction_injective (m n : ℕ) :
    Function.Injective (pairUnitsReduction m n) := by
  intro x y h
  apply Units.ext
  apply (ZMod.castHom_injective (R:=ZMod m × ZMod n))
  have hr : ZMod.castHom (dvd_refl (m.lcm n)) (ZMod m × ZMod n) =
      (ZMod.castHom (Nat.dvd_lcm_left m n) (ZMod m)).prod
        (ZMod.castHom (Nat.dvd_lcm_right m n) (ZMod n)) := Subsingleton.elim _ _
  rw [hr]
  apply Prod.ext
  · exact congrArg (fun z => (z.1 : ZMod m)) h
  · exact congrArg (fun z => (z.2 : ZMod n)) h

theorem paired_square_card_le (m n : ℕ) [NeZero (m.lcm n)]
    (a : (ZMod m)ˣ) (b : (ZMod n)ˣ) :
    Nat.card {x : (ZMod (m.lcm n))ˣ //
      (ZMod.unitsMap (Nat.dvd_lcm_left m n) x)^2=a ∧
      (ZMod.unitsMap (Nat.dvd_lcm_right m n) x)^2=b} ≤
        2*(m.lcm n).divisors.card := by
  have h := Arithmetic.card_square_map_fiber_le_one (pairUnitsReduction m n)
    (pairUnitsReduction_injective m n) (a,b)
  have he : {x : (ZMod (m.lcm n))ˣ //
      (ZMod.unitsMap (Nat.dvd_lcm_left m n) x)^2=a ∧
      (ZMod.unitsMap (Nat.dvd_lcm_right m n) x)^2=b} ≃
      {x : (ZMod (m.lcm n))ˣ // (pairUnitsReduction m n x)^2=(a,b)} :=
    Equiv.subtypeEquivRight (fun x => by simp [pairUnitsReduction, Prod.ext_iff])
  exact (Nat.card_congr he).le.trans (h.trans
    (Arithmetic.card_unit_square_fiber_le_two_divisors (m.lcm n) 1))

theorem unitsMap_trans {a b c : ℕ} (hab:a∣b) (hbc:b∣c) (x:(ZMod c)ˣ) :
    ZMod.unitsMap hab (ZMod.unitsMap hbc x)=ZMod.unitsMap (dvd_trans hab hbc) x :=
  congrArg (fun f => f x) (ZMod.unitsMap_comp hab hbc)

theorem paired_square_probability_le_rpow (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ Q m n : ℕ, ∀ [NeZero Q],
      ∀ hm : m∣Q, ∀ hn : n∣Q, ∀ a : (ZMod m)ˣ, ∀ b : (ZMod n)ˣ,
      (Nat.card {x : (ZMod Q)ˣ //
        (ZMod.unitsMap hm x)^2=a ∧ (ZMod.unitsMap hn x)^2=b}:ℝ) /
        Nat.card (ZMod Q)ˣ ≤ C*(m.lcm n:ℝ)^(ε-1) := by
  obtain ⟨C,hC,hbound⟩ := Arithmetic.density_le_rpow_of_le_two_divisors ε hε
  refine ⟨C,hC,fun Q m n _ hm hn a b => ?_⟩
  have hlQ : m.lcm n∣Q := Nat.lcm_dvd hm hn
  have hl : NeZero (m.lcm n) := ⟨fun hz => NeZero.ne Q (by
    rw [hz] at hlQ
    exact Nat.zero_dvd.mp hlQ)⟩
  let P : (ZMod (m.lcm n))ˣ → Prop := fun x =>
    (ZMod.unitsMap (Nat.dvd_lcm_left m n) x)^2=a ∧
    (ZMod.unitsMap (Nat.dvd_lcm_right m n) x)^2=b
  have hhaar := unit_haar_proportion (ZMod.unitsMap hlQ) (ZMod.unitsMap_surjective hlQ) P
  have he : (Nat.card {x : (ZMod Q)ˣ //
      (ZMod.unitsMap hm x)^2=a ∧ (ZMod.unitsMap hn x)^2=b}:ℝ) /
      Nat.card (ZMod Q)ˣ =
      (Nat.card {x : (ZMod (m.lcm n))ˣ // P x}:ℝ)/Nat.card (ZMod (m.lcm n))ˣ := by
    simpa only [P, unitsMap_trans] using hhaar
  rw [he]
  have hc : Nat.card (ZMod (m.lcm n))ˣ=(m.lcm n).totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  rw [hc]
  exact hbound (m.lcm n) _ (NeZero.pos _) (paired_square_card_le m n a b)

end Ostmann.Characters

end

end OAI
