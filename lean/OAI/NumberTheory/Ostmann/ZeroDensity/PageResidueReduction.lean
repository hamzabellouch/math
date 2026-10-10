import OAI.NumberTheory.Ostmann.Construction.ExternalResidueReduction
import OAI.NumberTheory.Ostmann.ZeroDensity.GiantHaarDensity
import OAI.NumberTheory.Ostmann.ZeroDensity.PageConductorProjection

namespace OAI

/-! # Retaining the Page factor when redundant residue coordinates are removed -/

namespace Ostmann
open scoped BigOperators Classical

theorem nat_modEq_castHom_val {m n : ℕ} [NeZero m] [NeZero n]
    (h : m ∣ n) (a : ZMod n) :
    Nat.ModEq m a.val ((ZMod.castHom h (ZMod m)) a).val := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  rw [ZMod.natCast_zmod_val]
  have hh := map_natCast (ZMod.castHom h (ZMod m)) a.val
  rw [ZMod.natCast_zmod_val] at hh
  exact hh.symm

theorem pageGiantWeight_castHom (P : PublishedProgressionInput) (Q : ℕ)
    {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n)
    (hpage : pageAtModulus n (selectedPageZero P Q) = pageAtModulus m (selectedPageZero P Q))
    (a : ZMod n) (x : ℝ) :
    pageGiantWeight P Q n a.val x =
      pageGiantWeight P Q m ((ZMod.castHom h (ZMod m)) a).val x := by
  have he := pageCoefficient_eq_of_modEq (selectedPageZero P Q) (nat_modEq_castHom_val h a)
  simp only [pageGiantWeight, hpage, pageMultiplier, he]

theorem uniform_external_page_reduction (P : PublishedProgressionInput) (Q : ℕ)
    {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n)
    (hpage : pageAtModulus n (selectedPageZero P Q) = pageAtModulus m (selectedPageZero P Q))
    (F : ZMod m × (ZMod m)ˣ → ℂ) (y : ℝ) :
    (Fintype.card (ZMod n × (ZMod n)ˣ) : ℂ)⁻¹ *
      (∑ z, F (externalResidueReduction h z) * pageGiantWeight P Q n (z.2 : ZMod n).val y) =
    (Fintype.card (ZMod m × (ZMod m)ˣ) : ℂ)⁻¹ *
      ∑ z, F z * pageGiantWeight P Q m (z.2 : ZMod m).val y := by
  have he (z : ZMod n × (ZMod n)ˣ) := pageGiantWeight_castHom P Q h hpage (z.2 : ZMod n) y
  simp_rw [he]
  exact uniform_external_residue_reduction h (fun z => F z * pageGiantWeight P Q m (z.2 : ZMod m).val y)

theorem uniform_prime_pair_page_reduction (P : PublishedProgressionInput) (Q : ℕ)
    {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n)
    (hpage : pageAtModulus n (selectedPageZero P Q) = pageAtModulus m (selectedPageZero P Q))
    (F : (ZMod m)ˣ × (ZMod m)ˣ → ℂ) (x y : ℝ) :
    (Fintype.card ((ZMod n)ˣ × (ZMod n)ˣ) : ℂ)⁻¹ *
      (∑ z, F (primePairResidueReduction h z) * pageGiantWeight P Q n (z.1 : ZMod n).val x *
        pageGiantWeight P Q n (z.2 : ZMod n).val y) =
    (Fintype.card ((ZMod m)ˣ × (ZMod m)ˣ) : ℂ)⁻¹ *
      ∑ z, F z * pageGiantWeight P Q m (z.1 : ZMod m).val x * pageGiantWeight P Q m (z.2 : ZMod m).val y := by
  simp_rw [pageGiantWeight_castHom P Q h hpage]
  exact uniform_prime_pair_residue_reduction h (fun z =>
    F z * pageGiantWeight P Q m (z.1 : ZMod m).val x * pageGiantWeight P Q m (z.2 : ZMod m).val y)

end Ostmann

end OAI
