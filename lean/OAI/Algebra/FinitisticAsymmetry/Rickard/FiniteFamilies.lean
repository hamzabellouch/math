import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Model
import OAI.Algebra.Finitistic.Dimension.PDDimension

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.Rickard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

lemma exists_finite_module_high_pd (h : littleFinitisticDimension R = ⊤) (i : ℕ) :
    ∃ M : PDMinimal.FiniteModule k R,
      (i : WithBot ℕ∞) < projectiveDimension M.cat ∧ projectiveDimension M.cat < ⊤ := by
  have hi : (i : WithBot ℕ∞) < littleFinitisticDimension R := by
    rw [h]
    exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top i)
  simp only [littleFinitisticDimension, lt_iSup_iff] at hi
  obtain ⟨M, hfg, hpd, hgt⟩ := hi
  let := hfg
  let : Module k M := Module.compHom M (algebraMap k R)
  let : IsScalarTower k R M := IsScalarTower.of_compHom k R M
  let : FiniteDimensional k M := Module.Finite.trans R M
  exact ⟨PDMinimal.FiniteModule.of (k := k) (A := R) M, hgt, hpd⟩

lemma exists_minimal_family (h : littleFinitisticDimension R = ⊤) :
    ∃ (M : ℕ → PDMinimal.FiniteModule k R) (d : ℕ → ℕ),
      (∀ i, i < d i) ∧
      (∀ i, HasProjectiveDimensionLE (M i).cat (d i)) ∧
      (∀ i, ¬ Subsingleton (PDMinimal.term (M i) (d i))) := by
  classical
  choose M hgt hfin using exists_finite_module_high_pd (k := k) h
  have hb (i : ℕ) : ∃ d, HasProjectiveDimensionLE (M i).cat d :=
    (projectiveDimension_ne_top_iff _).mp (hfin i).ne
  let d := fun i => Nat.find (hb i)
  have hd (i : ℕ) : HasProjectiveDimensionLE (M i).cat (d i) := Nat.find_spec (hb i)
  have hdi (i : ℕ) : i < d i := by
    have hp := (projectiveDimension_le_iff _ _).mpr (hd i)
    have hlt := (hgt i).trans_le hp
    exact_mod_cast hlt
  refine ⟨M, d, hdi, hd, ?_⟩
  intro i hz
  have hpos := hdi i
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d i ≠ 0)
  have hh : HasProjectiveDimensionLE (M i).cat n :=
    (PDMinimal.pdLE_iff_term_zero (M i) n).mpr (by simpa [hn] using hz)
  have hm := Nat.find_min' (hb i) hh
  change d i ≤ n at hm
  omega

end LittleFinitistic.Rickard

end

end OAI
