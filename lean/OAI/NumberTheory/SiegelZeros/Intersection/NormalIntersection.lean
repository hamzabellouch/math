import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Colon
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace OAI

namespace SiegelZeros

section

open Submodule

namespace SiegelZerosAwei.Workers.W15

variable {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]

def baseFractions : Submodule R K := (Algebra.linearMap R K).range

def denominatorIdeal (x : K) : Ideal R := (baseFractions (R := R)).colon {x}

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K] in
lemma mem_denominatorIdeal (x : K) (a : R) :
    a ∈ denominatorIdeal (R := R) x ↔ ∃ b : R, algebraMap R K b = algebraMap R K a * x := by
  simp [denominatorIdeal, mem_colon_singleton, baseFractions, Algebra.smul_def]

omit [IsNoetherianRing R] [IsIntegrallyClosed R] in
lemma denominatorIdeal_ne_bot (x : K) : denominatorIdeal (R := R) x ≠ ⊥ := by
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective R x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap R K b ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr hb0
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨b, (mem_denominatorIdeal x b).2 ⟨a, ?_⟩, hb0⟩
  rw [← hx]
  simp [div_eq_mul_inv, mul_left_comm, hbK]

omit [IsDomain R] in
lemma fraction_in_base_of_preserves_ideal (I : Ideal R) (hI : I ≠ ⊥) (x : K)
    (hx : ∀ a ∈ I, ∃ b ∈ I, algebraMap R K b = x * algebraMap R K a) :
    x ∈ baseFractions (R := R) := by
  let M := Submodule.map (Algebra.linearMap R K) I
  have hM : M ≠ ⊥ := by
    obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff I).mp hI
    exact (Submodule.ne_bot_iff M).mpr
      ⟨algebraMap R K a, ⟨a, ha, rfl⟩, IsFractionRing.to_map_eq_zero_iff.not.mpr ha0⟩
  have hMfg : M.FG := (IsNoetherian.noetherian I).map _
  have hstable : ∀ y ∈ M, x • y ∈ M := by
    rintro y ⟨a, ha, rfl⟩
    obtain ⟨b, hb, heq⟩ := hx a ha
    exact ⟨b, hb, heq⟩
  exact IsIntegrallyClosed.algebraMap_eq_of_integral
    (isIntegral_of_smul_mem_submodule M hM hMfg x hstable)

theorem prime_denominatorIdeal_height_eq_one (x : K)
    [hP : (denominatorIdeal (R := R) x).IsPrime] :
    (denominatorIdeal (R := R) x).height = 1 := by
  let P := denominatorIdeal (R := R) x
  have hnotbase : x ∉ baseFractions (R := R) := by
    intro hx
    apply hP.ne_top
    exact (Submodule.colon_eq_top_iff_subset {x}).2 (Set.singleton_subset_iff.mpr hx)
  have hnotstable : ¬ ∀ a ∈ P, ∃ b ∈ P,
      algebraMap R K b = x * algebraMap R K a := by
    intro h
    exact hnotbase (fraction_in_base_of_preserves_ideal P (denominatorIdeal_ne_bot x) x h)
  push Not at hnotstable
  obtain ⟨a, ha, hfail⟩ := hnotstable
  obtain ⟨b, hb⟩ := (mem_denominatorIdeal x a).1 ha
  have hb' : algebraMap R K b = x * algebraMap R K a := by simpa [mul_comm] using hb
  have hbnot : b ∉ P := fun h => hfail b h hb'
  have hrelation : ∀ z ∈ P, ∃ c : R, b * z = a * c := by
    intro z hz
    obtain ⟨c, hc⟩ := (mem_denominatorIdeal x z).1 hz
    refine ⟨c, (IsFractionRing.injective R K) ?_⟩
    simp only [map_mul]
    rw [hb, hc]
    ring
  have hminimal : P ∈ (Ideal.span {a}).minimalPrimes := by
    refine ⟨⟨hP, Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha)⟩, ?_⟩
    intro Q hQ hQP z hz
    obtain ⟨c, hc⟩ := hrelation z hz
    have haQ : a ∈ Q := hQ.2 (Ideal.subset_span (Set.mem_singleton a))
    have hprod : b * z ∈ Q := by rw [hc]; exact Q.mul_mem_right c haQ
    exact (hQ.1.mem_or_mem hprod).resolve_left (fun hbQ => hbnot (hQP hbQ))
  have hle : P.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hminimal
  have hpos : 0 < P.height := by
    simpa only [Ideal.height_bot] using
      (Ideal.height_strict_mono_of_isPrime
        (bot_lt_iff_ne_bot.mpr (denominatorIdeal_ne_bot (R := R) x)))
  exact le_antisymm hle (by simpa using (ENat.add_one_le_iff (by simp : (0 : ℕ∞) ≠ ⊤)).2 hpos)

theorem mem_base_of_mem_heightOne_localizations (x : K)
    (h : ∀ (P : Ideal R) [P.IsPrime], P.height = 1 →
      x ∈ Localization.subalgebra.ofField K P.primeCompl
        P.primeCompl_le_nonZeroDivisors) :
    x ∈ baseFractions (R := R) := by
  by_contra hx
  have hd : denominatorIdeal (R := R) x ≠ ⊤ := by
    simpa [denominatorIdeal, Submodule.colon_eq_top_iff_subset] using hx
  obtain ⟨⟨P, hP⟩⟩ := Ideal.nonempty_minimalPrimes hd
  have : P.IsPrime := hP.1.1
  obtain ⟨y, hy⟩ := Submodule.exists_eq_colon_of_mem_minimalPrimes hP
  have hheight : P.height = 1 := by
    have : (denominatorIdeal (R := R) y).IsPrime := by
      simpa only [denominatorIdeal, ← hy] using (inferInstance : P.IsPrime)
    simpa [denominatorIdeal, ← hy] using prime_denominatorIdeal_height_eq_one (R := R) y
  obtain ⟨n, d, hdP, hxd⟩ := h P hheight
  have hdK : algebraMap R K d ≠ 0 :=
    IsFractionRing.to_map_eq_zero_iff.not.mpr (fun heq => hdP (heq ▸ P.zero_mem))
  apply hdP
  apply hP.1.2
  apply (mem_denominatorIdeal x d).2
  refine ⟨n, ?_⟩
  rw [hxd]
  field_simp

end SiegelZerosAwei.Workers.W15

end

end SiegelZeros

end OAI
