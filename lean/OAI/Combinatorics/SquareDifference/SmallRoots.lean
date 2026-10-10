import OAI.Combinatorics.SquareDifference.IntervalCoefficient

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

noncomputable def smallStrict (p : ℕ) (x : ZMod (smallQuadraticModulus p)) : Prop :=
  if p=2 then x=1 else x≠0 ∧ IsSquare x

lemma exists_small_root (p : ℕ) [Fact p.Prime] (x : ZMod (smallQuadraticModulus p))
    (hx : smallStrict p x) : ∃c : ZMod p,(if p=2 then c=1 else c≠0) ∧ smallRootSquare p c=x := by
  classical
  by_cases h2 : p=2
  · subst p
    refine ⟨1,by simp,?_⟩
    simpa only [smallStrict,smallRootSquare,ite_true] using hx.symm
  · have he : smallQuadraticModulus p=p := by simp only [smallQuadraticModulus,h2,ite_false]
    let e : ZMod (smallQuadraticModulus p) ≃+* ZMod p := RingEquiv.cast he
    have hx' : x≠0 ∧ IsSquare x := by simpa only [smallStrict,h2,ite_false] using hx
    have hn := hx'.1
    have hs := hx'.2
    obtain ⟨y,hy⟩ := hs
    refine ⟨e y,by simpa only [h2,ite_false] using (show e y≠0 from fun hz => hn (by
      have hy0 : y=0 := e.injective (by simpa using hz)
      simp only [hy0,mul_zero] at hy; exact hy)),?_⟩
    apply e.injective
    rw [hy,map_mul]
    have hh : e (smallRootSquare p (e y))=(e y)^2 := by
      simp only [smallRootSquare,h2,ite_false,map_pow,map_natCast,ZMod.natCast_zmod_val]
    rw [hh,pow_two]

section Small

variable {S : Type*} [Fintype S] [instDecidableEqS : DecidableEq S] (ps : S → ℕ)

noncomputable def smallModulus : ℕ := ∏s,smallQuadraticModulus (ps s)

lemma smallModulus_dvd {S : Type*}
    [Fintype S]
    [DecidableEq S]
    (ps : S → ℕ) (s : S) : smallQuadraticModulus (ps s)∣smallModulus ps := dvd_prod_of_mem _ (mem_univ s)

noncomputable def smallProjection (s : S) : ZMod (smallModulus ps) →+* ZMod (smallQuadraticModulus (ps s)) :=
  ZMod.castHom (smallModulus_dvd ps s) _

@[simp] lemma smallProjection_nat (s : S) (n : ℕ) : smallProjection ps s (n:ZMod (smallModulus ps))=(n:ZMod (smallQuadraticModulus (ps s))) := map_natCast _ _

noncomputable def smallStrictPair (s t : ZMod (smallModulus ps)) : Prop :=
  ∀i,smallStrict (ps i) (smallProjection ps i (t-s))

end Small

end SquareDifference

end

end OAI
